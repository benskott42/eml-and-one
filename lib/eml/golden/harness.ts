#!/usr/bin/env tsx
/**
 * Golden output parity harness.
 *
 *   npm run eml:golden                 compare in-process golden.txt
 *   npm run eml:golden -- --wire       compare fresh-process golden-wire.txt
 *   npm run eml:golden -- --update     rewrite the file for the selected mode
 *   npm run eml:golden -- --self-test  parser checks only
 *
 * --wire packs each expression in this process and evaluates it in its own
 * child. The child unpacks through the exact worker's path, evaluates twice,
 * and the second screen is the eval2 column. Children are spawned one at a
 * time so a row cannot warm the next row's cache.
 */
import { spawnSync } from "node:child_process";
import { mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import path from "node:path";
import { deserialize, serialize } from "node:v8";
import { fileURLToPath } from "node:url";
import { compileExpression } from "../parse";
import { packCircuit, unpackCircuit } from "../wire";
import { getAllCorpus, heavyCorpus } from "./corpus";
import { compareGolden, formatGolden, type GoldenEntry, type GoldenMode } from "./compare";
import { screenNode, type Screen } from "./screen";
import { runGoldenSelfTest } from "./self-test";

const repoRoot = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "../../..");
const goldenPath = path.join(repoRoot, "lib/eml/golden/golden.txt");
const goldenWirePath = path.join(repoRoot, "lib/eml/golden/golden-wire.txt");
const wireChildScript = path.join(repoRoot, "scripts/wire-eval-child.ts");
const uncachedScript = path.join(repoRoot, "scripts/golden-uncached-child.ts");
const tsxCli = path.join(repoRoot, "node_modules", "tsx", "dist", "cli.mjs");
const esbuildBin = path.join(repoRoot, "node_modules", "esbuild", "bin", "esbuild");

/** In-process budget. The wire child uses the worker's 80_000. */
const IN_PROCESS_BUDGET = 200_000;

const BUGS: Record<string, string> = {
  "6.103e-120*i+6.103e-120*i": "v1.1-complex-half: exact mode shows half the sum",
  "(i*(1+10^(-124))-i)*i+i*10^10/3": "A1-real-drop: real part dropped",
  "((1+10^(-130))-1)+i/2": "wire-real-drop: real part ~1e-130 dropped; fix owned by bigfixer",
  "((1+10^(-130))-1)+i*(1+10^(-130))/2": "wire-real-drop: real part ~1e-130 dropped; fix owned by bigfixer",
  "((1+10^(-136))-1)+i*3/2": "wire-real-drop: real part ~1e-136 dropped; fix owned by bigfixer",
  "sinh(1e-7)-1e-7": "folded-zero: certified 0",
  "artanh(1e-7)-1e-7": "folded-zero: certified 0",
  "1-cos(sqrt(1/10^130))": "roundtrip+cache-second: pack/unpack text mismatch, and a repeat eval certifies 0",
  "cos(1e100)": "cache-second: fresh eval is argument too large; the repeat certifies it",
  "sin(1e22)": "cache-second: fresh eval is argument too large; the repeat certifies it",
  "cos(1e7)": "cache-second: fresh eval is argument too large; the repeat certifies it",
  "tan(1e100)": "cache-second: fresh eval is argument too large; the repeat certifies it",
  "tan(1e22)": "cache-second: fresh eval is argument too large; the repeat certifies it",
  "cos(1e119)": "repeat-cache: eval2 certifies −0.9849923936; true value is −0.37226",
  "sin(1e150)": "repeat-cache: eval2 certifies −0",
  "tan(pi/2)": "pole-wording: fresh eval is near a pole; the repeat says indeterminate (∞ − ∞ or 0 · ∞)",
  "tan(3*pi/2)": "pole-wording: fresh eval is near a pole; the repeat says indeterminate (∞ − ∞ or 0 · ∞)",
  "6*i+(-6*i)": "roundtrip: pack/unpack text mismatch",
  "1e-100*1.5/1.5-1e-100": "residue-stable: certified nonzero residue of an exact 0",
  "1e-50*1.5/1.5-1e-50": "residue-stable: certified nonzero residue of an exact 0",
  "exp(ln(1e-400))-1e-400": "residue-stable: certified −5×10^−801, true value is 0",
  "1e-400*1.5/1.5-1e-400": "residue-stable: certified −5×10^−801, true value is 0",
  "1e-400/2*2-1e-400": "residue-stable: certified −5×10^−801, true value is 0",
  "inf+1": "inf-finite: −∞i, singular:uses ln 0 = −∞",
  "ln(0)-1": "inf-finite: −∞i, singular:uses ln 0 = −∞",
  "ln(0)+i": "inf-finite: −∞i, singular:uses ln 0 = −∞",
  "(inf*i)/2": "inf-finite: ∞, singular:uses ln 0 = −∞",
  "ln(ln(0)*i)": "inf-finite: ∞, singular:uses ln 0 = −∞",
  "1e-320*(1+1e-100)-1e-320": "jimmy1: certified residue, true value is 1e-420",
  "exp(ln(ln(0))*i)": "jimmy1: ∞, singular:uses ln 0 = −∞",
  "exp(800)-exp(800)": "jimmy1: −∞, singular:passed through a non-finite value, true value is 0",
};

function entryFrom(source: string, screen: Screen, roundTrip: string, second?: Screen): GoldenEntry {
  return {
    source,
    exactText: screen.exactText,
    exactNotes: screen.exactNotes,
    floatText: screen.floatText,
    floatNotes: screen.floatNotes,
    pressCount: screen.pressCount,
    roundTrip,
    eval2Text: second?.exactText,
    eval2Notes: second?.exactNotes,
    bug: BUGS[source],
  };
}

function evaluateExpression(source: string): GoldenEntry {
  const node = compileExpression(source, {});
  const screen = screenNode(node, IN_PROCESS_BUDGET);
  let roundTrip = "OK";
  try {
    const packed = packCircuit(node);
    const again = screenNode(unpackCircuit(packed.tokens, packed.root), IN_PROCESS_BUDGET);
    const why: string[] = [];
    if (screen.exactText !== again.exactText) why.push("text-mismatch");
    if (screen.singular !== again.singular) why.push("singular-mismatch");
    if (screen.unverified !== again.unverified) why.push("unverified-mismatch");
    if (why.length) roundTrip = `FAIL:${why.join("+")}`;
  } catch (err) {
    roundTrip = `FAIL:${err instanceof Error ? err.message : String(err)}`;
  }
  return entryFrom(source, screen, roundTrip);
}

function evaluateViaWire(sources: string[]): Map<string, GoldenEntry> {
  const dir = mkdtempSync(path.join(tmpdir(), "eml-wire-"));
  try {
    const childPath = path.join(dir, "wire-child.cjs");
    const built = spawnSync(
      esbuildBin,
      [wireChildScript, "--bundle", "--platform=node", "--format=cjs", `--outfile=${childPath}`],
      { encoding: "utf8" },
    );
    if (built.status !== 0) {
      throw new Error(built.stderr || built.stdout || "esbuild failed");
    }
    const results = new Map<string, GoldenEntry>();
    for (const source of sources) {
      try {
        const node = compileExpression(source, {});
        const packed = packCircuit(node);
        const child = spawnSync(process.execPath, [childPath], {
          input: serialize({ tokens: packed.tokens, root: packed.root }),
          timeout: 180_000,
          maxBuffer: 32 * 1024 * 1024,
        });
        if (child.status !== 0) {
          throw new Error(child.stderr.toString().trim() || `wire child exited ${child.status}`);
        }
        const body = deserialize(child.stdout) as { first: Screen; second: Screen };
        results.set(source, entryFrom(source, body.first, "OK", body.second));
      } catch (err) {
        const message = err instanceof Error ? err.message : String(err);
        throw new Error(`wire ${source}: ${message}`);
      }
    }
    return results;
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
}

function generateGolden(includeHeavy: boolean, wireMode: boolean): string {
  const corpus = includeHeavy ? [...getAllCorpus(), ...heavyCorpus] : getAllCorpus();
  const mode: GoldenMode = wireMode ? "fresh-process" : "in-process";
  console.log(`Evaluating ${corpus.length} expressions (${mode})...`);
  const entries: GoldenEntry[] = [];
  if (wireMode) {
    const wired = evaluateViaWire(corpus);
    for (const source of corpus) {
      const entry = wired.get(source);
      if (!entry) throw new Error(`missing wire result for ${source}`);
      entries.push(entry);
    }
  } else {
    for (const source of corpus) entries.push(evaluateExpression(source));
  }
  entries.sort((a, b) => a.source.localeCompare(b.source));
  const seen = new Set<string>();
  for (const entry of entries) {
    if (seen.has(entry.source)) throw new Error(`duplicate corpus key: ${entry.source}`);
    seen.add(entry.source);
  }
  return formatGolden(mode, entries);
}

/**
 * EML_NOCACHE is read when exact.ts loads. A child started with the variable
 * already set is the check that the flag is real: the cached repeat of
 * 1-cos(sqrt(1/10^130)) certifies 0, and the uncached repeat must not.
 */
function checkUncached(): void {
  const sources = ["1+1", "sqrt(-0)", "1-cos(sqrt(1/10^130))"];
  const child = spawnSync(process.execPath, [tsxCli, uncachedScript], {
    input: JSON.stringify(sources),
    encoding: "utf8",
    timeout: 180_000,
    env: { ...process.env, EML_NOCACHE: "1" },
  });
  if (child.status !== 0) {
    console.error(child.stderr);
    throw new Error("uncached child failed");
  }
  const body = JSON.parse(child.stdout) as {
    nocache: string;
    rows: { source: string; first: string; second: string }[];
  };
  if (body.nocache !== "1") {
    throw new Error("EML_NOCACHE was not set in the child that loads exact.ts");
  }
  for (const row of body.rows) {
    if (row.first !== row.second) {
      throw new Error(`EML_NOCACHE did not keep ${row.source} stable: ${row.first} then ${row.second}`);
    }
    console.log(`uncached ${row.source}: ${row.first}`);
  }
}

function main() {
  const args = process.argv.slice(2);
  runGoldenSelfTest();
  console.log("self-test passed");
  if (args.includes("--self-test")) return;

  const isUpdate = args.includes("--update");
  const isHeavy = args.includes("--heavy");
  const isWire = args.includes("--wire");
  if (isUpdate && process.env.CI) {
    console.error("refusing --update because CI is set");
    process.exit(1);
  }

  const targetPath = isWire ? goldenWirePath : goldenPath;
  const generated = generateGolden(isHeavy, isWire);
  if (isUpdate) {
    writeFileSync(targetPath, generated, "utf8");
    console.log(`wrote ${targetPath}`);
    checkUncached();
    return;
  }

  let existing = "";
  try {
    existing = readFileSync(targetPath, "utf8");
  } catch {
    console.error(`Could not read ${targetPath}`);
    console.error("Run with --update to generate it.");
    process.exit(1);
  }
  const messages = compareGolden(existing, generated);
  if (messages.length) {
    for (const message of messages) console.log(message);
    console.log(`\n${messages.length} difference(s).`);
    console.log("Run with --update to regenerate. Every changed line needs a reason in the PR.");
    process.exit(1);
  }
  console.log("golden output matches");
  checkUncached();
}

try {
  main();
} catch (err) {
  console.error(err instanceof Error ? err.message : err);
  process.exit(1);
}
