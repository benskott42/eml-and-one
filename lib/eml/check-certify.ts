import { spawnSync } from "node:child_process";
import path from "node:path";
import { fileURLToPath } from "node:url";
import Decimal from "decimal.js";
import { exactReport, formatExact } from "./exact";
import { compileExpression } from "./parse";
import { packCircuit, unpackCircuit } from "./wire";

/**
 * Values that exact mode certified wrong, and their siblings.
 * Every row runs the worker's path (parse, pack, unpack, exact report with the
 * worker's node budget), twice, so the second run reads the pure cache.
 * References are mpmath at 250 digits.
 */
const R = Decimal.clone({ precision: 200 });

function workerReport(source: string) {
  const packed = packCircuit(compileExpression(source, {}));
  return exactReport(unpackCircuit(packed.tokens, packed.root), {}, { maxNodes: 80_000 });
}

/** Agrees to 30 significant digits. A zero reference part must be an exact zero. */
function agrees(got: Decimal, want: string): boolean {
  const ref = new R(want);
  const value = new R(got.toString());
  if (ref.isZero()) return value.isZero();
  if (!value.isFinite()) return false;
  return value.sub(ref).abs().lte(ref.abs().mul("1e-30"));
}

/**
 * Tiny sums and differences behind a 10^k lift. A subnormal operand was lifted
 * only to 10^307, a pure imaginary that the lift pushed past π fell back to a
 * word that rounds a 10^(−200) term to 0, and a cancellation of 96 to 112
 * decades inside the lift was not seen by the exact engine.
 */
const tinyRows: Array<[string, string, string]> = [
  ["1e-320*(1+1e-100)-1e-320", "1e-420", "0"],
  ["(1+1e-100)*1e-320-1e-320", "1e-420", "0"],
  ["2e-320*(1+1e-100)-2e-320", "2e-420", "0"],
  ["1e-320*(1+1e-110)-1e-320", "1e-430", "0"],
  ["1e-320*(1+1e-100)+(-1e-320)", "1e-420", "0"],
  ["5e-322*(1+1e-60)-5e-322", "5e-382", "0"],
  ["1e-300*(1+1e-110)-1e-300", "1e-410", "0"],
  ["1e-5*(1+1e-110)-1e-5", "1e-115", "0"],
  ["1e-320*i*(1+1e-100)-1e-320*i", "0", "1e-420"],
  ["5e-300*i-4e-300*i", "0", "1e-300"],
  ["5e-200*i-4e-200*i", "0", "1e-200"],
  ["5e-200*i+3e-200*i", "0", "8e-200"],
  ["5e-200*i+(-4e-200*i)", "0", "1e-200"],
  ["5e-320*i+3e-320*i", "0", "8e-320"],
  // Was listed in docs/known-limitations.md as showing half the true sum. Same cause as the rows above.
  ["6.103e-120*i+6.103e-120*i", "0", "1.2206e-119"],
  ["6.103*10^(-120)*i+6.103*10^(-120)*i", "0", "1.2206e-119"],
];

/**
 * An infinity whose finite partner a gate drops. ln(ln(0)) is ∞ + iπ, so
 * ln(ln(0))·i is −π + i∞, and exp of that has modulus e^(−π) and no limiting
 * angle. The product word printed a real ∞ for both. Neither may be certified.
 */
const refusedRows = [
  "exp(ln(ln(0))*i)",
  "ln(ln(0))*i",
  "exp(-ln(ln(0))*i)",
  "ln(ln(0))*2",
  "sqrt(-inf)*2",
  "1/exp(ln(ln(0))*i)",
  "exp(-(ln(ln(0))*i))",
];

/** Directed and extended values that lose nothing stay certified, with these texts. */
const keptRows: Array<[string, string]> = [
  ["ln(0)*i", "−∞i"],
  ["(ln(0)*i)^3", "∞i"],
  ["(inf*i)^3", "−∞i"],
  ["inf*i*i", "−∞"],
  ["sqrt(ln(0))", "∞i"],
  ["ln(ln(0))", "∞ + 3.14159265359i"],
  ["ln(-inf)", "∞ + 3.14159265359i"],
  ["ln(0)^2", "∞"],
  ["exp(ln(0))", "0"],
  ["0^2", "0"],
  ["6*i+(-6*i)", "0"],
  ["4*i+0.5*i", "4.5i"],
  ["exp(ln(0)*i)", "undefined"],
  ["exp(inf*i)", "undefined"],
];

function certifyChecks(): number {
  let failed = 0;
  for (const [source, re, im] of tinyRows) {
    for (const run of ["first", "cached"]) {
      const report = workerReport(source);
      const text = formatExact(report.value);
      const ok = report.unverified !== true && report.singular === null && agrees(report.value.re, re) && agrees(report.value.im, im);
      if (!ok) {
        failed += 1;
        console.log("FAIL certify tiny", run, source, report.unverified ? "unverified" : text, report.value.re.toString(), report.value.im.toString());
      } else {
        console.log("certify tiny", run, source, text);
      }
    }
  }
  for (const source of refusedRows) {
    for (const run of ["first", "cached"]) {
      const report = workerReport(source);
      if (report.unverified !== true) {
        failed += 1;
        console.log("FAIL certify lost partner", run, source, formatExact(report.value), report.singular ?? "");
      } else {
        console.log("certify lost partner", run, source, "unverified");
      }
    }
  }
  for (const [source, want] of keptRows) {
    const report = workerReport(source);
    const text = report.unverified ? "unverified" : formatExact(report.value);
    if (text !== want) {
      failed += 1;
      console.log("FAIL certify kept", source, text, "want", want);
    } else {
      console.log("certify kept", source, text);
    }
  }
  failed += freshChecks();
  return failed;
}

/**
 * The same rows in a process that never built the circuits, as the worker
 * receives them: only what the wire carries (the lift marks included) survives.
 */
function freshChecks(): number {
  let failed = 0;
  const repoRoot = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "../..");
  const sources = [...tinyRows.map(([source]) => source), ...refusedRows, ...keptRows.map(([source]) => source)];
  const jobs = sources.map((source) => {
    const packed = packCircuit(compileExpression(source, {}));
    return { source, tokens: packed.tokens, root: packed.root };
  });
  const run = spawnSync(process.execPath, [path.join(repoRoot, "node_modules", "tsx", "dist", "cli.mjs"), path.join(repoRoot, "scripts/fresh-exact.ts")], {
    cwd: repoRoot,
    input: JSON.stringify(jobs),
    encoding: "utf8",
    timeout: 600_000,
  });
  if (run.status !== 0) {
    console.log("FAIL certify fresh", run.status, run.stderr);
    return 1;
  }
  const rows = JSON.parse(run.stdout) as Array<{ source: string; text: string; unverified: boolean }>;
  for (const row of rows) {
    const tiny = tinyRows.find(([source]) => source === row.source);
    const kept = keptRows.find(([source]) => source === row.source);
    const text = row.unverified ? "unverified" : row.text.replace(/\u200b/g, "");
    // A tiny row compares its 12 shown digits here; the in-process rows above compare 30.
    const want = tiny ? formatExact({ re: new R(tiny[1]), im: new R(tiny[2]) }) : kept ? kept[1] : "unverified";
    if (text !== want) {
      failed += 1;
      console.log("FAIL certify fresh", row.source, text, "want", want);
    } else {
      console.log("certify fresh", row.source, text);
    }
  }
  return failed;
}

/** Called by check.ts after the property checks. */
export function runCertifyChecks(): number {
  return certifyChecks();
}
