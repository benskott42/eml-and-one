/**
 * Pool and record parity against fixtures from untouched v1.1.
 * The fixture is the output of searchConstants at 63e0d8d (lib/eml/golf.ts
 * as that commit shipped it). This script does not compare against a
 * reimplementation kept in the PR.
 *
 * There is no meet-in-the-middle audit: that probe did not beat the key-table
 * fix, so the search does not use it. Every pair is still examined.
 */
import { readFileSync } from "node:fs";
import { searchConstants, type GolfHit } from "../lib/eml/golf";

type FixtureHit = GolfHit;
type FixtureRun = { allowLn0: boolean; pool: number; hits: FixtureHit[] };
type Fixture = { commit: string; maxK: number; runs: FixtureRun[] };

const fixture = JSON.parse(readFileSync(new URL("./fixtures/enum-v11-k29.json", import.meta.url), "utf8")) as Fixture;
const ORACLE = "63e0d8d1a422b71d4d653f6fc3a10e017ff7e1ac";

function hitKey(hit: FixtureHit): string {
  return [hit.id, hit.k, hit.rpn, hit.singular, hit.usesLn0, hit.branch, hit.domain].join("|");
}

let failed = 0;
function report(name: string, ok: boolean, detail = ""): void {
  if (!ok) {
    failed += 1;
    console.log("FAIL", name, detail);
  } else console.log("ok", name);
}

report("fixture is untouched v1.1", fixture.commit === ORACLE, fixture.commit);

for (const run of fixture.runs) {
  const got = searchConstants(fixture.maxK, { allowLn0: run.allowLn0 });
  const label = `K≤${fixture.maxK} ln0=${run.allowLn0}`;
  report(`${label} pool`, got.pool === run.pool, `got ${got.pool} want ${run.pool}`);
  const wantHits = run.hits.map(hitKey).join("\n");
  const gotHits = got.hits.map(hitKey).join("\n");
  report(`${label} hits`, wantHits === gotHits, `\nwant ${wantHits}\ngot  ${gotHits}`);
}

if (failed) {
  console.log(`${failed} failed`);
  process.exit(1);
}
console.log("parity passed");
