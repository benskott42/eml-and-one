import { checkCutTraces, exactTraceOf, floatTraceOf, ruleSelfTest, setCutTrace } from "./cut";
import { wordsForCutRule } from "./countModel";
import { exactReport } from "./exact";
import { evaluateReport, nodeFromRpn } from "./node";

export type CutDebug = {
  words: number;
  bad: string[];
  case2: string[];
  rule: { name: string; want: "fail" | "pass"; got: "fail" | "pass" }[];
  ua: string;
};

/** Per-gate cut check. Used by the unit test and, only when asked, by the page. */
export async function runCutRule(pairs?: Array<[string, string]>): Promise<CutDebug> {
  const list = pairs ?? wordsForCutRule();
  const bad: string[] = [];
  const case2: string[] = [];
  setCutTrace(true);
  try {
    for (const [word, label] of list) {
      const node = nodeFromRpn(word.split(""));
      evaluateReport(node, {}, { maxNodes: 80_000 });
      const report = exactReport(node, {}, { maxNodes: 80_000 });
      let check;
      try {
        check = checkCutTraces(floatTraceOf(node), exactTraceOf(node));
      } catch (err) {
        bad.push(`${label}: ${err instanceof Error ? err.message : "trace failed"}`);
        continue;
      }
      if (!check.lengthOk || !check.ok) bad.push(`${label}: ${check.violations.join("; ")}`);
      if (report.cutHits !== check.exactHits) bad.push(`${label}: exact cut ${report.cutHits} vs trace ${check.exactHits}`);
      for (const gate of check.case2) case2.push(`${word} K${word.length} ${gate.gate} ${gate.floatIm.toExponential(2)}`);
      await new Promise((resolve) => setTimeout(resolve, 0));
    }
  } finally {
    setCutTrace(false);
  }
  return {
    words: list.length,
    bad,
    case2,
    rule: ruleSelfTest(),
    ua: typeof navigator === "undefined" ? "node" : navigator.userAgent,
  };
}
