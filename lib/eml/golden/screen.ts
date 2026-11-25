/**
 * Display fields the golden harness records for one circuit.
 * Shared by the in-process harness and the fresh-process wire child.
 */
import { beyondFloatBound } from "../float-bound";
import { formatC } from "../format";
import { seriesShortcutNote } from "../library";
import { evaluateReport, type Node } from "../node";
import { exactToFloat, exactUnderflowsFloat, formatExact, type ExactReport } from "../exact";
import { pressPreviewForNode } from "../presses";
import { reportNode } from "../packed-eval";

export type Screen = {
  exactText: string;
  exactNotes: string[];
  floatText: string;
  floatNotes: string[];
  pressCount: string;
  singular: string | null;
  unverified: boolean;
};

export function screenOf(node: Node, report: ExactReport, maxNodes: number): Screen {
  const exactNotes: string[] = [];
  let exactText = "";
  if (report.unverified) {
    exactText = "—";
    exactNotes.push("couldn't verify");
  } else if (report.singular !== null) {
    exactText = formatExact(report.value).replace(/\u200b/g, "");
    exactNotes.push(`singular:${report.singular}`);
  } else {
    exactText = formatExact(report.value).replace(/\u200b/g, "");
    exactNotes.push("certified");
  }
  if (report.touchedLn0) exactNotes.push("ln0");
  if (seriesShortcutNote(node)) exactNotes.push("series-shortcut");

  const floatRep = evaluateReport(node, {}, { maxNodes });
  const floatNotes: string[] = [];
  let floatText = "";
  if (floatRep.unverified) {
    floatText = "—";
    floatNotes.push("unverified");
  } else {
    floatText = formatC({ re: floatRep.value.re, im: floatRep.value.im });
  }
  if (floatRep.singular !== null) floatNotes.push(`singular:${floatRep.singular}`);
  if (floatRep.touchedLn0) floatNotes.push("ln0");
  if (floatRep.overflowed) floatNotes.push("overflowed");
  if (floatRep.underflowed) floatNotes.push("underflowed");
  if (floatRep.nearCut) floatNotes.push("near-cut");
  if (!report.unverified && !floatRep.unverified) {
    const exactFloat = exactToFloat(report.value);
    if (exactUnderflowsFloat(report.value) || beyondFloatBound(floatRep.value, exactFloat)) {
      floatNotes.push("differs-from-exact");
    }
  }

  const press = pressPreviewForNode(node);
  const pressCount = press
    ? press.truncated
      ? `${press.presses.toString()}+`
      : press.presses.toString()
    : "N/A";

  return {
    exactText,
    exactNotes,
    floatText,
    floatNotes,
    pressCount,
    singular: report.singular,
    unverified: report.unverified === true,
  };
}

export function screenNode(node: Node, maxNodes: number): Screen {
  return screenOf(node, reportNode(node, maxNodes), maxNodes);
}
