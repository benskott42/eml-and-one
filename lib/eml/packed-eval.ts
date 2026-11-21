/**
 * The exact worker's evaluation path.
 * The golden wire child calls this too, so a packed circuit is unpacked and
 * reported the same way the worker reports it.
 */
import type { C } from "./complex";
import { exactReport, type ExactReport } from "./exact";
import type { Node } from "./node";
import { unpackCircuit, type Wire } from "./wire";

/** Node budget used by lib/eml/exact.worker.ts. */
export const WORKER_NODE_BUDGET = 80_000;

export function reportNode(
  node: Node,
  maxNodes = WORKER_NODE_BUDGET,
  env: Record<string, C> = {},
): ExactReport {
  return exactReport(node, env, { maxNodes });
}

export function reportUnpacked(
  tokens: Wire[],
  root: number,
  maxNodes = WORKER_NODE_BUDGET,
  env: Record<string, C> = {},
): { node: Node; report: ExactReport } {
  const node = unpackCircuit(tokens, root);
  return { node, report: reportNode(node, maxNodes, env) };
}
