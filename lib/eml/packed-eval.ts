/**
 * The exact worker's evaluation path.
 * The golden wire child calls this too, so a packed circuit is unpacked and
 * reported the same way the worker reports it.
 */
import type { C } from "./complex";
import { exactReport, type ExactReport } from "./exact";
import { isolateCircuit, substitute, type Node } from "./node";
import { unpackCircuit, type Wire } from "./wire";

/** Node budget used by lib/eml/exact.worker.ts. */
export const WORKER_NODE_BUDGET = 80_000;

export type PackedEnvNodes = Record<string, { tokens: Wire[]; root: number }>;

export function reportNode(
  node: Node,
  maxNodes = WORKER_NODE_BUDGET,
  env: Record<string, C> = {},
  envNodes?: Record<string, Node>,
): ExactReport {
  const target = envNodes && Object.keys(envNodes).length > 0 ? substitute(node, envNodes) : node;
  return exactReport(target, env, { maxNodes });
}

export function reportUnpacked(
  tokens: Wire[],
  root: number,
  maxNodes = WORKER_NODE_BUDGET,
  env: Record<string, C> = {},
  envNodes?: PackedEnvNodes,
): { node: Node; report: ExactReport } {
  // Isolate the hash-cons table per worker request so WeakMap/WeakSet annotations
  // (exactUnsure, unverified, series shortcuts, etc.) cannot bleed into later requests.
  return isolateCircuit(() => {
    const node = unpackCircuit(tokens, root);
    const unpackedEnv: Record<string, Node> | undefined = envNodes
      ? Object.fromEntries(Object.entries(envNodes).map(([name, packed]) => [name, unpackCircuit(packed.tokens, packed.root)]))
      : undefined;
    return { node, report: reportNode(node, maxNodes, env, unpackedEnv) };
  });
}
