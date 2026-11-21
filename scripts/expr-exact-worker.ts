import { parentPort } from "node:worker_threads";

type Handler = (event: { data: unknown }) => void;

/**
 * Loads lib/eml/exact.worker.ts inside a Worker thread.
 * The browser does the same import; this host only forwards the port.
 */
async function main(): Promise<void> {
  if (!parentPort) throw new Error("expr-exact-worker runs inside a Worker.");
  const port = parentPort;
  let handler: Handler | null = null;
  const scope = {
    postMessage(data: unknown) {
      port.postMessage(data);
    },
    set onmessage(fn: Handler | null) {
      handler = fn;
    },
    get onmessage() {
      return handler;
    },
  };
  (globalThis as { self?: typeof scope }).self = scope;
  await import("../lib/eml/exact.worker");
  port.on("message", (data: unknown) => {
    handler?.({ data });
  });
  port.postMessage({ type: "ready" });
}

void main();
