import { performance } from "node:perf_hooks";
import { JSDOM } from "jsdom";

// React checks `input` event support once at import time, so JSDOM must exist first.
const boot = new JSDOM("<!doctype html><html><body></body></html>", {
  url: "http://localhost/",
  pretendToBeVisual: true,
});
const bootView = boot.window;
const globals = globalThis as unknown as {
  window: typeof bootView;
  document: Document;
  HTMLElement: typeof bootView.HTMLElement;
  self: typeof bootView;
  IS_REACT_ACT_ENVIRONMENT: boolean;
  Worker?: unknown;
};
globals.window = bootView;
globals.self = bootView;
globals.document = bootView.document;
globals.HTMLElement = bootView.HTMLElement;
globals.IS_REACT_ACT_ENVIRONMENT = true;

// Stub Worker in jsdom so hardware-view background compare does not fall back to
// synchronous main-thread exactReport during keystroke/push measurements.
class SilentWorker {
  onmessage: ((event: { data: unknown }) => void) | null = null;
  onerror: (() => void) | null = null;
  postMessage() {
    /* background worker in browser */
  }
  terminate() {
    /* noop */
  }
}
globals.Worker = SilentWorker;

type Sample = { wallMs: number; renderMs: number; flushes: number };

function percentile(values: number[], p: number): number {
  const sorted = [...values].sort((a, b) => a - b);
  const idx = Math.min(sorted.length - 1, Math.max(0, Math.ceil((p / 100) * sorted.length) - 1));
  return sorted[idx] ?? 0;
}

function median(values: number[]): number {
  const sorted = [...values].sort((a, b) => a - b);
  const mid = Math.floor(sorted.length / 2);
  if (sorted.length % 2 === 1) return sorted[mid] ?? 0;
  return ((sorted[mid - 1] ?? 0) + (sorted[mid] ?? 0)) / 2;
}

function summarize(name: string, samples: Sample[]) {
  const walls = samples.map((s) => s.wallMs);
  const renders = samples.map((s) => s.renderMs);
  const flushes = samples.map((s) => s.flushes);
  const totalFlushes = flushes.reduce((a, b) => a + b, 0);
  const row = {
    scenario: name,
    n: samples.length,
    wallMedianMs: Number(median(walls).toFixed(2)),
    wallP95Ms: Number(percentile(walls, 95).toFixed(2)),
    renderMedianMs: Number(median(renders).toFixed(2)),
    renderP95Ms: Number(percentile(renders, 95).toFixed(2)),
    flushesMedian: Number(median(flushes).toFixed(1)),
    flushesTotal: totalFlushes,
  };
  return row;
}

async function main() {
  const { act, Profiler } = await import("react");
  const { createRoot } = await import("react-dom/client");
  const { EmlCalculator } = await import("../components/EmlCalculator");
  const { onCircuitIsolate } = await import("../lib/eml/node");

  let isolateCount = 0;
  onCircuitIsolate(() => {
    isolateCount += 1;
  });

  const N = 20;

  async function mountCalc() {
    const dom = new JSDOM(`<!doctype html><html><body><div id="root"></div></body></html>`, {
      url: "http://localhost/",
      pretendToBeVisual: true,
    });
    const view = dom.window;
    globals.window = view;
    globals.self = view;
    globals.document = view.document;
    globals.HTMLElement = view.HTMLElement;

    const mount = view.document.getElementById("root")!;
    const root = createRoot(mount);

    let renderMs = 0;
    const onRender = (_id: string, _phase: "mount" | "update" | "nested-update", actualDuration: number) => {
      renderMs += actualDuration;
    };

    await act(async () => {
      root.render(
        <Profiler id="calc" onRender={onRender}>
          <EmlCalculator />
        </Profiler>,
      );
    });

    const buttonByText = (label: string) =>
      [...view.document.querySelectorAll("button")].find((b) => b.textContent?.trim() === label) as
        | HTMLButtonElement
        | undefined;

    const clickBtn = async (label: string) => {
      const btn = buttonByText(label);
      if (!btn) throw new Error(`Missing button: ${label}`);
      await act(async () => {
        btn.click();
      });
    };

    const setInput = async (input: HTMLInputElement, value: string) => {
      const setter = Object.getOwnPropertyDescriptor(view.HTMLInputElement.prototype, "value")?.set;
      await act(async () => {
        setter?.call(input, value);
        input.dispatchEvent(new view.Event("input", { bubbles: true }));
      });
    };

    // Switch to hardware view (float mode) and clear any previous session state.
    const clearBtn = buttonByText("Clear");
    if (clearBtn) {
      await act(async () => {
        clearBtn.click();
      });
    }
    const hw = buttonByText("hardware");
    if (!hw) throw new Error("Missing hardware button");
    if (hw.getAttribute("aria-checked") !== "true") {
      await act(async () => {
        hw.click();
      });
    }

    const inputs = [...view.document.querySelectorAll("input.ti-field")] as HTMLInputElement[];
    const xInput = inputs[0];
    const yInput = inputs[1];
    const exprInput = view.document.getElementById("expr") as HTMLInputElement | null;
    if (!xInput || !yInput || !exprInput) throw new Error("Missing calculator inputs");

    // Normalize x and y text for each fresh scenario.
    await setInput(xInput, "0.5");
    await setInput(yInput, "2");

    const computeExpr = async (source: string) => {
      await setInput(exprInput, source);
      await clickBtn("Compute");
    };

    const measure = async (fn: () => Promise<void>): Promise<Sample> => {
      renderMs = 0;
      const beforeFlushes = isolateCount;
      const t0 = performance.now();
      await fn();
      const wallMs = performance.now() - t0;
      return { wallMs, renderMs, flushes: isolateCount - beforeFlushes };
    };

    const cleanup = async () => {
      await act(async () => {
        root.unmount();
      });
      view.close();
    };

    return { view, xInput, yInput, exprInput, buttonByText, clickBtn, setInput, computeExpr, measure, cleanup };
  }

  const results = [];

  // Scenario 1: x keystroke with an empty stack (alternating / typing digits)
  {
    const c = await mountCalc();
    // Warm up one keystroke so JIT / React mount overhead is settled
    await c.setInput(c.xInput, "0.5");
    const samples: Sample[] = [];
    const digits = "12345678901234567890";
    for (let i = 0; i < N; i += 1) {
      const next = i % 2 === 0 ? `0.5${digits[i % 10]}` : "0.5";
      samples.push(await c.measure(() => c.setInput(c.xInput, next)));
    }
    results.push(summarize("x keystroke (empty, edit)", samples));
    await c.cleanup();
  }

  // Scenario 1b: x keystroke with an empty stack (20 distinct strings)
  {
    const c = await mountCalc();
    const samples: Sample[] = [];
    for (let i = 0; i < N; i += 1) {
      const next = `0.${50 + i}`;
      samples.push(await c.measure(() => c.setInput(c.xInput, next)));
    }
    results.push(summarize("x keystroke (empty, distinct)", samples));
    await c.cleanup();
  }

  // Scenario 2: x keystroke with top = sin(pi/6)
  {
    const c = await mountCalc();
    await c.computeExpr("sin(pi/6)");
    const samples: Sample[] = [];
    for (let i = 0; i < N; i += 1) {
      const next = `0.${50 + i}`;
      samples.push(await c.measure(() => c.setInput(c.xInput, next)));
    }
    results.push(summarize("x keystroke (top=sin(pi/6))", samples));
    await c.cleanup();
  }

  // Scenario 3: x keystroke with 2 items and top exp^3(...) K ~ 3143
  {
    const c = await mountCalc();
    await c.computeExpr("sin(pi/6)");
    await c.computeExpr("exp(exp(exp(sin(0.25))))");
    const samples: Sample[] = [];
    for (let i = 0; i < N; i += 1) {
      const next = `0.${50 + i}`;
      samples.push(await c.measure(() => c.setInput(c.xInput, next)));
    }
    results.push(summarize("x keystroke (2 items, exp^3 K~3021)", samples));
    await c.cleanup();
  }

  // Scenario 4: control - expression-field keystroke
  {
    const c = await mountCalc();
    const samples: Sample[] = [];
    for (let i = 0; i < N; i += 1) {
      const next = `sin(pi/6)+${i}`;
      samples.push(await c.measure(() => c.setInput(c.exprInput, next)));
    }
    results.push(summarize("control (expr keystroke)", samples));
    await c.cleanup();
  }

  // Scenario 5: history push (ln key on sin(pi/6))
  {
    const c = await mountCalc();
    await c.computeExpr("sin(pi/6)");
    const samples: Sample[] = [];
    for (let i = 0; i < N; i += 1) {
      samples.push(await c.measure(() => c.clickBtn("ln")));
      // Reset top back to sin(pi/6) outside measurement
      await c.clickBtn("drop");
      await c.computeExpr("sin(pi/6)");
    }
    results.push(summarize("history push (ln on sin(pi/6))", samples));
    await c.cleanup();
  }

  console.log("| Scenario | Wall med (ms) | Wall p95 (ms) | Render med (ms) | Render p95 (ms) | Flushes/op (med) | Flushes total |");
  console.log("| --- | ---: | ---: | ---: | ---: | ---: | ---: |");
  for (const r of results) {
    console.log(
      `| ${r.scenario} | ${r.wallMedianMs.toFixed(2)} | ${r.wallP95Ms.toFixed(2)} | ${r.renderMedianMs.toFixed(2)} | ${r.renderP95Ms.toFixed(2)} | ${r.flushesMedian.toFixed(1)} | ${r.flushesTotal} |`,
    );
  }
}

main().catch((err: unknown) => {
  console.error(err);
  process.exit(1);
});
