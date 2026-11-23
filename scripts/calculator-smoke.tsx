import { readFileSync } from "node:fs";
import { performance } from "node:perf_hooks";
import { JSDOM } from "jsdom";

// React decides once, at import, whether `input` events are supported. A window
// has to exist before that import or a typed program number never reaches the field.
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
};
globals.window = bootView;
globals.self = bootView;
globals.document = bootView.document;
globals.HTMLElement = bootView.HTMLElement;
globals.IS_REACT_ACT_ENVIRONMENT = true;

async function main() {
  const { act } = await import("react");
  const { createRoot } = await import("react-dom/client");
  const { renderToStaticMarkup } = await import("react-dom/server");
  const { EmlCalculator } = await import("../components/EmlCalculator");

  const html = renderToStaticMarkup(<EmlCalculator />).replace(/\s+/g, " ");
  const css = readFileSync(new URL("../components/ti-calculator.css", import.meta.url), "utf8");
  const font = readFileSync(new URL("../public/fonts/VT323-OFL.txt", import.meta.url), "utf8");

  const needles = [
    "EML and One",
    "a two-button calculator",
    "ti-device",
    "ti-lcd",
    "Two buttons only",
    "Every other key is a shortcut that presses these two for you.",
    ">1</button>",
    ">EML</button>",
    "Undo",
    "Clear",
    "Known float limits",
    "pressing the circuit runs the same gates",
    "i·arcosh",
    "low absolute precision",
    'aria-label="Calculator screen"',
    'aria-pressed="false"',
    "Cancel stops a long one and shows a dash.",
  ];

  let failed = false;
  for (const needle of needles) {
    if (!html.includes(needle)) {
      console.error(`missing ${needle}`);
      failed = true;
    }
  }
  if (!css.includes("prefers-reduced-motion") || !css.includes("VT323") || !css.includes(".ti-btn:focus-visible")) {
    console.error("calculator css is missing the font, focus ring, or reduced motion");
    failed = true;
  }
  if (!font.includes("SIL Open Font License")) {
    console.error("VT323 license is not the SIL Open Font License");
    failed = true;
  }

  const dom = new JSDOM(`<!doctype html><html><body><div id="root"></div></body></html>`, {
    url: "http://localhost/",
    pretendToBeVisual: true,
  });
  const view = dom.window;
  globals.window = view;
  globals.self = view;
  globals.document = view.document;
  globals.HTMLElement = view.HTMLElement;
  const mount = view.document.getElementById("root");
  if (!mount) {
    console.error("missing smoke root");
    process.exit(1);
  }
  const root = createRoot(mount);
  await act(async () => {
    root.render(<EmlCalculator />);
  });
  // Browser checks wait for this marker: the static HTML has the keys before they work.
  if (html.includes("data-ready") || view.document.querySelector(".ti-stage")?.getAttribute("data-ready") !== "1") {
    console.error("data-ready must be absent from the static HTML and set once mounted");
    failed = true;
  }
  const click = async (selector: string) => {
    const button = view.document.querySelector(selector);
    if (!(button instanceof view.HTMLButtonElement)) {
      console.error(`missing ${selector}`);
      failed = true;
      return;
    }
    await act(async () => {
      button.click();
    });
  };
  await click(".ti-btn-one");
  await click(".ti-btn-one");
  await click(".ti-btn-eml");
  const screenText = () => view.document.querySelector("[aria-label='Calculator screen']")?.textContent ?? "";
  const resultText = () => view.document.querySelector(".ti-lcd-result")?.textContent ?? "";
  const waitResult = async () => {
    for (let i = 0; i < 80; i += 1) {
      const text = resultText();
      if (text && text !== "computing" && text !== "0") return text;
      await act(async () => {
        await new Promise((resolve) => setTimeout(resolve, 25));
      });
    }
    return resultText();
  };
  await waitResult();
  const built = screenText();
  if (!resultText().includes("2.718") || !built.includes("001")) {
    console.error("pressing 1, 1, EML did not build e", built);
    failed = true;
  }
  const manualText = () => view.document.querySelector(".ti-manual")?.textContent ?? "";
  if (!manualText().includes("higher program number is a higher binary value")) {
    console.error("ordering legend missing from the manual", manualText());
    failed = true;
  }
  if (built.includes("higher program number is a higher binary value")) {
    console.error("ordering legend is still on the screen", built);
    failed = true;
  }
  await act(async () => {
    view.dispatchEvent(new view.KeyboardEvent("keydown", { key: "1", bubbles: true }));
  });
  if (resultText() !== "1") {
    console.error("the 1 key did not push after e", resultText(), screenText());
    failed = true;
  }
  const buttonByText = (label: string) =>
    [...view.document.querySelectorAll("button")].find((button) => button.textContent?.trim() === label);
  const undo = buttonByText("Undo");
  const exact = buttonByText("exact");
  if (!(undo instanceof view.HTMLButtonElement) || !(exact instanceof view.HTMLButtonElement)) {
    console.error("missing undo or exact");
    failed = true;
  } else {
    await act(async () => {
      undo.click();
      exact.click();
    });
    let after = "";
    for (let i = 0; i < 80; i += 1) {
      after = resultText();
      if (after.includes("2.718")) break;
      await act(async () => {
        await new Promise((resolve) => setTimeout(resolve, 25));
      });
    }
    if (!after.includes("2.718")) {
      console.error("undo during a mode switch dropped e", after, screenText());
      failed = true;
    }
    if (exact.getAttribute("aria-checked") !== "true") {
      console.error("exact mode was not selected", exact.getAttribute("aria-checked"));
      failed = true;
    }
  }
  const clear = buttonByText("Clear");
  if (!(clear instanceof view.HTMLButtonElement)) {
    console.error("missing Clear");
    failed = true;
  } else {
    await act(async () => {
      clear.click();
    });
  }
  const program = view.document.querySelector("input[placeholder='#1, 001, or 11E']");
  const setProgram = async (value: string) => {
    if (!(program instanceof view.HTMLInputElement)) {
      console.error("missing program field");
      failed = true;
      return;
    }
    const setter = Object.getOwnPropertyDescriptor(view.HTMLInputElement.prototype, "value")?.set;
    await act(async () => {
      setter?.call(program, value);
      program.dispatchEvent(new view.Event("input", { bubbles: true }));
    });
  };
  const clickNamed = async (label: string) => {
    const button = buttonByText(label);
    if (!(button instanceof view.HTMLButtonElement)) {
      console.error(`missing ${label}`);
      failed = true;
      return;
    }
    await act(async () => {
      button.click();
    });
    await act(async () => {
      await new Promise((resolve) => setTimeout(resolve, 40));
    });
  };
  await setProgram("#1");
  await clickNamed("Load");
  await waitResult();
  if (!resultText().includes("2.718") || !screenText().includes("program #1")) {
    console.error("loading #1 did not show e", resultText(), screenText());
    failed = true;
  }
  await clickNamed("Next");
  if (!screenText().includes("program #2") || resultText().includes("2.718")) {
    console.error("Next did not step to program #2", resultText(), screenText());
    failed = true;
  }
  await clickNamed("Prev");
  await waitResult();
  if (!resultText().includes("2.718") || !screenText().includes("program #1")) {
    console.error("Prev did not return to program #1", resultText(), screenText());
    failed = true;
  }
  await setProgram("E11");
  await clickNamed("Load");
  if (!screenText().includes("Rotated E11 to 11E.")) {
    console.error("a rotated word was silent", screenText());
    failed = true;
  }
  await setProgram("xE");
  await clickNamed("Load");
  const wordError = view.document.querySelector(".ti-lcd-error")?.textContent ?? "";
  if (!wordError.includes("two values")) {
    console.error("a variable word skipped the parser", wordError, screenText());
    failed = true;
  }
  await clickNamed("π");
  const copyNumber = buttonByText("Copy number");
  const piNumber = "#3125315318547434611379164";
  const note = view.document.querySelector(".ti-lcd-note span");
  if (!(copyNumber instanceof view.HTMLButtonElement) || copyNumber.getAttribute("title") !== piNumber || note?.getAttribute("title") !== piNumber) {
    console.error("pi's full program number is not on the tooltip or the copy button", copyNumber?.getAttribute("title"), note?.getAttribute("title"), screenText());
    failed = true;
  }
  if (!screenText().includes("#3125") || !screenText().includes("9164") || !screenText().includes("25 digits")) {
    console.error("pi's shortened program number is missing", screenText());
    failed = true;
  }

  // C2: each LCD flag is printed once. C3: "Copied" does not survive the next number, and the 2 s timer restores the label.
  const countLcd = (needle: string) => {
    const text = screenText();
    let count = 0;
    for (let from = 0; from < text.length; ) {
      const at = text.indexOf(needle, from);
      if (at < 0) break;
      count += 1;
      from = at + needle.length;
    }
    return count;
  };
  const waitFor = async (ready: () => boolean, tries: number, ms: number) => {
    for (let i = 0; i < tries; i += 1) {
      if (ready()) return true;
      await act(async () => {
        await new Promise((resolve) => setTimeout(resolve, ms));
      });
    }
    return ready();
  };
  const setInput = async (field: Element | null | undefined, value: string, missing: string) => {
    if (!(field instanceof view.HTMLInputElement)) {
      console.error(missing);
      failed = true;
      return false;
    }
    const setter = Object.getOwnPropertyDescriptor(view.HTMLInputElement.prototype, "value")?.set;
    await act(async () => {
      setter?.call(field, value);
      field.dispatchEvent(new view.Event("input", { bubbles: true }));
    });
    return true;
  };
  const setExpr = async (value: string) => setInput(view.document.querySelector("#expr"), value, "missing expression field");
  await clickNamed("Clear");
  await setExpr("ln(0)");
  await clickNamed("Compute");
  const ln0Flag = "uses ln 0 = −∞";
  const ln0Ready = await waitFor(() => resultText().includes("−∞") && countLcd(ln0Flag) > 0, 120, 50);
  const ln0Count = countLcd(ln0Flag);
  if (!ln0Ready || ln0Count !== 1) {
    console.error("exact ln(0) flag count", ln0Count, resultText(), screenText());
    failed = true;
  }
  await clickNamed("Clear");
  await clickNamed("hardware");
  await setExpr("ln(1+10^(-130))");
  await clickNamed("Compute");
  const differs = "float differs from exact";
  const differsReady = await waitFor(() => screenText().includes(differs), 160, 50);
  const differsCount = countLcd(differs);
  if (!differsReady || differsCount !== 1) {
    console.error("hardware ln(1+10^(-130)) flag count", differsCount, screenText());
    failed = true;
  }
  // N1: with floatDiffers set, the underflow caveat stays on the note.
  if (!screenText().includes("float underflows")) {
    console.error("hardware ln(1+10^(-130)) dropped the underflow caveat", screenText());
    failed = true;
  }
  await clickNamed("Clear");
  const xField = [...view.document.querySelectorAll("label")].find((label) => label.textContent?.trim().startsWith("x"))?.querySelector("input");
  if (await setInput(xField, "1e-400", "missing x field")) {
    await clickNamed("push x");
    const tinyReady = await waitFor(() => screenText().includes(differs), 160, 50);
    const tinyScreen = screenText();
    if (!tinyReady || (tinyScreen.includes(differs) && tinyScreen.includes("matches the usual value"))) {
      console.error("hardware 1e-400 shows both float differs and matches the usual value", tinyScreen);
      failed = true;
    }
  }
  const navigatorDescriptor = Object.getOwnPropertyDescriptor(globalThis, "navigator");
  Object.defineProperty(globalThis, "navigator", { value: view.navigator, configurable: true });
  Object.defineProperty(view.navigator, "clipboard", {
    value: { writeText: () => Promise.resolve() },
    configurable: true,
  });
  await clickNamed("Clear");
  await clickNamed("π");
  const copyPi = buttonByText("Copy number");
  if (!(copyPi instanceof view.HTMLButtonElement)) {
    console.error("pi chip did not show Copy number", screenText());
    failed = true;
  } else {
    await act(async () => {
      copyPi.click();
      await Promise.resolve();
    });
    if (buttonByText("Copied")?.textContent?.trim() !== "Copied") {
      console.error("Copy number did not flip to Copied", screenText());
      failed = true;
    }
  }
  await setExpr("e+pi");
  await clickNamed("Compute");
  if (!(buttonByText("Copy number") instanceof view.HTMLButtonElement) || buttonByText("Copied")) {
    console.error("e+pi left Copied on the screen", screenText());
    failed = true;
  }
  await clickNamed("Clear");
  await click(".ti-btn-one");
  const copyBits = buttonByText("Copy bits");
  let capturedReset: (() => void) | null = null;
  const originalSetTimeout = view.window.setTimeout;
  view.window.setTimeout = ((handler: TimerHandler, timeout?: number, ...args: unknown[]) => {
    if (timeout === 2000 && typeof handler === "function") {
      capturedReset = () => {
        handler(...args);
      };
      return 0;
    }
    return originalSetTimeout.call(view.window, handler, timeout, ...(args as never[]));
  }) as typeof view.window.setTimeout;
  if (!(copyBits instanceof view.HTMLButtonElement)) {
    console.error("pressing 1 did not show Copy bits", screenText());
    failed = true;
  } else {
    await act(async () => {
      copyBits.click();
      await Promise.resolve();
    });
  }
  view.window.setTimeout = originalSetTimeout;
  if (buttonByText("Copied bits")?.textContent?.trim() !== "Copied bits" || !capturedReset) {
    console.error("Copy bits did not flip to Copied bits", buttonByText("Copied bits")?.textContent, screenText());
    failed = true;
  } else {
    await click(".ti-btn-one");
    await act(async () => {
      capturedReset?.();
    });
    const bitsLabel = buttonByText("Copy bits")?.textContent?.trim() ?? buttonByText("Copied bits")?.textContent?.trim();
    if (bitsLabel !== "Copy bits") {
      console.error("Copy bits did not reset after pushing 1 again", bitsLabel, screenText());
      failed = true;
    }
  }
  if (navigatorDescriptor) Object.defineProperty(globalThis, "navigator", navigatorDescriptor);
  await act(async () => {
    root.unmount();
  });
  view.close();

  // A slow exact job must not hold the next one. The stand-in worker answers
  // only a job that arrived after the previous worker was replaced.
  class HoldingWorker {
    static made: HoldingWorker[] = [];
    onmessage: ((event: { data: unknown }) => void) | null = null;
    onerror: (() => void) | null = null;
    terminated = false;
    constructor() {
      HoldingWorker.made.push(this);
    }
    postMessage(data: { request: number }) {
      if (HoldingWorker.made[0] === this) return;
      const deliver = () => {
        if (this.terminated || !this.onmessage) return;
        this.onmessage({
          data: { type: "done", request: data.request, text: "2", re: 2, im: 0, singular: null, touchedLn0: false },
        });
      };
      setTimeout(deliver, 0);
    }
    terminate() {
      this.terminated = true;
    }
  }
  const workerGlobal = globalThis as unknown as { Worker?: typeof HoldingWorker };
  workerGlobal.Worker = HoldingWorker;
  const preempt = new JSDOM(`<!doctype html><html><body><div id="root"></div></body></html>`, {
    url: "http://localhost/",
    pretendToBeVisual: true,
  });
  const preemptView = preempt.window;
  globals.window = preemptView;
  globals.self = preemptView;
  globals.document = preemptView.document;
  globals.HTMLElement = preemptView.HTMLElement;
  const preemptMount = preemptView.document.getElementById("root");
  if (!preemptMount) {
    console.error("missing preemption root");
    process.exit(1);
  }
  const preemptRoot = createRoot(preemptMount);
  await act(async () => {
    preemptRoot.render(<EmlCalculator />);
  });
  const submitExpr = async (value: string) => {
    const form = preemptView.document.querySelector("form.ti-form");
    const field = form?.querySelector("input");
    const button = form?.querySelector("button");
    if (!(field instanceof preemptView.HTMLInputElement) || !(button instanceof preemptView.HTMLButtonElement)) {
      console.error("missing expression form");
      failed = true;
      return;
    }
    const setter = Object.getOwnPropertyDescriptor(preemptView.HTMLInputElement.prototype, "value")?.set;
    await act(async () => {
      setter?.call(field, value);
      field.dispatchEvent(new preemptView.Event("input", { bubbles: true }));
    });
    await act(async () => {
      button.click();
    });
  };
  await submitExpr("1e-300-3e-300");
  await submitExpr("1+1");
  let raced = "";
  for (let i = 0; i < 20; i += 1) {
    raced = preemptView.document.querySelector(".ti-lcd-result")?.textContent ?? "";
    if (raced.includes("2")) break;
    await act(async () => {
      await new Promise((resolve) => setTimeout(resolve, 20));
    });
  }
  if (!raced.includes("2") || !HoldingWorker.made[0]?.terminated || HoldingWorker.made.length < 2) {
    console.error("a fast exact job waited behind a slow one", raced, HoldingWorker.made.map((worker) => worker.terminated));
    failed = true;
  }
  const preemptClear = [...preemptView.document.querySelectorAll("button")].find((b) => b.textContent?.trim() === "Clear");
  if (preemptClear instanceof preemptView.HTMLButtonElement) {
    await act(async () => {
      preemptClear.click();
    });
  }
  await act(async () => {
    preemptRoot.unmount();
  });
  preemptView.close();
  delete workerGlobal.Worker;

  // --- Perf / isolation / memo / Load-isolation regression probes ---
  const { circuitStats, onCircuitIsolate } = await import("../lib/eml/node");
  const { compileExpression } = await import("../lib/eml/parse");
  const { programIndexDigits, rankProgram } = await import("../lib/eml/programIndex");

  let isolateFlushes = 0;
  onCircuitIsolate(() => {
    isolateFlushes += 1;
  });

  // 1. Key-cost label snapshot (captured from unmodified v1.1 304de9a) and isolate flush counts.
  const EXPECTED_KEY_COSTS: Record<string, Record<string, string>> = {
    empty: {
      "0": "K 7",
      "2": "K 19",
      e: "K 3",
      "π": "K 93",
      i: "K 57",
      "−1": "K 15",
      "½": "K 29",
      "√2": "K 61",
      exp: "K 209",
      ln: "K 213",
      "√": "K 249",
      "x²": "K 429",
      "1/x": "K 223",
      "±": "K 221",
      sin: "K 1383",
      cos: "K 1371",
      tan: "K 7307",
      asin: "K 8123",
      acos: "wide",
      atan: "K 777",
      sinh: "K 725",
      cosh: "K 739",
      tanh: "K 915",
      asinh: "K 2019",
      "σ": "K 257",
      "+": "K 243",
      "−": "K 235",
      "×": "K 241",
      "÷": "K 241",
      "xʸ": "K 249",
      "logₓy": "K 253",
      avg: "K 287",
      hypot: "K 791",
    },
    pi: {
      "0": "K 7",
      "2": "K 19",
      e: "K 3",
      "π": "K 93",
      i: "K 57",
      "−1": "K 15",
      "½": "K 29",
      "√2": "K 61",
      exp: "K 95",
      ln: "K 99",
      "√": "K 135",
      "x²": "K 201",
      "1/x": "K 109",
      "±": "K 107",
      sin: "K 975",
      cos: "K 963",
      tan: "K 5825",
      asin: "K 5981",
      acos: "wide",
      atan: "K 1511",
      sinh: "K 383",
      cosh: "K 397",
      tanh: "K 1047",
      asinh: "K 1479",
      "σ": "K 143",
      "+": "K 129",
      "−": "K 121",
      "×": "K 127",
      "÷": "K 127",
      "xʸ": "K 135",
      "logₓy": "K 139",
      avg: "K 173",
      hypot: "K 313",
    },
    "sin(pi/6)": {
      "0": "K 7",
      "2": "K 19",
      e: "K 3",
      "π": "K 93",
      i: "K 57",
      "−1": "K 15",
      "½": "K 29",
      "√2": "K 61",
      exp: "K 1241",
      ln: "K 1245",
      "√": "K 1281",
      "x²": "K 2493",
      "1/x": "K 1255",
      "±": "K 1269",
      sin: "wide",
      cos: "wide",
      tan: "wide",
      asin: "wide",
      acos: "wide",
      atan: "wide",
      sinh: "wide",
      cosh: "wide",
      tanh: "wide",
      asinh: "wide",
      "σ": "wide",
      "+": "K 1457",
      "−": "K 1415",
      "×": "K 1273",
      "÷": "K 1273",
      "xʸ": "K 1281",
      "logₓy": "K 1285",
      avg: "K 1501",
      hypot: "K 2855",
    },
    two_items_exp3: {
      "0": "K 7",
      "2": "K 19",
      e: "K 3",
      "π": "K 93",
      i: "K 57",
      "−1": "K 15",
      "½": "K 29",
      "√2": "K 61",
      exp: "K 3023",
      ln: "K 3027",
      "√": "K 3063",
      "x²": "K 6057",
      "1/x": "K 3037",
      "±": "K 3051",
      sin: "wide",
      cos: "wide",
      tan: "wide",
      asin: "wide",
      acos: "wide",
      atan: "wide",
      sinh: "wide",
      cosh: "wide",
      tanh: "wide",
      asinh: "wide",
      "σ": "wide",
      "+": "wide",
      "−": "wide",
      "×": "K 4275",
      "÷": "K 4275",
      "xʸ": "K 4283",
      "logₓy": "K 4287",
      avg: "wide",
      hypot: "wide",
    },
  };

  class SilentWorker {
    onmessage: ((event: { data: unknown }) => void) | null = null;
    onerror: (() => void) | null = null;
    postMessage() {
      /* background compare in hardware view */
    }
    terminate() {
      /* noop */
    }
  }
  workerGlobal.Worker = SilentWorker as unknown as typeof HoldingWorker;

  const perfDom = new JSDOM(`<!doctype html><html><body><div id="root"></div></body></html>`, {
    url: "http://localhost/",
    pretendToBeVisual: true,
  });
  const perfView = perfDom.window;
  globals.window = perfView;
  globals.self = perfView;
  globals.document = perfView.document;
  globals.HTMLElement = perfView.HTMLElement;
  const perfMount = perfView.document.getElementById("root");
  if (!perfMount) {
    console.error("missing perf root");
    process.exit(1);
  }
  const perfRoot = createRoot(perfMount);
  await act(async () => {
    perfRoot.render(<EmlCalculator />);
  });

  const perfButtonByText = (label: string) =>
    [...perfView.document.querySelectorAll("button")].find((b) => b.textContent?.trim() === label);
  const perfClick = async (label: string) => {
    const btn = perfButtonByText(label);
    if (!(btn instanceof perfView.HTMLButtonElement)) {
      console.error(`missing button ${label}`);
      failed = true;
      return;
    }
    await act(async () => {
      btn.click();
    });
  };
  const perfSetInput = async (input: HTMLInputElement, value: string) => {
    const setter = Object.getOwnPropertyDescriptor(perfView.HTMLInputElement.prototype, "value")?.set;
    await act(async () => {
      setter?.call(input, value);
      input.dispatchEvent(new perfView.Event("input", { bubbles: true }));
    });
  };
  const readKeyCosts = () => {
    const out: Record<string, string> = {};
    for (const group of perfView.document.querySelectorAll(".ti-group")) {
      for (const cell of group.querySelectorAll(".ti-key")) {
        const alt = cell.querySelector(".ti-key-alt")?.textContent?.trim() ?? "";
        const btn = cell.querySelector("button")?.textContent?.trim() ?? "";
        if (btn) out[btn] = alt;
      }
    }
    return out;
  };
  const checkCostsSnapshot = (name: string) => {
    const got = readKeyCosts();
    const want = EXPECTED_KEY_COSTS[name];
    const gotKeys = Object.keys(got).sort();
    const wantKeys = Object.keys(want).sort();
    if (gotKeys.length !== wantKeys.length || gotKeys.some((k, i) => k !== wantKeys[i])) {
      console.error(`key-cost snapshot key mismatch for ${name}`, gotKeys, wantKeys);
      failed = true;
      return;
    }
    for (const k of wantKeys) {
      if (got[k] !== want[k]) {
        console.error(`key-cost label mismatch for ${name}[${k}]: got ${got[k]}, want ${want[k]}`);
        failed = true;
      }
    }
  };

  await perfClick("Clear");
  await perfClick("hardware");
  const perfFields = [...perfView.document.querySelectorAll("input.ti-field")] as HTMLInputElement[];
  const perfXField = perfFields[0];
  const perfYField = perfFields[1];
  const perfExpr = perfView.document.getElementById("expr") as HTMLInputElement;
  await perfSetInput(perfXField, "0.5");
  await perfSetInput(perfYField, "2");

  // Snapshot 1: empty stack
  checkCostsSnapshot("empty");

  // Empty-stack isolate flush count: warm "2", then 10 x keystrokes across cached scalars give 0 (<= 1/keystroke).
  await perfSetInput(perfXField, "2");
  await perfSetInput(perfXField, "0.5");
  const emptyBefore = isolateFlushes;
  for (let i = 0; i < 10; i += 1) {
    await perfSetInput(perfXField, i % 2 === 0 ? "2" : "0.5");
  }
  const emptyCachedFlushes = isolateFlushes - emptyBefore;
  if (emptyCachedFlushes > 10) {
    console.error("empty-stack cached x keystrokes flushed too many times", emptyCachedFlushes);
    failed = true;
  }

  // Empty-stack unseen scalar still preserves per-preview isolation (1 scalar + 17 unary + 8 binary = 26, no const/default/y flushes).
  const unseenBefore = isolateFlushes;
  await perfSetInput(perfXField, "0.75");
  const unseenFlushes = isolateFlushes - unseenBefore;
  if (unseenFlushes !== 26) {
    console.error("empty-stack unseen x preview expected 26 isolated flushes, got", unseenFlushes);
    failed = true;
  }
  await perfSetInput(perfXField, "0.5");

  // Snapshot 2: pi stack
  await perfClick("π");
  checkCostsSnapshot("pi");

  // Snapshot 3: sin(pi/6) stack
  await perfClick("Clear");
  await perfSetInput(perfExpr, "sin(pi/6)");
  await perfClick("Compute");
  checkCostsSnapshot("sin(pi/6)");

  // 1-item stack isolate flush count: 10 distinct x keystrokes must trigger 0 flushes.
  const oneItemBefore = isolateFlushes;
  for (let i = 0; i < 10; i += 1) {
    await perfSetInput(perfXField, `0.${60 + i}`);
  }
  const oneItemFlushes = isolateFlushes - oneItemBefore;
  if (oneItemFlushes !== 0) {
    console.error("1-item stack x keystrokes triggered isolate flushes", oneItemFlushes);
    failed = true;
  }
  await perfSetInput(perfXField, "0.5");

  // Snapshot 4: two items with exp^3 top
  await perfSetInput(perfExpr, "exp(exp(exp(sin(0.25))))");
  await perfClick("Compute");
  checkCostsSnapshot("two_items_exp3");

  // 2-item stack isolate flush count: 10 distinct x keystrokes must trigger 0 flushes.
  const twoItemBefore = isolateFlushes;
  for (let i = 0; i < 10; i += 1) {
    await perfSetInput(perfXField, `0.${50 + i}`);
  }
  const twoItemFlushes = isolateFlushes - twoItemBefore;
  if (twoItemFlushes !== 0) {
    console.error("2-item stack x keystrokes triggered isolate flushes", twoItemFlushes);
    failed = true;
  }

  await perfClick("Clear");
  await act(async () => {
    perfRoot.unmount();
  });
  perfView.close();
  delete workerGlobal.Worker;

  // 2. Load after compute: compute ln(1+10^(-130)), then Load the 671-press word in exact mode.
  const e1Words = JSON.parse(readFileSync(new URL("./e1-words-v10.json", import.meta.url), "utf8")) as Record<string, string>;
  const ln130Word = e1Words["ln(1+10^(-130))"];
  if (!ln130Word || ln130Word.length !== 671) {
    console.error("missing 671-press word fixture for ln(1+10^(-130))");
    failed = true;
  } else {
    const loadDom = new JSDOM(`<!doctype html><html><body><div id="root"></div></body></html>`, {
      url: "http://localhost/",
      pretendToBeVisual: true,
    });
    const loadView = loadDom.window;
    globals.window = loadView;
    globals.self = loadView;
    globals.document = loadView.document;
    globals.HTMLElement = loadView.HTMLElement;
    const loadMount = loadView.document.getElementById("root")!;
    const loadRoot = createRoot(loadMount);
    await act(async () => {
      loadRoot.render(<EmlCalculator />);
    });
    const loadBtn = (label: string) =>
      [...loadView.document.querySelectorAll("button")].find((b) => b.textContent?.trim() === label) as HTMLButtonElement | undefined;
    const loadSet = async (el: HTMLInputElement, value: string) => {
      const setter = Object.getOwnPropertyDescriptor(loadView.HTMLInputElement.prototype, "value")?.set;
      await act(async () => {
        setter?.call(el, value);
        el.dispatchEvent(new loadView.Event("input", { bubbles: true }));
      });
    };
    const loadResult = () => loadView.document.querySelector(".ti-lcd-result")?.textContent ?? "";
    const waitExactDone = async () => {
      for (let i = 0; i < 200; i += 1) {
        const text = loadResult();
        const note = loadView.document.querySelector(".ti-lcd-note")?.textContent ?? "";
        if (text && text !== "computing" && text !== "0" && !note.includes("computing")) return text;
        await act(async () => {
          await new Promise((resolve) => setTimeout(resolve, 25));
        });
      }
      return loadResult();
    };

    const clearLoad = loadBtn("Clear");
    const exactLoad = loadBtn("exact");
    if (clearLoad) await act(async () => { clearLoad.click(); });
    if (exactLoad && exactLoad.getAttribute("aria-checked") !== "true") {
      await act(async () => { exactLoad.click(); });
    }
    const exprLoad = loadView.document.getElementById("expr") as HTMLInputElement;
    await loadSet(exprLoad, "ln(1+10^(-130))");
    await act(async () => { loadBtn("Compute")?.click(); });
    const computed130 = await waitExactDone();
    if (computed130 !== "1×10^−130") {
      console.error("compute ln(1+10^(-130)) did not produce 1×10^−130", computed130);
      failed = true;
    }

    const progLoad = loadView.document.querySelector("input[placeholder='#1, 001, or 11E']") as HTMLInputElement;
    await loadSet(progLoad, ln130Word);
    const flushesBeforeLoad = isolateFlushes;
    await act(async () => { loadBtn("Load")?.click(); });
    const flushesOnLoad = isolateFlushes - flushesBeforeLoad;
    const loaded130 = await waitExactDone();
    if (flushesOnLoad < 1) {
      console.error("Load path did not call isolateCircuit", flushesOnLoad);
      failed = true;
    }
    if (loaded130 !== "1×10^−130") {
      console.error("Load of 671-press word after compute did not equal fresh-process 1×10^−130", loaded130);
      failed = true;
    }

    await act(async () => {
      loadRoot.unmount();
    });
    loadView.close();
  }

  // 3. Second programIndexDigits on a K~1239 node takes under 0.1 ms, and non-default maxGates is not poisoned.
  const sinNode = compileExpression("sin(pi/6)", {});
  if (circuitStats(sinNode).rpnLength !== BigInt(1239)) {
    console.error("expected sin(pi/6) to be K 1239", circuitStats(sinNode).rpnLength.toString());
    failed = true;
  }
  const firstDigits = programIndexDigits(sinNode);
  const t0 = performance.now();
  const secondDigits = programIndexDigits(sinNode);
  const elapsedMs = performance.now() - t0;
  if (!firstDigits || secondDigits !== firstDigits || elapsedMs >= 0.1) {
    console.error("second programIndexDigits was wrong or slow", { ok: Boolean(firstDigits), same: secondDigits === firstDigits, elapsedMs });
    failed = true;
  }
  if (rankProgram(sinNode, 10) !== null || rankProgram(sinNode)?.toString() !== firstDigits) {
    console.error("rankProgram cache interacted with non-default maxGates");
    failed = true;
  }

  if (failed) process.exit(1);
  console.log("calculator smoke passed");
}

main().catch((err: unknown) => {
  console.error(err);
  process.exit(1);
});
