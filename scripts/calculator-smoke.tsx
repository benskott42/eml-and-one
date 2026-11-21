import { readFileSync } from "node:fs";
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
  await act(async () => {
    preemptRoot.unmount();
  });
  preemptView.close();
  delete workerGlobal.Worker;

  if (failed) process.exit(1);
  console.log("calculator smoke passed");
}

main().catch((err: unknown) => {
  console.error(err);
  process.exit(1);
});
