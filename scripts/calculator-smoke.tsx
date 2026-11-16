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
  if (!css.includes("max-height: 11rem") || !css.includes("max-height: 8.25rem") || !css.includes("orientation: landscape") || !css.includes("max-height: 500px")) {
    console.error("phone display cap or landscape layout is missing");
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
  if (!resultText().includes("2.718") || !built.includes("110")) {
    console.error("pressing 1, 1, EML did not build e", built);
    failed = true;
  }
  if (!built.includes("higher program number is a lower binary value")) {
    console.error("ordering legend missing after a key press", built);
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
  const exact = buttonByText("exact mode · 120 digits");
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
  const oneInTurn = view.document.querySelector(".ti-btn-one");
  const emlInTurn = view.document.querySelector(".ti-btn-eml");
  const sin = buttonByText("sin");
  const times = buttonByText("×");
  if (!(oneInTurn instanceof view.HTMLButtonElement) || !(emlInTurn instanceof view.HTMLButtonElement)) {
    console.error("missing 1 or EML for the one-turn press");
    failed = true;
  } else if (emlInTurn.disabled || emlInTurn.getAttribute("aria-disabled") !== "true") {
    console.error("empty stack should mark EML with aria-disabled and leave it clickable", emlInTurn.disabled, emlInTurn.getAttribute("aria-disabled"));
    failed = true;
  } else if (!(sin instanceof view.HTMLButtonElement) || sin.getAttribute("aria-disabled") !== "true" || sin.disabled) {
    console.error("empty stack should mark sin with aria-disabled", sin instanceof view.HTMLButtonElement ? sin.getAttribute("aria-disabled") : sin);
    failed = true;
  } else if (!(times instanceof view.HTMLButtonElement) || times.getAttribute("aria-disabled") !== "true" || times.disabled) {
    console.error("empty stack should mark × with aria-disabled", times instanceof view.HTMLButtonElement ? times.getAttribute("aria-disabled") : times);
    failed = true;
  } else {
    await act(async () => {
      sin.click();
    });
    const oneValue = view.document.querySelector(".ti-lcd-error")?.textContent ?? "";
    if (oneValue !== "Needs a value. Press 1 first.") {
      console.error("a one-value key on an empty stack used the wrong message", oneValue);
      failed = true;
    }
    await act(async () => {
      emlInTurn.click();
    });
    const twoValue = view.document.querySelector(".ti-lcd-error")?.textContent ?? "";
    if (twoValue !== "EML needs two values. Press 1 first.") {
      console.error("EML on an empty stack used the wrong message", twoValue);
      failed = true;
    }
    await act(async () => {
      const one = view.document.querySelector(".ti-btn-one");
      const eml = view.document.querySelector(".ti-btn-eml");
      if (!(one instanceof view.HTMLButtonElement) || !(eml instanceof view.HTMLButtonElement)) return;
      one.click();
      one.click();
      eml.click();
    });
    let raced = "";
    for (let i = 0; i < 80; i += 1) {
      raced = resultText().trim();
      if (raced === "2.718281828459") break;
      await act(async () => {
        await new Promise((resolve) => setTimeout(resolve, 25));
      });
    }
    if (raced !== "2.718281828459") {
      console.error("1, 1, EML in one turn did not build e", raced, screenText());
      failed = true;
    }
  }
  const program = view.document.querySelector("input[placeholder='#110, 110, or 11E']");
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
  const copyNumber = buttonByText("Copy #");
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

  const ui = new JSDOM(`<!doctype html><html><body><div id="root"></div></body></html>`, {
    url: "http://localhost/",
    pretendToBeVisual: true,
  });
  const uiView = ui.window;
  globals.window = uiView;
  globals.self = uiView;
  globals.document = uiView.document;
  globals.HTMLElement = uiView.HTMLElement;
  const uiMount = uiView.document.getElementById("root");
  if (!uiMount) {
    console.error("missing ui root");
    process.exit(1);
  }
  const uiRoot = createRoot(uiMount);
  await act(async () => {
    uiRoot.render(<EmlCalculator />);
  });
  const uiButton = (label: string) =>
    [...uiView.document.querySelectorAll("button")].find((button) => button.textContent?.trim() === label);
  const uiResult = () => uiView.document.querySelector(".ti-lcd-result")?.textContent ?? "";
  const uiAlert = () => uiView.document.querySelector("[role='alert']")?.textContent ?? "";
  const skip = uiButton("Skip");
  if (skip instanceof uiView.HTMLButtonElement) {
    await act(async () => {
      skip.click();
    });
  }
  await act(async () => {
    uiView.dispatchEvent(new uiView.KeyboardEvent("keydown", { key: "1", bubbles: true }));
  });
  await act(async () => {
    uiView.dispatchEvent(new uiView.KeyboardEvent("keydown", { key: "1", bubbles: true, repeat: true }));
  });
  if ((uiView.document.querySelector(".ti-tape")?.textContent ?? "") !== "1") {
    console.error("a repeated 1 key pushed more than once", uiView.document.querySelector(".ti-tape")?.textContent);
    failed = true;
  }
  const swap = uiButton("swap");
  if (!(swap instanceof uiView.HTMLButtonElement)) {
    console.error("missing swap");
    failed = true;
  } else {
    await act(async () => {
      swap.click();
    });
    const alert = uiView.document.querySelector(".ti-lcd-error");
    if (alert?.getAttribute("role") !== "alert" || !alert.textContent?.includes("Swap needs two values.")) {
      console.error("swap error is not in the alert region", alert?.getAttribute("role"), alert?.textContent);
      failed = true;
    }
    const expression = uiView.document.querySelector("#expression");
    if (expression instanceof uiView.HTMLElement) {
      await act(async () => {
        expression.dispatchEvent(new uiView.KeyboardEvent("keydown", { key: "Escape", bubbles: true }));
      });
      if ((uiView.document.querySelector(".ti-lcd-error")?.textContent ?? "") !== "") {
        console.error("Escape inside a field left the error up", uiView.document.querySelector(".ti-lcd-error")?.textContent);
        failed = true;
      }
    }
  }
  const pushY = uiButton("push y");
  if (!(pushY instanceof uiView.HTMLButtonElement)) {
    console.error("missing push y");
    failed = true;
  } else {
    await act(async () => {
      pushY.dispatchEvent(new uiView.PointerEvent("pointerdown", { bubbles: true, button: 0, clientX: 0, clientY: 0, pointerId: 1 }));
    });
    await act(async () => {
      await new Promise((resolve) => setTimeout(resolve, 520));
    });
    await act(async () => {
      pushY.dispatchEvent(new uiView.PointerEvent("pointerup", { bubbles: true, button: 0, clientX: 0, clientY: 0, pointerId: 1 }));
      pushY.dispatchEvent(new uiView.MouseEvent("click", { bubbles: true, button: 0 }));
    });
    const hint = uiView.document.querySelector(".ti-lcd-hold")?.textContent ?? "";
    if (!hint.includes("Push the value of y") || uiResult().includes("2")) {
      console.error("a long-press both hinted and pushed y", hint, uiResult());
      failed = true;
    }
    await act(async () => {
      pushY.click();
    });
    let afterShort = "";
    for (let i = 0; i < 40; i += 1) {
      afterShort = uiResult();
      if (afterShort.includes("2")) break;
      await act(async () => {
        await new Promise((resolve) => setTimeout(resolve, 25));
      });
    }
    if (!afterShort.includes("2") || (uiView.document.querySelector(".ti-lcd-hold")?.textContent ?? "") !== "") {
      console.error("a short press after a long-press did not push y or left the hint", afterShort, uiView.document.querySelector(".ti-lcd-hold")?.textContent);
      failed = true;
    }
  }
  const setUiProgram = async (value: string) => {
    const program = uiView.document.querySelector("input[placeholder='#110, 110, or 11E']");
    if (!(program instanceof uiView.HTMLInputElement)) {
      console.error("missing program field");
      failed = true;
      return;
    }
    const setter = Object.getOwnPropertyDescriptor(uiView.HTMLInputElement.prototype, "value")?.set;
    await act(async () => {
      setter?.call(program, value);
      program.dispatchEvent(new uiView.Event("input", { bubbles: true }));
    });
  };
  const loadUi = async () => {
    const load = uiButton("Load");
    if (!(load instanceof uiView.HTMLButtonElement)) {
      console.error("missing Load");
      failed = true;
      return;
    }
    await act(async () => {
      load.click();
    });
  };
  await setUiProgram("xyE");
  await loadUi();
  if (!uiAlert().includes("free input") || uiAlert().toLowerCase().includes("cancelled")) {
    console.error("xyE without free input was not rejected clearly", uiAlert());
    failed = true;
  }
  const free = uiView.document.querySelector("input[type='checkbox']");
  if (!(free instanceof uiView.HTMLInputElement)) {
    console.error("missing free input");
    failed = true;
  } else {
    await act(async () => {
      free.click();
    });
    await setUiProgram("xyE");
    await loadUi();
    let loaded = "";
    for (let i = 0; i < 80; i += 1) {
      loaded = uiResult();
      if (loaded.includes("0.955")) break;
      await act(async () => {
        await new Promise((resolve) => setTimeout(resolve, 25));
      });
    }
    const note = uiView.document.querySelector(".ti-lcd-note")?.textContent ?? "";
    if (!loaded.includes("0.955") || note.includes("cancelled") || uiAlert().includes("needs a value")) {
      console.error("xyE did not use x and y", loaded, note, uiAlert());
      failed = true;
    }
  }
  await setUiProgram(`${"1".repeat(20_001)}${"E".repeat(20_000)}`);
  await loadUi();
  if (!uiAlert().includes("too long") || uiAlert().toLowerCase().includes("cancelled")) {
    console.error("a huge word was not rejected before it was built", uiAlert());
    failed = true;
  }
  const expression = uiView.document.querySelector("#expression");
  const compute = uiView.document.querySelector("button[aria-label='Compute']");
  const typeExpr = async (value: string) => {
    if (!(expression instanceof uiView.HTMLInputElement) || !(compute instanceof uiView.HTMLButtonElement)) {
      console.error("missing expression");
      failed = true;
      return;
    }
    const setter = Object.getOwnPropertyDescriptor(uiView.HTMLInputElement.prototype, "value")?.set;
    await act(async () => {
      setter?.call(expression, value);
      expression.dispatchEvent(new uiView.Event("input", { bubbles: true }));
    });
    await act(async () => {
      compute.click();
    });
  };
  await typeExpr("😀");
  const emojiError = uiView.document.querySelector(".ti-field-error")?.textContent ?? "";
  if (!emojiError.includes("😀") || emojiError.includes("“\ud83d”")) {
    console.error("emoji parse error split the character", emojiError);
    failed = true;
  }
  await typeExpr("1)");
  const parenError = uiView.document.querySelector(".ti-field-error")?.textContent ?? "";
  if (!parenError.includes("Unexpected") || parenError.includes("Missing")) {
    console.error("an extra ) was called missing", parenError);
    failed = true;
  }
  await typeExpr("sin pi/6");
  const sinError = uiView.document.querySelector(".ti-field-error")?.textContent ?? "";
  if (!sinError.toLowerCase().includes("parentheses")) {
    console.error("sin without parentheses was an unknown name", sinError);
    failed = true;
  }
  let stored = "";
  let denyClip = false;
  Object.defineProperty(uiView.navigator, "clipboard", {
    configurable: true,
    value: {
      writeText: async (value: string) => {
        if (denyClip) throw new uiView.DOMException("denied", "NotAllowedError");
        stored = value;
      },
    },
  });
  const clearUi = uiButton("Clear");
  if (clearUi instanceof uiView.HTMLButtonElement) {
    await act(async () => {
      clearUi.click();
    });
  }
  const kept = uiView.document.querySelector("#expression");
  if (!(kept instanceof uiView.HTMLInputElement) || kept.value !== "sin pi/6") {
    console.error("Clear wiped the expression", kept instanceof uiView.HTMLInputElement ? kept.value : kept);
    failed = true;
  }
  const one = uiView.document.querySelector(".ti-btn-one");
  if (one instanceof uiView.HTMLButtonElement) {
    await act(async () => {
      one.click();
    });
  }
  const copyValue = uiButton("Copy value");
  if (!(copyValue instanceof uiView.HTMLButtonElement)) {
    console.error("missing copy value");
    failed = true;
  } else {
    await act(async () => {
      copyValue.click();
      await new Promise((resolve) => setTimeout(resolve, 0));
    });
    if (stored !== "1" || copyValue.textContent?.trim() !== "Copied") {
      console.error("copy value did not copy the shown number", stored, copyValue.textContent);
      failed = true;
    }
    await act(async () => {
      await new Promise((resolve) => setTimeout(resolve, 2100));
    });
    if (uiButton("Copy value")?.textContent?.trim() !== "Copy value") {
      console.error("Copied did not reset", uiButton("Copy value")?.textContent);
      failed = true;
    }
    denyClip = true;
    await act(async () => {
      uiButton("Copy value")?.dispatchEvent(new uiView.MouseEvent("click", { bubbles: true }));
      await new Promise((resolve) => setTimeout(resolve, 0));
    });
    if (!uiAlert().includes("denied")) {
      console.error("a denied clipboard was silent", uiAlert());
      failed = true;
    }
  }
  await act(async () => {
    uiRoot.unmount();
  });
  uiView.close();

  class ErrorWorker {
    onmessage: ((event: { data: unknown }) => void) | null = null;
    onerror: (() => void) | null = null;
    postMessage(data: { request: number }) {
      setTimeout(() => {
        this.onmessage?.({
          data: { type: "error", request: data.request, message: "This circuit is too large for exact mode." },
        });
      }, 0);
    }
    terminate() {}
  }
  const errorGlobal = globalThis as unknown as { Worker?: typeof ErrorWorker };
  errorGlobal.Worker = ErrorWorker;
  const limit = new JSDOM(`<!doctype html><html><body><div id="root"></div></body></html>`, {
    url: "http://localhost/",
    pretendToBeVisual: true,
  });
  const limitView = limit.window;
  globals.window = limitView;
  globals.self = limitView;
  globals.document = limitView.document;
  globals.HTMLElement = limitView.HTMLElement;
  const limitMount = limitView.document.getElementById("root");
  if (!limitMount) {
    console.error("missing limit root");
    process.exit(1);
  }
  const limitRoot = createRoot(limitMount);
  await act(async () => {
    limitRoot.render(<EmlCalculator />);
  });
  const limitClick = async (selector: string) => {
    const button = limitView.document.querySelector(selector);
    if (!(button instanceof limitView.HTMLButtonElement)) return;
    await act(async () => {
      button.click();
    });
  };
  await limitClick(".ti-btn-one");
  await limitClick(".ti-btn-one");
  await limitClick(".ti-btn-eml");
  let limitText = "";
  for (let i = 0; i < 20; i += 1) {
    limitText = limitView.document.querySelector(".ti-lcd-error")?.textContent ?? "";
    if (limitText.includes("too large")) break;
    await act(async () => {
      await new Promise((resolve) => setTimeout(resolve, 20));
    });
  }
  const limitNote = limitView.document.querySelector(".ti-lcd-note")?.textContent ?? "";
  if (!limitText.includes("too large") || limitNote.includes("cancelled") || limitText.toLowerCase().includes("cancelled")) {
    console.error("an exact error was labelled cancelled", limitText, limitNote);
    failed = true;
  }
  await act(async () => {
    limitRoot.unmount();
  });
  limitView.close();
  delete errorGlobal.Worker;

  process.env.PAGES_BASE_PATH = "/eml-and-one";
  const manifestMod = await import("../app/manifest");
  const manifest = manifestMod.default();
  delete process.env.PAGES_BASE_PATH;
  if (manifest.orientation !== "portrait" || manifest.start_url !== "/eml-and-one/" || manifest.scope !== "/eml-and-one/" || manifest.display !== "standalone") {
    console.error("manifest is missing the portrait lock or the Pages base path", manifest);
    failed = true;
  }

  if (failed) process.exit(1);
  console.log("calculator smoke passed");
}

main().catch((err: unknown) => {
  console.error(err);
  process.exit(1);
});
