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
  if (!css.includes("max-height: 11rem") || !css.includes("max-height: 10.25rem") || !css.includes("orientation: landscape") || !css.includes("max-height: 500px") || !css.includes("100svh") || !css.includes("overflow-y: auto")) {
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
  if (!view.document.querySelector("[aria-label='First visit']")) {
    console.error("welcome card missing on a first visit");
    failed = true;
  }
  await click(".ti-btn-one");
  if (view.document.querySelector("[aria-label='First visit']")) {
    console.error("welcome card stayed after the first key");
    failed = true;
  }
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
  const bareDash = () => {
    const text = uiResult().replace(/\s+/g, " ").trim();
    if (text !== "—") return;
    if (!uiAlert().trim()) {
      console.error("a result was a bare dash with no reason");
      failed = true;
    }
  };
  const fortyThousand = `${"1 ".repeat(20_001)}${"E ".repeat(20_000)}`;
  await setUiProgram(fortyThousand);
  await loadUi();
  const fortyScreen = uiView.document.querySelector("[aria-label='Calculator screen']")?.textContent ?? "";
  if (uiAlert().includes("Too long") || !fortyScreen.includes("40001 presses")) {
    console.error("a 40,001-press word with spaces did not load", uiAlert(), fortyScreen.slice(0, 240));
    failed = true;
  }
  const clearLoaded = uiButton("Clear");
  if (clearLoaded instanceof uiView.HTMLButtonElement) {
    await act(async () => {
      clearLoaded.click();
    });
  }
  await setUiProgram(`${"1".repeat(25_001)}${"E".repeat(25_000)}`);
  await loadUi();
  const waitComputed = async (mode: string) => {
    let text = "";
    let alert = "";
    for (let i = 0; i < 800; i += 1) {
      text = uiResult().replace(/\s+/g, " ").trim();
      alert = uiAlert().trim();
      bareDash();
      if (text && text !== "computing" && !text.startsWith("Stack empty") && (text !== "—" || alert)) break;
      await act(async () => {
        await new Promise((resolve) => setTimeout(resolve, 50));
      });
    }
    if (!text || text === "computing" || text.startsWith("Stack empty") || (text === "—" && !alert)) {
      console.error(`a 50,001-press word did not compute in ${mode}`, text, alert);
      failed = true;
    }
  };
  await waitComputed("exact mode");
  const floatMode = uiButton("float (hardware)");
  if (!(floatMode instanceof uiView.HTMLButtonElement)) {
    console.error("missing float mode");
    failed = true;
  } else {
    await act(async () => {
      floatMode.click();
    });
    await waitComputed("float mode");
  }
  await setUiProgram("1".repeat(50_003));
  await loadUi();
  if (uiAlert() !== "Too long: words are limited to 50,001 presses.") {
    console.error("a 50,003-press word was not refused with the limit", uiAlert());
    failed = true;
  }
  const paste = "1".repeat(400_000);
  await setUiProgram(paste);
  const pasteStarted = performance.now();
  await loadUi();
  const pasteMs = performance.now() - pasteStarted;
  if (uiAlert() !== "Too long: words are limited to 50,001 presses." || pasteMs > 100) {
    console.error("a 400k paste was not rejected quickly", pasteMs, uiAlert());
    failed = true;
  }
  await setUiProgram(`#${"1".repeat(50_002)}`);
  if (uiAlert() !== "Too long: program numbers are limited to 50,001 digits.") {
    console.error("a long program number was refused as presses", uiAlert());
    failed = true;
  }
  const storedProgram = uiView.document.querySelector("input[placeholder='#110, 110, or 11E']");
  if (storedProgram instanceof uiView.HTMLInputElement && storedProgram.value.length > 50_001) {
    console.error("an oversized word stayed in the program field", storedProgram.value.length);
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
  const limitResult = (limitView.document.querySelector(".ti-lcd-result")?.textContent ?? "").replace(/\s+/g, " ").trim();
  if (!limitText.includes("too large") || limitNote.includes("cancelled") || limitText.toLowerCase().includes("cancelled")) {
    console.error("an exact error was labelled cancelled", limitText, limitNote);
    failed = true;
  }
  if (limitResult === "—" && !limitText.trim()) {
    console.error("an exact dash had no reason", limitResult, limitText);
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
  const iconSrcs = (manifest.icons ?? []).map((icon) => icon.src);
  if (manifest.orientation !== "portrait" || manifest.start_url !== "/eml-and-one/" || manifest.scope !== "/eml-and-one/" || manifest.display !== "standalone") {
    console.error("manifest is missing the portrait lock or the Pages base path", manifest);
    failed = true;
  }
  if (!iconSrcs.includes("/eml-and-one/icon-192.png") || !iconSrcs.includes("/eml-and-one/icon-512.png") || !iconSrcs.some((src) => src.includes("icon-maskable-512.png") && src.startsWith("/eml-and-one/"))) {
    console.error("manifest icons are missing the Pages base path", manifest.icons);
    failed = true;
  }
  const { displayedCopy } = await import("../components/calculator/chrome");
  const { runNode, resultError } = await import("../components/calculator/screen");
  const { nodeFromRpn } = await import("../lib/eml/node");
  const copyCases: { shown: string; text: string; approximate: boolean }[] = [
    { shown: "1.25×10^16 ≈", text: "1.25e16", approximate: true },
    { shown: "1×10^−8 ≈", text: "1e-8", approximate: true },
    { shown: "−1×10^−40", text: "-1e-40", approximate: false },
    { shown: "1.414213562373 − 0.000314159265i", text: "1.414213562373-0.000314159265i", approximate: false },
    { shown: "1 + 0.000314159265i ≈", text: "1+0.000314159265i", approximate: true },
    { shown: "−2.5", text: "-2.5", approximate: false },
    { shown: "1", text: "1", approximate: false },
    { shown: `1${"\u200b"}000`, text: "1000", approximate: false },
  ];
  for (const sample of copyCases) {
    const got = displayedCopy(sample.shown);
    if (got.text !== sample.text || got.approximate !== sample.approximate) {
      console.error("copy formatter mismatch", sample, got);
      failed = true;
    }
  }
  const digits = (BigInt(2) ** BigInt(300)).toString();
  const withBreaks = `${digits.replace(/(.{20})(?=.)/g, "$1\u200b")}\u2060\u00ad\u2009`;
  const big = displayedCopy(withBreaks);
  const complexCopy = displayedCopy("1.414213562373 − 0.000314159265i");
  const exponentCopy = displayedCopy("1.234568×10^20 ≈");
  const ascii = /^[\x20-\x7e]+$/;
  if (big.text !== digits || big.approximate || !ascii.test(big.text)) {
    console.error("2^300 copy kept a hidden break", big.text.length, digits.length, big.text);
    failed = true;
  }
  if (complexCopy.text !== "1.414213562373-0.000314159265i" || !ascii.test(complexCopy.text)) {
    console.error("complex copy was not clean ASCII", complexCopy);
    failed = true;
  }
  if (exponentCopy.text !== "1.234568e20" || !exponentCopy.approximate || !ascii.test(exponentCopy.text)) {
    console.error("exponent copy was not clean ASCII", exponentCopy);
    failed = true;
  }
  const infinityCopy = displayedCopy("∞");
  const negativeInfinityCopy = displayedCopy("−∞");
  if (infinityCopy.text !== "Infinity" || negativeInfinityCopy.text !== "-Infinity") {
    console.error("infinity copy was not ASCII", infinityCopy, negativeInfinityCopy);
    failed = true;
  }
  const { compileExpression } = await import("../lib/eml/parse");
  const { copiedValue } = await import("../components/calculator/chrome");
  const floatOf = (expr: string) => {
    const row = runNode(compileExpression(expr, {}), "float");
    return { row, copied: copiedValue({ shown: row.text, value: row.value, overflowed: row.overflowed }) };
  };
  const floatPower = floatOf("2^300");
  if (
    floatPower.copied.text.includes("i") ||
    Number(floatPower.copied.text) !== floatPower.row.value.re ||
    !floatPower.copied.copiedLabel.includes("≈ not certified")
  ) {
    console.error("float 2^300 copy was not the shown double", floatPower.copied, floatPower.row.value.re, floatPower.row.text);
    failed = true;
  }
  const tiny = floatOf("10^(-8)");
  if (tiny.copied.text !== "1e-8" || tiny.copied.text.includes("i") || !tiny.copied.copiedLabel.includes("≈ not certified")) {
    console.error("float 10^(-8) did not copy the shown power", tiny.copied, tiny.row.value);
    failed = true;
  }
  const half = floatOf("sin(pi/6)");
  if (half.copied.text !== "0.5") {
    console.error("sin(pi/6) did not copy the snapped 0.5", half.copied, half.row.text);
    failed = true;
  }
  const underflowed = floatOf("10^(-400)");
  const positiveReal = !Object.is(underflowed.row.value.re, -0) && !(underflowed.row.value.re < 0);
  if (
    underflowed.row.text !== "0 ≈" ||
    underflowed.copied.text !== "0" ||
    Number(underflowed.copied.text) !== underflowed.row.value.re ||
    !positiveReal ||
    !underflowed.row.underflowed ||
    !underflowed.copied.copiedLabel.includes("≈ not certified")
  ) {
    console.error("float 10^(-400) kept a spurious minus", underflowed.row.text, underflowed.copied, underflowed.row.value);
    failed = true;
  }
  const negativeUnder = floatOf("(0-1)*exp(-1000)");
  const negativeReal = Object.is(negativeUnder.row.value.re, -0) || negativeUnder.row.value.re < 0 || Object.is(1 / negativeUnder.row.value.re, -Infinity);
  if (!negativeReal || negativeUnder.row.text !== "−0 ≈" || negativeUnder.copied.text !== "-0") {
    console.error("a negative underflow lost its sign", negativeUnder.row.text, negativeUnder.copied, negativeUnder.row.value.re);
    failed = true;
  }
  const overflow = floatOf("exp(710)");
  if (overflow.copied.text !== "Infinity" || !overflow.copied.copiedLabel.includes("≈ not certified") || !overflow.row.overflowed) {
    console.error("an overflowed infinity was copied as certified", overflow.copied, overflow.row.text, overflow.row.overflowed);
    failed = true;
  }
  const nan = floatOf("0/0");
  if (nan.copied.text !== "NaN" || nan.copied.text.includes("i")) {
    console.error("NaN copied a hidden imaginary part", nan.copied, nan.row.text);
    failed = true;
  }
  const exactNan = copiedValue({ shown: "undefined", node: compileExpression("0/0", {}) });
  if (exactNan.text !== "NaN") {
    console.error("exact 0/0 copied a name", exactNan);
    failed = true;
  }
  const hugeWant = (BigInt(10) ** BigInt(4100) + BigInt(1)).toString();
  const hugeCopy = copiedValue({ shown: "1×10^4100", node: compileExpression("10^4100+1", {}) });
  if (hugeCopy.text !== hugeWant || hugeCopy.copiedLabel !== "Copied") {
    console.error("10^4100+1 did not copy the exact integer", hugeCopy.text.slice(-6), hugeCopy.copiedLabel);
    failed = true;
  }
  const pow400 = (BigInt(10) ** BigInt(400)).toString();
  const copy400 = copiedValue({ shown: "1×10^400", node: compileExpression("10^400", {}) });
  if (copy400.text !== pow400 || copy400.text.length !== 401 || copy400.copiedLabel !== "Copied" || copy400.text === "1e400") {
    console.error("10^400 did not copy all 401 digits", copy400.text.length, copy400.text.slice(0, 8), copy400.copiedLabel);
    failed = true;
  }
  const oneDigit = copiedValue({ shown: "1×10^20", node: compileExpression("pi*10^20", {}) });
  if (oneDigit.text !== "1e20" || oneDigit.copiedLabel !== "Copied as shown (1 digit)") {
    console.error("a one-digit screen copy used the plural", oneDigit);
    failed = true;
  }
  const signedZero = runNode(compileExpression("-0", {}), "float");
  if (signedZero.text !== "−0") {
    console.error("a real negative zero was rewritten", signedZero.text);
    failed = true;
  }
  const sparseNode = compileExpression("10^130+1", {});
  const sparseStarted = performance.now();
  const sparseCopy = copiedValue({ shown: "1×10^130", node: sparseNode });
  const sparseMs = performance.now() - sparseStarted;
  const sparseWant = (BigInt(10) ** BigInt(130) + BigInt(1)).toString();
  if (sparseCopy.text !== sparseWant || !sparseCopy.text.endsWith("1") || sparseCopy.copiedLabel !== "Copied" || sparseMs > 50) {
    console.error("10^130+1 did not copy the proven integer", sparseCopy.text.slice(-4), sparseCopy.copiedLabel, sparseMs);
    failed = true;
  }
  const expCopy = copiedValue({ shown: "1.942426395241×10^130", node: compileExpression("exp(300)", {}) });
  if (expCopy.copiedLabel !== "Copied as shown (13 digits)" || expCopy.text !== "1.942426395241e130" || /^\d{20,}$/.test(expCopy.text)) {
    console.error("exp(300) copied a rounded integer", expCopy);
    failed = true;
  }
  const halfPower = copiedValue({ shown: "1.071508607186×10^301", node: compileExpression("2^1000+0.5", {}) });
  if (
    !halfPower.copiedLabel.startsWith("Copied as shown") ||
    halfPower.text === (BigInt(2) ** BigInt(1000)).toString() ||
    /^\d{20,}$/.test(halfPower.text)
  ) {
    console.error("2^1000+0.5 copied a rounded integer", halfPower);
    failed = true;
  }
  const exactPower = copiedValue({ shown: "2.037036×10^90", node: compileExpression("2^300", {}) });
  if (exactPower.text !== digits || exactPower.copiedLabel !== "Copied") {
    console.error("exact 2^300 did not copy the proven integer", exactPower.text.length, exactPower.copiedLabel);
    failed = true;
  }
  const limitNode = nodeFromRpn(`${"1".repeat(80)}${"E".repeat(79)}`.split(""));
  const limited = runNode(limitNode, "float", { maxNodes: 1 });
  const limitedReason = resultError({ ...limited, node: limitNode, caption: "limit" });
  if (limited.text !== "—" || limited.notice !== "too large to evaluate in float" || limitedReason !== "too large to evaluate in float") {
    console.error("float limit did not explain the dash", limited.text, limited.notice, limitedReason);
    failed = true;
  }

  const { EARLY_KEY_SCRIPT } = await import("../components/calculator/earlyKeys");
  const earlyDom = new JSDOM("<!doctype html><html><body><button class=\"ti-btn-one\">1</button><div id=\"root\"></div></body></html>", {
    url: "http://localhost/",
    pretendToBeVisual: true,
  });
  const earlyView = earlyDom.window;
  globals.window = earlyView;
  globals.self = earlyView;
  globals.document = earlyView.document;
  globals.HTMLElement = earlyView.HTMLElement;
  earlyView.eval(EARLY_KEY_SCRIPT);
  const earlyButton = earlyView.document.querySelector(".ti-btn-one");
  earlyButton?.dispatchEvent(new earlyView.MouseEvent("click", { bubbles: true, cancelable: true }));
  earlyView.document.dispatchEvent(new earlyView.KeyboardEvent("keydown", { key: "1", bubbles: true, cancelable: true }));
  const earlyMount = earlyView.document.getElementById("root");
  if (!earlyMount || !earlyButton) {
    console.error("missing early-press root");
    failed = true;
  } else {
    const earlyRoot = createRoot(earlyMount);
    await act(async () => {
      earlyRoot.render(<EmlCalculator />);
    });
    const replayed = earlyView.document.querySelectorAll(".ti-lcd-stack p").length;
    if (earlyView.document.querySelector("[aria-label='First visit']")) {
      console.error("an early click left the welcome card open");
      failed = true;
    }
    if (replayed !== 1 || earlyView.document.querySelector(".ti-lcd-result")?.textContent?.trim() !== "1") {
      console.error("an early click and key were not replayed once", replayed, earlyView.document.querySelector(".ti-lcd-result")?.textContent);
      failed = true;
    }
    await act(async () => {
      earlyView.document.dispatchEvent(new earlyView.KeyboardEvent("keydown", { key: "1", bubbles: true, cancelable: true }));
    });
    const afterLive = earlyView.document.querySelectorAll(".ti-lcd-stack p").length;
    if (afterLive !== 2) {
      console.error("a later key press was doubled or dropped", afterLive);
      failed = true;
    }
    await act(async () => {
      earlyRoot.unmount();
    });
  }
  earlyView.close();
  const editDom = new JSDOM("<!doctype html><html><body><button class=\"ti-btn-one\">1</button><div id=\"root\"></div></body></html>", {
    url: "http://localhost/",
    pretendToBeVisual: true,
  });
  const editView = editDom.window;
  globals.window = editView;
  globals.self = editView;
  globals.document = editView.document;
  globals.HTMLElement = editView.HTMLElement;
  editView.eval(EARLY_KEY_SCRIPT);
  editView.document.querySelector(".ti-btn-one")?.dispatchEvent(new editView.MouseEvent("click", { bubbles: true, cancelable: true }));
  editView.document.dispatchEvent(new editView.KeyboardEvent("keydown", { key: "Backspace", bubbles: true, cancelable: true }));
  editView.document.dispatchEvent(new editView.KeyboardEvent("keydown", { key: "Enter", bubbles: true, cancelable: true }));
  const editMount = editView.document.getElementById("root");
  if (!editMount) {
    console.error("missing early edit root");
    failed = true;
  } else {
    const editRoot = createRoot(editMount);
    await act(async () => {
      editRoot.render(<EmlCalculator />);
    });
    const edited = editView.document.querySelector(".ti-lcd-result")?.textContent?.trim();
    if (edited !== "Stack empty. Press 1.") {
      console.error("an early Enter on the page computed", edited);
      failed = true;
    }
    await act(async () => {
      editRoot.unmount();
    });
  }
  editView.close();
  const typedDom = new JSDOM("<!doctype html><html><body><input id=\"expression\" value=\"2^10\"><div id=\"root\"></div></body></html>", {
    url: "http://localhost/",
    pretendToBeVisual: true,
  });
  const typedView = typedDom.window;
  globals.window = typedView;
  globals.self = typedView;
  globals.document = typedView.document;
  globals.HTMLElement = typedView.HTMLElement;
  typedView.eval(EARLY_KEY_SCRIPT);
  typedView.document.getElementById("expression")?.dispatchEvent(new typedView.KeyboardEvent("keydown", { key: "Enter", bubbles: true, cancelable: true }));
  const typedMount = typedView.document.getElementById("root");
  if (!typedMount) {
    console.error("missing early expression root");
    failed = true;
  } else {
    const typedRoot = createRoot(typedMount);
    await act(async () => {
      typedRoot.render(<EmlCalculator />);
    });
    const typedResult = typedView.document.querySelector(".ti-lcd-result")?.textContent?.trim();
    const typedField = typedView.document.querySelector("#expression");
    const typedValue = typedField instanceof typedView.HTMLInputElement ? typedField.value : "";
    if (typedValue !== "2^10" || typedResult === "0.5" || typedResult === "sin(pi/6)") {
      console.error("an early Enter lost the typed expression", typedResult, typedValue);
      failed = true;
    }
    await act(async () => {
      typedRoot.unmount();
    });
  }
  typedView.close();
  globals.window = uiView;
  globals.self = uiView;
  globals.document = uiView.document;
  globals.HTMLElement = uiView.HTMLElement;

  const escapeDom = new JSDOM("<!doctype html><html><body><div id=\"root\"></div></body></html>", {
    url: "http://localhost/",
    pretendToBeVisual: true,
  });
  const escapeView = escapeDom.window;
  globals.window = escapeView;
  globals.self = escapeView;
  globals.document = escapeView.document;
  globals.HTMLElement = escapeView.HTMLElement;
  const escapeMount = escapeView.document.getElementById("root");
  if (!escapeMount) {
    console.error("missing escape root");
    failed = true;
  } else {
    const escapeRoot = createRoot(escapeMount);
    await act(async () => {
      escapeRoot.render(<EmlCalculator />);
    });
    if (!escapeView.document.querySelector("[aria-label='First visit']")) {
      console.error("welcome card missing before Escape");
      failed = true;
    }
    await act(async () => {
      escapeView.dispatchEvent(new escapeView.KeyboardEvent("keydown", { key: "Escape", bubbles: true }));
    });
    if (escapeView.document.querySelector("[aria-label='First visit']")) {
      console.error("Escape left the welcome card up");
      failed = true;
    }
    await act(async () => {
      escapeRoot.unmount();
    });
  }
  escapeView.close();

  if (failed) process.exit(1);
  console.log("calculator smoke passed");
}

main().catch((err: unknown) => {
  console.error(err);
  process.exit(1);
});
