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
    // One tab stop in the mode radio group: the checked radio.
    'role="radio" aria-checked="false" tabindex="-1"',
    'role="radio" aria-checked="true" tabindex="0"',
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
  // A closed fold carries no text once the page is live (the static HTML above has it),
  // and keeps it after it is opened: the browser would otherwise shape about 3,000
  // characters per closed fold when something reads the page.
  const foldNames = ["Branch, subtraction, and infinity", "Known float limits", "How ln is only 1 and EML"];
  const folds = ([...view.document.querySelectorAll("details.ti-fold")] as HTMLDetailsElement[]).filter((fold) =>
    foldNames.includes(fold.querySelector("summary")?.textContent ?? ""),
  );
  if (folds.length !== 3 || folds.some((fold) => fold.querySelector("p, ul"))) {
    console.error("closed folds still hold their text after mount", folds.map((fold) => fold.querySelectorAll("p, ul").length));
    failed = true;
  }
  const limits = folds.find((fold) => fold.querySelector("summary")?.textContent === "Known float limits");
  if (limits) {
    await act(async () => {
      limits.open = true;
      limits.dispatchEvent(new view.Event("toggle"));
    });
    if (!limits.textContent?.includes("pressing the circuit runs the same gates")) {
      console.error("an opened fold did not show its text");
      failed = true;
    }
    await act(async () => {
      limits.open = false;
      limits.dispatchEvent(new view.Event("toggle"));
    });
    if (!limits.textContent?.includes("pressing the circuit runs the same gates")) {
      console.error("a closed fold dropped the text it showed when it was opened");
      failed = true;
    }
  } else {
    console.error("missing the Known float limits fold");
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
  // There is no clipboard outside a secure context (nor in jsdom). Copy must not throw.
  const thrown: string[] = [];
  const onError = (event: ErrorEvent) => {
    thrown.push(String(event.error ?? event.message));
    event.preventDefault();
  };
  view.addEventListener("error", onError);
  const pressCopy = buttonByText("Copy");
  if (!(pressCopy instanceof view.HTMLButtonElement)) {
    console.error("pi's press line has no Copy button", screenText());
    failed = true;
  } else {
    await act(async () => {
      pressCopy.click();
    });
  }
  view.removeEventListener("error", onError);
  if (thrown.length > 0) {
    console.error("Copy without a clipboard threw", thrown);
    failed = true;
  }
  // A word of x and y reads the x and y fields, in exact as in float.
  const xField = view.document.querySelector(".ti-fields input");
  if (!(xField instanceof view.HTMLInputElement)) {
    console.error("missing x field");
    failed = true;
  } else {
    const setter = Object.getOwnPropertyDescriptor(view.HTMLInputElement.prototype, "value")?.set;
    await act(async () => {
      setter?.call(xField, "2");
      xField.dispatchEvent(new view.Event("input", { bubbles: true }));
    });
  }
  await setProgram("1xE");
  await clickNamed("Load");
  await waitResult();
  if (!resultText().includes("2.025134647") || screenText().includes("needs a value for x")) {
    console.error("the word 1xE did not read x = 2 in exact mode", resultText(), screenText());
    failed = true;
  }
  // Exact mode uses the parsed circuit for x in a loaded word, not a rounded float64:
  // with x = 1e-400, float64 underflows x to 0 (giving +∞), while exact gives e + 400·ln 10 ≈ 923.752.
  if (xField instanceof view.HTMLInputElement) {
    const setter = Object.getOwnPropertyDescriptor(view.HTMLInputElement.prototype, "value")?.set;
    await act(async () => {
      setter?.call(xField, "1e-400");
      xField.dispatchEvent(new view.Event("input", { bubbles: true }));
    });
    await setProgram("1xE");
    await clickNamed("Load");
    await waitResult();
    if (!resultText().includes("923.752")) {
      console.error("the word 1xE collapsed x = 1e-400 to float64 in exact mode", resultText(), screenText());
      failed = true;
    }
    await act(async () => {
      setter?.call(xField, "2");
      xField.dispatchEvent(new view.Event("input", { bubbles: true }));
    });
    await setProgram("1xE");
    await clickNamed("Load");
    await waitResult();
  }
  await clickNamed("hardware");
  await waitResult();
  if (!resultText().includes("2.025134647") || screenText().includes("needs a value for x")) {
    console.error("the word 1xE did not read x = 2 in float mode", resultText(), screenText());
    failed = true;
  }
  // A rotated program loaded in hardware mode keeps its rotation notice after compare runs.
  await setProgram("E11");
  await clickNamed("Load");
  await act(async () => {
    await new Promise((resolve) => setTimeout(resolve, 60));
  });
  if (!screenText().includes("Rotated E11 to 11E.")) {
    console.error("rotated word notice was lost in hardware mode", screenText());
    failed = true;
  }
  await clickNamed("exact");
  await waitResult();
  // A long-press caption goes with the next press.
  const sinKey = buttonByText("sin");
  if (!(sinKey instanceof view.HTMLButtonElement)) {
    console.error("missing sin");
    failed = true;
  } else {
    await act(async () => {
      sinKey.dispatchEvent(new view.Event("pointerdown", { bubbles: true }));
      await new Promise((resolve) => setTimeout(resolve, 520));
      view.dispatchEvent(new view.Event("pointerup"));
      sinKey.click();
    });
    const shown = view.document.querySelector(".ti-lcd-hold")?.textContent ?? "";
    await act(async () => {
      view.dispatchEvent(new view.KeyboardEvent("keydown", { key: "1", bubbles: true }));
    });
    const after = view.document.querySelector(".ti-lcd-hold");
    if (!shown.startsWith("sin") || after) {
      console.error("a long-press caption stayed after the next press", shown, after?.textContent);
      failed = true;
    }
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

  // A worker that answers only when told to, so a row stays computing.
  class ManualWorker {
    static made: ManualWorker[] = [];
    onmessage: ((event: { data: unknown }) => void) | null = null;
    onerror: (() => void) | null = null;
    terminated = false;
    jobs: number[] = [];
    constructor() {
      ManualWorker.made.push(this);
    }
    postMessage(data: { request: number }) {
      this.jobs.push(data.request);
    }
    answer(text: string) {
      for (const request of this.jobs.splice(0)) {
        if (!this.terminated) this.onmessage?.({ data: { type: "done", request, text, re: 3, im: 0, singular: null, touchedLn0: false } });
      }
    }
    terminate() {
      this.terminated = true;
    }
  }
  workerGlobal.Worker = ManualWorker as unknown as typeof HoldingWorker;
  const held = new JSDOM(`<!doctype html><html><body><div id="root"></div></body></html>`, {
    url: "http://localhost/",
    pretendToBeVisual: true,
  });
  const heldView = held.window;
  globals.window = heldView;
  globals.self = heldView;
  globals.document = heldView.document;
  globals.HTMLElement = heldView.HTMLElement;
  const heldMount = heldView.document.getElementById("root");
  if (!heldMount) {
    console.error("missing manual-worker root");
    process.exit(1);
  }
  const heldRoot = createRoot(heldMount);
  await act(async () => {
    heldRoot.render(<EmlCalculator />);
  });
  const heldButton = (label: string) =>
    [...heldView.document.querySelectorAll("button")].find((button) => button.textContent?.trim() === label);
  const heldClick = async (label: string) => {
    const button = heldButton(label);
    if (!(button instanceof heldView.HTMLButtonElement)) {
      console.error(`missing ${label}`);
      failed = true;
      return;
    }
    await act(async () => {
      button.click();
    });
  };
  const heldWait = async (ms: number) => {
    await act(async () => {
      await new Promise((resolve) => setTimeout(resolve, ms));
    });
  };
  const heldResult = () => heldView.document.querySelector(".ti-lcd-result")?.textContent ?? "";
  const heldError = () => heldView.document.querySelector(".ti-lcd-error")?.textContent ?? "";
  // A pending exact computation must not show "usual value" next to "computing".
  const heldExprForm = heldView.document.querySelector("form.ti-form");
  const heldExprInput = heldExprForm?.querySelector("input");
  const heldExprBtn = heldExprForm?.querySelector("button");
  if (heldExprInput instanceof heldView.HTMLInputElement && heldExprBtn instanceof heldView.HTMLButtonElement) {
    const setter = Object.getOwnPropertyDescriptor(heldView.HTMLInputElement.prototype, "value")?.set;
    await act(async () => {
      setter?.call(heldExprInput, "sin(pi/6)");
      heldExprInput.dispatchEvent(new heldView.Event("input", { bubbles: true }));
    });
    await act(async () => {
      heldExprBtn.click();
    });
    await heldWait(40);
    const pendingNote = heldView.document.querySelector(".ti-lcd-note span")?.textContent ?? "";
    if (!pendingNote.includes("computing") || pendingNote.includes("usual value")) {
      console.error("pending exact note leaked usual value", pendingNote);
      failed = true;
    }
    await heldClick("Clear");
  }
  // An error from a press made while the top row computes stays when that row lands.
  await heldClick("π");
  await heldClick("swap");
  const live = ManualWorker.made.find((worker) => !worker.terminated && worker.jobs.length > 0);
  await act(async () => {
    live?.answer("3");
  });
  if (heldResult() !== "3" || !heldError().includes("Swap needs two values")) {
    console.error("a landing exact row wiped the swap error", heldResult(), heldError());
    failed = true;
  }
  // Cancel while a mode switch is rebuilding the stack cancels the rows it lands.
  await heldClick("hardware");
  await heldWait(40);
  // A synchronous act runs the switch's effect but none of its timer turns,
  // so Cancel lands while the stack is being rebuilt.
  const toExact = heldButton("exact");
  act(() => {
    if (toExact instanceof heldView.HTMLButtonElement) toExact.click();
  });
  const cancel = [...heldView.document.querySelectorAll(".ti-modes button")].find((button) => button.textContent?.trim() === "Cancel");
  if (!(cancel instanceof heldView.HTMLButtonElement)) {
    console.error("no Cancel while a mode switch computes", heldResult());
    failed = true;
  } else {
    act(() => {
      cancel.click();
    });
  }
  await heldWait(60);
  if (heldResult() !== "—" || heldView.document.querySelector(".ti-lcd-note span")?.textContent !== "cancelled") {
    console.error("Cancel during a mode switch was lost", heldResult(), heldView.document.querySelector(".ti-lcd-note span")?.textContent);
    failed = true;
  }
  await act(async () => {
    heldRoot.unmount();
  });
  heldView.close();
  delete workerGlobal.Worker;

  // Step 7 re-test: float mode keeps "this is e" naming and the rotation notice
  // of a loaded word (1E1 -> 11E) across Undo and mode switches.
  const rotDom = new JSDOM(`<!doctype html><html><body><div id="root"></div></body></html>`, {
    url: "http://localhost/",
    pretendToBeVisual: true,
  });
  const rotView = rotDom.window;
  globals.window = rotView;
  globals.self = rotView;
  globals.document = rotView.document;
  globals.HTMLElement = rotView.HTMLElement;
  const rotMount = rotView.document.getElementById("root");
  if (!rotMount) {
    console.error("missing rot root");
    process.exit(1);
  }
  const rotRoot = createRoot(rotMount);
  await act(async () => {
    rotRoot.render(<EmlCalculator />);
  });
  const rotBtn = (label: string) =>
    [...rotView.document.querySelectorAll("button")].find((button) => button.textContent?.trim() === label);
  const rotClick = async (label: string) => {
    const button = rotBtn(label);
    if (!(button instanceof rotView.HTMLButtonElement)) {
      console.error(`missing ${label} in rot test`);
      failed = true;
      return;
    }
    await act(async () => {
      button.click();
    });
  };
  const rotWait = async (ms: number) => {
    await act(async () => {
      await new Promise((resolve) => setTimeout(resolve, ms));
    });
  };
  await rotClick("hardware");
  await rotWait(40);
  const progInput = rotView.document.querySelector('input[aria-label="Program number or word"]');
  const loadBtn = rotBtn("Load");
  if (progInput instanceof rotView.HTMLInputElement && loadBtn instanceof rotView.HTMLButtonElement) {
    const setter = Object.getOwnPropertyDescriptor(rotView.HTMLInputElement.prototype, "value")?.set;
    await act(async () => {
      setter?.call(progInput, "1E1");
      progInput.dispatchEvent(new rotView.Event("input", { bubbles: true }));
    });
    await act(async () => {
      loadBtn.click();
    });
    await rotWait(40);
    const checkRot = (phase: string) => {
      const cap = rotView.document.querySelector(".ti-lcd-caption")?.textContent ?? "";
      const note = rotView.document.querySelector(".ti-lcd-note")?.textContent ?? "";
      if (!cap.includes("this is e") || !note.includes("Rotated 1E1 to 11E.")) {
        console.error(`float loaded-word naming/notice lost at ${phase}`, { cap, note });
        failed = true;
      }
    };
    checkRot("initial load");
    await rotClick("1");
    await rotClick("Undo");
    await rotWait(40);
    checkRot("after Undo");
    await rotClick("exact");
    await rotWait(60);
    await rotClick("hardware");
    await rotWait(60);
    checkRot("after exact -> hardware mode switch");
  }
  await act(async () => {
    rotRoot.unmount();
  });
  rotView.close();

  if (failed) process.exit(1);
  console.log("calculator smoke passed");
}

main().catch((err: unknown) => {
  console.error(err);
  process.exit(1);
});
