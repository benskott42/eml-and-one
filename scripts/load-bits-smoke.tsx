/**
 * DOM smoke for the bit convention in the Load box and the press line:
 * plain bits are E = 1, the 1 key = 0; old bits (0 = EML) only after "old:", always with a note.
 * Run: npx tsx scripts/load-bits-smoke.tsx
 */
import { JSDOM } from "jsdom";

const dom = new JSDOM(`<!doctype html><html><body><div id="root"></div></body></html>`, { url: "http://localhost/", pretendToBeVisual: true });
const view = dom.window;
const globals = globalThis as unknown as { window: typeof view; document: Document; HTMLElement: typeof view.HTMLElement; self: typeof view; IS_REACT_ACT_ENVIRONMENT: boolean };
globals.window = view;
globals.self = view;
globals.document = view.document;
globals.HTMLElement = view.HTMLElement;
globals.IS_REACT_ACT_ENVIRONMENT = true;

async function main() {
  const { act } = await import("react");
  const { createRoot } = await import("react-dom/client");
  const { EmlCalculator } = await import("../components/EmlCalculator");
  let passed = 0;
  let failed = 0;
  const expect = (name: string, ok: boolean, detail = "") => {
    if (ok) passed += 1;
    else {
      failed += 1;
      console.error(`FAIL ${name}${detail ? ` — ${detail.slice(0, 400)}` : ""}`);
    }
  };
  const mount = view.document.getElementById("root");
  if (!mount) throw new Error("missing root");
  const root = createRoot(mount);
  await act(async () => {
    root.render(<EmlCalculator />);
  });
  const screenText = () => view.document.querySelector("[aria-label='Calculator screen']")?.textContent ?? "";
  const resultText = () => view.document.querySelector(".ti-lcd-result")?.textContent ?? "";
  const errorText = () => view.document.querySelector(".ti-lcd-error")?.textContent ?? "";
  const pressLine = () => view.document.querySelector(".ti-press")?.textContent ?? "";
  const settle = async (ms = 40) => act(async () => { await new Promise((resolve) => setTimeout(resolve, ms)); });
  const waitResult = async () => {
    for (let i = 0; i < 80; i += 1) {
      const text = resultText();
      if (text && text !== "computing" && text !== "0") return;
      await settle(25);
    }
  };
  const field = view.document.querySelector("input[placeholder='#1, 001, or 11E']");
  const button = (label: string) => [...view.document.querySelectorAll("button")].find((b) => b.textContent?.trim() === label);
  const load = async (value: string) => {
    if (!(field instanceof view.HTMLInputElement)) throw new Error("missing Load field");
    const setter = Object.getOwnPropertyDescriptor(view.HTMLInputElement.prototype, "value")?.set;
    await act(async () => {
      setter?.call(field, value);
      field.dispatchEvent(new view.Event("input", { bubbles: true }));
    });
    await act(async () => { button("Load")?.click(); });
    await settle();
  };
  const clear = async () => { await act(async () => { button("Clear")?.click(); }); await settle(); };

  expect("Load field hint names the convention and old:", (view.document.getElementById("load-bits-hint")?.textContent ?? "").includes("old:")
    && field?.getAttribute("aria-describedby") === "load-bits-hint");

  // Keys 1 1 EML: press line in the new convention.
  await act(async () => { (view.document.querySelector(".ti-btn-one") as HTMLButtonElement).click(); });
  await act(async () => { (view.document.querySelector(".ti-btn-one") as HTMLButtonElement).click(); });
  await act(async () => { (view.document.querySelector(".ti-btn-eml") as HTMLButtonElement).click(); });
  await waitResult();
  expect("press line for 1 1 EML is 001", pressLine().startsWith("001 (3 presses)"), pressLine());
  expect("press line legend is E = 1", screenText().includes("E = 1, the 1 key = 0"), screenText());
  expect("no old 0 = EML legend left", !screenText().includes("0 = EML"), screenText());
  expect("panel shows ID bits 1·001 and ID 9", (view.document.querySelector(".ti-pid")?.textContent ?? "").includes("1·001"));
  expect("EML key label says 1 in bits", (view.document.querySelector(".ti-btn-eml")?.getAttribute("aria-label") ?? "").includes("1 in bits"));
  await clear();

  // New convention.
  await load("001");
  await waitResult();
  expect("Load 001 gives e as program #1", resultText().includes("2.718") && screenText().includes("program #1"), screenText());
  expect("Load 001 shows no old-convention note", !screenText().includes("old convention"), screenText());
  await clear();
  await load("100");
  await waitResult();
  expect("Load 100 rotates with a note in bits", screenText().includes("Rotated 100 to 001."), screenText());
  await clear();

  // Old bits without the prefix: rejected, nothing loaded.
  await load("110");
  expect("plain 110 is rejected", errorText().includes("old:") && errorText().includes("E = 1"), errorText());
  expect("plain 110 loaded nothing", !resultText().includes("2.718") && !screenText().includes("Read in the old convention") && !screenText().includes("program #"), screenText());
  await clear();

  // Old convention, explicit.
  await load("old:110");
  await waitResult();
  expect("old:110 loads e", resultText().includes("2.718"), resultText());
  expect("old:110 shows the note", screenText().includes("Read in the old convention (0 = EML), shown here as 001."), screenText());
  expect("press line after old:110 is in the new convention", pressLine().startsWith("001"), pressLine());
  await clear();
  await load("old:011");
  await waitResult();
  expect("old:011 notes conversion and rotation", screenText().includes("Read in the old convention (0 = EML), shown here as 100. Rotated 100 to 001."), screenText());

  await settle(1500);
  await act(async () => { root.unmount(); });
  view.close();
  console.log(`load-bits-smoke: ${passed} passed, ${failed} failed`);
  process.exit(failed ? 1 : 0);
}

main().catch((err: unknown) => {
  console.error(err);
  process.exit(1);
});
