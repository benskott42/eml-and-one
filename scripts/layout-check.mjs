import { spawn } from "node:child_process";
import { setTimeout as delay } from "node:timers/promises";
import { mkdtempSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";

const site = process.env.SITE || "http://127.0.0.1:4173/eml-and-one/";
const port = Number(process.env.LAYOUT_CHROME_PORT || 9413);
const chromeBin = process.env.CHROME || "google-chrome";
const failures = [];
let chrome;

function fail(message) {
  failures.push(message);
  console.error(`FAIL ${message}`);
}

function launch() {
  const profile = mkdtempSync(join(tmpdir(), "layout-chrome-"));
  return spawn(chromeBin, [
    "--headless=new",
    "--disable-gpu",
    "--no-sandbox",
    `--remote-debugging-port=${port}`,
    `--user-data-dir=${profile}`,
    "about:blank",
  ], { stdio: "ignore" });
}

async function connect(timeoutMs) {
  const deadline = Date.now() + timeoutMs;
  let last = "chrome did not open a debugging port";
  while (Date.now() < deadline) {
    try {
      const version = await fetch(`http://127.0.0.1:${port}/json/version`).then((response) => {
        if (!response.ok) throw new Error(`version ${response.status}`);
        return response.json();
      });
      const socket = new WebSocket(version.webSocketDebuggerUrl);
      await new Promise((resolve, reject) => {
        socket.addEventListener("open", resolve, { once: true });
        socket.addEventListener("error", () => reject(new Error("debugger socket failed")), { once: true });
      });
      return socket;
    } catch (err) {
      last = err instanceof Error ? err.message : String(err);
      await delay(200);
    }
  }
  throw new Error(last);
}

const viewports = [
  { width: 320, height: 568 },
  { width: 375, height: 667 },
  { width: 1280, height: 800 },
];
const samples = [
  { name: "complex", expr: "sqrt(2)-0.000314159265*i", includes: "i" },
  { name: "exponent", expr: "1.234568*10^20", includes: "1234568" },
  { name: "power", expr: "2^300", includes: "2037035976" },
];

try {
  chrome = launch();
  const socket = await connect(30_000);
  let id = 0;
  const pending = new Map();
  socket.addEventListener("message", (event) => {
    const message = JSON.parse(event.data);
    if (message.id && pending.has(message.id)) {
      pending.get(message.id)(message);
      pending.delete(message.id);
    }
  });
  function send(method, params = {}, sessionId) {
    const messageId = ++id;
    return new Promise((resolve, reject) => {
      const timer = setTimeout(() => {
        pending.delete(messageId);
        reject(new Error(`timed out waiting for ${method}`));
      }, 30_000);
      pending.set(messageId, (message) => {
        clearTimeout(timer);
        resolve(message);
      });
      socket.send(JSON.stringify({ id: messageId, method, params, sessionId }));
    });
  }
  const target = await send("Target.createTarget", { url: "about:blank" });
  const session = await send("Target.attachToTarget", { targetId: target.result.targetId, flatten: true });
  const sessionId = session.result.sessionId;
  await send("Page.enable", {}, sessionId);
  await send("Runtime.enable", {}, sessionId);
  await send("Page.addScriptToEvaluateOnNewDocument", {
    source: `localStorage.setItem("eml-onboarding", "1");`,
  }, sessionId);

  async function evalJs(expression) {
    const result = await send("Runtime.evaluate", {
      expression,
      returnByValue: true,
      awaitPromise: true,
    }, sessionId);
    if (result.result?.exceptionDetails) {
      throw new Error(result.result.exceptionDetails.text || "evaluate failed");
    }
    return result.result?.result?.value;
  }

  const measureSource = `(() => {
    const result = document.querySelector(".ti-lcd-result");
    const lcd = document.querySelector(".ti-lcd");
    const chip = [...document.querySelectorAll("button")].find((el) => (el.textContent || "").includes("Copy value"));
    const one = document.querySelector(".ti-btn-one");
    const eml = document.querySelector(".ti-btn-eml");
    const box = (el) => {
      if (!el) return null;
      const r = el.getBoundingClientRect();
      return { top: r.top, left: r.left, right: r.right, bottom: r.bottom, width: r.width, height: r.height };
    };
    const ellipsis = [];
    let node = result;
    while (node) {
      if (getComputedStyle(node).textOverflow === "ellipsis") ellipsis.push(node.className || node.tagName);
      node = node.parentElement;
    }
    const clips = (el) => {
      if (!el) return "";
      const style = getComputedStyle(el);
      const hidesX = style.overflowX === "hidden" || style.overflowX === "clip";
      const hidesY = style.overflowY === "hidden" || style.overflowY === "clip";
      if (hidesX && el.scrollWidth > el.clientWidth + 1) return "x";
      if (hidesY && el.scrollHeight > el.clientHeight + 1) return "y";
      return "";
    };
    const ancestorClip = [];
    let parent = result?.parentElement || null;
    const resultBox = result?.getBoundingClientRect();
    while (parent) {
      const style = getComputedStyle(parent);
      const hides = style.overflowX === "hidden" || style.overflowX === "clip" || style.overflowY === "hidden" || style.overflowY === "clip";
      if (hides && resultBox) {
        const host = parent.getBoundingClientRect();
        if (resultBox.left < host.left - 1 || resultBox.right > host.right + 1 || resultBox.top < host.top - 1 || resultBox.bottom > host.bottom + 1) {
          ancestorClip.push(parent.className || parent.tagName);
        }
      }
      parent = parent.parentElement;
    }
    const view = { top: 0, left: 0, right: window.innerWidth, bottom: window.innerHeight };
    const inside = (inner, outer) => !!inner && inner.top >= outer.top - 1 && inner.left >= outer.left - 1 && inner.bottom <= outer.bottom + 1 && inner.right <= outer.right + 1 && inner.height > 8;
    const resultMore = !!result && result.scrollHeight > result.clientHeight + 1;
    const lcdMore = !!lcd && lcd.scrollHeight > lcd.clientHeight + lcd.scrollTop + 1;
    return {
      text: result?.textContent?.trim() ?? "",
      ellipsis,
      resultClip: clips(result),
      ancestorClip,
      resultMore,
      lcdMore,
      resultCue: result?.classList.contains("has-more") === true,
      lcdCue: lcd?.classList.contains("has-more") === true,
      chip: box(chip),
      lcd: box(lcd),
      one: box(one),
      eml: box(eml),
      chipInView: inside(box(chip), view),
      chipInLcd: inside(box(chip), box(lcd)),
      oneInView: inside(box(one), view),
      emlInView: inside(box(eml), view),
      scrollY: document.scrollingElement?.scrollTop ?? 0,
    };
  })()`;

  for (const viewport of viewports) {
    await send("Emulation.setDeviceMetricsOverride", {
      width: viewport.width,
      height: viewport.height,
      deviceScaleFactor: 1,
      mobile: viewport.width < 700,
    }, sessionId);
    await send("Page.navigate", { url: site }, sessionId);
    const bootDeadline = Date.now() + 30_000;
    let booted = false;
    while (Date.now() < bootDeadline) {
      const boot = await evalJs(`({
        screen: !!document.querySelector('[aria-label="Calculator screen"]'),
        field: !!document.querySelector("#expression"),
      })`);
      if (boot?.screen && boot.field) {
        booted = true;
        break;
      }
      await delay(100);
    }
    if (!booted) {
      fail(`${viewport.width}x${viewport.height} did not boot`);
      continue;
    }
    const hydrateDeadline = Date.now() + 30_000;
    let hydrated = false;
    while (Date.now() < hydrateDeadline) {
      hydrated = await evalJs(`(() => {
        const input = document.querySelector("#expression");
        if (!input) return false;
        return Object.keys(input).some((key) => key.startsWith("__reactFiber") || key.startsWith("__reactProps"));
      })()`);
      if (hydrated) break;
      await delay(50);
    }
    if (!hydrated) {
      fail(`${viewport.width}x${viewport.height} did not hydrate`);
      continue;
    }
    for (const sample of samples) {
      const label = `${viewport.width}x${viewport.height} ${sample.name}`;
      await evalJs(`(() => {
        const input = document.querySelector("#expression");
        const set = Object.getOwnPropertyDescriptor(HTMLInputElement.prototype, "value").set;
        set.call(input, ${JSON.stringify(sample.expr)});
        input.dispatchEvent(new Event("input", { bubbles: true }));
      })()`);
      const commitDeadline = Date.now() + 5_000;
      let committed = false;
      while (Date.now() < commitDeadline) {
        committed = await evalJs(`(() => {
          const input = document.querySelector("#expression");
          const key = Object.keys(input).find((name) => name.startsWith("__reactProps"));
          return key ? input[key].value === ${JSON.stringify(sample.expr)} : false;
        })()`);
        if (committed) break;
        await delay(40);
      }
      if (!committed) {
        fail(`${label} did not commit the expression`);
        continue;
      }
      await evalJs(`document.querySelector("#expression").form.requestSubmit()`);
      let shown = null;
      const deadline = Date.now() + 30_000;
      while (Date.now() < deadline) {
        shown = await evalJs(measureSource);
        const text = shown?.text ?? "";
        if (text && text !== "computing" && !text.startsWith("Stack empty") && text.includes(sample.includes)) break;
        await delay(80);
      }
      if (!shown?.text?.includes(sample.includes)) {
        fail(`${label} did not compute (${JSON.stringify(shown?.text ?? "")})`);
        continue;
      }
      if (shown.ellipsis.length) fail(`${label} ellipsizes via ${shown.ellipsis.join(", ")}`);
      if (shown.resultClip) fail(`${label} result clips on the ${shown.resultClip} axis`);
      if (shown.ancestorClip.length) fail(`${label} is clipped by ${shown.ancestorClip.join(", ")}`);
      if (!shown.oneInView || !shown.emlInView) fail(`${label} keys are not fully in view`);
      if (!shown.chipInView || !shown.chipInLcd) fail(`${label} Copy chip is not fully visible`);
      if ((shown.resultMore && !shown.resultCue) || (shown.lcdMore && !shown.lcdCue)) {
        fail(`${label} has more content below without a cue`);
      }
      console.log(label, JSON.stringify({
        text: shown.text.slice(0, 60),
        resultMore: shown.resultMore,
        lcdMore: shown.lcdMore,
        one: shown.one && Math.round(shown.one.bottom),
        chip: shown.chip && [Math.round(shown.chip.top), Math.round(shown.chip.bottom)],
      }));
    }
  }
  if (failures.length) {
    console.error(`${failures.length} failed`);
    process.exitCode = 1;
  } else {
    console.log("layout check passed");
  }
} catch (err) {
  console.error(err);
  process.exitCode = 1;
} finally {
  if (chrome && !chrome.killed) chrome.kill();
}
