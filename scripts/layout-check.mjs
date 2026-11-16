import { spawn } from "node:child_process";
import { createServer } from "node:net";
import { setTimeout as delay } from "node:timers/promises";
import { mkdtempSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";

const site = process.env.SITE || "http://127.0.0.1:4173/eml-and-one/";

function freePort() {
  return new Promise((resolve, reject) => {
    const server = createServer();
    server.once("error", reject);
    server.listen(0, "127.0.0.1", () => {
      const address = server.address();
      const chosen = address && typeof address === "object" ? address.port : 0;
      server.close(() => resolve(chosen));
    });
  });
}

async function choosePort() {
  const preferred = process.env.LAYOUT_CHROME_PORT ? Number(process.env.LAYOUT_CHROME_PORT) : 0;
  if (preferred) {
    const open = await new Promise((resolve) => {
      const server = createServer();
      server.once("error", () => resolve(false));
      server.listen(preferred, "127.0.0.1", () => {
        server.close(() => resolve(true));
      });
    });
    if (open) return preferred;
    console.error(`debugging port ${preferred} is busy; choosing a free port`);
  }
  return freePort();
}

const port = await choosePort();
const chromeBin = process.env.CHROME || "google-chrome";
const failures = [];
let chrome;

function fail(message) {
  failures.push(message);
  console.error(`FAIL ${message}`);
}

function launch() {
  const profile = mkdtempSync(join(tmpdir(), "layout-chrome-"));
  const child = spawn(chromeBin, [
    "--headless=new",
    "--disable-gpu",
    "--no-sandbox",
    `--remote-debugging-port=${port}`,
    `--user-data-dir=${profile}`,
    "about:blank",
  ], { stdio: ["ignore", "pipe", "pipe"] });
  let log = "";
  child.stdout.on("data", (chunk) => { log += chunk; });
  child.stderr.on("data", (chunk) => { log += chunk; });
  child.chromeLog = () => log;
  return child;
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
  { name: "one", expr: "2+2", includes: "4", copy: "4" },
  { name: "complex", expr: "sqrt(2)-0.000314159265*i", includes: "i", copy: "1.41421356237309504880168872420969807856967187537694807317667973799073247846210703885038753432764-0.000314159265i" },
  { name: "exponent", expr: "1.234568*10^20", includes: "1234568" },
  { name: "power", expr: "2^300", includes: "2037035976", copy: (BigInt(2) ** BigInt(300)).toString() },
];

const timer = setTimeout(() => {
  console.error("layout check timed out");
  if (chrome && typeof chrome.chromeLog === "function") console.error(chrome.chromeLog());
  if (chrome && !chrome.killed) chrome.kill();
  process.exit(1);
}, 180_000);

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
    const colorAlpha = (value) => {
      if (!value || value === "currentcolor") return 1;
      if (value === "transparent") return 0;
      const slash = /\\/\\s*([0-9.]+)(%?)\\s*\\)/.exec(value);
      if (slash) return slash[2] ? Number(slash[1]) / 100 : Number(slash[1]);
      const comma = /rgba\\(\\s*[\\d.]+\\s*,\\s*[\\d.]+\\s*,\\s*[\\d.]+\\s*,\\s*([\\d.]+)\\s*\\)/.exec(value);
      if (comma) return Number(comma[1]);
      return 1;
    };
    const sampleMisses = (el) => {
      if (!el) return ["missing"];
      const r = el.getBoundingClientRect();
      if (r.width < 2 || r.height < 2) return ["box"];
      const spots = [[0.5, 0.5], [0.15, 0.5], [0.85, 0.5], [0.5, 0.25], [0.5, 0.75]];
      const misses = [];
      for (const [x, y] of spots) {
        const node = document.elementFromPoint(r.left + r.width * x, r.top + r.height * y);
        if (!node || (el !== node && !el.contains(node))) misses.push(x + "," + y);
      }
      return misses;
    };
    const hidden = [];
    const conceal = (el, label) => {
      if (!el) return;
      let host = el;
      let opacity = 1;
      while (host && host.nodeType === 1) {
        const style = getComputedStyle(host);
        const own = Number(style.opacity);
        if (Number.isFinite(own)) opacity *= own;
        const painted = style.contain === "paint" || style.contain === "strict" || (style.contain || "").split(" ").includes("paint");
        if (painted) hidden.push(label + " contain");
        host = host.parentElement;
      }
      if (opacity === 0) hidden.push(label + " opacity");
      const style = getComputedStyle(el);
      const fill = style.webkitTextFillColor || style.getPropertyValue("-webkit-text-fill-color");
      if (colorAlpha(style.color) === 0 || (fill && fill !== "currentcolor" && colorAlpha(fill) === 0)) hidden.push(label + " text");
      const misses = sampleMisses(el);
      if (misses.length) hidden.push(label + " clip " + misses.join(" "));
    };
    conceal(result, "result");
    conceal(chip, "chip");
    const view = { top: 0, left: 0, right: window.innerWidth, bottom: window.innerHeight };
    const inside = (inner, outer) => !!inner && inner.top >= outer.top - 1 && inner.left >= outer.left - 1 && inner.bottom <= outer.bottom + 1 && inner.right <= outer.right + 1 && inner.height > 8;
    const resultMore = !!result && result.scrollHeight > result.clientHeight + 1;
    const lcdMore = !!lcd && lcd.scrollHeight > lcd.clientHeight + lcd.scrollTop + 1;
    const hit = (el) => {
      if (!el) return "missing";
      const r = el.getBoundingClientRect();
      const node = document.elementFromPoint(r.left + r.width / 2, r.top + r.height / 2);
      if (!node) return "none";
      if (node.closest(".ti-sequence")) return "sequence";
      if (el === node || el.contains(node)) return "self";
      return node.className || node.tagName;
    };
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
      resultHit: hit(result),
      chipHit: hit(chip),
      hidden,
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
    await evalJs(`(() => {
      const write = (text) => {
        window.__copied = String(text);
        return Promise.resolve();
      };
      const clip = window.navigator.clipboard;
      if (clip) clip.writeText = write;
      else window.navigator.clipboard = { writeText: write };
    })()`);
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
      if (shown.resultHit !== "self") fail(`${label} result is covered by ${shown.resultHit}`);
      if (shown.chipHit !== "self") fail(`${label} Copy chip is covered by ${shown.chipHit}`);
      if (shown.hidden?.length) fail(`${label} hides the result or chip via ${shown.hidden.join(", ")}`);
      const copied = await evalJs(`(() => {
        window.__copied = "";
        const chip = [...document.querySelectorAll("button")].find((el) => (el.textContent || "").includes("Copy value"));
        if (!chip) return "";
        const r = chip.getBoundingClientRect();
        const node = document.elementFromPoint(r.left + r.width / 2, r.top + r.height / 2);
        if (!node || (node !== chip && !chip.contains(node))) return "";
        node.dispatchEvent(new MouseEvent("click", { bubbles: true, cancelable: true, clientX: r.left + r.width / 2, clientY: r.top + r.height / 2 }));
        return window.__copied;
      })()`);
      const hidden = /[\u00ad\u200b\u200c\u200d\u2060\u2009\u200a\u202f\ufeff\u2212\u00d7]/;
      if (!copied || hidden.test(copied) || !/^[\x20-\x7e]+$/.test(copied)) {
        fail(`${label} Copy chip did not copy clean text (${JSON.stringify(copied)})`);
      } else if (sample.copy && copied !== sample.copy) {
        fail(`${label} copied ${JSON.stringify(copied)}`);
      }
      if ((shown.resultMore && !shown.resultCue) || (shown.lcdMore && !shown.lcdCue)) {
        fail(`${label} has more content below without a cue`);
      }
      if (sample.name === "power" && viewport.width === 320 && copied && copied === sample.copy) {
        await evalJs(`(() => {
          const input = document.querySelector("#expression");
          const set = Object.getOwnPropertyDescriptor(HTMLInputElement.prototype, "value").set;
          set.call(input, ${JSON.stringify(copied)});
          input.dispatchEvent(new Event("input", { bubbles: true }));
        })()`);
        const pasteDeadline = Date.now() + 5_000;
        let pasted = false;
        while (Date.now() < pasteDeadline) {
          pasted = await evalJs(`(() => {
            const input = document.querySelector("#expression");
            const key = Object.keys(input).find((name) => name.startsWith("__reactProps"));
            return key ? input[key].value === ${JSON.stringify(copied)} : false;
          })()`);
          if (pasted) break;
          await delay(40);
        }
        if (!pasted) {
          fail(`${label} did not commit the copied digits`);
        } else {
          await evalJs(`document.querySelector("#expression").form.requestSubmit()`);
          let again = null;
          const againDeadline = Date.now() + 30_000;
          while (Date.now() < againDeadline) {
            again = await evalJs(measureSource);
            if ((again?.text ?? "").includes(sample.includes)) break;
            await delay(80);
          }
          const recopied = await evalJs(`(() => {
            window.__copied = "";
            const chip = [...document.querySelectorAll("button")].find((el) => (el.textContent || "").includes("Copy value"));
            if (!chip) return "";
            const r = chip.getBoundingClientRect();
            chip.dispatchEvent(new MouseEvent("click", { bubbles: true, cancelable: true, clientX: r.left + r.width / 2, clientY: r.top + r.height / 2 }));
            return window.__copied;
          })()`);
          if (!again?.text?.includes(sample.includes) || recopied !== copied) {
            fail(`${label} pasted copy did not round-trip (${JSON.stringify(recopied).slice(0, 80)})`);
          }
        }
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
  const mutations = [
    ["a center-only clip-path", "clip-path: inset(42% 42% 42% 42%)"],
    ["transparent text", "color: transparent"],
    ["opacity 0", "opacity: 0"],
    ["contain: paint", "contain: paint"],
  ];
  for (const [name, style] of mutations) {
    await evalJs(`(() => { document.querySelector(".ti-lcd-result").style.cssText = ${JSON.stringify(style)}; })()`);
    const guarded = await evalJs(measureSource);
    const caught = (guarded?.hidden || []).some((item) => String(item).startsWith("result"));
    if (!caught) fail(`guard allowed ${name} (${JSON.stringify(guarded?.hidden || [])})`);
    else console.log(`guard caught ${name}`);
    await evalJs(`document.querySelector(".ti-lcd-result").style.cssText = ""`);
  }
  if (failures.length) {
    console.error(`${failures.length} failed`);
    process.exitCode = 1;
  } else {
    console.log("layout check passed");
  }
} catch (err) {
  console.error(err);
  if (chrome && typeof chrome.chromeLog === "function" && chrome.chromeLog()) console.error(chrome.chromeLog());
  process.exitCode = 1;
} finally {
  clearTimeout(timer);
  if (chrome && !chrome.killed) chrome.kill();
}
