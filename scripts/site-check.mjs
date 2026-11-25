/**
 * Headless Chrome regression suite against the built static site (`out/`).
 *
 * Usage:
 *   node scripts/site-check.mjs [siteUrl] [chromePath] [--site-log <path>]
 *
 * Local quick start (PowerShell):
 *   $env:PAGES_BASE_PATH="/eml-and-one"; npm run build
 *   npm run eml:site
 *
 * When no siteUrl (or SITE env var) is provided, this script serves `./out`
 * under `/eml-and-one/` on an ephemeral localhost port for the duration of the run.
 */
import { spawn } from "node:child_process";
import { createServer as createHttpServer } from "node:http";
import { createServer as createNetServer } from "node:net";
import { setTimeout as delay } from "node:timers/promises";
import { existsSync, mkdtempSync, readFileSync, statSync } from "node:fs";
import { tmpdir } from "node:os";
import { extname, join, normalize, resolve } from "node:path";

const MIME = {
  ".html": "text/html; charset=utf-8",
  ".js": "text/javascript; charset=utf-8",
  ".mjs": "text/javascript; charset=utf-8",
  ".css": "text/css; charset=utf-8",
  ".json": "application/json; charset=utf-8",
  ".svg": "image/svg+xml",
  ".png": "image/png",
  ".ico": "image/x-icon",
  ".txt": "text/plain; charset=utf-8",
  ".woff2": "font/woff2",
  ".woff": "font/woff",
  ".wasm": "application/wasm",
};

function parseArgs(argv) {
  let site = process.env.SITE || "";
  let chromeBin = process.env.CHROME || "";
  let siteLog = process.env.SITE_LOG || "";
  const positional = [];
  for (let i = 0; i < argv.length; i += 1) {
    const arg = argv[i];
    if (arg === "--url" && argv[i + 1]) {
      site = argv[++i];
    } else if (arg === "--chrome" && argv[i + 1]) {
      chromeBin = argv[++i];
    } else if (arg === "--site-log" && argv[i + 1]) {
      siteLog = argv[++i];
    } else if (!arg.startsWith("-")) {
      positional.push(arg);
    }
  }
  if (!site && positional[0]) site = positional[0];
  if (!chromeBin && positional[1]) chromeBin = positional[1];
  return { site, chromeBin, siteLog };
}

function findChrome(explicit) {
  if (explicit) return explicit;
  if (process.platform === "win32") {
    const candidates = [
      "C:\\Program Files\\Google\\Chrome\\Application\\chrome.exe",
      "C:\\Program Files (x86)\\Google\\Chrome\\Application\\chrome.exe",
      process.env.LOCALAPPDATA ? join(process.env.LOCALAPPDATA, "Google", "Chrome", "Application", "chrome.exe") : "",
    ].filter(Boolean);
    for (const candidate of candidates) {
      if (existsSync(candidate)) return candidate;
    }
  } else if (process.platform === "darwin") {
    const mac = "/Applications/Google Chrome.app/Contents/MacOS/Google Chrome";
    if (existsSync(mac)) return mac;
  }
  return "google-chrome";
}

function startLocalServer(outDir) {
  const root = resolve(outDir);
  if (!existsSync(join(root, "index.html"))) {
    throw new Error(
      `Static build not found at ${root}. Build first with:\n` +
        `  PowerShell: $env:PAGES_BASE_PATH="/eml-and-one"; npm run build\n` +
        `  bash:       PAGES_BASE_PATH=/eml-and-one npm run build`,
    );
  }
  const serverHttpErrors = [];
  const server = createHttpServer((req, res) => {
    const rawPath = (req.url || "/").split("?")[0];
    let rel = rawPath;
    if (rel === "/eml-and-one") {
      res.writeHead(301, { Location: "/eml-and-one/" });
      res.end();
      return;
    }
    if (!rel.startsWith("/eml-and-one/")) {
      if (!rel.endsWith("/favicon.ico")) serverHttpErrors.push(`404 ${rawPath}`);
      res.writeHead(404);
      res.end("Not found");
      return;
    }
    rel = rel.slice("/eml-and-one/".length);
    if (!rel || rel.endsWith("/")) rel += "index.html";
    const filePath = resolve(root, normalize(rel));
    if (!filePath.startsWith(root) || !existsSync(filePath) || statSync(filePath).isDirectory()) {
      if (!rawPath.endsWith("/favicon.ico")) serverHttpErrors.push(`404 ${rawPath}`);
      res.writeHead(404);
      res.end("Not found");
      return;
    }
    const contentType = MIME[extname(filePath).toLowerCase()] || "application/octet-stream";
    res.writeHead(200, { "Content-Type": contentType });
    res.end(readFileSync(filePath));
  });
  return new Promise((resolvePromise, reject) => {
    server.once("error", reject);
    server.listen(0, "127.0.0.1", () => {
      const address = server.address();
      const port = address && typeof address === "object" ? address.port : 0;
      resolvePromise({
        server,
        url: `http://127.0.0.1:${port}/eml-and-one/`,
        errors: serverHttpErrors,
      });
    });
  });
}

const args = parseArgs(process.argv.slice(2));
const chromeBin = findChrome(args.chromeBin);
const siteLog = args.siteLog;
const failures = [];
let localServer;
let chrome;
let socket;
let chromeLog = "";

function fail(message) {
  failures.push(message);
  console.error(`FAIL ${message}`);
}

function shownText(shown) {
  if (shown && typeof shown === "object") {
    return `showed ${JSON.stringify(shown.text)} note ${JSON.stringify(shown.note ?? "")}`;
  }
  return `showed ${JSON.stringify(shown)}`;
}

function freePort() {
  return new Promise((resolvePromise, reject) => {
    const server = createNetServer();
    server.once("error", reject);
    server.listen(0, "127.0.0.1", () => {
      const address = server.address();
      const chosen = address && typeof address === "object" ? address.port : 0;
      server.close(() => resolvePromise(chosen));
    });
  });
}

function launch(port) {
  const profile = mkdtempSync(join(tmpdir(), "ci-chrome-"));
  const child = spawn(
    chromeBin,
    [
      "--headless=new",
      "--disable-gpu",
      "--no-sandbox",
      `--remote-debugging-port=${port}`,
      `--user-data-dir=${profile}`,
      "about:blank",
    ],
    { stdio: ["ignore", "pipe", "pipe"] },
  );
  let log = "";
  const take = (chunk) => {
    log += chunk.toString();
  };
  child.stdout.on("data", take);
  child.stderr.on("data", take);
  child.output = () => log;
  return child;
}

function serverErrors(log) {
  const errors = [];
  for (const line of log.split("\n")) {
    const match = line.match(/"[A-Z]+ ([^"]*?) HTTP\/\d+(?:\.\d+)?" (\d{3})/);
    if (!match) continue;
    const path = match[1].split("?")[0];
    const status = Number(match[2]);
    if (status < 400) continue;
    if (path.endsWith("/favicon.ico")) continue;
    errors.push(`${status} ${path}`);
  }
  return errors;
}

async function connect(port, timeoutMs) {
  const deadline = Date.now() + timeoutMs;
  let last = "chrome did not open a debugging port";
  while (Date.now() < deadline) {
    try {
      const version = await fetch(`http://127.0.0.1:${port}/json/version`).then((response) => {
        if (!response.ok) throw new Error(`version ${response.status}`);
        return response.json();
      });
      const ws = new WebSocket(version.webSocketDebuggerUrl);
      await new Promise((resolvePromise, reject) => {
        ws.addEventListener("open", resolvePromise, { once: true });
        ws.addEventListener("error", () => reject(new Error("debugger socket failed")), { once: true });
      });
      return ws;
    } catch (err) {
      last = err instanceof Error ? err.message : String(err);
      await delay(200);
    }
  }
  throw new Error(last);
}

try {
  let site = args.site;
  if (!site) {
    localServer = await startLocalServer("out");
    site = localServer.url;
  }

  for (let attempt = 1; attempt <= 2; attempt += 1) {
    const port = await freePort();
    chrome = launch(port);
    try {
      socket = await connect(port, 30_000);
      break;
    } catch (err) {
      chromeLog = chrome.output();
      console.error(`chrome failed to open a debugging port on ${port}`);
      if (chromeLog) console.error(chromeLog);
      else console.error(err instanceof Error ? err.message : err);
      chrome.kill();
      chrome = undefined;
      if (attempt === 2) throw err;
    }
  }

  let id = 0;
  const pending = new Map();
  const bad = [];
  socket.addEventListener("message", (event) => {
    const message = JSON.parse(event.data);
    if (message.id && pending.has(message.id)) {
      pending.get(message.id)(message);
      pending.delete(message.id);
      return;
    }
    const url = message.params?.response?.url || message.params?.request?.url || "";
    if (url.endsWith("/favicon.ico")) return;
    if (message.method === "Network.responseReceived" && message.params.response.status >= 400) {
      bad.push(`${message.params.response.status} ${url}`);
    }
    if (message.method === "Network.loadingFailed") {
      bad.push(`failed ${url} ${message.params.errorText || ""}`.trim());
    }
  });

  function send(method, params = {}, sessionId) {
    const messageId = ++id;
    return new Promise((resolvePromise, reject) => {
      const timer = setTimeout(() => {
        pending.delete(messageId);
        reject(new Error(`timed out waiting for ${method}`));
      }, 90_000);
      pending.set(messageId, (message) => {
        clearTimeout(timer);
        resolvePromise(message);
      });
      socket.send(JSON.stringify({ id: messageId, method, params, sessionId }));
    });
  }

  const target = await send("Target.createTarget", { url: "about:blank" });
  const session = await send("Target.attachToTarget", { targetId: target.result.targetId, flatten: true });
  const sessionId = session.result.sessionId;
  await send("Page.enable", {}, sessionId);
  await send("Runtime.enable", {}, sessionId);
  await send("Network.enable", {}, sessionId);
  await send(
    "Page.addScriptToEvaluateOnNewDocument",
    {
      source: `(() => {
        const urls = [];
        const Native = window.Worker;
        window.Worker = function Worker(url, options) {
          urls.push(String(url));
          return new Native(url, options);
        };
        window.Worker.prototype = Native.prototype;
        window.__workerUrls = urls;
      })();`,
    },
    sessionId,
  );
  await send(
    "Emulation.setDeviceMetricsOverride",
    {
      width: 1280,
      height: 800,
      deviceScaleFactor: 1,
      mobile: false,
    },
    sessionId,
  );
  await send("Page.navigate", { url: site }, sessionId);

  async function evalJs(expression) {
    const result = await send(
      "Runtime.evaluate",
      {
        expression,
        returnByValue: true,
        awaitPromise: true,
      },
      sessionId,
    );
    if (result.result?.exceptionDetails) {
      throw new Error(result.result.exceptionDetails.text || result.result.exceptionDetails.exception?.description || "evaluate failed");
    }
    return result.result?.result?.value;
  }

  const bootDeadline = Date.now() + 30_000;
  let boot;
  while (Date.now() < bootDeadline) {
    try {
      boot = await evalJs(`({
        path: location.pathname,
        screen: !!document.querySelector('[aria-label="Calculator screen"]'),
        one: !!document.querySelector(".ti-btn-one"),
        eml: !!document.querySelector(".ti-btn-eml"),
        result: document.querySelector(".ti-lcd-result")?.textContent?.trim() ?? "",
        // The keys exist in the static HTML before hydration; a click then is lost.
        ready: document.querySelector(".ti-stage")?.getAttribute("data-ready") === "1",
      })`);
      if (boot?.screen && boot.one && boot.eml && boot.ready) break;
    } catch {
      /* the document is still navigating */
    }
    await delay(200);
  }
  console.log("boot", JSON.stringify(boot));
  if (!boot?.path?.startsWith("/eml-and-one")) fail(`page loaded at ${JSON.stringify(boot?.path)}`);
  if (!boot?.screen) fail("calculator screen is missing");
  if (!boot?.one || !boot?.eml) fail("1 or EML key is missing");
  if (!boot?.ready) fail("the calculator did not hydrate within 30 s");

  const field = `document.querySelector("#expression") || [...document.querySelectorAll("label")].find((label) => /^\\s*Expression/i.test(label.textContent || ""))?.querySelector("input")`;

  async function compute(source, accept, timeoutMs, watchTasks) {
    return evalJs(`(async () => {
      const input = ${field};
      if (!input || !input.form) return { error: "no expression field" };
      const read = () => {
        const text = document.querySelector(".ti-lcd-result")?.textContent?.trim() ?? "";
        const note = document.querySelector(".ti-lcd-note span")?.textContent?.trim() ?? "";
        const error = document.querySelector(".ti-lcd-error")?.textContent?.trim() ?? "";
        return { text, note, error, chips: document.querySelectorAll(".ti-press-chip").length, hidden: document.querySelectorAll('[aria-hidden="true"] [tabindex="0"]').length };
      };
      const result = document.querySelector(".ti-lcd-result");
      let generation = 0;
      let seen = result?.textContent ?? "";
      const count = () => {
        const next = result?.textContent ?? "";
        if (next !== seen) {
          generation += 1;
          seen = next;
        }
      };
      const observer = result ? new MutationObserver(() => { generation += 1; count(); }) : null;
      observer?.observe(result, { subtree: true, characterData: true, childList: true });
      const tasks = [];
      const tasksObserver = ${watchTasks ? "new PerformanceObserver((list) => { for (const entry of list.getEntries()) tasks.push(Math.round(entry.duration)); })" : "null"};
      tasksObserver?.observe({ type: "longtask", buffered: false });
      const started = generation;
      const set = Object.getOwnPropertyDescriptor(HTMLInputElement.prototype, "value").set;
      set.call(input, ${JSON.stringify(source)});
      input.dispatchEvent(new Event("input", { bubbles: true }));
      input.form.requestSubmit();
      const accept = ${accept};
      const deadline = Date.now() + ${timeoutMs};
      let shown = read();
      while (Date.now() < deadline) {
        count();
        shown = read();
        if (generation > started && shown.text !== "computing" && accept(shown)) {
          observer?.disconnect();
          tasksObserver?.disconnect();
          return { ...shown, tasks };
        }
        await new Promise((resolve) => setTimeout(resolve, 40));
      }
      observer?.disconnect();
      tasksObserver?.disconnect();
      return { ...shown, tasks, error: shown.error || "timeout" };
    })()`);
  }

  // One turn: the second 1 and EML run before the browser paints, so a
  // native disabled attribute from the empty stack would drop EML.
  const e = await evalJs(`(async () => {
    const result = document.querySelector(".ti-lcd-result");
    let generation = 0;
    let seen = result?.textContent ?? "";
    const count = () => {
      const next = result?.textContent ?? "";
      if (next !== seen) { generation += 1; seen = next; }
    };
    const observer = new MutationObserver(() => { generation += 1; count(); });
    observer.observe(result, { subtree: true, characterData: true, childList: true });
    const started = generation;
    document.querySelector(".ti-btn-one").click();
    document.querySelector(".ti-btn-one").click();
    document.querySelector(".ti-btn-eml").click();
    const deadline = Date.now() + 20000;
    let text = "";
    while (Date.now() < deadline) {
      count();
      text = result?.textContent?.trim() ?? "";
      if (generation > started && text !== "computing" && text === "2.718281828459") {
        observer.disconnect();
        return text;
      }
      await new Promise((resolve) => setTimeout(resolve, 40));
    }
    observer.disconnect();
    return result?.textContent?.trim() ?? "";
  })()`);
  console.log("e", JSON.stringify(e));
  if (e !== "2.718281828459") fail(`1, 1, EML ${shownText(e)}`);

  const two = await compute("2*2", '(shown) => shown.text === "4"', 25000, false);
  console.log("2*2", JSON.stringify(two));
  if (two.error === "no expression field") fail(`2*2 ${shownText(two)}`);
  else if (two.text !== "4") fail(`2*2 ${shownText(two)}`);

  const ln = await compute("ln(-1)", '(shown) => shown.text === "3.14159265359i"', 25000, false);
  console.log("ln(-1)", JSON.stringify(ln));
  if (ln.text !== "3.14159265359i") fail(`ln(-1) ${shownText(ln)}`);

  const tan = await compute("tan(10^(-5000))", '(shown) => shown.text === "\\u2014"', 25000, true);
  console.log("tan", JSON.stringify(tan));
  if (tan.text !== "—") fail(`tan(10^(-5000)) ${shownText(tan)}`);
  if (!String(tan.note || "").split(" · ").includes("couldn't verify")) fail(`tan(10^(-5000)) ${shownText(tan)}`);
  const long = (tan.tasks || []).filter((duration) => duration > 50);
  if (long.length) fail(`tan(10^(-5000)) long tasks ${JSON.stringify(tan.tasks)}`);
  if (tan.chips) fail(`collapsed view rendered ${tan.chips} chips`);
  if (tan.hidden) fail(`aria-hidden contains ${tan.hidden} tab stops`);

  const ln130 = await compute(
    "ln(1+10^(-130))",
    '(shown) => shown.text === "1\\u00d710^\\u2212130" && shown.note.split(" \\u00b7 ").includes("ln 0")',
    30000,
    false,
  );
  console.log("ln(1+10^(-130))", JSON.stringify(ln130));
  if (ln130.text !== "1×10^−130" || !String(ln130.note || "").split(" · ").includes("ln 0")) {
    fail(`ln(1+10^(-130)) ${shownText(ln130)}`);
  }

  const followed = await evalJs(`(async () => {
    const input = ${field};
    if (!input || !input.form) return { error: "no expression field" };
    const result = document.querySelector(".ti-lcd-result");
    let generation = 0;
    const observer = new MutationObserver(() => { generation += 1; });
    observer.observe(result, { subtree: true, characterData: true, childList: true });
    const set = Object.getOwnPropertyDescriptor(HTMLInputElement.prototype, "value").set;
    const submit = (source) => {
      set.call(input, source);
      input.dispatchEvent(new Event("input", { bubbles: true }));
      input.form.requestSubmit();
    };
    submit("ln(1+3*10^(-130))");
    let pending = "";
    const pendingDeadline = Date.now() + 500;
    while (Date.now() < pendingDeadline) {
      pending = result?.textContent?.trim() ?? "";
      if (pending === "computing" || pending === "3\\u00d710^\\u2212130") break;
      await new Promise((resolve) => setTimeout(resolve, 16));
    }
    const tasks = [];
    const tasksObserver = new PerformanceObserver((list) => {
      for (const entry of list.getEntries()) tasks.push(Math.round(entry.duration));
    });
    tasksObserver.observe({ type: "longtask", buffered: false });
    const started = generation;
    const t0 = Date.now();
    submit("1+1");
    let text = "";
    while (Date.now() - t0 < 2000) {
      text = result?.textContent?.trim() ?? "";
      if (generation > started && text !== "computing" && text === "2") {
        observer.disconnect();
        tasksObserver.disconnect();
        return { pending, text, ms: Date.now() - t0, tasks };
      }
      await new Promise((resolve) => setTimeout(resolve, 20));
    }
    observer.disconnect();
    tasksObserver.disconnect();
    return { pending, text, ms: Date.now() - t0, tasks, error: "timeout" };
  })()`);
  console.log("slow then 1+1", JSON.stringify(followed));
  if (followed.pending !== "computing") {
    fail(`slow job was not still pending when 1+1 was submitted; pending ${JSON.stringify(followed.pending)} ${shownText(followed.text)}`);
  }
  if (followed.text !== "2") fail(`slow job then 1+1 ${shownText(followed.text)}`);
  if ((followed.tasks || []).length) fail(`slow job then 1+1 long tasks ${JSON.stringify(followed.tasks)}; ${shownText(followed.text)}`);

  const again = await compute("1+1", '(shown) => shown.text === "2"', 15000, false);
  console.log("1+1 again", JSON.stringify(again));
  if (again.text !== "2") fail(`repeated 1+1 ${shownText(again)}`);

  const slowAfter = await compute("ln(1+3*10^(-130))", '(shown) => shown.text === "3\\u00d710^\\u2212130"', 30000, false);
  console.log("slow job afterwards", JSON.stringify(slowAfter));
  if (slowAfter.text !== "3×10^−130") fail(`slow job afterwards ${shownText(slowAfter)}`);

  const signed = await compute("ln(-2-10^(-20)*i)", '(shown) => shown.text === "0.69314718056 \\u2212 3.14159265359i"', 30000, false);
  console.log("tiny imaginary", JSON.stringify(signed));
  if (signed.text !== "0.69314718056 − 3.14159265359i") fail(`tiny imaginary sign ${shownText(signed)}`);

  const tinySet = [
    ["0.00005i+0.00005i", "0.0001i"],
    ["sinh(0.00005i)", "0.00005i"],
    ["tanh(1e-10*i)", "1×10^−10i"],
    ["tanh(1e-16*i)", "1×10^−16i"],
    ["cosh(0.00005i)", "0.99999999875000000026"],
  ];
  for (const [source, want] of tinySet) {
    const shown = await compute(source, `(shown) => shown.text === ${JSON.stringify(want)}`, 30000, false);
    console.log(source, JSON.stringify(shown));
    if (shown.text !== want) fail(`${source} ${shownText(shown)}`);
    if (String(shown.text).startsWith("−") || String(shown.text).startsWith("-")) fail(`${source} leading minus ${shownText(shown)}`);
  }

  // A mode click and an Undo pressed while a mode switch rebuilds the stack
  // are queued. The undo ran first and the second switch's effect cancelled
  // it: the screen kept its row, and the history lost a step.
  const queuedUndo = await evalJs(`(async () => {
    const button = (name) => [...document.querySelectorAll("button")].find((b) => b.textContent.trim() === name);
    const tape = () => document.querySelector(".ti-tape")?.textContent?.trim() ?? "";
    const settle = async (want) => {
      const deadline = Date.now() + 20000;
      while (Date.now() < deadline && tape() !== want) await new Promise((resolve) => setTimeout(resolve, 40));
      await new Promise((resolve) => setTimeout(resolve, 500));
    };
    button("Clear").click();
    for (let i = 0; i < 3; i += 1) document.querySelector(".ti-btn-one").click();
    await settle("1  1  1");
    button("hardware").click();
    await new Promise((resolve) => setTimeout(resolve, 0));
    button("exact").click();
    button("Undo").click();
    await settle("1  1");
    const first = tape();
    button("Undo").click();
    await settle("1");
    return { first, second: tape(), mode: document.querySelector(".ti-lcd-status span")?.textContent ?? "" };
  })()`);
  console.log("queued mode and undo", JSON.stringify(queuedUndo));
  if (queuedUndo.first !== "1  1" || queuedUndo.second !== "1" || queuedUndo.mode !== "exact") {
    fail(`queued mode switch and undo ${JSON.stringify(queuedUndo)}`);
  }

  // A refused program entered while a mode switch rebuilds the stack shows its error.
  // It was set on the old screen and replaced when the rebuild landed.
  const loadError = await evalJs(`(async () => {
    const button = (name) => [...document.querySelectorAll("button")].find((b) => b.textContent.trim() === name);
    const input = [...document.querySelectorAll("label")].find((label) => /^\\s*Program number/.test(label.textContent || ""))?.querySelector("input");
    if (!input || !input.form) return { error: "no program field" };
    for (let i = 0; i < 9; i += 1) document.querySelector(".ti-btn-one").click();
    await new Promise((resolve) => setTimeout(resolve, 500));
    const set = Object.getOwnPropertyDescriptor(HTMLInputElement.prototype, "value").set;
    set.call(input, "#12a");
    input.dispatchEvent(new Event("input", { bubbles: true }));
    button("hardware").click();
    await new Promise((resolve) => setTimeout(resolve, 0));
    input.form.requestSubmit();
    const deadline = Date.now() + 10000;
    let shown = "";
    while (Date.now() < deadline) {
      shown = document.querySelector(".ti-lcd-error")?.textContent ?? "";
      if (shown) break;
      await new Promise((resolve) => setTimeout(resolve, 40));
    }
    await new Promise((resolve) => setTimeout(resolve, 500));
    const kept = document.querySelector(".ti-lcd-error")?.textContent ?? "";
    button("exact").click();
    await new Promise((resolve) => setTimeout(resolve, 1500));
    return { shown, kept };
  })()`);
  console.log("program error during a switch", JSON.stringify(loadError));
  if (!/followed by digits/.test(loadError.kept || "")) fail(`program error during a mode switch ${JSON.stringify(loadError)}`);

  // A long-press caption read on an empty screen came back after a press and Clear.
  const keyCenter = await evalJs(`(() => {
    const key = [...document.querySelectorAll(".ti-key button")].find((b) => b.textContent.trim() === "π");
    key.scrollIntoView({ block: "center" });
    const r = key.getBoundingClientRect();
    return { x: r.x + r.width / 2, y: r.y + r.height / 2 };
  })()`);
  await evalJs(`[...document.querySelectorAll("button")].find((b) => b.textContent.trim() === "Clear").click()`);
  await delay(300);
  const mouse = (type) => send("Input.dispatchMouseEvent", { type, x: keyCenter.x, y: keyCenter.y, button: "left", clickCount: 1 }, sessionId);
  await mouse("mousePressed");
  await delay(700);
  await mouse("mouseReleased");
  await delay(200);
  const heldCaption = await evalJs(`document.querySelector(".ti-lcd-hold")?.textContent ?? ""`);
  const afterClear = await evalJs(`(async () => {
    document.querySelector(".ti-btn-one").click();
    await new Promise((resolve) => setTimeout(resolve, 300));
    [...document.querySelectorAll("button")].find((b) => b.textContent.trim() === "Clear").click();
    await new Promise((resolve) => setTimeout(resolve, 300));
    return document.querySelector(".ti-lcd-hold")?.textContent ?? "";
  })()`);
  console.log("long-press caption", JSON.stringify({ heldCaption, afterClear }));
  if (!heldCaption.startsWith("π.")) fail(`long-press on π showed ${JSON.stringify(heldCaption)}`);
  if (afterClear) fail(`long-press caption came back after a press and Clear: ${JSON.stringify(afterClear)}`);

  const workers = await evalJs(`window.__workerUrls || []`);
  console.log("workers", JSON.stringify(workers));
  if (!Array.isArray(workers) || workers.length === 0) fail("exact worker was not created");
  for (const url of workers) {
    let path = "";
    try {
      path = new URL(String(url)).pathname;
    } catch {
      path = String(url);
    }
    if (!path.startsWith("/eml-and-one/_next/")) fail(`worker URL is outside /eml-and-one/_next/: ${url}`);
  }
  if (bad.length) fail(`failed requests ${JSON.stringify(bad)}`);
  if (siteLog) {
    let siteText = "";
    try {
      siteText = readFileSync(siteLog, "utf8");
    } catch (err) {
      fail(`could not read the static server log: ${err instanceof Error ? err.message : err}`);
    }
    const httpErrors = serverErrors(siteText);
    if (httpErrors.length) fail(`static server errors ${JSON.stringify(httpErrors)}`);
  } else if (localServer?.errors.length) {
    fail(`static server errors ${JSON.stringify(localServer.errors)}`);
  }

  if (failures.length) {
    console.error(`${failures.length} failed`);
  } else {
    console.log("chrome regression passed");
  }
} catch (err) {
  chromeLog = chrome?.output?.() || chromeLog;
  if (chromeLog) console.error(chromeLog);
  console.error(err);
  failures.push("chrome regression threw");
} finally {
  try {
    socket?.close();
  } catch {
    /* the debugger socket is already closed */
  }
  if (chrome && !chrome.killed) chrome.kill();
  localServer?.server?.close();
}
process.exit(failures.length ? 1 : 0);
