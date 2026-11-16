/**
 * Headless check of the built count page under /eml-and-one/.
 * Builds the static site, serves it, and drives Chrome over the debugging port.
 */
import { spawn } from "node:child_process";
import { mkdirSync, mkdtempSync, rmSync, symlinkSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { setTimeout as delay } from "node:timers/promises";

const root = join(import.meta.dirname, "..");
const port = 4183;
const debugPort = 9222;
const site = `http://127.0.0.1:${port}/eml-and-one/count/`;
const failures = [];

function report(name, ok, detail = "") {
  const line = `${ok ? "PASS" : "FAIL"} ${name}${detail ? ` — ${detail}` : ""}`;
  console.log(line);
  if (!ok) failures.push(line);
}

function chromeBin() {
  return process.env.CHROME || "google-chrome";
}

function launch() {
  const profile = mkdtempSync(join(tmpdir(), "count-e2e-"));
  return spawn(chromeBin(), [
    "--headless=new",
    "--disable-gpu",
    "--no-sandbox",
    `--remote-debugging-port=${debugPort}`,
    `--user-data-dir=${profile}`,
    "about:blank",
  ], { stdio: "ignore" });
}

async function connect(timeoutMs) {
  const debug = debugPort;
  const deadline = Date.now() + timeoutMs;
  let last = "chrome did not open a debugging port";
  while (Date.now() < deadline) {
    try {
      const version = await fetch(`http://127.0.0.1:${debug}/json/version`).then((response) => {
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

const build = spawn("npm", ["run", "build"], {
  cwd: root,
  env: { ...process.env, PAGES_BASE_PATH: "/eml-and-one" },
  stdio: "inherit",
});
const buildCode = await new Promise((resolve) => build.on("close", resolve));
if (buildCode !== 0) {
  console.error("build failed");
  process.exit(1);
}

const serveRoot = mkdtempSync(join(tmpdir(), "count-site-"));
mkdirSync(serveRoot, { recursive: true });
symlinkSync(join(root, "out"), join(serveRoot, "eml-and-one"));
const serverLog = [];
const server = spawn("python3", ["-m", "http.server", String(port), "--directory", serveRoot], {
  stdio: ["ignore", "pipe", "pipe"],
});
server.stdout.on("data", (chunk) => serverLog.push(String(chunk)));
server.stderr.on("data", (chunk) => serverLog.push(String(chunk)));

for (let i = 0; i < 50; i += 1) {
  try {
    const response = await fetch(`http://127.0.0.1:${port}/eml-and-one/count/`);
    if (response.ok) break;
  } catch {
    // the server is still binding
  }
  await delay(200);
}

let chrome;
try {
  let socket;
  for (let attempt = 1; attempt <= 2; attempt += 1) {
    chrome = launch();
    try {
      socket = await connect(30_000);
      break;
    } catch (err) {
      chrome.kill();
      chrome = undefined;
      if (attempt === 2) throw err;
    }
  }

  let id = 0;
  const pending = new Map();
  const network = [];
  socket.addEventListener("message", (event) => {
    const message = JSON.parse(event.data);
    if (message.id && pending.has(message.id)) {
      pending.get(message.id)(message);
      pending.delete(message.id);
      return;
    }
    const url = message.params?.response?.url || message.params?.request?.url || "";
    if (String(url).endsWith("/favicon.ico")) return;
    if (message.method === "Network.responseReceived") {
      network.push({ url, status: message.params.response.status });
      if (message.params.response.status >= 400) network.push({ url, status: message.params.response.status, bad: true });
    }
    if (message.method === "Network.loadingFailed") {
      network.push({ url, status: 0, bad: true, error: message.params.errorText || "" });
    }
  });

  function send(method, params = {}, sessionId, timeoutMs = 30_000) {
    const messageId = ++id;
    return new Promise((resolve, reject) => {
      const timer = setTimeout(() => {
        pending.delete(messageId);
        reject(new Error(`timed out waiting for ${method}`));
      }, timeoutMs);
      pending.set(messageId, (message) => {
        clearTimeout(timer);
        resolve(message);
      });
      socket.send(JSON.stringify({ id: messageId, method, params, sessionId }));
    });
  }

  async function evalJs(expression, timeoutMs = 30_000) {
    const result = await send("Runtime.evaluate", {
      expression,
      returnByValue: true,
      awaitPromise: true,
    }, sessionId, timeoutMs);
    if (result.result?.exceptionDetails) {
      const details = result.result.exceptionDetails;
      throw new Error(details.text || details.exception?.description || "evaluate failed");
    }
    return result.result?.result?.value;
  }

  const target = await send("Target.createTarget", { url: "about:blank" });
  const session = await send("Target.attachToTarget", { targetId: target.result.targetId, flatten: true });
  const sessionId = session.result.sessionId;
  await send("Page.enable", {}, sessionId);
  await send("Runtime.enable", {}, sessionId);
  await send("Network.enable", {}, sessionId);
  await send("Page.addScriptToEvaluateOnNewDocument", {
    source: `(() => {
      window.__longtasks = [];
      new PerformanceObserver((list) => {
        for (const entry of list.getEntries()) window.__longtasks.push(entry.duration);
      }).observe({ type: "longtask", buffered: true });
      const urls = [];
      const Native = window.Worker;
      window.Worker = function Worker(url, options) {
        urls.push(String(url));
        return new Native(url, options);
      };
      window.Worker.prototype = Native.prototype;
      window.__workerUrls = urls;
    })();`,
  }, sessionId);

  async function open(url) {
    await send("Page.navigate", { url }, sessionId);
    const deadline = Date.now() + 30_000;
    while (Date.now() < deadline) {
      const ready = await evalJs(`document.getElementById("nbig") ? document.getElementById("nbig").textContent : ""`);
      if (ready) return;
      await delay(100);
    }
    throw new Error(`page did not render ${url}`);
  }

  async function waitFor(expression, timeoutMs = 120_000) {
    const deadline = Date.now() + timeoutMs;
    let last = null;
    while (Date.now() < deadline) {
      last = await evalJs(expression);
      if (last) return last;
      await delay(100);
    }
    return last;
  }

  await open(`${site}#n=50`);
  const sawChecking = await waitFor(`(document.getElementById("big")?.textContent || "").includes("checking") || window.__sawFifty === true`);
  const fifty = await waitFor(`(() => {
    const big = document.getElementById("big")?.textContent?.trim() || "";
    const chips = document.getElementById("chips")?.textContent || "";
    const note = document.getElementById("cutnote")?.textContent || "";
    const shown = big === "50" && chips.includes("exact mode · 120 digits") && note.includes("94 gates");
    if (shown) window.__sawFifty = true;
    return shown ? { big, chips, note, tasks: window.__longtasks.slice() } : null;
  })()`, 180_000);
  const workerUrls = await evalJs(`window.__workerUrls || []`);
  const workerPath = Array.isArray(workerUrls) && workerUrls.length
    ? new URL(workerUrls[0], site).pathname
    : "";
  const workerFile = workerPath.split("/").pop() || "";
  // The worker's own script load is reported on the worker target. Ask the page for that
  // same script URL so the response is in this network log.
  if (workerUrls?.[0]) {
    await evalJs(`fetch(${JSON.stringify(String(workerUrls[0]))}, { cache: "no-store" }).then((response) => response.status)`);
  }
  await delay(300);
  const workerHit = network.find((item) => workerFile && item.url.includes(workerFile) && item.status === 200);
  report(
    "worker URL starts with /eml-and-one/ and returns 200",
    workerPath.startsWith("/eml-and-one/") && Boolean(workerHit),
    workerHit ? workerPath : workerPath || "no worker",
  );
  report("n = 50 shows checking, then 50, the exact chip, and 94 gates", Boolean(sawChecking) && Boolean(fifty), fifty ? fifty.note : "timed out");
  const long = (fifty?.tasks || []).filter((duration) => duration > 100);
  report("no long task over 100 ms before the result", long.length === 0, long.join(", "));

  await open(`${site}#n=7`);
  await waitFor(`document.getElementById("nbig")?.textContent === "7"`);
  await evalJs(`document.getElementById("slider").focus()`);
  await send("Input.dispatchKeyEvent", { type: "keyDown", key: "ArrowRight", code: "ArrowRight", windowsVirtualKeyCode: 39 }, sessionId);
  await send("Input.dispatchKeyEvent", { type: "keyUp", key: "ArrowRight", code: "ArrowRight", windowsVirtualKeyCode: 39 }, sessionId);
  await delay(150);
  const stepped = await evalJs(`document.getElementById("nbig")?.textContent`);
  report("slider ArrowRight steps 7 to 8", stepped === "8", String(stepped));
  await evalJs(`document.getElementById("slider").blur(); document.body.focus()`);
  await send("Input.dispatchKeyEvent", { type: "keyDown", key: "ArrowLeft", code: "ArrowLeft", windowsVirtualKeyCode: 37 }, sessionId);
  await send("Input.dispatchKeyEvent", { type: "keyUp", key: "ArrowLeft", code: "ArrowLeft", windowsVirtualKeyCode: 37 }, sessionId);
  await delay(150);
  const steppedBack = await evalJs(`document.getElementById("nbig")?.textContent`);
  report("body ArrowLeft steps 8 to 7", steppedBack === "7", String(steppedBack));

  await evalJs(`document.getElementById("mfloat").click()`);
  const pressed = await evalJs(`({
    float: document.getElementById("mfloat").getAttribute("aria-pressed"),
    exact: document.getElementById("mexact").getAttribute("aria-pressed"),
  })`);
  await evalJs(`document.getElementById("mexact").click()`);
  const pressedBack = await evalJs(`({
    float: document.getElementById("mfloat").getAttribute("aria-pressed"),
    exact: document.getElementById("mexact").getAttribute("aria-pressed"),
  })`);
  report("float button aria-pressed", pressed?.float === "true" && pressed?.exact === "false" && pressedBack?.exact === "true" && pressedBack?.float === "false", JSON.stringify({ pressed, pressedBack }));

  await evalJs(`location.hash = "#n=12"`);
  const hashed = await waitFor(`document.getElementById("nbig")?.textContent === "12" ? "12" : ""`);
  report("hashchange shows 12", hashed === "12", String(hashed));

  await evalJs(`location.hash = "#n=3"`);
  const three = await waitFor(`(() => {
    const label = document.getElementById("label")?.textContent || "";
    const line = document.body.innerText.includes("Lower cut, Arg in [−π, π), ln 0 = −∞. On this cut −iπ becomes +iπ under the principal Log.");
    return label.includes("shortest known, not proven minimal (ties Kaseorg's code-golf answer)") && line ? label : "";
  })()`);
  report("n = 3 pill and cut line", Boolean(three));

  const docsHref = await evalJs(`document.getElementById("docs-link")?.href || ""`);
  try {
    const docs = await fetch(docsHref, { redirect: "follow", headers: { "User-Agent": "eml-count-e2e" } });
    if (docs.status === 200) report("docs link", true, docsHref);
    else report("docs link", false, `${docs.status} ${docsHref}`);
  } catch (err) {
    console.log(`SKIP docs link — offline (${err instanceof Error ? err.message : err}) ${docsHref}`);
  }

  await open(`${site}?debug=cut#n=7`);
  const hooked = await waitFor(`typeof window.__countCutDebug === "function" ? "yes" : ""`);
  if (hooked !== "yes") throw new Error("debug hook was not installed");
  const debug = await evalJs(`window.__countCutDebug()`, 20 * 60 * 1000);
  const ruleOk = debug && Array.isArray(debug.bad) && debug.bad.length === 0 && Array.isArray(debug.rule) && debug.rule.every((row) => row.got === row.want);
  report("debug cut rule has zero violations", Boolean(ruleOk), debug ? `${debug.words} words, ${debug.bad.length} bad` : "no result");
  console.log(`case-2 gates (chrome): ${(debug?.case2 || []).join("; ") || "none"}`);
  await open(`${site}#n=7`);
  const leaked = await evalJs(`({
    trace: typeof window.__countCutDebug,
    floatCount: (document.body.innerText || "").includes("floatHits") || (document.body.innerText || "").includes("float cut"),
  })`);
  report("shipped page has no trace global and no float count", leaked?.trace === "undefined" && leaked?.floatCount === false, JSON.stringify(leaked));

  async function shows(hash, probe) {
    await evalJs(`location.hash = ${JSON.stringify(hash)}`);
    return waitFor(probe, 180_000);
  }
  const neg2 = await shows("#n=-2", `(() => {
    const text = document.body.innerText;
    const pill = document.getElementById("label")?.textContent || "";
    const ok = text.includes("K 25") && text.includes("shortest known (depends on ln 0; unresolved tower trees remain)") && !pill.trimStart().startsWith("proven minimal");
    return ok ? "ok" : "";
  })()`);
  report("n = −2 is K 25 and shortest known, not proved", neg2 === "ok");
  const neg2free = await shows("#n=-2&noln0", `(() => {
    const text = document.body.innerText;
    return text.includes("K 27") && text.includes("minimal conditional on Schanuel's conjecture") ? "ok" : "";
  })()`);
  report("n = −2 without ln 0 is K 27 with the Schanuel footnote", neg2free === "ok");
  const neg8 = await shows("#n=-8", `document.body.innerText.includes("K 77") ? "ok" : ""`);
  report("n = −8 is K 77", neg8 === "ok");
  const neg8free = await shows("#n=-8&noln0", `document.body.innerText.includes("K 79") ? "ok" : ""`);
  report("n = −8 without ln 0 is K 79", neg8free === "ok");
  const neg9 = await shows("#n=-9", `(document.getElementById("cutnote")?.textContent || "").includes("3 gates") ? "ok" : ""`);
  report("n = −9 cut note says 3 gates", neg9 === "ok");
  const eight = await shows("#n=8", `(() => {
    const text = document.body.innerText;
    return text.includes("K 71") && text.includes("shortest known, not proven minimal") ? "ok" : "";
  })()`);
  report("n = 8 is K 71 and shortest known, not proven minimal", eight === "ok");
  const thirteen = await shows("#n=13", `document.body.innerText.includes("K 99") ? "ok" : ""`);
  report("n = 13 is K 99", thirteen === "ok");
  const thirteenFree = await shows("#n=13&noln0", `document.body.innerText.includes("K 101") ? "ok" : ""`);
  report("n = 13 without ln 0 is K 101", thirteenFree === "ok");

  const badNet = network.filter((item) => item.bad);
  report("no failed page requests", badNet.length === 0, badNet.map((item) => `${item.status} ${item.url}`).join("; "));
  const log = serverLog.join("");
  const logged404 = log.split("\n").filter((line) => line.includes(" 404 ") && !line.includes("favicon.ico"));
  report("server log has no 404", logged404.length === 0, logged404.join(" | "));
} catch (err) {
  console.error(err);
  failures.push(err instanceof Error ? err.message : String(err));
} finally {
  if (chrome && !chrome.killed) chrome.kill();
  server.kill();
  rmSync(serveRoot, { recursive: true, force: true });
}

if (failures.length) {
  console.error(`${failures.length} e2e failures`);
  process.exit(1);
}
console.log("count:e2e passed");
