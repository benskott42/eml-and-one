/**
 * Headless check of the built count page under /eml-and-one/.
 * Builds the static site, serves it, and drives Chrome over the debugging port.
 */
import { spawn } from "node:child_process";
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync } from "node:fs";
import { createServer } from "node:net";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { setTimeout as delay } from "node:timers/promises";

const root = join(import.meta.dirname, "..");
const labelSrc = readFileSync(join(root, "lib/eml/statusLabels.ts"), "utf8");
function exportedPhrase(name) {
  const match = new RegExp(`export const ${name} = "([^"]+)"`).exec(labelSrc);
  if (!match) throw new Error(`missing ${name}`);
  return match[1];
}
const PROVEN_PILL = exportedPhrase("PROVEN_MINIMAL");
const KNOWN_PILL = `shortest known, not ${PROVEN_PILL}`;
const THREE_PILL = `${KNOWN_PILL} (ties Kaseorg's code-golf answer)`;
const NEG2_PILL = `shortest known (depends on ln 0; unresolved tower trees remain), not ${PROVEN_PILL}`;
const BAD_PORTS = new Set([1, 7, 9, 11, 13, 15, 17, 19, 20, 21, 22, 23, 25, 37, 42, 43, 53, 69, 77, 79, 87, 95, 101, 102, 103, 104, 109, 110, 111, 113, 115, 117, 119, 123, 135, 137, 139, 143, 179, 389, 427, 465, 512, 513, 514, 515, 526, 530, 531, 532, 540, 548, 554, 556, 563, 587, 601, 636, 989, 990, 993, 995, 1719, 1720, 1723, 2049, 3659, 4045, 5060, 5061, 6000, 6566, 6665, 6666, 6667, 6668, 6669, 6697, 10080]);
function freePort() {
  return new Promise((resolve, reject) => {
    const server = createServer();
    server.once("error", reject);
    server.listen(0, "127.0.0.1", () => {
      const address = server.address();
      const chosen = typeof address === "object" && address ? address.port : 0;
      server.close(() => resolve(chosen));
    });
  });
}
async function openPort() {
  for (let attempt = 0; attempt < 20; attempt += 1) {
    const chosen = await freePort();
    if (chosen && !BAD_PORTS.has(chosen)) return chosen;
  }
  throw new Error("no free port");
}
const port = await openPort();
const debugPort = await openPort();
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
let serverCode = null;
const server = spawn("python3", ["-m", "http.server", String(port), "--directory", serveRoot], {
  stdio: ["ignore", "pipe", "pipe"],
});
server.stdout.on("data", (chunk) => serverLog.push(String(chunk)));
server.stderr.on("data", (chunk) => serverLog.push(String(chunk)));
server.on("exit", (code) => {
  serverCode = code;
});

let served = false;
for (let i = 0; i < 50; i += 1) {
  if (serverCode !== null) break;
  try {
    const response = await fetch(`http://127.0.0.1:${port}/eml-and-one/count/`);
    const html = await response.text();
    if (response.ok && html.includes("count to n")) {
      served = true;
      break;
    }
  } catch {
    // the server is still binding
  }
  await delay(200);
}
if (!served) {
  console.error(serverLog.join(""));
  console.error(serverCode !== null ? `static server exited ${serverCode}` : "static server did not serve this build");
  server.kill();
  rmSync(serveRoot, { recursive: true, force: true });
  process.exit(1);
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
      const error = message.params?.errorText || "";
      if (error === "net::ERR_ABORTED") return;
      network.push({ url, status: 0, bad: true, error });
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

  function exactProbe(n) {
    const shown = n < 0 ? `−${-n}` : String(n);
    return `(() => {
      const big = (document.getElementById("big")?.textContent || "").replace(/\\s+/g, " ").trim();
      const chips = document.getElementById("chips")?.textContent || "";
      if (!big || big.includes("checking")) return "";
      return big === ${JSON.stringify(shown)} && chips.includes("exact mode · 120 digits") ? "ok" : "bad:" + big;
    })()`;
  }

  function displayedN(url) {
    const match = /[#?&]n=(-?\d+)/.exec(url);
    if (!match) return null;
    const n = Number(match[1]);
    return n < 0 ? `−${-n}` : String(n);
  }

  function waitEvent(method, timeoutMs = 30_000) {
    return new Promise((resolve, reject) => {
      const timer = setTimeout(() => {
        socket.removeEventListener("message", hear);
        reject(new Error(`timed out waiting for ${method}`));
      }, timeoutMs);
      function hear(event) {
        const message = JSON.parse(event.data);
        if (message.method !== method) return;
        clearTimeout(timer);
        socket.removeEventListener("message", hear);
        resolve(message);
      }
      socket.addEventListener("message", hear);
    });
  }

  function waitForMainFrame(url) {
    const target = new URL(url, "http://127.0.0.1");
    return new Promise((resolve, reject) => {
      const timer = setTimeout(() => {
        socket.removeEventListener("message", hear);
        reject(new Error(`timed out waiting for ${url}`));
      }, 30_000);
      function hear(event) {
        const message = JSON.parse(event.data);
        if (message.sessionId && message.sessionId !== sessionId) return;
        if (message.method !== "Page.frameNavigated") return;
        const frame = message.params?.frame;
        if (!frame || frame.parentId) return;
        if (target.protocol === "about:") {
          if (!String(frame.url).startsWith("about:blank")) return;
        } else {
          let parsed;
          try {
            parsed = new URL(frame.url);
          } catch {
            return;
          }
          const path = (value) => (value.length > 1 && value.endsWith("/") ? value.slice(0, -1) : value);
          if (parsed.origin !== target.origin || path(parsed.pathname) !== path(target.pathname) || parsed.search !== target.search) return;
        }
        clearTimeout(timer);
        socket.removeEventListener("message", hear);
        resolve(frame);
      }
      socket.addEventListener("message", hear);
    });
  }

  async function open(url) {
    const current = await evalJs(`location.href`);
    // The cut-rule page holds a large exact heap. Drop that document before the
    // next load, or the new page's script evaluation waits behind its teardown
    // and #nbig never fills inside the navigation budget.
    if (typeof current === "string" && current.includes("debug=cut") && !url.includes("debug=cut")) {
      const blank = waitForMainFrame("about:blank");
      await send("Page.navigate", { url: "about:blank" }, sessionId);
      await blank;
    }
    const here = typeof current === "string" && !String(current).includes("debug=cut") ? new URL(current) : null;
    const target = new URL(url);
    const sameDocument = Boolean(here && here.origin === target.origin && here.pathname === target.pathname && here.search === target.search);
    const arrived = sameDocument ? null : waitForMainFrame(url);
    await send("Page.navigate", { url }, sessionId);
    if (arrived) await arrived;
    const want = displayedN(url);
    const hash = new URL(url).hash;
    const deadline = Date.now() + 30_000;
    let last = null;
    while (Date.now() < deadline) {
      last = await evalJs(`({ n: document.getElementById("nbig")?.textContent || "", hash: location.hash, href: location.href, ready: Boolean(document.getElementById("n")) })`);
      if (last?.ready && last.n && (!want || last.n === want) && (!hash || last.hash === hash)) return;
      await delay(50);
    }
    throw new Error(`page did not render ${url} (${JSON.stringify(last)})`);
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
    const big = (document.getElementById("big")?.textContent || "").replace(/\\s+/g, " ").trim();
    const chips = document.getElementById("chips")?.textContent || "";
    const note = document.getElementById("cutnote")?.textContent || "";
    if (!big || big.includes("checking")) return null;
    if (big === "50") window.__sawFifty = true;
    return { big, chips, note, tasks: window.__longtasks.slice() };
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
  const ends = await evalJs(`({
    plus: document.querySelector("[aria-label='n plus 1']")?.disabled === true,
    minus: document.querySelector("[aria-label='n minus 1']")?.disabled === true,
  })`);
  report("plus is disabled at 50 and minus is not", ends?.plus === true && ends?.minus === false, JSON.stringify(ends));
  const fiftyPill = await evalJs(`(document.getElementById("label")?.textContent || "").trim()`);
  const fiftyBuilt = await evalJs(`(document.getElementById("kline")?.textContent || "").includes("(gives exactly n on both cuts, without ln 0)")`);
  report(
    "n = 50 shows checking, then exactly 50, the exact chip, and 94 gates",
    Boolean(sawChecking) && fifty?.big === "50" && fifty.chips.includes("exact mode · 120 digits") && fifty.note.includes("94 gates"),
    fifty ? `${fifty.big} | ${fifty.note}` : "timed out",
  );
  report("n = 50 is a construction, not a search record", fiftyPill === "a construction, not a search record" && fiftyBuilt === true, String(fiftyPill));
  const contrast = await evalJs(`(() => {
    function channel(v) { const s = v / 255; return s <= 0.04045 ? s / 12.92 : ((s + 0.055) / 1.055) ** 2.4; }
    function lum(color) {
      const match = /rgba?\\((\\d+), (\\d+), (\\d+)/.exec(color);
      if (!match) return null;
      return 0.2126 * channel(+match[1]) + 0.7152 * channel(+match[2]) + 0.0722 * channel(+match[3]);
    }
    function background(el) {
      let node = el;
      while (node) {
        const color = getComputedStyle(node).backgroundColor;
        const match = /rgba?\\((\\d+), (\\d+), (\\d+)(?:, ([\\d.]+))?\\)/.exec(color);
        if (match && (match[4] === undefined || Number(match[4]) > 0.5)) return color;
        node = node.parentElement;
      }
      return "rgb(0, 0, 0)";
    }
    function ratio(el) {
      if (!el) return 0;
      const fg = lum(getComputedStyle(el).color);
      const back = lum(background(el));
      if (fg == null || back == null) return 0;
      return (Math.max(fg, back) + 0.05) / (Math.min(fg, back) + 0.05);
    }
    return {
      note: ratio(document.getElementById("cutnote")),
      floatNote: ratio(document.querySelector("#chips .count-note")),
      link: ratio(document.getElementById("docs-link")),
    };
  })()`);
  report(
    "cut note, float note, and docs link reach 4.5:1",
    contrast?.note >= 4.5 && contrast?.floatNote >= 4.5 && contrast?.link >= 4.5,
    JSON.stringify(contrast),
  );
  // Long Tasks use wall-clock time on the main thread, so a render that is
  // under 100 ms when the machine is idle stretches past it while eml:check
  // (or anything else) owns the cores. Scale the budget by a fixed loop
  // measured on this same page. An idle run stays at 100 ms.
  const stretch = await evalJs(`(() => {
    const samples = [];
    for (let s = 0; s < 5; s += 1) {
      const started = performance.now();
      let n = 1;
      for (let i = 0; i < 2000000; i += 1) n = Math.imul(n, 1664525) + i;
      samples.push(performance.now() - started);
    }
    samples.sort((a, b) => a - b);
    return samples[2];
  })()`);
  const idleLoopMs = 25;
  const budget = Math.min(1500, 100 * Math.max(1, Number(stretch) / idleLoopMs));
  const long = (fifty?.tasks || []).filter((duration) => duration > budget);
  report(
    "no long task over 100 ms before the result",
    long.length === 0,
    `budget ${budget.toFixed(0)} ms (loop ${Number(stretch).toFixed(1)} ms) tasks ${(fifty?.tasks || []).join(", ")}`,
  );

  await open(`${site}#n=7`);
  await waitFor(`document.getElementById("nbig")?.textContent === "7"`);
  const repeated = await evalJs(`document.querySelector(".count-x")?.textContent?.trim() || ""`);
  report("outline shows the × n badge", typeof repeated === "string" && repeated.startsWith("× "), String(repeated));
  await evalJs(`document.getElementById("slider").focus()`);
  await send("Input.dispatchKeyEvent", { type: "keyDown", key: "ArrowRight", code: "ArrowRight", windowsVirtualKeyCode: 39 }, sessionId);
  await send("Input.dispatchKeyEvent", { type: "keyUp", key: "ArrowRight", code: "ArrowRight", windowsVirtualKeyCode: 39 }, sessionId);
  const stepped = await waitFor(exactProbe(8), 180_000);
  report("slider ArrowRight steps 7 to 8 and shows exactly 8", stepped === "ok", String(stepped));
  await evalJs(`document.getElementById("slider").blur(); document.body.focus()`);
  await send("Input.dispatchKeyEvent", { type: "keyDown", key: "ArrowLeft", code: "ArrowLeft", windowsVirtualKeyCode: 37 }, sessionId);
  await send("Input.dispatchKeyEvent", { type: "keyUp", key: "ArrowLeft", code: "ArrowLeft", windowsVirtualKeyCode: 37 }, sessionId);
  const steppedBack = await waitFor(exactProbe(7), 180_000);
  report("body ArrowLeft steps 8 to 7 and shows exactly 7", steppedBack === "ok", String(steppedBack));
  await evalJs(`document.querySelector("a.ti-home")?.focus()`);
  await send("Input.dispatchKeyEvent", { type: "keyDown", key: "ArrowRight", code: "ArrowRight", windowsVirtualKeyCode: 39 }, sessionId);
  await send("Input.dispatchKeyEvent", { type: "keyUp", key: "ArrowRight", code: "ArrowRight", windowsVirtualKeyCode: 39 }, sessionId);
  await delay(200);
  const linkHeld = await evalJs(`document.getElementById("nbig")?.textContent || ""`);
  report("arrow keys ignore a focused link", linkHeld === "7", String(linkHeld));

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
  const hashed = await waitFor(exactProbe(12), 180_000);
  report("hashchange shows exactly 12", hashed === "ok", String(hashed));

  await evalJs(`location.hash = "#n=3"`);
  const three = await waitFor(`(() => {
    const big = (document.getElementById("big")?.textContent || "").replace(/\\s+/g, " ").trim();
    const chips = document.getElementById("chips")?.textContent || "";
    if (!big || big.includes("checking")) return "";
    const label = (document.getElementById("label")?.textContent || "").trim();
    const line = document.body.innerText.includes("Lower cut, Arg in [−π, π), ln 0 = −∞. On this cut −iπ becomes +iπ under the principal Log.");
    const ok = big === "3" && chips.includes("exact mode · 120 digits") && label === ${JSON.stringify(THREE_PILL)} && line;
    return ok ? "ok" : "bad:" + big + "|" + label;
  })()`, 180_000);
  report("n = 3 is exactly 3 with its pill and cut line", three === "ok", String(three));

  const docsHref = await evalJs(`document.getElementById("docs-link")?.href || ""`);
  let docsPath = "";
  try {
    docsPath = docsHref ? new URL(docsHref).pathname.replace(/\/$/, "") : "";
  } catch {
    docsPath = "";
  }
  const docsInSite = docsPath.endsWith("/counting") && !String(docsHref).includes("/blob/");
  try {
    const docs = await fetch(docsHref, { redirect: "follow", headers: { "User-Agent": "eml-count-e2e" } });
    if (docs.status === 200 && docsInSite) report("docs link", true, docsHref);
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
    const want = displayedN(`http://127.0.0.1/${hash}`);
    await evalJs(`location.hash = ${JSON.stringify(hash)}`);
    const ready = await waitFor(`(() => {
      const n = document.getElementById("nbig")?.textContent || "";
      return location.hash === ${JSON.stringify(hash)} && n === ${JSON.stringify(want)} ? "ready" : "";
    })()`, 30_000);
    if (ready !== "ready") throw new Error(`did not reach ${hash} (nbig stayed ${await evalJs(`document.getElementById("nbig")?.textContent || ""`)} hash ${await evalJs("location.hash")})`);
    const numeric = Number(String(want).replace("−", "-"));
    const exact = await waitFor(exactProbe(numeric), 180_000);
    if (exact !== "ok") {
      report(`exact value for ${hash}`, false, String(exact));
      return "";
    }
    return waitFor(probe, 180_000);
  }
  const neg2 = await shows("#n=-2", `(() => {
    const text = document.body.innerText;
    const pill = (document.getElementById("label")?.textContent || "").trim();
    const ok = text.includes("K 25") && pill === ${JSON.stringify(NEG2_PILL)};
    return ok ? "ok" : "bad:" + pill;
  })()`);
  report("n = −2 is K 25 and the unproved pill", neg2 === "ok");
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
    const pill = (document.getElementById("label")?.textContent || "").trim();
    return text.includes("K 71") && pill === ${JSON.stringify(KNOWN_PILL)} ? "ok" : "";
  })()`);
  report("n = 8 is K 71 and the unproved pill", eight === "ok");
  const thirteen = await shows("#n=13", `document.body.innerText.includes("K 99") ? "ok" : ""`);
  report("n = 13 is K 99", thirteen === "ok");
  const thirteenFree = await shows("#n=13&noln0", `document.body.innerText.includes("K 101") ? "ok" : ""`);
  report("n = 13 without ln 0 is K 101", thirteenFree === "ok");

  const rangeLabel = await evalJs(`document.querySelector("label[for=n]")?.textContent || ""`);
  report("n field label shows the range", rangeLabel.includes("n, from −50 to 50"), String(rangeLabel));
  const title = await evalJs(`document.title`);
  report("count page title", title === "Count to n — EML and One", String(title));
  const live = await evalJs(`document.querySelectorAll("[aria-live]").length`);
  report("one screen-reader announcement region", live === 1, String(live));
  const provedRows = await shows("#n=0", `(() => {
    const pill = (document.getElementById("label")?.textContent || "").trim();
    const basis = document.getElementById("basis")?.textContent || "";
    const built = document.body.innerText.includes("ln(1) via the ln template 11xE1EE: 7 presses");
    const source = document.body.innerText.includes("Source: integer table: 0 at K 7");
    const kline = document.getElementById("kline")?.textContent || "";
    return pill === ${JSON.stringify(PROVEN_PILL)} && basis.includes("K ≤ 5") && basis.includes("with or without ln 0") && !basis.includes(${JSON.stringify(KNOWN_PILL)}) && built && source && kline.includes("ln(1) via the ln template 11xE1EE: 7 presses") && !kline.includes("built by: counting construction") ? "ok" : "bad:" + pill + "|" + kline;
  })()`);
  report("n = 0 shows the proved pill and its basis", provedRows === "ok", String(provedRows));
  const one = await shows("#n=1", `(() => {
    const pill = (document.getElementById("label")?.textContent || "").trim();
    const basis = document.getElementById("basis");
    const built = document.body.innerText.includes("the 1 key: 1 press");
    const kline = document.getElementById("kline")?.textContent || "";
    return pill === "the 1 key itself · K 1" && !basis && pill !== ${JSON.stringify(PROVEN_PILL)} && built && !kline.includes("counting construction") ? "ok" : "bad:" + pill + "|" + kline;
  })()`);
  report("n = 1 keeps the neutral pill", one === "ok", String(one));
  const negFree = await shows("#n=-1&noln0", `(() => {
    const pill = (document.getElementById("label")?.textContent || "").trim();
    const kline = document.getElementById("kline")?.textContent || "";
    const want = ${JSON.stringify(`${PROVEN_PILL} without ln 0`)};
    const built = "counting construction: K = 10m + 7, m = −n (gives exactly n on both cuts, without ln 0)";
    return pill === want && kline.includes(built) ? "ok" : "bad:" + pill + "|" + kline;
  })()`);
  report("n = −1 without ln 0 uses the construction wording", negFree === "ok", String(negFree));
  const back = await evalJs(`document.querySelector("a.ti-home")?.href || ""`);
  report("count page links back to the calculator", typeof back === "string" && /\/eml-and-one\/?$/.test(back), String(back));

  await evalJs(`(() => {
    const input = document.getElementById("n");
    input.focus();
    const set = Object.getOwnPropertyDescriptor(HTMLInputElement.prototype, "value").set;
    set.call(input, "-5");
    input.dispatchEvent(new Event("input", { bubbles: true }));
    input.dispatchEvent(new KeyboardEvent("keydown", { key: "Enter", bubbles: true }));
  })()`);
  const typed = await waitFor(`(() => {
    const shown = document.getElementById("nbig")?.textContent || "";
    const field = document.getElementById("n")?.value || "";
    return shown === "−5" && field === "-5" ? "ok" : "";
  })()`);
  report("typing -5 keeps -5", typed === "ok", String(typed));
  const typedExact = await waitFor(exactProbe(-5), 180_000);
  report("typing -5 shows exactly −5", typedExact === "ok", String(typedExact));

  await evalJs(`(() => {
    const input = document.getElementById("n");
    input.focus();
    const set = Object.getOwnPropertyDescriptor(HTMLInputElement.prototype, "value").set;
    set.call(input, "−5");
    input.dispatchEvent(new Event("input", { bubbles: true }));
    input.dispatchEvent(new KeyboardEvent("keydown", { key: "Enter", bubbles: true }));
  })()`);
  const typedMinus = await waitFor(`(() => {
    const shown = document.getElementById("nbig")?.textContent || "";
    const field = document.getElementById("n")?.value || "";
    return shown === "−5" && location.hash.includes("n=-5") ? "ok" : field + " " + shown;
  })()`);
  report("typing U+2212 −5 keeps −5", typedMinus === "ok", String(typedMinus));

  await evalJs(`(() => {
    const input = document.getElementById("n");
    input.focus();
    const set = Object.getOwnPropertyDescriptor(HTMLInputElement.prototype, "value").set;
    set.call(input, "+3");
    input.dispatchEvent(new Event("input", { bubbles: true }));
    input.dispatchEvent(new KeyboardEvent("keydown", { key: "Enter", bubbles: true }));
  })()`);
  const typedPlus = await waitFor(`(() => {
    const shown = document.getElementById("nbig")?.textContent || "";
    return shown === "3" && location.hash.includes("n=3") ? "ok" : "";
  })()`);
  report("typing +3 shows 3", typedPlus === "ok", String(typedPlus));

  for (const bad of ["#n=1e400", "#n=1e5", "#n=3.5", "#n=2.9", "#n=999", "#n=99"]) {
    const token = bad.slice(3);
    await evalJs(`location.hash = ${JSON.stringify(bad)}`);
    const rejected = await waitFor(`(() => {
      const error = document.getElementById("n-error")?.textContent || "";
      const shown = document.getElementById("nbig")?.textContent || "";
      const field = document.getElementById("n")?.value || "";
      return error && field === ${JSON.stringify(token)} && shown === "—" && location.hash.includes(${JSON.stringify("n=" + token)}) ? "ok" : "";
    })()`, 10_000);
    report("bad address " + bad + " shows an error", rejected === "ok", String(rejected));
  }
  await evalJs(`location.hash = "#nope"`);
  const nope = await waitFor(`(() => {
    const error = document.getElementById("n-error")?.textContent || "";
    const shown = document.getElementById("nbig")?.textContent || "";
    const wordmark = document.querySelector("h1")?.textContent || "";
    return error.includes("−50") && shown === "—" && location.hash === "#nope" && wordmark.includes("EML") ? "ok" : error + "|" + shown + "|" + location.hash;
  })()`, 10_000);
  report("bad address #nope shows an error", nope === "ok", String(nope));
  await evalJs(`location.hash = "#n=-5"`);
  await waitFor(`document.getElementById("nbig")?.textContent === "−5" ? "ok" : ""`);

  await evalJs(`(() => {
    const input = document.getElementById("n");
    input.focus();
    const set = Object.getOwnPropertyDescriptor(HTMLInputElement.prototype, "value").set;
    set.call(input, "999");
    input.dispatchEvent(new Event("input", { bubbles: true }));
    input.blur();
  })()`);
  const outOfRange = await waitFor(`(() => {
    const error = document.getElementById("n-error")?.textContent || "";
    const shown = document.getElementById("nbig")?.textContent || "";
    return error && shown === "−5" ? error : "";
  })()`);
  report("out-of-range input shows an error and does not clamp", Boolean(outOfRange) && String(outOfRange).includes("−50"), String(outOfRange));

  await evalJs(`(() => {
    const input = document.getElementById("n");
    input.focus();
    const set = Object.getOwnPropertyDescriptor(HTMLInputElement.prototype, "value").set;
    set.call(input, "1.5");
    input.dispatchEvent(new Event("input", { bubbles: true }));
    input.blur();
  })()`);
  const nonInteger = await waitFor(`(() => {
    const error = document.getElementById("n-error")?.textContent || "";
    const shown = document.getElementById("nbig")?.textContent || "";
    const field = document.getElementById("n")?.value || "";
    return error && shown === "−5" && field === "1.5" ? "ok" : "";
  })()`);
  report("non-integer input shows an error", nonInteger === "ok");

  const focus = await evalJs(`(() => {
    function ring(el) {
      if (!el) return false;
      try { el.focus({ focusVisible: true }); }
      catch { el.focus(); }
      const style = getComputedStyle(el);
      return style.outlineStyle !== "none" && parseFloat(style.outlineWidth) >= 2;
    }
    const copy = [...document.querySelectorAll("button")].find((item) => item.textContent.trim().startsWith("Copy as 1"));
    return {
      n: ring(document.getElementById("n")),
      slider: ring(document.getElementById("slider")),
      ln0: ring(document.getElementById("ln0")),
      home: ring(document.querySelector("a.ti-home")),
      docs: ring(document.getElementById("docs-link")),
      copy: ring(copy),
    };
  })()`);
  report("focus ring on the n field, slider, ln 0 box, links, and Copy", Boolean(focus) && Object.values(focus).every(Boolean), JSON.stringify(focus));

  await send("Emulation.setDeviceMetricsOverride", { width: 320, height: 900, deviceScaleFactor: 1, mobile: true }, sessionId);
  await delay(200);
  const small = await evalJs(`(() => {
    return [...document.querySelectorAll(".count-layout a, .count-layout button, .count-layout input")].flatMap((el) => {
      const rect = el.getBoundingClientRect();
      if (rect.width === 0 && rect.height === 0) return [];
      return [{ name: el.id || el.getAttribute("aria-label") || el.textContent.trim().slice(0, 24), w: Math.round(rect.width), h: Math.round(rect.height) }];
    }).filter((item) => item.w < 44 || item.h < 44);
  })()`);
  report("phone targets are at least 44px", Array.isArray(small) && small.length === 0, JSON.stringify(small));
  const deviceH = await evalJs(`document.querySelector(".count-layout .ti-device")?.getBoundingClientRect().height || 0`);
  report("phone device does not fill the screen before the panels", deviceH > 0 && deviceH < 800, String(deviceH));
  await send("Emulation.setDeviceMetricsOverride", { width: 844, height: 390, deviceScaleFactor: 1, mobile: true }, sessionId);
  await delay(200);
  const landscape = await evalJs(`(() => {
    return [...document.querySelectorAll(".count-layout a, .count-layout button, .count-layout input")].flatMap((el) => {
      const rect = el.getBoundingClientRect();
      if (rect.width === 0 && rect.height === 0) return [];
      return [{ name: el.id || el.getAttribute("aria-label") || el.textContent.trim().slice(0, 24), w: Math.round(rect.width), h: Math.round(rect.height) }];
    }).filter((item) => item.w < 44 || item.h < 44);
  })()`);
  report("landscape targets are at least 44px", Array.isArray(landscape) && landscape.length === 0, JSON.stringify(landscape));
  await send("Emulation.clearDeviceMetricsOverride", {}, sessionId);

  await evalJs(`(() => {
    window.__copyErrors = [];
    window.addEventListener("unhandledrejection", (event) => window.__copyErrors.push(String(event.reason && event.reason.message || event.reason)));
    [...document.querySelectorAll("button")].find((item) => item.textContent.trim() === "Copy as 1 / E")?.click();
  })()`);
  const copied = await waitFor(`document.getElementById("copy-status")?.textContent || ""`);
  const copyErrors = await evalJs(`window.__copyErrors || []`);
  report(
    "copy shows Copied or a visible failure",
    (copied === "Copied" || copied === "Could not copy") && Array.isArray(copyErrors) && copyErrors.length === 0,
    `${copied} ${JSON.stringify(copyErrors)}`,
  );

  const keptN = await evalJs(`document.getElementById("nbig")?.textContent || ""`);
  await evalJs(`document.getElementById("docs-link")?.click()`);
  const onDocs = await waitFor(`document.querySelector(".count-doc") ? "yes" : ""`, 20_000);
  await evalJs(`([...document.querySelectorAll("a")].find((item) => item.textContent.trim() === "Count to n") || {}).click()`);
  const docsBack = await waitFor(`(() => {
    const shown = document.getElementById("nbig")?.textContent || "";
    return shown && shown === ${JSON.stringify(String(keptN))} ? "ok" : "";
  })()`, 20_000);
  report("docs link does not reset n", onDocs === "yes" && docsBack === "ok", `${onDocs} ${docsBack} wanted ${keptN}`);

  await evalJs(`document.querySelector("a.ti-home")?.click()`);
  const onCalc = await waitFor(`document.body.innerText.includes("a two-button calculator") ? "yes" : ""`, 20_000);
  const focused = await waitFor(`document.activeElement?.tagName === "H1" ? "H1" : ""`, 5_000);
  report("page change moves focus to the heading", onCalc === "yes" && focused === "H1", String(focused));
  await evalJs(`(() => {
    const input = document.getElementById("expr");
    const set = Object.getOwnPropertyDescriptor(HTMLInputElement.prototype, "value").set;
    set.call(input, "1+1");
    input.dispatchEvent(new Event("input", { bubbles: true }));
    [...document.querySelectorAll("button")].find((item) => item.getAttribute("aria-label")?.startsWith("Push the constant 1"))?.click();
  })()`);
  const stacked = await waitFor(`(() => {
    const tape = document.querySelector(".ti-footer .ti-tape")?.textContent || "";
    const result = document.querySelector(".ti-lcd-result")?.textContent || "";
    const expr = document.getElementById("expr")?.value || "";
    return tape.includes("1") && result.trim() === "1" && expr === "1+1" ? "ok" : "";
  })()`);
  const lengthBefore = await evalJs(`history.length`);
  await evalJs(`([...document.querySelectorAll("a")].find((item) => item.textContent.trim() === "Count to n") || {}).click()`);
  const onCount = await waitFor(`document.getElementById("nbig")?.textContent ? "yes" : ""`, 20_000);
  await evalJs(`document.querySelector("[aria-label='n plus 1']")?.click()`);
  await evalJs(`document.querySelector("[aria-label='n plus 1']")?.click()`);
  await delay(100);
  const lengthAfter = await evalJs(`history.length`);
  report("n updates do not add history entries", onCount === "yes" && lengthAfter === lengthBefore + 1, `${lengthBefore} -> ${lengthAfter}`);
  await evalJs(`history.back()`);
  const oneBack = await waitFor(`(() => {
    const calc = document.body.innerText.includes("a two-button calculator");
    const count = location.pathname.includes("/count");
    return calc && !count ? "ok" : "";
  })()`, 20_000);
  report("one Back leaves Count to n", oneBack === "ok", String(oneBack));
  const kept = await waitFor(`(() => {
    const tape = document.querySelector(".ti-footer .ti-tape")?.textContent || "";
    const result = document.querySelector(".ti-lcd-result")?.textContent || "";
    const expr = document.getElementById("expr")?.value || "";
    return tape.includes("1") && result.trim() === "1" && expr === "1+1" ? "ok" : "";
  })()`);
  report("calculator stack, tape, and expression survive the header", stacked === "ok" && kept === "ok", `${stacked} ${kept}`);

  await evalJs(`([...document.querySelectorAll("a")].find((item) => item.textContent.trim() === "Count to n") || {}).click()`);
  await waitFor(`document.getElementById("nbig")?.textContent ? "yes" : ""`, 20_000);
  await evalJs(`location.hash = "#n=20"`);
  const edited = await waitFor(`document.getElementById("nbig")?.textContent === "20" ? "ok" : ""`);
  await evalJs(`document.querySelector("a.ti-home")?.click()`);
  await waitFor(`document.body.innerText.includes("a two-button calculator") ? "yes" : ""`, 20_000);
  await evalJs(`history.back()`);
  const returned = await waitFor(`(() => {
    const model = document.querySelector(".ti-model")?.textContent || "";
    const shown = document.getElementById("nbig")?.textContent || "";
    return location.pathname.includes("/count") && model.includes("count to n") && shown === "20" ? "ok" : "";
  })()`, 20_000);
  report("Back after an edited address shows the count page", edited === "ok" && returned === "ok", `${edited} ${returned}`);

  const calcLoaded = waitEvent("Page.loadEventFired");
  await send("Page.navigate", { url: `http://127.0.0.1:${port}/eml-and-one/` }, sessionId);
  await calcLoaded;
  const calcLink = await waitFor(`(() => {
    const link = [...document.querySelectorAll("a")].find((item) => {
      const path = new URL(item.href).pathname.replace(/\\/$/, "");
      return path.endsWith("/count") && item.textContent.trim() === "Count to n";
    });
    return link ? link.href : "";
  })()`, 20000);
  report("calculator links to the count page", typeof calcLink === "string" && calcLink.includes("/count"), String(calcLink));
  await send("Emulation.setDeviceMetricsOverride", { width: 844, height: 390, deviceScaleFactor: 1, mobile: true }, sessionId);
  await delay(200);
  const countToN = await evalJs(`(() => {
    const link = [...document.querySelectorAll("a")].find((item) => item.textContent.trim() === "Count to n");
    if (!link) return null;
    const rect = link.getBoundingClientRect();
    return { w: Math.round(rect.width), h: Math.round(rect.height) };
  })()`);
  report("landscape Count to n link is at least 44px", Boolean(countToN) && countToN.h >= 44 && countToN.w >= 44, JSON.stringify(countToN));
  await send("Emulation.clearDeviceMetricsOverride", {}, sessionId);
  const calcTitle = await evalJs(`document.title`);
  report("calculator title stays distinct", calcTitle === "EML and One", String(calcTitle));

  const countingLoaded = waitEvent("Page.loadEventFired");
  await send("Page.navigate", { url: `http://127.0.0.1:${port}/eml-and-one/counting/` }, sessionId);
  await countingLoaded;
  const counting = await evalJs(`(() => {
    const html = document.querySelector(".count-doc")?.innerHTML || "";
    const links = [...document.querySelectorAll(".count-doc-nav a")];
    const boxes = links.map((link) => link.getBoundingClientRect());
    const gap = boxes.length === 2 ? boxes[1].left - boxes[0].right : 0;
    return {
      sub: html.includes("<sub>"),
      sup: html.includes("<sup>"),
      list: document.querySelectorAll(".count-doc li").length,
      raw: html.includes("c_{") || html.includes("c_k"),
      links: links.length,
      gap,
    };
  })()`);
  report(
    "counting page renders math, a list, and separated links",
    Boolean(counting?.sub) && Boolean(counting?.sup) && counting.list >= 6 && !counting.raw && counting.links === 2 && counting.gap >= 8,
    JSON.stringify(counting),
  );

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
