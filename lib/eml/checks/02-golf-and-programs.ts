import type { CheckModule } from "./_types";
import { makeCheckHelpers } from "./_helpers";
import { c, clog, close } from "../complex";
import { circuitStats, describe, E, EmlError, evaluate, evaluateReport, expUnderflows, input, type Node, nodeFromRpn, ONE, rpnTokens, V } from "../node";
import { constantNode, tAdd, X, Y } from "../library";
import { acceptsConstantProgram, acceptsConstantValue, functionFingerprint, ln0Dependence, searchConstants, searchConstantsMerged } from "../golf";
import { exactClose, exactEvaluate, exactParts, exactToFloat, exactValueAt } from "../exact";
import { nodeFromCompact, programNode } from "../programs";
import { rotSubCircuit } from "../lowering";
import { compileExpression } from "../parse";
import { ballVerdict, enclose } from "../enclose";
import { approximateIndexBits, catalan, isProgram, parseProgramInput, programIndexDigits, programNumberText, rankProgram, rankRpn, rotateToProgram, stepProgram, unnumberedReason, unrankProgram, unrankRpn } from "../programIndex";
import { encodePresses, pressPreviewForNode, previewPresses } from "../presses";

/**
 * Constant golf search, program ranking/unranking, press previews, and short-program catalog.
 */
const checks: CheckModule[] = [
  {
    id: "core-golf",
    weight: 400,
    run(ctx) {
      const { absClose } = makeCheckHelpers(ctx);
      if (clog(c(-1, 0)).im !== -Math.PI || clog(c(-1, -0)).im !== -Math.PI) {
        ctx.fail("FAIL pinned cut", clog(c(-1, 0)), clog(c(-1, -0)));
      }
      if (evaluate(constantNode("i")).im <= 0) {
        ctx.fail("FAIL i sign");
      }
      const wantedK: Record<string, number> = {
        e: 3,
        "0": 7,
        "-1": 15,
        "2": 19,
        ipi: 21,
      };
      const searchedRun = searchConstants(21);
      const searched = searchedRun.hits;
      // The pool keeps every finite circuit that did not overflow: 16311 through K 21, the same as v1.0.
      if (searchedRun.pool !== 16311) {
        ctx.fail("FAIL K21 pool changed", searchedRun.pool);
      }
      for (const [id, k] of Object.entries(wantedK)) {
        const hit = searched.find((item) => item.id === id);
        if (!hit || hit.k !== k) {
          ctx.fail("FAIL K", id, hit, "want", k);
        }
      }
      const ipiWord = "111111E1EEEE11E1E1EEE";
      const ipiNode = nodeFromRpn(ipiWord.split(""));
      const ipiValue = evaluate(ipiNode);
      if (ipiValue.im <= 0 || Math.abs(ipiValue.re) > 1e-6) {
        ctx.fail("FAIL K21 word is +iπ on this cut", ipiValue);
      }
      const ipiHit = searched.find((item) => item.rpn === ipiWord);
      if (ipiHit && ipiHit.id !== "ipi") {
        ctx.fail("FAIL golf labeled the K21 word", ipiHit.id);
      }
      const namedIpi = searched.find((item) => item.id === "ipi");
      if (namedIpi && evaluate(nodeFromRpn(namedIpi.rpn.split(""))).im <= 0) {
        ctx.fail("FAIL golf ipi label is the negative cut", namedIpi.rpn);
      }
      const negPi = exactValueAt(ipiNode, 280).im.neg();
      const k33Word = "11111EE1E1111E1E1EEEE1EE11E1E1EEE";
      const k35Word = "11111111E1E1EEEEEE111EEE1E11E1E1EEE";
      const k33Node = nodeFromCompact(k33Word);
      const k35Node = nodeFromCompact(k35Word);
      // The K 33 word is 5.724×10^(−116) − iπ. A 40-digit read either loses that part (0) or,
      // once it re-reads a log just off the negative axis, keeps its true value. Never −iπ.
      const k33At40 = exactValueAt(k33Node, 40);
      const k33Re = k33At40.re.isZero() || k33At40.re.sub("5.724022659417535e-116").abs().lt("1e-129");
      if (!k33Re || acceptsConstantProgram(k33Node, 0, -Math.PI)) {
        ctx.fail("FAIL K33 word", k33At40.re.toString(), acceptsConstantProgram(k33Node, 0, -Math.PI));
      }
      if (acceptsConstantProgram(k35Node, 0, -Math.PI)) {
        ctx.fail("FAIL K35 −iπ impostor was accepted");
      }
      // A deeper one: −9×10^(−307) − i(π − 4×10^(−307)). The ball and the 280-digit compare
      // both read it as −iπ; exact mode sees the 10^(−306) part it passes through.
      const k35DeepNode = nodeFromCompact("11111111E11E1EE1EEEEEE1E1E11E1E1EEE");
      if (acceptsConstantProgram(k35DeepNode, 0, -Math.PI)) {
        ctx.fail("FAIL K35 −iπ impostor near 10^(−307) was accepted");
      }
      const rot = rotSubCircuit(V("x"), V("y"));
      const rotStats = circuitStats(rot);
      if (rotStats.rpnLength !== BigInt(131) || rotStats.dagGates !== 34) {
        ctx.fail("FAIL rotSub size", rotStats.rpnLength.toString(), rotStats.dagGates);
      }
      if (!acceptsConstantValue(exactParts(0, negPi), 0, -Math.PI)) {
        ctx.fail("FAIL exact −iπ was rejected");
      }
      if (!acceptsConstantValue(exactValueAt(ipiNode, 280), 0, Math.PI)) {
        ctx.fail("FAIL K21 +iπ failed the 240-digit check");
      }
      if (acceptsConstantValue(exactParts("-1.00000000000000000001", "0"), -1, 0)) {
        ctx.fail("FAIL −1 + 10^(−20) was accepted");
      }
      if (acceptsConstantValue(exactParts("0", "3.1415926535897932384726433832795"), 0, Math.PI)) {
        ctx.fail("FAIL i(π + 10^(−20)) was accepted");
      }
      if (searched.some((hit) => hit.id === "-ipi")) {
        ctx.fail("FAIL golf kept a −iπ hit by K 21");
      }
      const minusOne = searched.find((item) => item.id === "-1");
      const halfHit = searched.find((item) => item.id === "1/2");
      if (minusOne && (!minusOne.usesLn0 || minusOne.singular)) {
        ctx.fail("FAIL -1 ln 0 should be recorded but finite", minusOne);
      }
      if (halfHit) {
        ctx.fail("FAIL 1/2 appeared before K 21", halfHit);
      }
      const noInf = searchConstants(15, { allowLn0: false }).hits;
      if (noInf.some((hit) => hit.usesLn0 || hit.domain === "extended") || noInf.some((hit) => hit.id === "-1")) {
        ctx.fail("FAIL no-inf search kept a ln 0 program", noInf);
      }
      if (!noInf.some((hit) => hit.id === "0") || !noInf.some((hit) => hit.id === "e")) {
        ctx.fail("FAIL no-inf search dropped a finite constant", noInf.map((hit) => hit.id));
      }

      if (minusOne && ln0Dependence(minusOne) !== "depends on ln 0 = −∞") {
        ctx.fail("FAIL -1 was not labeled as depending on ln 0", minusOne);
      }
      const solo = searchConstantsMerged(15, 1);
      const split = searchConstantsMerged(15, 4);
      for (const id of ["e", "0", "-1"]) {
        if (solo.find((item) => item.id === id)?.k !== split.find((item) => item.id === id)?.k) {
          ctx.fail("FAIL worker merge", id, solo, split);
        }
      }
      const fingerA = functionFingerprint(tAdd(X, Y), (point) => ({ x: point, y: { re: 0.3, im: -0.2 } }));
      const fingerB = functionFingerprint(tAdd(Y, X), (point) => ({ x: point, y: { re: 0.3, im: -0.2 } }));
      if (fingerA !== fingerB) {
        ctx.fail("FAIL fingerprint add");
      }
      const kept = exactToFloat(exactEvaluate(tAdd(X, Y), { x: c(-2.5, 1e-4), y: c(0.3, -0.2) }));
      absClose("exact add keeps 1e-4", kept, -2.2, -0.1999, 1e-12);
      const gate = E(ONE, ONE);
      if (gate.type !== "eml") throw new Error("expected an eml node");
      const cycle = { type: "eml" as const, a: gate, b: ONE, id: -1 };
      cycle.a = cycle;
      try {
        evaluate(cycle);
        ctx.fail("FAIL cycle evaluate did not throw");
      } catch (err) {
        if (!(err instanceof EmlError) || err.message !== "Could not evaluate this circuit.") {
          ctx.fail("FAIL cycle evaluate", err);
        }
      }
      try {
        circuitStats(cycle);
        ctx.fail("FAIL cycle stats did not throw");
      } catch (err) {
        if (!(err instanceof EmlError) || err.message !== "Could not evaluate this circuit.") {
          ctx.fail("FAIL cycle stats", err);
        }
      }
      if (describe(cycle) !== null || rpnTokens(cycle) !== null) {
        ctx.fail("FAIL cycle text", describe(cycle), rpnTokens(cycle));
      }
      if (evaluate(ONE).re !== 1 || evaluate(ONE).im !== 0) {
        ctx.fail("FAIL one", evaluate(ONE));
      }
      const regressions: [string, number, number][] = [
        ["sin(1e-5)", 1e-5, 0],
        ["sin(pi/6)", 0.5, 0],
        ["asinh(-2)", Math.asinh(-2), 0],
        ["asinh(0)", 0, 0],
        ["hypot(-3,4)", 5, 0],
        ["hypot(0,5)", 5, 0],
        ["avg(0,5)", 2.5, 0],
        ["1000+i", 1000, 1],
        ["arcsin(1)", Math.PI / 2, 0],
        ["0-ln(-2)", -Math.log(2), -Math.PI],
        ["1-ln(-1)", 1, -Math.PI],
        ["2-(pi-1e-12)*i", 2, -(Math.PI - 1e-12)],
        ["sqrt(1e-4)", 0.01, 0],
        ["(1+1e-15)-1", 0, 0],
      ];
      for (const [source, re, im] of regressions) {
        const got = evaluate(compileExpression(source, {}));
        if (source === "(1+1e-15)-1") {
          const exact = exactToFloat(exactEvaluate(compileExpression(source, {})));
          if (got.re === 0 || got.im !== 0 || !close(got, c(1.1102230246251565e-15), 1e-6)) {
            ctx.fail("FAIL float tiny subtraction", got);
          }
          if (!close(exact, c(1e-15), 1e-9)) {
            ctx.fail("FAIL exact tiny subtraction", exact);
          }
          continue;
        }
        if (!close(got, c(re, im), 1e-8)) {
          ctx.fail("FAIL", source, got, re, im);
        }
      }
    },
  },
  {
    id: 8,
    weight: 1983,
    run(ctx) {
      const k23Word = "111111E1E1EEE1EE11E1EEE";
      const k23Node = nodeFromCompact(k23Word);
      const k23Ball = enclose(k23Node);
      if (ballVerdict(k23Ball, 0, -Math.PI) === "equal" || ballVerdict(k23Ball, 0, Math.PI) === "equal") {
        ctx.fail("FAIL K23 ball certified a branch", k23Ball.cut, k23Ball.im.toString());
      }
      if (!acceptsConstantProgram(k23Node, 0, Math.PI) || acceptsConstantProgram(k23Node, 0, -Math.PI)) {
        ctx.fail("FAIL K23 acceptance", acceptsConstantProgram(k23Node, 0, Math.PI), acceptsConstantProgram(k23Node, 0, -Math.PI));
      }
      const halfNode = programNode("1/2-strict");
      if (ballVerdict(enclose(halfNode), 0.5, 0) === "equal" || !acceptsConstantProgram(halfNode, 0.5, 0)) {
        ctx.fail("FAIL cut ball certified 1/2", ballVerdict(enclose(halfNode), 0.5, 0));
      }
      for (const [id, re, im] of [
        ["e", Math.E, 0],
        ["0", 0, 0],
        ["2", 2, 0],
        ["3", 3, 0],
      ] as const) {
        const verdict = ballVerdict(enclose(programNode(id)), re, im);
        if (verdict !== "equal" || !acceptsConstantProgram(programNode(id), re, im)) {
          ctx.fail("FAIL ball did not certify", id, verdict);
        }
      }
      const noInfPi = searchConstants(23, { allowLn0: false }).hits;
      const cleanPi = noInfPi.find((item) => item.id === "ipi");
      if (!cleanPi || cleanPi.k !== 23 || cleanPi.usesLn0 || cleanPi.rpn !== k23Word) {
        ctx.fail("FAIL no-inf +iπ", cleanPi);
      }
    },
  },
  {
    id: 27,
    weight: 10907,
    run(ctx) {
      let total = BigInt(0);
      for (let n = 0; n <= 12; n += 1) total += catalan(n);
      for (let i = BigInt(0); i < total; i += BigInt(1)) {
        const rpn = unrankRpn(i);
        if (rankRpn(rpn) !== i || !isProgram(rpn)) {
          ctx.fail("FAIL program round trip", i.toString(), rpn);
          break;
        }
        const node = unrankProgram(i);
        if (rankProgram(node) !== i || unrankProgram(i) !== node) {
          ctx.fail("FAIL node round trip", i.toString());
          break;
        }
      }
    },
  },
  {
    id: 28,
    weight: 261,
    run(ctx) {
      const first = `${"1".repeat(1001)}${"E".repeat(1000)}`;
      const index = rankRpn(first);
      const last = unrankRpn(index + catalan(1000) - BigInt(1));
      if (unrankRpn(index) !== first || rankRpn(last) !== index + catalan(1000) - BigInt(1)) {
        ctx.fail("FAIL n=1000 round trip");
      }
      const node = unrankProgram(index);
      if (rankProgram(node) !== index || unrankProgram(index) !== node) {
        ctx.fail("FAIL n=1000 node round trip");
      }
      let tower: Node = ONE;
      for (let i = 0; i < 20; i += 1) tower = E(tower, tower);
      if (rankProgram(tower) !== null || !programNumberText(tower)?.startsWith("program ≈ 2^")) {
        ctx.fail("FAIL large program number", programNumberText(tower));
      }
    },
  },
  {
    id: "core-program-index",
    weight: 50,
    run(ctx) {
      if (approximateIndexBits(BigInt(10)) !== BigInt(14)) {
        ctx.fail("FAIL approximate bits", approximateIndexBits(BigInt(10)));
      }
      const numbered: Array<[bigint, ReturnType<typeof c>]> = [
        [BigInt(1), c(Math.E)],
        [BigInt(5), c(0)],
        [BigInt(242), c(-1)],
        [BigInt(2431), c(2)],
        [BigInt(98362), c(-2)],
      ];
      for (const [index, value] of numbered) {
        const node = unrankProgram(index);
        if (!close(evaluate(node), value, 1e-9) || rankProgram(node) !== index) {
          ctx.fail("FAIL known program", index.toString(), evaluate(node));
        }
      }
      if (stepProgram(BigInt(0), -1) !== BigInt(0) || stepProgram(BigInt(5), 1) !== BigInt(6) || stepProgram(BigInt(5), -1) !== BigInt(4)) {
        ctx.fail("FAIL stepProgram");
      }
      if (rankProgram(V("x")) !== null || rankProgram(E(V("y"), ONE)) !== null || rankProgram(input(c(3), "3")) !== null) {
        ctx.fail("FAIL rank of a non-constant");
      }
      for (let n = 0; n <= 7; n += 1) {
        const count = catalan(n);
        let begin = BigInt(0);
        for (let m = 0; m < n; m += 1) begin += catalan(m);
        for (let k = BigInt(0); k < count; k += BigInt(1)) {
          const rpn = unrankRpn(begin + k);
          const turns: string[] = [];
          for (let i = 0; i < rpn.length; i += 1) turns.push(rpn.slice(i) + rpn.slice(0, i));
          const valid = turns.filter(isProgram);
          if (valid.length !== 1 || valid[0] !== rpn || turns.some((turn) => rotateToProgram(turn) !== rpn)) {
            ctx.fail("FAIL rotation", rpn);
            n = 8;
            break;
          }
        }
      }
    },
  },
  {
    id: 29,
    weight: 2,
    run(ctx) {
      const short = previewPresses("110");
      const exact = previewPresses("1".repeat(30));
      const over = previewPresses("1".repeat(31));
      if (short.preview !== "110" || short.truncated || short.presses !== BigInt(3)) {
        ctx.fail("FAIL short presses", short);
      }
      if (exact.preview !== "1".repeat(30) || exact.truncated || exact.presses !== BigInt(30)) {
        ctx.fail("FAIL 30 presses", exact);
      }
      if (over.preview !== `${"1".repeat(30)}…` || !over.truncated || over.presses !== BigInt(31)) {
        ctx.fail("FAIL 31 presses", over);
      }
      if (encodePresses(["1", "1", "E"]) !== "110" || encodePresses(["1", "x", "E", "y"]) !== "1x0y" || encodePresses(["2"]) !== null) {
        ctx.fail("FAIL press alphabet");
      }
      const emlPress = pressPreviewForNode(E(ONE, ONE));
      const named = pressPreviewForNode(E(V("x"), ONE));
      if (!emlPress || emlPress.full !== "110" || emlPress.usesVariables) {
        ctx.fail("FAIL e presses", emlPress);
      }
      if (!named || named.full !== "x10" || !named.usesVariables) {
        ctx.fail("FAIL variable presses", named);
      }
      if (pressPreviewForNode(input(c(3), "3")) !== null) {
        ctx.fail("FAIL typed press string");
      }
      let wide: Node = ONE;
      for (let i = 0; i < 15; i += 1) wide = E(wide, ONE);
      const widePress = pressPreviewForNode(wide);
      if (!widePress || widePress.presses !== BigInt(31) || !widePress.truncated || widePress.preview.length !== 31 || !widePress.preview.endsWith("…")) {
        ctx.fail("FAIL wide press preview", widePress);
      }
      let shared: Node = ONE;
      for (let i = 0; i < 14; i += 1) shared = E(shared, shared);
      const over20k = pressPreviewForNode(shared);
      if (!over20k || over20k.presses !== (BigInt(1) << BigInt(15)) - BigInt(1) || over20k.copyable || over20k.presses <= BigInt(20_000)) {
        ctx.fail("FAIL press count past 20000", over20k?.presses.toString());
      }
      let tower61: Node = ONE;
      for (let i = 0; i < 61; i += 1) tower61 = E(tower61, tower61);
      const huge = pressPreviewForNode(tower61);
      const hugeCount = (BigInt(1) << BigInt(62)) - BigInt(1);
      if (!huge || huge.presses !== hugeCount || huge.copyable || huge.presses === BigInt(Number.MAX_SAFE_INTEGER)) {
        ctx.fail("FAIL press count past 2^53", huge?.presses.toString());
      }
      const hugeNumber = programNumberText(tower61);
      const bits = /2\^(\d+)/.exec(hugeNumber ?? "");
      if (!bits || BigInt(bits[1] ?? "0") < BigInt(2) ** BigInt(60)) {
        ctx.fail("FAIL tower index bits", hugeNumber);
      }
      const reason = unnumberedReason(tower61);
      if (!reason || !reason.includes("past 1000") || !reason.includes("10^")) {
        ctx.fail("FAIL unnumbered reason", reason);
      }
    },
  },
  {
    id: 30,
    weight: 2,
    run(ctx) {
      const records: Record<string, string> = {
        e: "1",
        "0": "5",
        "-inf": "24",
        "-1": "242",
        "2": "2431",
        "-2": "98362",
        ipi: "7948",
        ln2: "85587",
        "3": "1086729",
        "-1/2": "1131653",
        "1/2": "2246702",
        "1/2-strict": "8107003",
        sqrt2: "1432982456885549",
        i: "99292101684726",
        pi: "3125315318547434611379164",
      };
      for (const [id, indexText] of Object.entries(records)) {
        const index = BigInt(indexText);
        const node = programNode(id);
        if (rankProgram(node) !== index || unrankProgram(index) !== node) {
          ctx.fail("FAIL record number", id, rankProgram(node)?.toString());
          break;
        }
        if (id === "pi") {
          const digits = programIndexDigits(node);
          const shown = programNumberText(node);
          if (digits !== indexText || shown !== `program #${indexText.slice(0, 4)}…${indexText.slice(-4)} (${indexText.length} digits)`) {
            ctx.fail("FAIL pi number text", digits, shown);
          }
        }
      }
      if (rankRpn("1") !== BigInt(0)) {
        ctx.fail("FAIL program 0");
      }
    },
  },
  {
    id: 31,
    weight: 15,
    run(ctx) {
      const copied = pressPreviewForNode(unrankProgram(BigInt(1)));
      const pasted = copied ? parseProgramInput(copied.full) : null;
      const roundTrip = pasted && pasted.kind === "word" ? rankProgram(nodeFromRpn(pasted.word.split(""))) : null;
      if (!copied || copied.full !== "110" || pasted?.kind !== "word" || pasted.word !== "11E" || roundTrip !== BigInt(1)) {
        ctx.fail("FAIL copy paste round trip", copied?.full, pasted, roundTrip?.toString());
      }
      const one = parseProgramInput("1");
      const hashOne = parseProgramInput("#1");
      const hash110 = parseProgramInput("#110");
      const wordE = parseProgramInput("1E1");
      const wordLower = parseProgramInput("1e1");
      const spacedWord = parseProgramInput("1 1 E");
      const variable = parseProgramInput("x10");
      if (one.kind !== "word" || rankRpn(one.word) !== BigInt(0)) {
        ctx.fail("FAIL press 1 is program 0", one);
      }
      if (hashOne.kind !== "index" || hashOne.index !== BigInt(1) || hash110.kind !== "index" || hash110.index !== BigInt(110)) {
        ctx.fail("FAIL hash numbers", hashOne, hash110);
      }
      if (wordE.kind !== "word" || wordE.word !== "11E" || wordE.rotatedFrom !== "1E1" || wordLower.kind !== "word" || wordLower.word !== "11E" || wordLower.rotatedFrom !== "1E1" || spacedWord.kind !== "word" || spacedWord.word !== "11E" || spacedWord.rotatedFrom !== null) {
        ctx.fail("FAIL word input", wordE, wordLower, spacedWord);
      }
      const turned = parseProgramInput("E11");
      const turnedPress = parseProgramInput("011");
      if (turned.kind !== "word" || turned.word !== "11E" || turned.rotatedFrom !== "E11" || turnedPress.kind !== "word" || turnedPress.word !== "11E" || turnedPress.rotatedFrom !== "011") {
        ctx.fail("FAIL rotated word", turned, turnedPress);
      }
      for (const [text, needle] of [["xE", "two values"], ["xy", "one value"], ["Exy", "two values"]] as const) {
        let message = "";
        try {
          parseProgramInput(text);
        } catch (err) {
          message = err instanceof Error ? err.message : "";
        }
        if (!message.includes(needle) || /missing a value|did not leave one value/i.test(message)) {
          ctx.fail("FAIL variable word", text, message);
        }
      }
      if (variable.kind !== "word" || variable.word !== "x1E" || nodeFromRpn(variable.word.split("")) !== E(V("x"), ONE)) {
        ctx.fail("FAIL variable presses", variable);
      }
      for (const text of ["1 2", "#1 2", "12 0"]) {
        let message = "";
        try {
          parseProgramInput(text);
        } catch (err) {
          message = err instanceof Error ? err.message : "";
        }
        if (!/space/i.test(message)) {
          ctx.fail("FAIL spaces in a number", text, message);
        }
      }
      for (const text of ["-5", "#-5"]) {
        let message = "";
        try {
          parseProgramInput(text);
        } catch (err) {
          message = err instanceof Error ? err.message : "";
        }
        if (!/negative/i.test(message)) {
          ctx.fail("FAIL negative program", text, message);
        }
      }
      let bare = "";
      try {
        parseProgramInput("12");
      } catch (err) {
        bare = err instanceof Error ? err.message : "";
      }
      if (!bare.includes("#")) {
        ctx.fail("FAIL bare digits", bare);
      }
      let tooBig = "";
      try {
        unrankProgram(BigInt(10) ** BigInt(1000));
      } catch (err) {
        tooBig = err instanceof Error ? err.message : "";
      }
      if (!tooBig.includes("1000 gates") || !tooBig.includes("10^1000")) {
        ctx.fail("FAIL gate limit message", tooBig);
      }
    },
  },
  {
    id: 32,
    weight: 84,
    run(ctx) {
      const near = unrankProgram(BigInt(431));
      const report = evaluateReport(near);
      // Guard digits past 240. This overflowed word then agrees with −1, so the
      // 240-digit check does not reject it. The float overflow flag does.
      const exact = exactValueAt(near, 280);
      if (!report.overflowed || !close(report.value, c(-1), 1e-9) || report.singular !== null) {
        ctx.fail("FAIL #431 overflow flag", report);
      }
      if (!acceptsConstantValue(exact, -1, 0) || acceptsConstantProgram(near, -1, 0)) {
        ctx.fail("FAIL #431 golf near-miss", acceptsConstantValue(exact, -1, 0), acceptsConstantProgram(near, -1, 0));
      }
      const minus = unrankProgram(BigInt(242));
      const minusReport = evaluateReport(minus);
      if (minusReport.overflowed || minusReport.underflowed || !acceptsConstantProgram(minus, -1, 0)) {
        ctx.fail("FAIL real -1 still accepted", minusReport.overflowed, minusReport.underflowed);
      }
      const underNode = unrankProgram(BigInt(5884));
      const underWord = rpnTokens(underNode, 40)?.join("") ?? "";
      const underReport = evaluateReport(underNode);
      const underCoarse = exactValueAt(underNode, 40);
      if (underWord !== "11E111E1E1EEE1E11EE" || !underReport.underflowed || underReport.overflowed || underReport.value.re !== -1 || underReport.value.im !== 0) {
        ctx.fail("FAIL #5884 underflow", underWord, underReport);
      }
      if (!exactClose(underCoarse, -1, 0, 12) || acceptsConstantProgram(underNode, -1, 0)) {
        ctx.fail("FAIL #5884 golf near-miss", exactClose(underCoarse, -1, 0, 12), acceptsConstantProgram(underNode, -1, 0));
      }
      const expOfPole = evaluateReport(E(input(c(-Infinity), "−∞"), ONE));
      if (expOfPole.underflowed || expOfPole.value.re !== 0 || !expUnderflows(c(-800)) || expUnderflows(c(-Infinity)) || expUnderflows(c(0))) {
        ctx.fail("FAIL ln 0 is not underflow", expOfPole, expUnderflows(c(-800)), expUnderflows(c(-Infinity)));
      }
      const half = programNode("1/2");
      if (!evaluateReport(half).touchedLn0 || evaluateReport(half).overflowed) {
        ctx.fail("FAIL ln 0 is not overflow");
      }
    },
  },
];

export default checks;
