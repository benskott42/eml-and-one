import {
  binaryProgramInfo,
  binaryToFormula,
  binaryToRank,
  binaryToRpn,
  binaryTreeMetrics,
  cycleOrbit,
  dyckProfile,
  isValidBinaryProgram,
  maxBinaryProgram,
  minBinaryProgram,
  nextBinaryProgram,
  rankToBinary,
  rpnToBinary,
} from "../binary";
import best from "../best-known.json";
import { exactReport, formatExact } from "../exact";
import { compileExpression } from "../parse";
import { catalan, parseProgramInput, rankRpn } from "../programIndex";
import type { CheckModule } from "./_types";

/**
 * Binary representation of constant EML programs:
 * - Dyck-prefix integer sequence (1, 6, 26, 28, 106, 108, 114, 116, 120, ...)
 * - Catalan counts per odd bit length 2n + 1
 * - O(bitlen) nextBinaryProgram enumeration
 * - Cycle Lemma orbit decomposition
 * - 0x... and 0b... program input parsing (including hex digits e/E and rotation)
 */
const checkModule: CheckModule = {
  id: 104,
  weight: 120,
  run(ctx) {
    // First 9 valid binary EML programs: n=0 (1), n=1 (6), n=2 (26, 28), n=3 (106, 108, 114, 116, 120).
    const expected = [1, 6, 26, 28, 106, 108, 114, 116, 120].map((v) => BigInt(v));
    const got: bigint[] = [];
    let cur = BigInt(0);
    for (let k = 0; k < expected.length; k += 1) {
      cur = nextBinaryProgram(cur);
      got.push(cur);
      cur += BigInt(1);
    }
    if (got.join(",") !== expected.join(",")) {
      ctx.fail(`FAIL binary-sequence got=${got.join(",")} want=${expected.join(",")}`);
    }

    // For n = 0..5, nextBinaryProgram enumerates exactly Catalan(n) programs in [min, max],
    // each satisfies isValidBinaryProgram, and rankRpn reverses binary order within each length.
    for (let gates = 0; gates <= 5; gates += 1) {
      const lo = minBinaryProgram(gates);
      const hi = maxBinaryProgram(gates);
      let count = BigInt(0);
      let prevRank: bigint | null = null;
      let p = nextBinaryProgram(lo);
      while (p <= hi) {
        if (!isValidBinaryProgram(p)) ctx.fail(`FAIL binary-valid ${p.toString()}`);
        const rank = rankRpn(binaryToRpn(p.toString(2)));
        if (prevRank !== null && rank >= prevRank) {
          ctx.fail(`FAIL binary-order gates=${gates} p=${p.toString()} rank=${rank.toString()} prev=${prevRank.toString()}`);
        }
        prevRank = rank;
        count += BigInt(1);
        p = nextBinaryProgram(p + BigInt(1));
      }
      if (count !== catalan(gates)) {
        ctx.fail(`FAIL binary-catalan gates=${gates} count=${count.toString()} want=${catalan(gates).toString()}`);
      }
    }

    // Known constants: exact binary values and hex/binary parsing (including hex containing 'e').
    const known: [string, string, string][] = [
      ["e", "0x6", "6"],
      ["0", "0x74", "116"],
      ["-1", "0x7d0c", "32012"],
      ["2", "0x7e264", "516708"],
      ["ipi", "0x1fa1a8", "2073000"],
    ];
    for (const [name, hex, dec] of known) {
      const word = best.programs[name as keyof typeof best.programs];
      const bits = rpnToBinary(word);
      const info = binaryProgramInfo(bits);
      if (!info || info.hex !== hex || info.decimal !== dec) {
        ctx.fail(`FAIL binary-info ${name} got=${JSON.stringify(info)} want=${hex}/${dec}`);
      }
      const fromHex = parseProgramInput(hex);
      const fromBin = parseProgramInput(`0b${bits}`);
      if (fromHex.kind !== "word" || fromHex.word !== word || fromHex.rotatedFrom !== null) {
        ctx.fail(`FAIL parse-hex ${name} (${hex}) got=${JSON.stringify(fromHex)}`);
      }
      if (fromBin.kind !== "word" || fromBin.word !== word || fromBin.rotatedFrom !== null) {
        ctx.fail(`FAIL parse-bin ${name} got=${JSON.stringify(fromBin)}`);
      }
    }

    // Cycle Lemma: every cyclic rotation of 1110100 (0) maps back to 1110100 with the right offset.
    const zeroBits = "1110100";
    for (let shift = 0; shift < zeroBits.length; shift += 1) {
      const rot = zeroBits.slice(shift) + zeroBits.slice(0, shift);
      const orbit = cycleOrbit(rot);
      const wantRot = (zeroBits.length - shift) % zeroBits.length;
      if (orbit.canonical !== zeroBits || orbit.rotation !== wantRot || orbit.orbitSize !== 7) {
        ctx.fail(`FAIL cycle-orbit shift=${shift} rot=${rot} got=${JSON.stringify(orbit)}`);
      }
    }

    // Hex input that needs Cycle Lemma rotation: 0x4e = 1001110 -> rotates left by 3 to 1110100 (0).
    const rotatedHex = parseProgramInput("0x4e");
    if (rotatedHex.kind !== "word" || rotatedHex.word !== "111E1EE" || rotatedHex.rotatedFrom !== "1001110") {
      ctx.fail(`FAIL parse-hex-rotate 0x4e got=${JSON.stringify(rotatedHex)}`);
    }

    // Malformed 0x / 0b prefixes report clear errors instead of falling through to variable 'x'.
    for (const bad of ["0x", "0xZZ", "0b", "0b102"]) {
      let msg = "";
      try {
        parseProgramInput(bad);
      } catch (err) {
        msg = err instanceof Error ? err.message : String(err);
      }
      if (!msg.includes("Write hex") && !msg.includes("Write binary")) {
        ctx.fail(`FAIL parse-bad-prefix ${bad} msg=${msg}`);
      }
    }

    // Binary <-> Catalan rank bijection round-trip over #0..#200.
    for (let r = 0; r <= 200; r += 1) {
      const rank = BigInt(r);
      const bin = rankToBinary(rank);
      if (!isValidBinaryProgram(bin) || binaryToRank(bin) !== rank) {
        ctx.fail(`FAIL binary-rank-bijection rank=${r} bin=${bin.toString(16)}`);
      }
    }

    // Binary tree metrics on known constants: 1 (depth 0), e (depth 1, maxStack 2), 0 (depth 3, maxStack 3).
    const mOne = binaryTreeMetrics("1");
    const mE = binaryTreeMetrics("110");
    const mZero = binaryTreeMetrics("1110100");
    if (mOne.gates !== 0 || mOne.depth !== 0 || mOne.maxStack !== 1) ctx.fail(`FAIL metrics 1 ${JSON.stringify(mOne)}`);
    if (mE.gates !== 1 || mE.depth !== 1 || mE.maxStack !== 2) ctx.fail(`FAIL metrics e ${JSON.stringify(mE)}`);
    if (mZero.gates !== 3 || mZero.depth !== 3 || mZero.maxStack !== 3) ctx.fail(`FAIL metrics 0 ${JSON.stringify(mZero)}`);

    // Dyck profile and formula decoding from binary.
    if (dyckProfile("1110100").join(",") !== "1,2,3,2,3,2,1") {
      ctx.fail(`FAIL dyck-profile 0 got=${dyckProfile("1110100").join(",")}`);
    }
    if (binaryToFormula("110") !== "E(1, 1)" || binaryToFormula("1110100") !== "E(1, E(E(1, 1), 1))") {
      ctx.fail(`FAIL binary-formula got=${binaryToFormula("1110100")}`);
    }

    // Signed-zero positive powers and hyperbolic imaginary-pi identities/poles.
    for (const [src, want] of [
      ["(-0)^2", "0"],
      ["(-0)^3", "−0"],
      ["(-0)^(1/2)", "0"],
      ["sinh(i*pi)", "0"],
      ["sinh(-2*i*pi)", "0"],
      ["sinh(i*pi/2) - i", "0"],
      ["sinh(3*i*pi/2) + i", "0"],
      ["tanh(i*pi/2)", "undefined"],
      ["tanh(3*i*pi/2)", "undefined"],
      ["tanh(3*i*pi)", "0"],
      ["tanh(i*pi/4) - i", "0"],
      ["tanh(-i*pi/4) + i", "0"],
    ] as const) {
      const rep = exactReport(compileExpression(src, {}), {}, { maxNodes: 800_000 });
      const gotText = formatExact(rep.value);
      if (rep.unverified || gotText !== want) {
        ctx.fail(`FAIL neg-zero-pow-and-hyp ${src} got=${rep.unverified ? "unverified" : gotText} want=${want}`);
      }
    }
  },
};

export default checkModule;
