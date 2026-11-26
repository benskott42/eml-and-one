import { generateMinimalityCertificate } from "../certificate";
import { E, ONE, type Node, nodeFromRpn } from "../node";
import { deriveProof } from "../proof";
import type { CheckModule } from "./_types";

/**
 * Rigorous minimality certificates (directed-rounding ball arithmetic)
 * and deductive symbolic proof derivations.
 */
const checkModule: CheckModule = {
  id: 106,
  weight: 100,
  run(ctx) {
    const assert = (label: string, ok: boolean, detail?: string) => {
      if (!ok) ctx.fail(`FAIL ${label}${detail ? ` (${detail})` : ""}`);
    };

    // 1. Computer-assisted minimality certificate: 0 is absent for all K <= 5 (all 4 Catalan trees)
    const certZeroK5 = generateMinimalityCertificate("0", 0, 0, 5, 80);
    assert(
      "cert(0, K<=5) checks all 4 programs and proves absence",
      certZeroK5.expectedPrograms === 4 &&
        certZeroK5.totalPrograms === 4 &&
        certZeroK5.provedAbsent === true &&
        certZeroK5.openPrograms.length === 0,
      `total=${certZeroK5.totalPrograms} open=${certZeroK5.openPrograms.length}`,
    );

    // At K <= 7 (all 9 Catalan trees), 0 has exactly 1 exact hit: 111E1EE (0x74), 0 open!
    const certZeroK7 = generateMinimalityCertificate("0", 0, 0, 7, 80);
    assert(
      "cert(0, K<=7) finds exactly 1 hit (0x74) with 0 open",
      certZeroK7.totalPrograms === 9 &&
        certZeroK7.openPrograms.length === 0 &&
        certZeroK7.exactHits.length === 1 &&
        certZeroK7.exactHits[0]?.hex === "0x74",
      `hits=${certZeroK7.exactHits.map((h) => h.hex).join(",")} open=${certZeroK7.openPrograms.length}`,
    );

    // −1 is absent for all K <= 9 (all 23 Catalan trees) with 0 open!
    const certNeg1K9 = generateMinimalityCertificate("-1", -1, 0, 9, 80);
    assert(
      "cert(-1, K<=9) checks all 23 programs and proves absence",
      certNeg1K9.totalPrograms === 23 && certNeg1K9.provedAbsent === true,
      `open=${certNeg1K9.openPrograms.length} hits=${certNeg1K9.exactHits.length}`,
    );

    // 2. Deductive symbolic proof kernel
    const proofE = deriveProof(E(ONE, ONE));
    assert("deriveProof(e) deduces e in 1 step", proofE?.resultText === "e" && proofE.steps.length === 1);

    const proofZero = deriveProof(nodeFromRpn("111E1EE".split("")));
    assert(
      "deriveProof(0) deduces 0 in 3 steps without ln 0",
      proofZero?.resultText === "0" && proofZero.steps.length === 3 && !proofZero.usesLn0,
      `got ${proofZero?.resultText} (${proofZero?.steps.length} steps)`,
    );

    // −1 = 0x7d0c = 111110100001100₂ = 11111E1EEEE11EE
    const proofNeg1 = deriveProof(nodeFromRpn("11111E1EEEE11EE".split("")));
    assert(
      "deriveProof(-1, 0x7d0c) deduces −1 using ln 0",
      proofNeg1?.resultText === "−1" && proofNeg1.usesLn0,
      `got ${proofNeg1?.resultText}`,
    );

    // exp(x) = eml(x, 1) and ln(x) = eml(1, eml(eml(1, x), 1))
    const x: Node = { type: "var", name: "x", id: 999_999 };
    const proofExp = deriveProof(E(x, ONE));
    assert("deriveProof(exp(x)) deduces exp(x)", proofExp?.resultText === "exp(x)");

    const proofLn = deriveProof(E(ONE, E(E(ONE, x), ONE)));
    assert("deriveProof(ln(x)) deduces ln(x)", proofLn?.resultText === "ln(x)", `got ${proofLn?.resultText}`);

    // 2 = 0x7e264 (without ln 0), +iπ = 0x1fa1a8 (lower cut + ln 0), −2 = 0x1fa1a8c
    const proofTwo = deriveProof(nodeFromRpn("111111EEE1EE11EE1EE".split("")));
    assert("deriveProof(2, 0x7e264) deduces 2 without ln 0", proofTwo?.resultText === "2" && !proofTwo.usesLn0, `got ${proofTwo?.resultText}`);

    const proofIpi = deriveProof(nodeFromRpn("111111E1EEEE11E1E1EEE".split("")));
    assert(
      "deriveProof(+iπ, 0x1fa1a8) deduces iπ with lower cut + ln 0",
      proofIpi?.resultText === "iπ" && proofIpi.usesLn0 && proofIpi.usesLowerCut,
      `got ${proofIpi?.resultText}`,
    );

    const proofNeg2 = deriveProof(nodeFromRpn("111111E1EEEE11E1E1EEE11EE".split("")));
    assert("deriveProof(-2, 0x1fa1a8c) deduces −2", proofNeg2?.resultText === "−2", `got ${proofNeg2?.resultText}`);
  },
};

export default checkModule;
