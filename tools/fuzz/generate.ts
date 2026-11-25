/**
 * Deterministic seeded expression generator for fuzzing the EML exact engine.
 * Covers random trees over every calculator function, huge/tiny leaves,
 * cut-adjacent complex inputs, poles, and exact angle multiples.
 */

export type FuzzCase = {
  category: "random" | "scale" | "cut" | "pole-angle";
  source: string;
};

function mulberry32(seed: number): () => number {
  let a = seed >>> 0;
  return () => {
    a = (a + 0x6d2b79f5) >>> 0;
    let t = Math.imul(a ^ (a >>> 15), 1 | a);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

const UNARY = [
  "exp",
  "ln",
  "sqrt",
  "sin",
  "cos",
  "tan",
  "sinh",
  "cosh",
  "tanh",
  "asin",
  "acos",
  "atan",
  "asinh",
  "acosh",
  "atanh",
] as const;

const BINARY = ["+", "-", "*", "/"] as const;

const BASIC_LEAVES = [
  "0",
  "-0",
  "1",
  "-1",
  "2",
  "3",
  "0.5",
  "0.1",
  "0.2",
  "0.3",
  "1.5",
  "pi",
  "e",
  "i",
  "-i",
  "pi/2",
  "pi/6",
  "1+i",
  "-1-i",
];

const SCALE_LEAVES = [
  "10^400",
  "10^(-400)",
  "10^(-500)",
  "10^(-130)",
  "10^(-240)",
  "1e-320",
  "1e-50",
  "exp(800)",
  "exp(-1000)",
  "exp(-300)",
  "10^300",
];

const CUT_LEAVES = [
  "-2-10^(-20)*i",
  "-2+10^(-20)*i",
  "-1-10^(-120)*i",
  "-1+10^(-120)*i",
  "1+10^(-16)",
  "1-10^(-200)",
  "-5-10^(-300)*i",
  "10^(-100)*i",
  "10^(-236)+10^(-236)*i",
];

const POLE_ANGLE_LEAVES = [
  "0",
  "-0",
  "ln(0)",
  "inf",
  "-inf",
  "i",
  "-i",
  "pi",
  "pi/2",
  "3*pi/2",
  "pi/4",
  "pi/3",
  "pi/6",
];

export function generateFuzzCases(count: number, seed: number): FuzzCase[] {
  const rand = mulberry32(seed);
  const pick = <T,>(arr: readonly T[]): T => arr[Math.floor(rand() * arr.length)] as T;

  const buildTree = (leaves: readonly string[], depth: number): string => {
    if (depth <= 0 || rand() < 0.35) return `(${pick(leaves)})`;
    const roll = rand();
    if (roll < 0.45) {
      return `${pick(UNARY)}(${buildTree(leaves, depth - 1)})`;
    }
    if (roll < 0.85) {
      return `(${buildTree(leaves, depth - 1)}${pick(BINARY)}${buildTree(leaves, depth - 1)})`;
    }
    // Small integer or simple power
    const expLeaf = pick(["0", "1", "2", "3", "-1", "0.5", "i"]);
    return `((${buildTree(leaves, depth - 1)})^(${expLeaf}))`;
  };

  const out: FuzzCase[] = [];
  const seen = new Set<string>();
  const categories: FuzzCase["category"][] = ["random", "scale", "cut", "pole-angle"];
  let attempts = 0;

  while (out.length < count && attempts < count * 10) {
    attempts += 1;
    const category = categories[out.length % categories.length] as FuzzCase["category"];
    const depth = 1 + Math.floor(rand() * 3);
    let source: string;
    if (category === "random") {
      source = buildTree(BASIC_LEAVES, depth);
    } else if (category === "scale") {
      const pool = [...SCALE_LEAVES, ...BASIC_LEAVES.slice(0, 8)];
      source = buildTree(pool, depth);
    } else if (category === "cut") {
      const pool = [...CUT_LEAVES, ...BASIC_LEAVES.slice(0, 10)];
      source = buildTree(pool, Math.min(depth, 2));
    } else {
      source = buildTree(POLE_ANGLE_LEAVES, Math.min(depth, 2));
    }
    if (seen.has(source)) continue;
    seen.add(source);
    out.push({ category, source });
  }
  return out;
}
