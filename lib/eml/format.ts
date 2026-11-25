import { type C, c, hypotC } from "./complex";

function formatReal(n: number): string {
  if (Number.isNaN(n)) return "undefined";
  if (Object.is(n, -0)) return "−0";
  if (n === 0) return "0";
  if (!Number.isFinite(n)) return n > 0 ? "∞" : "−∞";
  const sign = n < 0 ? "−" : "";
  const abs = Math.abs(n);
  const nearest = Math.round(abs);
  // Print a nearby integer only when twelve digits could not tell the value from it.
  // A relative 10^(−9) printed 2·10^9/3 as 666666667 and 10^9/7 as 142857143.
  const twelfth = 10 ** (Math.floor(Math.log10(abs)) - 11);
  if (nearest !== 0 && Math.abs(abs - nearest) < twelfth / 2 && nearest < 1e15) {
    return sign + String(nearest);
  }
  let text: string;
  if (abs >= 1e9 || abs < 1e-6) {
    text = abs.toExponential(6).replace(/\.?0+e/, "e").replace("e+", "×10^").replace("e-", "×10^−");
  } else {
    text = abs.toPrecision(12).replace(/(\.\d*?)0+$/, "$1").replace(/\.$/, "");
  }
  return sign + text;
}

function formatImag(n: number): string {
  const sign = n < 0 ? "−" : "";
  const abs = Math.abs(n);
  const text = formatReal(abs);
  return text === "1" ? `${sign}i` : `${sign}${text}i`;
}

/**
 * Round each component to about twelve digits of the whole number's magnitude.
 * A 2 beside 10^10 becomes 2, and a 7 beside 10^15 becomes 0. A component that
 * is part of the leading digits is left as the gates computed it. This is
 * display rounding for float mode. A component that changed is marked with ≈.
 * Exact mode does not use this function.
 */
function tidy(z: C): C {
  if (!Number.isFinite(z.re) || !Number.isFinite(z.im)) return z;
  const mag = hypotC(z);
  if (!(mag > 0)) return z;
  const uExp = Math.floor(Math.log10(mag)) - 11;
  // Below 1e-307, 10^uExp becomes subnormal and loses precision, corrupting digits.
  if (uExp < -307 || uExp > 308) return z;
  const unit = 10 ** uExp;
  const inv = uExp < 0 ? 10 ** -uExp : 0;
  if (!(unit > 0) || !Number.isFinite(unit)) return z;
  const snap = (part: number): number => {
    if (part === 0 || Object.is(part, -0)) return part;
    if (Math.abs(part) * 1e4 >= mag) return part;
    // Divide by 10^(-uExp) for negative uExp so exact multiples like 0.3 stay exact instead of 3*0.1.
    const rounded = uExp < 0 ? Math.round(part * inv) / inv : Math.round(part / unit) * unit;
    if (Math.abs(rounded) < unit / 2) return 0;
    return rounded;
  };
  const re = snap(z.re);
  const im = snap(z.im);
  return re === z.re && im === z.im ? z : { re, im };
}

function formatBody(v: C): string {
  const reFinite = Number.isFinite(v.re);
  const imFinite = Number.isFinite(v.im);
  if (!reFinite && !imFinite) {
    const joiner = v.im < 0 ? " − " : " + ";
    return `${formatReal(v.re)}${joiner}∞i`;
  }
  if (!reFinite && (v.im === 0 || Object.is(v.im, -0))) return formatReal(v.re);
  if (!imFinite && (v.re === 0 || Object.is(v.re, -0))) return formatImag(v.im);
  if (!reFinite && imFinite) {
    const joiner = v.im < 0 ? " − " : " + ";
    return `${formatReal(v.re)}${joiner}${formatImag(Math.abs(v.im))}`;
  }
  if (!imFinite && reFinite) {
    const sign = v.im < 0 ? " − " : " + ";
    return `${formatReal(v.re)}${sign}∞i`;
  }
  if (v.re === 0 && v.im === 0) return Object.is(v.re, -0) || Object.is(v.im, -0) ? "−0" : "0";
  if (v.im === 0 || Object.is(v.im, -0)) return formatReal(v.re);
  if (v.re === 0) return formatImag(v.im);
  const joiner = v.im < 0 ? " − " : " + ";
  return `${formatReal(v.re)}${joiner}${formatImag(Math.abs(v.im))}`;
}

export function formatC(z: C): string {
  if (Number.isNaN(z.re) || Number.isNaN(z.im)) return "undefined";
  const v = tidy(z);
  const body = formatBody(v);
  return v !== z ? `${body} ≈` : body;
}

const NAMED: { value: C; name: string }[] = [
  { value: c(0), name: "0" },
  { value: c(1), name: "1" },
  { value: c(-1), name: "−1" },
  { value: c(2), name: "2" },
  { value: c(0.5), name: "1/2" },
  { value: c(Math.SQRT2), name: "√2" },
  { value: c(Math.sqrt(3) / 2), name: "√3/2" },
  { value: c(Math.E), name: "e" },
  { value: c(Math.PI), name: "π" },
  { value: c(Math.PI / 2), name: "π/2" },
  { value: c(Math.PI / 3), name: "π/3" },
  { value: c(Math.PI / 4), name: "π/4" },
  { value: c(Math.PI / 6), name: "π/6" },
  { value: c(Math.SQRT1_2), name: "√2/2" },
  { value: c((1 + Math.sqrt(5)) / 2), name: "φ" },
  { value: c(0, 1), name: "i" },
  { value: c(0, -1), name: "−i" },
  { value: c(0, Math.PI), name: "iπ" },
];

export function recognize(z: C): string | null {
  if (!Number.isFinite(z.re) || !Number.isFinite(z.im)) return null;
  for (const item of NAMED) {
    const diff = Math.hypot(z.re - item.value.re, z.im - item.value.im);
    const scale = Math.max(hypotC(z), hypotC(item.value));
    // Within what twelve digits hide (the float-differs bound). A relative 10^(−9)
    // named a typed 3.141592654 "π" while the screen showed it differ in the tenth digit.
    if (diff === 0 || (scale > 0 && diff <= 5e-12 * scale)) return item.name;
  }
  return null;
}

const EXACT_NAMED_TEXT: Record<string, string[]> = {
  "0": ["0", "−0", "-0"],
  "1": ["1"],
  "−1": ["−1", "-1"],
  "2": ["2"],
  "1/2": ["0.5"],
  i: ["i"],
  "−i": ["−i", "-i"],
};

/**
 * Name shown beside a caption. recognize() reads the float view of an exact
 * value, which can round 1 + 10^(−20) to 1 or 1 + 10^(−200)i to 1 while the
 * screen visibly prints the extra digits or imaginary part. Only stamp a name
 * when the displayed text is consistent with that constant.
 */
export function captionName(text: string, value: C, caption: string): string | null {
  const known = recognize(value);
  if (!known) return null;
  if (known === caption || known === caption.replace(/-/g, "−")) return null;
  const clean = text.replace(/\s*≈$/, "").trim();
  if (!clean) return null;
  const exactTexts = EXACT_NAMED_TEXT[known];
  if (exactTexts) return exactTexts.includes(clean) ? known : null;
  // Every remaining NAMED entry (e, π, √2, φ, iπ, …) lies on one axis with |v| in [0.5, π].
  if (clean.includes(" + ") || clean.includes(" − ") || clean.includes("×10^") || clean.length > 16) return null;
  const isImag = known === "iπ";
  if (isImag !== clean.endsWith("i")) return null;
  return known;
}

export function isUsable(z: C): boolean {
  return Number.isFinite(z.re) && Number.isFinite(z.im);
}
