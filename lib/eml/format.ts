import { type C, c, hypotC } from "./complex";

function formatReal(n: number): string {
  if (Object.is(n, -0)) return "−0";
  if (n === 0) return "0";
  if (!Number.isFinite(n)) return n > 0 ? "∞" : "−∞";
  const sign = n < 0 ? "−" : "";
  const abs = Math.abs(n);
  const nearest = Math.round(abs);
  if (nearest !== 0 && Math.abs(abs - nearest) <= 1e-9 * nearest && nearest < 1e15) {
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
  if (Math.abs(abs - 1) <= 1e-9) return `${sign}i`;
  return `${sign}${formatReal(abs)}i`;
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
  const unit = 10 ** (Math.floor(Math.log10(mag)) - 11);
  if (!(unit > 0) || !Number.isFinite(unit)) return z;
  const snap = (part: number): number => {
    if (part === 0 || Object.is(part, -0)) return part;
    if (Math.abs(part) * 1e4 >= mag) return part;
    const rounded = Math.round(part / unit) * unit;
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
  if (!reFinite && !imFinite) return "undefined";
  if (!reFinite && (v.im === 0 || Object.is(v.im, -0))) return formatReal(v.re);
  if (!imFinite && (v.re === 0 || Object.is(v.re, -0))) return formatImag(v.im);
  if (!reFinite && imFinite) {
    if (v.im === 0 || Object.is(v.im, -0)) return formatReal(v.re);
    const joiner = v.im < 0 ? " − " : " + ";
    return `${formatReal(v.re)}${joiner}${formatImag(Math.abs(v.im))}`;
  }
  if (!imFinite && reFinite) {
    const imag = v.im < 0 ? "∞i" : "∞i";
    const sign = v.im < 0 ? " − " : " + ";
    return `${formatReal(v.re)}${sign}${imag}`;
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
    if (diff === 0 || (scale > 0 && diff <= 1e-9 * scale)) return item.name;
  }
  return null;
}

function displayedZero(text: string): boolean {
  const body = text.trim();
  return body === "0" || body === "−0" || body === "-0";
}

/**
 * Name shown beside a caption. recognize() of a tiny exact value is 0 once the
 * float conversion underflows, and that must not be printed next to a nonzero text.
 */
export function captionName(text: string, value: C, caption: string): string | null {
  const known = recognize(value);
  if (!known || known === caption) return null;
  if ((known === "0" || known === "−0") && !displayedZero(text)) return null;
  return known;
}

export function isUsable(z: C): boolean {
  return Number.isFinite(z.re) && Number.isFinite(z.im);
}
