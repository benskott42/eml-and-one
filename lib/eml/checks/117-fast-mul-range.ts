import Decimal from "decimal.js";
import { installFastMul } from "../fast-mul";
import type { CheckModule } from "./_types";

/**
 * A narrow clone's multiply underflows to zero and overflows to infinity on the
 * same side of minE/maxE as decimal.js, including a product whose exponent is
 * minE − 1 and whose rounding carries it back into range. Operands stay long
 * enough to take the fast path. The reference constructor is not opted in.
 */
const SIG = "9".repeat(84);

type Row = {
  rounding: Decimal.Rounding;
  exp: string;
  neg: boolean;
  precision: number;
  minE: number;
  maxE: number;
  want: string;
};

const rows: Row[] = [
  { rounding: Decimal.ROUND_HALF_UP, exp: "e-89", neg: false, precision: 20, minE: -10, maxE: 10, want: "1|-10|10000" },
  { rounding: Decimal.ROUND_UP, exp: "e-89", neg: true, precision: 20, minE: -10, maxE: 10, want: "-1|-10|10000" },
  { rounding: Decimal.ROUND_DOWN, exp: "e-89", neg: false, precision: 20, minE: -10, maxE: 10, want: "0" },
  { rounding: Decimal.ROUND_DOWN, exp: "e-89", neg: true, precision: 20, minE: -10, maxE: 10, want: "-0" },
  { rounding: Decimal.ROUND_HALF_UP, exp: "", neg: false, precision: 20, minE: -10, maxE: 5, want: "Infinity" },
  { rounding: Decimal.ROUND_HALF_UP, exp: "", neg: true, precision: 20, minE: -10, maxE: 5, want: "-Infinity" },
  { rounding: Decimal.ROUND_HALF_UP, exp: "e-120", neg: false, precision: 20, minE: -10, maxE: 10, want: "0" },
  { rounding: Decimal.ROUND_HALF_UP, exp: "e-120", neg: true, precision: 20, minE: -10, maxE: 10, want: "-0" },
  { rounding: Decimal.ROUND_HALF_UP, exp: "e-80", neg: false, precision: 40, minE: -80, maxE: 80, want: "1|8|10" },
  { rounding: Decimal.ROUND_DOWN, exp: "e-80", neg: true, precision: 40, minE: -80, maxE: 80, want: "-1|7|9,9999999,9999999,9999999,9999999,9999999,9999000" },
];

function picture(x: Decimal): string {
  if (!x.isFinite()) return x.isNaN() ? "NaN" : x.isNeg() ? "-Infinity" : "Infinity";
  if (x.isZero()) return x.isNeg() ? "-0" : "0";
  return `${x.s}|${x.e}|${x.d!.join(",")}`;
}

const checkModule: CheckModule = {
  id: 117,
  weight: 50,
  run(ctx) {
    for (const row of rows) {
      const wide = { precision: 90, rounding: row.rounding, minE: -9e15, maxE: 9e15 };
      const refC = Decimal.clone(wide);
      const fastC = installFastMul(Decimal.clone(wide));
      const mag = SIG + row.exp;
      const xr = new refC((row.neg ? "-" : "") + mag);
      const yr = new refC(mag);
      const xf = new fastC((row.neg ? "-" : "") + mag);
      const yf = new fastC(mag);
      if ((xf.d?.length ?? 0) < 12 || (yf.d?.length ?? 0) < 12) {
        ctx.fail(`operands missed the fast path (${row.exp}, rounding ${row.rounding})`);
        continue;
      }
      const narrow = { precision: row.precision, minE: row.minE, maxE: row.maxE };
      refC.set(narrow);
      fastC.set(narrow);
      const ref = picture(xr.mul(yr));
      const got = picture(xf.mul(yf));
      const label = `rounding ${row.rounding} ${row.exp || "e0"} ${row.neg ? "neg" : "pos"}`;
      if (ref !== row.want) ctx.fail(`decimal.js ${label}: ${ref}, want ${row.want}`);
      if (got !== ref) ctx.fail(`fast mul ${label}: ${got}, decimal.js ${ref}`);
    }
    console.log("fast mul narrow range", `${rows.length} products`);
  },
};

export default checkModule;
