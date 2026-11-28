import { exactReport, formatExact } from "../exact";
import { formatC } from "../format";
import { SINGULAR_LN0, V, evaluateReport, type Node } from "../node";
import { compileExpression } from "../parse";
import { packCircuit, unpackCircuit } from "../wire";
import { reportUnpacked } from "../packed-eval";
import type { CheckModule } from "./_types";

/**
 * IEEE: the sign of 0·a is the sign of a, for a literal, a computed value,
 * or a variable bound to either. Division by that zero keeps the ln 0 note.
 * An enclosure that does not decide the sign is refused.
 * Composed ln(−0) stays −∞ + iπ.
 */
const rows: Array<[string, string, string, string | null]> = [
  ["(1/3-1)*0", "−0", "−0", null],
  ["1/((1/3-1)*0)", "−∞", "−∞", SINGULAR_LN0],
  ["ln(0*(1/3-1))", "−∞ + 3.14159265359i", "−∞ + 3.14159265359i", SINGULAR_LN0],
  ["(-ln(2))*0", "−0", "−0", null],
  ["ln(0*(-ln(2)))", "−∞ + 3.14159265359i", "−∞ + 3.14159265359i", SINGULAR_LN0],
  ["ln(-0)", "−∞ + 3.14159265359i", "−∞ + 3.14159265359i", SINGULAR_LN0],
  ["(-2)*0", "−0", "−0", null],
  ["1/(-2*0)", "−∞", "−∞", SINGULAR_LN0],
  ["1/(-((ln(1/3))*0))", "∞", "∞", SINGULAR_LN0],
  ["ln((ln(1/3))*0)", "−∞ + 3.14159265359i", "−∞ + 3.14159265359i", SINGULAR_LN0],
  ["(1/(-3/2))*0", "−0", "−0", null],
  ["((-1/2)/2)*0", "−0", "−0", null],
  ["(-ln(2)/2)*0", "−0", "−0", null],
  ["((-e)/2)*0", "−0", "−0", null],
  ["(2/(-0.5))*0", "−0", "−0", null],
    ["(atan(-3))*0", "−0", "−0", null],
  ["((-2/3)*0)*((-2/3)*0)", "0", "0", null],
  ["((-2/3)*0)^-1", "−∞", "−∞", SINGULAR_LN0],
  ["i/((1/3-1)*0)", "−∞i", "−∞i", SINGULAR_LN0],
  ["-(((-2/3)*0)*((e*0)*(-3/2)))", "−0", "−0", null],
  ["(((0)*0*(-3/2))*0*(atan(-2/3)))+((-ln(2)/2)*0)", "0", "0", null],
  ["0*cos(1)", "0", "0", null],
  ["0*cos(2)", "−0", "−0", null],
  ["(-0)+(-0)", "−0", "−0", null],
  ["0+(-0)", "0", "0", null],
];

function show(node: Node): { float: string; exact: string; floatNote: string | null; exactNote: string | null; floatUnverified: boolean; exactUnverified: boolean } {
  const floated = evaluateReport(node);
  const exact = exactReport(node, {}, { maxNodes: 80_000 });
  return {
    float: formatC(floated.value),
    exact: exact.unverified ? "unverified" : formatExact(exact.value),
    floatNote: floated.singular,
    exactNote: exact.singular,
    floatUnverified: floated.unverified === true,
    exactUnverified: exact.unverified === true,
  };
}

const checkModule: CheckModule = {
  id: 117,
  weight: 800,
  run(ctx) {
    for (const [source, floatText, exactText, note] of rows) {
      const got = show(compileExpression(source, {}));
      if (got.floatUnverified || got.float !== floatText || got.floatNote !== note) {
        ctx.fail("FAIL signed zero float", source, got.float, got.floatNote, got.floatUnverified, "want", floatText, note);
      }
      if (got.exactUnverified || got.exact !== exactText || got.exactNote !== note) {
        ctx.fail("FAIL signed zero exact", source, got.exact, got.exactNote, "want", exactText, note);
      }
    }

    // The same negative, built three ways, is the same −0, and 1 over it is −∞.
    const factors = ["-3/2", "1/(-3/2)", "atan(-3)"];
    for (const factor of factors) {
      const literal = compileExpression(`(${factor})*0`, {});
      const reciprocal = compileExpression(`1/((${factor})*0)`, {});
      const bound = compileExpression(factor, {});
      const variable = compileExpression("x*0", { x: bound });
      const variableReciprocal = compileExpression("1/(x*0)", { x: bound });
      for (const [label, node] of [
        ["product", literal],
        ["variable", variable],
      ] as const) {
        const got = show(node);
        if (got.float !== "−0" || got.exact !== "−0" || got.floatNote !== null || got.exactNote !== null || got.floatUnverified || got.exactUnverified) {
          ctx.fail("FAIL signed zero path", factor, label, got.float, got.exact, got.floatNote, got.exactNote);
        }
      }
      for (const [label, node] of [
        ["reciprocal", reciprocal],
        ["variable reciprocal", variableReciprocal],
      ] as const) {
        const got = show(node);
        if (got.float !== "−∞" || got.exact !== "−∞" || got.floatNote !== SINGULAR_LN0 || got.exactNote !== SINGULAR_LN0) {
          ctx.fail("FAIL signed zero reciprocal", factor, label, got.float, got.exact, got.floatNote, got.exactNote);
        }
      }
    }

    const atan = compileExpression("(atan(-3))*0", {});
    const packed = packCircuit(atan);
    const wire = reportUnpacked(packed.tokens, packed.root).report;
    const wireText = wire.unverified ? "unverified" : formatExact(wire.value);
    if (wireText !== "−0" || wire.singular !== null) {
      ctx.fail("FAIL atan zero wire", wireText, wire.singular);
    }

    // 1 − cos(0) is the real 0, but that factor records no sign. 0 times it
    // must be refused rather than printed as a certified zero.
    const refused = show(compileExpression("0*(1-1*cos(0))", {}));
    if (!refused.floatUnverified || !refused.exactUnverified) {
      ctx.fail("FAIL uncertified sign", refused.float, refused.floatUnverified, refused.exact, refused.exactUnverified);
    }

    // A factor whose sign is not certified stays unverified even when it is
    // not proven finite. A signed zero times a non-real factor stays unverified
    // on both operand orders. App and the worker wire must agree.
    const uncertified = [
      "(-pi)^3*0",
      "0*(-(exp(0.5)^2))",
      "(exp(0.5))^2*((-0.5)*0)",
      "(0*cos(2))*i",
      "i*(0*cos(2))",
      "((-2/3)*0)*(-1+i)",
      "(-1+i)*((-2/3)*0)",
      // Every grouping of a zero and a product that contains a non-real factor.
      "(cos(2)*i)*0",
      "cos(2)*i*0",
      "cos(2)*(i*0)",
      "0*(cos(2)*i)",
      "i*(cos(2)*0)",
      "(i*cos(2))*0",
      "0*(i*cos(2))",
      "(i*0)*cos(2)",
      "cos(2)*(0*i)",
      "((-1)*0)*i",
      "i*((-1)*0)",
    ];
    for (const source of uncertified) {
      const node = compileExpression(source, {});
      const app = show(node);
      const packed = packCircuit(node);
      const unpacked = reportUnpacked(packed.tokens, packed.root);
      const wireFloat = evaluateReport(unpacked.node);
      const wireExact = unpacked.report;
      if (!app.floatUnverified || !app.exactUnverified || wireFloat.unverified !== true || wireExact.unverified !== true) {
        ctx.fail(
          "FAIL uncertified product",
          source,
          "app",
          app.float,
          app.floatUnverified,
          app.exact,
          app.exactUnverified,
          "wire",
          wireFloat.unverified,
          wireExact.unverified ? "unverified" : formatExact(wireExact.value),
        );
      }
    }

    // Signs that are proven without a stored range, and +0 times one pure
    // imaginary factor. A refused zero exponent is still x^0 = 1.
    const restored: Array<[string, string]> = [
      ["0*(exp(0.5)^2)", "0"],
      ["(exp(0.5)^2)*0", "0"],
      ["0*tanh(1)", "0"],
      ["tanh(1)*0", "0"],
      ["-(0*tanh(1))", "−0"],
      ["0*ln(0.1)", "−0"],
      ["(ln(0.1))*0", "−0"],
      ["0*(1/i)", "0"],
      ["(0*pi)*i", "0"],
      ["(0*sin(1))*i", "0"],
      ["0^((1+i)*0)", "1"],
      ["0^((1-i)*0)", "1"],
      ["0^((-0)*(2*i))", "1"],
      ["0^(0*(1+i))", "1"],
      ["2^((1-i)*0)", "1"],
      ["0^(0*(cos(2)*i))", "1"],
    ];
    for (const [source, want] of restored) {
      const node = compileExpression(source, {});
      const app = show(node);
      const packed = packCircuit(node);
      const unpacked = reportUnpacked(packed.tokens, packed.root);
      const wireFloat = evaluateReport(unpacked.node);
      const wireExact = unpacked.report;
      const wireExactText = wireExact.unverified ? "unverified" : formatExact(wireExact.value);
      const wireFloatText = wireFloat.unverified ? "unverified" : formatC(wireFloat.value);
      if (app.exact !== want || app.float !== want || wireExactText !== want || wireFloatText !== want) {
        ctx.fail("FAIL restored zero", source, "want", want, "app", app.float, app.exact, "wire", wireFloatText, wireExactText);
      }
    }

    // Negating the product word's 0 stays that exact 0. A +0 leaf would flip to −0.
    // The float keeps a minus the exact text does not, and app and wire agree.
    for (const source of ["-(0*(exp(0.5)^2))", "((-1)*0)*(exp(0.5)^2)"]) {
      const node = compileExpression(source, {});
      const app = show(node);
      const packed = packCircuit(node);
      const unpacked = reportUnpacked(packed.tokens, packed.root);
      const wireFloat = evaluateReport(unpacked.node);
      const wireExact = unpacked.report;
      const wireExactText = wireExact.unverified ? "unverified" : formatExact(wireExact.value);
      const wireFloatText = wireFloat.unverified ? "unverified" : formatC(wireFloat.value);
      if (app.exactUnverified || app.exact !== "0" || wireExactText !== "0" || app.floatUnverified || wireFloat.unverified === true || app.float !== wireFloatText) {
        ctx.fail("FAIL product-word zero", source, app.float, app.exact, wireFloatText, wireExactText);
      }
    }

    // x is bound when the circuit runs. x·0 with x = −2/3 is −0 on app and wire.
    const bound = { x: { re: -2 / 3, im: 0 } };
    const variable = compileExpression("x*0", { x: V("x") });
    const variableFloat = evaluateReport(variable, bound);
    const variableExact = exactReport(variable, bound, { maxNodes: 80_000 });
    const variablePacked = packCircuit(variable);
    const variableUnpacked = unpackCircuit(variablePacked.tokens, variablePacked.root);
    const variableWireFloat = evaluateReport(variableUnpacked, bound);
    const variableWireReport = exactReport(variableUnpacked, bound, { maxNodes: 80_000 });
    const variableWireExact = variableWireReport.unverified ? "unverified" : formatExact(variableWireReport.value);
    const variableExactText = variableExact.unverified ? "unverified" : formatExact(variableExact.value);
    if (
      variableFloat.unverified === true ||
      formatC(variableFloat.value) !== "−0" ||
      variableExactText !== "−0" ||
      variableWireFloat.unverified === true ||
      formatC(variableWireFloat.value) !== "−0" ||
      variableWireExact !== "−0"
    ) {
      ctx.fail("FAIL bound variable", formatC(variableFloat.value), variableExactText, formatC(variableWireFloat.value), variableWireExact);
    }
  },
};

export default checkModule;
