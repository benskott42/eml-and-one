import { useMemo, useState } from "react";
import { binaryToRpn, maxBinaryProgram, minBinaryProgram, nextBinaryProgram } from "@/lib/eml/binary";
import { generateMinimalityCertificate, type MinimalityCertificate } from "@/lib/eml/certificate";
import { formatC } from "@/lib/eml/format";
import { evaluateReport, nodeFromRpn } from "@/lib/eml/node";
import { Fold } from "./widgets";

type MapPoint = {
  k: number;
  hex: string;
  rpn: string;
  re: number;
  im: number;
  label: string;
};

const X_MIN = -6;
const X_MAX = 8;
const Y_MIN = -5;
const Y_MAX = 5;
const SVG_W = 420;
const SVG_H = 240;
const PAD = 18;

function collectPlanePoints(maxK: number): { points: MapPoint[]; total: number; outOfView: number } {
  const maxGates = (maxK - 1) >> 1;
  const points: MapPoint[] = [];
  const seen = new Set<string>();
  let total = 0;
  let outOfView = 0;
  for (let n = 0; n <= maxGates; n += 1) {
    const k = 2 * n + 1;
    const lo = minBinaryProgram(n);
    const hi = maxBinaryProgram(n);
    let cur = lo;
    while (cur <= hi) {
      total += 1;
      const rpn = binaryToRpn(cur.toString(2));
      const report = evaluateReport(nodeFromRpn(rpn.split("")));
      const { re, im } = report.value;
      if (Number.isFinite(re) && Number.isFinite(im) && !report.overflowed && !report.underflowed) {
        if (re >= X_MIN && re <= X_MAX && im >= Y_MIN && im <= Y_MAX) {
          const key = `${re.toFixed(4)},${im.toFixed(4)}`;
          if (!seen.has(key)) {
            seen.add(key);
            points.push({
              k,
              hex: `0x${cur.toString(16)}`,
              rpn,
              re,
              im,
              label: formatC({ re, im }),
            });
          }
        } else {
          outOfView += 1;
        }
      }
      cur = cur === hi ? hi + BigInt(1) : nextBinaryProgram(cur + BigInt(1));
    }
  }
  return { points, total, outOfView };
}

function toX(re: number): number {
  return PAD + ((re - X_MIN) / (X_MAX - X_MIN)) * (SVG_W - 2 * PAD);
}

function toY(im: number): number {
  return SVG_H - PAD - ((im - Y_MIN) / (Y_MAX - Y_MIN)) * (SVG_H - 2 * PAD);
}

function ComplexMapBody({ onLoadProgram }: { onLoadProgram?: (program: string) => void }) {
  const [maxK, setMaxK] = useState<11 | 13>(11);
  const [selected, setSelected] = useState<MapPoint | null>(null);
  const [cert, setCert] = useState<MinimalityCertificate | null>(null);

  const data = useMemo(() => collectPlanePoints(maxK), [maxK]);
  const axisX = toY(0);
  const axisY = toX(0);

  return (
    <div className="ti-inspector">
      <div className="ti-manual-actions">
        <button
          type="button"
          className={maxK === 11 ? "ti-chip ti-chip-active" : "ti-chip"}
          onClick={() => setMaxK(11)}
        >
          K ≤ 11 (65 trees)
        </button>
        <button
          type="button"
          className={maxK === 13 ? "ti-chip ti-chip-active" : "ti-chip"}
          onClick={() => setMaxK(13)}
        >
          K ≤ 13 (197 trees)
        </button>
      </div>
      <p className="ti-inspector-note">
        Showing {data.points.length} distinct finite values in [{X_MIN}, {X_MAX}] × [{Y_MIN}i, {Y_MAX}i] ({data.total} Catalan trees, {data.outOfView} outside box). Click any dot to load it.
      </p>
      <figure className="ti-svg-box">
        <figcaption>Complex plane ℂ · Re horizontal, Im vertical</figcaption>
        <svg viewBox={`0 0 ${SVG_W} ${SVG_H}`} className="ti-svg" role="img" aria-label={`Complex plane plot of ${data.points.length} EML circuits`}>
          <line x1={PAD} y1={axisX} x2={SVG_W - PAD} y2={axisX} className="ti-svg-edge" />
          <line x1={axisY} y1={PAD} x2={axisY} y2={SVG_H - PAD} className="ti-svg-edge" />
          <text x={SVG_W - PAD - 12} y={axisX - 4} className="ti-svg-axis">Re</text>
          <text x={axisY + 4} y={PAD + 8} className="ti-svg-axis">Im</text>
          {data.points.map((pt) => {
            const cx = toX(pt.re);
            const cy = toY(pt.im);
            const isSel = selected?.rpn === pt.rpn;
            const r = pt.k <= 7 ? 4.5 : pt.k <= 11 ? 3.2 : 2.5;
            return (
              <circle
                key={pt.rpn}
                cx={cx}
                cy={cy}
                r={isSel ? r + 2 : r}
                className={isSel ? "ti-svg-dot is-selected" : "ti-svg-dot ti-svg-plot-pt"}
                onClick={() => {
                  setSelected(pt);
                  onLoadProgram?.(pt.rpn);
                }}
              >
                <title>{`${pt.label} · K ${pt.k} (${pt.hex})`}</title>
              </circle>
            );
          })}
        </svg>
      </figure>
      {selected ? (
        <p className="ti-inspector-stack" aria-live="polite">
          Loaded {selected.label} · K {selected.k} · {selected.hex} ({selected.rpn})
        </p>
      ) : null}

      <div className="ti-proof">
        <p className="ti-inspector-note">
          <strong>Live minimality certifier</strong> (directed-rounding ball arithmetic over every Catalan tree):
        </p>
        <div className="ti-manual-actions">
          <button
            type="button"
            className="ti-chip"
            onClick={() => setCert(generateMinimalityCertificate("0", 0, 0, 5, 80))}
          >
            Prove 0 ∉ K ≤ 5
          </button>
          <button
            type="button"
            className="ti-chip"
            onClick={() => setCert(generateMinimalityCertificate("0", 0, 0, 7, 80))}
          >
            Verify 0 unique at K ≤ 7
          </button>
          <button
            type="button"
            className="ti-chip"
            onClick={() => setCert(generateMinimalityCertificate("−1", -1, 0, 9, 80))}
          >
            Prove −1 ∉ K ≤ 9
          </button>
        </div>
        {cert ? (
          <p className="ti-inspector-stack" aria-live="polite">
            Target {cert.targetLabel} (K ≤ {cert.maxK}): {cert.totalPrograms}/{cert.expectedPrograms} trees · {cert.counts["ball-separated"]} ball-separated · {cert.counts["exact-infinite"]} inf · {cert.counts.indeterminate} indet · {cert.exactHits.length} hits · {cert.openPrograms.length} open
            {cert.provedAbsent ? " → PROVED ABSENT" : cert.openPrograms.length === 0 && cert.exactHits.length > 0 ? ` → UNIQUE HIT ${cert.exactHits.map((h) => h.hex).join(", ")}` : ""}
          </p>
        ) : null}
      </div>
    </div>
  );
}

export function ComplexMap({ onLoadProgram }: { onLoadProgram?: (program: string) => void }) {
  return (
    <Fold summary="Complex-plane map & minimality certifier">
      <ComplexMapBody onLoadProgram={onLoadProgram} />
    </Fold>
  );
}
