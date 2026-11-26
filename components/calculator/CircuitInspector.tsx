import { useEffect, useMemo, useState } from "react";
import { dyckProfile } from "@/lib/eml/binary";
import { layoutBinaryTree, nodeToEmlExpr, nodeToLatex, nodeToLean4, traceRpnSteps } from "@/lib/eml/export";
import { type Node } from "@/lib/eml/node";
import { pressPreviewForNode } from "@/lib/eml/presses";
import { Fold } from "./widgets";

const MAX_TRACE_K = 201;
const MAX_TREE_K = 63;

function copyText(text: string, onDone: () => void) {
  const clip = navigator.clipboard;
  if (!clip) return;
  void clip.writeText(text).then(onDone).catch(() => undefined);
}

function CircuitInspectorBody({ node }: { node: Node | null }) {
  const view = useMemo(() => (node ? pressPreviewForNode(node) : null), [node]);
  const pureBits = view && !view.usesVariables && view.copyable ? view.full : null;
  const traceable = pureBits && pureBits.length <= MAX_TRACE_K ? pureBits : null;

  const trace = useMemo(() => {
    if (!traceable) return null;
    try {
      return traceRpnSteps(traceable);
    } catch {
      return null;
    }
  }, [traceable]);

  const profile = useMemo(() => {
    if (!traceable) return null;
    try {
      return dyckProfile(traceable);
    } catch {
      return null;
    }
  }, [traceable]);

  const tree = useMemo(() => {
    if (!traceable || traceable.length > MAX_TREE_K) return null;
    try {
      return layoutBinaryTree(traceable);
    } catch {
      return null;
    }
  }, [traceable]);

  const exports = useMemo(() => {
    if (!node) return null;
    return {
      eml: nodeToEmlExpr(node),
      latex: nodeToLatex(node),
      lean: nodeToLean4(node),
    };
  }, [node]);

  const maxStep = trace ? trace.length - 1 : 0;
  const [step, setStep] = useState(maxStep);
  const [playing, setPlaying] = useState(false);
  const [copiedKey, setCopiedKey] = useState<string | null>(null);

  useEffect(() => {
    if (!playing || step >= maxStep) return;
    const id = window.setTimeout(() => {
      const next = Math.min(maxStep, step + 1);
      setStep(next);
      if (next >= maxStep) setPlaying(false);
    }, 420);
    return () => window.clearTimeout(id);
  }, [playing, step, maxStep]);

  // Binary tree SVG geometry
  const treeW = 420;
  const treePadX = 18;
  const treePadY = 18;
  const treeH = tree ? Math.min(240, Math.max(96, (tree.maxDepth + 1) * 30 + 20)) : 0;
  const treeCoords = useMemo(() => {
    if (!tree || tree.nodes.length === 0) return null;
    const spanX = Math.max(1, tree.leafCount - 1);
    const spanY = Math.max(1, tree.maxDepth);
    const map = new Map<number, { cx: number; cy: number }>();
    for (const n of tree.nodes) {
      const cx = tree.leafCount <= 1 ? treeW / 2 : treePadX + (n.x / spanX) * (treeW - 2 * treePadX);
      const cy = tree.maxDepth === 0 ? treeH / 2 : treePadY + (n.depth / spanY) * (treeH - 2 * treePadY);
      map.set(n.id, { cx, cy });
    }
    return map;
  }, [tree, treeH]);

  if (!node) {
    return <p>Build any circuit (try pressing 1, 1, EML or a constant key) to inspect its tree, Dyck path, and step-by-step stack replay.</p>;
  }

  const current = trace ? trace[Math.min(step, maxStep)] : null;
  const maxStack = profile ? Math.max(1, ...profile) : 1;

  // Dyck-path SVG geometry
  const dyckW = 420;
  const dyckH = 88;
  const dyckPadX = 14;
  const dyckPadY = 12;
  const dyckPoints =
    profile && profile.length > 1
      ? profile.map((h, i) => {
          const x = dyckPadX + (i / (profile.length - 1)) * (dyckW - 2 * dyckPadX);
          const y = dyckH - dyckPadY - (h / maxStack) * (dyckH - 2 * dyckPadY);
          return { x, y, h };
        })
      : null;

  return (
    <div className="ti-inspector">
      {exports && (exports.eml || exports.latex || exports.lean) ? (
        <div className="ti-manual-actions">
          {exports.eml ? (
            <button
              type="button"
              className="ti-chip"
              onClick={() => copyText(exports.eml!, () => setCopiedKey("eml"))}
            >
              {copiedKey === "eml" ? "Copied EML" : "Copy EML"}
            </button>
          ) : null}
          {exports.latex ? (
            <button
              type="button"
              className="ti-chip"
              onClick={() => copyText(exports.latex!, () => setCopiedKey("latex"))}
            >
              {copiedKey === "latex" ? "Copied LaTeX" : "Copy LaTeX"}
            </button>
          ) : null}
          {exports.lean ? (
            <button
              type="button"
              className="ti-chip"
              onClick={() => copyText(exports.lean!, () => setCopiedKey("lean"))}
            >
              {copiedKey === "lean" ? "Copied Lean 4" : "Copy Lean 4"}
            </button>
          ) : null}
        </div>
      ) : (
        <p className="ti-inspector-note">Formula export is available for circuits up to 120 expanded nodes.</p>
      )}

      {trace && current ? (
        <>
          <div className="ti-player">
            <div className="ti-manual-actions">
              <button type="button" className="ti-chip" onClick={() => { setPlaying(false); setStep(0); }} disabled={step === 0}>
                Start
              </button>
              <button type="button" className="ti-chip" onClick={() => { setPlaying(false); setStep((s) => Math.max(0, s - 1)); }} disabled={step === 0}>
                Prev
              </button>
              <button
                type="button"
                className="ti-chip"
                onClick={() => {
                  if (playing) {
                    setPlaying(false);
                  } else {
                    if (step >= maxStep) setStep(0);
                    setPlaying(true);
                  }
                }}
              >
                {playing ? "Pause" : "Play"}
              </button>
              <button type="button" className="ti-chip" onClick={() => { setPlaying(false); setStep((s) => Math.min(maxStep, s + 1)); }} disabled={step >= maxStep}>
                Next
              </button>
              <button type="button" className="ti-chip" onClick={() => { setPlaying(false); setStep(maxStep); }} disabled={step >= maxStep}>
                End
              </button>
            </div>
            <label className="ti-inspector-slider">
              <span>
                Step {current.step}/{maxStep}
                {current.token ? ` · press ${current.token === "E" ? "EML (0)" : "1 (1)"}` : " · empty stack"}
              </span>
              <input
                type="range"
                min={0}
                max={maxStep}
                value={current.step}
                onChange={(event) => {
                  setPlaying(false);
                  setStep(Number(event.target.value));
                }}
              />
            </label>
            <p className="ti-inspector-stack" aria-live="polite">
              Stack ({current.depth}): {current.stack.length > 0 ? current.stack.join("  |  ") : "empty"}
            </p>
          </div>

          {tree && treeCoords ? (
            <figure className="ti-svg-box">
              <figcaption>EML binary tree (K = {maxStep}, depth {tree.maxDepth})</figcaption>
              <svg viewBox={`0 0 ${treeW} ${treeH}`} className="ti-svg" role="img" aria-label={`EML binary tree with ${maxStep} nodes`}>
                {tree.edges.map((edge, idx) => {
                  const a = treeCoords.get(edge.from);
                  const b = treeCoords.get(edge.to);
                  if (!a || !b) return null;
                  const parentNode = tree.nodes.find((n) => n.id === edge.from);
                  const active = parentNode ? parentNode.step <= current.step : false;
                  return (
                    <line
                      key={idx}
                      x1={a.cx}
                      y1={a.cy}
                      x2={b.cx}
                      y2={b.cy}
                      className={active ? "ti-svg-edge is-active" : "ti-svg-edge"}
                    />
                  );
                })}
                {tree.nodes.map((n) => {
                  const pt = treeCoords.get(n.id);
                  if (!pt) return null;
                  const isCurrent = n.step === current.step;
                  const isDone = n.step <= current.step;
                  const r = tree.leafCount > 20 ? 5.5 : 8;
                  return (
                    <g key={n.id} className={isCurrent ? "ti-svg-node is-current" : isDone ? "ti-svg-node is-done" : "ti-svg-node"}>
                      <circle cx={pt.cx} cy={pt.cy} r={r} />
                      {r >= 7 ? (
                        <text x={pt.cx} y={pt.cy + 3} textAnchor="middle">
                          {n.label}
                        </text>
                      ) : null}
                    </g>
                  );
                })}
              </svg>
            </figure>
          ) : null}

          {dyckPoints ? (
            <figure className="ti-svg-box">
              <figcaption>Dyck path · stack height over {maxStep} presses (max {maxStack})</figcaption>
              <svg viewBox={`0 0 ${dyckW} ${dyckH}`} className="ti-svg" role="img" aria-label={`Dyck path stack height profile up to ${maxStack}`}>
                <polyline
                  points={dyckPoints.map((p) => `${p.x.toFixed(1)},${p.y.toFixed(1)}`).join(" ")}
                  className="ti-svg-dyck"
                />
                {dyckPoints[current.step] ? (
                  <>
                    <line
                      x1={dyckPoints[current.step]!.x}
                      y1={dyckPadY}
                      x2={dyckPoints[current.step]!.x}
                      y2={dyckH - dyckPadY}
                      className="ti-svg-cursor"
                    />
                    <circle
                      cx={dyckPoints[current.step]!.x}
                      cy={dyckPoints[current.step]!.y}
                      r={4}
                      className="ti-svg-dot"
                    />
                  </>
                ) : null}
              </svg>
            </figure>
          ) : null}
        </>
      ) : (
        <p className="ti-inspector-note">
          {view?.usesVariables
            ? "Step player and tree view apply to pure 1-and-EML constant circuits (no x or y)."
            : `This circuit has ${view ? view.presses.toString() : "many"} presses; interactive tree and step replay run up to K = ${MAX_TRACE_K}.`}
        </p>
      )}
    </div>
  );
}

export function CircuitInspector({ node }: { node: Node | null }) {
  return (
    <Fold summary="Tree, Dyck path & step player">
      <CircuitInspectorBody key={node?.id ?? 0} node={node} />
    </Fold>
  );
}
