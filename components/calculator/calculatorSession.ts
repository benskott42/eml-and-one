import type { History } from "@/lib/eml/history";
import type { Mode, Model } from "./screen";

export type CalculatorSession = {
  model: Model;
  xText: string;
  yText: string;
  expr: string;
  programField: string;
  mode: Mode;
  history: History<Model>;
};

let session: CalculatorSession | null = null;

export function readCalculatorSession(): CalculatorSession | null {
  if (typeof window === "undefined") return null;
  return session;
}

export function writeCalculatorSession(next: CalculatorSession): void {
  session = next;
}
