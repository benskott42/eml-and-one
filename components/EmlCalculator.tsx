"use client";

import { CalculatorView } from "./calculator/CalculatorView";
import { useCalculatorModel } from "./calculator/useCalculatorModel";

export function EmlCalculator() {
  const model = useCalculatorModel();
  return <CalculatorView {...model} />;
}
