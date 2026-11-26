import { defineConfig, globalIgnores } from "eslint/config";
import nextVitals from "eslint-config-next/core-web-vitals";
import nextTs from "eslint-config-next/typescript";

const eslintConfig = defineConfig([
  ...nextVitals,
  ...nextTs,
  // The ball-checks scripts are the recorded soundness run, not application code.
  globalIgnores([".next/**", "out/**", "build/**", "next-env.d.ts", "docs/design/ball-checks/**", "formal/lean/.lake/**"]),
]);

export default eslintConfig;
