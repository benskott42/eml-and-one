/**
 * Shared contract for standalone check files under `lib/eml/checks/*.ts`.
 *
 * Adding a check is adding one file in `lib/eml/checks/` (any filename not
 * starting with `_`). Each file exports a default `CheckModule` or
 * `CheckModule[]`. `lib/eml/check.ts` discovers all `*.ts` files there
 * automatically, shards them with `EML_SHARD=i/N`, and filters them with
 * `EML_ONLY_BLOCK=<id-or-basename>`. No edits to `check.ts` or
 * `check-shards.json` are required.
 */
export type CheckContext = {
  fail: (message: string, ...details: unknown[]) => void;
  /** Add failures counted by a helper suite that already logged its own lines. */
  addFailures?: (count: number) => void;
};

export type CheckModule = {
  /** Optional legacy numeric or string id (so `EML_ONLY_BLOCK=<id>` selects this check). */
  id?: number | string;
  /** Optional fallback weight in ms if absent from `check-shards.json`. */
  weight?: number;
  run: (ctx: CheckContext) => void | Promise<void>;
};

export type CheckModuleExport = CheckModule | CheckModule[];
