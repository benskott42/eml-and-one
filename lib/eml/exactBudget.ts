/**
 * The exact worker refuses a circuit once evaluation steps pass this.
 * The expression compiler uses the same budget, so it does not hand the
 * worker a sequence the worker will not run.
 */
export const EXACT_MAX_NODES = 80_000;

/**
 * Shown when a circuit exceeds the evaluation budget.
 * Exact mode, the float evaluator, and the press compiler all use this
 * sentence. "Too large to evaluate" covers those three; "for exact mode"
 * would be the wrong reason on the float evaluator and on the compiler.
 */
export const EXACT_TOO_LARGE = "This circuit is too large to evaluate.";
