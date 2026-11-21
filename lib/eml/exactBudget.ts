/**
 * The exact worker refuses a circuit once evaluation steps pass this.
 * The expression compiler uses the same budget, so it does not hand the
 * worker a sequence the worker will not run.
 */
export const EXACT_MAX_NODES = 80_000;

/** Shown by the worker and by the compiler when that budget is exceeded. */
export const EXACT_TOO_LARGE = "This circuit is too large to evaluate.";
