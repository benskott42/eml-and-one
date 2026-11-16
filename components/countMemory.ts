const KEY = "eml-count-hash";

export function rememberCountHash(hash: string): void {
  try {
    sessionStorage.setItem(KEY, hash);
  } catch {
    /* private mode */
  }
}

export function readCountHash(): string {
  try {
    const hash = sessionStorage.getItem(KEY) ?? "";
    return /^#n=-?\d+(?:&noln0)?$/.test(hash) ? hash : "";
  } catch {
    return "";
  }
}
