/**
 * Sound-mode admission. The search calls `consider` once per clean value
 * and writes the pool slot itself. Nothing in here touches KeySet.
 *
 * The optional negative-real fast path (docs/interval-bounds.md §5) is not
 * implemented: the exact engine has no provable-realness flag. A disk that
 * meets the closed ray (−∞, 0] stays inconclusive and is not certified distinct.
 */
import { DiskGrid, certificationEnabled, disksDisjoint, emlDisk, type Disk } from "./interval";

/**
 * Counts from sound mode. `upperBound` is true because a class is dropped only
 * when exact proves equality, including ln 0 specials.
 */
export type SoundReport = {
  /** Float-key hits. Each nominates a merge and does not drop the new class by itself. */
  nominations: number;
  /** Exact comparisons that proved the circuits equal, so the new class was not kept. */
  confirmations: number;
  /** Exact comparisons that did not prove equality. Both classes stay. */
  rejections: number;
  /** Same float key, but the disks are disjoint, so exact was not asked. */
  distinct: number;
  exactChecks: number;
  /** Clean candidates (not a special) that needed at least one exact comparison. */
  escalation: { k: number; candidates: number; escalated: number }[];
  certification: boolean;
  upperBound: true;
};

/**
 * Disk index for one search. `consider` decides merge or keep.
 * `proveEqual` is the only exact-engine hook, so this class can sit behind
 * PoolAdmit.commit without sharing KeySet.
 */
export class SoundDedup {
  private grid = new DiskGrid();
  private keys = new Map<string, number[]>();
  private diskRe = new Float64Array(4096);
  private diskIm = new Float64Array(4096);
  private diskR = new Float64Array(4096);
  private diskOk = new Uint8Array(4096);
  private escalation = new Map<number, { candidates: number; escalated: number }>();
  private stats = { nominations: 0, confirmations: 0, rejections: 0, distinct: 0, exactChecks: 0 };

  constructor(oneKey: string) {
    this.remember(0, oneKey, { re: 1, im: 0, r: 0, ok: true });
  }

  diskAt(id: number): Disk {
    if (this.diskOk[id] !== 1) {
      return { re: Number.NaN, im: Number.NaN, r: Number.POSITIVE_INFINITY, ok: false };
    }
    return { re: this.diskRe[id] ?? 0, im: this.diskIm[id] ?? 0, r: this.diskR[id] ?? 0, ok: true };
  }

  /** Stored center, including an inconclusive slot. Trace uses this. */
  stored(id: number): { re: number; im: number; r: number; ok: boolean } {
    return {
      re: this.diskRe[id] ?? 0,
      im: this.diskIm[id] ?? 0,
      r: this.diskR[id] ?? 0,
      ok: this.diskOk[id] === 1,
    };
  }

  /**
   * Float-key hits only nominate. A keep is certified distinct only when every
   * disk the grid can see is disjoint; otherwise `proveEqual` has to say so.
   * A true proof drops the new class. Anything else keeps both.
   */
  consider(
    a: Disk,
    b: Disk,
    k: number,
    key: string,
    proveEqual: (id: number) => boolean,
  ): { merged: boolean; disk: Disk } {
    const disk = emlDisk(a, b);
    const row = this.escalation.get(k) ?? { candidates: 0, escalated: 0 };
    row.candidates += 1;
    const nominated = this.keys.get(key) ?? [];
    this.stats.nominations += nominated.length;
    const must = new Set<number>();
    if (disk.ok && certificationEnabled()) {
      for (const id of this.grid.nearby(disk)) {
        if (!disksDisjoint(disk, this.diskAt(id))) must.add(id);
      }
      for (const id of nominated) {
        if (disksDisjoint(disk, this.diskAt(id))) this.stats.distinct += 1;
        else must.add(id);
      }
    } else {
      for (const id of nominated) must.add(id);
    }
    let escalated = false;
    let merged = false;
    for (const id of must) {
      escalated = true;
      this.stats.exactChecks += 1;
      if (proveEqual(id)) {
        this.stats.confirmations += 1;
        merged = true;
        break;
      }
      this.stats.rejections += 1;
    }
    if (escalated) row.escalated += 1;
    this.escalation.set(k, row);
    return { merged, disk };
  }

  /** Index a class the caller has already written into the pool. */
  remember(id: number, key: string, disk: Disk): void {
    this.ensure(id);
    this.diskRe[id] = disk.re;
    this.diskIm[id] = disk.im;
    this.diskR[id] = disk.ok ? disk.r : Number.POSITIVE_INFINITY;
    this.diskOk[id] = disk.ok ? 1 : 0;
    this.noteKey(id, key);
    if (disk.ok) this.grid.add(id, disk);
  }

  report(): SoundReport {
    return {
      nominations: this.stats.nominations,
      confirmations: this.stats.confirmations,
      rejections: this.stats.rejections,
      distinct: this.stats.distinct,
      exactChecks: this.stats.exactChecks,
      escalation: [...this.escalation.entries()]
        .map(([levelK, row]) => ({ k: levelK, candidates: row.candidates, escalated: row.escalated }))
        .sort((p, q) => p.k - q.k),
      certification: certificationEnabled(),
      upperBound: true,
    };
  }

  private noteKey(id: number, key: string): void {
    const list = this.keys.get(key);
    if (list) list.push(id);
    else this.keys.set(key, [id]);
  }

  private ensure(id: number): void {
    if (id < this.diskOk.length) return;
    let cap = this.diskOk.length;
    while (cap <= id) cap *= 2;
    const diskRe = new Float64Array(cap);
    const diskIm = new Float64Array(cap);
    const diskR = new Float64Array(cap);
    const diskOk = new Uint8Array(cap);
    diskRe.set(this.diskRe);
    diskIm.set(this.diskIm);
    diskR.set(this.diskR);
    diskOk.set(this.diskOk);
    this.diskRe = diskRe;
    this.diskIm = diskIm;
    this.diskR = diskR;
    this.diskOk = diskOk;
  }
}
