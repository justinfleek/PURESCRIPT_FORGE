import { describe, it, expect } from 'vitest';
import { same } from '@/utils/same';

describe('same utility', () => {
  it('returns true for identical arrays', () => {
    expect(same([1, 2, 3], [1, 2, 3])).toBe(true);
  });

  it('returns false for different arrays', () => {
    expect(same([1, 2, 3], [1, 2, 4])).toBe(false);
  });

  it('returns true for same reference', () => {
    const arr = [1, 2, 3];
    expect(same(arr, arr)).toBe(true);
  });

  it('handles undefined', () => {
    expect(same(undefined, undefined)).toBe(true);
    expect(same([1, 2], undefined)).toBe(false);
    expect(same(undefined, [1, 2])).toBe(false);
  });

  it('handles different lengths', () => {
    expect(same([1, 2], [1, 2, 3])).toBe(false);
  });
});
