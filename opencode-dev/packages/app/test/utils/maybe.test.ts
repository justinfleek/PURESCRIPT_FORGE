import { describe, it, expect } from 'vitest';
import { just, none, isJust, isNone, fromMaybe, mapMaybe, bindMaybe } from '@/utils/maybe';

describe('Maybe utilities', () => {
  it('just creates Maybe with value', () => {
    const m = just(42);
    expect(isJust(m)).toBe(true);
    expect(isNone(m)).toBe(false);
    if (isJust(m)) {
      expect(m.value).toBe(42);
    }
  });

  it('none creates empty Maybe', () => {
    const m = none<number>();
    expect(isJust(m)).toBe(false);
    expect(isNone(m)).toBe(true);
  });

  it('fromMaybe returns value or default', () => {
    expect(fromMaybe(just(42), 0)).toBe(42);
    expect(fromMaybe(none<number>(), 0)).toBe(0);
  });

  it('mapMaybe transforms value', () => {
    const m1 = just(42);
    const m2 = mapMaybe(m1, x => x * 2);
    expect(isJust(m2)).toBe(true);
    if (isJust(m2)) {
      expect(m2.value).toBe(84);
    }

    const m3 = none<number>();
    const m4 = mapMaybe(m3, x => x * 2);
    expect(isNone(m4)).toBe(true);
  });

  it('bindMaybe chains operations', () => {
    const m1 = just(42);
    const m2 = bindMaybe(m1, x => just(x * 2));
    expect(isJust(m2)).toBe(true);
    if (isJust(m2)) {
      expect(m2.value).toBe(84);
    }

    const m3 = bindMaybe(m1, x => none<number>());
    expect(isNone(m3)).toBe(true);
  });
});
