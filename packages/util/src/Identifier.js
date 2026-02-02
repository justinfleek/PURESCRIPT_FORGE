// FFI for Identifier.purs
export const toHex = (n) => () => {
  const buf = Buffer.alloc(6);
  const bigN = BigInt(Math.floor(n));
  for (let i = 0; i < 6; i++) {
    buf[i] = Number((bigN >> BigInt(40 - 8 * i)) & BigInt(0xff));
  }
  return buf.toString("hex");
};

export const charAt_ = (idx) => (str) => str.charAt(idx);

export const toNumber = (n) => n;

export const negate = (n) => ~n;
