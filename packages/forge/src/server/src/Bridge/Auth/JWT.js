// JWT Authentication FFI - Node.js jose library bindings
// Production-grade JWT generation and validation

const { SignJWT, jwtVerify } = require('jose');
const crypto = require('crypto');

// Get JWT secret from environment (or generate for development)
function getSecret() {
  const secret = process.env.JWT_SECRET || process.env.BRIDGE_JWT_SECRET;
  if (!secret) {
    // Development fallback (warn in production)
    if (process.env.NODE_ENV === 'production') {
      throw new Error('JWT_SECRET must be set in production');
    }
    // Use a deterministic secret for development (NOT SECURE FOR PRODUCTION)
    return crypto.createHash('sha256').update('development-secret').digest();
  }
  return Buffer.from(secret, 'utf-8');
}

// Generate JWT token (EffectFnAff for PureScript Aff)
exports.generateTokenImpl = function(options) {
  return function(onError, onSuccess) {
    try {
      const secret = getSecret();
      const now = Math.floor(Date.now() / 1000);
      const expiresInSeconds = options.expiresIn !== null && options.expiresIn !== undefined
        ? Math.floor(options.expiresIn / 1000) // Convert milliseconds to seconds
        : 24 * 60 * 60; // Default: 24 hours
      const exp = now + expiresInSeconds;
      const jti = crypto.randomBytes(16).toString('hex');
      
      SignJWT({
        sub: options.userId,
        roles: options.roles || [],
        exp: exp,
        iat: now,
        jti: jti
      })
        .setProtectedHeader({ alg: 'HS256', typ: 'JWT' })
        .setIssuedAt(now)
        .setExpirationTime(exp)
        .setJti(jti)
        .sign(secret)
        .then(token => onSuccess({ tag: 'Right', value: token }))
        .catch(err => onSuccess({ tag: 'Left', value: err.message }));
    } catch (e) {
      onSuccess({ tag: 'Left', value: 'JWT generation error: ' + e.message });
    }
  };
};

// Validate JWT token (EffectFnAff for PureScript Aff)
exports.validateTokenImpl = function(token) {
  return function(onError, onSuccess) {
    try {
      const secret = getSecret();
      
      jwtVerify(token, secret)
        .then(result => {
          const payload = result.payload;
          onSuccess({
            valid: true,
            claims: {
              sub: payload.sub,
              roles: payload.roles || [],
              exp: payload.exp,
              iat: payload.iat,
              jti: payload.jti
            },
            error: null
          });
        })
        .catch(err => {
          onSuccess({
            valid: false,
            claims: null,
            error: err.message
          });
        });
    } catch (e) {
      onSuccess({
        valid: false,
        claims: null,
        error: 'Token validation error: ' + e.message
      });
    }
  };
};

// Decode token without validation (for debugging)
exports.decodeTokenImpl = function(token) {
  return function() {
    try {
      const parts = token.split('.');
      if (parts.length !== 3) {
        return { tag: 'Left', value: 'Invalid token format' };
      }
      
      const payload = JSON.parse(Buffer.from(parts[1], 'base64').toString('utf-8'));
      return {
        tag: 'Right',
        value: {
          sub: payload.sub,
          roles: payload.roles || [],
          exp: payload.exp,
          iat: payload.iat,
          jti: payload.jti
        }
      };
    } catch (e) {
      return { tag: 'Left', value: 'Token decode error: ' + e.message };
    }
  };
};

// Get current Unix time
exports.getCurrentUnixTime = function() {
  return Math.floor(Date.now() / 1000);
};
