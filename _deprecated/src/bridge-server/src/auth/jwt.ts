/**
 * JWT Authentication Module
 * Production-grade JWT token generation and validation
 */
import { SignJWT, jwtVerify, type JWTPayload } from 'jose';
import { randomBytes, createSecretKey } from 'crypto';

export interface TokenPayload extends JWTPayload {
  userId: string;
  sessionId: string;
  role: 'user' | 'admin' | 'service';
  permissions: string[];
  issuedAt: number;
  expiresAt: number;
}

export interface TokenResult {
  token: string;
  expiresAt: Date;
  refreshToken: string;
  refreshExpiresAt: Date;
}

/**
 * JWT Manager - Handles token generation and validation
 */
export class JWTManager {
  private secretKey: Uint8Array;
  private algorithm = 'HS256';
  private tokenExpiryMs: number;
  private refreshExpiryMs: number;
  
  constructor(secret?: string, tokenExpiryHours = 24, refreshExpiryDays = 30) {
    // Generate or use provided secret
    if (secret) {
      this.secretKey = new TextEncoder().encode(secret);
    } else {
      // Generate random secret (should be persisted in production)
      this.secretKey = randomBytes(32);
    }
    
    this.tokenExpiryMs = tokenExpiryHours * 60 * 60 * 1000;
    this.refreshExpiryMs = refreshExpiryDays * 24 * 60 * 60 * 1000;
  }
  
  /**
   * Generate access token and refresh token
   */
  async generateTokens(
    userId: string,
    sessionId: string,
    role: 'user' | 'admin' | 'service' = 'user',
    permissions: string[] = []
  ): Promise<TokenResult> {
    const now = Date.now();
    const expiresAt = now + this.tokenExpiryMs;
    const refreshExpiresAt = now + this.refreshExpiryMs;
    
    const payload: TokenPayload = {
      userId,
      sessionId,
      role,
      permissions,
      issuedAt: Math.floor(now / 1000),
      expiresAt: Math.floor(expiresAt / 1000),
      iat: Math.floor(now / 1000),
      exp: Math.floor(expiresAt / 1000),
    };
    
    // Generate access token
    const token = await new SignJWT(payload)
      .setProtectedHeader({ alg: this.algorithm })
      .setIssuedAt()
      .setExpirationTime(Math.floor(expiresAt / 1000))
      .sign(this.secretKey);
    
    // Generate refresh token (longer expiry, no permissions)
    const refreshPayload: TokenPayload = {
      userId,
      sessionId,
      role,
      permissions: [],
      issuedAt: Math.floor(now / 1000),
      expiresAt: Math.floor(refreshExpiresAt / 1000),
      iat: Math.floor(now / 1000),
      exp: Math.floor(refreshExpiresAt / 1000),
    };
    
    const refreshToken = await new SignJWT(refreshPayload)
      .setProtectedHeader({ alg: this.algorithm })
      .setIssuedAt()
      .setExpirationTime(Math.floor(refreshExpiresAt / 1000))
      .sign(this.secretKey);
    
    return {
      token,
      expiresAt: new Date(expiresAt),
      refreshToken,
      refreshExpiresAt: new Date(refreshExpiresAt),
    };
  }
  
  /**
   * Verify and decode token
   */
  async verifyToken(token: string): Promise<TokenPayload> {
    try {
      const { payload } = await jwtVerify(token, this.secretKey, {
        algorithms: [this.algorithm],
      });
      
      // Validate payload structure
      if (
        typeof payload.userId !== 'string' ||
        typeof payload.sessionId !== 'string' ||
        typeof payload.role !== 'string' ||
        !Array.isArray(payload.permissions)
      ) {
        throw new Error('Invalid token payload structure');
      }
      
      return payload as TokenPayload;
    } catch (error) {
      if (error instanceof Error) {
        throw new Error(`Token verification failed: ${error.message}`);
      }
      throw new Error('Token verification failed: Unknown error');
    }
  }
  
  /**
   * Refresh access token using refresh token
   */
  async refreshAccessToken(refreshToken: string): Promise<TokenResult> {
    const payload = await this.verifyToken(refreshToken);
    
    // Generate new tokens
    return this.generateTokens(
      payload.userId,
      payload.sessionId,
      payload.role,
      payload.permissions
    );
  }
  
  /**
   * Get secret key (for persistence)
   */
  getSecretKey(): string {
    return Buffer.from(this.secretKey).toString('base64');
  }
  
  /**
   * Set secret key (for loading from storage)
   */
  setSecretKey(secret: string): void {
    this.secretKey = Buffer.from(secret, 'base64');
  }
}
