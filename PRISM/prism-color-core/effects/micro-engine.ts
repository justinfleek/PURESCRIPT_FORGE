/**
 * Prism Luxe Micro-Interactions Engine
 * 
 * Performance-first subtle effects that enhance UX without causing lag.
 * Designed for VSCode, Neovim, and Emacs plugins.
 * 
 * Core Principles:
 * - Transform and opacity only (GPU-composited, no layout thrashing)
 * - 30fps target for particles (sufficient for subtle effects, saves power)
 * - Automatic pause when tab hidden (Page Visibility API)
 * - Respects prefers-reduced-motion
 * - Memory pooling for particles
 * - Lazy initialization
 */

// =============================================================================
// Types
// =============================================================================

interface Vector2 {
  x: number;
  y: number;
}

interface Color {
  r: number;
  g: number;
  b: number;
  a: number;
}

interface ParticleConfig {
  position: Vector2;
  velocity: Vector2;
  size: number;
  color: Color;
  lifetime: number;
  decay: number;
  drift?: 'rise' | 'fall' | 'float' | 'sparkle';
}

interface MicroConfig {
  maxParticles: number;
  targetFPS: number;
  respectReducedMotion: boolean;
  pauseWhenHidden: boolean;
  debug: boolean;
}

// =============================================================================
// Configuration
// =============================================================================

const DEFAULT_CONFIG: MicroConfig = {
  maxParticles: 30,
  targetFPS: 30,
  respectReducedMotion: true,
  pauseWhenHidden: true,
  debug: false
};

// =============================================================================
// Utility Functions
// =============================================================================

function lerp(a: number, b: number, t: number): number {
  return a + (b - a) * t;
}

function easeOutCubic(t: number): number {
  return 1 - Math.pow(1 - t, 3);
}

function easeOutElastic(t: number): number {
  const c4 = (2 * Math.PI) / 3;
  return t === 0 ? 0 : t === 1 ? 1 
    : Math.pow(2, -10 * t) * Math.sin((t * 10 - 0.75) * c4) + 1;
}

function parseColor(hex: string): Color {
  const result = /^#?([a-f\d]{2})([a-f\d]{2})([a-f\d]{2})([a-f\d]{2})?$/i.exec(hex);
  return result ? {
    r: parseInt(result[1], 16),
    g: parseInt(result[2], 16),
    b: parseInt(result[3], 16),
    a: result[4] ? parseInt(result[4], 16) / 255 : 1
  } : { r: 255, g: 255, b: 255, a: 1 };
}

function colorToRgba(c: Color): string {
  return `rgba(${c.r}, ${c.g}, ${c.b}, ${c.a})`;
}

// =============================================================================
// Particle Pool (Memory Optimization)
// =============================================================================

class Particle {
  x = 0;
  y = 0;
  vx = 0;
  vy = 0;
  size = 2;
  color: Color = { r: 255, g: 255, b: 255, a: 1 };
  life = 0;
  maxLife = 1000;
  decay = 0.98;
  drift: 'rise' | 'fall' | 'float' | 'sparkle' = 'float';
  active = false;
  element: HTMLElement | null = null;

  init(config: ParticleConfig): void {
    this.x = config.position.x;
    this.y = config.position.y;
    this.vx = config.velocity.x;
    this.vy = config.velocity.y;
    this.size = config.size;
    this.color = { ...config.color };
    this.life = 0;
    this.maxLife = config.lifetime;
    this.decay = config.decay;
    this.drift = config.drift || 'float';
    this.active = true;
  }

  update(dt: number): void {
    if (!this.active) return;

    this.life += dt;
    
    if (this.life >= this.maxLife) {
      this.active = false;
      return;
    }

    // Apply drift behaviors
    switch (this.drift) {
      case 'rise':
        this.vy -= 0.02 * dt;
        this.vx += (Math.random() - 0.5) * 0.01 * dt;
        break;
      case 'fall':
        this.vy += 0.01 * dt;
        this.vx += (Math.random() - 0.5) * 0.005 * dt;
        break;
      case 'float':
        this.vx += (Math.random() - 0.5) * 0.02 * dt;
        this.vy += (Math.random() - 0.5) * 0.02 * dt;
        break;
      case 'sparkle':
        // Mostly stationary with occasional twinkle
        this.vx *= 0.9;
        this.vy *= 0.9;
        break;
    }

    // Apply velocity
    this.x += this.vx * dt * 0.1;
    this.y += this.vy * dt * 0.1;

    // Apply decay
    this.vx *= this.decay;
    this.vy *= this.decay;

    // Fade out near end of life
    const lifeProgress = this.life / this.maxLife;
    if (lifeProgress > 0.7) {
      this.color.a = (1 - (lifeProgress - 0.7) / 0.3) * this.color.a;
    }
  }

  reset(): void {
    this.active = false;
    this.life = 0;
  }
}

class ParticlePool {
  private particles: Particle[] = [];
  private maxSize: number;

  constructor(maxSize: number) {
    this.maxSize = maxSize;
    // Pre-allocate particles
    for (let i = 0; i < maxSize; i++) {
      this.particles.push(new Particle());
    }
  }

  acquire(): Particle | null {
    for (const p of this.particles) {
      if (!p.active) {
        return p;
      }
    }
    return null;
  }

  getActive(): Particle[] {
    return this.particles.filter(p => p.active);
  }

  update(dt: number): void {
    for (const p of this.particles) {
      if (p.active) {
        p.update(dt);
      }
    }
  }

  clear(): void {
    for (const p of this.particles) {
      p.reset();
    }
  }
}

// =============================================================================
// CSS-Only Effects (Zero JS Overhead After Init)
// =============================================================================

const cssEffects = {
  /**
   * Hover lift effect - pure CSS, hardware accelerated
   */
  hoverLift: (selector: string, distance: number, duration: number) => `
    ${selector} {
      transition: transform ${duration}ms cubic-bezier(0.34, 1.56, 0.64, 1),
                  box-shadow ${duration}ms ease-out;
      will-change: transform;
    }
    ${selector}:hover {
      transform: translateY(-${distance}px) translateZ(0);
    }
  `,

  /**
   * Press effect - subtle scale down
   */
  pressEffect: (selector: string, scale: number, duration: number) => `
    ${selector}:active {
      transform: scale(${scale}) translateZ(0);
      transition: transform ${duration}ms ease-out;
    }
  `,

  /**
   * Focus ring - accessible and beautiful
   */
  focusRing: (selector: string, color: string, spread: number, blur: number) => `
    ${selector}:focus-visible {
      outline: none;
      box-shadow: 0 0 0 ${spread}px ${color}, 0 0 ${blur}px ${color};
    }
  `,

  /**
   * Neumorphism shadows
   */
  neumorphism: (
    selector: string,
    lightColor: string,
    darkColor: string,
    distance: number,
    blur: number
  ) => `
    ${selector} {
      box-shadow: 
        -${distance}px -${distance}px ${blur}px ${lightColor},
        ${distance}px ${distance}px ${blur}px ${darkColor};
    }
    ${selector}:active {
      box-shadow: 
        inset -${distance/2}px -${distance/2}px ${blur/2}px ${lightColor},
        inset ${distance/2}px ${distance/2}px ${blur/2}px ${darkColor};
    }
  `,

  /**
   * Glassmorphism
   */
  glassmorphism: (
    selector: string,
    blur: number,
    saturation: number,
    borderColor: string
  ) => `
    ${selector} {
      backdrop-filter: blur(${blur}px) saturate(${saturation});
      -webkit-backdrop-filter: blur(${blur}px) saturate(${saturation});
      border: 1px solid ${borderColor};
    }
  `,

  /**
   * Subtle glow on accent elements
   */
  accentGlow: (selector: string, color: string, intensity: number) => `
    ${selector} {
      box-shadow: 0 0 ${20 * intensity}px ${color}40,
                  0 0 ${40 * intensity}px ${color}20;
    }
  `,

  /**
   * Reduced motion fallback
   */
  reducedMotion: () => `
    @media (prefers-reduced-motion: reduce) {
      *, *::before, *::after {
        animation-duration: 0.01ms !important;
        animation-iteration-count: 1 !important;
        transition-duration: 0.01ms !important;
      }
    }
  `
};

// =============================================================================
// Micro-Interactions Engine
// =============================================================================

class MicroEngine {
  private config: MicroConfig;
  private particlePool: ParticlePool;
  private canvas: HTMLCanvasElement | null = null;
  private ctx: CanvasRenderingContext2D | null = null;
  private running = false;
  private lastTime = 0;
  private frameInterval: number;
  private styleElement: HTMLStyleElement | null = null;
  private reducedMotion = false;
  private isVisible = true;

  constructor(config: Partial<MicroConfig> = {}) {
    this.config = { ...DEFAULT_CONFIG, ...config };
    this.particlePool = new ParticlePool(this.config.maxParticles);
    this.frameInterval = 1000 / this.config.targetFPS;

    // Check reduced motion preference
    if (typeof window !== 'undefined' && this.config.respectReducedMotion) {
      const mq = window.matchMedia('(prefers-reduced-motion: reduce)');
      this.reducedMotion = mq.matches;
      mq.addEventListener('change', (e) => {
        this.reducedMotion = e.matches;
        if (this.reducedMotion) {
          this.particlePool.clear();
        }
      });
    }

    // Track visibility
    if (typeof document !== 'undefined' && this.config.pauseWhenHidden) {
      document.addEventListener('visibilitychange', () => {
        this.isVisible = !document.hidden;
      });
    }
  }

  /**
   * Initialize the particle canvas
   */
  initCanvas(container: HTMLElement): void {
    if (this.reducedMotion) return;

    this.canvas = document.createElement('canvas');
    this.canvas.style.cssText = `
      position: fixed;
      top: 0;
      left: 0;
      width: 100%;
      height: 100%;
      pointer-events: none;
      z-index: 9999;
    `;
    this.canvas.width = window.innerWidth;
    this.canvas.height = window.innerHeight;
    
    this.ctx = this.canvas.getContext('2d', { alpha: true });
    container.appendChild(this.canvas);

    // Resize handler
    window.addEventListener('resize', () => {
      if (this.canvas) {
        this.canvas.width = window.innerWidth;
        this.canvas.height = window.innerHeight;
      }
    });
  }

  /**
   * Inject CSS effects
   */
  injectStyles(styles: string): void {
    if (!this.styleElement) {
      this.styleElement = document.createElement('style');
      this.styleElement.id = 'prism-micro-styles';
      document.head.appendChild(this.styleElement);
    }
    this.styleElement.textContent = styles + cssEffects.reducedMotion();
  }

  /**
   * Start the animation loop
   */
  start(): void {
    if (this.running || this.reducedMotion) return;
    this.running = true;
    this.lastTime = performance.now();
    this.tick();
  }

  /**
   * Stop the animation loop
   */
  stop(): void {
    this.running = false;
  }

  /**
   * Main animation loop
   */
  private tick = (): void => {
    if (!this.running) return;

    const now = performance.now();
    const delta = now - this.lastTime;

    // Frame limiting
    if (delta >= this.frameInterval) {
      this.lastTime = now - (delta % this.frameInterval);
      
      // Only update/render when visible
      if (this.isVisible) {
        this.particlePool.update(delta);
        this.render();
      }
    }

    requestAnimationFrame(this.tick);
  };

  /**
   * Render particles to canvas
   */
  private render(): void {
    if (!this.ctx || !this.canvas) return;

    this.ctx.clearRect(0, 0, this.canvas.width, this.canvas.height);

    const particles = this.particlePool.getActive();
    for (const p of particles) {
      this.ctx.beginPath();
      this.ctx.arc(p.x, p.y, p.size, 0, Math.PI * 2);
      this.ctx.fillStyle = colorToRgba(p.color);
      this.ctx.fill();

      // Optional glow for sparkle drift
      if (p.drift === 'sparkle' && p.color.a > 0.5) {
        this.ctx.shadowColor = colorToRgba(p.color);
        this.ctx.shadowBlur = p.size * 3;
        this.ctx.fill();
        this.ctx.shadowBlur = 0;
      }
    }
  }

  // ===========================================================================
  // Public Effect Methods
  // ===========================================================================

  /**
   * Spawn dust motes (ambient particles)
   */
  spawnDustMotes(count: number, color: string, region?: DOMRect): void {
    if (this.reducedMotion) return;

    const parsed = parseColor(color);
    const bounds = region || {
      x: 0, y: 0,
      width: window.innerWidth,
      height: window.innerHeight
    };

    for (let i = 0; i < count; i++) {
      const particle = this.particlePool.acquire();
      if (!particle) break;

      particle.init({
        position: {
          x: bounds.x + Math.random() * bounds.width,
          y: bounds.y + Math.random() * bounds.height
        },
        velocity: {
          x: (Math.random() - 0.5) * 0.5,
          y: (Math.random() - 0.5) * 0.5
        },
        size: 1 + Math.random() * 2,
        color: { ...parsed, a: 0.1 + Math.random() * 0.15 },
        lifetime: 5000 + Math.random() * 10000,
        decay: 0.995,
        drift: 'float'
      });
    }
  }

  /**
   * Spawn rising particles (champagne bubbles, embers)
   */
  spawnRising(count: number, color: string, origin: Vector2): void {
    if (this.reducedMotion) return;

    const parsed = parseColor(color);

    for (let i = 0; i < count; i++) {
      const particle = this.particlePool.acquire();
      if (!particle) break;

      particle.init({
        position: {
          x: origin.x + (Math.random() - 0.5) * 50,
          y: origin.y
        },
        velocity: {
          x: (Math.random() - 0.5) * 0.3,
          y: -0.5 - Math.random() * 0.5
        },
        size: 1 + Math.random() * 2,
        color: { ...parsed, a: 0.2 + Math.random() * 0.2 },
        lifetime: 3000 + Math.random() * 4000,
        decay: 0.99,
        drift: 'rise'
      });
    }
  }

  /**
   * Spawn sparkle burst (celebration effect)
   */
  spawnSparkleBurst(origin: Vector2, colors: string[], count: number = 12): void {
    if (this.reducedMotion) return;

    for (let i = 0; i < count; i++) {
      const particle = this.particlePool.acquire();
      if (!particle) break;

      const angle = (Math.PI * 2 * i) / count + (Math.random() - 0.5) * 0.3;
      const speed = 2 + Math.random() * 2;
      const color = parseColor(colors[i % colors.length]);

      particle.init({
        position: { x: origin.x, y: origin.y },
        velocity: {
          x: Math.cos(angle) * speed,
          y: Math.sin(angle) * speed
        },
        size: 1 + Math.random() * 2,
        color: { ...color, a: 0.8 },
        lifetime: 600 + Math.random() * 400,
        decay: 0.96,
        drift: 'sparkle'
      });
    }
  }

  /**
   * Pulse effect on element (non-particle, CSS-based)
   */
  pulseElement(element: HTMLElement, color: string, duration: number = 400): void {
    if (this.reducedMotion) return;

    const originalBoxShadow = element.style.boxShadow;
    element.style.transition = `box-shadow ${duration}ms ease-out`;
    element.style.boxShadow = `0 0 20px ${color}60, 0 0 40px ${color}30`;

    setTimeout(() => {
      element.style.boxShadow = originalBoxShadow;
    }, duration);
  }

  /**
   * Ripple effect at position
   */
  createRipple(origin: Vector2, color: string, maxRadius: number = 100): void {
    if (this.reducedMotion) return;

    const ripple = document.createElement('div');
    ripple.style.cssText = `
      position: fixed;
      left: ${origin.x}px;
      top: ${origin.y}px;
      width: 0;
      height: 0;
      border-radius: 50%;
      border: 2px solid ${color};
      transform: translate(-50%, -50%);
      pointer-events: none;
      z-index: 9998;
      opacity: 0.6;
    `;
    document.body.appendChild(ripple);

    // Animate with requestAnimationFrame
    let start: number | null = null;
    const duration = 500;

    const animate = (timestamp: number) => {
      if (!start) start = timestamp;
      const progress = (timestamp - start) / duration;

      if (progress < 1) {
        const size = maxRadius * easeOutCubic(progress);
        const opacity = 0.6 * (1 - progress);
        ripple.style.width = `${size * 2}px`;
        ripple.style.height = `${size * 2}px`;
        ripple.style.opacity = String(opacity);
        requestAnimationFrame(animate);
      } else {
        ripple.remove();
      }
    };

    requestAnimationFrame(animate);
  }

  /**
   * Cleanup
   */
  destroy(): void {
    this.stop();
    this.particlePool.clear();
    if (this.canvas) {
      this.canvas.remove();
      this.canvas = null;
    }
    if (this.styleElement) {
      this.styleElement.remove();
      this.styleElement = null;
    }
  }
}

// =============================================================================
// Easter Egg System
// =============================================================================

class EasterEggSystem {
  private engine: MicroEngine;
  private konamiSequence = ['ArrowUp', 'ArrowUp', 'ArrowDown', 'ArrowDown', 'ArrowLeft', 'ArrowRight', 'ArrowLeft', 'ArrowRight', 'KeyB', 'KeyA'];
  private konamiProgress = 0;
  private typingStreak = 0;
  private lastKeyTime = 0;
  private callbacks: Map<string, () => void> = new Map();

  constructor(engine: MicroEngine) {
    this.engine = engine;
    this.initListeners();
  }

  private initListeners(): void {
    // Konami code detector
    document.addEventListener('keydown', (e) => {
      if (e.code === this.konamiSequence[this.konamiProgress]) {
        this.konamiProgress++;
        if (this.konamiProgress === this.konamiSequence.length) {
          this.trigger('konami');
          this.konamiProgress = 0;
        }
      } else {
        this.konamiProgress = 0;
      }

      // Typing streak detector
      const now = Date.now();
      if (now - this.lastKeyTime < 200) {
        this.typingStreak++;
        if (this.typingStreak === 50) {
          this.trigger('flowState');
        }
      } else {
        this.typingStreak = 0;
      }
      this.lastKeyTime = now;
    });

    // Triple click detector
    let clickCount = 0;
    let clickTimer: number | null = null;

    document.addEventListener('click', (e) => {
      clickCount++;
      
      if (clickTimer) clearTimeout(clickTimer);
      
      clickTimer = window.setTimeout(() => {
        if (clickCount >= 3) {
          this.trigger('tripleClick', { x: e.clientX, y: e.clientY });
        }
        clickCount = 0;
      }, 300);
    });
  }

  on(event: string, callback: () => void): void {
    this.callbacks.set(event, callback);
  }

  private trigger(event: string, data?: any): void {
    const callback = this.callbacks.get(event);
    if (callback) {
      callback();
    }

    // Default behaviors
    switch (event) {
      case 'konami':
        // Rainbow celebration
        for (let i = 0; i < 5; i++) {
          setTimeout(() => {
            this.engine.spawnSparkleBurst(
              { x: Math.random() * window.innerWidth, y: Math.random() * window.innerHeight },
              ['#ff6b6b', '#feca57', '#48dbfb', '#ff9ff3', '#54a0ff'],
              15
            );
          }, i * 200);
        }
        break;

      case 'tripleClick':
        if (data) {
          this.engine.spawnSparkleBurst(data, ['#d4af37', '#c0c0c0'], 8);
        }
        break;

      case 'flowState':
        // Gentle ambient glow increase - handled by theme
        console.log('🔥 Flow state achieved!');
        break;
    }
  }
}

// =============================================================================
// Theme Integration
// =============================================================================

interface ThemeEffects {
  hoverLift?: { distance: number; duration: number };
  pressEffect?: { scale: number; duration: number };
  focusRing?: { color: string; spread: number; blur: number };
  neumorphism?: { lightColor: string; darkColor: string; distance: number; blur: number };
  glassmorphism?: { blur: number; saturation: number; borderColor: string };
  accentGlow?: { color: string; intensity: number };
  particles?: { enabled: boolean; type: string; count: number; color: string };
}

function generateThemeStyles(selector: string, effects: ThemeEffects): string {
  let styles = '';

  if (effects.hoverLift) {
    styles += cssEffects.hoverLift(selector, effects.hoverLift.distance, effects.hoverLift.duration);
  }

  if (effects.pressEffect) {
    styles += cssEffects.pressEffect(selector, effects.pressEffect.scale, effects.pressEffect.duration);
  }

  if (effects.focusRing) {
    styles += cssEffects.focusRing(selector, effects.focusRing.color, effects.focusRing.spread, effects.focusRing.blur);
  }

  if (effects.neumorphism) {
    styles += cssEffects.neumorphism(
      selector,
      effects.neumorphism.lightColor,
      effects.neumorphism.darkColor,
      effects.neumorphism.distance,
      effects.neumorphism.blur
    );
  }

  if (effects.glassmorphism) {
    styles += cssEffects.glassmorphism(
      selector,
      effects.glassmorphism.blur,
      effects.glassmorphism.saturation,
      effects.glassmorphism.borderColor
    );
  }

  if (effects.accentGlow) {
    styles += cssEffects.accentGlow(selector, effects.accentGlow.color, effects.accentGlow.intensity);
  }

  return styles;
}

// =============================================================================
// Exports
// =============================================================================

export {
  MicroEngine,
  EasterEggSystem,
  ParticlePool,
  Particle,
  cssEffects,
  generateThemeStyles
};

export type {
  MicroConfig,
  ThemeEffects,
  Vector2,
  Color,
  ParticleConfig
};
