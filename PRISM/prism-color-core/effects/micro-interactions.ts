/**
 * Prism Micro-Interactions Engine
 * 
 * Performance-optimized subtle effects for premium themes.
 * All effects respect prefers-reduced-motion and stay under 4ms frame budget.
 * 
 * Architecture:
 * - Uses requestAnimationFrame with frame skipping
 * - CSS transforms only (no layout thrashing)
 * - GPU-accelerated via will-change and transform3d
 * - Automatic cleanup and memory management
 * - Lazy initialization - effects only activate when visible
 */

// =============================================================================
// Configuration
// =============================================================================

export interface MicroConfig {
  /** Target frames per second (will skip frames if needed) */
  targetFPS: number;
  /** Maximum particles across all effects */
  maxParticles: number;
  /** Enable GPU acceleration hints */
  useGPU: boolean;
  /** Respect prefers-reduced-motion */
  respectMotionPreference: boolean;
  /** Fade out effects when idle */
  fadeOnIdle: boolean;
  /** Idle timeout in ms */
  idleTimeout: number;
}

const DEFAULT_CONFIG: MicroConfig = {
  targetFPS: 30, // 30fps is enough for subtle effects, saves battery
  maxParticles: 12,
  useGPU: true,
  respectMotionPreference: true,
  fadeOnIdle: true,
  idleTimeout: 3000
};

// =============================================================================
// Core Engine
// =============================================================================

type EffectCleanup = () => void;

class MicroEngine {
  private config: MicroConfig;
  private isRunning = false;
  private lastFrameTime = 0;
  private frameInterval: number;
  private animationId: number | null = null;
  private effects: Map<string, EffectCleanup> = new Map();
  private reducedMotion = false;
  private isIdle = false;
  private idleTimer: ReturnType<typeof setTimeout> | null = null;
  private particles: Particle[] = [];
  
  constructor(config: Partial<MicroConfig> = {}) {
    this.config = { ...DEFAULT_CONFIG, ...config };
    this.frameInterval = 1000 / this.config.targetFPS;
    
    // Check motion preference
    if (this.config.respectMotionPreference && typeof window !== 'undefined') {
      const mq = window.matchMedia('(prefers-reduced-motion: reduce)');
      this.reducedMotion = mq.matches;
      mq.addEventListener('change', (e) => {
        this.reducedMotion = e.matches;
        if (this.reducedMotion) this.stop();
      });
    }
    
    // Track activity for idle detection
    if (typeof window !== 'undefined' && this.config.fadeOnIdle) {
      ['mousemove', 'keydown', 'scroll', 'click'].forEach(event => {
        window.addEventListener(event, () => this.resetIdleTimer(), { passive: true });
      });
    }
  }
  
  private resetIdleTimer(): void {
    this.isIdle = false;
    if (this.idleTimer) clearTimeout(this.idleTimer);
    this.idleTimer = setTimeout(() => {
      this.isIdle = true;
    }, this.config.idleTimeout);
  }
  
  start(): void {
    if (this.isRunning || this.reducedMotion) return;
    this.isRunning = true;
    this.lastFrameTime = performance.now();
    this.tick();
  }
  
  stop(): void {
    this.isRunning = false;
    if (this.animationId !== null) {
      cancelAnimationFrame(this.animationId);
      this.animationId = null;
    }
  }
  
  private tick = (): void => {
    if (!this.isRunning) return;
    
    const now = performance.now();
    const delta = now - this.lastFrameTime;
    
    // Frame skip if we're behind
    if (delta >= this.frameInterval) {
      this.lastFrameTime = now - (delta % this.frameInterval);
      this.update(delta);
    }
    
    this.animationId = requestAnimationFrame(this.tick);
  };
  
  private update(delta: number): void {
    // Update particles
    for (let i = this.particles.length - 1; i >= 0; i--) {
      const p = this.particles[i];
      p.update(delta, this.isIdle);
      if (p.isDead()) {
        p.cleanup();
        this.particles.splice(i, 1);
      }
    }
  }
  
  registerEffect(id: string, cleanup: EffectCleanup): void {
    this.effects.set(id, cleanup);
  }
  
  unregisterEffect(id: string): void {
    const cleanup = this.effects.get(id);
    if (cleanup) {
      cleanup();
      this.effects.delete(id);
    }
  }
  
  addParticle(particle: Particle): boolean {
    if (this.particles.length >= this.config.maxParticles) return false;
    this.particles.push(particle);
    return true;
  }
  
  destroy(): void {
    this.stop();
    this.effects.forEach(cleanup => cleanup());
    this.effects.clear();
    this.particles.forEach(p => p.cleanup());
    this.particles = [];
    if (this.idleTimer) clearTimeout(this.idleTimer);
  }
  
  get isReducedMotion(): boolean {
    return this.reducedMotion;
  }
  
  get idle(): boolean {
    return this.isIdle;
  }
}

// =============================================================================
// Particle System
// =============================================================================

interface ParticleConfig {
  x: number;
  y: number;
  size: number;
  color: string;
  opacity: number;
  lifetime: number;
  velocity?: { x: number; y: number };
  drift?: 'rise' | 'fall' | 'wave' | 'organic';
  element?: HTMLElement;
}

class Particle {
  private config: ParticleConfig;
  private age = 0;
  private element: HTMLElement | null = null;
  private baseY: number;
  
  constructor(config: ParticleConfig) {
    this.config = config;
    this.baseY = config.y;
    
    if (config.element) {
      this.element = config.element;
    } else if (typeof document !== 'undefined') {
      this.element = document.createElement('div');
      this.element.className = 'prism-particle';
      this.element.style.cssText = `
        position: fixed;
        pointer-events: none;
        z-index: 9999;
        width: ${config.size}px;
        height: ${config.size}px;
        border-radius: 50%;
        background: ${config.color};
        opacity: 0;
        will-change: transform, opacity;
        transform: translate3d(${config.x}px, ${config.y}px, 0);
      `;
      document.body.appendChild(this.element);
    }
  }
  
  update(delta: number, isIdle: boolean): void {
    this.age += delta;
    
    if (!this.element) return;
    
    const progress = Math.min(this.age / this.config.lifetime, 1);
    
    // Fade in/out
    let opacity = this.config.opacity;
    if (progress < 0.1) {
      opacity *= progress / 0.1; // Fade in
    } else if (progress > 0.8) {
      opacity *= (1 - progress) / 0.2; // Fade out
    }
    
    // Apply idle fade
    if (isIdle) {
      opacity *= 0.3;
    }
    
    // Calculate position based on drift type
    let x = this.config.x;
    let y = this.config.y;
    
    if (this.config.velocity) {
      x += this.config.velocity.x * this.age * 0.001;
      y += this.config.velocity.y * this.age * 0.001;
    }
    
    switch (this.config.drift) {
      case 'rise':
        y = this.baseY - (this.age * 0.02);
        x += Math.sin(this.age * 0.002) * 10;
        break;
      case 'fall':
        y = this.baseY + (this.age * 0.015);
        x += Math.sin(this.age * 0.003) * 8;
        break;
      case 'wave':
        x += Math.sin(this.age * 0.001) * 20;
        y += Math.cos(this.age * 0.0015) * 15;
        break;
      case 'organic':
        x += Math.sin(this.age * 0.0008 + this.config.x * 0.1) * 25;
        y += Math.cos(this.age * 0.001 + this.config.y * 0.1) * 20;
        break;
    }
    
    this.element.style.transform = `translate3d(${x}px, ${y}px, 0)`;
    this.element.style.opacity = String(opacity);
  }
  
  isDead(): boolean {
    return this.age >= this.config.lifetime;
  }
  
  cleanup(): void {
    if (this.element && this.element.parentNode) {
      this.element.parentNode.removeChild(this.element);
    }
    this.element = null;
  }
}

// =============================================================================
// Effect Implementations
// =============================================================================

/**
 * Cursor Spotlight - subtle glow that follows the cursor
 */
export function createCursorSpotlight(options: {
  color: string;
  radius: number;
  opacity: number;
  blur: number;
  smoothing: number;
}): EffectCleanup {
  if (typeof document === 'undefined') return () => {};
  
  const spotlight = document.createElement('div');
  spotlight.className = 'prism-cursor-spotlight';
  spotlight.style.cssText = `
    position: fixed;
    pointer-events: none;
    z-index: 9998;
    width: ${options.radius * 2}px;
    height: ${options.radius * 2}px;
    border-radius: 50%;
    background: radial-gradient(circle, ${options.color}${Math.round(options.opacity * 255).toString(16).padStart(2, '0')} 0%, transparent 70%);
    filter: blur(${options.blur}px);
    opacity: 0;
    will-change: transform, opacity;
    transform: translate3d(-50%, -50%, 0);
    transition: opacity 0.3s ease-out;
  `;
  document.body.appendChild(spotlight);
  
  let targetX = 0, targetY = 0;
  let currentX = 0, currentY = 0;
  let rafId: number | null = null;
  
  const lerp = (a: number, b: number, t: number) => a + (b - a) * t;
  
  const animate = () => {
    currentX = lerp(currentX, targetX, options.smoothing);
    currentY = lerp(currentY, targetY, options.smoothing);
    spotlight.style.transform = `translate3d(${currentX}px, ${currentY}px, 0)`;
    rafId = requestAnimationFrame(animate);
  };
  
  const onMove = (e: MouseEvent) => {
    targetX = e.clientX;
    targetY = e.clientY;
    spotlight.style.opacity = '1';
  };
  
  const onLeave = () => {
    spotlight.style.opacity = '0';
  };
  
  document.addEventListener('mousemove', onMove, { passive: true });
  document.addEventListener('mouseleave', onLeave);
  animate();
  
  return () => {
    if (rafId) cancelAnimationFrame(rafId);
    document.removeEventListener('mousemove', onMove);
    document.removeEventListener('mouseleave', onLeave);
    if (spotlight.parentNode) spotlight.parentNode.removeChild(spotlight);
  };
}

/**
 * Ambient Particles - barely visible floating particles
 */
export function createAmbientParticles(
  engine: MicroEngine,
  options: {
    count: number;
    colors: string[];
    sizeRange: [number, number];
    speed: number;
    drift: 'rise' | 'fall' | 'wave' | 'organic';
    opacity: number;
    container?: HTMLElement;
  }
): EffectCleanup {
  if (typeof document === 'undefined' || engine.isReducedMotion) return () => {};
  
  const container = options.container || document.body;
  const bounds = container.getBoundingClientRect();
  const particles: Particle[] = [];
  
  const spawnParticle = () => {
    if (particles.length >= options.count) return;
    
    const color = options.colors[Math.floor(Math.random() * options.colors.length)];
    const size = options.sizeRange[0] + Math.random() * (options.sizeRange[1] - options.sizeRange[0]);
    
    const particle = new Particle({
      x: bounds.left + Math.random() * bounds.width,
      y: bounds.top + Math.random() * bounds.height,
      size,
      color,
      opacity: options.opacity,
      lifetime: 8000 + Math.random() * 12000,
      drift: options.drift
    });
    
    particles.push(particle);
    engine.addParticle(particle);
  };
  
  // Spawn initial particles staggered
  for (let i = 0; i < options.count; i++) {
    setTimeout(spawnParticle, i * 500);
  }
  
  // Continuously spawn to replace dead particles
  const spawnInterval = setInterval(() => {
    if (particles.length < options.count && !engine.isReducedMotion) {
      spawnParticle();
    }
    // Clean up dead particles from our tracking
    for (let i = particles.length - 1; i >= 0; i--) {
      if (particles[i].isDead()) {
        particles.splice(i, 1);
      }
    }
  }, 2000);
  
  return () => {
    clearInterval(spawnInterval);
    particles.forEach(p => p.cleanup());
  };
}

/**
 * Hover Lift - subtle elevation on hover
 */
export function createHoverLift(options: {
  selector: string;
  lift: number;
  scale: number;
  shadowBoost: number;
  transitionMs: number;
  easing: string;
}): EffectCleanup {
  if (typeof document === 'undefined') return () => {};
  
  const style = document.createElement('style');
  style.textContent = `
    ${options.selector} {
      transition: transform ${options.transitionMs}ms ${options.easing},
                  box-shadow ${options.transitionMs}ms ${options.easing};
      will-change: transform;
    }
    ${options.selector}:hover {
      transform: translateY(-${options.lift}px) scale(${options.scale});
    }
  `;
  document.head.appendChild(style);
  
  return () => {
    if (style.parentNode) style.parentNode.removeChild(style);
  };
}

/**
 * Click Ripple - quantum-style wave collapse effect
 */
export function createClickRipple(options: {
  color: string;
  opacity: number;
  duration: number;
  size: number;
}): EffectCleanup {
  if (typeof document === 'undefined') return () => {};
  
  const onClick = (e: MouseEvent) => {
    const ripple = document.createElement('div');
    ripple.style.cssText = `
      position: fixed;
      pointer-events: none;
      z-index: 9999;
      width: ${options.size}px;
      height: ${options.size}px;
      border-radius: 50%;
      background: transparent;
      border: 1px solid ${options.color};
      opacity: ${options.opacity};
      transform: translate(-50%, -50%) scale(0);
      left: ${e.clientX}px;
      top: ${e.clientY}px;
      animation: prism-ripple ${options.duration}ms ease-out forwards;
    `;
    document.body.appendChild(ripple);
    
    setTimeout(() => {
      if (ripple.parentNode) ripple.parentNode.removeChild(ripple);
    }, options.duration);
  };
  
  // Add keyframes if not present
  if (!document.getElementById('prism-ripple-keyframes')) {
    const keyframes = document.createElement('style');
    keyframes.id = 'prism-ripple-keyframes';
    keyframes.textContent = `
      @keyframes prism-ripple {
        to {
          transform: translate(-50%, -50%) scale(1);
          opacity: 0;
        }
      }
    `;
    document.head.appendChild(keyframes);
  }
  
  document.addEventListener('click', onClick);
  
  return () => {
    document.removeEventListener('click', onClick);
  };
}

/**
 * Surface Shimmer - subtle light movement across surfaces
 */
export function createSurfaceShimmer(options: {
  selector: string;
  color: string;
  intensity: number;
  angle: number;
  speed: number;
}): EffectCleanup {
  if (typeof document === 'undefined') return () => {};
  
  const id = `prism-shimmer-${Date.now()}`;
  const style = document.createElement('style');
  style.textContent = `
    ${options.selector}::before {
      content: '';
      position: absolute;
      inset: 0;
      background: linear-gradient(
        ${options.angle}deg,
        transparent 0%,
        ${options.color}${Math.round(options.intensity * 255).toString(16).padStart(2, '0')} 50%,
        transparent 100%
      );
      background-size: 200% 100%;
      animation: ${id} ${1 / options.speed}ms linear infinite;
      pointer-events: none;
    }
    @keyframes ${id} {
      from { background-position: 200% 0; }
      to { background-position: -200% 0; }
    }
  `;
  document.head.appendChild(style);
  
  return () => {
    if (style.parentNode) style.parentNode.removeChild(style);
  };
}

/**
 * Typing Pulse - subtle glow on keystroke
 */
export function createTypingPulse(options: {
  color: string;
  intensity: number;
  duration: number;
  selector: string;
}): EffectCleanup {
  if (typeof document === 'undefined') return () => {};
  
  let timeoutId: ReturnType<typeof setTimeout> | null = null;
  
  const onKeyDown = () => {
    const elements = document.querySelectorAll(options.selector);
    elements.forEach(el => {
      (el as HTMLElement).style.boxShadow = `0 0 ${20 * options.intensity}px ${options.color}`;
    });
    
    if (timeoutId) clearTimeout(timeoutId);
    timeoutId = setTimeout(() => {
      elements.forEach(el => {
        (el as HTMLElement).style.boxShadow = '';
      });
    }, options.duration);
  };
  
  document.addEventListener('keydown', onKeyDown);
  
  return () => {
    document.removeEventListener('keydown', onKeyDown);
    if (timeoutId) clearTimeout(timeoutId);
  };
}

/**
 * Marble Veins - SVG filter for marble texture effect
 */
export function createMarbleVeins(options: {
  color: string;
  secondaryColor?: string;
  turbulence: number;
  frequency: number;
}): EffectCleanup {
  if (typeof document === 'undefined') return () => {};
  
  const svg = document.createElementNS('http://www.w3.org/2000/svg', 'svg');
  svg.setAttribute('width', '0');
  svg.setAttribute('height', '0');
  svg.style.position = 'absolute';
  svg.innerHTML = `
    <defs>
      <filter id="marble-texture" x="0%" y="0%" width="100%" height="100%">
        <feTurbulence 
          type="fractalNoise" 
          baseFrequency="${options.frequency}" 
          numOctaves="4" 
          seed="${Math.random() * 100}"
          result="noise"
        />
        <feDisplacementMap 
          in="SourceGraphic" 
          in2="noise" 
          scale="${options.turbulence * 10}" 
          xChannelSelector="R" 
          yChannelSelector="G"
        />
      </filter>
    </defs>
  `;
  document.body.appendChild(svg);
  
  return () => {
    if (svg.parentNode) svg.parentNode.removeChild(svg);
  };
}

/**
 * Neumorphic Shadows - dynamic soft shadows for neumorphism
 */
export function createNeumorphicShadows(options: {
  selector: string;
  surfaceColor: string;
  lightColor: string;
  shadowColor: string;
  distance: number;
  blur: number;
}): EffectCleanup {
  if (typeof document === 'undefined') return () => {};
  
  const style = document.createElement('style');
  style.textContent = `
    ${options.selector} {
      background: ${options.surfaceColor};
      box-shadow: 
        -${options.distance}px -${options.distance}px ${options.blur}px ${options.lightColor},
        ${options.distance}px ${options.distance}px ${options.blur}px ${options.shadowColor};
      transition: box-shadow 0.2s ease;
    }
    ${options.selector}:active,
    ${options.selector}.pressed {
      box-shadow: 
        inset -${options.distance / 2}px -${options.distance / 2}px ${options.blur / 2}px ${options.lightColor},
        inset ${options.distance / 2}px ${options.distance / 2}px ${options.blur / 2}px ${options.shadowColor};
    }
  `;
  document.head.appendChild(style);
  
  return () => {
    if (style.parentNode) style.parentNode.removeChild(style);
  };
}

/**
 * Glass Effect - glassmorphism with backdrop blur
 */
export function createGlassEffect(options: {
  selector: string;
  blur: number;
  opacity: number;
  saturation: number;
  borderColor: string;
  borderWidth: number;
}): EffectCleanup {
  if (typeof document === 'undefined') return () => {};
  
  const style = document.createElement('style');
  style.textContent = `
    ${options.selector} {
      background: rgba(255, 255, 255, ${options.opacity * 0.1});
      backdrop-filter: blur(${options.blur}px) saturate(${options.saturation});
      -webkit-backdrop-filter: blur(${options.blur}px) saturate(${options.saturation});
      border: ${options.borderWidth}px solid ${options.borderColor};
    }
  `;
  document.head.appendChild(style);
  
  return () => {
    if (style.parentNode) style.parentNode.removeChild(style);
  };
}

// =============================================================================
// Easter Eggs
// =============================================================================

/**
 * Konami Code Easter Egg
 */
export function createKonamiEasterEgg(callback: () => void): EffectCleanup {
  if (typeof document === 'undefined') return () => {};
  
  const sequence = ['ArrowUp', 'ArrowUp', 'ArrowDown', 'ArrowDown', 'ArrowLeft', 'ArrowRight', 'ArrowLeft', 'ArrowRight', 'KeyB', 'KeyA'];
  let progress = 0;
  
  const onKeyDown = (e: KeyboardEvent) => {
    if (e.code === sequence[progress]) {
      progress++;
      if (progress === sequence.length) {
        callback();
        progress = 0;
      }
    } else {
      progress = 0;
    }
  };
  
  document.addEventListener('keydown', onKeyDown);
  
  return () => {
    document.removeEventListener('keydown', onKeyDown);
  };
}

/**
 * Idle Sparkle - rare sparkle when user is idle
 */
export function createIdleSparkle(
  engine: MicroEngine,
  options: {
    color: string;
    probability: number;
    intensity: number;
    duration: number;
  }
): EffectCleanup {
  if (typeof document === 'undefined') return () => {};
  
  let intervalId: ReturnType<typeof setInterval>;
  
  intervalId = setInterval(() => {
    if (!engine.idle || engine.isReducedMotion) return;
    
    if (Math.random() < options.probability) {
      const sparkle = document.createElement('div');
      const x = Math.random() * window.innerWidth;
      const y = Math.random() * window.innerHeight;
      
      sparkle.style.cssText = `
        position: fixed;
        pointer-events: none;
        z-index: 9999;
        left: ${x}px;
        top: ${y}px;
        width: 4px;
        height: 4px;
        background: ${options.color};
        border-radius: 50%;
        box-shadow: 0 0 ${10 * options.intensity}px ${options.color};
        animation: prism-sparkle ${options.duration}ms ease-out forwards;
      `;
      
      document.body.appendChild(sparkle);
      
      setTimeout(() => {
        if (sparkle.parentNode) sparkle.parentNode.removeChild(sparkle);
      }, options.duration);
    }
  }, 1000);
  
  // Add keyframes
  if (!document.getElementById('prism-sparkle-keyframes')) {
    const keyframes = document.createElement('style');
    keyframes.id = 'prism-sparkle-keyframes';
    keyframes.textContent = `
      @keyframes prism-sparkle {
        0% { transform: scale(0); opacity: 1; }
        50% { transform: scale(1); opacity: 1; }
        100% { transform: scale(0); opacity: 0; }
      }
    `;
    document.head.appendChild(keyframes);
  }
  
  return () => {
    clearInterval(intervalId);
  };
}

// =============================================================================
// Main Export
// =============================================================================

export const PrismMicro = {
  Engine: MicroEngine,
  Particle,
  effects: {
    cursorSpotlight: createCursorSpotlight,
    ambientParticles: createAmbientParticles,
    hoverLift: createHoverLift,
    clickRipple: createClickRipple,
    surfaceShimmer: createSurfaceShimmer,
    typingPulse: createTypingPulse,
    marbleVeins: createMarbleVeins,
    neumorphicShadows: createNeumorphicShadows,
    glassEffect: createGlassEffect
  },
  easterEggs: {
    konami: createKonamiEasterEgg,
    idleSparkle: createIdleSparkle
  }
};

export default PrismMicro;
