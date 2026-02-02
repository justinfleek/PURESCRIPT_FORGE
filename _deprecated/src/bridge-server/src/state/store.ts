/**
 * State Store - Single Source of Truth
 * Production-grade state management with event broadcasting
 */
import { EventEmitter } from 'events';

export interface BalanceState {
  venice: {
    diem: number;
    usd: number;
    effective: number;
    lastUpdated: Date | null;
  };
  consumptionRate: number; // Diem per hour
  timeToDepletion: number | null; // milliseconds
  todayUsed: number;
  todayStartBalance: number;
  resetCountdown: number | null; // milliseconds until UTC midnight
  alertLevel: 'normal' | 'warning' | 'critical';
}

export interface SessionState {
  id: string;
  promptTokens: number;
  completionTokens: number;
  totalTokens: number;
  cost: number;
  model: string;
  provider: string;
  messageCount: number;
  startedAt: Date;
  updatedAt: Date;
}

export interface ProofState {
  connected: boolean;
  file: string | null;
  position: { line: number; column: number } | null;
  goals: Array<{
    type: string;
    context: Array<{ name: string; type: string }>;
  }>;
  diagnostics: Array<{
    severity: 'error' | 'warning' | 'info';
    message: string;
    range: {
      start: { line: number; col: number };
      end: { line: number; col: number };
    };
  }>;
  suggestedTactics: Array<{
    tactic: string;
    confidence: number;
  }>;
}

export interface UsageMetrics {
  totalTokens: number;
  totalCost: number;
  averageResponseTime: number;
  toolTimings: Record<string, number>; // tool name -> average duration (ms)
}

export interface VoiceMessage {
  id: string;
  role: 'user' | 'assistant';
  text: string;
  audioUrl?: string;
  durationSeconds?: number;
  sttConfidence?: number;
  timestamp: Date;
}

export interface VoiceSession {
  id: string;
  conversationId: string;
  orgId: string;
  userId: string;
  state: 'idle' | 'listening' | 'processing' | 'thinking' | 'speaking' | 'interrupted' | 'error' | 'ended';
  totalAudioSeconds: number;
  totalSttTokens: number;
  totalTtsCharacters: number;
  startedAt: Date;
  endedAt?: Date;
}

export interface VoiceUIState {
  isListening: boolean;
  isProcessing: boolean;
  isSpeaking: boolean;
  audioLevel: number; // 0-1 for visualization
}

export interface VoiceSettings {
  voice: string;
  language: string;
  quality: 'standard' | 'high';
}

export interface VoiceState {
  session: VoiceSession | null;
  messages: VoiceMessage[];
  uiState: VoiceUIState;
  settings: VoiceSettings;
}

export interface AppState {
  connected: boolean;
  balance: BalanceState;
  session: SessionState | null;
  proof: ProofState;
  metrics: UsageMetrics;
  voice: VoiceState;
}

function initialState(): AppState {
  return {
    connected: false,
    balance: {
      venice: {
        diem: 0,
        usd: 0,
        effective: 0,
        lastUpdated: null,
      },
      consumptionRate: 0,
      timeToDepletion: null,
      todayUsed: 0,
      todayStartBalance: 0,
      resetCountdown: null,
      alertLevel: 'normal',
    },
    session: null,
    proof: {
      connected: false,
      file: null,
      position: null,
      goals: [],
      diagnostics: [],
      suggestedTactics: [],
    },
    metrics: {
      totalTokens: 0,
      totalCost: 0,
      averageResponseTime: 0,
      toolTimings: {},
    },
    voice: {
      session: null,
      messages: [],
      uiState: {
        isListening: false,
        isProcessing: false,
        isSpeaking: false,
        audioLevel: 0,
      },
      settings: {
        voice: 'Ryan',
        language: 'en',
        quality: 'standard',
      },
    },
  };
}

/**
 * State Store - Manages application state and broadcasts changes
 */
export class StateStore extends EventEmitter {
  private state: AppState;
  
  constructor() {
    super();
    this.state = initialState();
  }
  
  /**
   * Get current state (immutable copy)
   */
  getState(): AppState {
    return structuredClone(this.state);
  }
  
  /**
   * Update balance (called by Venice proxy)
   */
  updateBalance(partial: Partial<BalanceState>): void {
    const prev = this.state.balance;
    this.state.balance = {
      ...prev,
      ...partial,
      venice: {
        ...prev.venice,
        ...(partial.venice ?? {}),
      },
    };
    
    // Calculate effective balance
    this.state.balance.venice.effective = 
      this.state.balance.venice.diem + this.state.balance.venice.usd;
    
    // Calculate alert level
    this.state.balance.alertLevel = this.calculateAlertLevel(this.state.balance);
    
    // Only broadcast changed fields
    const changes = this.diff(prev, this.state.balance);
    if (Object.keys(changes).length > 0) {
      this.emit('change', 'balance', changes);
    }
  }
  
  /**
   * Update session (called by OpenCode client)
   */
  updateSession(partial: Partial<SessionState>): void {
    if (!this.state.session && partial.id) {
      // New session
      this.state.session = {
        id: partial.id,
        promptTokens: partial.promptTokens ?? 0,
        completionTokens: partial.completionTokens ?? 0,
        totalTokens: partial.totalTokens ?? 0,
        cost: partial.cost ?? 0,
        model: partial.model ?? '',
        provider: partial.provider ?? '',
        messageCount: partial.messageCount ?? 0,
        startedAt: partial.startedAt ?? new Date(),
        updatedAt: partial.updatedAt ?? new Date(),
      };
      this.emit('change', 'session', this.state.session);
    } else if (this.state.session) {
      const prev = this.state.session;
      this.state.session = {
        ...prev,
        ...partial,
        updatedAt: new Date(),
      };
      
      const changes = this.diff(prev, this.state.session);
      if (Object.keys(changes).length > 0) {
        this.emit('change', 'session', changes);
      }
    }
  }
  
  /**
   * Clear session
   */
  clearSession(): void {
    if (this.state.session) {
      this.state.session = null;
      this.emit('change', 'session', null);
    }
  }
  
  /**
   * Update proof state (called by Lean proxy)
   */
  updateProof(partial: Partial<ProofState>): void {
    const prev = this.state.proof;
    this.state.proof = { ...prev, ...partial };
    
    const changes = this.diff(prev, this.state.proof);
    if (Object.keys(changes).length > 0) {
      this.emit('change', 'proof', changes);
    }
  }
  
  /**
   * Update metrics
   */
  updateMetrics(partial: Partial<UsageMetrics>): void {
    const prev = this.state.metrics;
    this.state.metrics = { ...prev, ...partial };
    
    const changes = this.diff(prev, this.state.metrics);
    if (Object.keys(changes).length > 0) {
      this.emit('change', 'metrics', changes);
    }
  }
  
  /**
   * Set connection status
   */
  setConnected(connected: boolean): void {
    if (this.state.connected !== connected) {
      this.state.connected = connected;
      this.emit('change', 'connected', connected);
    }
  }
  
  /**
   * Update voice state
   */
  updateVoice(partial: Partial<VoiceState>): void {
    const prev = this.state.voice;
    this.state.voice = {
      session: partial.session ?? prev.session,
      messages: partial.messages ?? prev.messages,
      uiState: {
        ...prev.uiState,
        ...(partial.uiState ?? {}),
      },
      settings: {
        ...prev.settings,
        ...(partial.settings ?? {}),
      },
    };
    
    const changes = this.diff(prev, this.state.voice);
    if (Object.keys(changes).length > 0) {
      this.emit('change', 'voice', changes);
    }
  }
  
  /**
   * Add voice message
   */
  addVoiceMessage(message: VoiceMessage): void {
    this.state.voice.messages = [...this.state.voice.messages, message];
    this.emit('change', 'voice.messages', this.state.voice.messages);
  }
  
  /**
   * Clear voice session
   */
  clearVoiceSession(): void {
    if (this.state.voice.session) {
      this.state.voice.session = null;
      this.state.voice.messages = [];
      this.state.voice.uiState = {
        isListening: false,
        isProcessing: false,
        isSpeaking: false,
        audioLevel: 0,
      };
      this.emit('change', 'voice', this.state.voice);
    }
  }
  
  /**
   * Calculate alert level based on balance
   */
  private calculateAlertLevel(balance: BalanceState): 'normal' | 'warning' | 'critical' {
    if (balance.venice.effective === 0) {
      return 'critical';
    }
    
    const depletionHours = balance.timeToDepletion 
      ? balance.timeToDepletion / (1000 * 60 * 60)
      : Infinity;
    
    if (depletionHours < 2) {
      return 'critical';
    }
    
    if (depletionHours < 8 || balance.venice.effective < balance.todayStartBalance * 0.2) {
      return 'warning';
    }
    
    return 'normal';
  }
  
  /**
   * Calculate diff between objects (only changed fields)
   */
  private diff(prev: Record<string, unknown>, next: Record<string, unknown>): Record<string, unknown> {
    const changes: Record<string, unknown> = {};
    for (const key of Object.keys(next)) {
      try {
        const prevStr = JSON.stringify(prev[key]);
        const nextStr = JSON.stringify(next[key]);
        if (prevStr !== nextStr) {
          changes[key] = next[key];
        }
      } catch (error) {
        // If JSON.stringify fails (e.g., circular reference), consider it changed
        // Fallback to direct comparison
        if (prev[key] !== next[key]) {
          changes[key] = next[key];
        }
      }
    }
    return changes;
  }
  
  /**
   * Subscribe to state changes
   */
  onStateChange(handler: (path: string, value: unknown) => void): () => void {
    this.on('change', handler);
    return () => {
      this.off('change', handler);
    };
  }
}
