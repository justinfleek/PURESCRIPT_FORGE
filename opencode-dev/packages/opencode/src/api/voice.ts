/**
 * Voice API Client
 * 
 * TypeScript client for voice engine API endpoints.
 */

export interface VoiceChatResponse {
  user_transcript: string;
  stt_confidence: number;
  stt_cost_usd: number;
  assistant_text: string;
  assistant_thinking: string | null;
  assistant_audio: string | null; // base64
  assistant_audio_format: string;
  tts_cost_usd: number;
  total_cost_usd: number;
  stt_error: string | null;
  chat_error: string | null;
  tts_error: string | null;
}

export interface TextChatResponse {
  assistant_text: string;
  assistant_thinking: string | null;
  assistant_audio_base64: string;
  assistant_audio_format: string;
  tts_cost_usd: number;
  total_cost_usd: number;
}

export interface VoiceSession {
  id: string;
  conversation_id: string;
  state: string;
  total_audio_seconds: number;
  started_at: string;
}

export interface TTSModel {
  id: string;
  name: string;
  hf_repo: string;
  status: string;
  file_size_mb: number;
  downloaded_at: string | null;
}

const API_BASE = '/api/voice';

/**
 * Send voice message (audio → transcript → AI → audio)
 */
export async function sendVoiceMessage(
  audio: Blob,
  conversationId: string = 'default',
  voice: string = 'Ryan',
  language: string = 'en'
): Promise<VoiceChatResponse> {
  const formData = new FormData();
  formData.append('audio', audio, 'audio.webm');
  formData.append('conversation_id', conversationId);
  formData.append('voice', voice);
  formData.append('language', language);

  const response = await fetch(`${API_BASE}/chat`, {
    method: 'POST',
    body: formData,
  });

  if (!response.ok) {
    interface ErrorResponse {
      error?: string;
      message?: string;
    }
    
    const getErrorMessage = (fallback: unknown, status: number): string => {
      if (typeof fallback === 'object' && fallback !== null) {
        const err = fallback as ErrorResponse;
        if (err.message) return err.message;
        if (err.error) return err.error;
      }
      return `HTTP ${status}`;
    };
    
    const error = await response.json().catch(() => ({ error: 'Unknown error' }));
    throw new Error(getErrorMessage(error, response.status));
  }

  return response.json();
}

/**
 * Send text message (text → AI → audio)
 */
export async function sendTextMessage(
  text: string,
  conversationId: string = 'default',
  voice: string = 'Ryan'
): Promise<TextChatResponse> {
  const response = await fetch(`${API_BASE}/chat/text`, {
    method: 'POST',
    headers: {
      'Content-Type': 'application/json',
    },
    body: JSON.stringify({
      text,
      conversation_id: conversationId,
      voice,
    }),
  });

  if (!response.ok) {
    interface ErrorResponse {
      error?: string;
      message?: string;
    }
    
    const getErrorMessage = (fallback: unknown, status: number): string => {
      if (typeof fallback === 'object' && fallback !== null) {
        const err = fallback as ErrorResponse;
        if (err.message) return err.message;
        if (err.error) return err.error;
      }
      return `HTTP ${status}`;
    };
    
    const error = await response.json().catch(() => ({ error: 'Unknown error' }));
    throw new Error(getErrorMessage(error, response.status));
  }

  return response.json();
}

/**
 * Get voice session
 */
export async function getVoiceSession(sessionId: string): Promise<VoiceSession> {
  const response = await fetch(`${API_BASE}/sessions/${sessionId}`);

  if (!response.ok) {
    interface ErrorResponse {
      error?: string;
      message?: string;
    }
    
    const getErrorMessage = (fallback: unknown, status: number): string => {
      if (typeof fallback === 'object' && fallback !== null) {
        const err = fallback as ErrorResponse;
        if (err.message) return err.message;
        if (err.error) return err.error;
      }
      return `HTTP ${status}`;
    };
    
    const error = await response.json().catch(() => ({ error: 'Unknown error' }));
    throw new Error(getErrorMessage(error, response.status));
  }

  return response.json();
}

/**
 * End voice session
 */
export async function endVoiceSession(sessionId: string): Promise<{ status: string; session_id: string }> {
  const response = await fetch(`${API_BASE}/sessions/${sessionId}/end`, {
    method: 'POST',
  });

  if (!response.ok) {
    interface ErrorResponse {
      error?: string;
      message?: string;
    }
    
    const getErrorMessage = (fallback: unknown, status: number): string => {
      if (typeof fallback === 'object' && fallback !== null) {
        const err = fallback as ErrorResponse;
        if (err.message) return err.message;
        if (err.error) return err.error;
      }
      return `HTTP ${status}`;
    };
    
    const error = await response.json().catch(() => ({ error: 'Unknown error' }));
    throw new Error(getErrorMessage(error, response.status));
  }

  return response.json();
}

/**
 * List available voices
 */
export async function listVoices(): Promise<string[]> {
  const response = await fetch(`${API_BASE}/voices`);

  if (!response.ok) {
    interface ErrorResponse {
      error?: string;
      message?: string;
    }
    
    const getErrorMessage = (fallback: unknown, status: number): string => {
      if (typeof fallback === 'object' && fallback !== null) {
        const err = fallback as ErrorResponse;
        if (err.message) return err.message;
        if (err.error) return err.error;
      }
      return `HTTP ${status}`;
    };
    
    const error = await response.json().catch(() => ({ error: 'Unknown error' }));
    throw new Error(getErrorMessage(error, response.status));
  }

  const data = await response.json();
  
  // Explicit check instead of || []
  if (data.voices && Array.isArray(data.voices)) {
    return data.voices;
  }
  return [];
}

/**
 * List available TTS models
 */
export async function listModels(): Promise<TTSModel[]> {
  const response = await fetch(`${API_BASE}/models`);

  if (!response.ok) {
    interface ErrorResponse {
      error?: string;
      message?: string;
    }
    
    const getErrorMessage = (fallback: unknown, status: number): string => {
      if (typeof fallback === 'object' && fallback !== null) {
        const err = fallback as ErrorResponse;
        if (err.message) return err.message;
        if (err.error) return err.error;
      }
      return `HTTP ${status}`;
    };
    
    const error = await response.json().catch(() => ({ error: 'Unknown error' }));
    throw new Error(getErrorMessage(error, response.status));
  }

  const data = await response.json();
  
  // Explicit check instead of || []
  if (data.models && Array.isArray(data.models)) {
    return data.models;
  }
  return [];
}

/**
 * Download TTS model
 */
export async function downloadModel(modelId: string): Promise<{ status: string; model_id: string; message: string }> {
  const response = await fetch(`${API_BASE}/models/download`, {
    method: 'POST',
    headers: {
      'Content-Type': 'application/json',
    },
    body: JSON.stringify({ model_id: modelId }),
  });

  if (!response.ok) {
    interface ErrorResponse {
      error?: string;
      message?: string;
    }
    
    const getErrorMessage = (fallback: unknown, status: number): string => {
      if (typeof fallback === 'object' && fallback !== null) {
        const err = fallback as ErrorResponse;
        if (err.message) return err.message;
        if (err.error) return err.error;
      }
      return `HTTP ${status}`;
    };
    
    const error = await response.json().catch(() => ({ error: 'Unknown error' }));
    throw new Error(getErrorMessage(error, response.status));
  }

  return response.json();
}
