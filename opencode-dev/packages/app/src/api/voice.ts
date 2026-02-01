/**
 * Voice API Client
 * 
 * TypeScript client for voice engine API endpoints.
 */

export interface VoiceChatResponse {
  user_transcript: string
  stt_confidence: number
  stt_cost_usd: number
  assistant_text: string
  assistant_thinking: string | null
  assistant_audio: string | null // base64
  assistant_audio_format: string
  tts_cost_usd: number
  total_cost_usd: number
  stt_error: string | null
  chat_error: string | null
  tts_error: string | null
}

export interface TextChatResponse {
  assistant_text: string
  assistant_thinking: string | null
  assistant_audio_base64: string
  assistant_audio_format: string
  tts_cost_usd: number
  total_cost_usd: number
}

const API_BASE = "/api/voice"

/**
 * Send voice message (audio → transcript → AI → audio)
 */
export async function sendVoiceMessage(
  audio: Blob,
  conversationId: string = "default",
  voice: string = "Ryan",
  language: string = "en"
): Promise<VoiceChatResponse> {
  const formData = new FormData()
  formData.append("audio", audio, "audio.webm")
  formData.append("conversation_id", conversationId)
  formData.append("voice", voice)
  formData.append("language", language)

  const response = await fetch(`${API_BASE}/chat`, {
    method: "POST",
    body: formData,
  })

  if (!response.ok) {
    const error = await response.json().catch(() => ({ error: "Unknown error" }))
    const msg = typeof error === "object" && error !== null
      ? (error as { message?: string; error?: string }).message ?? (error as { error?: string }).error ?? `HTTP ${response.status}`
      : `HTTP ${response.status}`
    throw new Error(msg)
  }

  return response.json()
}

/**
 * Send text message (text → AI → audio)
 */
export async function sendTextMessage(
  text: string,
  conversationId: string = "default",
  voice: string = "Ryan"
): Promise<TextChatResponse> {
  const response = await fetch(`${API_BASE}/chat/text`, {
    method: "POST",
    headers: {
      "Content-Type": "application/json",
    },
    body: JSON.stringify({
      text,
      conversation_id: conversationId,
      voice,
    }),
  })

  if (!response.ok) {
    const error = await response.json().catch(() => ({ error: "Unknown error" }))
    const msg = typeof error === "object" && error !== null
      ? (error as { message?: string; error?: string }).message ?? (error as { error?: string }).error ?? `HTTP ${response.status}`
      : `HTTP ${response.status}`
    throw new Error(msg)
  }

  return response.json()
}

/**
 * List available voices
 */
export async function listVoices(): Promise<string[]> {
  const response = await fetch(`${API_BASE}/voices`)

  if (!response.ok) {
    const error = await response.json().catch(() => ({ error: "Unknown error" }))
    const msg = typeof error === "object" && error !== null
      ? (error as { message?: string; error?: string }).message ?? (error as { error?: string }).error ?? `HTTP ${response.status}`
      : `HTTP ${response.status}`
    throw new Error(msg)
  }

  const data = await response.json()
  
  if (data.voices && Array.isArray(data.voices)) {
    return data.voices
  }
  return []
}
