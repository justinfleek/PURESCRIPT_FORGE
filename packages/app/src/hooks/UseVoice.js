// FFI for UseVoice.purs
export const getUserMedia = (constraints) => () =>
  new Promise((resolve) => {
    navigator.mediaDevices.getUserMedia(constraints)
      .then(stream => resolve({ tag: "Right", value: stream }))
      .catch(err => resolve({ tag: "Left", value: err.message }));
  });

export const createMediaRecorder = (stream) => (mimeType) => () =>
  new MediaRecorder(stream, { mimeType });

export const startMediaRecorder = (recorder) => () => recorder.start();
export const stopMediaRecorder = (recorder) => () => recorder.stop();

export const setOnDataAvailable = (recorder) => (handler) => () => {
  recorder.ondataavailable = (event) => {
    if (event.data.size > 0) handler(event.data)();
  };
};

export const setOnStop = (recorder) => (handler) => () => {
  recorder.onstop = () => handler();
};

export const stopAllTracks = (stream) => () =>
  stream.getTracks().forEach(track => track.stop());

export const createBlob = (chunks) => (type) =>
  new Blob(chunks, { type });

export const transcribeAudio = (audioBlob) => (language) => () =>
  new Promise(async (resolve) => {
    const endpoint = localStorage.getItem("forge-voice-endpoint");
    if (!endpoint) {
      // Fallback to Web Speech API
      resolve({ tag: "Left", value: "No whisper endpoint configured" });
      return;
    }
    
    try {
      const formData = new FormData();
      formData.append("file", audioBlob, "audio.webm");
      formData.append("model", "whisper-1");
      formData.append("language", language);
      
      const response = await fetch(`${endpoint}/v1/audio/transcriptions`, {
        method: "POST",
        body: formData,
      });
      
      if (!response.ok) {
        resolve({ tag: "Left", value: `Transcription failed: ${response.statusText}` });
        return;
      }
      
      const result = await response.json();
      resolve({ tag: "Right", value: result.text || "" });
    } catch (err) {
      resolve({ tag: "Left", value: err.message });
    }
  });

export const speakWithBrowserTTS = (text) => () =>
  new Promise((resolve, reject) => {
    if (!("speechSynthesis" in window)) {
      reject(new Error("Speech synthesis not supported"));
      return;
    }
    const utterance = new SpeechSynthesisUtterance(text);
    utterance.onend = () => resolve();
    utterance.onerror = () => reject(new Error("Speech synthesis failed"));
    window.speechSynthesis.speak(utterance);
  });

export const speakWithAPI = (endpoint) => (text) => (voice) => () =>
  new Promise(async (resolve, reject) => {
    try {
      const response = await fetch(`${endpoint}/v1/audio/speech`, {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify({ model: "tts-1", input: text, voice }),
      });
      
      if (!response.ok) {
        reject(new Error(`TTS failed: ${response.statusText}`));
        return;
      }
      
      const audioBlob = await response.blob();
      const audioUrl = URL.createObjectURL(audioBlob);
      const audio = new Audio(audioUrl);
      
      audio.onended = () => {
        URL.revokeObjectURL(audioUrl);
        resolve();
      };
      audio.onerror = () => {
        URL.revokeObjectURL(audioUrl);
        reject(new Error("Audio playback failed"));
      };
      audio.play();
    } catch (err) {
      reject(err);
    }
  });
