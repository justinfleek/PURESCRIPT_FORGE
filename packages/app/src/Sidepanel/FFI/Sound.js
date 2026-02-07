// | Sound FFI - Alert Sound Effects
// | Provides sound playback for alert notifications
"use strict";

// | Play alert sound
exports.playAlertSound = function() {
  return function() {
    // Create audio context and play alert sound
    // In a full implementation, would load and play a sound file
    // For now, use Web Audio API beep
    try {
      const audioContext = new (window.AudioContext || window.webkitAudioContext)();
      const oscillator = audioContext.createOscillator();
      const gainNode = audioContext.createGain();
      
      oscillator.connect(gainNode);
      gainNode.connect(audioContext.destination);
      
      oscillator.frequency.value = 800; // 800 Hz beep
      oscillator.type = "sine";
      
      gainNode.gain.setValueAtTime(0.3, audioContext.currentTime);
      gainNode.gain.exponentialRampToValueAtTime(0.01, audioContext.currentTime + 0.2);
      
      oscillator.start(audioContext.currentTime);
      oscillator.stop(audioContext.currentTime + 0.2);
    } catch (e) {
      // Silently fail if audio not supported
    }
  };
};
