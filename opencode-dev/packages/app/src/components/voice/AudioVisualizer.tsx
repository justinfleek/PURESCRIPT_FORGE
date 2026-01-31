import { createEffect, createSignal, onCleanup } from "solid-js";
import { type Maybe, just, none, isJust } from "@/utils/maybe";

interface AudioVisualizerProps {
  audioLevel: number; // 0-1
  isActive: boolean;
}

export function AudioVisualizer(props: AudioVisualizerProps) {
  const [displayLevel, setDisplayLevel] = createSignal(0);
  let animationFrameId: Maybe<number> = none();

  createEffect(() => {
    if (props.isActive) {
      const update = () => {
        // Smooth the audio level for visualization
        setDisplayLevel(prev => {
          const target = props.audioLevel;
          return prev + (target - prev) * 0.3;
        });
        animationFrameId = just(requestAnimationFrame(update));
      };
      update();
    } else {
      setDisplayLevel(0);
      if (isJust(animationFrameId)) {
        cancelAnimationFrame(animationFrameId.value);
        animationFrameId = none();
      }
    }
  });

  onCleanup(() => {
    if (isJust(animationFrameId)) {
      cancelAnimationFrame(animationFrameId.value);
    }
  });

  return (
    <div class="flex items-center justify-center w-32 h-32">
      <div
        class="rounded-full bg-gradient-to-r from-blue-500 to-purple-500 transition-all duration-100"
        style={{
          width: `${32 + displayLevel() * 64}px`,
          height: `${32 + displayLevel() * 64}px`,
          opacity: props.isActive ? 0.6 + displayLevel() * 0.4 : 0.2,
        }}
      />
    </div>
  );
}
