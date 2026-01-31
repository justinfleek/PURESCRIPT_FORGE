import { Show } from "solid-js";
import { Button } from "@opencode-ai/ui/button";
import { Icon } from "@opencode-ai/ui/icon";

interface MicrophoneButtonProps {
  isListening: boolean;
  isProcessing: boolean;
  audioLevel?: number; // 0-1 for visualization
  onStart: () => void;
  onStop: () => void;
  disabled?: boolean;
}

export function MicrophoneButton(props: MicrophoneButtonProps) {
  const handleClick = () => {
    if (props.isListening) {
      props.onStop();
    } else {
      props.onStart();
    }
  };

  return (
    <Button
      onClick={handleClick}
      disabled={props.disabled || props.isProcessing}
      class="relative"
      variant={props.isListening ? "destructive" : "default"}
      size="lg"
    >
      <Show
        when={props.isListening}
        fallback={<Icon name="mic" />}
      >
        <Icon name="mic-off" />
      </Show>
      <Show when={props.isListening && (props.audioLevel > 0)}>
        <div
          class="absolute inset-0 rounded-full bg-red-500/20 animate-pulse"
          style={{
            transform: `scale(${1 + props.audioLevel * 0.5})`,
            transition: "transform 0.1s",
          }}
        />
      </Show>
    </Button>
  );
}
