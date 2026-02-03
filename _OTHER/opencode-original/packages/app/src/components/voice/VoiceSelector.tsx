import { createSignal, For, Show } from "solid-js";
import { Button } from "@opencode-ai/ui/button";
import { Icon } from "@opencode-ai/ui/icon";

interface VoiceSelectorProps {
  voices: string[];
  selectedVoice: string;
  onVoiceChange: (voice: string) => void;
  disabled?: boolean;
}

export function VoiceSelector(props: VoiceSelectorProps) {
  const [isOpen, setIsOpen] = createSignal(false);

  return (
    <div class="relative">
      <Button
        onClick={() => setIsOpen(!isOpen())}
        disabled={props.disabled}
        variant="secondary"
        size="small"
      >
        <Icon name="user" class="mr-2" />
        {props.selectedVoice}
        <Icon name="chevron-down" class="ml-2" />
      </Button>
      <Show when={isOpen()}>
        <div class="absolute top-full mt-2 bg-background border rounded-lg shadow-lg z-50 min-w-[200px]">
          <For each={props.voices}>
            {(voice) => (
              <button
                class={`w-full text-left px-4 py-2 hover:bg-muted ${
                  voice === props.selectedVoice ? 'bg-primary/10' : ''
                }`}
                onClick={() => {
                  props.onVoiceChange(voice);
                  setIsOpen(false);
                }}
              >
                {voice}
              </button>
            )}
          </For>
        </div>
      </Show>
    </div>
  );
}
