import { For, Show } from "solid-js";
import { type Maybe, isJust, fromMaybe } from "@/utils/maybe";

export interface TranscriptMessage {
  id: string;
  role: 'user' | 'assistant';
  text: string;
  timestamp: Date;
  audioUrl: Maybe<string>;
}

interface TranscriptViewProps {
  messages: TranscriptMessage[];
}

export function TranscriptView(props: TranscriptViewProps) {
  return (
    <div class="flex flex-col gap-4 p-4 h-full overflow-y-auto">
      <Show
        when={props.messages.length > 0}
        fallback={
          <div class="text-center text-muted-foreground py-8">
            No messages yet. Start speaking to begin the conversation.
          </div>
        }
      >
        <For each={props.messages}>
          {(message) => (
            <div
              class={`flex gap-3 ${
                message.role === 'user' ? 'justify-end' : 'justify-start'
              }`}
            >
              <div
                class={`max-w-[80%] rounded-lg p-3 ${
                  message.role === 'user'
                    ? 'bg-primary text-primary-foreground'
                    : 'bg-muted'
                }`}
              >
                <div class="text-sm font-medium mb-1">
                  {message.role === 'user' ? 'You' : 'Assistant'}
                </div>
                <div class="text-sm whitespace-pre-wrap">{message.text}</div>
                <Show when={isJust(message.audioUrl)}>
                  <audio
                    src={fromMaybe(message.audioUrl, '')}
                    controls
                    class="mt-2 w-full"
                  />
                </Show>
              </div>
            </div>
          )}
        </For>
      </Show>
    </div>
  );
}
