# axiom-tui

Chat TUI that talks to **any** OpenAI-compatible or Anthropic-native agent,
with Axiom running locally as the reasoning tool.

```sh
cargo run -p axiom-tui -- --provider openai    # needs OPENAI_API_KEY
cargo run -p axiom-tui -- --provider anthropic # needs ANTHROPIC_API_KEY
```

Env:

| Var | Meaning | Default |
|---|---|---|
| `OPENAI_BASE_URL` | OpenAI-compatible base URL (Ollama, LM-Studio, vLLM, OpenRouter all work) | `https://api.openai.com/v1` |
| `OPENAI_API_KEY` | Bearer key for the OpenAI-compatible endpoint | (empty = local servers) |
| `OPENAI_MODEL` | Model name | `gpt-4o-mini` |
| `ANTHROPIC_API_KEY` | Anthropic key | — |
| `ANTHROPIC_MODEL` | Anthropic model | `claude-haiku-4-5` |
| `AXIOM_MAX_STEPS` | Default step budget per tool call | `1000000` |

Keys: `Enter` send · `Tab` switch provider · `Esc`/`Ctrl-C` quit.
Axiom verdicts render with their honest `Status`: `exhausted`/`unknown`
never look like answers.
