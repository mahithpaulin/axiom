# axiom-mcp

MCP stdio server: newline-delimited JSON-RPC 2.0 on stdin/stdout exposing
Axiom as agent tools. Std only — no new dependencies.

```sh
cargo run -p axiom-mcp
```

Handshake: `initialize` → `notifications/initialized` → `tools/list` →
`tools/call`. Any MCP-compatible client works (opencode, open-source
agents); the server never guesses — `exhausted`/`unknown` stay
inconclusive, and definite answers report `proof_present` + `verified`.
