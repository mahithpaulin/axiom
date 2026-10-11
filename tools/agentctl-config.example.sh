# agentctl configuration example — PLACEHOLDERS ONLY, no secrets here.
#
# Copy to ~/.config/agentctl/config.sh (or export these in your shell) and
# edit the values. Never put API keys or tokens in this file.
#
#   mkdir -p ~/.config/agentctl
#   cp tools/agentctl-config.example.sh ~/.config/agentctl/config.sh
#   # edit config.sh, then:
#   source ~/.config/agentctl/config.sh

# Repository that hosts the supervisor workflow and receives coding tasks.
AGENTCTL_REPO="owner/repo"

# Default Zen model for new tasks. Must be provider/model format.
# Free (zero-retention, limited-time) options include:
#   opencode/space-bunny-free   (default — matches this repo's /oc workflow)
# See https://opencode.ai/docs/zen/#pricing for the current free list.
AGENTCTL_MODEL="opencode/space-bunny-free"

# Bounds for new tasks submitted without explicit flags.
AGENTCTL_MAX_ITERS=3      # implementation iterations per worker attempt (1-5)
AGENTCTL_MAX_ATTEMPTS=2   # worker attempts incl. retries (1-3)
