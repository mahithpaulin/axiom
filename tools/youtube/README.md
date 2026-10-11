# YouTube publish — CI-only (no box, phone-safe)

Public repo Actions minutes do the render+upload. Box stays stopped.

## Auth (done 2026-10-11, do not redo unless rotating)
- Google Cloud project `youtube-uploader`, YouTube Data API v3 enabled.
- OAuth Desktop client + consent in Testing mode, test user = channel Gmail.
- Phone localhost flow: `~/bin/youtube-auth` serves 127.0.0.1:8090,
  approve in Chrome on the same phone, server auto-captures code.
- Local files (600, never committed): `~/.config/youtube/client_secrets.json`,
  `~/.config/youtube/token.json`.
- Actions secrets (values in GitHub only): `YOUTUBE_CLIENT_ID`,
  `YOUTUBE_CLIENT_SECRET`, `YOUTUBE_REFRESH_TOKEN`.

## Use
```bash
gh workflow run youtube-publish.yml --ref youtube-publish \
  -f title="axiom example upload" -f privacy=private
gh run watch --repo mahithpaulin/axiom
```
Log prints `VIDEO_ID=<id>` + `VERIFY privacyStatus=private`.

## Limits
- Unverified API project: uploads stay `private` until YouTube audits it.
- Quota ~100 uploads/day. Personal non-commercial use only.
- Runners: CPU ffmpeg only, 6h cap. GPU/heavy AI stays on Kaggle T4.
