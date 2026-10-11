#!/usr/bin/env python3
"""Upload a video to YouTube via Data API v3.

Secrets come from env only (never committed):
  YOUTUBE_CLIENT_ID, YOUTUBE_CLIENT_SECRET, YOUTUBE_REFRESH_TOKEN

Usage:
  python3 upload.py --file out.mp4 --title "t" --privacyStatus private
"""
import argparse
import os
import sys

SCOPES = ["https://www.googleapis.com/auth/youtube.upload"]


def get_service():
    from google.oauth2.credentials import Credentials
    from google.auth.transport.requests import Request
    from googleapiclient.discovery import build

    cid = os.environ.get("YOUTUBE_CLIENT_ID", "")
    csec = os.environ.get("YOUTUBE_CLIENT_SECRET", "")
    rtok = os.environ.get("YOUTUBE_REFRESH_TOKEN", "")
    if not (cid and csec and rtok):
        sys.exit("missing env: need YOUTUBE_CLIENT_ID/SECRET/REFRESH_TOKEN")
    creds = Credentials(
        token=None,
        refresh_token=rtok,
        token_uri="https://oauth2.googleapis.com/token",
        client_id=cid,
        client_secret=csec,
        scopes=SCOPES,
    )
    creds.refresh(Request())
    return build("youtube", "v3", credentials=creds)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--file", required=True)
    ap.add_argument("--title", default="axiom example upload")
    ap.add_argument("--description", default="Uploaded from CI (private test).")
    ap.add_argument("--privacyStatus", default="private",
                    choices=["private", "unlisted", "public"])
    ap.add_argument("--category", default="22")
    a = ap.parse_args()
    if not os.path.exists(a.file):
        sys.exit("no such file: " + a.file)

    from googleapiclient.http import MediaFileUpload
    from googleapiclient.errors import HttpError

    yt = get_service()
    body = {
        "snippet": {"title": a.title, "description": a.description,
                    "categoryId": a.category},
        "status": {"privacyStatus": a.privacyStatus},
    }
    try:
        req = yt.videos().insert(
            part="snippet,status", body=body,
            media_body=MediaFileUpload(a.file, resumable=True))
        resp = None
        while resp is None:
            _, resp = req.next_chunk()
        vid = resp["id"]
        print("VIDEO_ID=" + vid)
        try:
            v = yt.videos().list(id=vid, part="id,snippet,status").execute()
            items = v.get("items", [])
            st = items[0]["status"]["privacyStatus"] if items else "?"
            print("VERIFY privacyStatus=" + st)
        except HttpError as e:
            # youtube.upload scope allows insert but not list; insert
            # success above is the real proof. Check Studio manually.
            print("VERIFY skipped (upload scope cannot list): %s" % e)
    except HttpError as e:
        sys.exit("upload failed: %s" % e)


if __name__ == "__main__":
    main()
