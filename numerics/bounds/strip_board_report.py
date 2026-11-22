#!/usr/bin/env python3
"""strip_board_report.py — 条带员看板报数（thomson-workflow/board/board.jsonl 追加）。"""
import json
import sys
from datetime import datetime, timedelta, timezone
from pathlib import Path

BOARD = Path(__file__).resolve().parents[2].parent / "thomson-workflow" / "board" / "board.jsonl"


def report(subject: str, body: str, artifacts=None, type_="result", to="orchestrator,all"):
    ts = datetime.now(timezone(timedelta(hours=8))).isoformat(timespec="seconds")
    entry = dict(ts=ts, _from="strip-worker", to=to, type=type_,
                 subject=subject, body=body, artifacts=artifacts or [])
    line = json.dumps({"ts": entry["ts"], "from": entry["_from"], "to": entry["to"],
                       "type": entry["type"], "subject": entry["subject"],
                       "body": entry["body"], "artifacts": entry["artifacts"]},
                      ensure_ascii=False)
    BOARD.parent.mkdir(parents=True, exist_ok=True)
    with open(BOARD, "a") as f:
        f.write(line + "\n")
    print(f"[board] {subject}")


if __name__ == "__main__":
    report(sys.argv[1], sys.argv[2], sys.argv[3:])
