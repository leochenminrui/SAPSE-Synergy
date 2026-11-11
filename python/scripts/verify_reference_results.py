#!/usr/bin/env python3
"""Check the supplied benchmark records, without rerunning Coq or model inference."""

import csv
import hashlib
import json
from collections import Counter, defaultdict
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
EXPECTED = {
    "Baseline-RAG": {"Verified": 752, "Failed": 1248},
    "SAPSE-Strict": {"Verified": 746, "Failed": 1148, "Abstained": 106},
    "SAPSE-Fast": {"Verified": 656, "Failed": 1344},
    "SAPSE-Synergy": {"Verified": 656, "Failed": 1343, "Abstained": 1},
}


def require(condition, message):
    if not condition:
        raise SystemExit(f"Reference check failed: {message}")


def read_csv(path):
    with path.open(newline="", encoding="utf-8") as handle:
        return list(csv.DictReader(handle))


def main():
    # Verify the exact scientific inputs and saved outputs before comparing counts.
    for manifest_name in ("data/SHA256SUMS", "outputs/SHA256SUMS"):
        for line in (ROOT / manifest_name).read_text().splitlines():
            digest, name = line.split("  ", 1)
            path = ROOT / name
            require(path.is_file(), f"missing {name}")
            require(hashlib.sha256(path.read_bytes()).hexdigest() == digest,
                    f"checksum mismatch for {name}")

    items = [json.loads(line) for line in
             (ROOT / "data/input/synergy_rag_2k.jsonl").read_text().splitlines()]
    ids = {item["id"] for item in items}
    require(len(items) == len(ids) == 2000, "expected 2,000 distinct draft IDs")
    require(all(isinstance(item.get("draft"), str) for item in items),
            "each input must contain a draft string")

    rows = read_csv(ROOT / "outputs/full_results_seed5.csv")
    require(len(rows) == 8000, "expected 8,000 combined outcomes")
    grouped = defaultdict(list)
    for row in rows:
        grouped[row["config_name"]].append(row)
        require(row["status"] in {"Verified", "Failed", "Abstained"}, "unknown status")
        require(float(row["time_ms"]) >= 0, "negative runtime")
        require(int(row["urc_flag"]) in {0, 1}, "invalid URC flag")
    require(set(grouped) == set(EXPECTED), "expected exactly four modes")
    statuses = {}
    for mode, expected in EXPECTED.items():
        mode_rows = grouped[mode]
        require(len(mode_rows) == 2000, f"wrong row count for {mode}")
        require({r["item_id"] for r in mode_rows} == ids, f"ID mismatch for {mode}")
        require(Counter(r["status"] for r in mode_rows) == Counter(expected),
                f"status mismatch for {mode}")
        statuses[mode] = {r["item_id"]: r["status"] for r in mode_rows}
    for mode in ("SAPSE-Strict", "SAPSE-Synergy"):
        require(sum(int(r["urc_flag"]) for r in grouped[mode]) == 0,
                f"nonzero guarded-repair URC for {mode}")

    lost = {i for i in ids if statuses["Baseline-RAG"][i] == "Verified"
            and statuses["SAPSE-Synergy"][i] != "Verified"}
    require(len(lost) == 96, "expected 96 lost successes")
    require(all(statuses["SAPSE-Fast"][i] == statuses["SAPSE-Synergy"][i]
                == "Failed" for i in lost), "lost-success status mismatch")
    saved_lost = read_csv(ROOT / "outputs/analysis/lost_successes.csv")
    require(len(saved_lost) == 96 and {r["lemma_id"] for r in saved_lost} == lost,
            "lost-success table must contain the same 96 IDs")
    joint = read_csv(ROOT / "outputs/analysis/joint_results_2k.csv")
    require(len(joint) == 2000 and {r["lemma_id"] for r in joint} == ids,
            "joint table must contain the same 2,000 IDs")
    for mode, field in (("Baseline-RAG", "baseline_status"),
                        ("SAPSE-Strict", "strict_status"),
                        ("SAPSE-Fast", "fast_status"),
                        ("SAPSE-Synergy", "synergy_status")):
        require(all(r[field] == statuses[mode][r["lemma_id"]] for r in joint),
                f"joint-table outcomes disagree for {mode}")
    require(sum(r["in_frag_synergy"] == "True" for r in joint) == 1962,
            "saved per-lemma fragment flags disagree with the summary")
    require(all(r["in_frag_synergy"] == "True" for r in joint
                if r["synergy_status"] == "Verified"),
            "a saved Synergy success lies outside the recorded fragment")
    fragment = read_csv(ROOT / "outputs/analysis/fragment_coverage_summary.csv")
    require(len(fragment) == 1, "expected one saved fragment summary")
    fragment = fragment[0]
    require((int(fragment["num_lemmas"]), int(fragment["in_frag_count"]),
             int(fragment["synergy_verified_in_frag"]),
             int(fragment["synergy_verified_out_frag"])) == (2000, 1962, 656, 0),
            "saved fragment summary mismatch")
    require(float(fragment["in_frag_ratio"]) == 0.981, "fragment ratio mismatch")
    print(json.dumps({
        "check": "saved benchmark records and SHA-256 integrity",
        "drafts": len(ids), "outcome_rows": len(rows),
        "status_counts": EXPECTED, "lost_successes": len(lost),
        "saved_fragment_summary": fragment,
    }, indent=2))


if __name__ == "__main__":
    main()
