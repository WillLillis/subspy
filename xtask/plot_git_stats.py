#!/usr/bin/env python3
import csv
import sys
import matplotlib.pyplot as plt

path = sys.argv[1] if len(sys.argv) > 1 else "git_stats.csv"

steps, refs, packs, pack_kb, loose = [], [], [], [], []
with open(path) as f:
    for row in csv.DictReader(f):
        steps.append(int(row["step"]))
        refs.append(int(row["refs"]))
        packs.append(int(row["packs"]))
        pack_kb.append(int(row["pack_kb"]))
        loose.append(int(row["loose"]))

fig, axes = plt.subplots(4, 1, sharex=True, figsize=(12, 10))

axes[0].plot(steps, refs, marker=".", markersize=3)
axes[0].set_ylabel("refs")
axes[0].set_title("Git repository stats (sampled at repack intervals)")

axes[1].plot(steps, packs, marker=".", markersize=3, color="tab:orange")
axes[1].set_ylabel("pack files")

axes[2].plot(steps, pack_kb, marker=".", markersize=3, color="tab:green")
axes[2].set_ylabel("pack size (KB)")

axes[3].plot(steps, loose, marker=".", markersize=3, color="tab:red")
axes[3].set_ylabel("loose objects")
axes[3].set_xlabel("step")

plt.tight_layout()
plt.savefig("git_stats.png", dpi=150)
print(f"Saved git_stats.png ({len(steps)} samples)")
