#!/usr/bin/env python3
import csv
import sys
import matplotlib.pyplot as plt

BIN_SIZE = 1000

path = sys.argv[1] if len(sys.argv) > 1 else "timing.csv"

steps, op_ms, gt_ms, srv_us, polls = [], [], [], [], []
with open(path) as f:
    for row in csv.DictReader(f):
        steps.append(int(row["step"]))
        op_ms.append(int(row["op_ms"]))
        gt_ms.append(int(row["ground_truth_ms"]))
        srv_us.append(int(row["server_us"]))
        polls.append(int(row["polls"]))

def bin_mean(data):
    bins = []
    for i in range(0, len(data), BIN_SIZE):
        chunk = data[i : i + BIN_SIZE]
        bins.append(sum(chunk) / len(chunk))
    return bins

bin_steps = [steps[i] for i in range(0, len(steps), BIN_SIZE)]
bin_op = bin_mean(op_ms)
bin_gt = bin_mean(gt_ms)
bin_srv = bin_mean(srv_us)
bin_polls = bin_mean(polls)

fig, axes = plt.subplots(4, 1, sharex=True, figsize=(12, 10))

axes[0].plot(bin_steps, bin_op, linewidth=0.8)
axes[0].set_ylabel("op (ms)")
axes[0].set_title(f"Fuzzer step timing (binned per {BIN_SIZE} steps)")

axes[1].plot(bin_steps, bin_gt, linewidth=0.8, color="tab:orange")
axes[1].set_ylabel("ground truth (ms)")

axes[2].plot(bin_steps, bin_srv, linewidth=0.8, color="tab:green")
axes[2].set_ylabel("server (µs)")

axes[3].plot(bin_steps, bin_polls, linewidth=0.8, color="tab:red")
axes[3].set_ylabel("polls")
axes[3].set_xlabel("step")

plt.tight_layout()
plt.savefig("timing.png", dpi=150)
print(f"Saved timing.png ({len(steps)} steps, {len(bin_steps)} bins)")
