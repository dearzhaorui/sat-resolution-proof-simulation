# Experiment Results

This directory contains the experimental outputs of the proof simulation pipeline, organized as two compressed archives.

---

## Directory Structure

```
Experiment-results/
├── Experiment-logs-sat24-unsat-plain-chrono0.tar.xz
├── Example-trimmedProof-branchSeq.tar.xz
└── Plots
└── README.md
```

---

## Archive Contents

### `Experiment-logs-sat24-unsat-plain-chrono0.tar.xz`

Solver execution logs for all 50 benchmark instances, run with flags `--plain --chrono=0`.

Each benchmark instance produces three log files, identified by a content hash prefix and the original `.cnf` filename:

| Suffix | Description |
|---|---|
| `.res-1` | Log of the **original CaDiCaL run** (Step 1): solving the CNF instance and generating the DRAT proof |
| `.resw-1` | Log of the **sequence construction run** (Step 3): analyzing the trimmed proof and writing the branching sequence |
| `.resr-1` | Log of the **simulating solver run** (Step 4): reading the branching sequence and reproducing the proof |

**Example:**
```
fb51311320bb42bdb893249998a77f40-constraints_16_0.3_1.sanitized.cnf.res-1
fb51311320bb42bdb893249998a77f40-constraints_16_0.3_1.sanitized.cnf.resw-1
fb51311320bb42bdb893249998a77f40-constraints_16_0.3_1.sanitized.cnf.resr-1
```

---

### `Example-trimmedProof-branchSeq.tar.xz`

Example output files from the proof simulation pipeline for 5 instances (due to storage limitation).

| Suffix | Description |
|---|---|
| `.core` | Trimmed DRAT proof output by DRAT-trim, containing only the core lemmas necessary for the unsatisfiability proof |
| `.seq` | Branching sequence `σ` constructed from the trimmed proof, used to guide the simulating solver |

**Example:**
```
9cd3acdb765c15163bc239ae3a57f880-FmlaEquivChain_4_6_6.sanitized.cnf.core
9cd3acdb765c15163bc239ae3a57f880-FmlaEquivChain_4_6_6.sanitized.cnf.seq
```

