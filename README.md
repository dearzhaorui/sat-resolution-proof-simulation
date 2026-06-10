
An Empirical Look at the Equivalence between Resolution and CDCL
===============================================================================
This repository contains all sources used in the paper "An Empirical Look at the Equivalence between Resolution and CDCL".

SAT solvers continue to surprise users with their power and versatility, despite decades of intensive use across a wide range of industrial applications since the early 2000s. Yet a satisfactory theoretical explanation for their behavior remains one of the holy grails of research in this area. Notably, SAT solvers can simultaneously search for a solution and construct a resolution proof of unsatisfiability.

A landmark result [1, 2] establishes that CDCL-based SAT solvers can simulate any resolution proof. Specifically, given a resolution proof, one can construct a sequence of decision literals and restarts that guides the solver to find this proof — or one that is at most polynomially longer in the worst case.

The goal of this work is to deepen our understanding of CDCL-based SAT solvers by empirically analyzing how they simulate a given resolution proof of unsatisfiability. To this end, we use the modern SAT solver [CaDiCaL](https://github.com/arminbiere/cadical) v2.0.0 throughout our experiments.

The experiments have been done in a cluster with 10 nodes of type Dell PowerEdge R240 with Intel Xeon E-2124. Every solver on a node is set to have 4 cores and 15GB of memory available. The time limit is 3600 seconds.


# Prerequisites

- [DRAT-trim](https://github.com/marijnheule/drat-trim) v05.22.2023 — proof checker

```bash
git clone https://github.com/marijnheule/drat-trim
make .
mv drat-trim ..
```


# Repository Structure

| Directory / File | Description |
|---|---|
| `proof-simulation-write-sequence` | Modified CaDiCaL solver for constructing a branching sequence `σ` from a trimmed DRAT proof |
| `proof-simulation-read-sequence` | Solver that operates in two modes: **(1)** original CaDiCaL to generate a DRAT proof, or **(2)** simulating solver that reads a sequence `σ` to reproduce the proof |
| `Benchmarks_SAT24_B50` | Benchmark instances |
| `Experiment-results` | Output logs for all instances + 5 example trimmed proofs and branching sequences |
| `Summary-data-proof-simulation.ods` | Summary data spreadsheet |


# Build and Run

The proof simulation pipeline consists of four ordered steps.

---

## Step 1 — Generate a Resolution Proof (original CaDiCaL)

> **Flags**
> - `--rs=0` — Run the original CaDiCaL solver
> - `--rs=1` — Read a branching sequence from an external file (default)

**1). Generate an unsatisfiability proof `proof.txt` using the original CaDiCaL:**

```bash
cd proof-simulation-read-sequence
./configure
./build/cadical --plain --chrono=0 --inprocessing=false --walk=false --rs=0 \
    cnf/add16.cnf proof.txt
```

---

## Step 2 — Verify and trim the proof; output core lemmas to `trimmed_proof.txt`

```bash
../drat-trim cnf/add16.cnf proof.txt -l trimmed_proof.txt
```

---

## Step 3 — Construct a Branching Sequence (modified CaDiCaL)

**3). Analyze the core lemmas and write the sequence to `sequence.txt`:**

```bash
cd proof-simulation-write-sequence
./configure
./build/cadical --plain --chrono=0 --inprocessing=false --walk=false \
    -core ../proof-simulation-read-sequence/trimmed_proof.txt \
    -sequence sequence.txt \
    cnf/add16.cnf proof.txt
```

**4). Verify the proof:**

```bash
../drat-trim cnf/add16.cnf proof.txt
```

---

## Step 4 — Read a Branching Sequence (simulating solver)

> **Flags**
> - `--rs=0` — Run the original CaDiCaL solver
> - `--rs=1` — Read a branching sequence from an external file (default)

**5). Read `sequence.txt` and generate the simulated proof `simulated_proof.txt`:**

```bash
./build/cadical --plain --chrono=0 --inprocessing=false --walk=false --rs=1 \
    -sequence ../proof-simulation-write-sequence/sequence.txt \
    cnf/add16.cnf simulated_proof.txt
```

**6). Verify the proof:**

```bash
./drat-trim cnf/add16.cnf simulated_proof.txt
```

---

# References

- [1] Albert Atserias, Johannes Klaus Fichte, and Marc Thurley. Clause-learning algorithms with many restarts and bounded-width resolution. *J. Artif. Intell. Res.*, 40:353–373, 2011.
- [2] Knot Pipatsrisawat and Adnan Darwiche. On the power of clause-learning SAT solvers as resolution engines. *Artif. Intell.*, 175(2):512–525, 2011.
