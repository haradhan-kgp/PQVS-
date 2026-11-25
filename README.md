# PQVS reference implementation and symbolic models

Companion code for the paper *PQVS: Post-Quantum Verifiable Secret Sharing Beyond Thresholds*.

## Contents
| Path | Description |
|---|---|
| `pqvs.c` | C reference implementation (short-LSSS compiler, SIS commitment, Share / SlotCom / VerifyShare / Reconstruct), validation tests, cost and parameter reporting |
| `Makefile` | `make test`, `make bench`, `make plan` |
| `proverif/` | ProVerif models: hand-written 2-of-3 (`decl.pv`, `honest.pv`, `consistency.pv`, `run.sh`) and a generator for any t-of-n DNF (`gen_pv.py`, `run_gen.sh`) |
| `results/` | Recorded outputs of the tests, benchmark and ProVerif runs reported in the paper |

## C implementation
Requires GCC (uses `unsigned __int128`) and Linux, macOS or WSL (or Docker: `docker run --rm -v "$PWD":/work -w /work gcc:latest make test`).
```
make
./pqvs validate                      # exhaustive algebra checks and attack tests (expect: ALL VALIDATION CHECKS PASSED)
./pqvs bench t n lam_s qbits m k     # e.g. ./pqvs bench 3 5 16 62 512 11
./pqvs plan  t n lam_s qbits m       # closed-form sizes/costs for any q size, e.g. ./pqvs plan 5 10 40 100 4096
```
**Limitations.** Non-cryptographic RNG, not constant time, `q < 2^62`. `validate` uses toy parameters
(it checks the algebra, not security). The SIS estimate printed by `bench`/`plan` is a crude core-SVP heuristic;
confirm any parameter set with the lattice-estimator. Parameters that satisfy (K1)-(K3) are not necessarily secure.
Timings in `results/` are from one machine.

## ProVerif models
Requires ProVerif >= 2.04.
```
cd proverif
./run.sh                 # hand-written 2-of-3 models
./run_gen.sh 2 3         # generated models for t-of-n (also: 3 5, and 5 10 with a long timeout, e.g. ./run_gen.sh 5 10 3600)
```
Properties checked: secrecy against t-1 corrupted parties (and leakage for t, as a sanity check), diff-equivalence of two
secrets for t-1 corrupted parties, soundness of reconstruction with an honest dealer, and consistency of all authorized sets
with a malicious dealer. For the earlier design with independent per-slot commitments the consistency query
cannot be proved (an attack is found). Expected outputs: `results/proverif_results.txt`.

The model is symbolic: commitments are perfectly hiding and binding free constructors, linearity is an equational theory.
Statistical hiding, SIS binding and shortness bounds are not modelled; they are covered by the reductions in the paper.
Models were checked for 2-of-3, 3-of-5 and 5-of-10 (minimal-set DNF). The mixed formula with repeated parties is covered
by the C validation only.

## License
Add a license before publishing (e.g. MIT or Apache-2.0).
