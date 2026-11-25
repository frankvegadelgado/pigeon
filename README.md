# PigeonGoldbach: nested squares and distinct-prime Goldbach partitions

Lean 4 formalization for *Nested Squares and Distinct-Prime Goldbach Partitions* (`doc/paper.tex`). `formalization.yaml` is the machine-readable inventory; this file explains it.

## Main result

For `N ≥ 4` the following are equivalent (Theorem `thm:geometric`, Lean theorem `geometric_equivalence`):

1. `2N` is the sum of two distinct primes;
2. there is `M ∈ [1, N - 3]` with `N - M` and `N + M` both prime;
3. there is `M ∈ [1, N - 3]` such that the L-shaped area `N² - M²` between nested squares of side lengths `N` and `M` is a semiprime.

The paper does not prove the distinct-prime Goldbach conjecture. The Lean development covers the elementary statements of the paper and states which analytic results it does not touch.

## Repository layout

| Path | Content |
| --- | --- |
| `doc/paper.tex` | The manuscript. |
| `doc/formalization.md` | What Lean proves and what it does not. |
| `formalization.yaml` | Module inventory with status. |
| `PigeonGoldbach/Core.lean` | The elementary statements of the paper. |
| `PigeonGoldbach/CitedResults.lean` | Cited published results as hypotheses, and the theorems proved from them. |
| `PigeonGoldbach/Preprints.lean` | Hypotheses from recent preprints and the theorems proved from them. |
| `PigeonGoldbach/Extended.lean` | The case `M = 0`. |
| `PigeonGoldbach/Centered.lean` | The centered statistic `H_R` and `J_R`. |
| `Challenge.lean`, `Solution.lean` | Standalone challenge (imports only Mathlib) and its solution, compared by `lake comparator`. |
| `comparator.json` | The compared theorems, in the namespace `PigeonGoldbach.Public`. |
| `scripts/` | `check-lean-sources.py`, `verify-comparator.sh`. |

## Lean theorems

The theorems are in `PigeonGoldbach/Core.lean` unless the module is named; the sets are `A N = [1, N - 3]`, `C N`, `D N`, `E N`, `B N`.

| Theorem | Paper |
| --- | --- |
| `geometric_equivalence` | Theorem `thm:geometric` |
| `centered_intersection_criterion` | Proposition `prop:intersection` |
| `CD_subset_E`, `CED_eq_CD` | Lemma `lem:CD-in-E` |
| `C_D_subset_B` | Section `subsec:setintersection` (parity class) |
| `gap_lower`, `gap_lower_missing` | Lemma `lem:gap` |
| `gap_top`, `gap_top_missing` | Lemma `lem:gap-top` |
| `pigeonhole_CE` | Proposition `prop:pigeonhole-CE` (combinatorial step) |
| `card_C` | `\|C_N\|` equals the number of primes `3 ≤ P ≤ N - 1` |
| `card_E_ge` | Corollary `cor:half-difference-baseline` (combinatorial step) |
| `mem_E_shift` | Corollary `cor:goldbach-diff` (shift form) |
| `H_pos_iff`, `pigeonhole_CE_of_H` | Section `subsec:gaps-H`, Proposition `prop:pigeonhole-CE` (with `H`) |
| `card_C_le_CE_add`, `card_CE_le` | Corollary `cor:goldbach-diff` (counting step) |
| `mem_E_of_pair` | Section `subsec:upper-prime-count` |
| `card_E_ge_Ioo` | Corollary `cor:half-difference-baseline` |
| `gap_card_missing`, `gap_card_consecutive`, `cramer_bound` | Theorem `thm:cramer`, Corollary `cor:long-gaps` (finite form) |
| `cs_count`, `T_ge_pairs`, `card_lt_pairs`, `V_le_quad`, `positive_proportion_of_bounds` | Theorem `thm:positive-proportion` (combinatorial part; not the value `X/2382`) |
| `gExp_*`, `exceptional_half`, `exceptional_half_of_HL`, `exceptional_seven_twelfths`, `cnt_add_distinctExceptional`, `cnt_lower_of_exceptional`, `classical_iff_distinct_of_not_prime`, `card_distinctExceptional_le`, `two_mul_R_le_G`, `R_upper_of_goldbach_upper`, `linnik_six` (module `PigeonGoldbach/Preprints.lean`) | Propositions `prop:E-half`, `prop:E-distinct`, `prop:R-upper`, Corollary `cor:cnt-GRH`, Section `subsec:recent`: Pintz–Althöfer, Bhowmik–Grimmelt, Lichtman / Johnston–Trudgian, Alpöge (hypotheses) |
| `piCount`, `card_oddPrimes_add_one`, `T_lower_of_RS`, `positive_proportion_of_cited`, `verified_range` (module `PigeonGoldbach/CitedResults.lean`) | Theorem `thm:positive-proportion` and Proposition `prop:verified` from the cited results, stated as hypotheses (Siebert's bound `prop:siebert`, Dusart, Rosser–Schoenfeld) |
| `zero_case` | Open question on `M = 0` |
| `zero_mem_CDext_iff`, `zero_mem_Eext_iff`, `Rext_eq`, `classical_iff_Rext` (module `PigeonGoldbach/Extended.lean`) | Proposition `prop:M-zero` |
| `card_oddPrimes_le`, `R_le_half`, `log_sq_lt`, `HR_neg_of_ge_64` (module `PigeonGoldbach/Centered.lean`) | Proposition `prop:HR-negative` for `N ≥ 64` |
| `JR_pos_iff`, `JR_const`, `F_gt_of_JR_pos`, `JR_Fc_pos_of_HL`, `R_pos_of_JR_Fc_pos` (module `PigeonGoldbach/Centered.lean`) | Corollary `cor:JR` |
| `sixPowerRep_of_verification`, `sixPowerRep_outside_gap`, `sixPowerRep_complete`, `sixPowerRep_equal_powers` (module `PigeonGoldbach/Preprints.lean`) | Proposition `prop:six-powers`; `prop:six-powers-ext` up to `8·10¹⁸ - 4` |
| `CD_iff_centered_witness`, `card_CD_le_primes` | Pathways: straddling versus centered pairs; `R(2N) ≤ |C_N|` |
| `classical_iff_distinct`, `distinct_goldbach_iff_tail` | Pathways: reduction to the centered tail and the case `M = 0` |
| `centered_of_partition` | Proposition `prop:verified` (step from a partition with `p < N`) |
| `small_cases` | Section `subsec:small` (`4 ≤ N ≤ 12`) |

## Not formalized in Lean

- Mikawa's theorem (Proposition `prop:mikawa`) and Proposition `prop:almost-all`, Corollary `cor:goldbach-diff` in its asymptotic form.
- Siebert's sieve bound, Lemmas `lem:energy` and `lem:energy-bound`, Theorem `thm:linear` and the explicit bounds of Theorem `thm:positive-proportion`.
- The explicit estimates with logarithms and the prime-counting bounds of Dusart and Rosser–Schoenfeld: Lemma `lem:elementary`, Proposition `prop:many-upper`, and Proposition `prop:HR-negative` for `34 ≤ N ≤ 63` (`N ≥ 64` is formalized in `PigeonGoldbach/Centered.lean`), Corollary `cor:long-gaps` in its asymptotic form.
- The verification of the even Goldbach conjecture up to `4·10¹⁸` and the computations of the paper, including Propositions `prop:centering-data` and `prop:third-data`, which restate the computed tables.

## Toolchain

Lean `v4.35.0-rc2` with Mathlib tag `v4.35.0-rc2` (`lean-toolchain`, `lakefile.toml`, `lake-manifest.json`). The Palomar comparator requires this toolchain or later.

## Building and verifying

```bash
lake build
python3 scripts/check-lean-sources.py
bash scripts/verify-comparator.sh
```

## License

Apache-2.0 (`LICENSE`).

## Compiling the paper

`doc/paper.tex` uses the `amsart` class and `doc/biblio.bib` with the BibTeX style `plainurl` (package `urlbst`; `hyperref` is loaded because `plainurl` uses `\href`). From the `doc` folder:

```
pdflatex paper
bibtex paper
pdflatex paper
pdflatex paper
```

The resulting `paper.pdf` and the auxiliary files are ignored by git.

## Experiments

The scripts of the computational section of the paper are in `experiments/` and do not need any package of this repository or of the `goldbach` repository:

```
python experiments/experiment.py     # N in [4, 2^14]; Python standard library only
python experiments/large_range.py    # N in [4, 10^6]; requires NumPy
python experiments/centering_stats.py  # N in [4, 10^6], 12 s: min R/HL on N = 2^k, p, 2p; least centered prime; defects (--defect N ...); requires NumPy
python experiments/centering_jr.py     # J_R(N) = R(2N) - c w (2N-4)/log^2(2N): thresholds N_0(c); requires NumPy
python experiments/centering_third.py   # least M <= N/3 with N-M and N+M prime; requires NumPy
python experiments/linnik_reach.py     # reach of the six-power representation (exact integer arithmetic)
python experiments/linnik_threshold.py # reach 149268109580462718976 and the construction on all even n in [10, 34030144]
python experiments/linnik_goldbach.py  # n = p + q + 6 for even n in [10, 10^7+6]; standard library only
```

Results of the runs reported in the paper: `experiment.py` (263.6 s) and `large_range.py` (107.9 s) give the tables of the computational section; `centering_third.py` (3.0 s) lists the least `M <= N/3` with `N - M`, `N + M` prime and the 11 exceptional `N`; `centering_jr.py` (0.5 s) gives the thresholds of `J_R(N) > 0`; `centering_stats.py` (12.2 s, `--max 1000000 --defect 1000 5000 20000`) gives the tables of the centering statistics; `linnik_goldbach.py` finds a Goldbach partition for every even `n` in `[4, 10^7]`, with largest least prime `751` at `n = 3807404`, so `n = p + q + 6` holds for every even `n` in `[10, 10^7 + 6]`.

The complete map from the labelled statements of the paper to Lean theorems, cited hypotheses and computations is in `doc/formalization.md`.
