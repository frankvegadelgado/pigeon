# Formalization notes

This document states what the Lean development proves, what it takes from the literature, and what it does not touch.

## Main result

Theorem `thm:geometric` of the paper, `PigeonGoldbach.Core.geometric_equivalence`: for `N ≥ 4` the existence of two distinct primes with sum `2N`, of `M ∈ [1, N - 3]` with `N - M` and `N + M` prime, and of `M ∈ [1, N - 3]` with `N² - M²` a semiprime (a product of two primes) are equivalent. The distinct-prime Goldbach conjecture itself is not proved in the paper and is not claimed in Lean.

## Toolchain

The development builds with Lean `v4.35.0-rc2` and the Mathlib tag `v4.35.0-rc2`, as the Palomar comparator requires.

## Definitions

`A N = {1, ..., N - 3}`; `C N = {M ∈ A N : N - M prime}`; `D N = {M ∈ A N : N + M prime}`; `E N` is the set of `M ∈ A N` for which there are primes `P, Q` with `2 < P < N < Q < 2N` and `P + 2M = Q` (so that `M = (Q - P)/2`); `B N = {M ∈ A N : M ≢ N (mod 2)}`; `IsSemiprime n` means `n = p q` for primes `p, q`.

## Proved in Lean (`PigeonGoldbach/Core.lean`, and the modules named below)

* `geometric_equivalence`: Theorem `thm:geometric`, the equivalence of (i), (ii) and (iii), with the area identity `area_eq : N² - M² = (N - M)(N + M)` for `M ≤ N`.
* `centered_intersection_criterion`: Proposition `prop:intersection`, the distinct-prime partition of `2N` exists if and only if `C N ∩ D N` is nonempty.
* `CD_subset_E` and `CED_eq_CD`: Lemma `lem:CD-in-E`, `C N ∩ D N ⊆ E N` and `C N ∩ E N ∩ D N = C N ∩ D N`.
* `C_D_subset_B`: `C N` and `D N` lie in the parity class `B N`.
* `gap_lower` and `gap_lower_missing`: Lemma `lem:gap`. If every prime below `N` is at most `pm` and every prime above `N` is at least `pp`, then `pp - pm ≤ 2M` for `M ∈ E N`, and every `M ∈ A N` with `2M < pp - pm` lies in `A N \ E N`.
* `gap_top` and `gap_top_missing`: Lemma `lem:gap-top`. If every prime below `2N` is at most `q`, then `2M + 3 ≤ q` for `M ∈ E N`, and every `M ∈ A N` with `q < 2M + 3` lies in `A N \ E N`.
* `pigeonhole_core` and `pigeonhole_CE`: the pigeonhole step of Proposition `prop:pigeonhole-CE`: if `|A N \ E N| < |C N|` then `C N ∩ E N` is nonempty.
* `card_C`: `|C N|` equals the number of primes `P` with `3 ≤ P ≤ N - 1`.
* `card_E_ge`: for `N ≥ 4`, the number of primes `Q` with `N < Q ≤ 2N - 3` is at most `|E N|` (the injection `Q ↦ (Q - 3)/2` of Corollary `cor:half-difference-baseline`).
* `mem_E_shift`: for `3 ≤ P < N`, `N - P ∈ E N` if and only if there are primes `2 < P' < N < Q' < 2N` with `Q' + 2P = 2N + P'`, which is the equation `Q' = (2N - P) + (P' - P)` of Corollary `cor:goldbach-diff`.
* `H_pos_iff`: for `N ≥ 3`, `0 < H N` if and only if `|A N \ E N| < log²(2N)`, where `H N = log²(2N) - ((N - 3) - |E N|)` (Section `subsec:gaps-H`).
* `card_C_le_CE_add` and `card_CE_le`: `|C N| ≤ |C N ∩ E N| + |A N \ E N|` and `|C N ∩ E N| ≤ |C N|` (counting step of Corollary `cor:goldbach-diff`).
* `mem_E_of_pair`: primes `3 ≤ P < N < Q ≤ 2N - 3` give `(Q - P)/2 ∈ E N` (Section `subsec:upper-prime-count`).
* `card_E_ge_Ioo`: for `N ≥ 4`, the primes in `(N, 2N)` number at most `|E N| + 1` (Corollary `cor:half-difference-baseline`).
* `pigeonhole_CE_of_H`: `H N > 0` and `|C N| > log²(2N)` give `C N ∩ E N` nonempty (Proposition `prop:pigeonhole-CE`).
* `gap_card_missing` and `gap_card_consecutive`: with `pp - pm + 4 ≤ 2N`, `pp - pm ≤ 2|A N \ E N| + 2`; for consecutive primes `p < p'` with `p ≥ 3`, `p' - p ≤ 2|A (p+1) \ E (p+1)| + 2` (Theorem `thm:cramer`, Corollary `cor:long-gaps`; uses Bertrand's postulate from Mathlib).
* `cramer_bound`: `H (p+1) > 0` gives `p' - p < 2 log²(2p + 2) + 2` (Theorem `thm:cramer`).
* `cs_count`, `T_ge_pairs`, `card_lt_pairs`, `V_le_quad`, `positive_proportion_of_bounds`: the combinatorial part of Theorem `thm:positive-proportion`. With `R N = |C N ∩ D N|`, `T = ∑ R N` and `V = ∑ R N ²` over `4 ≤ N ≤ X`: `T² ≤ cnt · V` (Cauchy–Schwarz, `cnt` the number of `N` with `R N ≥ 1`); `T` is at least the number of pairs of odd primes `p < q ≤ X`, and `2 · pairs + |s| = |s|²` for any finite set `s`; `V` is at most the number of quadruples with `p, p'` odd primes `≤ X`, `q, q'` odd primes `≤ 2X` and `p + q = p' + q'`; and `T ≥ T₀ ≥ 0`, `V ≤ V₀`, `V₀ > 0` give `cnt ≥ T₀² / V₀`. The bounds for `T₀` and `V₀` (Siebert's inequality, Dusart's estimates, the constants) are not formalized, so `X/2382` is not a Lean statement.
* `CitedResults` (`PigeonGoldbach/CitedResults.lean`): the published results the paper uses are stated as hypotheses, as in the Paloma formalization (propositions, not axioms): `SiebertBound` (Siebert, Monatsh. Math. 82 (1976)), `DusartUpper`, `DusartLower`, `DusartShortInterval` (Dusart 1998), `RosserSchoenfeldPi`, `RosserSchoenfeldDyadic` (Rosser and Schoenfeld, Illinois J. Math. 6 (1962)) and `GoldbachVerification` (Oliveira e Silva, Herzog and Pardi, Math. Comp. 83 (2014)). Proved from them: `card_oddPrimes_add_one` (the odd primes `≤ X` number `π(X) - 1`), `T_lower_of_RS` (`T > (s - 2)²/2` with `s = X/log X`), `positive_proportion_of_cited` (the conditional proportion bound `((s - 2)²/2)² / V₀`) and `verified_range` (Proposition `prop:verified`: `C N ∩ D N` is nonempty for `4 ≤ N ≤ 2·10¹⁸` given `GoldbachVerification` and the computed range `N ≤ 9781`).
* `zero_case`: `N` is prime if and only if `2N = p + q` for primes with `p = q` (the case `M = 0` of the open questions).
* `CD_iff_centered_witness`: `M ∈ C N ∩ D N` if and only if `M ∈ A N` is the half-difference of a straddling pair `(P, Q)` with `P + Q = 2N`.
* `card_CD_le_primes`: `R(2N) ≤ |C N|`, the number of primes `3 ≤ P ≤ N - 1` (counting step of Proposition `prop:HR-negative`).
* `classical_iff_distinct`: `2N` is a sum of two primes if and only if `N` is prime or `2N` is a sum of two distinct primes.
* `Preprints` (`PigeonGoldbach/Preprints.lean`): hypotheses for the arXiv preprints of Pintz–Althöfer (2610.15559), Johnston–Trudgian (2605.17825) and Bhowmik–Grimmelt (2607.27282: `HardyLittlewoodConditional`, `ChudakovVdCEstermann`, `MontgomeryVaughan`, `PintzUnconditional`), the prime-pair bound `GoldbachUpperBound` and the generalized Riemann hypothesis `GRHDirichlet`; proved from them: `gExp_*` (exponent arithmetic), `exceptional_half`, `exceptional_half_of_HL`, `exceptional_seven_twelfths`, `cnt_add_distinctExceptional`, `cnt_lower_of_exceptional`, `exponent_pairs` (`2·19/24 - 1 = 7/12` and `2·4/5 - 1 = 3/5`), the definitions `ExceptionalBound` and `ZeroFreeHalfPlane`, `classical_iff_distinct_of_not_prime`, `goldbachExceptional_subset_distinct`, `distinctExceptional_subset`, `card_distinctExceptional_le`, `two_mul_R_le_G`, `R_upper_of_goldbach_upper`, `LinnikGoldbach.succ`, `linnikGoldbach_six_iff`, `linnik_six`, `linnik_seven`.
* `distinct_goldbach_of_tail` (`CitedResults`): `R(2N) > 0` for all `N ≥ N₁`, `N₁ ≤ 2·10¹⁸ + 1`, gives the distinct-prime conjecture for all `N ≥ 4`, given the cited verification.
* `distinct_goldbach_iff_tail` (`CitedResults`): the distinct-prime Goldbach conjecture is equivalent to `C N ∩ D N` nonempty for every `N > 2·10¹⁸`, given `GoldbachVerification` and the computed range `N ≤ 9781`.
* `centered_of_partition`: for `N ≥ 4`, primes `p, q` with `p + q = 2N` and `p < N` give an element of `C N ∩ D N` (the step of Proposition `prop:verified`).
* `small_cases`: `C N ∩ D N` is nonempty for `4 ≤ N ≤ 12`.

`comparator.json` lists the public versions of these theorems (namespace `PigeonGoldbach.Public`); `Challenge.lean` imports only Mathlib and `Solution.lean` proves the same statements from the project module. `Challenge.lean` contains only the definitions and lemmas that the compared statements need, because Palomar caps the configured challenge source at 1,000 lines; `scripts/check-lean-sources.py` fails when it exceeds the cap.

## Taken from the literature

| Result | Reference in the paper |
| --- | --- |
| Hardy–Littlewood asymptotic for prime pairs with almost all differences | Mikawa, Tsukuba J. Math. 15 (1991) |
| Explicit upper bound for prime pairs `p, p + h` | Siebert, Monatsh. Math. 82 (1976) |
| Primes in short intervals and bounds for `π(x)` | Dusart (1998); Rosser and Schoenfeld, Illinois J. Math. 6 (1962) |
| Long gaps between primes | Ford, Green, Konyagin, Maynard and Tao, J. Amer. Math. Soc. 31 (2018) |
| Verification of the even Goldbach conjecture up to `4·10¹⁸`; least prime `≤ 9781` of a partition | Oliveira e Silva, Herzog and Pardi, Math. Comp. 83 (2014); their web page |
| Prime pairs `p, p + 2k` for almost all `k` | Lavrik (1961), Wolke (1989), Mikawa (1991), Matomäki, Radziwiłł and Tao (2019): context for `prop:mikawa` and `prop:almost-all`; not stated in Lean |
| Exceptional set of sums of two primes: `E(X) ≪ X^{1/2+ε}` under `H_{1/2}`; Chudakov, van der Corput, Estermann; Montgomery–Vaughan; Pintz | Bhowmik–Grimmelt (arXiv 2607.27282), Montgomery and Vaughan (1975): hypotheses `HardyLittlewoodConditional`, `ChudakovVdCEstermann`, `MontgomeryVaughan`, `PintzUnconditional` |
| Exceptional set exponents `7/12` and `1/2` | Pintz–Althöfer (arXiv 2610.15559): hypotheses `PintzAlthoferTheorem1`, `PintzAlthoferTheorem3` |
| Upper bound for prime pairs, `G(n) ≤ C n/log² n` | Lichtman (arXiv 2309.08522) and Johnston–Trudgian (arXiv 2605.17825): hypothesis `GoldbachUpperBound` |
| Linnik–Goldbach with six powers of two under the generalized Riemann hypothesis | Johnston–Trudgian (arXiv 2605.17825), Theorem 1: hypothesis `JohnstonTrudgianTheorem1` |
| Generalized Riemann hypothesis `H_{1/2}` | Alpöge (Lean proof, 20 November 2026), certified by the Lean FRO and the Mathlib Initiative: hypothesis `GRHDirichlet` |
| Cramér's conjecture and the difference of consecutive primes | Cramér (1936), Baker, Harman and Pintz (2001): context for `thm:cramer`; not stated in Lean |
| Symmetric reformulation `N - M`, `N + M` prime | OEIS A082467: context for `thm:geometric`; Goldbach (1742/1843): the conjecture |

`SiebertBound`, the Dusart and Rosser–Schoenfeld bounds and `GoldbachVerification` are stated in `PigeonGoldbach/CitedResults.lean` as explicit hypotheses and used only as hypotheses of theorems; Mikawa's theorem and the long-gap theorem are not stated in Lean.

## Not formalized

* Proposition `prop:almost-all`, Corollary `cor:goldbach-diff` in its asymptotic form, Theorem `thm:linear`, Lemmas `lem:energy` and `lem:energy-bound`, and the explicit bounds of Theorem `thm:positive-proportion` (the value `X/2382`).
* Lemma `lem:elementary`, Proposition `prop:HR-negative` for `34 ≤ N ≤ 63`, Proposition `prop:many-upper`, Corollary `cor:long-gaps` in its asymptotic form, and the explicit numerical bounds on `ω` and `G`.
* The inequality `|C_N| > log²(2N)` of Proposition `prop:pigeonhole-CE` and the bound on the number of primes in `(N, 2N)` of Proposition `prop:many-upper`: they are taken as hypotheses in `pigeonhole_CE_of_H`, `card_E_ge_Ioo` and `cramer_bound`.
* Proposition `prop:verified`: the verification of the even Goldbach conjecture and the computation of Section `sec:computational` are not formalized; only the step from a partition `2N = p + q` with `p < N` to `C N ∩ D N` is.
* The computations, tables and scripts of Section `sec:computational`.

The computations of the paper (the eight scripts of `experiments/`: `experiment.py`, `large_range.py`, `centering_stats.py`, `centering_jr.py`, `centering_third.py`, `linnik_goldbach.py`, `linnik_reach.py` and `linnik_threshold.py`) are not formalized in Lean. The range `10 ≤ n ≤ 4·10¹⁸ + 6` of the six-power representation is covered in Lean from the cited verification (`sixPowerRep_of_verification`), and `linnik_goldbach.py` checks it directly for `10 ≤ n ≤ 10⁷ + 6`.

`Centered` (`PigeonGoldbach/Centered.lean`): `HR`, `card_oddPrimes_le`, `R_le_half`, `log_sq_lt` and `HR_neg_of_ge_64` (`H_R(N) < 0` for `N ≥ 64`, without cited results).

`Extended` (`PigeonGoldbach/Extended.lean`): the sets with `M = 0`; `zero_mem_CDext_iff`, `zero_mem_Eext_iff`, `CDext_eq`, `Rext_eq` (`R̄(2N) = R(2N) + 1` for prime `N`) and `classical_iff_Rext`. `sixPowerRep_equal_powers` (`Preprints`) covers even `n` up to `8·10¹⁸ - 4` with six equal powers of two; the reach `4·10¹⁸ + 63·2⁶¹` of Proposition `prop:six-powers-ext` is proved in the paper and checked by `experiments/linnik_reach.py` and `experiments/linnik_threshold.py`.

## Map from the statements of the paper to Lean

| Paper label | Status | Lean / cited |
|---|---|---|
| `prop:dusart-short` | cited | `DusartShortInterval` |
| `prop:dusart-consec` | cited | source of `DusartShortInterval`; not stated separately |
| `prop:dusart-upper` | cited | `DusartUpper`, `DusartLower` |
| `prop:rs-pi, prop:rs-dyadic` | cited | `RosserSchoenfeldPi`, `RosserSchoenfeldDyadic` |
| `lem:elementary` | not formalized | numerical inequality; checked in `experiment.py` (item 4) |
| `thm:geometric` | formalized | `geometric_equivalence` |
| `prop:intersection` | formalized | `centered_intersection_criterion` |
| `prop:M-zero` | formalized | `Extended`: `zero_mem_CDext_iff`, `zero_mem_Eext_iff`, `Rext_eq`, `classical_iff_Rext` |
| `lem:CD-in-E` | formalized | `CD_subset_E`, `CED_eq_CD`, `C_D_subset_B` |
| `lem:gap, lem:gap-top` | formalized | `gap_lower(_missing)`, `gap_top(_missing)`, `gap_card_missing` |
| `prop:siebert` | cited | `SiebertBound` |
| `lem:energy, lem:energy-bound, thm:linear` | not formalized | explicit analytic estimates |
| `prop:mikawa, prop:almost-all` | not formalized | Mikawa's theorem (asymptotic, unspecified constants) |
| `cor:goldbach-diff` | partly formalized | `mem_E_shift`, `card_C_le_CE_add`, `card_CE_le`; asymptotic form not formalized |
| `thm:positive-proportion` | combinatorial part formalized | `cs_count`, `T_ge_pairs`, `card_lt_pairs`, `V_le_quad`, `positive_proportion_of_bounds`, `positive_proportion_of_cited` |
| `prop:E-half` | from cited | `exceptional_half`, `exceptional_seven_twelfths` |
| `prop:E-distinct` | formalized | `classical_iff_distinct_of_not_prime`, `distinctExceptional_subset`, `card_distinctExceptional_le` |
| `cor:cnt-GRH` | from cited | `cnt_add_distinctExceptional`, `cnt_lower_of_exceptional` |
| `prop:R-upper` | from cited | `two_mul_R_le_G`, `R_upper_of_goldbach_upper` |
| `prop:six-powers` | from cited verification | `sixPowerRep_of_verification`, `sixPowerRep_outside_gap`, `sixPowerRep_complete` |
| `prop:six-powers-ext` | proved in the paper | range up to 8e18 - 4 in `sixPowerRep_equal_powers`; full range checked by `linnik_reach.py`; `linnik_threshold.py` checks the reach and the construction for all even `n` with `10 ≤ n ≤ 10⁶ + 63·2¹⁹` |
| `hyp:half-difference-density` | statement | `0 < H N` (`H_pos_iff`) |
| `hyp:centered` | statement | `0 < R N` (`distinct_goldbach_iff_tail`, `distinct_goldbach_of_tail`) |
| `prop:centering-data` | not formalized | consequences of the run of `centering_stats.py` (Tables `tab:family`, `tab:pmin`, `tab:defect`); the inequality `HL(2N) ≥ ω(2N-4)/log²(2N)` is `HL_ge` (with `HLintegral_ge`, `one_le_kappa`) |
| `cor:JR` | formalized from computed data | `Centered`: `JR`, `Fc`, `JR_pos_iff`, `JR_const`, `F_gt_of_JR_pos`, `JR_Fc_pos_of_HL`, `R_pos_of_JR_Fc_pos`; parts (4) and (5) from the runs of `centering_stats.py` and `centering_jr.py` |
| `prop:third-data` | not formalized | computation of `centering_third.py` (least `M ≤ N/3` with `N-M`, `N+M` prime, `N ≤ 10^6`) |
| `prop:many-upper` | not formalized | uses `DusartShortInterval`; `card_E_ge_Ioo` is the counting step |
| `cor:half-difference-baseline` | formalized | `card_E_ge`, `card_E_ge_Ioo` |
| `prop:pigeonhole-CE` | formalized | `pigeonhole_CE`, `pigeonhole_CE_of_H` |
| `thm:cramer` | formalized | `gap_card_consecutive`, `cramer_bound` |
| `cor:long-gaps` | partly formalized | `gap_card_consecutive`; the theorem of Ford, Green, Konyagin, Maynard and Tao is not stated |
| `prop:HR-negative` | formalized for `N ≥ 64` | `Centered`: `card_oddPrimes_le`, `R_le_half`, `log_sq_lt`, `HR_neg_of_ge_64`; `34 ≤ N ≤ 63` by computation (Table `tab:centered`) |
| `prop:verified` | formalized from cited | `centered_of_partition`, `verified_range`, `GoldbachVerification` |
| `prop:tail` | formalized | `distinct_goldbach_of_tail` |

In addition, `HLintegral`, `HL`, `HLintegral_ge` and `HL_ge` (`CitedResults`) state the Hardy–Littlewood prediction and prove `HL(2N) ≥ ω (2N-4)/log²(2N)`, and `one_le_kappa` and `main_term_ge` (`CitedResults`) give `κ(n) ≥ 1` and the lower bound `ω n / log² n` for the main term `ω κ(n) n / log² n`.
