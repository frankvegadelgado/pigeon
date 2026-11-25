module

public import Mathlib
public import PigeonGoldbach.Core

@[expose] public section

/-!
# Published results used as explicit hypotheses

Some steps of the paper rest on published theorems whose proofs are analytic number theory
and are not formalized here. This module states exactly what the paper uses from them, as
hypotheses (propositions, not axioms) with references, and proves everything that follows
from them.

* `SiebertBound`: Siebert's upper bound for prime pairs `p, p + h`, stated in
  H. Siebert, Montgomery's weighted sieve for dimension two, Monatsh. Math. 82 (1976) 327--336.
* `DusartUpper`, `DusartLower`, `DusartShortInterval`: P. Dusart, *Autour de la fonction qui
  compte le nombre de nombres premiers*, thesis, Limoges (1998).
* `RosserSchoenfeldPi`, `RosserSchoenfeldDyadic`: J. B. Rosser and L. Schoenfeld,
  Illinois J. Math. 6 (1962) 64--94.
* `GoldbachVerification`: T. Oliveira e Silva, S. Herzog and S. Pardi, Math. Comp. 83 (2014)
  2033--2060.

Mikawa's theorem (Tsukuba J. Math. 15 (1991)) and the theorem of Ford, Green, Konyagin,
Maynard and Tao (J. Amer. Math. Soc. 31 (2018)) are asymptotic statements with unspecified
constants; no Lean statement uses them, and they appear only in the documentation.
-/

namespace PigeonGoldbach.CitedResults

open scoped Classical

open PigeonGoldbach.Core

/-- `π(n)`, the number of primes `p ≤ n`. -/
noncomputable def piCount (n : ℕ) : ℕ := ((Finset.Icc 1 n).filter Nat.Prime).card

/-- The Hardy–Littlewood constant `ω = ∏_{p > 2} (1 - 1/(p - 1)²)`. -/
noncomputable def omegaConst : ℝ :=
  ∏' p : {p : ℕ // p.Prime ∧ 2 < p}, (1 - 1 / ((p : ℝ) - 1) ^ 2)

/-- The arithmetic factor `κ(h) = ∏_{p ∣ h, p > 2} (p - 1)/(p - 2)`. -/
noncomputable def kappa (h : ℕ) : ℝ :=
  ∏ p ∈ h.primeFactors.filter (fun p => 2 < p), ((p : ℝ) - 1) / ((p : ℝ) - 2)

/-- Cited: the sieve bound of Siebert (Proposition `prop:siebert`). For every real `x > 1`
and every even `h ≠ 0`, the number of primes `p ≤ x` with `p + h` prime is at most
`16 ω κ(h) x / log² x`. -/
def SiebertBound : Prop :=
  ∀ (x : ℝ) (h : ℕ), 1 < x → h ≠ 0 → h % 2 = 0 →
    (((Finset.Icc 1 ⌊x⌋₊).filter fun p => p.Prime ∧ (p + h).Prime).card : ℝ) ≤
      16 * omegaConst * kappa h * (x / Real.log x ^ 2)

/-- `κ(h) ≥ 1`: each factor `(p - 1)/(p - 2)` with `p > 2` is at least `1`. -/
theorem one_le_kappa (h : ℕ) : 1 ≤ kappa h := by
  unfold kappa
  calc (1 : ℝ) = ∏ p ∈ h.primeFactors.filter (fun p => 2 < p), (1 : ℝ) := by simp
    _ ≤ ∏ p ∈ h.primeFactors.filter (fun p => 2 < p), (((p : ℝ) - 1) / ((p : ℝ) - 2)) := by
      gcongr with p hp
      rw [Finset.mem_filter] at hp
      have h3 : (3 : ℝ) ≤ p := by exact_mod_cast hp.2
      rw [le_div_iff₀ (by linarith)]
      linarith

/-- The main term `ω κ(n) n / log² n` is at least `ω n / log² n`. -/
theorem main_term_ge (hω : 0 ≤ omegaConst) (n : ℕ) (hn : 1 < (n : ℝ)) :
    omegaConst * ((n : ℝ) / Real.log n ^ 2) ≤
      omegaConst * kappa n * ((n : ℝ) / Real.log n ^ 2) := by
  have hlog : 0 < Real.log n := Real.log_pos hn
  have hq : 0 ≤ (n : ℝ) / Real.log n ^ 2 := by positivity
  have hk := one_le_kappa n
  calc omegaConst * ((n : ℝ) / Real.log n ^ 2)
      = omegaConst * 1 * ((n : ℝ) / Real.log n ^ 2) := by ring
    _ ≤ omegaConst * kappa n * ((n : ℝ) / Real.log n ^ 2) := by
      apply mul_le_mul_of_nonneg_right _ hq
      exact mul_le_mul_of_nonneg_left hk hω

/-- The integral `∫_2^{2N-2} dt / (log t · log (2N - t))` of the Hardy–Littlewood prediction. -/
noncomputable def HLintegral (N : ℕ) : ℝ :=
  ∫ t in (2 : ℝ)..(2 * (N : ℝ) - 2), 1 / (Real.log t * Real.log (2 * (N : ℝ) - t))

/-- The Hardy–Littlewood prediction `HL(2N) = ω κ(N) ∫_2^{2N-2} dt / (log t · log (2N - t))`. -/
noncomputable def HL (N : ℕ) : ℝ := omegaConst * kappa N * HLintegral N

/-- `∫_2^{2N-2} dt / (log t · log (2N - t)) ≥ (2N - 4) / log² (2N)`: both logarithms are at
most `log (2N)` on the interval. -/
theorem HLintegral_ge {N : ℕ} (hN : 2 ≤ N) :
    (2 * (N : ℝ) - 4) / Real.log (2 * (N : ℝ)) ^ 2 ≤ HLintegral N := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hle : (2 : ℝ) ≤ 2 * (N : ℝ) - 2 := by linarith
  have hL : 0 < Real.log (2 * (N : ℝ)) := Real.log_pos (by linarith)
  have hcont : ContinuousOn (fun t : ℝ => 1 / (Real.log t * Real.log (2 * (N : ℝ) - t)))
      (Set.uIcc 2 (2 * (N : ℝ) - 2)) := by
    rw [Set.uIcc_of_le hle]
    have h1 : ∀ t ∈ Set.Icc (2 : ℝ) (2 * (N : ℝ) - 2), Real.log t ≠ 0 := by
      intro t ht
      exact (Real.log_pos (by linarith [ht.1])).ne'
    have h2 : ∀ t ∈ Set.Icc (2 : ℝ) (2 * (N : ℝ) - 2), Real.log (2 * (N : ℝ) - t) ≠ 0 := by
      intro t ht
      exact (Real.log_pos (by linarith [ht.2])).ne'
    refine continuousOn_const.div (ContinuousOn.mul ?_ ?_) ?_
    · refine ContinuousOn.log (f := fun t : ℝ => t) (by fun_prop) (fun t ht => ?_)
      have h3 : (2 : ℝ) ≤ t := ht.1
      show t ≠ 0
      exact ne_of_gt (by linarith)
    · refine ContinuousOn.log (f := fun t : ℝ => 2 * (N : ℝ) - t) (by fun_prop) (fun t ht => ?_)
      have h3 : t ≤ 2 * (N : ℝ) - 2 := ht.2
      show 2 * (N : ℝ) - t ≠ 0
      exact ne_of_gt (by linarith)
    · intro t ht
      exact mul_ne_zero (h1 t ht) (h2 t ht)
  have hmono : ∫ t in (2 : ℝ)..(2 * (N : ℝ) - 2), 1 / Real.log (2 * (N : ℝ)) ^ 2 ≤
      HLintegral N := by
    unfold HLintegral
    apply intervalIntegral.integral_mono_on hle
    · exact intervalIntegrable_const
    · exact hcont.intervalIntegrable
    · intro t ht
      have ht1 : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
      have ht2 : 0 < Real.log (2 * (N : ℝ) - t) := Real.log_pos (by linarith [ht.2])
      have ht3 : Real.log t ≤ Real.log (2 * (N : ℝ)) :=
        Real.log_le_log (by linarith [ht.1]) (by linarith [ht.1, ht.2])
      have ht4 : Real.log (2 * (N : ℝ) - t) ≤ Real.log (2 * (N : ℝ)) :=
        Real.log_le_log (by linarith [ht.2]) (by linarith [ht.1])
      apply one_div_le_one_div_of_le (mul_pos ht1 ht2)
      rw [sq]
      exact mul_le_mul ht3 ht4 ht2.le hL.le
  have hval : ∫ t in (2 : ℝ)..(2 * (N : ℝ) - 2), 1 / Real.log (2 * (N : ℝ)) ^ 2 =
      (2 * (N : ℝ) - 4) / Real.log (2 * (N : ℝ)) ^ 2 := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    ring
  rw [hval] at hmono
  exact hmono

/-- `HL(2N) ≥ ω (2N - 4) / log² (2N)` for `N ≥ 2`, since `κ(N) ≥ 1`. -/
theorem HL_ge (hω : 0 ≤ omegaConst) {N : ℕ} (hN : 2 ≤ N) :
    omegaConst * ((2 * (N : ℝ) - 4) / Real.log (2 * (N : ℝ)) ^ 2) ≤ HL N := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hL : 0 < Real.log (2 * (N : ℝ)) := Real.log_pos (by linarith)
  have hq : 0 ≤ (2 * (N : ℝ) - 4) / Real.log (2 * (N : ℝ)) ^ 2 := by
    apply div_nonneg (by linarith) (by positivity)
  have hI := HLintegral_ge hN
  have hk := one_le_kappa N
  unfold HL
  calc omegaConst * ((2 * (N : ℝ) - 4) / Real.log (2 * (N : ℝ)) ^ 2)
      = omegaConst * 1 * ((2 * (N : ℝ) - 4) / Real.log (2 * (N : ℝ)) ^ 2) := by ring
    _ ≤ omegaConst * kappa N * HLintegral N := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hk hω
      · exact hI
      · exact hq
      · exact mul_nonneg hω (by linarith)

/-- Cited: Dusart (1998), Théorème 1.10, upper bound
`π(x) ≤ x/log x · (1 + 1.2762/log x)` for `x > 1` (Proposition `prop:dusart-upper`). -/
def DusartUpper : Prop :=
  ∀ x : ℝ, 1 < x →
    (piCount ⌊x⌋₊ : ℝ) ≤ x / Real.log x * (1 + 1.2762 / Real.log x)

/-- Cited: Dusart (1998), Théorème 1.10, lower bound
`x/log x · (1 + 1/log x) ≤ π(x)` for `x ≥ 599` (Proposition `prop:dusart-upper`). -/
def DusartLower : Prop :=
  ∀ x : ℝ, 599 ≤ x →
    x / Real.log x * (1 + 1 / Real.log x) ≤ (piCount ⌊x⌋₊ : ℝ)

/-- Cited: Rosser and Schoenfeld (1962), Corollary 1, (3.5): `π(x) > x/log x` for
`x ≥ 17` (Proposition `prop:rs-pi`). -/
def RosserSchoenfeldPi : Prop :=
  ∀ x : ℝ, 17 ≤ x → x / Real.log x < (piCount ⌊x⌋₊ : ℝ)

/-- Cited: Rosser and Schoenfeld (1962), Corollaries 3.8–3.9:
`3x/(5 log x) < π(2x) - π(x) < 7x/(5 log x)` for `x ≥ 41/2` (Proposition `prop:rs-dyadic`). -/
def RosserSchoenfeldDyadic : Prop :=
  ∀ x : ℝ, 41 / 2 ≤ x →
    3 * x / (5 * Real.log x) < (piCount ⌊2 * x⌋₊ : ℝ) - (piCount ⌊x⌋₊ : ℝ) ∧
      (piCount ⌊2 * x⌋₊ : ℝ) - (piCount ⌊x⌋₊ : ℝ) < 7 * x / (5 * Real.log x)

/-- Cited: Dusart (1998), Théorème 1.9: for `x ≥ 3275` there is a prime `p` with
`x < p ≤ x (1 + 1/(2 log² x))` (Proposition `prop:dusart-short`). -/
def DusartShortInterval : Prop :=
  ∀ x : ℝ, 3275 ≤ x →
    ∃ p : ℕ, p.Prime ∧ x < p ∧ (p : ℝ) ≤ x * (1 + 1 / (2 * Real.log x ^ 2))

/-- Cited: the verification of the even Goldbach conjecture by Oliveira e Silva, Herzog and
Pardi (Math. Comp. 83 (2014)) up to `4 · 10¹⁸`, with least prime at most `9781`. -/
def GoldbachVerification : Prop :=
  ∀ n : ℕ, 4 ≤ n → n ≤ 4 * 10 ^ 18 → n % 2 = 0 →
    ∃ p : ℕ, p.Prime ∧ p ≤ 9781 ∧ (n - p).Prime

/-- The odd primes `≤ X` number `π(X) - 1`. -/
theorem card_oddPrimes_add_one {X : ℕ} (hX : 2 ≤ X) :
    (oddPrimes X).card + 1 = piCount X := by
  have h : (Finset.Icc 1 X).filter Nat.Prime = insert 2 (oddPrimes X) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert, oddPrimes]
    constructor
    · rintro ⟨⟨h1, h2⟩, hp⟩
      by_cases h2' : p = 2
      · exact Or.inl h2'
      · right
        have := hp.two_le
        exact ⟨⟨by omega, h2⟩, hp⟩
    · rintro (rfl | ⟨⟨h1, h2⟩, hp⟩)
      · exact ⟨⟨by norm_num, hX⟩, Nat.prime_two⟩
      · exact ⟨⟨by omega, h2⟩, hp⟩
  have hn : 2 ∉ oddPrimes X := by simp [oddPrimes]
  unfold piCount
  rw [h, Finset.card_insert_of_notMem hn]

/-- Theorem `thm:positive-proportion`, lower bound for `T` from the cited bound
`π(x) > x/log x`: `T > (s - 2)²/2` with `s = X/log X`. -/
theorem T_lower_of_RS (hRS : RosserSchoenfeldPi) {X : ℕ} (hX : 17 ≤ X)
    (hs : 2 ≤ (X : ℝ) / Real.log X) :
    ((X : ℝ) / Real.log X - 2) ^ 2 / 2 < (Tsum X : ℝ) := by
  have h1 := hRS (X : ℝ) (by exact_mod_cast hX)
  simp only [Nat.floor_natCast] at h1
  have h2 := card_oddPrimes_add_one (X := X) (by omega)
  have h3 : ((oddPrimes X).card : ℝ) + 1 = (piCount X : ℝ) := by exact_mod_cast h2
  have h4 := T_ge_pairs X
  have h5 := card_lt_pairs (oddPrimes X)
  have h6 : (oddPrimes X).card ^ 2 ≤ 2 * Tsum X + (oddPrimes X).card := by linarith
  have h7 : ((oddPrimes X).card : ℝ) ^ 2 ≤ 2 * (Tsum X : ℝ) + ((oddPrimes X).card : ℝ) := by
    exact_mod_cast h6
  have hmain : ∀ m s T : ℝ, s - 1 < m → 2 ≤ s → m ^ 2 ≤ 2 * T + m →
      (s - 2) ^ 2 / 2 < T := by
    intro m s T hm hs2 hT
    nlinarith [mul_pos (by linarith : 0 < m - 1 - (s - 2)) (by linarith : 0 < m - 1 + (s - 2))]
  exact hmain _ _ _ (by linarith) hs h7

/-- Theorem `thm:positive-proportion`: with the cited bound `π(x) > x/log x` and an upper
bound `V ≤ Vup` (which the paper derives from Siebert's inequality), at least
`((s - 2)²/2)² / Vup` integers `4 ≤ N ≤ X` have `R(2N) ≥ 1`. -/
theorem positive_proportion_of_cited (hRS : RosserSchoenfeldPi) {X : ℕ} {Vup : ℝ}
    (hX : 17 ≤ X) (hs : 2 ≤ (X : ℝ) / Real.log X) (hVup : 0 < Vup)
    (hV : (Vsum X : ℝ) ≤ Vup) :
    ((((X : ℝ) / Real.log X - 2) ^ 2 / 2) ^ 2) / Vup ≤ (cnt X : ℝ) :=
  positive_proportion_of_bounds (by positivity) hVup (T_lower_of_RS hRS hX hs).le hV

/-- Proposition `prop:verified`: from the cited verification of the even Goldbach conjecture
(with least prime at most `9781`) and the computed range `4 ≤ N ≤ 9781`, `R(2N) ≥ 1` for
every `4 ≤ N ≤ 2 · 10¹⁸`. -/
theorem verified_range (hG : GoldbachVerification)
    (hsmall : ∀ N : ℕ, 4 ≤ N → N ≤ 9781 → (C N ∩ D N).Nonempty)
    {N : ℕ} (h4 : 4 ≤ N) (hN : N ≤ 2 * 10 ^ 18) : (C N ∩ D N).Nonempty := by
  by_cases hs : N ≤ 9781
  · exact hsmall N h4 hs
  · obtain ⟨p, hp, hp9781, hq⟩ := hG (2 * N) (by omega) (by omega) (by omega)
    exact centered_of_partition h4 hp hq (by omega) (by omega)

/-- The distinct-prime Goldbach conjecture is equivalent to `C_N ∩ D_N ≠ ∅` for every
`N > 2 · 10¹⁸`, given the cited verification of the even Goldbach conjecture and the computed
range `4 ≤ N ≤ 9781`. -/
theorem distinct_goldbach_iff_tail (hG : GoldbachVerification)
    (hsmall : ∀ N : ℕ, 4 ≤ N → N ≤ 9781 → (C N ∩ D N).Nonempty) :
    (∀ N : ℕ, 4 ≤ N → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ p + q = 2 * N) ↔
      ∀ N : ℕ, 2 * 10 ^ 18 < N → (C N ∩ D N).Nonempty := by
  constructor
  · intro h N hN
    exact (centered_intersection_criterion (by omega)).1 (h N (by omega))
  · intro h N hN
    by_cases hb : N ≤ 2 * 10 ^ 18
    · exact (centered_intersection_criterion hN).2 (verified_range hG hsmall hN hb)
    · exact (centered_intersection_criterion hN).2 (h N (by omega))

/-- Patching: if `R(2N) > 0` for every `N ≥ N₁` with `N₁ ≤ 2 · 10¹⁸ + 1`, then, with the cited
verification and the computed range `4 ≤ N ≤ 9781`, every `2N` with `N ≥ 4` is a sum of two
distinct primes. -/
theorem distinct_goldbach_of_tail (hG : GoldbachVerification)
    (hsmall : ∀ N : ℕ, 4 ≤ N → N ≤ 9781 → (C N ∩ D N).Nonempty) {N1 : ℕ}
    (hN1 : N1 ≤ 2 * 10 ^ 18 + 1) (h : ∀ N : ℕ, N1 ≤ N → 0 < R N) :
    ∀ N : ℕ, 4 ≤ N → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ p + q = 2 * N := by
  refine (distinct_goldbach_iff_tail hG hsmall).2 ?_
  intro N hN
  exact Finset.card_pos.mp (h N (by omega))

end PigeonGoldbach.CitedResults
