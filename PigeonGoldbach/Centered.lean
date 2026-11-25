module

public import Mathlib
public import PigeonGoldbach.Core
public import PigeonGoldbach.CitedResults

@[expose] public section

/-!
# The centered statistic

`HR N = log²(2N) - ((N - 3) - R(2N))` is the centered statistic `H_R(N)` of
Proposition `prop:HR-negative`. This module proves `HR N < 0` for every `N ≥ 64` using
only `R(2N) ≤ |C_N|` and the parity bound `|C_N| ≤ N/2`; no cited result is used.
The values `34 ≤ N ≤ 63` are covered by the computation of the paper (Table `tab:centered`).
-/

namespace PigeonGoldbach.Centered

open scoped Classical

open PigeonGoldbach.Core
open PigeonGoldbach.CitedResults

/-- The centered statistic `H_R(N) = log²(2N) - ((N - 3) - R(2N))`. -/
noncomputable def HR (N : ℕ) : ℝ :=
  Real.log (2 * (N : ℝ)) ^ 2 - (((N : ℝ) - 3) - (R N : ℝ))

/-- The odd primes `3 ≤ p ≤ n` number at most `n / 2`. -/
theorem card_oddPrimes_le (n : ℕ) : (oddPrimes n).card ≤ n / 2 := by
  have h : (oddPrimes n).card ≤ (Finset.Icc 1 (n / 2)).card := by
    apply Finset.card_le_card_of_injOn (fun p => p / 2)
    · intro p hp
      simp only [oddPrimes, Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq] at hp
      obtain ⟨⟨h1, h2⟩, hpp⟩ := hp
      simp only [Finset.coe_Icc, Set.mem_Icc]
      omega
    · intro p hp q hq h
      simp only [oddPrimes, Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq] at hp hq
      obtain ⟨⟨hp1, hp2⟩, hpp⟩ := hp
      obtain ⟨⟨hq1, hq2⟩, hqp⟩ := hq
      have hp3 := hpp.eq_two_or_odd
      have hq3 := hqp.eq_two_or_odd
      have h' : p / 2 = q / 2 := h
      omega
  simpa using h

/-- `R(2N) ≤ (N - 1) / 2`. -/
theorem R_le_half (N : ℕ) : R N ≤ (N - 1) / 2 :=
  (card_CD_le_primes N).trans (card_oddPrimes_le (N - 1))

/-- `log²(2N) < N/2 - 3` for every `N ≥ 64`. -/
theorem log_sq_lt : ∀ N : ℕ, 64 ≤ N → Real.log (2 * (N : ℝ)) ^ 2 < (N : ℝ) / 2 - 3 := by
  intro N hN
  induction N, hN using Nat.le_induction with
  | base =>
    have h2 := Real.log_two_lt_d9
    have h2' := (Real.log_pos (by norm_num : (1 : ℝ) < 2))
    have e : Real.log (2 * ((64 : ℕ) : ℝ)) = 7 * Real.log 2 := by
      have h : (2 * ((64 : ℕ) : ℝ)) = 2 ^ 7 := by norm_num
      rw [h, Real.log_pow]
      norm_num
    have hsq : Real.log 2 ^ 2 < 0.5 := by
      nlinarith [mul_pos (sub_pos.2 h2) (add_pos h2' (by norm_num : (0 : ℝ) < 0.6931471808))]
    rw [e]
    push_cast
    nlinarith
  | succ n hn ih =>
    have hn' : (64 : ℝ) ≤ n := by exact_mod_cast hn
    have hpos : 0 < (n : ℝ) := by linarith
    have hn0 : (n : ℝ) ≠ 0 := hpos.ne'
    have hL : 0 ≤ Real.log (2 * (n : ℝ)) := Real.log_nonneg (by linarith)
    have hstep : Real.log (2 * ((n : ℝ) + 1)) ≤ Real.log (2 * (n : ℝ)) + 1 / n := by
      have e : 2 * ((n : ℝ) + 1) = 2 * (n : ℝ) * (1 + 1 / n) := by
        field_simp
      rw [e, Real.log_mul (mul_pos two_pos hpos).ne' (add_pos one_pos (one_div_pos.2 hpos)).ne']
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + 1 / n from
        add_pos one_pos (one_div_pos.2 hpos))
      linarith
    have hL' : 0 ≤ Real.log (2 * ((n : ℝ) + 1)) := Real.log_nonneg (by linarith)
    have hLn : Real.log (2 * (n : ℝ)) < n / 8 := by
      by_contra hc0
      have hc := not_lt.mp hc0
      nlinarith [mul_self_le_mul_self (by positivity : (0 : ℝ) ≤ n / 8) hc,
        mul_le_mul_of_nonneg_left hn' hpos.le]
    have hB : 0 ≤ Real.log (2 * (n : ℝ)) + 1 / n := by
      have := one_div_pos.2 hpos
      linarith
    have h1 := mul_le_mul hstep hstep hL' hB
    have h3 : (1 / (n : ℝ)) ≤ 1 / 64 := one_div_le_one_div_of_le (by norm_num) hn'
    have h4 : (1 / (n : ℝ)) ^ 2 ≤ 1 / 4 := by
      nlinarith [h3, one_div_pos.2 hpos]
    have h5 : 2 * Real.log (2 * (n : ℝ)) / n < 1 / 4 := by
      rw [div_lt_iff₀ hpos]
      linarith
    have h6 : (Real.log (2 * (n : ℝ)) + 1 / n) ^ 2 =
        Real.log (2 * (n : ℝ)) ^ 2 + 2 * Real.log (2 * (n : ℝ)) / n + (1 / (n : ℝ)) ^ 2 := by
      ring
    push_cast
    nlinarith [h1, h6, h4, h5, ih]

/-- Proposition `prop:HR-negative` for `N ≥ 64`: `H_R(N) < 0`. -/
theorem HR_neg_of_ge_64 {N : ℕ} (hN : 64 ≤ N) : HR N < 0 := by
  have hR : R N ≤ (N - 1) / 2 := R_le_half N
  have hR' : (R N : ℝ) ≤ (N : ℝ) / 2 := by
    have h1 : (R N : ℝ) ≤ (((N - 1) / 2 : ℕ) : ℝ) := by exact_mod_cast hR
    have h2 : (((N - 1) / 2 : ℕ) : ℝ) ≤ ((N - 1 : ℕ) : ℝ) / 2 := Nat.cast_div_le
    have h3 : ((N - 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.sub_le N 1
    linarith
  have h := log_sq_lt N hN
  unfold HR
  linarith

/-- `J_R(N) = F(N) - ((N - 3) - R(2N))` for a function `F`. -/
noncomputable def JR (F : ℕ → ℝ) (N : ℕ) : ℝ := F N - (((N : ℝ) - 3) - (R N : ℝ))

/-- `F_c(N) = N - 3 - c ω (2N - 4) / log² (2N)`. -/
noncomputable def Fc (c : ℝ) (N : ℕ) : ℝ :=
  (N : ℝ) - 3 - c * (omegaConst * ((2 * (N : ℝ) - 4) / Real.log (2 * (N : ℝ)) ^ 2))

theorem JR_pos_iff {F : ℕ → ℝ} {N : ℕ} : 0 < JR F N ↔ (N : ℝ) - 3 - F N < (R N : ℝ) := by
  unfold JR
  constructor <;> intro h <;> linarith

/-- For `F(N) = N - 3`, `J_R(N) = R(2N)`. -/
theorem JR_const (N : ℕ) : JR (fun n : ℕ => (n : ℝ) - 3) N = (R N : ℝ) := by
  unfold JR
  ring

/-- A necessary condition: `J_R(N) > 0` forces `F(N) > N - 3 - |C_N|`, where `|C_N|` is the
number of primes `3 ≤ P ≤ N - 1`. -/
theorem F_gt_of_JR_pos {F : ℕ → ℝ} {N : ℕ} (h : 0 < JR F N) :
    (N : ℝ) - 3 - (((Finset.Icc 3 (N - 1)).filter Nat.Prime).card : ℝ) < F N := by
  have h0 : R N ≤ ((Finset.Icc 3 (N - 1)).filter Nat.Prime).card := card_CD_le_primes N
  have h1 : (R N : ℝ) ≤ (((Finset.Icc 3 (N - 1)).filter Nat.Prime).card : ℝ) := by
    exact_mod_cast h0
  unfold JR at h
  linarith

/-- `J_R(N) > 0` for `F_c` follows from `c HL(2N) < R(2N)`. -/
theorem JR_Fc_pos_of_HL (hω : 0 ≤ omegaConst) {c : ℝ} (hc : 0 ≤ c) {N : ℕ} (hN : 2 ≤ N)
    (h : c * HL N < (R N : ℝ)) : 0 < JR (Fc c) N := by
  have h1 := HL_ge hω hN
  have h2 := mul_le_mul_of_nonneg_left h1 hc
  unfold JR Fc
  linarith

/-- `J_R(N) > 0` for `F_c` implies `R(2N) ≥ 1`. -/
theorem R_pos_of_JR_Fc_pos (hω : 0 ≤ omegaConst) {c : ℝ} (hc : 0 ≤ c) {N : ℕ} (hN : 2 ≤ N)
    (h : 0 < JR (Fc c) N) : 0 < R N := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hx : 0 ≤ (2 * (N : ℝ) - 4) / Real.log (2 * (N : ℝ)) ^ 2 :=
    div_nonneg (by linarith) (by positivity)
  have h3 : 0 ≤ c * (omegaConst * ((2 * (N : ℝ) - 4) / Real.log (2 * (N : ℝ)) ^ 2)) :=
    mul_nonneg hc (mul_nonneg hω hx)
  unfold JR Fc at h
  have h4 : (0 : ℝ) < (R N : ℝ) := by linarith
  exact_mod_cast h4

end PigeonGoldbach.Centered
