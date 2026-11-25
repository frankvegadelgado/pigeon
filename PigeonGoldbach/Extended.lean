module

public import Mathlib
public import PigeonGoldbach.Core

@[expose] public section

/-!
# The extended sets with `M = 0`

The sets `A_N`, `C_N`, `D_N`, `E_N` of the paper start at `M = 1`, which gives distinct primes
`N - M < N + M`. Allowing `M = 0` adds the diagonal `p = q = N`. This module defines the
extended sets and proves the relations used in the paper:

* `zero_mem_CDext_iff`: `0 ∈ C̄_N ∩ D̄_N` if and only if `N` is prime;
* `zero_mem_Eext_iff`: `0 ∈ Ē_N` if and only if `N` is an odd prime;
* `Rext_eq`: `R̄(2N) = R(2N) + 1` if `N` is prime and `R̄(2N) = R(2N)` otherwise.
-/

namespace PigeonGoldbach.Extended

open scoped Classical

open PigeonGoldbach.Core

/-- `Ā_N = {0, 1, ..., N - 3}`. -/
def Aext (N : ℕ) : Finset ℕ := Finset.Icc 0 (N - 3)

/-- `C̄_N = {M ∈ Ā_N : N - M is prime}`. -/
noncomputable def Cext (N : ℕ) : Finset ℕ := (Aext N).filter fun M => (N - M).Prime

/-- `D̄_N = {M ∈ Ā_N : N + M is prime}`. -/
noncomputable def Dext (N : ℕ) : Finset ℕ := (Aext N).filter fun M => (N + M).Prime

/-- `Ē_N`: half-differences `(Q - P)/2` of odd primes `P ≤ N ≤ Q < 2N`. -/
noncomputable def Eext (N : ℕ) : Finset ℕ :=
  (Aext N).filter fun M =>
    ∃ P Q : ℕ, P.Prime ∧ Q.Prime ∧ 2 < P ∧ P ≤ N ∧ N ≤ Q ∧ Q < 2 * N ∧ P + 2 * M = Q

/-- `R̄(2N) = |C̄_N ∩ D̄_N|`. -/
noncomputable def Rext (N : ℕ) : ℕ := (Cext N ∩ Dext N).card

theorem zero_mem_CDext_iff (N : ℕ) : 0 ∈ Cext N ∩ Dext N ↔ N.Prime := by
  simp [Cext, Dext, Aext]

theorem zero_mem_Eext_iff (N : ℕ) : 0 ∈ Eext N ↔ N.Prime ∧ 2 < N := by
  simp only [Eext, Aext, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨_, P, Q, hP, hQ, h2, hPN, hNQ, hQ2, h⟩
    have hPN' : P = N := by omega
    exact ⟨hPN' ▸ hP, by omega⟩
  · rintro ⟨hN, h2⟩
    exact ⟨⟨Nat.zero_le _, Nat.zero_le _⟩, N, N, hN, hN, h2, le_rfl, le_rfl, by omega, by omega⟩

theorem CDext_eq (N : ℕ) :
    Cext N ∩ Dext N = if N.Prime then insert 0 (C N ∩ D N) else C N ∩ D N := by
  split_ifs with hN
  · ext M
    simp only [Cext, Dext, Aext, C, D, A, Finset.mem_inter, Finset.mem_filter, Finset.mem_Icc,
      Finset.mem_insert]
    by_cases hM : M = 0
    · subst hM
      simp [hN]
    · have h1 : 1 ≤ M := Nat.pos_of_ne_zero hM
      constructor
      · rintro ⟨⟨⟨_, h2⟩, h3⟩, ⟨⟨_, _⟩, h4⟩⟩
        exact Or.inr ⟨⟨⟨h1, h2⟩, h3⟩, ⟨⟨h1, h2⟩, h4⟩⟩
      · rintro (h | ⟨⟨⟨_, h2⟩, h3⟩, ⟨⟨_, _⟩, h4⟩⟩)
        · exact absurd h hM
        · exact ⟨⟨⟨Nat.zero_le _, h2⟩, h3⟩, ⟨⟨Nat.zero_le _, h2⟩, h4⟩⟩
  · ext M
    simp only [Cext, Dext, Aext, C, D, A, Finset.mem_inter, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨⟨_, h2⟩, h3⟩, ⟨⟨_, _⟩, h4⟩⟩
      have h1 : 1 ≤ M := by
        by_contra hlt
        have hM : M = 0 := by omega
        subst hM
        exact hN (by simpa using h3)
      exact ⟨⟨⟨h1, h2⟩, h3⟩, ⟨⟨h1, h2⟩, h4⟩⟩
    · rintro ⟨⟨⟨h1, h2⟩, h3⟩, ⟨⟨_, _⟩, h4⟩⟩
      exact ⟨⟨⟨Nat.zero_le _, h2⟩, h3⟩, ⟨⟨Nat.zero_le _, h2⟩, h4⟩⟩

theorem Rext_eq (N : ℕ) : Rext N = R N + if N.Prime then 1 else 0 := by
  unfold Rext
  rw [CDext_eq]
  split_ifs with hN
  · have h0 : 0 ∉ C N ∩ D N := by simp [C, D, A]
    rw [Finset.card_insert_of_notMem h0]
    rfl
  · rfl

/-- For `N ≥ 4`, `2N` is a sum of two primes if and only if `C̄_N ∩ D̄_N` is nonempty. -/
theorem classical_iff_Rext {N : ℕ} (hN : 4 ≤ N) :
    (∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = 2 * N) ↔ 0 < Rext N := by
  rw [Rext_eq, classical_iff_distinct N]
  constructor
  · rintro (h | ⟨p, q, hp, hq, hne, hs⟩)
    · simp [h]
    · have hlt : p < q ∨ q < p := lt_or_gt_of_ne hne
      have hpos : 0 < R N := by
        rw [R, Finset.card_pos]
        rcases hlt with hlt | hlt
        · have := centered_of_lt hp hq hlt hs hN
          refine ⟨N - p, ?_⟩
          simp only [Finset.mem_inter, mem_C, mem_D]
          obtain ⟨a, b, c, d⟩ := this
          exact ⟨⟨⟨a, b⟩, c⟩, ⟨⟨a, b⟩, d⟩⟩
        · have := centered_of_lt hq hp hlt (by omega) hN
          refine ⟨N - q, ?_⟩
          simp only [Finset.mem_inter, mem_C, mem_D]
          obtain ⟨a, b, c, d⟩ := this
          exact ⟨⟨⟨a, b⟩, c⟩, ⟨⟨a, b⟩, d⟩⟩
      exact lt_of_lt_of_le hpos (Nat.le_add_right _ _)
  · intro h
    by_cases hP : N.Prime
    · exact Or.inl hP
    · have hR : 0 < R N := by simpa [hP] using h
      rw [R, Finset.card_pos] at hR
      obtain ⟨M, hM⟩ := hR
      rw [Finset.mem_inter, mem_C, mem_D] at hM
      obtain ⟨⟨⟨h1, h2⟩, h3⟩, ⟨_, h4⟩⟩ := hM
      exact Or.inr ⟨N - M, N + M, h3, h4, by omega, by omega⟩

end PigeonGoldbach.Extended
