module

public import Mathlib
public import PigeonGoldbach.Core
public import PigeonGoldbach.CitedResults

@[expose] public section

/-!
# Recent results used as explicit hypotheses

This module states what the paper uses from the following works, as hypotheses (propositions,
not axioms), and proves what follows from them.

* J. Pintz and I. Althöfer, *The Goldbach exceptional set: an exponent of 7/12 and conditional
  refinements*, arXiv:2610.15559v1 (11 October 2026): `PintzAlthoferTheorem1`,
  `PintzAlthoferTheorem3`.
* D. R. Johnston and T. Trudgian, *An update on the Linnik--Goldbach problem*,
  arXiv:2605.17825v2 (22 July 2026): `GoldbachUpperBound` (their Proposition 1 with
  `C = 6.7814`, and Proposition 3 with `C = 4` under the Elliott--Halberstam conjecture),
  `JohnstonTrudgianTheorem1`.
* G. Bhowmik and L. Grimmelt, *The exceptional set of the Goldbach problem*, arXiv:2607.27282v2
  (13 August 2026): `HardyLittlewoodConditional` (Theorem 3.1), `ChudakovVdCEstermann`
  (Theorem 4.3), `MontgomeryVaughan` (Theorem 5.1) and `PintzUnconditional` (Proposition 6.4).
* L. Alpöge, Lean proof of the Riemann hypothesis and of its generalization to Dirichlet
  `L`-functions, released 20 November 2026 (certified by the Lean FRO and the Mathlib
  Initiative): the statement `ZeroFreeHalfPlane (1/2)` below, taken as a hypothesis.

The reductions proved here are elementary: the exponent arithmetic, the comparison of the
exceptional sets for sums of two primes and of two distinct primes, the bound
`2 R(2N) ≤ G(2N)` for the number `R` of centered partitions, and the monotonicity of the
Linnik--Goldbach statement in the number of powers of two.
-/

namespace PigeonGoldbach.Preprints

open scoped Classical

open PigeonGoldbach.Core PigeonGoldbach.CitedResults

/-! ### Exponent arithmetic of Pintz--Althöfer -/

/-- `g(θ) = θ (5 - 4 θ) / (2 (2 - θ))`. -/
noncomputable def gExp (θ : ℝ) : ℝ := θ * (5 - 4 * θ) / (2 * (2 - θ))

theorem gExp_eq {θ : ℝ} (h : θ ≠ 2) :
    gExp θ = 2 * θ - 3 / 2 + 3 * (1 - θ) / (2 - θ) := by
  have h2 : (2 : ℝ) - θ ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  unfold gExp
  field_simp
  ring

theorem gExp_two_thirds : gExp (2 / 3) = 7 / 12 := by
  unfold gExp; norm_num

theorem gExp_half : gExp (1 / 2) = 1 / 2 := by
  unfold gExp; norm_num

theorem gExp_five_eighths : gExp (5 / 8) = 25 / 44 := by
  unfold gExp; norm_num

theorem seven_twelfths_sub : (7 : ℝ) / 12 - 25 / 44 = 1 / 66 := by norm_num

/-- The exponents `2 * (19/24) - 1` and `2 * (4/5) - 1` of the introduction. -/
theorem exponent_pairs : 2 * ((19 : ℝ) / 24) - 1 = 7 / 12 ∧ 2 * ((4 : ℝ) / 5) - 1 = 3 / 5 := by
  constructor <;> norm_num

/-- `g` is strictly increasing on `[1/2, 2/3]`. -/
theorem gExp_strictMonoOn : StrictMonoOn gExp (Set.Icc (1 / 2 : ℝ) (2 / 3)) := by
  intro a ha b hb hab
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  have hA : (2 : ℝ) - a ≠ 0 := by intro h; linarith
  have hB : (2 : ℝ) - b ≠ 0 := by intro h; linarith
  have hpos : 0 < (2 - a) * (2 - b) := by
    apply mul_pos <;> linarith
  have key : 16 / 9 ≤ (2 - a) * (2 - b) := by
    have h1 : 0 ≤ (2 - a) - 4 / 3 := by linarith
    have h2 : 0 ≤ (2 - b) - 4 / 3 := by linarith
    nlinarith [mul_nonneg h1 h2]
  have hdiff : gExp b - gExp a =
      (b - a) * (4 * ((2 - a) * (2 - b)) - 6) / (2 * ((2 - a) * (2 - b))) := by
    unfold gExp
    field_simp
    ring
  have : 0 < gExp b - gExp a := by
    rw [hdiff]
    apply div_pos
    · apply mul_pos
      · linarith
      · linarith
    · linarith
  linarith

/-! ### Exceptional sets -/

/-- The even integers `4 ≤ n ≤ X` that are not a sum of two primes (the primes may be equal). -/
noncomputable def goldbachExceptional (X : ℕ) : Finset ℕ :=
  (Finset.Icc 4 X).filter fun n => n % 2 = 0 ∧ ¬ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = n

/-- The even integers `4 ≤ n ≤ X` that are not a sum of two distinct primes. -/
noncomputable def distinctExceptional (X : ℕ) : Finset ℕ :=
  (Finset.Icc 4 X).filter fun n =>
    n % 2 = 0 ∧ ¬ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ p + q = n

/-- `E(X) ≪_ε X^(e + ε)`. -/
def ExceptionalBound (e : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ (C : ℝ) (X0 : ℕ), ∀ X : ℕ, X0 ≤ X →
    ((goldbachExceptional X).card : ℝ) ≤ C * (X : ℝ) ^ (e + ε)

theorem ExceptionalBound.mono {e e' : ℝ} (H : ExceptionalBound e) (hee : e ≤ e') :
    ExceptionalBound e' := by
  intro ε hε
  obtain ⟨C, X0, h⟩ := H ε hε
  refine ⟨|C|, max X0 1, ?_⟩
  intro X hX
  have hX1 : (1 : ℝ) ≤ X := by
    have : 1 ≤ X := le_trans (le_max_right _ _) hX
    exact_mod_cast this
  have hX0 : X0 ≤ X := le_trans (le_max_left _ _) hX
  calc ((goldbachExceptional X).card : ℝ) ≤ C * (X : ℝ) ^ (e + ε) := h X hX0
    _ ≤ |C| * (X : ℝ) ^ (e + ε) :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg (by linarith) _)
    _ ≤ |C| * (X : ℝ) ^ (e' + ε) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)) (abs_nonneg C)

/-- `H_θ`: every nontrivial zero `0 < Re s < 1` of the `L`-function of every primitive
Dirichlet character (the character modulo `1` gives `ζ`) has real part at most `θ`.
For `θ = 1/2` this is the generalized Riemann hypothesis. -/
def ZeroFreeHalfPlane (θ : ℝ) : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
    ∀ s : ℂ, 0 < s.re → s.re < 1 → χ.LFunction s = 0 → s.re ≤ θ

theorem ZeroFreeHalfPlane.mono {θ θ' : ℝ} (H : ZeroFreeHalfPlane θ) (h : θ ≤ θ') :
    ZeroFreeHalfPlane θ' := by
  intro q _ χ hχ s h0 h1 hz
  exact le_trans (H q χ hχ s h0 h1 hz) h

/-- Cited: Pintz--Althöfer, Theorem 1: `H_{θ0}` for a fixed `1/2 ≤ θ0 < 1` gives
`E(X) ≪ X^(7/12 + ε)`. -/
def PintzAlthoferTheorem1 : Prop :=
  ∀ θ0 : ℝ, 1 / 2 ≤ θ0 → θ0 < 1 → ZeroFreeHalfPlane θ0 → ExceptionalBound (7 / 12)

/-- Cited: Pintz--Althöfer, Theorem 3: `H_θ` with `1/2 ≤ θ ≤ 2/3` gives
`E(X) ≪ X^(g(θ) + ε)`. -/
def PintzAlthoferTheorem3 : Prop :=
  ∀ θ : ℝ, 1 / 2 ≤ θ → θ ≤ 2 / 3 → ZeroFreeHalfPlane θ → ExceptionalBound (gExp θ)

/-- The generalized Riemann hypothesis for Dirichlet `L`-functions (Alpöge, 2026), taken as a
hypothesis. -/
def GRHDirichlet : Prop := ZeroFreeHalfPlane (1 / 2)

theorem exceptional_seven_twelfths (h1 : PintzAlthoferTheorem1) (G : GRHDirichlet) :
    ExceptionalBound (7 / 12) :=
  h1 (1 / 2) le_rfl (by norm_num) G

theorem exceptional_half (h3 : PintzAlthoferTheorem3) (G : GRHDirichlet) :
    ExceptionalBound (1 / 2) := by
  have := h3 (1 / 2) le_rfl (by norm_num) G
  rwa [gExp_half] at this

/-- Cited: Bhowmik--Grimmelt, Theorem 3.1 (Hardy--Littlewood): if every zero of every Dirichlet
`L`-function has real part at most `Θ < 3/4`, then `E(X) ≪_ε X^(2 Θ - 1/2 + ε)`. -/
def HardyLittlewoodConditional : Prop :=
  ∀ θ : ℝ, 1 / 2 ≤ θ → θ < 3 / 4 → ZeroFreeHalfPlane θ → ExceptionalBound (2 * θ - 1 / 2)

/-- The exponent `1/2` from `H_{1/2}` and the bound of Hardy and Littlewood. -/
theorem exceptional_half_of_HL (h : HardyLittlewoodConditional) (G : GRHDirichlet) :
    ExceptionalBound (1 / 2) :=
  (h (1 / 2) le_rfl (by norm_num) G).mono (by norm_num)

/-- Cited: Chudakov, van der Corput and Estermann (Bhowmik--Grimmelt, Theorem 4.3): for every
`A > 0`, `E(X) ≪_A X (log X)^(-A)`. -/
def ChudakovVdCEstermann : Prop :=
  ∀ A : ℝ, 0 < A → ∃ (C : ℝ) (X0 : ℕ), ∀ X : ℕ, X0 ≤ X →
    ((goldbachExceptional X).card : ℝ) ≤ C * (X : ℝ) * Real.log (X : ℝ) ^ (-A)

/-- Cited: Montgomery and Vaughan (Bhowmik--Grimmelt, Theorem 5.1): there is `δ > 0` with
`E(X) ≪ X^(1 - δ)`. -/
def MontgomeryVaughan : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∃ (C : ℝ) (X0 : ℕ), ∀ X : ℕ, X0 ≤ X →
    ((goldbachExceptional X).card : ℝ) ≤ C * (X : ℝ) ^ (1 - δ)

/-- Cited: Pintz (Bhowmik--Grimmelt, Proposition 6.4): `E(X) < X^0.72` for all sufficiently
large `X` (with an ineffective constant). -/
def PintzUnconditional : Prop :=
  ∃ X0 : ℕ, ∀ X : ℕ, X0 ≤ X → ((goldbachExceptional X).card : ℝ) < (X : ℝ) ^ (0.72 : ℝ)

/-- For `N` not prime, `2N` is a sum of two primes if and only if it is a sum of two
distinct primes. -/
theorem classical_iff_distinct_of_not_prime {N : ℕ} (hN : ¬ N.Prime) :
    (∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = 2 * N) ↔
      ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ p + q = 2 * N := by
  rw [classical_iff_distinct N]
  constructor
  · rintro (h | h)
    · exact absurd h hN
    · exact h
  · intro h
    exact Or.inr h

theorem goldbachExceptional_subset_distinct (X : ℕ) :
    goldbachExceptional X ⊆ distinctExceptional X := by
  intro n hn
  simp only [goldbachExceptional, distinctExceptional, Finset.mem_filter] at hn ⊢
  obtain ⟨hI, he, hne⟩ := hn
  refine ⟨hI, he, ?_⟩
  rintro ⟨p, q, hp, hq, _, hs⟩
  exact hne ⟨p, q, hp, hq, hs⟩

/-- The two exceptional sets differ only by integers `2p` with `p` prime. -/
theorem distinctExceptional_subset (X : ℕ) :
    distinctExceptional X ⊆
      goldbachExceptional X ∪ ((Finset.Icc 1 (X / 2)).filter Nat.Prime).image (fun p => 2 * p) := by
  intro n hn
  simp only [distinctExceptional, Finset.mem_filter, Finset.mem_Icc] at hn
  obtain ⟨⟨h4, hX⟩, he, hnd⟩ := hn
  rw [Finset.mem_union]
  by_cases hc : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = n
  · right
    obtain ⟨N, rfl⟩ : ∃ N, n = 2 * N := ⟨n / 2, by omega⟩
    have hcl : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = 2 * N := hc
    rcases (classical_iff_distinct N).mp hcl with hP | hd
    · rw [Finset.mem_image]
      refine ⟨N, ?_, rfl⟩
      rw [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hP.one_lt.le, by omega⟩, hP⟩
    · exact absurd hd hnd
  · left
    simp only [goldbachExceptional, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨h4, hX⟩, he, hc⟩

theorem card_distinctExceptional_le (X : ℕ) :
    (distinctExceptional X).card ≤ (goldbachExceptional X).card + piCount (X / 2) := by
  calc (distinctExceptional X).card
      ≤ (goldbachExceptional X ∪
          ((Finset.Icc 1 (X / 2)).filter Nat.Prime).image (fun p => 2 * p)).card :=
        Finset.card_le_card (distinctExceptional_subset X)
    _ ≤ (goldbachExceptional X).card +
          (((Finset.Icc 1 (X / 2)).filter Nat.Prime).image (fun p => 2 * p)).card :=
        Finset.card_union_le _ _
    _ ≤ (goldbachExceptional X).card + piCount (X / 2) := by
        apply Nat.add_le_add_left
        exact Finset.card_image_le

/-- The integers `N ∈ [4, X]` with `R(2N) = 0` give distinct elements `2N` of the exceptional set
for sums of two distinct primes up to `2X`. -/
theorem cnt_add_distinctExceptional (X : ℕ) :
    X ≤ cnt X + (distinctExceptional (2 * X)).card + 3 := by
  have hsub : Finset.Icc 4 X ⊆ ((Finset.Icc 4 X).filter fun N => 1 ≤ R N) ∪
      ((Finset.Icc 4 X).filter fun N => ¬ 1 ≤ R N) := by
    intro N hN
    by_cases h : 1 ≤ R N
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hN, h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hN, h⟩)
  have h1 : (Finset.Icc 4 X).card ≤ cnt X +
      ((Finset.Icc 4 X).filter fun N => ¬ 1 ≤ R N).card :=
    (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have h2 : ((Finset.Icc 4 X).filter fun N => ¬ 1 ≤ R N).card ≤
      (distinctExceptional (2 * X)).card := by
    refine Finset.card_le_card_of_injOn (fun N => 2 * N) ?_ ?_
    · intro N hN
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hN
      simp only [Finset.mem_coe, distinctExceptional, Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨by omega, by omega⟩, by omega, ?_⟩
      rintro ⟨p, q, hp, hq, hpq, hs⟩
      have hne : (C N ∩ D N).Nonempty :=
        (centered_intersection_criterion hN.1.1).1 ⟨p, q, hp, hq, hpq, hs⟩
      exact hN.2 (Finset.card_pos.2 hne)
    · intro a _ b _ hab
      have : 2 * a = 2 * b := hab
      omega
  have h3 : (Finset.Icc 4 X).card = X + 1 - 4 := Nat.card_Icc 4 X
  omega

/-- Under the bound `E(X) ≪_ε X^(1/2 + ε)`, the number of `N ≤ X` with `R(2N) ≥ 1` is at least
`X - 3 - π(X) - C (2X)^(1/2 + ε)`. -/
theorem cnt_lower_of_exceptional (H : ExceptionalBound (1 / 2)) {ε : ℝ} (hε : 0 < ε) :
    ∃ (C : ℝ) (X0 : ℕ), ∀ X : ℕ, X0 ≤ X →
      (X : ℝ) - 3 - (piCount X : ℝ) - C * ((2 * X : ℕ) : ℝ) ^ (1 / 2 + ε) ≤ (cnt X : ℝ) := by
  obtain ⟨C, X0, h⟩ := H ε hε
  refine ⟨C, X0, fun X hX => ?_⟩
  have h1 := cnt_add_distinctExceptional X
  have h2 := card_distinctExceptional_le (2 * X)
  have h3 := h (2 * X) (by omega)
  have h4 : 2 * X / 2 = X := by omega
  rw [h4] at h2
  have h5 : (X : ℝ) ≤ (cnt X : ℝ) + ((distinctExceptional (2 * X)).card : ℝ) + 3 := by
    exact_mod_cast h1
  have h6 : ((distinctExceptional (2 * X)).card : ℝ) ≤
      ((goldbachExceptional (2 * X)).card : ℝ) + (piCount X : ℝ) := by
    exact_mod_cast h2
  linarith

/-! ### Upper bounds for prime pairs (Lichtman; Johnston--Trudgian) -/

/-- `G(n)`: the number of ordered pairs of primes `2 < p₁, p₂ < n` with `p₁ + p₂ = n`. -/
noncomputable def Gcount (n : ℕ) : ℕ :=
  ((Finset.Ioo 2 n ×ˢ Finset.Ioo 2 n).filter fun x => x.1.Prime ∧ x.2.Prime ∧ x.1 + x.2 = n).card

/-- Cited: for every `ε > 0` and all sufficiently large even `n`,
`G(n) ≤ (C + ε) ω κ(n) n / log² n`, with `C = 6.7814` (Lichtman, Johnston--Trudgian
Proposition 1) and `C = 4` under the Elliott--Halberstam conjecture (Proposition 3). -/
def GoldbachUpperBound (C : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → n % 2 = 0 →
    (Gcount n : ℝ) ≤ (C + ε) * omegaConst * ((n : ℝ) / Real.log n ^ 2) * kappa n

/-- `2 R(2N) ≤ G(2N)`: each centered partition `N - M, N + M` gives two ordered pairs. -/
theorem two_mul_R_le_G (N : ℕ) : 2 * R N ≤ Gcount (2 * N) := by
  set S := C N ∩ D N with hS
  have hmem : ∀ M ∈ S, 1 ≤ M ∧ M + 3 ≤ N ∧ (N - M).Prime ∧ (N + M).Prime := by
    intro M hM
    rw [hS, Finset.mem_inter, mem_C, mem_D] at hM
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, ⟨_, h4⟩⟩ := hM
    refine ⟨h1, ?_, h3, h4⟩
    have : 3 ≤ N := by
      by_contra hlt
      have : N - 3 = 0 := by omega
      omega
    omega
  let f1 : ℕ → ℕ × ℕ := fun M => (N - M, N + M)
  let f2 : ℕ → ℕ × ℕ := fun M => (N + M, N - M)
  have hf1 : Set.InjOn f1 S := by
    intro a ha b hb h
    have ha' := hmem a ha
    have hb' := hmem b hb
    have := congrArg Prod.fst h
    simp only [f1] at this
    omega
  have hf2 : Set.InjOn f2 S := by
    intro a ha b hb h
    have ha' := hmem a ha
    have hb' := hmem b hb
    have := congrArg Prod.fst h
    simp only [f2] at this
    omega
  have hdisj : Disjoint (S.image f1) (S.image f2) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    rw [Finset.mem_image] at hx1 hx2
    obtain ⟨a, ha, rfl⟩ := hx1
    obtain ⟨b, hb, hab⟩ := hx2
    have ha' := hmem a ha
    have hb' := hmem b hb
    have h1 := congrArg Prod.fst hab
    simp only [f1, f2] at h1
    omega
  have hsub : S.image f1 ∪ S.image f2 ⊆
      (Finset.Ioo 2 (2 * N) ×ˢ Finset.Ioo 2 (2 * N)).filter
        fun x => x.1.Prime ∧ x.2.Prime ∧ x.1 + x.2 = 2 * N := by
    intro x hx
    rw [Finset.mem_union, Finset.mem_image, Finset.mem_image] at hx
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_Ioo, Finset.mem_Ioo]
    rcases hx with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩
    · have ha' := hmem a ha
      simp only [f1]
      refine ⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩, ha'.2.2.1, ha'.2.2.2, by omega⟩
    · have ha' := hmem a ha
      simp only [f2]
      refine ⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩, ha'.2.2.2, ha'.2.2.1, by omega⟩
  have hcard : (S.image f1 ∪ S.image f2).card = 2 * S.card := by
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injOn hf1,
      Finset.card_image_of_injOn hf2]
    ring
  calc 2 * R N = 2 * S.card := rfl
    _ = (S.image f1 ∪ S.image f2).card := hcard.symm
    _ ≤ Gcount (2 * N) := Finset.card_le_card hsub

/-- Consequence for the number `R(2N)` of centered partitions: for every `ε > 0` and all
large `N`, `2 R(2N) ≤ (C + ε) ω κ(2N) (2N) / log²(2N)`. -/
theorem R_upper_of_goldbach_upper {C : ℝ} (H : GoldbachUpperBound C) :
    ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      2 * (R N : ℝ) ≤
        (C + ε) * omegaConst * (((2 * N : ℕ) : ℝ) / Real.log ((2 * N : ℕ) : ℝ) ^ 2) *
          kappa (2 * N) := by
  intro ε hε
  obtain ⟨n0, h⟩ := H ε hε
  refine ⟨n0, fun N hN => ?_⟩
  have h1 := h (2 * N) (by omega) (by omega)
  have h2 : (2 * R N : ℕ) ≤ Gcount (2 * N) := two_mul_R_le_G N
  have h3 : (2 * (R N : ℝ)) ≤ (Gcount (2 * N) : ℝ) := by exact_mod_cast h2
  exact le_trans h3 h1

/-! ### The Linnik--Goldbach problem -/

/-- Every sufficiently large even `n` is `p + q + 2^(ν₁) + ⋯ + 2^(ν_K)` with `p, q` prime. -/
def LinnikGoldbach (K : ℕ) : Prop :=
  ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → n % 2 = 0 →
    ∃ (p q : ℕ) (ν : Fin K → ℕ), p.Prime ∧ q.Prime ∧ n = p + q + ∑ i, 2 ^ ν i

theorem LinnikGoldbach.succ {K : ℕ} (H : LinnikGoldbach K) : LinnikGoldbach (K + 1) := by
  obtain ⟨n0, h⟩ := H
  refine ⟨n0 + 2, fun n hn he => ?_⟩
  obtain ⟨p, q, ν, hp, hq, hs⟩ := h (n - 2) (by omega) (by omega)
  refine ⟨p, q, (Fin.cons 1 ν : Fin (K + 1) → ℕ), hp, hq, ?_⟩
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, pow_one]
  omega

/-- Cited: Johnston--Trudgian, Theorem 1: under the generalized Riemann hypothesis every
sufficiently large even integer is the sum of two primes and six powers of two. -/
def JohnstonTrudgianTheorem1 : Prop := GRHDirichlet → LinnikGoldbach 6

theorem linnik_six (J : JohnstonTrudgianTheorem1) (G : GRHDirichlet) : LinnikGoldbach 6 :=
  J G

theorem linnik_seven (J : JohnstonTrudgianTheorem1) (G : GRHDirichlet) : LinnikGoldbach 7 :=
  (J G).succ

/-- The six-power representation `n = p + q + 2^ν₁ + ⋯ + 2^ν₆`. -/
def SixPowerRep (n : ℕ) : Prop :=
  ∃ (p q : ℕ) (ν : Fin 6 → ℕ), p.Prime ∧ q.Prime ∧ n = p + q + ∑ i, 2 ^ ν i

/-- Below the verified range the six-power representation needs no analytic input:
for every even `n` with `10 ≤ n ≤ 4·10¹⁸ + 6`, a Goldbach partition of `n - 6` and six
powers `2⁰ = 1` give `n = p + q + 6`. -/
theorem sixPowerRep_of_verification (hV : GoldbachVerification) {n : ℕ} (h10 : 10 ≤ n)
    (hn : n ≤ 4 * 10 ^ 18 + 6) (he : n % 2 = 0) : SixPowerRep n := by
  obtain ⟨p, hp, _, hq⟩ := hV (n - 6) (by omega) (by omega) (by omega)
  have h2 := hq.two_le
  refine ⟨p, n - 6 - p, fun _ => 0, hp, hq, ?_⟩
  simp only [pow_zero, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    mul_one]
  omega

/-- The six-power representation holds for all even `n ≥ 10` outside the interval
`(4·10¹⁸ + 6, n₀)`, given the verification and a threshold `n₀` for the cited theorem. -/
theorem sixPowerRep_outside_gap (hV : GoldbachVerification) {n0 : ℕ}
    (h : ∀ n : ℕ, n0 ≤ n → n % 2 = 0 → SixPowerRep n) {n : ℕ} (h10 : 10 ≤ n)
    (he : n % 2 = 0) (hn : n ≤ 4 * 10 ^ 18 + 6 ∨ n0 ≤ n) : SixPowerRep n := by
  rcases hn with hn | hn
  · exact sixPowerRep_of_verification hV h10 hn he
  · exact h n hn he

/-- If the threshold `n₀` is at most `4·10¹⁸ + 7`, every even `n ≥ 10` has the representation. -/
theorem sixPowerRep_complete (hV : GoldbachVerification) {n0 : ℕ}
    (hn0 : n0 ≤ 4 * 10 ^ 18 + 7) (h : ∀ n : ℕ, n0 ≤ n → n % 2 = 0 → SixPowerRep n) {n : ℕ}
    (h10 : 10 ≤ n) (he : n % 2 = 0) : SixPowerRep n := by
  apply sixPowerRep_outside_gap hV h h10 he
  by_cases hle : n ≤ 4 * 10 ^ 18 + 6
  · exact Or.inl hle
  · exact Or.inr (by omega)

/-- Six equal powers of two reach beyond the verified range: for every even `n` with
`4·10¹⁸ + 8 ≤ n ≤ 8·10¹⁸ - 4` there is `k` with `n - 6·2^k` in `[4, 4·10¹⁸]`, so the
verification gives `n = p + q + 6·2^k` with six equal powers `2^k`. -/
theorem sixPowerRep_equal_powers (hV : GoldbachVerification) {n : ℕ}
    (hn1 : 4 * 10 ^ 18 + 8 ≤ n) (hn2 : n ≤ 8 * 10 ^ 18 - 4) (he : n % 2 = 0) :
    SixPowerRep n := by
  have hex : ∃ k : ℕ, n - 4 * 10 ^ 18 ≤ 6 * 2 ^ k := by
    refine ⟨n, ?_⟩
    have h := @Nat.lt_two_pow_self n
    omega
  obtain ⟨j, hj⟩ : ∃ j : ℕ, Nat.find hex = j + 1 := by
    refine ⟨Nat.find hex - 1, ?_⟩
    have hk0 : Nat.find hex ≠ 0 := by
      intro h0
      have hs := Nat.find_spec hex
      rw [h0] at hs
      simp at hs
      omega
    omega
  have hk := Nat.find_spec hex
  rw [hj] at hk
  have hmin : ¬ (n - 4 * 10 ^ 18 ≤ 6 * 2 ^ j) := Nat.find_min hex (by omega)
  have h2 : 2 ^ (j + 1) = 2 * 2 ^ j := by ring
  obtain ⟨P, hP⟩ : ∃ P : ℕ, P = 2 ^ j := ⟨_, rfl⟩
  rw [h2, ← hP] at hk
  rw [← hP] at hmin
  obtain ⟨p, hp, _, hq⟩ := hV (n - 6 * (2 * P)) (by omega) (by omega) (by omega)
  have hq2 := hq.two_le
  refine ⟨p, n - 6 * (2 * P) - p, fun _ => j + 1, hp, hq, ?_⟩
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [h2, ← hP]
  omega

theorem linnikGoldbach_six_iff : LinnikGoldbach 6 ↔
    ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → n % 2 = 0 → SixPowerRep n := Iff.rfl

end PigeonGoldbach.Preprints
