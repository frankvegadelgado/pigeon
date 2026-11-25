module

public import Mathlib

@[expose] public section

/-!
# Nested squares and distinct-prime Goldbach partitions

Elementary statements of the paper: the geometric equivalence (Theorem `thm:geometric`),
the centered intersection criterion (Proposition `prop:intersection`), the half-difference
set `E_N` with `C_N ∩ D_N ⊆ E_N` (Lemma `lem:CD-in-E`), the gap obstructions
(Lemmas `lem:gap` and `lem:gap-top`), the pigeonhole step (Proposition `prop:pigeonhole-CE`),
the count of `C_N`, the baseline supply of half-differences, the step of Proposition
`prop:verified` and the small cases. The analytic results (Mikawa, Siebert, Dusart,
Rosser--Schoenfeld, Ford--Green--Konyagin--Maynard--Tao) are not formalized.
-/

namespace PigeonGoldbach.Core

open scoped Classical

/-- The admissible range `A_N = {1, ..., N - 3}` of the paper. -/
def A (N : ℕ) : Finset ℕ := Finset.Icc 1 (N - 3)

/-- `C_N = {M ∈ A_N : N - M is prime}`. -/
noncomputable def C (N : ℕ) : Finset ℕ := (A N).filter fun M => (N - M).Prime

/-- `D_N = {M ∈ A_N : N + M is prime}`. -/
noncomputable def D (N : ℕ) : Finset ℕ := (A N).filter fun M => (N + M).Prime

/-- The half-difference set `E_N`: the `M ∈ A_N` with `M = (Q - P) / 2` for primes
`2 < P < N < Q < 2N`, written as `P + 2 M = Q`. -/
noncomputable def E (N : ℕ) : Finset ℕ :=
  (A N).filter fun M =>
    ∃ P Q : ℕ, P.Prime ∧ Q.Prime ∧ 2 < P ∧ P < N ∧ N < Q ∧ Q < 2 * N ∧ P + 2 * M = Q

/-- The parity class `B_N = {M ∈ A_N : M ≢ N (mod 2)}`. -/
noncomputable def B (N : ℕ) : Finset ℕ := (A N).filter fun M => M % 2 ≠ N % 2

/-- A semiprime is a product of two primes. -/
def IsSemiprime (n : ℕ) : Prop := ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p * q

theorem mem_A {N M : ℕ} : M ∈ A N ↔ 1 ≤ M ∧ M ≤ N - 3 := by
  simp only [A, Finset.mem_Icc]

theorem mem_C {N M : ℕ} : M ∈ C N ↔ (1 ≤ M ∧ M ≤ N - 3) ∧ (N - M).Prime := by
  simp only [C, A, Finset.mem_filter, Finset.mem_Icc]

theorem mem_D {N M : ℕ} : M ∈ D N ↔ (1 ≤ M ∧ M ≤ N - 3) ∧ (N + M).Prime := by
  simp only [D, A, Finset.mem_filter, Finset.mem_Icc]

theorem mem_E {N M : ℕ} :
    M ∈ E N ↔ (1 ≤ M ∧ M ≤ N - 3) ∧
      ∃ P Q : ℕ, P.Prime ∧ Q.Prime ∧ 2 < P ∧ P < N ∧ N < Q ∧ Q < 2 * N ∧ P + 2 * M = Q := by
  simp only [E, A, Finset.mem_filter, Finset.mem_Icc]

theorem mem_B {N M : ℕ} : M ∈ B N ↔ (1 ≤ M ∧ M ≤ N - 3) ∧ M % 2 ≠ N % 2 := by
  simp only [B, A, Finset.mem_filter, Finset.mem_Icc]

/-- `N^2 - M^2 = (N - M)(N + M)` for `M ≤ N`. -/
theorem area_eq {N M : ℕ} (h : M ≤ N) : N ^ 2 - M ^ 2 = (N - M) * (N + M) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  have h1 : M + k - M = k := by omega
  rw [h1]
  apply Nat.sub_eq_of_eq_add
  ring

theorem odd_of_prime_gt {Q : ℕ} (hp : Q.Prime) (h : 2 < Q) : Q % 2 = 1 := by
  rcases hp.eq_two_or_odd with h' | h' <;> omega

theorem both_odd {N p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hs : p + q = 2 * N)
    (hN : 4 ≤ N) : p % 2 = 1 ∧ q % 2 = 1 := by
  rcases hp.eq_two_or_odd with h | h <;> rcases hq.eq_two_or_odd with h' | h' <;> omega

theorem centered_of_lt {N p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hlt : p < q)
    (hs : p + q = 2 * N) (hN : 4 ≤ N) :
    1 ≤ N - p ∧ N - p ≤ N - 3 ∧ (N - (N - p)).Prime ∧ (N + (N - p)).Prime := by
  obtain ⟨h1, h2⟩ := both_odd hp hq hs hN
  have hp2 := hp.two_le
  have e1 : N - (N - p) = p := by omega
  have e2 : N + (N - p) = q := by omega
  rw [e1, e2]
  exact ⟨by omega, by omega, hp, hq⟩

/-- Theorem `thm:geometric`: (i) `⇔` (ii) and (ii) `⇔` (iii). -/
theorem geometric_equivalence {N : ℕ} (hN : 4 ≤ N) :
    ((∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ p + q = 2 * N) ↔
      ∃ M : ℕ, 1 ≤ M ∧ M ≤ N - 3 ∧ (N - M).Prime ∧ (N + M).Prime) ∧
    ((∃ M : ℕ, 1 ≤ M ∧ M ≤ N - 3 ∧ (N - M).Prime ∧ (N + M).Prime) ↔
      ∃ M : ℕ, 1 ≤ M ∧ M ≤ N - 3 ∧ IsSemiprime (N ^ 2 - M ^ 2)) := by
  constructor
  · constructor
    · rintro ⟨p, q, hp, hq, hne, hs⟩
      rcases Nat.lt_or_ge p q with hlt | hge
      · obtain ⟨a, b, c, d⟩ := centered_of_lt hp hq hlt hs hN
        exact ⟨N - p, a, b, c, d⟩
      · obtain ⟨a, b, c, d⟩ := centered_of_lt hq hp (by omega) (by omega) hN
        exact ⟨N - q, a, b, c, d⟩
    · rintro ⟨M, h1, h2, hP, hQ⟩
      refine ⟨N - M, N + M, hP, hQ, ?_, ?_⟩ <;> omega
  · constructor
    · rintro ⟨M, h1, h2, hP, hQ⟩
      have hM : M ≤ N := by omega
      refine ⟨M, h1, h2, ?_⟩
      unfold IsSemiprime
      refine ⟨N - M, N + M, hP, hQ, ?_⟩
      exact area_eq hM
    · rintro ⟨M, h1, h2, hs⟩
      have hM : M ≤ N := by omega
      have ha : 2 ≤ N - M := by omega
      have hb : 2 ≤ N + M := by omega
      unfold IsSemiprime at hs
      obtain ⟨p, q, hp, hq, hpq0⟩ := hs
      have hpq : (N - M) * (N + M) = p * q := by rw [← area_eq hM]; exact hpq0
      have hdvd : p ∣ (N - M) * (N + M) := Dvd.intro q hpq.symm
      rcases (Nat.Prime.dvd_mul hp).1 hdvd with ⟨a', ha'⟩ | ⟨b', hb'⟩
      · have h3 : p * (a' * (N + M)) = p * q := by
          rw [← hpq, ha']
          ring
        have h4 : a' * (N + M) = q := Nat.eq_of_mul_eq_mul_left hp.pos h3
        rw [← h4] at hq
        rcases Nat.prime_mul_iff.1 hq with ⟨_, h5⟩ | ⟨h5, h6⟩
        · omega
        · refine ⟨M, h1, h2, ?_, h5⟩
          have h7 : N - M = p := by rw [ha', h6, Nat.mul_one]
          rw [h7]
          exact hp
      · have h3 : p * ((N - M) * b') = p * q := by
          rw [← hpq, hb']
          ring
        have h4 : (N - M) * b' = q := Nat.eq_of_mul_eq_mul_left hp.pos h3
        rw [← h4] at hq
        rcases Nat.prime_mul_iff.1 hq with ⟨h5, h6⟩ | ⟨_, h6⟩
        · refine ⟨M, h1, h2, h5, ?_⟩
          have h7 : N + M = p := by rw [hb', h6, Nat.mul_one]
          rw [h7]
          exact hp
        · omega

/-- Proposition `prop:intersection`. -/
theorem centered_intersection_criterion {N : ℕ} (hN : 4 ≤ N) :
    (∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ p + q = 2 * N) ↔ (C N ∩ D N).Nonempty := by
  rw [(geometric_equivalence hN).1]
  constructor
  · rintro ⟨M, h1, h2, hP, hQ⟩
    refine ⟨M, ?_⟩
    rw [Finset.mem_inter, mem_C, mem_D]
    exact ⟨⟨⟨h1, h2⟩, hP⟩, ⟨⟨h1, h2⟩, hQ⟩⟩
  · rintro ⟨M, hM⟩
    rw [Finset.mem_inter, mem_C, mem_D] at hM
    obtain ⟨⟨⟨h1, h2⟩, hP⟩, ⟨_, hQ⟩⟩ := hM
    exact ⟨M, h1, h2, hP, hQ⟩

/-- Lemma `lem:CD-in-E`. -/
theorem CD_subset_E (N : ℕ) : C N ∩ D N ⊆ E N := by
  intro M hM
  rw [Finset.mem_inter, mem_C, mem_D] at hM
  obtain ⟨⟨hA, hP⟩, _, hQ⟩ := hM
  obtain ⟨h1, h2⟩ := hA
  rw [mem_E]
  refine ⟨⟨h1, h2⟩, N - M, N + M, hP, hQ, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-- Lemma `lem:CD-in-E`, second statement: `C_N ∩ E_N ∩ D_N = C_N ∩ D_N`. -/
theorem CED_eq_CD (N : ℕ) : C N ∩ E N ∩ D N = C N ∩ D N := by
  ext M
  simp only [Finset.mem_inter]
  constructor
  · rintro ⟨⟨a, _⟩, c⟩
    exact ⟨a, c⟩
  · rintro ⟨a, c⟩
    exact ⟨⟨a, CD_subset_E N (Finset.mem_inter.2 ⟨a, c⟩)⟩, c⟩

/-- Both centered sets lie in the parity class `B_N` (Section `subsec:setintersection`). -/
theorem C_D_subset_B (N : ℕ) : C N ⊆ B N ∧ D N ⊆ B N := by
  constructor
  · intro M hM
    rw [mem_C] at hM
    obtain ⟨⟨h1, h2⟩, hP⟩ := hM
    have hodd := odd_of_prime_gt hP (by omega)
    rw [mem_B]
    exact ⟨⟨h1, h2⟩, by omega⟩
  · intro M hM
    rw [mem_D] at hM
    obtain ⟨⟨h1, h2⟩, hQ⟩ := hM
    have hodd := odd_of_prime_gt hQ (by omega)
    rw [mem_B]
    exact ⟨⟨h1, h2⟩, by omega⟩

/-- Lemma `lem:gap`: if `p⁻` is the largest prime below `N` and `p⁺` the smallest above `N`,
every `M ∈ E_N` satisfies `p⁺ - p⁻ ≤ 2M`. -/
theorem gap_lower {N pm pp M : ℕ}
    (hbelow : ∀ P : ℕ, P.Prime → P < N → P ≤ pm)
    (habove : ∀ Q : ℕ, Q.Prime → N < Q → pp ≤ Q)
    (hM : M ∈ E N) : pp - pm ≤ 2 * M := by
  rw [mem_E] at hM
  obtain ⟨_, P, Q, hP, hQ, _, hPN, hNQ, _, hPQ⟩ := hM
  have h1 := hbelow P hP hPN
  have h2 := habove Q hQ hNQ
  omega

/-- Lemma `lem:gap`, second statement: every `M ∈ A_N` with `2M < p⁺ - p⁻` is missing from `E_N`. -/
theorem gap_lower_missing {N pm pp M : ℕ}
    (hbelow : ∀ P : ℕ, P.Prime → P < N → P ≤ pm)
    (habove : ∀ Q : ℕ, Q.Prime → N < Q → pp ≤ Q)
    (hA : M ∈ A N) (hsmall : 2 * M < pp - pm) : M ∈ A N \ E N := by
  rw [Finset.mem_sdiff]
  refine ⟨hA, fun hE => ?_⟩
  have := gap_lower hbelow habove hE
  omega

/-- Lemma `lem:gap-top`: if `q` is the largest prime below `2N`, every `M ∈ E_N`
satisfies `2M + 3 ≤ q`. -/
theorem gap_top {N q M : ℕ}
    (hmax : ∀ Q : ℕ, Q.Prime → Q < 2 * N → Q ≤ q)
    (hM : M ∈ E N) : 2 * M + 3 ≤ q := by
  rw [mem_E] at hM
  obtain ⟨_, P, Q, _, hQ, hP2, _, _, hQN, hPQ⟩ := hM
  have h1 := hmax Q hQ hQN
  omega

/-- Lemma `lem:gap-top`, second statement: every `M ∈ A_N` with `q < 2M + 3` is missing from `E_N`. -/
theorem gap_top_missing {N q M : ℕ}
    (hmax : ∀ Q : ℕ, Q.Prime → Q < 2 * N → Q ≤ q)
    (hA : M ∈ A N) (hbig : q < 2 * M + 3) : M ∈ A N \ E N := by
  rw [Finset.mem_sdiff]
  refine ⟨hA, fun hE => ?_⟩
  have := gap_top hmax hE
  omega

/-- The pigeonhole step of Proposition `prop:pigeonhole-CE`. -/
theorem pigeonhole_core {α : Type*} [DecidableEq α] {S T U : Finset α}
    (hT : T ⊆ S) (h : (S \ U).card < T.card) : (T ∩ U).Nonempty := by
  by_contra hne
  rw [Finset.not_nonempty_iff_eq_empty] at hne
  have hsub : T ⊆ S \ U := by
    intro x hx
    rw [Finset.mem_sdiff]
    refine ⟨hT hx, fun hxU => ?_⟩
    have hmem : x ∈ T ∩ U := Finset.mem_inter.2 ⟨hx, hxU⟩
    rw [hne] at hmem
    simp at hmem
  have := Finset.card_le_card hsub
  omega

theorem C_subset_A (N : ℕ) : C N ⊆ A N := fun _ hM => mem_A.2 (mem_C.1 hM).1

/-- Proposition `prop:pigeonhole-CE`, combinatorial form: if `|A_N \ E_N| < |C_N|`
then `C_N ∩ E_N` is nonempty. -/
theorem pigeonhole_CE (N : ℕ) (h : (A N \ E N).card < (C N).card) : (C N ∩ E N).Nonempty :=
  pigeonhole_core (C_subset_A N) h

/-- The map `M ↦ N - M` is a bijection from `C_N` onto the primes `P` with `3 ≤ P ≤ N - 1`. -/
theorem card_C (N : ℕ) :
    (C N).card = ((Finset.Icc 3 (N - 1)).filter Nat.Prime).card := by
  refine Finset.card_nbij' (fun M => N - M) (fun P => N - P) ?_ ?_ ?_ ?_
  · intro M hM
    have hM' : M ∈ C N := by simpa only [Finset.mem_coe] using hM
    rw [mem_C] at hM'
    obtain ⟨⟨h1, h2⟩, hp⟩ := hM'
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨by omega, by omega⟩, hp⟩
  · intro P hP
    have hP' : (3 ≤ P ∧ P ≤ N - 1) ∧ P.Prime := by
      simpa only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] using hP
    obtain ⟨⟨h1, h2⟩, hp⟩ := hP'
    simp only [Finset.mem_coe, mem_C]
    have e : N - (N - P) = P := by omega
    rw [e]
    exact ⟨⟨by omega, by omega⟩, hp⟩
  · intro M hM
    have hM' : M ∈ C N := by simpa only [Finset.mem_coe] using hM
    rw [mem_C] at hM'
    obtain ⟨⟨h1, h2⟩, _⟩ := hM'
    show N - (N - M) = M
    omega
  · intro P hP
    have hP' : (3 ≤ P ∧ P ≤ N - 1) ∧ P.Prime := by
      simpa only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] using hP
    obtain ⟨⟨h1, h2⟩, _⟩ := hP'
    show N - (N - P) = P
    omega

/-- Corollary `cor:half-difference-baseline`, combinatorial form: every prime `Q` with
`N < Q ≤ 2N - 3` gives the distinct element `(Q - 3) / 2` of `E_N`. -/
theorem card_E_ge {N : ℕ} (hN : 4 ≤ N) :
    ((Finset.Ioc N (2 * N - 3)).filter Nat.Prime).card ≤ (E N).card := by
  refine Finset.card_le_card_of_injOn (fun Q => (Q - 3) / 2) ?_ ?_
  · intro Q hQ
    have hQ' : (N < Q ∧ Q ≤ 2 * N - 3) ∧ Q.Prime := by
      simpa only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ioc] using hQ
    obtain ⟨⟨h1, h2⟩, hp⟩ := hQ'
    have hodd := odd_of_prime_gt hp (by omega)
    simp only [Finset.mem_coe, mem_E]
    exact ⟨⟨by omega, by omega⟩, 3, Q, Nat.prime_three, hp, by omega, by omega, h1,
      by omega, by omega⟩
  · intro Q hQ Q' hQ' h
    have h' : (Q - 3) / 2 = (Q' - 3) / 2 := h
    have hq1 : (N < Q ∧ Q ≤ 2 * N - 3) ∧ Q.Prime := by
      simpa only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ioc] using hQ
    have hq2 : (N < Q' ∧ Q' ≤ 2 * N - 3) ∧ Q'.Prime := by
      simpa only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ioc] using hQ'
    obtain ⟨⟨a1, a2⟩, ap⟩ := hq1
    obtain ⟨⟨b1, b2⟩, bp⟩ := hq2
    have o1 := odd_of_prime_gt ap (by omega)
    have o2 := odd_of_prime_gt bp (by omega)
    omega

/-- Corollary `cor:goldbach-diff`, second statement: for a prime `3 ≤ P < N`, the value
`N - P` lies in `E_N` iff `Q' = (2N - P) + (P' - P)` for primes `2 < P' < N < Q' < 2N`. -/
theorem mem_E_shift {N P : ℕ} (hP3 : 3 ≤ P) (hPN : P < N) :
    (N - P) ∈ E N ↔ ∃ P' Q' : ℕ, P'.Prime ∧ Q'.Prime ∧ 2 < P' ∧ P' < N ∧ N < Q' ∧
      Q' < 2 * N ∧ Q' + 2 * P = 2 * N + P' := by
  rw [mem_E]
  constructor
  · rintro ⟨_, P', Q', h1, h2, h3, h4, h5, h6, h7⟩
    exact ⟨P', Q', h1, h2, h3, h4, h5, h6, by omega⟩
  · rintro ⟨P', Q', h1, h2, h3, h4, h5, h6, h7⟩
    exact ⟨⟨by omega, by omega⟩, P', Q', h1, h2, h3, h4, h5, h6, by omega⟩

/-- The step of Proposition `prop:verified`: a partition `2N = p + q` with `p < N` gives
an element of `C_N ∩ D_N`. -/
theorem centered_of_partition {N p q : ℕ} (hN : 4 ≤ N) (hp : p.Prime) (hq : q.Prime)
    (hs : p + q = 2 * N) (hlt : p < N) : (C N ∩ D N).Nonempty := by
  have hpq : p < q := by omega
  obtain ⟨a, b, c, d⟩ := centered_of_lt hp hq hpq hs hN
  refine ⟨N - p, ?_⟩
  rw [Finset.mem_inter, mem_C, mem_D]
  exact ⟨⟨⟨a, b⟩, c⟩, ⟨⟨a, b⟩, d⟩⟩

/-- The small cases of Section `subsec:small`: `C_N ∩ D_N ≠ ∅` for `4 ≤ N ≤ 12`. -/
theorem small_cases {N : ℕ} (h1 : 4 ≤ N) (h2 : N ≤ 12) : (C N ∩ D N).Nonempty := by
  have key : ∀ M : ℕ, 1 ≤ M → M ≤ N - 3 → (N - M).Prime → (N + M).Prime →
      (C N ∩ D N).Nonempty := by
    intro M hM1 hM2 hp hq
    refine ⟨M, ?_⟩
    rw [Finset.mem_inter, mem_C, mem_D]
    exact ⟨⟨⟨hM1, hM2⟩, hp⟩, ⟨⟨hM1, hM2⟩, hq⟩⟩
  interval_cases N
  · exact key 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact key 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact key 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact key 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact key 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact key 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact key 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact key 8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact key 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The coverage statistic `H(N) = log²(2N) - ((N - 3) - |E_N|)` of Section `subsec:gaps-H`. -/
noncomputable def H (N : ℕ) : ℝ :=
  Real.log (2 * (N : ℝ)) ^ 2 - (((N : ℝ) - 3) - (E N).card)

/-- `H(N) > 0` holds exactly when fewer than `log²(2N)` values of `A_N` are missing from `E_N`. -/
theorem H_pos_iff {N : ℕ} (hN : 3 ≤ N) :
    0 < H N ↔ ((A N \ E N).card : ℝ) < Real.log (2 * (N : ℝ)) ^ 2 := by
  have hsub : E N ⊆ A N := Finset.filter_subset _ _
  have h1 := Finset.card_sdiff_add_card_eq_card hsub
  have h2 : (A N).card = N - 3 := by
    unfold A
    rw [Nat.card_Icc]
    omega
  have h3 : ((A N \ E N).card : ℝ) + (E N).card = (N : ℝ) - 3 := by
    have h5 : (A N \ E N).card + (E N).card = N - 3 := by omega
    have h6 : (((A N \ E N).card + (E N).card : ℕ) : ℝ) = ((N - 3 : ℕ) : ℝ) := by
      rw [h5]
    rw [Nat.cast_sub hN] at h6
    push_cast at h6
    linarith
  unfold H
  constructor <;> intro h <;> linarith

/-- Corollary `cor:goldbach-diff`, counting form: `|C_N| ≤ |C_N ∩ E_N| + |A_N \ E_N|`. -/
theorem card_C_le_CE_add (N : ℕ) :
    (C N).card ≤ (C N ∩ E N).card + (A N \ E N).card := by
  have hsub : C N ⊆ (C N ∩ E N) ∪ (A N \ E N) := by
    intro M hM
    by_cases hE : M ∈ E N
    · exact Finset.mem_union_left _ (Finset.mem_inter.2 ⟨hM, hE⟩)
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.2 ⟨C_subset_A N hM, hE⟩)
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

/-- Corollary `cor:goldbach-diff`: `|C_N ∩ E_N| ≤ |C_N|`. -/
theorem card_CE_le (N : ℕ) : (C N ∩ E N).card ≤ (C N).card :=
  Finset.card_le_card Finset.inter_subset_left

/-- Section `subsec:upper-prime-count`: every pair of primes `3 ≤ P < N < Q ≤ 2N - 3`
gives the half-difference `(Q - P) / 2 ∈ E_N`. -/
theorem mem_E_of_pair {N P Q : ℕ} (hP : P.Prime) (hQ : Q.Prime) (hP3 : 3 ≤ P)
    (hPN : P < N) (hNQ : N < Q) (hQ3 : Q + 3 ≤ 2 * N) : (Q - P) / 2 ∈ E N := by
  have h1 := odd_of_prime_gt hP (by omega)
  have h2 := odd_of_prime_gt hQ (by omega)
  rw [mem_E]
  exact ⟨⟨by omega, by omega⟩, P, Q, hP, hQ, by omega, hPN, hNQ, by omega, by omega⟩

/-- Corollary `cor:half-difference-baseline`: the primes in `(N, 2N)` number at most
`|E_N| + 1`. -/
theorem card_E_ge_Ioo {N : ℕ} (hN : 4 ≤ N) :
    ((Finset.Ioo N (2 * N)).filter Nat.Prime).card ≤ (E N).card + 1 := by
  have hsub : (Finset.Ioo N (2 * N)).filter Nat.Prime ⊆
      insert (2 * N - 1) ((Finset.Ioc N (2 * N - 3)).filter Nat.Prime) := by
    intro Q hQ
    simp only [Finset.mem_filter, Finset.mem_Ioo] at hQ
    obtain ⟨⟨h1, h2⟩, hp⟩ := hQ
    have hodd := odd_of_prime_gt hp (by omega)
    rw [Finset.mem_insert]
    by_cases h : Q = 2 * N - 1
    · exact Or.inl h
    · right
      simp only [Finset.mem_filter, Finset.mem_Ioc]
      exact ⟨⟨h1, by omega⟩, hp⟩
  calc ((Finset.Ioo N (2 * N)).filter Nat.Prime).card
      ≤ (insert (2 * N - 1) ((Finset.Ioc N (2 * N - 3)).filter Nat.Prime)).card :=
        Finset.card_le_card hsub
    _ ≤ ((Finset.Ioc N (2 * N - 3)).filter Nat.Prime).card + 1 := Finset.card_insert_le _ _
    _ ≤ (E N).card + 1 := Nat.add_le_add_right (card_E_ge hN) 1

/-- Proposition `prop:pigeonhole-CE` with the statistic `H`: if `H(N) > 0` and
`|C_N| > log²(2N)` then `C_N ∩ E_N` is nonempty. -/
theorem pigeonhole_CE_of_H {N : ℕ} (hN : 3 ≤ N) (hH : 0 < H N)
    (hC : Real.log (2 * (N : ℝ)) ^ 2 < (C N).card) : (C N ∩ E N).Nonempty := by
  have h := (H_pos_iff hN).1 hH
  exact pigeonhole_CE N (Nat.cast_lt.1 (lt_trans h hC))

/-- Lemma `lem:gap` and Theorem `thm:cramer`, counting form: if `p⁻` is the largest prime
below `N` and `p⁺` the smallest above `N`, with `p⁺ - p⁻ + 4 ≤ 2N`, then at least
`(p⁺ - p⁻)/2 - 1` values of `A_N` are missing from `E_N`. -/
theorem gap_card_missing {N pm pp : ℕ}
    (hbelow : ∀ P : ℕ, P.Prime → P < N → P ≤ pm)
    (habove : ∀ Q : ℕ, Q.Prime → N < Q → pp ≤ Q)
    (hg : pp - pm + 4 ≤ 2 * N) :
    pp - pm ≤ 2 * (A N \ E N).card + 2 := by
  have hsub : Finset.Icc 1 ((pp - pm - 1) / 2) ⊆ A N \ E N := by
    intro M hM
    rw [Finset.mem_Icc] at hM
    exact gap_lower_missing hbelow habove (mem_A.2 ⟨hM.1, by omega⟩) (by omega)
  have := Finset.card_le_card hsub
  rw [Nat.card_Icc] at this
  omega

/-- Theorem `thm:cramer`, finite form: for consecutive primes `p < p'` with `3 ≤ p`
(no prime strictly between them), `p' - p ≤ 2 |A_{p+1} \ E_{p+1}| + 2`. -/
theorem gap_card_consecutive {p p' : ℕ} (hp3 : 3 ≤ p) (hpp : p < p')
    (hcons : ∀ r : ℕ, p < r → r < p' → ¬ r.Prime) :
    p' - p ≤ 2 * (A (p + 1) \ E (p + 1)).card + 2 := by
  obtain ⟨r, hr, hpr, hr2⟩ := Nat.exists_prime_lt_and_le_two_mul p (by omega)
  have hle : p' ≤ r := by
    by_contra h
    exact hcons r hpr (by omega) hr
  refine gap_card_missing (N := p + 1) (pm := p) (pp := p') ?_ ?_ (by omega)
  · intro P _ hP
    omega
  · intro Q hQ hpQ
    by_contra h
    exact hcons Q (by omega) (by omega) hQ

/-- Theorem `thm:cramer`: if `H(p + 1) > 0` for consecutive primes `p < p'` with `3 ≤ p`,
then `p' - p < 2 log²(2p + 2) + 2`. -/
theorem cramer_bound {p p' : ℕ} (hp3 : 3 ≤ p) (hpp : p < p')
    (hcons : ∀ r : ℕ, p < r → r < p' → ¬ r.Prime) (hH : 0 < H (p + 1)) :
    (p' : ℝ) - p < 2 * Real.log (2 * (p : ℝ) + 2) ^ 2 + 2 := by
  have h1 := gap_card_consecutive hp3 hpp hcons
  have h2 := (H_pos_iff (N := p + 1) (by omega)).1 hH
  have e : (2 : ℝ) * ((p + 1 : ℕ) : ℝ) = 2 * (p : ℝ) + 2 := by
    push_cast
    ring
  rw [e] at h2
  have h3 : p' ≤ 2 * (A (p + 1) \ E (p + 1)).card + 2 + p := by omega
  have h4 : (p' : ℝ) ≤ 2 * ((A (p + 1) \ E (p + 1)).card : ℝ) + 2 + p := by
    exact_mod_cast h3
  linarith

/-- `R(2N) = |C_N ∩ D_N|`, the number of centered Goldbach partitions of `2N`. -/
noncomputable def R (N : ℕ) : ℕ := (C N ∩ D N).card

/-- The odd primes `p ≤ n`. -/
noncomputable def oddPrimes (n : ℕ) : Finset ℕ := (Finset.Icc 3 n).filter Nat.Prime

/-- `T = ∑_{4 ≤ N ≤ X} R(2N)` of Theorem `thm:positive-proportion`. -/
noncomputable def Tsum (X : ℕ) : ℕ := ∑ N ∈ Finset.Icc 4 X, R N

/-- `V = ∑_{4 ≤ N ≤ X} R(2N)²` of Theorem `thm:positive-proportion`. -/
noncomputable def Vsum (X : ℕ) : ℕ := ∑ N ∈ Finset.Icc 4 X, R N ^ 2

/-- The number of `N` with `4 ≤ N ≤ X` and `R(2N) ≥ 1`. -/
noncomputable def cnt (X : ℕ) : ℕ := ((Finset.Icc 4 X).filter fun N => 1 ≤ R N).card

/-- Theorem `thm:positive-proportion`, Cauchy–Schwarz step: `T² ≤ cnt · V`. -/
theorem cs_count (X : ℕ) : Tsum X ^ 2 ≤ cnt X * Vsum X := by
  unfold Tsum Vsum cnt
  have hT : ∑ N ∈ Finset.Icc 4 X, R N =
      ∑ N ∈ (Finset.Icc 4 X).filter (fun N => 1 ≤ R N), R N := by
    symm
    apply Finset.sum_filter_of_ne
    intro N _ hN
    omega
  have hV : ∑ N ∈ Finset.Icc 4 X, R N ^ 2 =
      ∑ N ∈ (Finset.Icc 4 X).filter (fun N => 1 ≤ R N), R N ^ 2 := by
    symm
    apply Finset.sum_filter_of_ne
    intro N _ hN
    exact Nat.one_le_iff_ne_zero.2 (fun h => hN (by rw [h]; norm_num))
  rw [hT, hV]
  have key := Finset.sum_mul_sq_le_sq_mul_sq
    ((Finset.Icc 4 X).filter (fun N => 1 ≤ R N)) (fun _ => (1 : ℝ)) (fun N => (R N : ℝ))
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at key
  have key2 : (((∑ N ∈ (Finset.Icc 4 X).filter (fun N => 1 ≤ R N), R N : ℕ)) : ℝ) ^ 2 ≤
      (((Finset.Icc 4 X).filter (fun N => 1 ≤ R N)).card : ℝ) *
        ((∑ N ∈ (Finset.Icc 4 X).filter (fun N => 1 ≤ R N), R N ^ 2 : ℕ) : ℝ) := by
    push_cast
    exact key
  exact_mod_cast key2

/-- Theorem `thm:positive-proportion`, lower bound for `T`: every pair of odd primes
`p < q ≤ X` gives a distinct pair `(N, M)` with `N = (p + q)/2` and
`M = (q - p)/2 ∈ C_N ∩ D_N`. -/
theorem T_ge_pairs (X : ℕ) :
    (((oddPrimes X) ×ˢ (oddPrimes X)).filter (fun x : ℕ × ℕ => x.1 < x.2)).card ≤ Tsum X := by
  have hcard : ((Finset.Icc 4 X).sigma fun N => C N ∩ D N).card = Tsum X := by
    rw [Finset.card_sigma]
    simp only [Tsum, R]
  rw [← hcard]
  refine Finset.card_le_card_of_injOn
    (fun x : ℕ × ℕ => (⟨(x.1 + x.2) / 2, (x.2 - x.1) / 2⟩ : Σ _ : ℕ, ℕ)) ?_ ?_
  · rintro ⟨p, q⟩ hx
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, oddPrimes,
      Finset.mem_Icc] at hx
    obtain ⟨⟨⟨⟨h1, h2⟩, hp⟩, ⟨⟨h3, h4⟩, hq⟩⟩, hlt⟩ := hx
    have ho1 := odd_of_prime_gt hp (by omega)
    have ho2 := odd_of_prime_gt hq (by omega)
    have e1 : (p + q) / 2 - (q - p) / 2 = p := by omega
    have e2 : (p + q) / 2 + (q - p) / 2 = q := by omega
    have hmem : (⟨(p + q) / 2, (q - p) / 2⟩ : Σ _ : ℕ, ℕ) ∈
        (Finset.Icc 4 X).sigma (fun N => C N ∩ D N) := by
      simp only [Finset.mem_sigma, Finset.mem_Icc, Finset.mem_inter, mem_C, mem_D]
      refine ⟨⟨by omega, by omega⟩, ⟨⟨by omega, by omega⟩, ?_⟩, ⟨⟨by omega, by omega⟩, ?_⟩⟩
      · rw [e1]; exact hp
      · rw [e2]; exact hq
    exact hmem
  · rintro ⟨p, q⟩ hx ⟨p', q'⟩ hx' heq
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, oddPrimes,
      Finset.mem_Icc] at hx hx'
    obtain ⟨⟨⟨⟨h1, h2⟩, hp⟩, ⟨⟨h3, h4⟩, hq⟩⟩, hlt⟩ := hx
    obtain ⟨⟨⟨⟨h1', h2'⟩, hp'⟩, ⟨⟨h3', h4'⟩, hq'⟩⟩, hlt'⟩ := hx'
    have ho1 := odd_of_prime_gt hp (by omega)
    have ho2 := odd_of_prime_gt hq (by omega)
    have ho1' := odd_of_prime_gt hp' (by omega)
    have ho2' := odd_of_prime_gt hq' (by omega)
    simp only [Sigma.mk.inj_iff, heq_eq_eq] at heq
    obtain ⟨e1, e2⟩ := heq
    rw [Prod.mk.injEq]
    constructor <;> omega

/-- The number of pairs `(a, b) ∈ s × s` with `a < b` is `(|s|² - |s|)/2`. -/
theorem card_lt_pairs (s : Finset ℕ) :
    2 * ((s ×ˢ s).filter (fun x : ℕ × ℕ => x.1 < x.2)).card + s.card = s.card ^ 2 := by
  have hFU : (s ×ˢ s).filter (fun x : ℕ × ℕ => x.1 < x.2) ⊆ s ×ˢ s :=
    Finset.filter_subset _ _
  have hGUF : (s ×ˢ s).filter (fun x : ℕ × ℕ => x.2 < x.1) ⊆
      (s ×ˢ s) \ (s ×ˢ s).filter (fun x : ℕ × ℕ => x.1 < x.2) := by
    intro x hx
    rw [Finset.mem_filter] at hx
    rw [Finset.mem_sdiff, Finset.mem_filter]
    exact ⟨hx.1, fun h => by have h1 := h.2; have h2 := hx.2; omega⟩
  have hdiag : ((s ×ˢ s) \ (s ×ˢ s).filter (fun x : ℕ × ℕ => x.1 < x.2)) \
      (s ×ˢ s).filter (fun x : ℕ × ℕ => x.2 < x.1) = s.diag := by
    ext ⟨a, b⟩
    simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_product, Finset.mem_diag]
    constructor
    · rintro ⟨⟨⟨ha, hb⟩, h1⟩, h2⟩
      refine ⟨ha, ?_⟩
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with h | h
      · exact h1 ⟨⟨ha, hb⟩, h⟩
      · exact h2 ⟨⟨ha, hb⟩, h⟩
    · rintro ⟨ha, rfl⟩
      exact ⟨⟨⟨ha, ha⟩, fun h => lt_irrefl _ h.2⟩, fun h => lt_irrefl _ h.2⟩
  have hswap : ((s ×ˢ s).filter (fun x : ℕ × ℕ => x.2 < x.1)).card =
      ((s ×ˢ s).filter (fun x : ℕ × ℕ => x.1 < x.2)).card := by
    refine Finset.card_nbij' Prod.swap Prod.swap ?_ ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Prod.fst_swap,
        Prod.snd_swap] at hx ⊢
      exact ⟨⟨hx.1.2, hx.1.1⟩, hx.2⟩
    · intro x hx
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Prod.fst_swap,
        Prod.snd_swap] at hx ⊢
      exact ⟨⟨hx.1.2, hx.1.1⟩, hx.2⟩
    · intro x _
      exact Prod.swap_swap x
    · intro x _
      exact Prod.swap_swap x
  have h1 := Finset.card_sdiff_add_card_eq_card hGUF
  have h2 := Finset.card_sdiff_add_card_eq_card hFU
  rw [hdiag, Finset.diag_card] at h1
  have h3 : (s ×ˢ s).card = s.card ^ 2 := by
    rw [Finset.card_product]
    ring
  rw [hswap] at h1
  linarith

/-- Theorem `thm:positive-proportion`, upper bound for `V`: each `R(2N)²` counts pairs of
representations `2N = p + q = p' + q'`, so `V` is at most the number of quadruples
`(p, q, p', q')` with `p, p'` odd primes `≤ X`, `q, q'` odd primes `≤ 2X` and
`p + q = p' + q'`. -/
theorem V_le_quad (X : ℕ) :
    Vsum X ≤ (((((oddPrimes X) ×ˢ (oddPrimes (2 * X))) ×ˢ
      ((oddPrimes X) ×ˢ (oddPrimes (2 * X)))).filter
        (fun x : (ℕ × ℕ) × (ℕ × ℕ) => x.1.1 + x.1.2 = x.2.1 + x.2.2))).card := by
  have hcard : ((Finset.Icc 4 X).sigma fun N => (C N ∩ D N) ×ˢ (C N ∩ D N)).card =
      Vsum X := by
    rw [Finset.card_sigma]
    simp only [Finset.card_product, Vsum, R, sq]
  rw [← hcard]
  refine Finset.card_le_card_of_injOn
    (fun x : (Σ _ : ℕ, ℕ × ℕ) =>
      ((x.1 - x.2.1, x.1 + x.2.1), (x.1 - x.2.2, x.1 + x.2.2))) ?_ ?_
  · rintro ⟨N, M, M'⟩ hx
    simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_Icc, Finset.mem_product,
      Finset.mem_inter, mem_C, mem_D] at hx
    obtain ⟨⟨h4, hX⟩, ⟨⟨⟨⟨hM1, hM2⟩, hp⟩, ⟨_, hq⟩⟩, ⟨⟨⟨hM1', hM2'⟩, hp'⟩, ⟨_, hq'⟩⟩⟩⟩ := hx
    have hmem : ((N - M, N + M), (N - M', N + M')) ∈
        (((oddPrimes X) ×ˢ (oddPrimes (2 * X))) ×ˢ
          ((oddPrimes X) ×ˢ (oddPrimes (2 * X)))).filter
          (fun x : (ℕ × ℕ) × (ℕ × ℕ) => x.1.1 + x.1.2 = x.2.1 + x.2.2) := by
      simp only [Finset.mem_filter, Finset.mem_product, oddPrimes, Finset.mem_Icc]
      exact ⟨⟨⟨⟨⟨by omega, by omega⟩, hp⟩, ⟨⟨by omega, by omega⟩, hq⟩⟩,
        ⟨⟨⟨by omega, by omega⟩, hp'⟩, ⟨⟨by omega, by omega⟩, hq'⟩⟩⟩, by omega⟩
    exact hmem
  · rintro ⟨N, M, M'⟩ hx ⟨N2, K, K'⟩ hx2 heq
    simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_Icc, Finset.mem_product,
      Finset.mem_inter, mem_C, mem_D] at hx hx2
    obtain ⟨⟨h4, hX⟩, ⟨⟨⟨⟨hM1, hM2⟩, hp⟩, ⟨_, hq⟩⟩, ⟨⟨⟨hM1', hM2'⟩, hp'⟩, ⟨_, hq'⟩⟩⟩⟩ := hx
    obtain ⟨⟨h42, hX2⟩, ⟨⟨⟨⟨hK1, hK2⟩, hr⟩, ⟨_, hs⟩⟩, ⟨⟨⟨hK1', hK2'⟩, hr'⟩, ⟨_, hs'⟩⟩⟩⟩ := hx2
    simp only [Prod.mk.injEq] at heq
    obtain ⟨⟨e1, e2⟩, e3, e4⟩ := heq
    obtain rfl : N = N2 := by omega
    obtain rfl : M = K := by omega
    obtain rfl : M' = K' := by omega
    rfl

/-- Theorem `thm:positive-proportion`, conditional form: if `Tlow ≤ T` and `V ≤ Vup` with
`Tlow ≥ 0` and `Vup > 0`, then at least `Tlow² / Vup` integers `4 ≤ N ≤ X` have
`R(2N) ≥ 1`. The explicit bounds on `T` and `V` of the paper are analytic inputs
and are taken as hypotheses. -/
theorem positive_proportion_of_bounds {X : ℕ} {Tlow Vup : ℝ} (hTl : 0 ≤ Tlow)
    (hVup : 0 < Vup) (hT : Tlow ≤ (Tsum X : ℝ)) (hV : (Vsum X : ℝ) ≤ Vup) :
    Tlow ^ 2 / Vup ≤ (cnt X : ℝ) := by
  have h1 : (Tsum X : ℝ) ^ 2 ≤ (cnt X : ℝ) * (Vsum X : ℝ) := by
    exact_mod_cast cs_count X
  have h2 : Tlow ^ 2 ≤ (Tsum X : ℝ) ^ 2 := by
    nlinarith [mul_nonneg hTl (sub_nonneg.2 hT), sq_nonneg ((Tsum X : ℝ) - Tlow)]
  have h3 : (cnt X : ℝ) * (Vsum X : ℝ) ≤ (cnt X : ℝ) * Vup :=
    mul_le_mul_of_nonneg_left hV (Nat.cast_nonneg _)
  rw [div_le_iff₀ hVup]
  linarith

/-- Open question 5 (`M = 0`): `2N = p + p` with `p` prime exactly when `N` is prime. -/
theorem zero_case (N : ℕ) :
    N.Prime ↔ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p = q ∧ p + q = 2 * N := by
  constructor
  · intro h
    exact ⟨N, N, h, h, rfl, by ring⟩
  · rintro ⟨p, q, hp, _, hpq, hs⟩
    have h : p = N := by omega
    rw [← h]
    exact hp

/-- Open question 5: `2N` is a sum of two primes exactly when `N` is prime or `2N` is a sum
of two distinct primes. -/
theorem classical_iff_distinct (N : ℕ) :
    (∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = 2 * N) ↔
      N.Prime ∨ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ p + q = 2 * N := by
  constructor
  · rintro ⟨p, q, hp, hq, hs⟩
    by_cases h : p = q
    · left
      have hN : p = N := by omega
      rw [← hN]
      exact hp
    · right
      exact ⟨p, q, hp, hq, h, hs⟩
  · rintro (h | ⟨p, q, hp, hq, _, hs⟩)
    · exact ⟨N, N, h, h, by ring⟩
    · exact ⟨p, q, hp, hq, hs⟩

/-- Section `subsec:proof-gap`: `M ∈ C_N ∩ D_N` exactly when `M` is the half-difference of a
straddling pair `(P, Q)` that is centered, that is, with `P + Q = 2N`. -/
theorem CD_iff_centered_witness {N M : ℕ} :
    M ∈ C N ∩ D N ↔ (1 ≤ M ∧ M ≤ N - 3) ∧
      ∃ P Q : ℕ, P.Prime ∧ Q.Prime ∧ 2 < P ∧ P < N ∧ N < Q ∧ Q < 2 * N ∧
        P + 2 * M = Q ∧ P + Q = 2 * N := by
  rw [Finset.mem_inter, mem_C, mem_D]
  constructor
  · rintro ⟨⟨hA, hp⟩, ⟨_, hq⟩⟩
    exact ⟨hA, N - M, N + M, hp, hq, by omega, by omega, by omega, by omega, by omega,
      by omega⟩
  · rintro ⟨hA, P, Q, hP, hQ, h1, h2, h3, h4, h5, h6⟩
    have e1 : N - M = P := by omega
    have e2 : N + M = Q := by omega
    rw [e1, e2]
    exact ⟨⟨hA, hP⟩, ⟨hA, hQ⟩⟩

/-- Proposition `prop:HR-negative`, counting step: `R(2N) ≤ |C_N|`, the number of primes
`P` with `3 ≤ P ≤ N - 1`. -/
theorem card_CD_le_primes (N : ℕ) :
    (C N ∩ D N).card ≤ ((Finset.Icc 3 (N - 1)).filter Nat.Prime).card := by
  rw [← card_C N]
  exact Finset.card_le_card Finset.inter_subset_left

end PigeonGoldbach.Core
