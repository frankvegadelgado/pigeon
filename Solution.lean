module

public import PigeonGoldbach

public section

namespace PigeonGoldbach.Public

open PigeonGoldbach.Core (A C D E B H R Tsum Vsum cnt oddPrimes IsSemiprime)
open PigeonGoldbach.CitedResults (piCount RosserSchoenfeldPi GoldbachVerification)

theorem geometric_equivalence {N : ℕ} (hN : 4 ≤ N) :
    ((∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ p + q = 2 * N) ↔
      ∃ M : ℕ, 1 ≤ M ∧ M ≤ N - 3 ∧ (N - M).Prime ∧ (N + M).Prime) ∧
    ((∃ M : ℕ, 1 ≤ M ∧ M ≤ N - 3 ∧ (N - M).Prime ∧ (N + M).Prime) ↔
      ∃ M : ℕ, 1 ≤ M ∧ M ≤ N - 3 ∧ IsSemiprime (N ^ 2 - M ^ 2)) :=
  PigeonGoldbach.Core.geometric_equivalence hN

theorem centered_intersection_criterion {N : ℕ} (hN : 4 ≤ N) :
    (∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ p + q = 2 * N) ↔ (C N ∩ D N).Nonempty :=
  PigeonGoldbach.Core.centered_intersection_criterion hN

theorem CD_subset_E (N : ℕ) : C N ∩ D N ⊆ E N :=
  PigeonGoldbach.Core.CD_subset_E N

theorem CED_eq_CD (N : ℕ) : C N ∩ E N ∩ D N = C N ∩ D N :=
  PigeonGoldbach.Core.CED_eq_CD N

theorem C_D_subset_B (N : ℕ) : C N ⊆ B N ∧ D N ⊆ B N :=
  PigeonGoldbach.Core.C_D_subset_B N

theorem gap_lower {N pm pp M : ℕ}
    (hbelow : ∀ P : ℕ, P.Prime → P < N → P ≤ pm)
    (habove : ∀ Q : ℕ, Q.Prime → N < Q → pp ≤ Q)
    (hM : M ∈ E N) : pp - pm ≤ 2 * M :=
  PigeonGoldbach.Core.gap_lower hbelow habove hM

theorem gap_lower_missing {N pm pp M : ℕ}
    (hbelow : ∀ P : ℕ, P.Prime → P < N → P ≤ pm)
    (habove : ∀ Q : ℕ, Q.Prime → N < Q → pp ≤ Q)
    (hA : M ∈ A N) (hsmall : 2 * M < pp - pm) : M ∈ A N \ E N :=
  PigeonGoldbach.Core.gap_lower_missing hbelow habove hA hsmall

theorem gap_top {N q M : ℕ}
    (hmax : ∀ Q : ℕ, Q.Prime → Q < 2 * N → Q ≤ q)
    (hM : M ∈ E N) : 2 * M + 3 ≤ q :=
  PigeonGoldbach.Core.gap_top hmax hM

theorem gap_top_missing {N q M : ℕ}
    (hmax : ∀ Q : ℕ, Q.Prime → Q < 2 * N → Q ≤ q)
    (hA : M ∈ A N) (hbig : q < 2 * M + 3) : M ∈ A N \ E N :=
  PigeonGoldbach.Core.gap_top_missing hmax hA hbig

theorem pigeonhole_CE (N : ℕ) (h : (A N \ E N).card < (C N).card) :
    (C N ∩ E N).Nonempty :=
  PigeonGoldbach.Core.pigeonhole_CE N h

theorem card_C (N : ℕ) :
    (C N).card = ((Finset.Icc 3 (N - 1)).filter Nat.Prime).card :=
  PigeonGoldbach.Core.card_C N

theorem card_E_ge {N : ℕ} (hN : 4 ≤ N) :
    ((Finset.Ioc N (2 * N - 3)).filter Nat.Prime).card ≤ (E N).card :=
  PigeonGoldbach.Core.card_E_ge hN

theorem mem_E_shift {N P : ℕ} (hP3 : 3 ≤ P) (hPN : P < N) :
    (N - P) ∈ E N ↔ ∃ P' Q' : ℕ, P'.Prime ∧ Q'.Prime ∧ 2 < P' ∧ P' < N ∧ N < Q' ∧
      Q' < 2 * N ∧ Q' + 2 * P = 2 * N + P' :=
  PigeonGoldbach.Core.mem_E_shift hP3 hPN

theorem centered_of_partition {N p q : ℕ} (hN : 4 ≤ N) (hp : p.Prime) (hq : q.Prime)
    (hs : p + q = 2 * N) (hlt : p < N) : (C N ∩ D N).Nonempty :=
  PigeonGoldbach.Core.centered_of_partition hN hp hq hs hlt

theorem small_cases {N : ℕ} (h1 : 4 ≤ N) (h2 : N ≤ 12) : (C N ∩ D N).Nonempty :=
  PigeonGoldbach.Core.small_cases h1 h2

theorem H_pos_iff {N : ℕ} (hN : 3 ≤ N) :
    0 < H N ↔ ((A N \ E N).card : ℝ) < Real.log (2 * (N : ℝ)) ^ 2 :=
  PigeonGoldbach.Core.H_pos_iff hN

theorem card_C_le_CE_add (N : ℕ) :
    (C N).card ≤ (C N ∩ E N).card + (A N \ E N).card :=
  PigeonGoldbach.Core.card_C_le_CE_add N

theorem card_CE_le (N : ℕ) : (C N ∩ E N).card ≤ (C N).card :=
  PigeonGoldbach.Core.card_CE_le N

theorem mem_E_of_pair {N P Q : ℕ} (hP : P.Prime) (hQ : Q.Prime) (hP3 : 3 ≤ P)
    (hPN : P < N) (hNQ : N < Q) (hQ3 : Q + 3 ≤ 2 * N) : (Q - P) / 2 ∈ E N :=
  PigeonGoldbach.Core.mem_E_of_pair hP hQ hP3 hPN hNQ hQ3

theorem card_E_ge_Ioo {N : ℕ} (hN : 4 ≤ N) :
    ((Finset.Ioo N (2 * N)).filter Nat.Prime).card ≤ (E N).card + 1 :=
  PigeonGoldbach.Core.card_E_ge_Ioo hN

theorem pigeonhole_CE_of_H {N : ℕ} (hN : 3 ≤ N) (hH : 0 < H N)
    (hC : Real.log (2 * (N : ℝ)) ^ 2 < (C N).card) : (C N ∩ E N).Nonempty :=
  PigeonGoldbach.Core.pigeonhole_CE_of_H hN hH hC

theorem gap_card_missing {N pm pp : ℕ}
    (hbelow : ∀ P : ℕ, P.Prime → P < N → P ≤ pm)
    (habove : ∀ Q : ℕ, Q.Prime → N < Q → pp ≤ Q)
    (hg : pp - pm + 4 ≤ 2 * N) :
    pp - pm ≤ 2 * (A N \ E N).card + 2 :=
  PigeonGoldbach.Core.gap_card_missing hbelow habove hg

theorem gap_card_consecutive {p p' : ℕ} (hp3 : 3 ≤ p) (hpp : p < p')
    (hcons : ∀ r : ℕ, p < r → r < p' → ¬ r.Prime) :
    p' - p ≤ 2 * (A (p + 1) \ E (p + 1)).card + 2 :=
  PigeonGoldbach.Core.gap_card_consecutive hp3 hpp hcons

theorem cramer_bound {p p' : ℕ} (hp3 : 3 ≤ p) (hpp : p < p')
    (hcons : ∀ r : ℕ, p < r → r < p' → ¬ r.Prime) (hH : 0 < H (p + 1)) :
    (p' : ℝ) - p < 2 * Real.log (2 * (p : ℝ) + 2) ^ 2 + 2 :=
  PigeonGoldbach.Core.cramer_bound hp3 hpp hcons hH

theorem cs_count (X : ℕ) : Tsum X ^ 2 ≤ cnt X * Vsum X :=
  PigeonGoldbach.Core.cs_count X

theorem T_ge_pairs (X : ℕ) :
    (((oddPrimes X) ×ˢ (oddPrimes X)).filter (fun x : ℕ × ℕ => x.1 < x.2)).card ≤ Tsum X :=
  PigeonGoldbach.Core.T_ge_pairs X

theorem card_lt_pairs (s : Finset ℕ) :
    2 * ((s ×ˢ s).filter (fun x : ℕ × ℕ => x.1 < x.2)).card + s.card = s.card ^ 2 :=
  PigeonGoldbach.Core.card_lt_pairs s

theorem V_le_quad (X : ℕ) :
    Vsum X ≤ (((((oddPrimes X) ×ˢ (oddPrimes (2 * X))) ×ˢ
      ((oddPrimes X) ×ˢ (oddPrimes (2 * X)))).filter
        (fun x : (ℕ × ℕ) × (ℕ × ℕ) => x.1.1 + x.1.2 = x.2.1 + x.2.2))).card :=
  PigeonGoldbach.Core.V_le_quad X

theorem positive_proportion_of_bounds {X : ℕ} {Tlow Vup : ℝ} (hTl : 0 ≤ Tlow)
    (hVup : 0 < Vup) (hT : Tlow ≤ (Tsum X : ℝ)) (hV : (Vsum X : ℝ) ≤ Vup) :
    Tlow ^ 2 / Vup ≤ (cnt X : ℝ) :=
  PigeonGoldbach.Core.positive_proportion_of_bounds hTl hVup hT hV

theorem card_oddPrimes_add_one {X : ℕ} (hX : 2 ≤ X) :
    (oddPrimes X).card + 1 = piCount X :=
  PigeonGoldbach.CitedResults.card_oddPrimes_add_one hX

theorem T_lower_of_RS (hRS : RosserSchoenfeldPi) {X : ℕ} (hX : 17 ≤ X)
    (hs : 2 ≤ (X : ℝ) / Real.log X) :
    ((X : ℝ) / Real.log X - 2) ^ 2 / 2 < (Tsum X : ℝ) :=
  PigeonGoldbach.CitedResults.T_lower_of_RS hRS hX hs

theorem positive_proportion_of_cited (hRS : RosserSchoenfeldPi) {X : ℕ} {Vup : ℝ}
    (hX : 17 ≤ X) (hs : 2 ≤ (X : ℝ) / Real.log X) (hVup : 0 < Vup)
    (hV : (Vsum X : ℝ) ≤ Vup) :
    ((((X : ℝ) / Real.log X - 2) ^ 2 / 2) ^ 2) / Vup ≤ (cnt X : ℝ) :=
  PigeonGoldbach.CitedResults.positive_proportion_of_cited hRS hX hs hVup hV

theorem verified_range (hG : GoldbachVerification)
    (hsmall : ∀ N : ℕ, 4 ≤ N → N ≤ 9781 → (C N ∩ D N).Nonempty)
    {N : ℕ} (h4 : 4 ≤ N) (hN : N ≤ 2 * 10 ^ 18) : (C N ∩ D N).Nonempty :=
  PigeonGoldbach.CitedResults.verified_range hG hsmall h4 hN

theorem zero_case (N : ℕ) :
    N.Prime ↔ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p = q ∧ p + q = 2 * N :=
  PigeonGoldbach.Core.zero_case N

theorem classical_iff_distinct (N : ℕ) :
    (∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = 2 * N) ↔
      N.Prime ∨ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ p + q = 2 * N :=
  PigeonGoldbach.Core.classical_iff_distinct N

theorem distinct_goldbach_iff_tail (hG : GoldbachVerification)
    (hsmall : ∀ N : ℕ, 4 ≤ N → N ≤ 9781 → (C N ∩ D N).Nonempty) :
    (∀ N : ℕ, 4 ≤ N → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ p + q = 2 * N) ↔
      ∀ N : ℕ, 2 * 10 ^ 18 < N → (C N ∩ D N).Nonempty :=
  PigeonGoldbach.CitedResults.distinct_goldbach_iff_tail hG hsmall

theorem CD_iff_centered_witness {N M : ℕ} :
    M ∈ C N ∩ D N ↔ (1 ≤ M ∧ M ≤ N - 3) ∧
      ∃ P Q : ℕ, P.Prime ∧ Q.Prime ∧ 2 < P ∧ P < N ∧ N < Q ∧ Q < 2 * N ∧
        P + 2 * M = Q ∧ P + Q = 2 * N :=
  PigeonGoldbach.Core.CD_iff_centered_witness

theorem card_CD_le_primes (N : ℕ) :
    (C N ∩ D N).card ≤ ((Finset.Icc 3 (N - 1)).filter Nat.Prime).card :=
  PigeonGoldbach.Core.card_CD_le_primes N

end PigeonGoldbach.Public
