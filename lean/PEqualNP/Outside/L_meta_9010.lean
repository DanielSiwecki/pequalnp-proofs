import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9010

open PEqualNP.HeptadCover

def onLine (p l : Fin 13) : Prop :=
  let r := (p.val + 13 - l.val) % 13
  r = 0 ∨ r = 1 ∨ r = 3 ∨ r = 9

lemma on_iff (p l : Fin 13) : onLine p l ↔ p ∈ singerLines3 l := by
  simp [onLine, singerLines3]

def Claim (a b c d : Fin 13) : Prop :=
  (∀ l : Fin 13,
    ¬ (onLine a l ∧ onLine b l ∧ onLine c l) ∧
    ¬ (onLine a l ∧ onLine b l ∧ onLine d l) ∧
    ¬ (onLine a l ∧ onLine c l ∧ onLine d l) ∧
    ¬ (onLine b l ∧ onLine c l ∧ onLine d l)) →
  ∀ p : Fin 13, p ≠ a → p ≠ b → p ≠ c → p ≠ d →
    ∃ l : Fin 13, onLine p l ∧ ¬ onLine a l ∧ ¬ onLine b l ∧
      ¬ onLine c l ∧ ¬ onLine d l

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma check_0_1 : ∀ c d : Fin 13, (1 : Fin 13) < c → c < d → Claim 0 1 c d := by
  unfold Claim onLine
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma check_0_2 : ∀ c d : Fin 13, (2 : Fin 13) < c → c < d → Claim 0 2 c d := by
  unfold Claim onLine
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma check_0_3 : ∀ c d : Fin 13, (3 : Fin 13) < c → c < d → Claim 0 3 c d := by
  unfold Claim onLine
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma check_0_4 : ∀ c d : Fin 13, (4 : Fin 13) < c → c < d → Claim 0 4 c d := by
  unfold Claim onLine
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma check_0_5 : ∀ c d : Fin 13, (5 : Fin 13) < c → c < d → Claim 0 5 c d := by
  unfold Claim onLine
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma check_0_6 : ∀ c d : Fin 13, (6 : Fin 13) < c → c < d → Claim 0 6 c d := by
  unfold Claim onLine
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma check_0_7 : ∀ c d : Fin 13, (7 : Fin 13) < c → c < d → Claim 0 7 c d := by
  unfold Claim onLine
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma check_0_8 : ∀ c d : Fin 13, (8 : Fin 13) < c → c < d → Claim 0 8 c d := by
  unfold Claim onLine
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma check_0_9 : ∀ c d : Fin 13, (9 : Fin 13) < c → c < d → Claim 0 9 c d := by
  unfold Claim onLine
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma check_0_10 : ∀ c d : Fin 13, (10 : Fin 13) < c → c < d → Claim 0 10 c d := by
  unfold Claim onLine
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma check_1_2 : ∀ c d : Fin 13, (2 : Fin 13) < c → c < d → Claim 1 2 c d := by
  unfold Claim onLine
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma check_1_3 : ∀ c d : Fin 13, (3 : Fin 13) < c → c < d → Claim 1 3 c d := by
  unfold Claim onLine
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma check_1_4 : ∀ c d : Fin 13, (4 : Fin 13) < c → c < d → Claim 1 4 c d := by
  unfold Claim onLine
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma check_1_5 : ∀ c d : Fin 13, (5 : Fin 13) < c → c < d → Claim 1 5 c d := by
  unfold Claim onLine
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma check_1_6 : ∀ c d : Fin 13, (6 : Fin 13) < c → c < d → Claim 1 6 c d := by
  unfold Claim onLine
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma check_1_7 : ∀ c d : Fin 13, (7 : Fin 13) < c → c < d → Claim 1 7 c d := by
  unfold Claim onLine
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma check_1_8 : ∀ c d : Fin 13, (8 : Fin 13) < c → c < d → Claim 1 8 c d := by
  unfold Claim onLine
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma check_1_9 : ∀ c d : Fin 13, (9 : Fin 13) < c → c < d → Claim 1 9 c d := by
  unfold Claim onLine
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma check_1_10 : ∀ c d : Fin 13, (10 : Fin 13) < c → c < d → Claim 1 10 c d := by
  unfold Claim onLine
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma check_2_3 : ∀ c d : Fin 13, (3 : Fin 13) < c → c < d → Claim 2 3 c d := by
  unfold Claim onLine
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma check_2_4 : ∀ c d : Fin 13, (4 : Fin 13) < c → c < d → Claim 2 4 c d := by
  unfold Claim onLine
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma check_2_5 : ∀ c d : Fin 13, (5 : Fin 13) < c → c < d → Claim 2 5 c d := by
  unfold Claim onLine
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma check_2_6 : ∀ c d : Fin 13, (6 : Fin 13) < c → c < d → Claim 2 6 c d := by
  unfold Claim onLine
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma check_2_7 : ∀ c d : Fin 13, (7 : Fin 13) < c → c < d → Claim 2 7 c d := by
  unfold Claim onLine
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma check_2_8 : ∀ c d : Fin 13, (8 : Fin 13) < c → c < d → Claim 2 8 c d := by
  unfold Claim onLine
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma check_2_9 : ∀ c d : Fin 13, (9 : Fin 13) < c → c < d → Claim 2 9 c d := by
  unfold Claim onLine
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma check_2_10 : ∀ c d : Fin 13, (10 : Fin 13) < c → c < d → Claim 2 10 c d := by
  unfold Claim onLine
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma check_3_4 : ∀ c d : Fin 13, (4 : Fin 13) < c → c < d → Claim 3 4 c d := by
  unfold Claim onLine
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma check_3_5 : ∀ c d : Fin 13, (5 : Fin 13) < c → c < d → Claim 3 5 c d := by
  unfold Claim onLine
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma check_3_6 : ∀ c d : Fin 13, (6 : Fin 13) < c → c < d → Claim 3 6 c d := by
  unfold Claim onLine
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma check_3_7 : ∀ c d : Fin 13, (7 : Fin 13) < c → c < d → Claim 3 7 c d := by
  unfold Claim onLine
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma check_3_8 : ∀ c d : Fin 13, (8 : Fin 13) < c → c < d → Claim 3 8 c d := by
  unfold Claim onLine
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma check_3_9 : ∀ c d : Fin 13, (9 : Fin 13) < c → c < d → Claim 3 9 c d := by
  unfold Claim onLine
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma check_3_10 : ∀ c d : Fin 13, (10 : Fin 13) < c → c < d → Claim 3 10 c d := by
  unfold Claim onLine
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma check_4_5 : ∀ c d : Fin 13, (5 : Fin 13) < c → c < d → Claim 4 5 c d := by
  unfold Claim onLine
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma check_4_6 : ∀ c d : Fin 13, (6 : Fin 13) < c → c < d → Claim 4 6 c d := by
  unfold Claim onLine
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma check_4_7 : ∀ c d : Fin 13, (7 : Fin 13) < c → c < d → Claim 4 7 c d := by
  unfold Claim onLine
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma check_4_8 : ∀ c d : Fin 13, (8 : Fin 13) < c → c < d → Claim 4 8 c d := by
  unfold Claim onLine
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma check_4_9 : ∀ c d : Fin 13, (9 : Fin 13) < c → c < d → Claim 4 9 c d := by
  unfold Claim onLine
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma check_4_10 : ∀ c d : Fin 13, (10 : Fin 13) < c → c < d → Claim 4 10 c d := by
  unfold Claim onLine
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma check_5_6 : ∀ c d : Fin 13, (6 : Fin 13) < c → c < d → Claim 5 6 c d := by
  unfold Claim onLine
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma check_5_7 : ∀ c d : Fin 13, (7 : Fin 13) < c → c < d → Claim 5 7 c d := by
  unfold Claim onLine
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma check_5_8 : ∀ c d : Fin 13, (8 : Fin 13) < c → c < d → Claim 5 8 c d := by
  unfold Claim onLine
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma check_5_9 : ∀ c d : Fin 13, (9 : Fin 13) < c → c < d → Claim 5 9 c d := by
  unfold Claim onLine
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma check_5_10 : ∀ c d : Fin 13, (10 : Fin 13) < c → c < d → Claim 5 10 c d := by
  unfold Claim onLine
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma check_6_7 : ∀ c d : Fin 13, (7 : Fin 13) < c → c < d → Claim 6 7 c d := by
  unfold Claim onLine
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma check_6_8 : ∀ c d : Fin 13, (8 : Fin 13) < c → c < d → Claim 6 8 c d := by
  unfold Claim onLine
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma check_6_9 : ∀ c d : Fin 13, (9 : Fin 13) < c → c < d → Claim 6 9 c d := by
  unfold Claim onLine
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma check_6_10 : ∀ c d : Fin 13, (10 : Fin 13) < c → c < d → Claim 6 10 c d := by
  unfold Claim onLine
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma check_7_8 : ∀ c d : Fin 13, (8 : Fin 13) < c → c < d → Claim 7 8 c d := by
  unfold Claim onLine
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma check_7_9 : ∀ c d : Fin 13, (9 : Fin 13) < c → c < d → Claim 7 9 c d := by
  unfold Claim onLine
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma check_7_10 : ∀ c d : Fin 13, (10 : Fin 13) < c → c < d → Claim 7 10 c d := by
  unfold Claim onLine
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma check_8_9 : ∀ c d : Fin 13, (9 : Fin 13) < c → c < d → Claim 8 9 c d := by
  unfold Claim onLine
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma check_8_10 : ∀ c d : Fin 13, (10 : Fin 13) < c → c < d → Claim 8 10 c d := by
  unfold Claim onLine
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma check_9_10 : ∀ c d : Fin 13, (10 : Fin 13) < c → c < d → Claim 9 10 c d := by
  unfold Claim onLine
  decide

set_option maxHeartbeats 1000000 in
lemma ordered_check (a b c d : Fin 13) (hab : a < b) (hbc : b < c) (hcd : c < d) :
    Claim a b c d := by
  fin_cases a
  · fin_cases b
    · omega
    · exact check_0_1 c d hbc hcd
    · exact check_0_2 c d hbc hcd
    · exact check_0_3 c d hbc hcd
    · exact check_0_4 c d hbc hcd
    · exact check_0_5 c d hbc hcd
    · exact check_0_6 c d hbc hcd
    · exact check_0_7 c d hbc hcd
    · exact check_0_8 c d hbc hcd
    · exact check_0_9 c d hbc hcd
    · exact check_0_10 c d hbc hcd
    · omega
    · omega
  · fin_cases b
    · omega
    · omega
    · exact check_1_2 c d hbc hcd
    · exact check_1_3 c d hbc hcd
    · exact check_1_4 c d hbc hcd
    · exact check_1_5 c d hbc hcd
    · exact check_1_6 c d hbc hcd
    · exact check_1_7 c d hbc hcd
    · exact check_1_8 c d hbc hcd
    · exact check_1_9 c d hbc hcd
    · exact check_1_10 c d hbc hcd
    · omega
    · omega
  · fin_cases b
    · omega
    · omega
    · omega
    · exact check_2_3 c d hbc hcd
    · exact check_2_4 c d hbc hcd
    · exact check_2_5 c d hbc hcd
    · exact check_2_6 c d hbc hcd
    · exact check_2_7 c d hbc hcd
    · exact check_2_8 c d hbc hcd
    · exact check_2_9 c d hbc hcd
    · exact check_2_10 c d hbc hcd
    · omega
    · omega
  · fin_cases b
    · omega
    · omega
    · omega
    · omega
    · exact check_3_4 c d hbc hcd
    · exact check_3_5 c d hbc hcd
    · exact check_3_6 c d hbc hcd
    · exact check_3_7 c d hbc hcd
    · exact check_3_8 c d hbc hcd
    · exact check_3_9 c d hbc hcd
    · exact check_3_10 c d hbc hcd
    · omega
    · omega
  · fin_cases b
    · omega
    · omega
    · omega
    · omega
    · omega
    · exact check_4_5 c d hbc hcd
    · exact check_4_6 c d hbc hcd
    · exact check_4_7 c d hbc hcd
    · exact check_4_8 c d hbc hcd
    · exact check_4_9 c d hbc hcd
    · exact check_4_10 c d hbc hcd
    · omega
    · omega
  · fin_cases b
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · exact check_5_6 c d hbc hcd
    · exact check_5_7 c d hbc hcd
    · exact check_5_8 c d hbc hcd
    · exact check_5_9 c d hbc hcd
    · exact check_5_10 c d hbc hcd
    · omega
    · omega
  · fin_cases b
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · exact check_6_7 c d hbc hcd
    · exact check_6_8 c d hbc hcd
    · exact check_6_9 c d hbc hcd
    · exact check_6_10 c d hbc hcd
    · omega
    · omega
  · fin_cases b
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · exact check_7_8 c d hbc hcd
    · exact check_7_9 c d hbc hcd
    · exact check_7_10 c d hbc hcd
    · omega
    · omega
  · fin_cases b
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · exact check_8_9 c d hbc hcd
    · exact check_8_10 c d hbc hcd
    · omega
    · omega
  · fin_cases b
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · exact check_9_10 c d hbc hcd
    · omega
    · omega
  · omega
  · omega
  · omega

lemma no_three (Q : Finset (Fin 13)) (l u v w : Fin 13)
    (h : (Q ∩ singerLines3 l).card ≤ 2)
    (hu : u ∈ Q) (hv : v ∈ Q) (hw : w ∈ Q)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    ¬ (onLine u l ∧ onLine v l ∧ onLine w l) := by
  rintro ⟨hu', hv', hw'⟩
  have hs : ({u, v, w} : Finset (Fin 13)) ⊆ Q ∩ singerLines3 l := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact Finset.mem_inter.mpr ⟨hu, (on_iff _ _).mp hu'⟩
    · exact Finset.mem_inter.mpr ⟨hv, (on_iff _ _).mp hv'⟩
    · exact Finset.mem_inter.mpr ⟨hw, (on_iff _ _).mp hw'⟩
  have hcard : ({u, v, w} : Finset (Fin 13)).card = 3 := by
    simp [Finset.card_insert_of_not_mem, huv, huw, hvw]
  have hh := Finset.card_le_card hs
  omega

lemma sorted_four (Q : Finset (Fin 13)) (hc : Q.card = 4) :
    ∃ a b c d : Fin 13, a < b ∧ b < c ∧ c < d ∧ Q = {a, b, c, d} := by
  have hlen : (Q.sort (· ≤ ·)).length = 4 := by
    rw [Finset.length_sort, hc]
  obtain ⟨a, b, c, d, hs⟩ : ∃ a b c d : Fin 13, Q.sort (· ≤ ·) = [a, b, c, d] := by
    generalize heq : Q.sort (· ≤ ·) = xs at hlen ⊢
    rcases xs with _ | ⟨a, xs⟩
    · simp at hlen
    rcases xs with _ | ⟨b, xs⟩
    · simp at hlen
    rcases xs with _ | ⟨c, xs⟩
    · simp at hlen
    rcases xs with _ | ⟨d, xs⟩
    · simp at hlen
    rcases xs with _ | ⟨e, xs⟩
    · exact ⟨a, b, c, d, rfl⟩
    · simp only [List.length_cons] at hlen
      omega
  have hp := Finset.pairwise_sort Q (· ≤ ·)
  have hn := Finset.sort_nodup Q (· ≤ ·)
  rw [hs] at hp hn
  have hab_le : a ≤ b := (List.pairwise_cons.mp hp).1 b (by simp)
  have hbc_le : b ≤ c := (List.pairwise_cons.mp (List.pairwise_cons.mp hp).2).1 c (by simp)
  have hcd_le : c ≤ d :=
    (List.pairwise_cons.mp (List.pairwise_cons.mp (List.pairwise_cons.mp hp).2).2).1 d (by simp)
  have hab_ne : a ≠ b := by
    intro h
    subst b
    simpa using hn
  have hbc_ne : b ≠ c := by
    intro h
    subst c
    simpa using hn
  have hcd_ne : c ≠ d := by
    intro h
    subst d
    simpa using hn
  refine ⟨a, b, c, d, lt_of_le_of_ne hab_le hab_ne,
    lt_of_le_of_ne hbc_le hbc_ne, lt_of_le_of_ne hcd_le hcd_ne, ?_⟩
  have ht := Finset.sort_toFinset Q (· ≤ ·)
  rw [hs] at ht
  simpa using ht.symm

end PEqualNP.Outside.L_meta_9010

open PEqualNP.HeptadCover
open PEqualNP.Outside.L_meta_9010

theorem PEqualNP.Outside.L_meta_9010 : ∀ x1 ∈ PEqualNP.HeptadCover.quadrangles PEqualNP.HeptadCover.singerLines3, ∀ x3 ∉ x1, ∃ x5 ∈ PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x1, x3 ∈ PEqualNP.HeptadCover.singerLines3 x5 := by
  intro Q hQ p hp
  change Q ∈ (Finset.univ.powersetCard 4).filter
    (fun Q : Finset (Fin 13) => ∀ l : Fin 13, (Q ∩ singerLines3 l).card ≤ 2) at hQ
  have hc : Q.card = 4 := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hQ).1).2
  have hline := (Finset.mem_filter.mp hQ).2
  obtain ⟨a, b, c, d, hab, hbc, hcd, hEq⟩ := sorted_four Q hc
  have hac := lt_trans hab hbc
  have hbd := lt_trans hbc hcd
  have had := lt_trans hac hcd
  have haQ : a ∈ Q := by rw [hEq]; simp
  have hbQ : b ∈ Q := by rw [hEq]; simp
  have hcQ : c ∈ Q := by rw [hEq]; simp
  have hdQ : d ∈ Q := by rw [hEq]; simp
  have hpa : p ≠ a := by intro h; subst p; exact hp haQ
  have hpb : p ≠ b := by intro h; subst p; exact hp hbQ
  have hpc : p ≠ c := by intro h; subst p; exact hp hcQ
  have hpd : p ≠ d := by intro h; subst p; exact hp hdQ
  have h := ordered_check a b c d hab hbc hcd
  unfold Claim at h
  obtain ⟨l, hpl, hla, hlb, hlc, hld⟩ := h (fun l =>
    ⟨no_three Q l a b c (hline l) haQ hbQ hcQ hab.ne hac.ne hbc.ne,
     no_three Q l a b d (hline l) haQ hbQ hdQ hab.ne had.ne hbd.ne,
     no_three Q l a c d (hline l) haQ hcQ hdQ hac.ne had.ne hcd.ne,
     no_three Q l b c d (hline l) hbQ hcQ hdQ hbc.ne hbd.ne hcd.ne⟩)
    p hpa hpb hpc hpd
  refine ⟨l, ?_, (on_iff _ _).mp hpl⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  rw [Finset.disjoint_left]
  intro u huS huQ
  rw [hEq] at huQ
  simp only [Finset.mem_insert, Finset.mem_singleton] at huQ
  rcases huQ with rfl | rfl | rfl | rfl
  · exact hla ((on_iff _ _).mpr huS)
  · exact hlb ((on_iff _ _).mpr huS)
  · exact hlc ((on_iff _ _).mpr huS)
  · exact hld ((on_iff _ _).mpr huS)
