import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10044

abbrev Rect := Finset (Fin 13) × Finset (Fin 13)

def entry (i j : Fin 13) : Bool :=
  (([5658, 3125, 6250, 4309, 427, 854, 1708, 3416, 6832, 5473, 2755, 5510, 2829] : List ℕ).getD i.val 0).testBit j.val

def row (a : Fin 39) : Fin 13 :=
  Fin.ofNat 13 (a.val / 3)

def col (a : Fin 39) : Fin 13 :=
  Fin.ofNat 13 (a.val / 3 + ([2, 5, 6] : List ℕ).getD (a.val % 3) 0)

lemma selected_zero (a : Fin 39) : entry (row a) (col a) = false := by
  fin_cases a <;> decide

-- The selected entries are the three cyclic diagonals with offsets 2, 5 and 6.
-- The following finite table records compatible distinct pairs of selected entries.
def neighbors (a : Fin 39) : Finset (Fin 39) :=
  ([{1, 2, 7, 8, 12, 23, 25, 27, 29, 31},
    {0, 2, 9, 10, 15, 17, 23, 31, 33, 38},
    {0, 1, 4, 5, 12, 18, 19, 25, 33, 38},
    {4, 5, 10, 11, 15, 26, 28, 30, 32, 34},
    {2, 3, 5, 12, 13, 18, 20, 26, 34, 36},
    {2, 3, 4, 7, 8, 15, 21, 22, 28, 36},
    {7, 8, 13, 14, 18, 29, 31, 33, 35, 37},
    {0, 5, 6, 8, 15, 16, 21, 23, 29, 37},
    {0, 5, 6, 7, 10, 11, 18, 24, 25, 31},
    {1, 10, 11, 16, 17, 21, 32, 34, 36, 38},
    {1, 3, 8, 9, 11, 18, 19, 24, 26, 32},
    {3, 8, 9, 10, 13, 14, 21, 27, 28, 34},
    {0, 2, 4, 13, 14, 19, 20, 24, 35, 37},
    {4, 6, 11, 12, 14, 21, 22, 27, 29, 35},
    {6, 11, 12, 13, 16, 17, 24, 30, 31, 37},
    {1, 3, 5, 7, 16, 17, 22, 23, 27, 38},
    {7, 9, 14, 15, 17, 24, 25, 30, 32, 38},
    {1, 9, 14, 15, 16, 19, 20, 27, 33, 34},
    {2, 4, 6, 8, 10, 19, 20, 25, 26, 30},
    {2, 10, 12, 17, 18, 20, 27, 28, 33, 35},
    {4, 12, 17, 18, 19, 22, 23, 30, 36, 37},
    {5, 7, 9, 11, 13, 22, 23, 28, 29, 33},
    {5, 13, 15, 20, 21, 23, 30, 31, 36, 38},
    {0, 1, 7, 15, 20, 21, 22, 25, 26, 33},
    {8, 10, 12, 14, 16, 25, 26, 31, 32, 36},
    {0, 2, 8, 16, 18, 23, 24, 26, 33, 34},
    {3, 4, 10, 18, 23, 24, 25, 28, 29, 36},
    {0, 11, 13, 15, 17, 19, 28, 29, 34, 35},
    {3, 5, 11, 19, 21, 26, 27, 29, 36, 37},
    {0, 6, 7, 13, 21, 26, 27, 28, 31, 32},
    {3, 14, 16, 18, 20, 22, 31, 32, 37, 38},
    {0, 1, 6, 8, 14, 22, 24, 29, 30, 32},
    {3, 9, 10, 16, 24, 29, 30, 31, 34, 35},
    {1, 2, 6, 17, 19, 21, 23, 25, 34, 35},
    {3, 4, 9, 11, 17, 25, 27, 32, 33, 35},
    {6, 12, 13, 19, 27, 32, 33, 34, 37, 38},
    {4, 5, 9, 20, 22, 24, 26, 28, 37, 38},
    {6, 7, 12, 14, 20, 28, 30, 35, 36, 38},
    {1, 2, 9, 15, 16, 22, 30, 35, 36, 37}] : List (Finset (Fin 39))).getD a.val ∅

def EdgesFrom (a : Fin 39) : Prop :=
  ∀ b ∈ (Finset.univ : Finset (Fin 39)), a ≠ b →
    entry (row a) (col b) = false →
    entry (row b) (col a) = false →
    b ∈ neighbors a

def NoExtend (a : Fin 39) : Prop :=
  ∀ b ∈ neighbors a, ∀ c ∈ neighbors a ∩ neighbors b,
    (neighbors a ∩ neighbors b) ∩ neighbors c = ∅

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma edge_0 : EdgesFrom 0 := by
  unfold EdgesFrom
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma triangle_0 : NoExtend 0 := by
  unfold NoExtend
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma edge_1 : EdgesFrom 1 := by
  unfold EdgesFrom
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma triangle_1 : NoExtend 1 := by
  unfold NoExtend
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma edge_2 : EdgesFrom 2 := by
  unfold EdgesFrom
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma triangle_2 : NoExtend 2 := by
  unfold NoExtend
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma edge_3 : EdgesFrom 3 := by
  unfold EdgesFrom
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma triangle_3 : NoExtend 3 := by
  unfold NoExtend
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma edge_4 : EdgesFrom 4 := by
  unfold EdgesFrom
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma triangle_4 : NoExtend 4 := by
  unfold NoExtend
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma edge_5 : EdgesFrom 5 := by
  unfold EdgesFrom
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma triangle_5 : NoExtend 5 := by
  unfold NoExtend
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma edge_6 : EdgesFrom 6 := by
  unfold EdgesFrom
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma triangle_6 : NoExtend 6 := by
  unfold NoExtend
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma edge_7 : EdgesFrom 7 := by
  unfold EdgesFrom
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma triangle_7 : NoExtend 7 := by
  unfold NoExtend
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma edge_8 : EdgesFrom 8 := by
  unfold EdgesFrom
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma triangle_8 : NoExtend 8 := by
  unfold NoExtend
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma edge_9 : EdgesFrom 9 := by
  unfold EdgesFrom
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma triangle_9 : NoExtend 9 := by
  unfold NoExtend
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma edge_10 : EdgesFrom 10 := by
  unfold EdgesFrom
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma triangle_10 : NoExtend 10 := by
  unfold NoExtend
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma edge_11 : EdgesFrom 11 := by
  unfold EdgesFrom
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma triangle_11 : NoExtend 11 := by
  unfold NoExtend
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma edge_12 : EdgesFrom 12 := by
  unfold EdgesFrom
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma triangle_12 : NoExtend 12 := by
  unfold NoExtend
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma edge_13 : EdgesFrom 13 := by
  unfold EdgesFrom
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma triangle_13 : NoExtend 13 := by
  unfold NoExtend
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma edge_14 : EdgesFrom 14 := by
  unfold EdgesFrom
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma triangle_14 : NoExtend 14 := by
  unfold NoExtend
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma edge_15 : EdgesFrom 15 := by
  unfold EdgesFrom
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma triangle_15 : NoExtend 15 := by
  unfold NoExtend
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma edge_16 : EdgesFrom 16 := by
  unfold EdgesFrom
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma triangle_16 : NoExtend 16 := by
  unfold NoExtend
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma edge_17 : EdgesFrom 17 := by
  unfold EdgesFrom
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma triangle_17 : NoExtend 17 := by
  unfold NoExtend
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma edge_18 : EdgesFrom 18 := by
  unfold EdgesFrom
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma triangle_18 : NoExtend 18 := by
  unfold NoExtend
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma edge_19 : EdgesFrom 19 := by
  unfold EdgesFrom
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma triangle_19 : NoExtend 19 := by
  unfold NoExtend
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma edge_20 : EdgesFrom 20 := by
  unfold EdgesFrom
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma triangle_20 : NoExtend 20 := by
  unfold NoExtend
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma edge_21 : EdgesFrom 21 := by
  unfold EdgesFrom
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma triangle_21 : NoExtend 21 := by
  unfold NoExtend
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma edge_22 : EdgesFrom 22 := by
  unfold EdgesFrom
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma triangle_22 : NoExtend 22 := by
  unfold NoExtend
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma edge_23 : EdgesFrom 23 := by
  unfold EdgesFrom
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma triangle_23 : NoExtend 23 := by
  unfold NoExtend
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma edge_24 : EdgesFrom 24 := by
  unfold EdgesFrom
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma triangle_24 : NoExtend 24 := by
  unfold NoExtend
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma edge_25 : EdgesFrom 25 := by
  unfold EdgesFrom
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma triangle_25 : NoExtend 25 := by
  unfold NoExtend
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma edge_26 : EdgesFrom 26 := by
  unfold EdgesFrom
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma triangle_26 : NoExtend 26 := by
  unfold NoExtend
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma edge_27 : EdgesFrom 27 := by
  unfold EdgesFrom
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma triangle_27 : NoExtend 27 := by
  unfold NoExtend
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma edge_28 : EdgesFrom 28 := by
  unfold EdgesFrom
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma triangle_28 : NoExtend 28 := by
  unfold NoExtend
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma edge_29 : EdgesFrom 29 := by
  unfold EdgesFrom
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma triangle_29 : NoExtend 29 := by
  unfold NoExtend
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma edge_30 : EdgesFrom 30 := by
  unfold EdgesFrom
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma triangle_30 : NoExtend 30 := by
  unfold NoExtend
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma edge_31 : EdgesFrom 31 := by
  unfold EdgesFrom
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma triangle_31 : NoExtend 31 := by
  unfold NoExtend
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma edge_32 : EdgesFrom 32 := by
  unfold EdgesFrom
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma triangle_32 : NoExtend 32 := by
  unfold NoExtend
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma edge_33 : EdgesFrom 33 := by
  unfold EdgesFrom
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma triangle_33 : NoExtend 33 := by
  unfold NoExtend
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma edge_34 : EdgesFrom 34 := by
  unfold EdgesFrom
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma triangle_34 : NoExtend 34 := by
  unfold NoExtend
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma edge_35 : EdgesFrom 35 := by
  unfold EdgesFrom
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma triangle_35 : NoExtend 35 := by
  unfold NoExtend
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma edge_36 : EdgesFrom 36 := by
  unfold EdgesFrom
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma triangle_36 : NoExtend 36 := by
  unfold NoExtend
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma edge_37 : EdgesFrom 37 := by
  unfold EdgesFrom
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma triangle_37 : NoExtend 37 := by
  unfold NoExtend
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma edge_38 : EdgesFrom 38 := by
  unfold EdgesFrom
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma triangle_38 : NoExtend 38 := by
  unfold NoExtend
  decide

lemma edges_from (a : Fin 39) : EdgesFrom a := by
  fin_cases a
  · exact edge_0
  · exact edge_1
  · exact edge_2
  · exact edge_3
  · exact edge_4
  · exact edge_5
  · exact edge_6
  · exact edge_7
  · exact edge_8
  · exact edge_9
  · exact edge_10
  · exact edge_11
  · exact edge_12
  · exact edge_13
  · exact edge_14
  · exact edge_15
  · exact edge_16
  · exact edge_17
  · exact edge_18
  · exact edge_19
  · exact edge_20
  · exact edge_21
  · exact edge_22
  · exact edge_23
  · exact edge_24
  · exact edge_25
  · exact edge_26
  · exact edge_27
  · exact edge_28
  · exact edge_29
  · exact edge_30
  · exact edge_31
  · exact edge_32
  · exact edge_33
  · exact edge_34
  · exact edge_35
  · exact edge_36
  · exact edge_37
  · exact edge_38

lemma no_extend (a : Fin 39) : NoExtend a := by
  fin_cases a
  · exact triangle_0
  · exact triangle_1
  · exact triangle_2
  · exact triangle_3
  · exact triangle_4
  · exact triangle_5
  · exact triangle_6
  · exact triangle_7
  · exact triangle_8
  · exact triangle_9
  · exact triangle_10
  · exact triangle_11
  · exact triangle_12
  · exact triangle_13
  · exact triangle_14
  · exact triangle_15
  · exact triangle_16
  · exact triangle_17
  · exact triangle_18
  · exact triangle_19
  · exact triangle_20
  · exact triangle_21
  · exact triangle_22
  · exact triangle_23
  · exact triangle_24
  · exact triangle_25
  · exact triangle_26
  · exact triangle_27
  · exact triangle_28
  · exact triangle_29
  · exact triangle_30
  · exact triangle_31
  · exact triangle_32
  · exact triangle_33
  · exact triangle_34
  · exact triangle_35
  · exact triangle_36
  · exact triangle_37
  · exact triangle_38

def Valid (r : Rect) : Prop :=
  ∀ i ∈ r.1, ∀ j ∈ r.2, entry i j = false

def hits (r : Rect) : Finset (Fin 39) :=
  Finset.univ.filter fun a => row a ∈ r.1 ∧ col a ∈ r.2

lemma hit_edge (r : Rect) (hr : Valid r) (a b : Fin 39)
    (ha : a ∈ hits r) (hb : b ∈ hits r) (hne : a ≠ b) :
    b ∈ neighbors a := by
  have ha' := (Finset.mem_filter.mp ha).2
  have hb' := (Finset.mem_filter.mp hb).2
  exact edges_from a b (Finset.mem_univ b) hne
    (hr (row a) ha'.1 (col b) hb'.2)
    (hr (row b) hb'.1 (col a) ha'.2)

lemma hit_bound (r : Rect) (hr : Valid r) : (hits r).card ≤ 3 := by
  by_contra h
  let S := hits r
  have hs : 3 < S.card := by
    change ¬ S.card ≤ 3 at h
    omega
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (show 0 < S.card by omega)
  let S1 := S.erase a
  have h1 : S1.card = S.card - 1 := Finset.card_erase_of_mem ha
  obtain ⟨b, hb⟩ := Finset.card_pos.mp (show 0 < S1.card by omega)
  let S2 := S1.erase b
  have h2 : S2.card = S1.card - 1 := Finset.card_erase_of_mem hb
  obtain ⟨c, hc⟩ := Finset.card_pos.mp (show 0 < S2.card by omega)
  let S3 := S2.erase c
  have h3 : S3.card = S2.card - 1 := Finset.card_erase_of_mem hc
  obtain ⟨d, hd⟩ := Finset.card_pos.mp (show 0 < S3.card by omega)
  have hb' : b ≠ a ∧ b ∈ S := Finset.mem_erase.mp hb
  have hc' : c ≠ b ∧ c ∈ S1 := Finset.mem_erase.mp hc
  have hc'' : c ≠ a ∧ c ∈ S := Finset.mem_erase.mp hc'.2
  have hd' : d ≠ c ∧ d ∈ S2 := Finset.mem_erase.mp hd
  have hd'' : d ≠ b ∧ d ∈ S1 := Finset.mem_erase.mp hd'.2
  have hd''' : d ≠ a ∧ d ∈ S := Finset.mem_erase.mp hd''.2
  have hbN : b ∈ neighbors a := hit_edge r hr a b ha hb'.2 (Ne.symm hb'.1)
  have hcN : c ∈ neighbors a ∩ neighbors b := Finset.mem_inter.mpr
    ⟨hit_edge r hr a c ha hc''.2 (Ne.symm hc''.1),
     hit_edge r hr b c hb'.2 hc''.2 (Ne.symm hc'.1)⟩
  have hdN : d ∈ (neighbors a ∩ neighbors b) ∩ neighbors c :=
    Finset.mem_inter.mpr
      ⟨Finset.mem_inter.mpr
        ⟨hit_edge r hr a d ha hd'''.2 (Ne.symm hd'''.1),
         hit_edge r hr b d hb'.2 hd'''.2 (Ne.symm hd''.1)⟩,
       hit_edge r hr c d hc''.2 hd'''.2 (Ne.symm hd'.1)⟩
  have he := no_extend a b hbN c hcN
  rw [he] at hdN
  simp at hdN

def covered (L : List Rect) : Finset (Fin 39) :=
  L.foldr (fun r s => hits r ∪ s) ∅

lemma covered_bound (L : List Rect) :
    (∀ r ∈ L, Valid r) → (covered L).card ≤ 3 * L.length := by
  induction L with
  | nil => intro h; simp [covered]
  | cons r L ih =>
    intro h
    have hr := hit_bound r (h r (by simp))
    have ht := ih (fun s hs => h s (List.mem_cons_of_mem _ hs))
    have hu := Finset.card_union_le (hits r) (covered L)
    change (hits r ∪ covered L).card ≤ 3 * (L.length + 1)
    omega

lemma covered_mem (L : List Rect) (a : Fin 39) :
    (∃ r ∈ L, a ∈ hits r) → a ∈ covered L := by
  induction L with
  | nil =>
    rintro ⟨r, hr, ha⟩
    simp at hr
  | cons r L ih =>
    rintro ⟨s, hs, ha⟩
    change a ∈ hits r ∪ covered L
    rcases List.mem_cons.mp hs with he | hs
    · subst s
      exact Finset.mem_union.mpr (Or.inl ha)
    · exact Finset.mem_union.mpr (Or.inr (ih ⟨s, hs, ha⟩))

end PEqualNP.Outside.L_meta_10044

open PEqualNP.Outside.L_meta_10044

theorem PEqualNP.Outside.L_meta_10044 : ¬ (∃ L : List (Finset (Fin 13) × Finset (Fin 13)), L.length ≤ 12 ∧ (∀ r ∈ L, ∀ i ∈ r.1, ∀ j ∈ r.2, (([5658, 3125, 6250, 4309, 427, 854, 1708, 3416, 6832, 5473, 2755, 5510, 2829] : List ℕ).getD i.val 0).testBit j.val = false) ∧ ∀ (i : Fin 13) (j : Fin 13), (([5658, 3125, 6250, 4309, 427, 854, 1708, 3416, 6832, 5473, 2755, 5510, 2829] : List ℕ).getD i.val 0).testBit j.val = false → ∃ r ∈ L, i ∈ r.1 ∧ j ∈ r.2) := by
  rintro ⟨L, hlen, hvalid, hcover⟩
  have hupper := covered_bound L hvalid
  have hs : (Finset.univ : Finset (Fin 39)) ⊆ covered L := by
    intro a ha
    obtain ⟨r, hr, hi, hj⟩ := hcover (row a) (col a) (selected_zero a)
    exact covered_mem L a ⟨r, hr, Finset.mem_filter.mpr
      ⟨Finset.mem_univ a, hi, hj⟩⟩
  have hlower : 39 ≤ (covered L).card := by
    simpa using Finset.card_le_card hs
  omega
