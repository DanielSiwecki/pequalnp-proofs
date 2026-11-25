import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10046

abbrev V := Fin 17
abbrev Rect := Finset V × Finset V

def entry (i j : V) : Bool :=
  (([107286, 83501, 35931, 71862, 12653, 25306, 50612, 101224, 71377, 11683, 23366, 46732, 93464, 55857, 111714, 92357, 53643] : List ℕ).getD i.val 0).testBit j.val

def zeroRow (i : V) : Finset V :=
  ([{0, 3, 5, 6, 7, 10, 11, 12, 14},
    {1, 4, 6, 7, 8, 11, 12, 13, 15},
    {2, 5, 7, 8, 9, 12, 13, 14, 16},
    {0, 3, 6, 8, 9, 10, 13, 14, 15},
    {1, 4, 7, 9, 10, 11, 14, 15, 16},
    {0, 2, 5, 8, 10, 11, 12, 15, 16},
    {0, 1, 3, 6, 9, 11, 12, 13, 16},
    {0, 1, 2, 4, 7, 10, 12, 13, 14},
    {1, 2, 3, 5, 8, 11, 13, 14, 15},
    {2, 3, 4, 6, 9, 12, 14, 15, 16},
    {0, 3, 4, 5, 7, 10, 13, 15, 16},
    {0, 1, 4, 5, 6, 8, 11, 14, 16},
    {0, 1, 2, 5, 6, 7, 9, 12, 15},
    {1, 2, 3, 6, 7, 8, 10, 13, 16},
    {0, 2, 3, 4, 7, 8, 9, 11, 14},
    {1, 3, 4, 5, 8, 9, 10, 12, 15},
    {2, 4, 5, 6, 9, 10, 11, 13, 16}] : List (Finset V)).getD i.val ∅

def off (R C : Finset V) : Finset (V × V) :=
  (R ×ˢ C).filter fun p => p.1 ≠ p.2

def RowCert (i : V) : Prop :=
  (off {i} (zeroRow i)).card ≤ 8 ∧
    ∀ j ∈ (Finset.univ : Finset V),
      (j ∈ zeroRow i ↔ entry i j = false) ∧ entry i j = entry j i

def PairCert (a b : V) : Prop :=
  (off {a, b} (zeroRow a ∩ zeroRow b)).card ≤ 8 ∧
    ∀ c ∈ (Finset.univ : Finset V), b < c →
      ((zeroRow a ∩ zeroRow b) ∩ zeroRow c).card ≤ 3 ∧
      (off {a, b, c} ((zeroRow a ∩ zeroRow b) ∩ zeroRow c)).card ≤ 8

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row_0 : RowCert 0 := by
  unfold RowCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row_1 : RowCert 1 := by
  unfold RowCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row_2 : RowCert 2 := by
  unfold RowCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row_3 : RowCert 3 := by
  unfold RowCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row_4 : RowCert 4 := by
  unfold RowCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row_5 : RowCert 5 := by
  unfold RowCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row_6 : RowCert 6 := by
  unfold RowCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row_7 : RowCert 7 := by
  unfold RowCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row_8 : RowCert 8 := by
  unfold RowCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row_9 : RowCert 9 := by
  unfold RowCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row_10 : RowCert 10 := by
  unfold RowCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row_11 : RowCert 11 := by
  unfold RowCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row_12 : RowCert 12 := by
  unfold RowCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row_13 : RowCert 13 := by
  unfold RowCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row_14 : RowCert 14 := by
  unfold RowCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row_15 : RowCert 15 := by
  unfold RowCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row_16 : RowCert 16 := by
  unfold RowCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_0_1 : PairCert 0 1 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_0_2 : PairCert 0 2 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_0_3 : PairCert 0 3 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_0_4 : PairCert 0 4 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_0_5 : PairCert 0 5 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_0_6 : PairCert 0 6 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_0_7 : PairCert 0 7 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_0_8 : PairCert 0 8 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_0_9 : PairCert 0 9 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_0_10 : PairCert 0 10 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_0_11 : PairCert 0 11 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_0_12 : PairCert 0 12 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_0_13 : PairCert 0 13 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_0_14 : PairCert 0 14 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_0_15 : PairCert 0 15 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_0_16 : PairCert 0 16 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_1_2 : PairCert 1 2 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_1_3 : PairCert 1 3 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_1_4 : PairCert 1 4 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_1_5 : PairCert 1 5 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_1_6 : PairCert 1 6 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_1_7 : PairCert 1 7 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_1_8 : PairCert 1 8 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_1_9 : PairCert 1 9 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_1_10 : PairCert 1 10 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_1_11 : PairCert 1 11 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_1_12 : PairCert 1 12 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_1_13 : PairCert 1 13 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_1_14 : PairCert 1 14 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_1_15 : PairCert 1 15 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_1_16 : PairCert 1 16 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_2_3 : PairCert 2 3 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_2_4 : PairCert 2 4 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_2_5 : PairCert 2 5 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_2_6 : PairCert 2 6 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_2_7 : PairCert 2 7 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_2_8 : PairCert 2 8 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_2_9 : PairCert 2 9 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_2_10 : PairCert 2 10 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_2_11 : PairCert 2 11 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_2_12 : PairCert 2 12 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_2_13 : PairCert 2 13 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_2_14 : PairCert 2 14 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_2_15 : PairCert 2 15 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_2_16 : PairCert 2 16 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_3_4 : PairCert 3 4 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_3_5 : PairCert 3 5 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_3_6 : PairCert 3 6 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_3_7 : PairCert 3 7 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_3_8 : PairCert 3 8 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_3_9 : PairCert 3 9 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_3_10 : PairCert 3 10 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_3_11 : PairCert 3 11 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_3_12 : PairCert 3 12 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_3_13 : PairCert 3 13 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_3_14 : PairCert 3 14 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_3_15 : PairCert 3 15 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_3_16 : PairCert 3 16 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_4_5 : PairCert 4 5 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_4_6 : PairCert 4 6 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_4_7 : PairCert 4 7 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_4_8 : PairCert 4 8 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_4_9 : PairCert 4 9 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_4_10 : PairCert 4 10 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_4_11 : PairCert 4 11 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_4_12 : PairCert 4 12 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_4_13 : PairCert 4 13 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_4_14 : PairCert 4 14 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_4_15 : PairCert 4 15 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_4_16 : PairCert 4 16 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_5_6 : PairCert 5 6 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_5_7 : PairCert 5 7 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_5_8 : PairCert 5 8 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_5_9 : PairCert 5 9 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_5_10 : PairCert 5 10 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_5_11 : PairCert 5 11 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_5_12 : PairCert 5 12 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_5_13 : PairCert 5 13 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_5_14 : PairCert 5 14 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_5_15 : PairCert 5 15 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_5_16 : PairCert 5 16 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_6_7 : PairCert 6 7 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_6_8 : PairCert 6 8 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_6_9 : PairCert 6 9 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_6_10 : PairCert 6 10 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_6_11 : PairCert 6 11 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_6_12 : PairCert 6 12 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_6_13 : PairCert 6 13 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_6_14 : PairCert 6 14 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_6_15 : PairCert 6 15 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_6_16 : PairCert 6 16 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_7_8 : PairCert 7 8 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_7_9 : PairCert 7 9 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_7_10 : PairCert 7 10 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_7_11 : PairCert 7 11 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_7_12 : PairCert 7 12 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_7_13 : PairCert 7 13 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_7_14 : PairCert 7 14 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_7_15 : PairCert 7 15 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_7_16 : PairCert 7 16 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_8_9 : PairCert 8 9 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_8_10 : PairCert 8 10 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_8_11 : PairCert 8 11 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_8_12 : PairCert 8 12 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_8_13 : PairCert 8 13 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_8_14 : PairCert 8 14 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_8_15 : PairCert 8 15 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_8_16 : PairCert 8 16 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_9_10 : PairCert 9 10 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_9_11 : PairCert 9 11 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_9_12 : PairCert 9 12 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_9_13 : PairCert 9 13 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_9_14 : PairCert 9 14 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_9_15 : PairCert 9 15 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_9_16 : PairCert 9 16 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_10_11 : PairCert 10 11 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_10_12 : PairCert 10 12 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_10_13 : PairCert 10 13 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_10_14 : PairCert 10 14 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_10_15 : PairCert 10 15 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_10_16 : PairCert 10 16 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_11_12 : PairCert 11 12 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_11_13 : PairCert 11 13 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_11_14 : PairCert 11 14 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_11_15 : PairCert 11 15 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_11_16 : PairCert 11 16 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_12_13 : PairCert 12 13 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_12_14 : PairCert 12 14 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_12_15 : PairCert 12 15 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_12_16 : PairCert 12 16 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_13_14 : PairCert 13 14 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_13_15 : PairCert 13 15 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_13_16 : PairCert 13 16 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_14_15 : PairCert 14 15 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_14_16 : PairCert 14 16 := by
  unfold PairCert
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma pair_15_16 : PairCert 15 16 := by
  unfold PairCert
  decide

lemma row_cert (a : V) : RowCert a := by
  fin_cases a
  · exact row_0
  · exact row_1
  · exact row_2
  · exact row_3
  · exact row_4
  · exact row_5
  · exact row_6
  · exact row_7
  · exact row_8
  · exact row_9
  · exact row_10
  · exact row_11
  · exact row_12
  · exact row_13
  · exact row_14
  · exact row_15
  · exact row_16

set_option maxHeartbeats 4000000 in
lemma pair_cert (a b : V) (hab : a < b) : PairCert a b := by
  fin_cases a
  · fin_cases b
    · exact False.elim ((show ¬ ((0 : V) < (0 : V)) by decide) hab)
    · exact pair_0_1
    · exact pair_0_2
    · exact pair_0_3
    · exact pair_0_4
    · exact pair_0_5
    · exact pair_0_6
    · exact pair_0_7
    · exact pair_0_8
    · exact pair_0_9
    · exact pair_0_10
    · exact pair_0_11
    · exact pair_0_12
    · exact pair_0_13
    · exact pair_0_14
    · exact pair_0_15
    · exact pair_0_16
  · fin_cases b
    · exact False.elim ((show ¬ ((1 : V) < (0 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((1 : V) < (1 : V)) by decide) hab)
    · exact pair_1_2
    · exact pair_1_3
    · exact pair_1_4
    · exact pair_1_5
    · exact pair_1_6
    · exact pair_1_7
    · exact pair_1_8
    · exact pair_1_9
    · exact pair_1_10
    · exact pair_1_11
    · exact pair_1_12
    · exact pair_1_13
    · exact pair_1_14
    · exact pair_1_15
    · exact pair_1_16
  · fin_cases b
    · exact False.elim ((show ¬ ((2 : V) < (0 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((2 : V) < (1 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((2 : V) < (2 : V)) by decide) hab)
    · exact pair_2_3
    · exact pair_2_4
    · exact pair_2_5
    · exact pair_2_6
    · exact pair_2_7
    · exact pair_2_8
    · exact pair_2_9
    · exact pair_2_10
    · exact pair_2_11
    · exact pair_2_12
    · exact pair_2_13
    · exact pair_2_14
    · exact pair_2_15
    · exact pair_2_16
  · fin_cases b
    · exact False.elim ((show ¬ ((3 : V) < (0 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((3 : V) < (1 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((3 : V) < (2 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((3 : V) < (3 : V)) by decide) hab)
    · exact pair_3_4
    · exact pair_3_5
    · exact pair_3_6
    · exact pair_3_7
    · exact pair_3_8
    · exact pair_3_9
    · exact pair_3_10
    · exact pair_3_11
    · exact pair_3_12
    · exact pair_3_13
    · exact pair_3_14
    · exact pair_3_15
    · exact pair_3_16
  · fin_cases b
    · exact False.elim ((show ¬ ((4 : V) < (0 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((4 : V) < (1 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((4 : V) < (2 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((4 : V) < (3 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((4 : V) < (4 : V)) by decide) hab)
    · exact pair_4_5
    · exact pair_4_6
    · exact pair_4_7
    · exact pair_4_8
    · exact pair_4_9
    · exact pair_4_10
    · exact pair_4_11
    · exact pair_4_12
    · exact pair_4_13
    · exact pair_4_14
    · exact pair_4_15
    · exact pair_4_16
  · fin_cases b
    · exact False.elim ((show ¬ ((5 : V) < (0 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((5 : V) < (1 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((5 : V) < (2 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((5 : V) < (3 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((5 : V) < (4 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((5 : V) < (5 : V)) by decide) hab)
    · exact pair_5_6
    · exact pair_5_7
    · exact pair_5_8
    · exact pair_5_9
    · exact pair_5_10
    · exact pair_5_11
    · exact pair_5_12
    · exact pair_5_13
    · exact pair_5_14
    · exact pair_5_15
    · exact pair_5_16
  · fin_cases b
    · exact False.elim ((show ¬ ((6 : V) < (0 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((6 : V) < (1 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((6 : V) < (2 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((6 : V) < (3 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((6 : V) < (4 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((6 : V) < (5 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((6 : V) < (6 : V)) by decide) hab)
    · exact pair_6_7
    · exact pair_6_8
    · exact pair_6_9
    · exact pair_6_10
    · exact pair_6_11
    · exact pair_6_12
    · exact pair_6_13
    · exact pair_6_14
    · exact pair_6_15
    · exact pair_6_16
  · fin_cases b
    · exact False.elim ((show ¬ ((7 : V) < (0 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((7 : V) < (1 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((7 : V) < (2 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((7 : V) < (3 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((7 : V) < (4 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((7 : V) < (5 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((7 : V) < (6 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((7 : V) < (7 : V)) by decide) hab)
    · exact pair_7_8
    · exact pair_7_9
    · exact pair_7_10
    · exact pair_7_11
    · exact pair_7_12
    · exact pair_7_13
    · exact pair_7_14
    · exact pair_7_15
    · exact pair_7_16
  · fin_cases b
    · exact False.elim ((show ¬ ((8 : V) < (0 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((8 : V) < (1 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((8 : V) < (2 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((8 : V) < (3 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((8 : V) < (4 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((8 : V) < (5 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((8 : V) < (6 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((8 : V) < (7 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((8 : V) < (8 : V)) by decide) hab)
    · exact pair_8_9
    · exact pair_8_10
    · exact pair_8_11
    · exact pair_8_12
    · exact pair_8_13
    · exact pair_8_14
    · exact pair_8_15
    · exact pair_8_16
  · fin_cases b
    · exact False.elim ((show ¬ ((9 : V) < (0 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((9 : V) < (1 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((9 : V) < (2 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((9 : V) < (3 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((9 : V) < (4 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((9 : V) < (5 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((9 : V) < (6 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((9 : V) < (7 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((9 : V) < (8 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((9 : V) < (9 : V)) by decide) hab)
    · exact pair_9_10
    · exact pair_9_11
    · exact pair_9_12
    · exact pair_9_13
    · exact pair_9_14
    · exact pair_9_15
    · exact pair_9_16
  · fin_cases b
    · exact False.elim ((show ¬ ((10 : V) < (0 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((10 : V) < (1 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((10 : V) < (2 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((10 : V) < (3 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((10 : V) < (4 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((10 : V) < (5 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((10 : V) < (6 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((10 : V) < (7 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((10 : V) < (8 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((10 : V) < (9 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((10 : V) < (10 : V)) by decide) hab)
    · exact pair_10_11
    · exact pair_10_12
    · exact pair_10_13
    · exact pair_10_14
    · exact pair_10_15
    · exact pair_10_16
  · fin_cases b
    · exact False.elim ((show ¬ ((11 : V) < (0 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((11 : V) < (1 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((11 : V) < (2 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((11 : V) < (3 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((11 : V) < (4 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((11 : V) < (5 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((11 : V) < (6 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((11 : V) < (7 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((11 : V) < (8 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((11 : V) < (9 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((11 : V) < (10 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((11 : V) < (11 : V)) by decide) hab)
    · exact pair_11_12
    · exact pair_11_13
    · exact pair_11_14
    · exact pair_11_15
    · exact pair_11_16
  · fin_cases b
    · exact False.elim ((show ¬ ((12 : V) < (0 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((12 : V) < (1 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((12 : V) < (2 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((12 : V) < (3 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((12 : V) < (4 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((12 : V) < (5 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((12 : V) < (6 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((12 : V) < (7 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((12 : V) < (8 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((12 : V) < (9 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((12 : V) < (10 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((12 : V) < (11 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((12 : V) < (12 : V)) by decide) hab)
    · exact pair_12_13
    · exact pair_12_14
    · exact pair_12_15
    · exact pair_12_16
  · fin_cases b
    · exact False.elim ((show ¬ ((13 : V) < (0 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((13 : V) < (1 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((13 : V) < (2 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((13 : V) < (3 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((13 : V) < (4 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((13 : V) < (5 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((13 : V) < (6 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((13 : V) < (7 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((13 : V) < (8 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((13 : V) < (9 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((13 : V) < (10 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((13 : V) < (11 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((13 : V) < (12 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((13 : V) < (13 : V)) by decide) hab)
    · exact pair_13_14
    · exact pair_13_15
    · exact pair_13_16
  · fin_cases b
    · exact False.elim ((show ¬ ((14 : V) < (0 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((14 : V) < (1 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((14 : V) < (2 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((14 : V) < (3 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((14 : V) < (4 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((14 : V) < (5 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((14 : V) < (6 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((14 : V) < (7 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((14 : V) < (8 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((14 : V) < (9 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((14 : V) < (10 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((14 : V) < (11 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((14 : V) < (12 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((14 : V) < (13 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((14 : V) < (14 : V)) by decide) hab)
    · exact pair_14_15
    · exact pair_14_16
  · fin_cases b
    · exact False.elim ((show ¬ ((15 : V) < (0 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((15 : V) < (1 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((15 : V) < (2 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((15 : V) < (3 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((15 : V) < (4 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((15 : V) < (5 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((15 : V) < (6 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((15 : V) < (7 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((15 : V) < (8 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((15 : V) < (9 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((15 : V) < (10 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((15 : V) < (11 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((15 : V) < (12 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((15 : V) < (13 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((15 : V) < (14 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((15 : V) < (15 : V)) by decide) hab)
    · exact pair_15_16
  · fin_cases b
    · exact False.elim ((show ¬ ((16 : V) < (0 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((16 : V) < (1 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((16 : V) < (2 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((16 : V) < (3 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((16 : V) < (4 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((16 : V) < (5 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((16 : V) < (6 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((16 : V) < (7 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((16 : V) < (8 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((16 : V) < (9 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((16 : V) < (10 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((16 : V) < (11 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((16 : V) < (12 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((16 : V) < (13 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((16 : V) < (14 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((16 : V) < (15 : V)) by decide) hab)
    · exact False.elim ((show ¬ ((16 : V) < (16 : V)) by decide) hab)

lemma row_iff (a b : V) : b ∈ zeroRow a ↔ entry a b = false :=
  ((row_cert a).2 b (Finset.mem_univ b)).1

lemma entry_symm (a b : V) : entry a b = entry b a :=
  ((row_cert a).2 b (Finset.mem_univ b)).2

lemma off_mono {R R' C C' : Finset V} (hr : R ⊆ R') (hc : C ⊆ C') :
    off R C ⊆ off R' C' := by
  intro p hp
  have h := Finset.mem_filter.mp hp
  have h' := Finset.mem_product.mp h.1
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_product.mpr ⟨hr h'.1, hc h'.2⟩, h.2⟩

lemma off_swap (R C : Finset V) : (off R C).card = (off C R).card := by
  apply Finset.card_bij (fun p _ => (p.2, p.1))
  · intro p hp
    have h := Finset.mem_filter.mp hp
    have h' := Finset.mem_product.mp h.1
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨h'.2, h'.1⟩, Ne.symm h.2⟩
  · intro p hp q hq he
    exact Prod.ext (congrArg Prod.snd he) (congrArg Prod.fst he)
  · intro q hq
    have h := Finset.mem_filter.mp hq
    have h' := Finset.mem_product.mp h.1
    refine ⟨(q.2, q.1), ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨h'.2, h'.1⟩, Ne.symm h.2⟩
    · cases q
      rfl

def Valid (r : Rect) : Prop :=
  ∀ i ∈ r.1, ∀ j ∈ r.2, entry i j = false

lemma row_subset (R C : Finset V) (hv : Valid (R, C)) (a : V) (ha : a ∈ R) :
    C ⊆ zeroRow a := by
  intro j hj
  exact (row_iff a j).mpr (hv a ha j hj)

lemma row_analysis (R C : Finset V) (hv : Valid (R, C)) :
    (R.card ≤ 3 → (off R C).card ≤ 8) ∧ (3 ≤ R.card → C.card ≤ 3) := by
  by_cases h0 : R.card = 0
  · have he := Finset.card_eq_zero.mp h0
    constructor
    · intro _
      simp [he, off]
    · omega
  have hR : R.Nonempty := Finset.card_pos.mp (by omega)
  let a := R.min' hR
  have ha : a ∈ R := Finset.min'_mem R hR
  let A := R.erase a
  have hA : A.card = R.card - 1 := Finset.card_erase_of_mem ha
  have heA : insert a A = R := Finset.insert_erase ha
  have hCa := row_subset R C hv a ha
  by_cases h1 : A.card = 0
  · have he := Finset.card_eq_zero.mp h1
    have hEq : R = {a} := by
      rw [he] at heA
      exact heA.symm
    constructor
    · intro _
      rw [hEq]
      exact le_trans (Finset.card_le_card (off_mono (fun _ h => h) hCa)) (row_cert a).1
    · omega
  have hAn : A.Nonempty := Finset.card_pos.mp (by omega)
  let b := A.min' hAn
  have hb : b ∈ A := Finset.min'_mem A hAn
  have hb' : b ≠ a ∧ b ∈ R := Finset.mem_erase.mp hb
  have hab : a < b := lt_of_le_of_ne (Finset.min'_le R b hb'.2) (Ne.symm hb'.1)
  let B := A.erase b
  have hB : B.card = A.card - 1 := Finset.card_erase_of_mem hb
  have heB : insert b B = A := Finset.insert_erase hb
  have hCb := row_subset R C hv b hb'.2
  have hCab : C ⊆ zeroRow a ∩ zeroRow b := by
    intro j hj
    exact Finset.mem_inter.mpr ⟨hCa hj, hCb hj⟩
  have hp := pair_cert a b hab
  by_cases h2 : B.card = 0
  · have he := Finset.card_eq_zero.mp h2
    have hEq : R = {a, b} := by
      rw [← heA, ← heB, he]
      rfl
    constructor
    · intro _
      rw [hEq]
      exact le_trans (Finset.card_le_card (off_mono (fun _ h => h) hCab)) hp.1
    · omega
  have hBn : B.Nonempty := Finset.card_pos.mp (by omega)
  let c := B.min' hBn
  have hc : c ∈ B := Finset.min'_mem B hBn
  have hc' : c ≠ b ∧ c ∈ A := Finset.mem_erase.mp hc
  have hc'' : c ≠ a ∧ c ∈ R := Finset.mem_erase.mp hc'.2
  have hbc : b < c := lt_of_le_of_ne (Finset.min'_le A c hc'.2) (Ne.symm hc'.1)
  have hCc := row_subset R C hv c hc''.2
  have hCabc : C ⊆ (zeroRow a ∩ zeroRow b) ∩ zeroRow c := by
    intro j hj
    exact Finset.mem_inter.mpr ⟨hCab hj, hCc hj⟩
  have ht := hp.2 c (Finset.mem_univ c) hbc
  constructor
  · intro hsmall
    let D := B.erase c
    have hD : D.card = B.card - 1 := Finset.card_erase_of_mem hc
    have heD : insert c D = B := Finset.insert_erase hc
    have he : D = ∅ := Finset.card_eq_zero.mp (by omega)
    have hEq : R = {a, b, c} := by
      rw [← heA, ← heB, ← heD, he]
      rfl
    rw [hEq]
    exact le_trans (Finset.card_le_card (off_mono (fun _ h => h) hCabc)) ht.2
  · intro _
    exact le_trans (Finset.card_le_card hCabc) ht.1

lemma hit_bound (r : Rect) (hr : Valid r) : (off r.1 r.2).card ≤ 8 := by
  have h := row_analysis r.1 r.2 hr
  by_cases hs : r.1.card ≤ 3
  · exact h.1 hs
  · have hC : r.2.card ≤ 3 := h.2 (by omega)
    have hv : Valid (r.2, r.1) := by
      intro i hi j hj
      rw [entry_symm i j]
      exact hr j hj i hi
    rw [off_swap]
    exact (row_analysis r.2 r.1 hv).1 hC

def selected : Finset (V × V) :=
  Finset.univ.filter fun p => p.1 ≠ p.2 ∧ entry p.1 p.2 = false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma selected_card : selected.card = 136 := by decide

def covered (L : List Rect) : Finset (V × V) :=
  L.foldr (fun r s => off r.1 r.2 ∪ s) ∅

lemma covered_bound (L : List Rect) :
    (∀ r ∈ L, Valid r) → (covered L).card ≤ 8 * L.length := by
  induction L with
  | nil => intro h; simp [covered]
  | cons r L ih =>
    intro h
    have hr := hit_bound r (h r (by simp))
    have ht := ih (fun s hs => h s (List.mem_cons_of_mem _ hs))
    have hu := Finset.card_union_le (off r.1 r.2) (covered L)
    change (off r.1 r.2 ∪ covered L).card ≤ 8 * (L.length + 1)
    omega

lemma covered_mem (L : List Rect) (p : V × V) :
    (∃ r ∈ L, p ∈ off r.1 r.2) → p ∈ covered L := by
  induction L with
  | nil =>
    rintro ⟨r, hr, hp⟩
    simp at hr
  | cons r L ih =>
    rintro ⟨s, hs, hp⟩
    change p ∈ off r.1 r.2 ∪ covered L
    rcases List.mem_cons.mp hs with he | hs
    · subst s
      exact Finset.mem_union.mpr (Or.inl hp)
    · exact Finset.mem_union.mpr (Or.inr (ih ⟨s, hs, hp⟩))

end PEqualNP.Outside.L_meta_10046

open PEqualNP.Outside.L_meta_10046

theorem PEqualNP.Outside.L_meta_10046 : ¬ (∃ L : List (Finset (Fin 17) × Finset (Fin 17)), L.length ≤ 16 ∧ (∀ r ∈ L, ∀ i ∈ r.1, ∀ j ∈ r.2, (([107286, 83501, 35931, 71862, 12653, 25306, 50612, 101224, 71377, 11683, 23366, 46732, 93464, 55857, 111714, 92357, 53643] : List ℕ).getD i.val 0).testBit j.val = false) ∧ ∀ (i : Fin 17) (j : Fin 17), (([107286, 83501, 35931, 71862, 12653, 25306, 50612, 101224, 71377, 11683, 23366, 46732, 93464, 55857, 111714, 92357, 53643] : List ℕ).getD i.val 0).testBit j.val = false → ∃ r ∈ L, i ∈ r.1 ∧ j ∈ r.2) := by
  rintro ⟨L, hlen, hvalid, hcover⟩
  have hupper := covered_bound L hvalid
  have hs : selected ⊆ covered L := by
    intro p hp
    have h := (Finset.mem_filter.mp hp).2
    obtain ⟨r, hr, hi, hj⟩ := hcover p.1 p.2 h.2
    exact covered_mem L p ⟨r, hr, Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hi, hj⟩, h.1⟩⟩
  have hlower := Finset.card_le_card hs
  rw [selected_card] at hlower
  omega
