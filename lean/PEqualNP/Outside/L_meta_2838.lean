import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2838
open PEqualNP.CircuitLowerBounds

-- Merge-count machinery from the checked L_meta_1624, in this Apache-2.0 repository.

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem eval_eq (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨gs, o⟩ x = (wf gs x).getD o false := rfl

theorem wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem wf_prefix (pre post : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + pre.length) :
    (wf (pre ++ post) w).getD i false = (wf pre w).getD i false := by
  have : wf (pre ++ post) w = wf post (wf pre w) := by simp [wf, List.foldl_append]
  rw [this]
  exact wf_keep post _ i (by rw [wf_len]; exact hi)

theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega


theorem wire_take (gates : List Gate) (X : List Bool) (k i : ℕ) (hi : i < X.length + k)
    (hk : k ≤ gates.length) :
    (wf gates X).getD i false = (wf (gates.take k) X).getD i false := by
  conv_lhs => rw [← List.take_append_drop k gates]
  exact wf_prefix _ _ _ _ (by rw [List.length_take, Nat.min_eq_left hk]; exact hi)

theorem gate_val (gates : List Gate) (X : List Bool) (k : ℕ) (hk : k < gates.length) :
    (wf gates X).getD (X.length + k) false
      = gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false) := by
  rw [wire_take gates X (k + 1) _ (by omega) hk, List.take_succ_eq_append_getElem hk, wf_snoc]
  have := getD_snoc_eq (wf (gates.take k) X)
    (gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false))
  rw [wf_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)] at this
  exact this

def val (gates : List Gate) {n : ℕ} (w : ℕ) (x : Fin n → Bool) : Bool :=
  (wf gates (List.ofFn x)).getD w false

theorem iv_eq (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k ≤ gates.length)
    (i : ℕ) : (wf (gates.take k) (List.ofFn x)).getD i false = true ↔
      i < n + k ∧ val gates i x = true := by
  by_cases hi : i < n + k
  · rw [val, wire_take gates (List.ofFn x) k i (by simpa using hi) hk]
    simp [hi]
  · rw [List.getD_eq_default _ _ (by rw [wf_len, List.length_take, Nat.min_eq_left hk]; simp; omega)]
    simp [hi]

theorem val_and (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gates.length)
    (hop : gates[k].op = GateOp.and) :
    val gates (n + k) x = true ↔ ∀ i ∈ gates[k].inputs, i < n + k ∧ val gates i x = true := by
  have := gate_val gates (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
  constructor
  · intro h i hi; exact (iv_eq gates x k (Nat.le_of_lt hk) i).1 (h i hi)
  · intro h i hi; exact (iv_eq gates x k (Nat.le_of_lt hk) i).2 (h i hi)

theorem val_or (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gates.length)
    (hop : gates[k].op = GateOp.or) :
    val gates (n + k) x = true ↔ ∃ i ∈ gates[k].inputs, i < n + k ∧ val gates i x = true := by
  have := gate_val gates (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
  constructor
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gates x k (Nat.le_of_lt hk) i).1 h⟩
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gates x k (Nat.le_of_lt hk) i).2 h⟩

theorem val_input (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    val gates w x = x ⟨w, hw⟩ := by
  rw [val, wf_keep gates _ w (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

theorem val_big (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ)
    (hw : n + gates.length ≤ w) : val gates w x = false := by
  rw [val, List.getD_eq_default _ _ (by rw [wf_len]; simpa using hw)]

def Cl {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool) (τ : Fin n → Fin n → Bool)
    (i : Fin gates.length) (X : Finset (Fin n)) : Prop :=
  (gates.get i).op = GateOp.or → val gates (n + (i : ℕ)) c = false →
    ∀ a b : ℕ, (gates.get i).inputs = [a, b] → ∀ y ∈ M, ∀ y' ∈ M,
      (val gates a (τ y) = true ∨ val gates b (τ y) = true) →
      (val gates a (τ y') = true ∨ val gates b (τ y') = true) → (y ∈ X ↔ y' ∈ X)

def Con {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool) (τ : Fin n → Fin n → Bool)
    (k : ℕ) (X : Finset (Fin n)) : Prop :=
  ∀ i : Fin gates.length, (i : ℕ) < k → Cl gates M c τ i X

def Mrg {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool) (τ : Fin n → Fin n → Bool)
    (g : Fin gates.length) : Prop :=
  (gates.get g).op = GateOp.or ∧ val gates (n + (g : ℕ)) c = false ∧
    ∃ w1 w2 : ℕ, (gates.get g).inputs = [w1, w2] ∧ ∃ r ∈ M, ∃ r' ∈ M,
      val gates w1 (τ r) = true ∧ val gates w2 (τ r') = true ∧
      ∃ X : Finset (Fin n), r ∈ X ∧ r' ∉ X ∧ Con gates M c τ (g : ℕ) X

theorem single {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool)
    (hτ : ∀ p ∈ M, ∀ v, τ p v = true → v = p)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hin : ∀ i : Fin gates.length, ∀ a ∈ (gates.get i).inputs, a < n + (i : ℕ))
    (k : ℕ) (hk : k ≤ gates.length) (X : Finset (Fin n)) (hX : Con gates M c τ k X) :
    ∀ w, w < n + k → val gates w c = false → ∀ y ∈ M, ∀ y' ∈ M,
      val gates w (τ y) = true → val gates w (τ y') = true → (y ∈ X ↔ y' ∈ X) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hwc y hy y' hy' h1 h2
    by_cases hwn : w < n
    · rw [val_input gates _ w hwn] at h1 h2
      have e1 := hτ y hy _ h1
      have e2 := hτ y' hy' _ h2
      rw [← e1, ← e2]
    · have hi : w - n < gates.length := by omega
      have he : n + (w - n) = w := by omega
      rw [← he] at hwc h1 h2
      have hinp : ∀ a ∈ gates[w - n].inputs, a < n + (w - n) :=
        hin ⟨w - n, hi⟩
      have hlen := (legal gates[w - n] (List.getElem_mem hi)).2
      rcases (legal gates[w - n] (List.getElem_mem hi)).1 with ha | ho
      · have hex : ∃ j ∈ gates[w - n].inputs, val gates j c = false := by
          by_contra hne
          have hall : val gates (n + (w - n)) c = true := by
            apply (val_and gates c (w - n) hi ha).2
            intro j hj
            refine ⟨hinp j hj, ?_⟩
            cases hv : val gates j c with
            | true => rfl
            | false => exact absurd ⟨j, hj, hv⟩ hne
          rw [hall] at hwc
          exact Bool.noConfusion hwc
        obtain ⟨j, hj, hjc⟩ := hex
        have hjlt := hinp j hj
        exact ih j (by omega) (by omega) hjc y hy y' hy'
          ((val_and gates (τ y) (w - n) hi ha).1 h1 j hj).2
          ((val_and gates (τ y') (w - n) hi ha).1 h2 j hj).2
      · have hall : ∀ j ∈ gates[w - n].inputs, val gates j c = false := by
          intro j hj
          cases hv : val gates j c with
          | false => rfl
          | true =>
            have ht : val gates (n + (w - n)) c = true :=
              (val_or gates c (w - n) hi ho).2 ⟨j, hj, hinp j hj, hv⟩
            rw [ht] at hwc
            exact Bool.noConfusion hwc
        obtain ⟨j1, hj1, _, hv1⟩ := (val_or gates (τ y) (w - n) hi ho).1 h1
        obtain ⟨j2, hj2, _, hv2⟩ := (val_or gates (τ y') (w - n) hi ho).1 h2
        rcases hinpe : gates[w - n].inputs with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
        · rw [hinpe] at hj1
          simp at hj1
        · rw [hinpe] at hj1 hj2
          have e1 : j1 = a := by simpa using hj1
          have e2 : j2 = a := by simpa using hj2
          rw [e1] at hv1
          rw [e2] at hv2
          have hjlt := hinp a (by rw [hinpe]; simp)
          exact ih a (by omega) (by omega) (hall a (by rw [hinpe]; simp)) y hy y' hy' hv1 hv2
        · rw [hinpe] at hj1 hj2
          have d1 : val gates a (τ y) = true ∨ val gates b (τ y) = true := by
            rcases List.mem_pair.1 hj1 with e | e
            · subst e; exact Or.inl hv1
            · subst e; exact Or.inr hv1
          have d2 : val gates a (τ y') = true ∨ val gates b (τ y') = true := by
            rcases List.mem_pair.1 hj2 with e | e
            · subst e; exact Or.inl hv2
            · subst e; exact Or.inr hv2
          exact hX ⟨w - n, hi⟩ (by simp; omega) ho hwc a b hinpe y hy y' hy' d1 d2
        · rw [hinpe] at hlen
          simp at hlen

theorem con_succ {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool) (k : ℕ) (hk : k < gates.length) (X : Finset (Fin n)) :
    Con gates M c τ (k + 1) X ↔ Con gates M c τ k X ∧ Cl gates M c τ ⟨k, hk⟩ X := by
  constructor
  · intro h
    exact ⟨fun i hi => h i (by omega), h ⟨k, hk⟩ (by simp)⟩
  · rintro ⟨h1, h2⟩ i hi
    by_cases e : (i : ℕ) = k
    · have e' : i = ⟨k, hk⟩ := Fin.ext e
      rw [e']
      exact h2
    · exact h1 i (by omega)

theorem con_compl {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool) (k : ℕ) (X : Finset (Fin n)) (h : Con gates M c τ k X) :
    Con gates M c τ k Xᶜ := by
  intro i hi ho hc' a b hab y hy y' hy' h1 h2
  rw [Finset.mem_compl, Finset.mem_compl, not_iff_not]
  exact h i hi ho hc' a b hab y hy y' hy' h1 h2

theorem con_symm {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool) (k : ℕ) (X Y : Finset (Fin n)) (hX : Con gates M c τ k X)
    (hY : Con gates M c τ k Y) : Con gates M c τ k (symmDiff X Y) := by
  intro i hi ho hc' a b hab y hy y' hy' h1 h2
  have e1 := hX i hi ho hc' a b hab y hy y' hy' h1 h2
  have e2 := hY i hi ho hc' a b hab y hy y' hy' h1 h2
  rw [Finset.mem_symmDiff, Finset.mem_symmDiff, e1, e2]

theorem con_inter {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool) (k : ℕ) (X : Finset (Fin n)) (hX : Con gates M c τ k X) :
    Con gates M c τ k (X ∩ M) := by
  intro i hi ho hc' a b hab y hy y' hy' h1 h2
  have e1 := hX i hi ho hc' a b hab y hy y' hy' h1 h2
  rw [Finset.mem_inter, Finset.mem_inter, e1]
  exact ⟨fun h => ⟨h.1, hy'⟩, fun h => ⟨h.1, hy⟩⟩

theorem cl_of {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool) (g : Fin gates.length) (X : Finset (Fin n)) (a b : ℕ)
    (hab : (gates.get g).inputs = [a, b])
    (sA : ∀ y ∈ M, ∀ y' ∈ M, val gates a (τ y) = true → val gates a (τ y') = true →
      (y ∈ X ↔ y' ∈ X))
    (sB : ∀ y ∈ M, ∀ y' ∈ M, val gates b (τ y) = true → val gates b (τ y') = true →
      (y ∈ X ↔ y' ∈ X))
    (Q : ∀ y ∈ M, ∀ y' ∈ M, val gates a (τ y) = true → val gates b (τ y') = true →
      (y ∈ X ↔ y' ∈ X)) : Cl gates M c τ g X := by
  intro _ _ a' b' hab' y hy y' hy' h1 h2
  rw [hab] at hab'
  obtain ⟨e1, e2⟩ : a = a' ∧ b = b' := by simpa using hab'
  subst e1
  subst e2
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact sA y hy y' hy' h1 h2
  · exact Q y hy y' hy' h1 h2
  · exact (Q y' hy' y hy h2 h1).symm
  · exact sB y hy y' hy' h1 h2

theorem symm_flip {n : ℕ} (X Y : Finset (Fin n)) (r r' : Fin n) (hr : r ∈ Y) (hr' : r' ∉ Y) :
    (r ∈ symmDiff X Y ↔ r' ∈ symmDiff X Y) ↔ ¬ (r ∈ X ↔ r' ∈ X) := by
  by_cases h1 : r ∈ X <;> by_cases h2 : r' ∈ X <;> simp [Finset.mem_symmDiff, h1, h2, hr, hr']

open Classical in
noncomputable def P {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool) (k : ℕ) : Finset (Finset (Fin n)) :=
  M.powerset.filter (fun X => Con gates M c τ k X)

open Classical in
theorem symm_mem {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool) (k : ℕ) (X Y : Finset (Fin n)) (hX : X ∈ P gates M c τ k)
    (hY : Y ⊆ M) (hYc : Con gates M c τ k Y) : symmDiff X Y ∈ P gates M c τ k := by
  rw [P, Finset.mem_filter, Finset.mem_powerset] at hX ⊢
  refine ⟨?_, con_symm gates M c τ k X Y hX.2 hYc⟩
  intro v hv
  rw [Finset.mem_symmDiff] at hv
  rcases hv with hv | hv
  · exact hX.1 hv.1
  · exact hY hv.1

open Classical in
theorem step {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool)
    (hτ : ∀ p ∈ M, ∀ v, τ p v = true → v = p)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hin : ∀ i : Fin gates.length, ∀ a ∈ (gates.get i).inputs, a < n + (i : ℕ))
    (g : Fin gates.length) :
    (P gates M c τ ((g : ℕ) + 1)).card * (if Mrg gates M c τ g then 2 else 1)
      = (P gates M c τ (g : ℕ)).card := by
  by_cases hal : (gates.get g).op = GateOp.or ∧ val gates (n + (g : ℕ)) c = false ∧
      ∃ a b : ℕ, (gates.get g).inputs = [a, b]
  swap
  · have hnm : ¬ Mrg gates M c τ g := by
      rintro ⟨h1, h2, w1, w2, h3, _⟩
      exact hal ⟨h1, h2, w1, w2, h3⟩
    have hP : P gates M c τ ((g : ℕ) + 1) = P gates M c τ (g : ℕ) := by
      unfold P
      apply Finset.filter_congr
      intro X _
      rw [con_succ gates M c τ g g.2 X]
      constructor
      · exact fun h => h.1
      · intro h
        refine ⟨h, ?_⟩
        intro ho hc' a b hab
        exact absurd ⟨ho, hc', a, b, hab⟩ hal
    rw [hP, if_neg hnm, Nat.mul_one]
  · obtain ⟨ho, hgc, a, b, hab⟩ := hal
    have hma : a ∈ (gates.get g).inputs := by rw [hab]; simp
    have hmb : b ∈ (gates.get g).inputs := by rw [hab]; simp
    have ha : a < n + (g : ℕ) := hin g a hma
    have hb : b < n + (g : ℕ) := hin g b hmb
    have hac : val gates a c = false := by
      cases hv : val gates a c with
      | false => rfl
      | true =>
        have ht : val gates (n + (g : ℕ)) c = true :=
          (val_or gates c g g.2 ho).2 ⟨a, hma, ha, hv⟩
        rw [ht] at hgc
        exact Bool.noConfusion hgc
    have hbc : val gates b c = false := by
      cases hv : val gates b c with
      | false => rfl
      | true =>
        have ht : val gates (n + (g : ℕ)) c = true :=
          (val_or gates c g g.2 ho).2 ⟨b, hmb, hb, hv⟩
        rw [ht] at hgc
        exact Bool.noConfusion hgc
    have sA : ∀ X, Con gates M c τ g X → ∀ y ∈ M, ∀ y' ∈ M, val gates a (τ y) = true →
        val gates a (τ y') = true → (y ∈ X ↔ y' ∈ X) := fun X hX =>
      single gates M c τ hτ legal hin g (le_of_lt g.2) X hX a ha hac
    have sB : ∀ X, Con gates M c τ g X → ∀ y ∈ M, ∀ y' ∈ M, val gates b (τ y) = true →
        val gates b (τ y') = true → (y ∈ X ↔ y' ∈ X) := fun X hX =>
      single gates M c τ hτ legal hin g (le_of_lt g.2) X hX b hb hbc
    by_cases hm : ∃ r ∈ M, ∃ r' ∈ M, val gates a (τ r) = true ∧ val gates b (τ r') = true ∧
        ∃ X : Finset (Fin n), r ∈ X ∧ r' ∉ X ∧ Con gates M c τ (g : ℕ) X
    · have hmrg : Mrg gates M c τ g := ⟨ho, hgc, a, b, hab, hm⟩
      obtain ⟨r, hr, r', hr', hra, hrb, X0, hrX, hr'X, hX0⟩ := hm
      rw [if_pos hmrg]
      have hP : P gates M c τ ((g : ℕ) + 1)
          = (P gates M c τ (g : ℕ)).filter (fun X => r ∈ X ↔ r' ∈ X) := by
        unfold P
        rw [Finset.filter_filter]
        apply Finset.filter_congr
        intro X _
        rw [con_succ gates M c τ g g.2 X]
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨h1, h2 ho hgc a b hab r hr r' hr' (Or.inl hra) (Or.inr hrb)⟩
        · rintro ⟨h1, h2⟩
          refine ⟨h1, cl_of gates M c τ g X a b hab (sA X h1) (sB X h1) ?_⟩
          intro y hy y' hy' hya hyb
          exact ((sA X h1 y hy r hr hya hra).trans h2).trans (sB X h1 r' hr' y' hy' hrb hyb)
      rw [hP]
      have hsplit := Finset.card_filter_add_card_filter_not (s := P gates M c τ (g : ℕ))
        (fun X => r ∈ X ↔ r' ∈ X)
      have hY0 : X0 ∩ M ⊆ M := Finset.inter_subset_right
      have hY0c := con_inter gates M c τ g X0 hX0
      have hrY : r ∈ X0 ∩ M := Finset.mem_inter.2 ⟨hrX, hr⟩
      have hr'Y : r' ∉ X0 ∩ M := fun h => hr'X (Finset.mem_inter.1 h).1
      have hbij : ((P gates M c τ (g : ℕ)).filter (fun X => ¬ (r ∈ X ↔ r' ∈ X))).card
          = ((P gates M c τ (g : ℕ)).filter (fun X => r ∈ X ↔ r' ∈ X)).card := by
        refine Finset.card_bij' (fun X _ => symmDiff X (X0 ∩ M)) (fun X _ => symmDiff X (X0 ∩ M))
          ?_ ?_ ?_ ?_
        · intro X hX
          rw [Finset.mem_filter] at hX ⊢
          refine ⟨symm_mem gates M c τ g X _ hX.1 hY0 hY0c, ?_⟩
          exact (symm_flip X (X0 ∩ M) r r' hrY hr'Y).2 hX.2
        · intro X hX
          rw [Finset.mem_filter] at hX ⊢
          refine ⟨symm_mem gates M c τ g X _ hX.1 hY0 hY0c, ?_⟩
          intro hcon
          exact (symm_flip X (X0 ∩ M) r r' hrY hr'Y).1 hcon hX.2
        · intro X _
          exact symmDiff_symmDiff_cancel_right _ _
        · intro X _
          exact symmDiff_symmDiff_cancel_right _ _
      omega
    · have hnm : ¬ Mrg gates M c τ g := by
        rintro ⟨_, _, w1, w2, h3, r, hr, r', hr', h4, h5, h6⟩
        rw [hab] at h3
        obtain ⟨e1, e2⟩ : a = w1 ∧ b = w2 := by simpa using h3
        subst e1
        subst e2
        exact hm ⟨r, hr, r', hr', h4, h5, h6⟩
      rw [if_neg hnm, Nat.mul_one]
      congr 1
      unfold P
      apply Finset.filter_congr
      intro X _
      rw [con_succ gates M c τ g g.2 X]
      constructor
      · exact fun h => h.1
      · intro h
        refine ⟨h, cl_of gates M c τ g X a b hab (sA X h) (sB X h) ?_⟩
        intro y hy y' hy' hya hyb
        constructor
        · intro hyX
          by_contra hn
          exact hm ⟨y, hy, y', hy', hya, hyb, X, hyX, hn, h⟩
        · intro hyX
          by_contra hn
          exact hm ⟨y, hy, y', hy', hya, hyb, Xᶜ, Finset.mem_compl.2 hn,
            fun h' => Finset.mem_compl.1 h' hyX, con_compl gates M c τ g X h⟩

open Classical in
theorem count {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool)
    (hτ : ∀ p ∈ M, ∀ v, τ p v = true → v = p)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hin : ∀ i : Fin gates.length, ∀ a ∈ (gates.get i).inputs, a < n + (i : ℕ))
    (k : ℕ) (hk : k ≤ gates.length) :
    (P gates M c τ k).card *
      2 ^ (∑ g : Fin gates.length, if (g : ℕ) < k ∧ Mrg gates M c τ g then 1 else 0)
      = 2 ^ M.card := by
  induction k with
  | zero =>
    have h0 : P gates M c τ 0 = M.powerset := by
      unfold P
      apply Finset.filter_true_of_mem
      intro X _ i hi
      exact absurd hi (Nat.not_lt_zero _)
    rw [h0, Finset.card_powerset]
    simp
  | succ k ih =>
    have hk' : k < gates.length := hk
    have hs : (P gates M c τ (k + 1)).card * (if Mrg gates M c τ ⟨k, hk'⟩ then 2 else 1)
        = (P gates M c τ k).card := step gates M c τ hτ legal hin ⟨k, hk'⟩
    have hsum : (∑ g : Fin gates.length, if (g : ℕ) < k + 1 ∧ Mrg gates M c τ g then 1 else 0)
        = (∑ g : Fin gates.length, if (g : ℕ) < k ∧ Mrg gates M c τ g then 1 else 0)
          + (if Mrg gates M c τ ⟨k, hk'⟩ then 1 else 0) := by
      have hpt : ∀ g : Fin gates.length,
          (if (g : ℕ) < k + 1 ∧ Mrg gates M c τ g then 1 else 0)
          = (if (g : ℕ) < k ∧ Mrg gates M c τ g then 1 else 0)
            + (if g = ⟨k, hk'⟩ then (if Mrg gates M c τ ⟨k, hk'⟩ then 1 else 0) else 0) := by
        intro g
        by_cases e : g = ⟨k, hk'⟩
        · subst e
          simp
        · have hne : (g : ℕ) ≠ k := fun h => e (Fin.ext h)
          have h2 : ((g : ℕ) < k + 1) ↔ ((g : ℕ) < k) := by omega
          simp [e, h2]
      rw [Finset.sum_congr rfl (fun g _ => hpt g), Finset.sum_add_distrib]
      simp
    rw [hsum, pow_add, ← ih (le_of_lt hk'), ← hs]
    split_ifs <;> ring


open Classical in
theorem mcount {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool)
    (hτ : ∀ p ∈ M, ∀ v, τ p v = true → v = p)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hin : ∀ i : Fin gates.length, ∀ a ∈ (gates.get i).inputs, a < n + (i : ℕ))
    (hM : 1 ≤ M.card) (o : ℕ) (hoc : val gates o c = false)
    (hot : ∀ p ∈ M, val gates o (τ p) = true) :
    (∑ g : Fin gates.length, if Mrg gates M c τ g then 1 else 0) = M.card - 1 := by
  have hne : M.Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨p0, hp0⟩ := hne
  have holt : o < n + gates.length := by
    by_contra h
    have hb := val_big gates (τ p0) o (by omega)
    rw [hot p0 hp0] at hb
    exact Bool.noConfusion hb
  have hfin : P gates M c τ gates.length = {∅, M} := by
    ext X
    rw [P, Finset.mem_filter, Finset.mem_powerset, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hsub, hX⟩
      have hs := single gates M c τ hτ legal hin gates.length le_rfl X hX o holt hoc
      by_cases hex : ∃ y ∈ M, y ∈ X
      · obtain ⟨y, hy, hyX⟩ := hex
        right
        apply Finset.Subset.antisymm hsub
        intro z hz
        exact (hs y hy z hz (hot y hy) (hot z hz)).1 hyX
      · left
        apply Finset.eq_empty_of_forall_notMem
        intro z hz
        exact hex ⟨z, hsub hz, hz⟩
    · rintro (e | e)
      · subst e
        refine ⟨Finset.empty_subset _, ?_⟩
        intro i _ _ _ a b _ y _ y' _ _ _
        simp
      · subst e
        refine ⟨Finset.Subset.refl _, ?_⟩
        intro i _ _ _ a b _ y hy y' hy' _ _
        exact ⟨fun _ => hy', fun _ => hy⟩
  have hcnt := count gates M c τ hτ legal hin gates.length le_rfl
  have hpair : ({∅, M} : Finset (Finset (Fin n))).card = 2 := by
    apply Finset.card_pair
    intro h
    rw [← h] at hp0
    simp at hp0
  rw [hfin, hpair] at hcnt
  have hsum : (∑ g : Fin gates.length, if (g : ℕ) < gates.length ∧ Mrg gates M c τ g then 1 else 0)
      = ∑ g : Fin gates.length, if Mrg gates M c τ g then 1 else 0 :=
    Finset.sum_congr rfl (fun g _ => by simp [g.2])
  rw [hsum] at hcnt
  have hm1 : 2 ^ M.card = 2 * 2 ^ (M.card - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have h8 : 2 ^ (∑ g : Fin gates.length, if Mrg gates M c τ g then 1 else 0) = 2 ^ (M.card - 1) :=
    Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) (hcnt.trans hm1)
  exact Nat.pow_right_injective (le_refl 2) h8

theorem val_mono (gates : List Gate) {n : ℕ}
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x x' : Fin n → Bool) (hx : ∀ v, x v = true → x' v = true) :
    ∀ w, val gates w x = true → val gates w x' = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro h
    by_cases hwn : w < n
    · rw [val_input gates _ w hwn] at h ⊢
      exact hx _ h
    · by_cases hbig : n + gates.length ≤ w
      · rw [val_big gates x w hbig] at h
        exact Bool.noConfusion h
      · have hi : w - n < gates.length := by omega
        have he : n + (w - n) = w := by omega
        rw [← he] at h ⊢
        rcases (legal gates[w - n] (List.getElem_mem hi)).1 with ha | ho
        · apply (val_and gates x' (w - n) hi ha).2
          intro j hj
          obtain ⟨hjlt, hjv⟩ := (val_and gates x (w - n) hi ha).1 h j hj
          exact ⟨hjlt, ih j (by omega) hjv⟩
        · obtain ⟨j, hj, hjlt, hv⟩ := (val_or gates x (w - n) hi ho).1 h
          exact (val_or gates x' (w - n) hi ho).2 ⟨j, hj, hjlt, ih j (by omega) hv⟩


def hotOne {n : ℕ} (p : Fin n) (v : Fin n) : Bool := decide (v = p)

open Classical in
theorem multi_count {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (G : Finset (Fin gates.length)) (o : Fin gates.length → ℕ)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hin : ∀ i : Fin gates.length, ∀ a ∈ (gates.get i).inputs, a < n + (i : ℕ))
    (hc : ∀ g ∈ G, val gates (o g) c = false)
    (hot : ∀ p ∈ M, ∃ g ∈ G, val gates (o g) (hotOne p) = true) :
    M.card ≤ (∑ g : Fin gates.length, if Mrg gates M c hotOne g then 1 else 0) + G.card := by
  let F : Finset (Fin n) → Finset (Fin gates.length) :=
    fun X => G.filter (fun g => ∃ p ∈ X, val gates (o g) (hotOne p) = true)
  have hτ : ∀ p ∈ M, ∀ v, hotOne p v = true → v = p := by
    intro p _ v h
    exact of_decide_eq_true h
  have hinc : ∀ X Y : Finset (Fin n), X ∈ P gates M c hotOne gates.length →
      Y ∈ P gates M c hotOne gates.length → F X = F Y → X ⊆ Y := by
    intro X Y hX hY heq p hp
    rw [P, Finset.mem_filter, Finset.mem_powerset] at hX hY
    obtain ⟨g, hg, hgp⟩ := hot p (hX.1 hp)
    have hfg : g ∈ F X := Finset.mem_filter.mpr ⟨hg, p, hp, hgp⟩
    rw [heq] at hfg
    obtain ⟨_, p', hp', hgp'⟩ := Finset.mem_filter.mp hfg
    have hlt : o g < n + gates.length := by
      by_contra h
      have hz := val_big gates (hotOne p) (o g) (by omega)
      rw [hz] at hgp
      exact Bool.noConfusion hgp
    exact (single gates M c hotOne hτ legal hin gates.length le_rfl Y hY.2
      (o g) hlt (hc g hg) p (hX.1 hp) p' (hY.1 hp') hgp hgp').2 hp'
  have hP : (P gates M c hotOne gates.length).card ≤ G.powerset.card := by
    apply Finset.card_le_card_of_injOn F
    · intro X _
      exact Finset.mem_coe.mpr (Finset.mem_powerset.mpr (Finset.filter_subset _ _))
    · intro X hX Y hY heq
      exact Finset.Subset.antisymm
        (hinc X Y (Finset.mem_coe.mp hX) (Finset.mem_coe.mp hY) heq)
        (hinc Y X (Finset.mem_coe.mp hY) (Finset.mem_coe.mp hX) heq.symm)
  rw [Finset.card_powerset] at hP
  have hcnt := count gates M c hotOne hτ legal hin gates.length le_rfl
  have hs : (∑ g : Fin gates.length, if (g : ℕ) < gates.length ∧ Mrg gates M c hotOne g then 1 else 0)
      = ∑ g : Fin gates.length, if Mrg gates M c hotOne g then 1 else 0 :=
    Finset.sum_congr rfl (fun g _ => by simp [g.2])
  rw [hs] at hcnt
  have hp : 2 ^ M.card ≤ 2 ^ ((∑ g : Fin gates.length, if Mrg gates M c hotOne g then 1 else 0) + G.card) := by
    rw [← hcnt, pow_add, Nat.mul_comm (2 ^ (∑ g : Fin gates.length, if Mrg gates M c hotOne g then 1 else 0))]
    exact Nat.mul_le_mul_right _ hP
  by_contra h
  have hlt : 2 ^ ((∑ g : Fin gates.length, if Mrg gates M c hotOne g then 1 else 0) + G.card) < 2 ^ M.card :=
    Nat.pow_lt_pow_right (by decide) (by omega)
  omega

theorem merge_disjoint {n : ℕ} (gates : List Gate)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hin : ∀ i : Fin gates.length, ∀ a ∈ (gates.get i).inputs, a < n + (i : ℕ))
    (L1 L2 M1 M2 : Finset (Fin n)) (c1 c2 : Fin n → Bool)
    (hM : M1 ⊆ L1) (hcard : (L1 ∩ L2).card ≤ 1)
    (hcomp : ∀ p ∈ L1, p ∉ L2 → c2 p = true)
    (g : Fin gates.length)
    (h1 : Mrg gates M1 c1 hotOne g) (h2 : Mrg gates M2 c2 hotOne g) : False := by
  obtain ⟨ho, _, w1, w2, hab, r, hr, r', hr', hv1, hv2, X, hrX, hr'X, _⟩ := h1
  obtain ⟨_, hc2, _⟩ := h2
  have hne : r ≠ r' := fun e => hr'X (e ▸ hrX)
  have hm1 : w1 ∈ (gates.get g).inputs := by rw [hab]; simp
  have hm2 : w2 ∈ (gates.get g).inputs := by rw [hab]; simp
  have ht1 : val gates (n + (g : ℕ)) (hotOne r) = true :=
    (val_or gates _ g g.2 ho).2 ⟨w1, hm1, hin g w1 hm1, hv1⟩
  have ht2 : val gates (n + (g : ℕ)) (hotOne r') = true :=
    (val_or gates _ g g.2 ho).2 ⟨w2, hm2, hin g w2 hm2, hv2⟩
  have key : ∀ s ∈ L1, val gates (n + (g : ℕ)) (hotOne s) = true → s ∈ L2 := by
    intro s hs hv
    by_contra hns
    have hmo := val_mono gates legal (hotOne s) c2 (by
      intro v hv'
      have e : v = s := of_decide_eq_true hv'
      rw [e]
      exact hcomp s hs hns) _ hv
    rw [hc2] at hmo
    exact Bool.noConfusion hmo
  have hsub : ({r, r'} : Finset (Fin n)) ⊆ L1 ∩ L2 := by
    intro v hv
    rw [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with e | e
    · rw [e]; exact Finset.mem_inter.2 ⟨hM hr, key r (hM hr) ht1⟩
    · rw [e]; exact Finset.mem_inter.2 ⟨hM hr', key r' (hM hr') ht2⟩
  have hle := Finset.card_le_card hsub
  rw [Finset.card_pair hne] at hle
  omega

open Classical in
theorem family_count {n : ℕ} {ι : Type} [Fintype ι] (gates : List Gate)
    (L M : ι → Finset (Fin n)) (c : ι → Fin n → Bool) (side : ι → Bool)
    (group : Fin gates.length → Option ι) (o : Fin gates.length → ℕ)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hin : ∀ i : Fin gates.length, ∀ a ∈ (gates.get i).inputs, a < n + (i : ℕ))
    (hL : ∀ i j, i ≠ j → side i = side j → (L i ∩ L j).card ≤ 1)
    (hcomp : ∀ i j, side i = side j → ∀ p ∈ L i, p ∉ L j → c j p = true)
    (hM : ∀ i, M i ⊆ L i)
    (hc : ∀ i g, group g = some i → val gates (o g) (c i) = false)
    (hot : ∀ i p, p ∈ M i → ∃ g, group g = some i ∧ val gates (o g) (hotOne p) = true) :
    ∑ i, (M i).card ≤ 3 * gates.length := by
  let G : ι → Finset (Fin gates.length) := fun i => Finset.univ.filter (fun g => group g = some i)
  have h1 : ∀ i, (M i).card ≤
      (∑ g : Fin gates.length, if Mrg gates (M i) (c i) hotOne g then 1 else 0) + (G i).card := by
    intro i
    apply multi_count gates (M i) (c i) (G i) o legal hin
    · intro g hg
      exact hc i g (Finset.mem_filter.mp hg).2
    · intro p hp
      obtain ⟨g, hg, hv⟩ := hot i p hp
      exact ⟨g, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg⟩, hv⟩
  have h2 : ∀ g : Fin gates.length,
      (∑ i : ι, if Mrg gates (M i) (c i) hotOne g then 1 else 0) ≤ 2 := by
    intro g
    rw [← Finset.card_filter]
    have hcard : (Finset.univ.filter (fun i : ι => Mrg gates (M i) (c i) hotOne g)).card ≤
        (Finset.univ : Finset Bool).card := by
      apply Finset.card_le_card_of_injOn side
      · intro i _
        exact Finset.mem_coe.mpr (Finset.mem_univ _)
      · intro i hi j hj heq
        by_contra hne
        exact merge_disjoint gates legal hin (L i) (L j) (M i) (M j) (c i) (c j)
          (hM i) (hL i j hne heq) (hcomp i j heq) g
          (Finset.mem_filter.mp (Finset.mem_coe.mp hi)).2
          (Finset.mem_filter.mp (Finset.mem_coe.mp hj)).2
    simpa using hcard
  have h3 : (∑ i : ι, (G i).card) ≤ gates.length := by
    simp only [G, Finset.card_filter]
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ _g : Fin gates.length, (1 : ℕ) := by
        apply Finset.sum_le_sum
        intro g _
        cases h : group g <;> simp [h]
      _ = gates.length := by simp
  have h4 : (∑ g : Fin gates.length, ∑ i : ι,
      if Mrg gates (M i) (c i) hotOne g then (1 : ℕ) else 0) ≤ 2 * gates.length := by
    calc
      _ ≤ ∑ _g : Fin gates.length, (2 : ℕ) := Finset.sum_le_sum (fun g _ => h2 g)
      _ = 2 * gates.length := by simp [Nat.mul_comm]
  have h5 := Finset.sum_le_sum (s := (Finset.univ : Finset ι)) (fun i _ => h1 i)
  rw [Finset.sum_add_distrib, Finset.sum_comm] at h5
  omega

abbrev Center (N : ℕ) := Sum (Fin N) (Fin N)

def point {N : ℕ} (p : Fin N) : Fin (N + N) := Fin.castAdd N p
def line {N : ℕ} (l : Fin N) : Fin (N + N) := Fin.natAdd N l

theorem point_eq {N : ℕ} (p p' : Fin N) : point p = point p' ↔ p = p' := by
  constructor
  · intro h
    exact Fin.ext (congrArg Fin.val h)
  · rintro rfl
    rfl

theorem line_eq {N : ℕ} (l l' : Fin N) : line l = line l' ↔ l = l' := by
  constructor
  · intro h
    have hh := congrArg Fin.val h
    change N + l.val = N + l'.val at hh
    exact Fin.ext (by omega)
  · rintro rfl
    rfl

theorem point_ne_line {N : ℕ} (p l : Fin N) : point p ≠ line l := by
  intro h
  have hh := congrArg Fin.val h
  change p.val = N + l.val at hh
  omega

theorem line_ne_point {N : ℕ} (l p : Fin N) : line l ≠ point p := (point_ne_line p l).symm

def side {N : ℕ} : Center N → Bool
  | .inl _ => false
  | .inr _ => true

def reference {N : ℕ} (I : Fin N → Fin N → Prop) (i : Center N) (v : Fin (N + N)) : Prop :=
  match i with
  | .inl p => ∃ l, v = line l ∧ I p l
  | .inr l => ∃ p, v = point p ∧ I p l

def outside {N : ℕ} (I : Fin N → Fin N → Prop) (i : Center N) (v : Fin (N + N)) : Prop :=
  match i with
  | .inl p => ∃ l, v = line l ∧ ¬ I p l
  | .inr l => ∃ p, v = point p ∧ ¬ I p l

open Classical in
noncomputable def refs {N : ℕ} (I : Fin N → Fin N → Prop) (i : Center N) : Finset (Fin (N + N)) :=
  Finset.univ.filter (reference I i)

open Classical in
noncomputable def test {N : ℕ} (I : Fin N → Fin N → Prop) (i : Center N) : Fin (N + N) → Bool :=
  fun v => decide (outside I i v)

def centerOK {N : ℕ} (i : Center N) (e : Fin N × Fin N) : Prop :=
  match i with
  | .inl p => e.1 = p
  | .inr l => e.2 = l

def leaf {N : ℕ} (i : Center N) (e : Fin N × Fin N) : Fin (N + N) :=
  match i with
  | .inl _ => line e.2
  | .inr _ => point e.1

def NoRect {N : ℕ} (I : Fin N → Fin N → Prop) : Prop :=
  ∀ p p' l l', p ≠ p' → l ≠ l' → I p l → I p' l → I p l' → I p' l' → False

theorem ref_inter {N : ℕ} (I : Fin N → Fin N → Prop) (h4 : NoRect I) :
    ∀ i j : Center N, i ≠ j → side i = side j → (refs I i ∩ refs I j).card ≤ 1 := by
  classical
  intro i j hij hs
  apply Finset.card_le_one.mpr
  intro x hx y hy
  have hx1 := (Finset.mem_filter.mp (Finset.mem_inter.mp hx).1).2
  have hx2 := (Finset.mem_filter.mp (Finset.mem_inter.mp hx).2).2
  have hy1 := (Finset.mem_filter.mp (Finset.mem_inter.mp hy).1).2
  have hy2 := (Finset.mem_filter.mp (Finset.mem_inter.mp hy).2).2
  rcases i with p | l <;> rcases j with p' | l'
  · obtain ⟨a, ha, hpa⟩ := hx1
    obtain ⟨a', ha', hp'a⟩ := hx2
    obtain ⟨b, hb, hpb⟩ := hy1
    obtain ⟨b', hb', hp'b⟩ := hy2
    have ea : a = a' := (line_eq a a').mp (ha.symm.trans ha')
    have eb : b = b' := (line_eq b b').mp (hb.symm.trans hb')
    subst a'
    subst b'
    by_contra hne
    exact h4 p p' a b (fun e => hij (congrArg Sum.inl e))
      (fun e => hne (ha.trans (e ▸ hb.symm))) hpa hp'a hpb hp'b
  · simp [side] at hs
  · simp [side] at hs
  · obtain ⟨a, ha, hal⟩ := hx1
    obtain ⟨a', ha', hal'⟩ := hx2
    obtain ⟨b, hb, hbl⟩ := hy1
    obtain ⟨b', hb', hbl'⟩ := hy2
    have ea : a = a' := (point_eq a a').mp (ha.symm.trans ha')
    have eb : b = b' := (point_eq b b').mp (hb.symm.trans hb')
    subst a'
    subst b'
    by_contra hne
    exact h4 a b l l' (fun e => hne (ha.trans (e ▸ hb.symm)))
      (fun e => hij (congrArg Sum.inr e)) hal hbl hal' hbl'

theorem ref_comp {N : ℕ} (I : Fin N → Fin N → Prop) :
    ∀ i j : Center N, side i = side j → ∀ v ∈ refs I i, v ∉ refs I j → test I j v = true := by
  classical
  intro i j hs v hv hn
  have h := (Finset.mem_filter.mp hv).2
  rcases i with p | l <;> rcases j with p' | l'
  · obtain ⟨a, rfl, _⟩ := h
    have hna : ¬ I p' a := fun ha => hn (Finset.mem_filter.mpr ⟨Finset.mem_univ _, a, rfl, ha⟩)
    exact decide_eq_true ⟨a, rfl, hna⟩
  · simp [side] at hs
  · simp [side] at hs
  · obtain ⟨a, rfl, _⟩ := h
    have hna : ¬ I a l' := fun ha => hn (Finset.mem_filter.mpr ⟨Finset.mem_univ _, a, rfl, ha⟩)
    exact decide_eq_true ⟨a, rfl, hna⟩

theorem test_pp {N : ℕ} (I : Fin N → Fin N → Prop) (p p' : Fin N) :
    test I (Sum.inl p) (point p') = false := by
  classical
  simp [test, outside, point_ne_line]

theorem test_pl {N : ℕ} (I : Fin N → Fin N → Prop) (p l : Fin N) :
    test I (Sum.inl p) (line l) = decide (¬ I p l) := by
  classical
  simp [test, outside, line_eq]

theorem test_ll {N : ℕ} (I : Fin N → Fin N → Prop) (l l' : Fin N) :
    test I (Sum.inr l) (line l') = false := by
  classical
  simp [test, outside, line_ne_point]

theorem test_lp {N : ℕ} (I : Fin N → Fin N → Prop) (l p : Fin N) :
    test I (Sum.inr l) (point p) = decide (¬ I p l) := by
  classical
  simp [test, outside, point_eq]

def joinInput {n : ℕ} (x y : Fin n → Bool) : Fin n → Bool := fun v => x v || y v

def Below {N : ℕ} (I : Fin N → Fin N → Prop) (gs : List Gate) (g : Fin gs.length) : Prop :=
  ∀ z : Fin (N + N) → Bool, val gs (N + N + (g : ℕ)) z = true →
    ∃ p l : Fin N, I p l ∧ z (point p) = true ∧ z (line l) = true

def Wit {N : ℕ} (I : Fin N → Fin N → Prop) (gs : List Gate) (g : Fin gs.length)
    (e : Fin N × Fin N) : Prop :=
  I e.1 e.2 ∧ (gs.get g).op = GateOp.and ∧
    ∃ a c : ℕ, ((gs.get g).inputs = [a,c] ∨ (gs.get g).inputs = [c,a]) ∧ Below I gs g ∧
      val gs a (hotOne (point e.1)) = true ∧ val gs c (hotOne (line e.2)) = true

theorem combine {N : ℕ} (I : Fin N → Fin N → Prop) (gs : List Gate) (g : Fin gs.length)
    (legal : ∀ t ∈ gs, (t.op = GateOp.and ∨ t.op = GateOp.or) ∧ t.inputs.length ≤ 2)
    (hin : ∀ i : Fin gs.length, ∀ a ∈ (gs.get i).inputs, a < N + N + (i : ℕ))
    (hop : (gs.get g).op = GateOp.and) (a c : ℕ)
    (hins : (gs.get g).inputs = [a,c] ∨ (gs.get g).inputs = [c,a])
    (hb : Below I gs g) (x y : Fin (N+N) → Bool)
    (ha : val gs a x = true) (hc : val gs c y = true) :
    ∃ p l : Fin N, I p l ∧ joinInput x y (point p) = true ∧ joinInput x y (line l) = true := by
  have ha' := val_mono gs legal x (joinInput x y) (by intro v hv; simp [joinInput,hv]) a ha
  have hc' := val_mono gs legal y (joinInput x y) (by intro v hv; simp [joinInput,hv]) c hc
  apply hb
  apply (val_and gs _ g g.2 hop).2
  intro w hw
  refine ⟨hin g w hw, ?_⟩
  rcases hins with h | h
  · rw [h] at hw
    rcases List.mem_pair.mp hw with e | e
    · simpa [e] using ha'
    · simpa [e] using hc'
  · rw [h] at hw
    rcases List.mem_pair.mp hw with e | e
    · simpa [e] using hc'
    · simpa [e] using ha'

theorem gate_star {N : ℕ} (I : Fin N → Fin N → Prop) (gs : List Gate)
    (h4 : NoRect I)
    (legal : ∀ t ∈ gs, (t.op = GateOp.and ∨ t.op = GateOp.or) ∧ t.inputs.length ≤ 2)
    (hin : ∀ i : Fin gs.length, ∀ a ∈ (gs.get i).inputs, a < N + N + (i : ℕ))
    (g : Fin gs.length) (hex : ∃ e, Wit I gs g e) :
    ∃ i : Center N, ∃ o : ℕ, val gs o (test I i) = false ∧
      ∀ e, Wit I gs g e → centerOK i e ∧ leaf i e ∈ refs I i ∧ val gs o (hotOne (leaf i e)) = true := by
  classical
  obtain ⟨⟨p0,l0⟩, hi, hop, a, c, hins, hb, ha, hc⟩ := hex
  have cb := combine I gs g legal hin hop a c hins hb
  have noP : ∀ p : Fin N, val gs c (hotOne (point p)) ≠ true := by
    intro p hv
    obtain ⟨p', l', _, _, hl⟩ := cb _ _ ha hv
    simp [joinInput, hotOne, line_ne_point] at hl
  have orient : ∀ e, Wit I gs g e →
      val gs a (hotOne (point e.1)) = true ∧ val gs c (hotOne (line e.2)) = true := by
    intro e he
    obtain ⟨_, _, a', c', hins', _, ha', hc'⟩ := he
    have hpair : (a' = a ∧ c' = c) ∨ (a' = c ∧ c' = a) := by
      rcases hins with h | h <;> rcases hins' with h' | h' <;>
        have heq := h'.symm.trans h <;> simp only [List.cons.injEq, and_true] at heq <;> tauto
    rcases hpair with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact ⟨ha',hc'⟩
    · exact False.elim (noP e.1 ha')
  have rect : ∀ p l : Fin N, val gs a (hotOne (point p)) = true →
      val gs c (hotOne (line l)) = true → I p l := by
    intro p l hp hl
    obtain ⟨p', l', hi', hpp, hll⟩ := cb _ _ hp hl
    have ep : p' = p := by simpa [joinInput, hotOne, point_eq, point_ne_line] using hpp
    have el : l' = l := by simpa [joinInput, hotOne, line_eq, line_ne_point] using hll
    simpa [ep,el] using hi'
  by_cases hp : ∀ p : Fin N, val gs a (hotOne (point p)) = true → p = p0
  · refine ⟨Sum.inl p0, c, ?_, ?_⟩
    · cases hv : val gs c (test I (Sum.inl p0)) with
      | false => rfl
      | true =>
        obtain ⟨p', l', hi', hpp, hll⟩ := cb _ _ ha hv
        have ep : p' = p0 := by simpa [joinInput, hotOne, point_eq, test_pp] using hpp
        have hn : ¬ I p0 l' := by simpa [joinInput, hotOne, line_ne_point, test_pl] using hll
        exact False.elim (hn (by simpa [ep] using hi'))
    · intro e he
      have hv := orient e he
      have ep := hp e.1 hv.1
      refine ⟨ep, ?_, hv.2⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, e.2, rfl, ep ▸ he.1⟩
  · push_neg at hp
    obtain ⟨p1, hp1, hpne⟩ := hp
    have hl : ∀ l : Fin N, val gs c (hotOne (line l)) = true → l = l0 := by
      intro l hv
      by_contra hne
      exact h4 p0 p1 l0 l hpne.symm hne.symm (rect p0 l0 ha hc) (rect p1 l0 hp1 hc)
        (rect p0 l ha hv) (rect p1 l hp1 hv)
    refine ⟨Sum.inr l0, a, ?_, ?_⟩
    · cases hv : val gs a (test I (Sum.inr l0)) with
      | false => rfl
      | true =>
        obtain ⟨p', l', hi', hpp, hll⟩ := cb _ _ hv hc
        have el : l' = l0 := by simpa [joinInput, hotOne, line_eq, test_ll] using hll
        have hn : ¬ I p' l0 := by simpa [joinInput, hotOne, point_ne_line, test_lp] using hpp
        exact False.elim (hn (by simpa [el] using hi'))
    · intro e he
      have hv := orient e he
      have el := hl e.2 hv.2
      refine ⟨el, ?_, hv.1⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, e.1, rfl, el ▸ he.1⟩

open Classical in
theorem all_pairs {N : ℕ} (I : Fin N → Fin N → Prop) (gs : List Gate)
    (h4 : NoRect I)
    (legal : ∀ t ∈ gs, (t.op = GateOp.and ∨ t.op = GateOp.or) ∧ t.inputs.length ≤ 2)
    (hin : ∀ i : Fin gs.length, ∀ a ∈ (gs.get i).inputs, a < N + N + (i : ℕ)) :
    (Finset.univ.filter (fun e : Fin N × Fin N => ∃ g : Fin gs.length, Wit I gs g e)).card ≤ 3 * gs.length := by
  let S := fun (g : Fin gs.length) (h : ∃ e, Wit I gs g e) => gate_star I gs h4 legal hin g h
  let group : Fin gs.length → Option (Center N) := fun g =>
    if h : ∃ e, Wit I gs g e then some (Classical.choose (S g h)) else none
  let o : Fin gs.length → ℕ := fun g =>
    if h : ∃ e, Wit I gs g e then Classical.choose (Classical.choose_spec (S g h)) else 0
  let M : Center N → Finset (Fin (N+N)) := fun i =>
    (refs I i).filter (fun v => ∃ g, group g = some i ∧ val gs (o g) (hotOne v) = true)
  have hsound : ∀ i g, group g = some i → val gs (o g) (test I i) = false := by
    intro i g hg
    by_cases h : ∃ e, Wit I gs g e
    · have he : Classical.choose (S g h) = i := by simpa [group,h] using hg
      have hs := (Classical.choose_spec (Classical.choose_spec (S g h))).1
      simpa [o,h,he] using hs
    · simp [group,h] at hg
  have hcount := family_count gs (refs I) M (test I) side group o legal hin (ref_inter I h4)
    (ref_comp I) (fun i => Finset.filter_subset _ _) hsound
    (fun i p hp => (Finset.mem_filter.mp hp).2)
  have hcover : ∀ e : Fin N × Fin N, (∃ g, Wit I gs g e) →
      ∃ i, centerOK i e ∧ leaf i e ∈ M i := by
    intro e he
    obtain ⟨g,hg⟩ := he
    have h : ∃ e', Wit I gs g e' := ⟨e,hg⟩
    let i := Classical.choose (S g h)
    have hs := (Classical.choose_spec (Classical.choose_spec (S g h))).2 e hg
    refine ⟨i,hs.1,Finset.mem_filter.mpr ⟨hs.2.1,g,?_,?_⟩⟩
    · simp [group,h,i]
    · simpa [o,h,i] using hs.2.2
  let E : Finset (Fin N × Fin N) := Finset.univ.filter (fun e => ∃ g : Fin gs.length, Wit I gs g e)
  let f : (Fin N × Fin N) → (Σ i : Center N, Fin (N+N)) := fun e =>
    if h : ∃ i, centerOK i e ∧ leaf i e ∈ M i then
      ⟨Classical.choose h, leaf (Classical.choose h) e⟩
    else ⟨Sum.inl e.1, line e.2⟩
  have hf : ∀ e ∈ E, centerOK (f e).1 e ∧ (f e).2 = leaf (f e).1 e ∧ (f e).2 ∈ M (f e).1 := by
    intro e he
    have h := hcover e (Finset.mem_filter.mp he).2
    have hs := Classical.choose_spec h
    simpa [f,h] using (show centerOK (Classical.choose h) e ∧
      leaf (Classical.choose h) e = leaf (Classical.choose h) e ∧
      leaf (Classical.choose h) e ∈ M (Classical.choose h) from ⟨hs.1,rfl,hs.2⟩)
  have hb : E.card ≤ (Finset.univ.sigma M).card := by
    apply Finset.card_le_card_of_injOn f
    · intro e he
      exact Finset.mem_coe.mpr (Finset.mem_sigma.mpr ⟨Finset.mem_univ _, (hf e (Finset.mem_coe.mp he)).2.2⟩)
    · intro e he e' he' heq
      have hs := hf e (Finset.mem_coe.mp he)
      have ht := hf e' (Finset.mem_coe.mp he')
      rw [← heq] at ht
      have hv := hs.2.1.symm.trans ht.2.1
      cases hi : (f e).1 with
      | inl p =>
        have ep : e.1 = p := by simpa [hi,centerOK] using hs.1
        have ep' : e'.1 = p := by simpa [hi,centerOK] using ht.1
        have el : e.2 = e'.2 := (line_eq _ _).mp (by simpa [hi,leaf] using hv)
        exact Prod.ext (ep.trans ep'.symm) el
      | inr l =>
        have el : e.2 = l := by simpa [hi,centerOK] using hs.1
        have el' : e'.2 = l := by simpa [hi,centerOK] using ht.1
        have ep : e.1 = e'.1 := (point_eq _ _).mp (by simpa [hi,leaf] using hv)
        exact Prod.ext ep (el.trans el'.symm)
  rw [Finset.card_sigma] at hb
  exact hb.trans hcount

end PEqualNP.Outside.L_meta_2838

theorem PEqualNP.Outside.L_meta_2838 : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) → (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) → PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C → (∀ p l : Fin N, I p l → PEqualNP.MetaComplexity.circuitFun (N + N) C (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)) = true) → (∀ z : Fin (N + N) → Bool, (Finset.univ.filter (fun l : Fin N => z (Fin.natAdd N l) = true)).card ≤ q → (¬ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) → PEqualNP.MetaComplexity.circuitFun (N + N) C z = false) → {e : Fin N × Fin N | I e.1 e.2 ∧ ∃ j < C.gates.length, ∃ a c : ℕ, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs = [a, c] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs = [c, a]) ∧ (∀ z : Fin (N + N) → Bool, (C.wires (List.ofFn z)).getD (N + N + j) false = true → ∃ p0 l0 : Fin N, I p0 l0 ∧ z (Fin.castAdd N p0) = true ∧ z (Fin.natAdd N l0) = true) ∧ (C.wires (List.ofFn (fun k : Fin (N + N) => decide (k = Fin.castAdd N e.1)))).getD a false = true ∧ (C.wires (List.ofFn (fun k : Fin (N + N) => decide (k = Fin.natAdd N e.2)))).getD c false = true}.ncard ≤ 3 * C.size + 2 * N := by
  intro q N I inst C hq hN hlines hunique hmono hrb hright hsound
  classical
  let E : Finset (Fin N × Fin N) := Finset.univ.filter (fun e => ∃ g : Fin C.gates.length,
    PEqualNP.Outside.L_meta_2838.Wit I C.gates g e)
  have h4 : PEqualNP.Outside.L_meta_2838.NoRect I := by
    intro p p' l l' hp hl h1 h2 h3 h4
    obtain ⟨u, hu, huniq⟩ := hunique p p' hp
    exact hl ((huniq l ⟨h1,h2⟩).trans (huniq l' ⟨h3,h4⟩).symm)
  have legal : ∀ g ∈ C.gates,
      (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    obtain ⟨h1,h2⟩ := hmono g hg
    exact ⟨h1.elim Or.inl Or.inr,h2⟩
  have hin : ∀ i : Fin C.gates.length, ∀ a ∈ (C.gates.get i).inputs, a < N + N + (i : ℕ) := by
    intro i a ha
    apply hrb i i.2 a
    unfold PEqualNP.MetaComplexity.NestedCover.gateAt
    rw [List.getD_eq_getElem _ _ i.2]
    exact ha
  have hbound : E.card ≤ 3 * C.size :=
    PEqualNP.Outside.L_meta_2838.all_pairs I C.gates h4 legal hin
  have hs : {e : Fin N × Fin N | I e.1 e.2 ∧ ∃ j < C.gates.length, ∃ a c : ℕ,
      (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
      ((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs = [a,c] ∨
       (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs = [c,a]) ∧
      (∀ z : Fin (N+N) → Bool, (C.wires (List.ofFn z)).getD (N+N+j) false = true →
        ∃ p0 l0 : Fin N, I p0 l0 ∧ z (Fin.castAdd N p0) = true ∧ z (Fin.natAdd N l0) = true) ∧
      (C.wires (List.ofFn (fun k : Fin (N+N) => decide (k = Fin.castAdd N e.1)))).getD a false = true ∧
      (C.wires (List.ofFn (fun k : Fin (N+N) => decide (k = Fin.natAdd N e.2)))).getD c false = true}
        ⊆ (E : Set (Fin N × Fin N)) := by
    intro e he
    obtain ⟨hI,j,hj,a,c,hop,hins,hb,ha,hc⟩ := he
    apply Finset.mem_coe.mpr
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,⟨j,hj⟩,hI,?_,a,c,?_,hb,ha,hc⟩
    · simpa [PEqualNP.MetaComplexity.NestedCover.gateAt,List.getD_eq_getElem _ _ hj] using hop
    · simpa [PEqualNP.MetaComplexity.NestedCover.gateAt,List.getD_eq_getElem _ _ hj] using hins
  have hsub := Set.ncard_le_ncard hs (Set.toFinite _)
  rw [Set.ncard_coe_finset] at hsub
  omega

