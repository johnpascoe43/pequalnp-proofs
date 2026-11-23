import Mathlib
import PEqualNP.Defs


namespace PEqualNP.Outside.L_meta_583_aux
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_start (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_start gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_start gs w
  rw [ht, List.getD_append _ _ _ _ h]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

variable {n : ℕ}

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

def gateSupp (L : List (Finset (Fin n))) (g : Gate) : Finset (Fin n) :=
  (g.inputs.map fun a => L.getD a ∅).foldr (· ∪ ·) ∅

theorem mem_foldr_union (l : List ℕ) (F : ℕ → Finset (Fin n)) (i : Fin n) :
    i ∈ (l.map F).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ l, i ∈ F a := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih]

theorem mem_gateSupp (L : List (Finset (Fin n))) (g : Gate) (i : Fin n) :
    i ∈ gateSupp L g ↔ ∃ a ∈ g.inputs, i ∈ L.getD a ∅ :=
  mem_foldr_union _ _ _

def suppsFrom (gs : List Gate) (L : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  gs.foldl (fun L g => L ++ [gateSupp L g]) L

def inputSupps (n : ℕ) : List (Finset (Fin n)) := List.ofFn fun i : Fin n => {i}

def Agree (x y : Fin n → Bool) (L : List (Finset (Fin n))) (w w' : List Bool) : Prop :=
  L.length = w.length ∧ w.length = w'.length ∧
    ∀ j : ℕ, (∀ i ∈ L.getD j ∅, x i = y i) → w.getD j false = w'.getD j false

theorem agree_wiresFrom (x y : Fin n → Bool) (gs : List Gate) :
    ∀ (L : List (Finset (Fin n))) (w w' : List Bool), Agree x y L w w' →
      Agree x y (suppsFrom gs L) (wiresFrom gs w) (wiresFrom gs w') := by
  induction gs with
  | nil => intro L w w' h; exact h
  | cons g gs ih =>
    intro L w w' h
    obtain ⟨h1, h2, h3⟩ := h
    apply ih (L ++ [gateSupp L g])
      (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
    refine ⟨by simp [h1], by simp [h2], ?_⟩
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq] at hj
      rw [h1, getD_snoc_eq, h2, getD_snoc_eq]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact h3 a (fun i hi => hj i ((mem_gateSupp L g i).2 ⟨a, ha, hi⟩))
    · rw [getD_snoc_ne _ _ _ _ hjl] at hj
      rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
      exact h3 j hj

theorem agree_inputs (x y : Fin n → Bool) :
    Agree x y (inputSupps n) (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp [inputSupps], by simp, ?_⟩
  intro j hj
  by_cases hjn : j < n
  · have hx : x ⟨j, hjn⟩ = y ⟨j, hjn⟩ := hj _ (by simp [inputSupps, hjn])
    simp [hjn, hx]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

def Cnt (t : ℕ) (L : List (Finset (Fin n))) : Prop :=
  ∀ W : Finset ℕ, (W.biUnion fun j => L.getD j ∅).card ≤ t + W.card

theorem cnt_inputs : Cnt 0 (inputSupps n) := by
  intro W
  refine le_trans Finset.card_biUnion_le ?_
  rw [zero_add, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro j _
  by_cases hjn : j < n
  · simp [inputSupps, hjn]
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

theorem cnt_step (t : ℕ) (L : List (Finset (Fin n))) (g : Gate) (hg : g.inputs.length ≤ 2)
    (h : Cnt t L) : Cnt (t + 1) (L ++ [gateSupp L g]) := by
  intro W
  by_cases hW : L.length ∈ W
  · have hsub : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        ⊆ ((W.erase L.length ∪ g.inputs.toFinset).biUnion fun j => L.getD j ∅) := by
      intro i hi
      rw [Finset.mem_biUnion] at hi ⊢
      obtain ⟨j, hjW, hij⟩ := hi
      by_cases hjl : j = L.length
      · subst hjl
        rw [getD_snoc_eq] at hij
        obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g i).1 hij
        exact ⟨a, Finset.mem_union_right _ (List.mem_toFinset.2 ha), hia⟩
      · rw [getD_snoc_ne _ _ _ _ hjl] at hij
        exact ⟨j, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hjl, hjW⟩), hij⟩
    have hc1 : (W.erase L.length ∪ g.inputs.toFinset).card ≤ (W.card - 1) + 2 := by
      refine le_trans (Finset.card_union_le _ _) ?_
      rw [Finset.card_erase_of_mem hW]
      exact Nat.add_le_add_left (le_trans (List.toFinset_card_le _) hg) _
    have hWpos : 1 ≤ W.card := Finset.card_pos.2 ⟨_, hW⟩
    have := h (W.erase L.length ∪ g.inputs.toFinset)
    have := Finset.card_le_card hsub
    omega
  · have heq : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        = (W.biUnion fun j => L.getD j ∅) := by
      apply Finset.biUnion_congr rfl
      intro j hj
      exact getD_snoc_ne _ _ _ _ (fun e => hW (e ▸ hj))
    rw [heq]
    have := h W
    omega

theorem cnt_suppsFrom (gs : List Gate) : ∀ (t : ℕ) (L : List (Finset (Fin n))),
    (∀ g ∈ gs, Ok g) → Cnt t L → Cnt (t + gs.length) (suppsFrom gs L) := by
  induction gs with
  | nil => intro t L _ h; exact h
  | cons g gs ih =>
    intro t L hok h
    have := ih (t + 1) (L ++ [gateSupp L g]) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (cnt_step t L g (hok g List.mem_cons_self).2 h)
    rw [List.length_cons, show t + (gs.length + 1) = t + 1 + gs.length by omega]
    exact this

theorem dep_lower (n : ℕ) (f : (Fin n → Bool) → Bool)
    (hdep : ∀ i : Fin n, ∃ x : Fin n → Bool, f (Function.update x i (!x i)) ≠ f x)
    (s : ℕ) (h : HasCircuitSize n f s) : n ≤ s + 1 := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set S := (suppsFrom C.gates (inputSupps n)).getD C.output ∅ with hS
  have hall : ∀ i : Fin n, i ∈ S := by
    intro i
    by_contra hi
    obtain ⟨x, hx⟩ := hdep i
    apply hx
    have hag := (agree_wiresFrom (Function.update x i (!x i)) x C.gates _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ i := fun e => hi (e ▸ hk)
        simp [Function.update_of_ne this])
    rw [← hev, ← hev]
    exact hag
  have hcard : S.card = n := by
    rw [Finset.eq_univ_of_forall hall]; simp
  have hc := cnt_suppsFrom C.gates 0 (inputSupps n) ok cnt_inputs {C.output}
  simp only [Finset.singleton_biUnion, Finset.card_singleton, zero_add] at hc
  rw [← hS, hcard] at hc
  omega

def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

theorem normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

theorem normGate_nok (g : Gate) (h : Ok g) : NOk (normGate g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with h | h | h
  · have : op = GateOp.and := h
    subst this; exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.or := h
    subst this; exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.not := h
    subst this
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩ <;> simp [normGate] <;> omega

theorem wiresFrom_norm (gs : List Gate) : ∀ w : List Bool,
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    have s1 : wiresFrom ((g :: gs).map normGate) w = wiresFrom (gs.map normGate)
        (w ++ [(normGate g).op.eval ((normGate g).inputs.map fun i => w.getD i false)]) := rfl
    have s2 : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [s1, s2, normGate_eval, ih]

inductive Stat : Type
  | const (c : Bool)
  | wire (j : ℕ)

def Stat.val (w : List Bool) : Stat → Bool
  | Stat.const c => c
  | Stat.wire j => w.getD j false

def Stat.Valid (m : ℕ) : Stat → Prop
  | Stat.const _ => True
  | Stat.wire j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const true)
  | Stat.const c :: _ => (none, Stat.const (!c))
  | Stat.wire j :: _ => (some ⟨GateOp.not, [j]⟩, Stat.wire m)

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const true)
  | [Stat.const c] => (none, Stat.const c)
  | [Stat.wire j] => (none, Stat.wire j)
  | [Stat.const c, Stat.const d] => (none, Stat.const (c && d))
  | [Stat.const c, Stat.wire j] => (none, bif c then Stat.wire j else Stat.const false)
  | [Stat.wire j, Stat.const c] => (none, bif c then Stat.wire j else Stat.const false)
  | [Stat.wire j, Stat.wire k] => (some ⟨GateOp.and, [j, k]⟩, Stat.wire m)
  | _ => (none, Stat.const false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const false)
  | [Stat.const c] => (none, Stat.const c)
  | [Stat.wire j] => (none, Stat.wire j)
  | [Stat.const c, Stat.const d] => (none, Stat.const (c || d))
  | [Stat.const c, Stat.wire j] => (none, bif c then Stat.const true else Stat.wire j)
  | [Stat.wire j, Stat.const c] => (none, bif c then Stat.const true else Stat.wire j)
  | [Stat.wire j, Stat.wire k] => (some ⟨GateOp.or, [j, k]⟩, Stat.wire m)
  | _ => (none, Stat.const false)

def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Stat.const false)

theorem simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; simp [Ok])
  · simp at hg
  · simp at hg

theorem simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Stat.const c ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, s.Valid w.length) :
    ((simplify op w.length ins).2).Valid (w.length + (simplify op w.length ins).1.toList.length) ∧
    ((simplify op w.length ins).2).val (wiresFrom (simplify op w.length ins).1.toList w)
      = op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

theorem elim_getD (n k : ℕ) (d : Stat) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    k < acc.1.length → (elim n gs acc).1.getD k d = acc.1.getD k d := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hk
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, ih (elimStep n acc g) (by simp [elimStep]; omega)]
    exact getD_snoc_ne _ _ _ _ (by omega)

theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

theorem elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ acc.2, Ok g) → ∀ g ∈ (elim n gs acc).2, Ok g := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih (elimStep n acc g)
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplify_ok _ _ _ g' (by simpa using h1)

theorem elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimStep n acc g)
    have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_length_le (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1
      omega
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]; omega

theorem elim_len_lt (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, NOk g) → k < acc.1.length → (∃ c, acc.1.getD k (Stat.const false) = Stat.const c) →
    (∃ g ∈ gs, k ∈ g.inputs) → (elim n gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _ h; obtain ⟨g, hg, _⟩ := h; simp at hg
  | cons g gs ih =>
    intro acc hok hk hc hex
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]
    by_cases hkg : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1 = none := by
        apply simplify_count
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        show (acc.2 ++ (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList).length = _
        rw [hnone]; simp
      have := elim_len n gs (elimStep n acc g)
      omega
    · have hex' : ∃ g' ∈ gs, k ∈ g'.inputs := by
        obtain ⟨g', hg', hk'⟩ := hex
        rcases List.mem_cons.1 hg' with rfl | h
        · exact absurd hk' hkg
        · exact ⟨g', h, hk'⟩
      have h1 := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [elimStep]; omega)
        (by
          obtain ⟨c, hc⟩ := hc
          refine ⟨c, ?_⟩
          simp only [elimStep]
          rw [getD_snoc_ne _ _ _ _ (by omega)]; exact hc)
        hex'
      have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1
        omega
      omega

theorem Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Stat.const _, _ => trivial
  | Stat.wire _, hj => lt_of_lt_of_le hj h

theorem Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Stat.const _, _ => rfl
  | Stat.wire _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Stat.const false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Stat.const false)).val (wiresFrom acc.2 y) = w.getD i false

theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Stat.const false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (Stat.val w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, htl⟩ := wiresFrom_start r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show ((acc.1 ++ [r.2]).getD i (Stat.const false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i (Stat.const false)).val (wiresFrom (acc.2 ++ r.1.toList) y) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨Stat.valid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

def initStats (n : ℕ) (b : Bool) : List Stat :=
  List.ofFn (fun i : Fin n => Stat.wire i) ++ [Stat.const b]

theorem inv_init (n : ℕ) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y ++ [b]) (initStats n b, []) := by
  refine ⟨by simp [initStats], ?_⟩
  intro i
  have l1 : (List.ofFn (fun i : Fin n => Stat.wire i)).length = n := by simp
  have l2 : (List.ofFn y).length = n := by simp
  by_cases hin : i = n
  · subst hin
    simp only [initStats]
    rw [getD_snoc_len _ _ _ _ l1, getD_snoc_len _ _ _ _ l2]
    exact ⟨trivial, rfl⟩
  · simp only [initStats]
    rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
    by_cases hlt : i < n
    · simp [hlt, Stat.Valid, Stat.val, wiresFrom]
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      exact ⟨trivial, rfl⟩

theorem ofFn_snoc (n : ℕ) (y : Fin n → Bool) (b : Bool) :
    List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool) = List.ofFn y ++ [b] := by
  rw [List.ofFn_succ']
  simp

theorem supp_noread (n : ℕ) (gs : List Gate) : ∀ L : List (Finset (Fin (n + 1))),
    (∀ g ∈ gs, n ∉ g.inputs) → (∀ j : ℕ, j ≠ n → Fin.last n ∉ L.getD j ∅) →
    ∀ j : ℕ, j ≠ n → Fin.last n ∉ (suppsFrom gs L).getD j ∅ := by
  induction gs with
  | nil => intro L _ h; exact h
  | cons g gs ih =>
    intro L hno h
    apply ih (L ++ [gateSupp L g]) (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq]
      intro hmem
      obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g _).1 hmem
      exact h a (fun e => hno g List.mem_cons_self (e ▸ ha)) hia
    · rw [getD_snoc_ne _ _ _ _ hjl]; exact h j hj

theorem inputSupps_getD (m j : ℕ) (h : j < m) :
    (inputSupps m).getD j ∅ = {⟨j, h⟩} := by
  simp [inputSupps, h]

theorem inputSupps_noread (n : ℕ) : ∀ j : ℕ, j ≠ n →
    Fin.last n ∉ (inputSupps (n + 1)).getD j ∅ := by
  intro j hj
  by_cases hlt : j < n + 1
  · have e : (inputSupps (n + 1)).getD j ∅ = {⟨j, hlt⟩} := inputSupps_getD (n + 1) j hlt
    rw [e, Finset.mem_singleton]
    intro e'
    exact hj (by have := congrArg Fin.val e'; simpa using this.symm)
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

theorem gate_elim (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (b : Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x)
    (hnc : ∃ y y' : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc y' b))
    (h : HasCircuitSize (n + 1) f (s + 1)) :
    HasCircuitSize n (fun y : Fin n → Bool => f (Fin.snoc y b)) s := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s + 1 := hsz
  set gs := C.gates.map normGate with hgs
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (ok g0 hg0)
  have hevg : ∀ x : Fin (n + 1) → Bool, (wiresFrom gs (List.ofFn x)).getD C.output false = f x := by
    intro x
    rw [hgs, wiresFrom_norm, ← hev x]; rfl
  set acc := elim n gs (initStats n b, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool))) acc := by
    intro y
    rw [ofFn_snoc]
    exact inv_elim n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_init n b y)
  have hval : ∀ y : Fin n → Bool,
      (acc.1.getD C.output (Stat.const false)).val (wiresFrom acc.2 (List.ofFn y))
        = f (Fin.snoc y b) := by
    intro y
    rw [((hinv y).2 C.output).2, hevg]
  have hvalid : (acc.1.getD C.output (Stat.const false)).Valid (n + acc.2.length) := by
    obtain ⟨y, _, _⟩ := hnc
    exact ((hinv y).2 C.output).1
  cases hst : acc.1.getD C.output (Stat.const false) with
  | const c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | wire j =>
    have hlen : acc.2.length ≤ s := by
      by_cases hread : ∃ g ∈ gs, n ∈ g.inputs
      · have := elim_len_lt n n gs (initStats n b, []) hnok (by simp [initStats])
          ⟨b, getD_snoc_len _ _ _ _ (by simp)⟩ hread
        rw [← hacc] at this
        have hl : gs.length = C.gates.length := by simp [hgs]
        simp only [List.length_nil, zero_add] at this
        omega
      · exfalso
        push Not at hread
        have hout : C.output ≠ n := by
          intro e
          rw [e, hacc, elim_getD n n _ gs _ (by simp [initStats])] at hst
          have hb : (initStats n b).getD n (Stat.const false) = Stat.const b :=
            getD_snoc_len _ _ _ _ (by simp)
          rw [show ((initStats n b, ([] : List Gate))).1 = initStats n b from rfl, hb] at hst
          cases hst
        obtain ⟨x, hx⟩ := hdep
        apply hx
        have hns := supp_noread n gs (inputSupps (n + 1)) hread (inputSupps_noread n) C.output hout
        have hag := (agree_wiresFrom (Function.update x (Fin.last n) (!x (Fin.last n))) x gs _ _ _
          (agree_inputs _ _)).2.2 C.output (by
            intro k hk
            have : k ≠ Fin.last n := fun e => hns (e ▸ hk)
            simp [Function.update_of_ne this])
        rw [← hevg, ← hevg]
        exact hag
    refine ⟨⟨acc.2, j⟩, elim_ok n gs _ (by simp), hlen, ?_⟩
    intro y
    have := hval y
    rw [hst] at this
    exact this

theorem elim_cons (n : ℕ) (g : Gate) (gs : List Gate) (acc : List Stat × List Gate) :
    elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl

theorem elim_append (n : ℕ) (pre post : List Gate) (acc : List Stat × List Gate) :
    elim n (pre ++ post) acc = elim n post (elim n pre acc) := by
  simp [elim, List.foldl_append]

theorem elim_fst_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).1.length = acc.1.length + gs.length := by
  induction gs with
  | nil => intro acc; rfl
  | cons g gs ih =>
    intro acc
    rw [elim_cons, ih]
    simp only [elimStep, List.length_append, List.length_cons, List.length_nil]
    omega

theorem initStats_last (n : ℕ) (b : Bool) :
    (initStats n b).getD n (Stat.const false) = Stat.const b :=
  getD_snoc_len _ _ _ _ (by simp)

theorem simplify_const (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (b : Bool)
    (hand : op = GateOp.and → b = false) (hor : op = GateOp.or → b = true)
    (hc : Stat.const b ∈ ins) : ∃ c, (simplify op m ins).2 = Stat.const c := by
  rcases hop with rfl | rfl | rfl
  · have := hand rfl
    subst this
    rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
      simp_all [simplify, simpAnd]
  · have := hor rfl
    subst this
    rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨d, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

theorem elimStep_none (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (c : Bool) (hc : acc.1.getD k (Stat.const false) = Stat.const c) :
    (elimStep n acc g).2.length = acc.2.length := by
  have hnone : (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1 = none := by
    apply simplify_count
    · exact hg.1.1
    · simpa using hg.1.2
    · intro h; simpa using hg.2 h
    · exact ⟨c, List.mem_map.2 ⟨k, hk, hc⟩⟩
  show (acc.2 ++ (simplify g.op (n + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList).length = _
  rw [hnone]; simp

def fixBit (g : Gate) : Bool :=
  match g.op with
  | GateOp.or => true
  | _ => false

theorem elimStep_const (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (hc : acc.1.getD k (Stat.const false) = Stat.const (fixBit g)) :
    ∃ c, (elimStep n acc g).1.getD acc.1.length (Stat.const false) = Stat.const c := by
  have e : (elimStep n acc g).1.getD acc.1.length (Stat.const false)
      = (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).2 := getD_snoc_eq _ _ _
  rw [e]
  apply simplify_const _ _ _ hg.1.1 (by simpa using hg.1.2) (fun h => by simpa using hg.2 h)
    (fixBit g)
  · intro h; simp [fixBit, h]
  · intro h; simp [fixBit, h]
  · exact List.mem_map.2 ⟨k, hk, hc⟩

theorem suppsFrom_append {n : ℕ} (pre post : List Gate) (L : List (Finset (Fin n))) :
    suppsFrom (pre ++ post) L = suppsFrom post (suppsFrom pre L) := by
  simp [suppsFrom, List.foldl_append]

theorem length_suppsFrom {n : ℕ} (gs : List Gate) : ∀ L : List (Finset (Fin n)),
    (suppsFrom gs L).length = L.length + gs.length := by
  induction gs with
  | nil => intro L; rfl
  | cons g gs ih =>
    intro L
    have h : suppsFrom (g :: gs) L = suppsFrom gs (L ++ [gateSupp L g]) := rfl
    rw [h, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

def CleanGate (m : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.not ∧ ∃ j, j < m ∧ g.inputs = [j]) ∨
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ j k, j < m ∧ k < m ∧ g.inputs = [j, k])

def CleanL (m : ℕ) (gs : List Gate) : Prop :=
  ∀ (p : ℕ) (g : Gate), gs[p]? = some g → CleanGate (m + p) g

theorem CleanGate.nok {m : ℕ} {g : Gate} (h : CleanGate m g) : NOk g := by
  rcases h with ⟨h1, j, _, h2⟩ | ⟨h1 | h1, j, k, _, _, h2⟩
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inr (Or.inr rfl)
    · rw [h2]; simp
    · intro _; rw [h2]; simp
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inl rfl
    · rw [h2]; simp
    · intro h; rw [h1] at h; cases h
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inr (Or.inl rfl)
    · rw [h2]; simp
    · intro h; rw [h1] at h; cases h

theorem CleanGate.lt {m : ℕ} {g : Gate} (h : CleanGate m g) : ∀ a ∈ g.inputs, a < m := by
  intro a ha
  rcases h with ⟨_, j, hj, h2⟩ | ⟨_, j, k, hj, hk, h2⟩
  · rw [h2] at ha
    simp at ha
    subst ha; exact hj
  · rw [h2] at ha
    simp at ha
    rcases ha with rfl | rfl
    · exact hj
    · exact hk

theorem clean_nok (m : ℕ) (gs : List Gate) (h : CleanL m gs) : ∀ g ∈ gs, NOk g := by
  intro g hg
  obtain ⟨p, hp⟩ := List.mem_iff_getElem?.1 hg
  exact (h p g hp).nok

theorem simplify_clean (op : GateOp) (m : ℕ) (ins : List Stat) (hv : ∀ s ∈ ins, s.Valid m) :
    ∀ g ∈ (simplify op m ins).1, CleanGate m g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg
    refine Or.inr ⟨Or.inl rfl, _, _, ?_, ?_, rfl⟩
    · exact hv _ List.mem_cons_self
    · exact hv _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg
    refine Or.inr ⟨Or.inr rfl, _, _, ?_, ?_, rfl⟩
    · exact hv _ List.mem_cons_self
    · exact hv _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot] at hg
    subst hg
    refine Or.inl ⟨rfl, _, ?_, rfl⟩
    exact hv _ List.mem_cons_self
  · simp at hg
  · simp at hg

theorem toList_getElem? {α : Type} (o : Option α) (k : ℕ) (a : α)
    (h : o.toList[k]? = some a) : k = 0 ∧ a ∈ o := by
  cases o with
  | none => simp at h
  | some b =>
    cases k with
    | zero => simp at h; simp [h]
    | succ k => simp at h

theorem clean_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      CleanL n acc.2 → CleanL n (elim n gs acc).2 := by
  induction gs with
  | nil => intro w acc _ _ h; exact h
  | cons g gs ih =>
    intro w acc hok hinv hcl
    have hinv' : Inv n y (wiresFrom [g] w) (elimStep n acc g) :=
      inv_elim n y hy [g] w acc (fun g' hg' => hok g' (by simp at hg'; simp [hg'])) hinv
    refine ih _ (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')) hinv' ?_
    intro p g' hp
    have hp' : (acc.2 ++ (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList)[p]? = some g' := hp
    by_cases hlt : p < acc.2.length
    · rw [List.getElem?_append_left hlt] at hp'
      exact hcl p g' hp'
    · rw [List.getElem?_append_right (by omega)] at hp'
      obtain ⟨h0, hmem⟩ := toList_getElem? _ _ _ hp'
      have hpl : p = acc.2.length := by omega
      rw [hpl]
      exact simplify_clean _ _ _ (fun s hs => by
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        exact (hinv.2 a).1) g' hmem

def HasClean (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
  ∃ (gs : List Gate) (o : ℕ), CleanL n gs ∧ gs.length ≤ s ∧
    ∀ x : Fin n → Bool, (wiresFrom gs (List.ofFn x)).getD o false = f x

def idStats (n : ℕ) : List Stat := List.ofFn (fun i : Fin n => Stat.wire i)

theorem inv_id (n : ℕ) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y) (idStats n, []) := by
  refine ⟨by simp [idStats], ?_⟩
  intro i
  by_cases hlt : i < n
  · simp [idStats, hlt, Stat.Valid, Stat.val, wiresFrom]
  · rw [List.getD_eq_default _ _ (by simp [idStats]; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

theorem clean_of (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ)
    (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (h : HasCircuitSize n f s) : HasClean n f s := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  have hok : ∀ g ∈ C.gates, Ok g := ok
  set acc := elim n C.gates (idStats n, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom C.gates (List.ofFn y)) acc :=
    fun y => inv_elim n _ (by simp) C.gates _ _ hok (inv_id n y)
  have hval : ∀ y : Fin n → Bool,
      (acc.1.getD C.output (Stat.const false)).val (wiresFrom acc.2 (List.ofFn y)) = f y := by
    intro y
    rw [((hinv y).2 C.output).2, ← hev y]; rfl
  cases hst : acc.1.getD C.output (Stat.const false) with
  | const c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | wire j =>
    refine ⟨acc.2, j, ?_, ?_, ?_⟩
    · exact clean_elim n (List.ofFn fun _ : Fin n => false) (by simp) C.gates _ _ hok
        (inv_id n _) (by intro p g hp; simp at hp)
    · have := elim_len n C.gates (idStats n, [])
      rw [← hacc] at this
      simp only [List.length_nil, zero_add] at this
      omega
    · intro y
      have := hval y
      rw [hst] at this
      exact this

theorem getD_ofFn {α : Type} (m : ℕ) (F : Fin m → α) (d : α) (j : Fin m) :
    (List.ofFn F).getD j d = F j := by
  simp
theorem split_at {α : Type} : ∀ (l : List α) (p : ℕ) (g : α), l[p]? = some g →
    ∃ pre post, l = pre ++ g :: post ∧ pre.length = p := by
  intro l
  induction l with
  | nil => intro p g h; simp at h
  | cons x l ih =>
    intro p g h
    cases p with
    | zero =>
      simp at h
      subst h
      exact ⟨[], l, rfl, rfl⟩
    | succ p =>
      simp at h
      obtain ⟨pre, post, rfl, rfl⟩ := ih p g h
      exact ⟨x :: pre, post, rfl, rfl⟩

end PEqualNP.Outside.L_meta_583_aux

namespace PEqualNP.Outside.L_meta_583_aux
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

def kept {α : Type} (b : Bool) (x : α) (xs : List α) : List α :=
  if b then x :: xs else xs

inductive Run {α : Type} (inv : α → α) (meet join : α → α → α) (y : α) : ℕ → List α → Prop
  | done : Run inv meet join y 0 [y]
  | perm {s xs zs} : xs.Perm zs → Run inv meet join y s xs → Run inv meet join y s zs
  | one {s a rest} (neg save : Bool) :
      Run inv meet join y s ((if neg then inv a else a) :: kept save a rest) →
      Run inv meet join y (s+1) (a :: rest)
  | two {s a b rest} (conj ka kb : Bool) :
      Run inv meet join y s ((if conj then meet a b else join a b) :: kept ka a (kept kb b rest)) →
      Run inv meet join y (s+1) (a :: b :: rest)

theorem kept_map {α β : Type} (e : α → β) (b : Bool) (x : α) (xs : List α) :
    (kept b x xs).map e = kept b (e x) (xs.map e) := by
  cases b <;> simp [kept]

theorem mem_kept {α : Type} (b : Bool) (x a : α) (xs : List α) :
    a ∈ kept b x xs ↔ (b = true ∧ a = x) ∨ a ∈ xs := by
  cases b <;> simp [kept]

theorem nodup_kept {α : Type} (b : Bool) (x : α) (xs : List α) (h : xs.Nodup) (hx : x ∉ xs) :
    (kept b x xs).Nodup := by
  cases b
  · simpa [kept] using h
  · simpa [kept] using And.intro hx h

theorem Run.map {α β : Type} (e : α → β) {inv : α → α} {meet join : α → α → α}
    {inv' : β → β} {meet' join' : β → β → β}
    (hi : ∀ a, e (inv a) = inv' (e a)) (hm : ∀ a b, e (meet a b) = meet' (e a) (e b))
    (hj : ∀ a b, e (join a b) = join' (e a) (e b))
    {y : α} {s : ℕ} {ws : List α} (h : Run inv meet join y s ws) :
    Run inv' meet' join' (e y) s (ws.map e) := by
  induction h with
  | done => exact Run.done
  | perm hp _ ih => exact Run.perm (hp.map e) ih
  | @one s a rest neg save _ ih =>
    have e1 : ((if neg then inv a else a) :: kept save a rest).map e
        = (if neg then inv' (e a) else e a) :: kept save (e a) (rest.map e) := by
      cases neg <;> simp [kept_map, hi]
    rw [e1] at ih
    exact Run.one neg save ih
  | @two s a b rest conj ka kb _ ih =>
    have e1 : ((if conj then meet a b else join a b) :: kept ka a (kept kb b rest)).map e
        = (if conj then meet' (e a) (e b) else join' (e a) (e b))
            :: kept ka (e a) (kept kb (e b) (rest.map e)) := by
      cases conj <;> simp [kept_map, hm, hj]
    rw [e1] at ih
    exact Run.two conj ka kb ih

abbrev BFn (n : ℕ) := (Fin n → Bool) → Bool

def val (gs : List Gate) (n : ℕ) (a : ℕ) : BFn n :=
  fun x => (wiresFrom gs (List.ofFn x)).getD a false

theorem val_input (gs : List Gate) (n : ℕ) (i : Fin n) : val gs n i = fun x => x i := by
  funext x
  unfold val
  rw [getD_wiresFrom _ _ _ (by simp)]
  simp

theorem val_gate (n : ℕ) (gs : List Gate) (p : ℕ) (g : Gate) (hp : gs[p]? = some g)
    (hlt : ∀ a ∈ g.inputs, a < n + p) (x : Fin n → Bool) :
    val gs n (n + p) x = g.op.eval (g.inputs.map fun a => val gs n a x) := by
  obtain ⟨pre, post, rfl, hlen⟩ := split_at gs p g hp
  unfold val
  have h1 : wiresFrom (pre ++ g :: post) (List.ofFn x) = wiresFrom post
      (wiresFrom pre (List.ofFn x) ++
        [g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn x)).getD i false)]) := by
    rw [wiresFrom_append]; rfl
  have hl : (wiresFrom pre (List.ofFn x)).length = n + p := by
    rw [length_wiresFrom]; simp [hlen]
  rw [h1, getD_wiresFrom _ _ _ (by simp [hl]), getD_snoc_len _ _ _ _ hl]
  congr 1
  apply List.map_congr_left
  intro a ha
  have hal := hlt a ha
  have e1 := getD_wiresFrom post (wiresFrom pre (List.ofFn x) ++
        [g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn x)).getD i false)]) a
        (by simp [hl]; omega)
  rw [e1, List.getD_append _ _ _ _ (by omega)]

def shift (K a : ℕ) : ℕ := if a < K then a else a - 1

def shGate (K : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (shift K)⟩

def RelD (K : ℕ) (W W' : List Bool) : Prop :=
  W.length = W'.length + 1 ∧ K ≤ W'.length ∧
    ∀ a, a ≠ K → W'.getD (shift K a) false = W.getD a false

theorem relD_wires (K : ℕ) (post : List Gate) : ∀ W W' : List Bool,
    (∀ g ∈ post, K ∉ g.inputs) → RelD K W W' →
    RelD K (wiresFrom post W) (wiresFrom (post.map (shGate K)) W') := by
  induction post with
  | nil => intro W W' _ h; exact h
  | cons g post ih =>
    intro W W' hno h
    obtain ⟨h1, h2, h3⟩ := h
    have hv : (shGate K g).op.eval ((shGate K g).inputs.map fun i => W'.getD i false)
        = g.op.eval (g.inputs.map fun i => W.getD i false) := by
      simp only [shGate, List.map_map]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact h3 a (fun e => hno g List.mem_cons_self (e ▸ ha))
    have s1 : wiresFrom (g :: post) W
        = wiresFrom post (W ++ [g.op.eval (g.inputs.map fun i => W.getD i false)]) := rfl
    have s2 : wiresFrom ((g :: post).map (shGate K)) W'
        = wiresFrom (post.map (shGate K))
          (W' ++ [(shGate K g).op.eval ((shGate K g).inputs.map fun i => W'.getD i false)]) := rfl
    rw [s1, s2, hv]
    apply ih _ _ (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
    refine ⟨by simp; omega, by simp; omega, ?_⟩
    intro a haK
    rcases Nat.lt_trichotomy a W.length with hw | hw | hw
    · have hlt : shift K a < W'.length := by
        unfold shift; split <;> omega
      rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
      exact h3 a haK
    · have he : shift K a = W'.length := by
        unfold shift; split <;> omega
      rw [he, hw, getD_snoc_eq, getD_snoc_eq]
    · have hge : W'.length + 1 ≤ shift K a := by
        unfold shift; split <;> omega
      rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

theorem del_gate (n : ℕ) (pre : List Gate) (g : Gate) (post : List Gate) (o : ℕ) (f : BFn n)
    (hok : ∀ g' ∈ pre ++ g :: post, Ok g')
    (hno : ∀ g' ∈ post, n + pre.length ∉ g'.inputs) (ho : o ≠ n + pre.length)
    (hev : ∀ x, val (pre ++ g :: post) n o x = f x) :
    HasCircuitSize n f (pre.length + post.length) := by
  refine ⟨⟨pre ++ post.map (shGate (n + pre.length)), shift (n + pre.length) o⟩, ?_, ?_, ?_⟩
  · intro g' hg'
    rcases List.mem_append.1 hg' with h | h
    · exact hok g' (List.mem_append_left _ h)
    · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 h
      have := hok g0 (List.mem_append_right _ (List.mem_cons_of_mem _ hg0))
      exact ⟨this.1, by simpa [shGate] using this.2⟩
  · simp [Circuit.size]
  · intro x
    rw [← hev x]
    show (wiresFrom (pre ++ post.map (shGate (n + pre.length))) (List.ofFn x)).getD
      (shift (n + pre.length) o) false = _
    unfold val
    have h1 : wiresFrom (pre ++ g :: post) (List.ofFn x) = wiresFrom post
        (wiresFrom pre (List.ofFn x) ++
          [g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn x)).getD i false)]) := by
      rw [wiresFrom_append]; rfl
    have hl : (wiresFrom pre (List.ofFn x)).length = n + pre.length := by
      rw [length_wiresFrom]; simp
    rw [h1, wiresFrom_append]
    refine (relD_wires (n + pre.length) post _ _ hno ⟨by simp, by omega, ?_⟩).2.2 o ho
    intro a ha
    by_cases hlt : a < n + pre.length
    · have : shift (n + pre.length) a = a := by simp [shift, hlt]
      rw [this, List.getD_append _ _ _ _ (by omega)]
    · have : shift (n + pre.length) a = a - 1 := by simp [shift, hlt]
      rw [this, List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by simp; omega)]

def Live (gs : List Gate) (o p a : ℕ) : Prop :=
  a = o ∨ ∃ q, p ≤ q ∧ ∃ g, gs[q]? = some g ∧ a ∈ g.inputs

open Classical in
noncomputable def liveList (gs : List Gate) (n o p : ℕ) : List ℕ :=
  (List.range (n + p)).filter (fun a => decide (Live gs o p a))

theorem mem_liveList (gs : List Gate) (n o p a : ℕ) :
    a ∈ liveList gs n o p ↔ a < n + p ∧ Live gs o p a := by
  simp [liveList]

theorem nodup_liveList (gs : List Gate) (n o p : ℕ) : (liveList gs n o p).Nodup :=
  List.Nodup.filter _ List.nodup_range

abbrev invF {n : ℕ} : BFn n → BFn n := fun a x => !a x
abbrev meetF {n : ℕ} : BFn n → BFn n → BFn n := fun a b x => a x && b x
abbrev joinF {n : ℕ} : BFn n → BFn n → BFn n := fun a b x => a x || b x

theorem live_succ (n : ℕ) (gs : List Gate) (o : ℕ) (hcl : CleanL n gs)
    (hnd : ∀ p, p < gs.length → n + p = o ∨ ∃ (q : ℕ) (g : Gate), gs[q]? = some g ∧ n + p ∈ g.inputs)
    (p : ℕ) (g : Gate) (hg : gs[p]? = some g) (a : ℕ) :
    a ∈ liveList gs n o (p + 1) ↔
      a = n + p ∨ (a ∈ liveList gs n o p ∧ (a ∈ g.inputs → Live gs o (p + 1) a)) := by
  have hplt : p < gs.length := (List.getElem?_eq_some_iff.1 hg).1
  rw [mem_liveList, mem_liveList]
  constructor
  · rintro ⟨hlt, hl⟩
    by_cases ha : a = n + p
    · exact Or.inl ha
    · refine Or.inr ⟨⟨by omega, ?_⟩, fun _ => hl⟩
      rcases hl with h | ⟨q, hq, g', hg', hin⟩
      · exact Or.inl h
      · exact Or.inr ⟨q, by omega, g', hg', hin⟩
  · rintro (rfl | ⟨⟨hlt, hl⟩, himp⟩)
    · refine ⟨by omega, ?_⟩
      rcases hnd p hplt with h | ⟨q, g', hg', hin⟩
      · exact Or.inl h
      · refine Or.inr ⟨q, ?_, g', hg', hin⟩
        have := (hcl q g' hg').lt _ hin
        omega
    · refine ⟨by omega, ?_⟩
      rcases hl with h | ⟨q, hq, g', hg', hin⟩
      · exact Or.inl h
      · by_cases hqp : q = p
        · subst hqp
          rw [hg] at hg'
          cases hg'
          exact himp hin
        · exact Or.inr ⟨q, by omega, g', hg', hin⟩

open Classical in
theorem run_live (n : ℕ) (gs : List Gate) (o : ℕ) (hcl : CleanL n gs) (ho : o < n + gs.length)
    (hnd : ∀ p, p < gs.length → n + p = o ∨ ∃ (q : ℕ) (g : Gate), gs[q]? = some g ∧ n + p ∈ g.inputs) :
    ∀ d p, p + d = gs.length →
      Run (invF (n := n)) meetF joinF (val gs n o) d ((liveList gs n o p).map (val gs n)) := by
  intro d
  induction d with
  | zero =>
    intro p hp
    have hperm : [o].Perm (liveList gs n o p) := by
      refine (List.perm_ext_iff_of_nodup (List.nodup_singleton o) (nodup_liveList _ _ _ _)).2 ?_
      intro a
      rw [mem_liveList, List.mem_singleton]
      constructor
      · rintro rfl; exact ⟨by omega, Or.inl rfl⟩
      · rintro ⟨_, h | ⟨q, hq, g', hg', _⟩⟩
        · exact h
        · have := (List.getElem?_eq_some_iff.1 hg').1
          omega
    exact Run.perm (hperm.map (val gs n)) Run.done
  | succ d ih =>
    intro p hp
    have hplt : p < gs.length := by omega
    obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hplt⟩
    have IH := ih (p + 1) (by omega)
    have hstep := live_succ n gs o hcl hnd p g hg
    have hin : ∀ a ∈ g.inputs, a ∈ liveList gs n o p := fun a ha =>
      (mem_liveList _ _ _ _ _).2 ⟨(hcl p g hg).lt a ha, Or.inr ⟨p, le_rfl, g, hg, ha⟩⟩
    have hnew : ∀ a ∈ liveList gs n o p, a ≠ n + p := fun a ha =>
      Nat.ne_of_lt ((mem_liveList _ _ _ _ _).1 ha).1
    have hvg := val_gate n gs p g hg (hcl p g hg).lt
    have hnd0 := nodup_liveList gs n o p
    
    have single : ∀ (j : ℕ) (neg : Bool), (∀ a, a ∈ g.inputs ↔ a = j) →
        val gs n (n + p) = (if neg then invF (val gs n j) else val gs n j) →
        Run (invF (n := n)) meetF joinF (val gs n o) (d + 1)
          ((liveList gs n o p).map (val gs n)) := by
      intro j neg hmem hval
      have hj := hin j ((hmem j).2 rfl)
      have hp1 : (liveList gs n o p).Perm (j :: (liveList gs n o p).erase j) :=
        List.perm_cons_erase hj
      have hnr : ((liveList gs n o p).erase j).Nodup := hnd0.erase j
      have hp2 : (liveList gs n o (p + 1)).Perm
          ((n + p) :: kept (decide (Live gs o (p + 1) j)) j ((liveList gs n o p).erase j)) := by
        refine (List.perm_ext_iff_of_nodup (nodup_liveList _ _ _ _) ?_).2 ?_
        · refine List.nodup_cons.2 ⟨?_, nodup_kept _ _ _ hnr (by simp [hnd0.mem_erase_iff])⟩
          rw [mem_kept]
          rintro (⟨_, h⟩ | h)
          · exact hnew j hj h.symm
          · exact hnew _ (List.mem_of_mem_erase h) rfl
        · intro a
          rw [hstep a, List.mem_cons, mem_kept, hnd0.mem_erase_iff, hmem a]
          simp only [decide_eq_true_eq]
          constructor
          · rintro (h | ⟨h1, h2⟩)
            · exact Or.inl h
            · by_cases haj : a = j
              · exact Or.inr (Or.inl ⟨haj ▸ h2 haj, haj⟩)
              · exact Or.inr (Or.inr ⟨haj, h1⟩)
          · rintro (h | ⟨h1, rfl⟩ | ⟨h1, h2⟩)
            · exact Or.inl h
            · exact Or.inr ⟨hj, fun _ => h1⟩
            · exact Or.inr ⟨h2, fun h => absurd h h1⟩
      have IH' := Run.perm (hp2.map (val gs n)) IH
      rw [List.map_cons, kept_map, hval] at IH'
      exact Run.perm (hp1.map (val gs n)).symm (Run.one neg _ IH')
    rcases hcl p g hg with ⟨hop, j, hj, hinp⟩ | ⟨hop, j, k, hj, hk, hinp⟩
    · apply single j true
      · intro a; simp [hinp]
      · funext x
        rw [hvg x, hop, hinp]
        simp [GateOp.eval]
    · by_cases hjk : j = k
      · subst hjk
        apply single j false
        · intro a; simp [hinp]
        · funext x
          rw [hvg x, hinp]
          rcases hop with hop | hop <;> rw [hop] <;> simp [GateOp.eval]
      · have hjm := hin j (by simp [hinp])
        have hkm := hin k (by simp [hinp])
        have hke : k ∈ (liveList gs n o p).erase j :=
          (hnd0.mem_erase_iff).2 ⟨fun e => hjk e.symm, hkm⟩
        have hnr : ((liveList gs n o p).erase j).Nodup := hnd0.erase j
        have hnr2 : (((liveList gs n o p).erase j).erase k).Nodup := hnr.erase k
        have hp1 : (liveList gs n o p).Perm
            (j :: k :: ((liveList gs n o p).erase j).erase k) :=
          (List.perm_cons_erase hjm).trans ((List.perm_cons_erase hke).cons j)
        have hmr : ∀ a, a ∈ ((liveList gs n o p).erase j).erase k ↔
            a ≠ k ∧ a ≠ j ∧ a ∈ liveList gs n o p := by
          intro a
          rw [hnr.mem_erase_iff, hnd0.mem_erase_iff]
        have hp2 : (liveList gs n o (p + 1)).Perm
            ((n + p) :: kept (decide (Live gs o (p + 1) j)) j
              (kept (decide (Live gs o (p + 1) k)) k
                (((liveList gs n o p).erase j).erase k))) := by
          refine (List.perm_ext_iff_of_nodup (nodup_liveList _ _ _ _) ?_).2 ?_
          · refine List.nodup_cons.2 ⟨?_, nodup_kept _ _ _ (nodup_kept _ _ _ hnr2 ?_) ?_⟩
            · rw [mem_kept, mem_kept]
              rintro (⟨_, h⟩ | ⟨_, h⟩ | h)
              · exact hnew j hjm h.symm
              · exact hnew k hkm h.symm
              · exact hnew _ ((hmr _).1 h).2.2 rfl
            · rw [hmr]; simp
            · rw [mem_kept, hmr]
              rintro (⟨_, h⟩ | h)
              · exact hjk h
              · exact h.2.1 rfl
          · intro a
            rw [hstep a, List.mem_cons, mem_kept, mem_kept, hmr a]
            simp only [decide_eq_true_eq, hinp, List.mem_cons, List.not_mem_nil, or_false]
            constructor
            · rintro (h | ⟨h1, h2⟩)
              · exact Or.inl h
              · by_cases haj : a = j
                · exact Or.inr (Or.inl ⟨haj ▸ h2 (Or.inl haj), haj⟩)
                · by_cases hak : a = k
                  · exact Or.inr (Or.inr (Or.inl ⟨hak ▸ h2 (Or.inr hak), hak⟩))
                  · exact Or.inr (Or.inr (Or.inr ⟨hak, haj, h1⟩))
            · rintro (h | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, h2, h3⟩)
              · exact Or.inl h
              · exact Or.inr ⟨hjm, fun _ => h1⟩
              · exact Or.inr ⟨hkm, fun _ => h1⟩
              · exact Or.inr ⟨h3, fun h => by rcases h with h | h <;> contradiction⟩
        have IH' := Run.perm (hp2.map (val gs n)) IH
        have hval : val gs n (n + p) = (if decide (g.op = GateOp.and)
            then meetF (val gs n j) (val gs n k) else joinF (val gs n j) (val gs n k)) := by
          funext x
          rw [hvg x, hinp]
          rcases hop with hop | hop <;> rw [hop] <;> simp [GateOp.eval]
        rw [List.map_cons, kept_map, kept_map, hval] at IH'
        exact Run.perm (hp1.map (val gs n)).symm (Run.two _ _ _ IH')

theorem exists_run {n : ℕ} (f : BFn n) (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (s : ℕ)
    (h : HasCircuitSize n f s) :
    ∃ s', s' ≤ s ∧ ∃ ws : List (BFn n),
      ws.Sublist (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i)) ∧
      Run (invF (n := n)) meetF joinF f s' ws := by
  classical
  let P : ℕ → Prop := fun t => ∃ (gs : List Gate) (o : ℕ), CleanL n gs ∧ gs.length = t ∧
    ∀ x, val gs n o x = f x
  have hP : ∀ t, HasCircuitSize n f t → ∃ t', t' ≤ t ∧ P t' := by
    intro t ht
    obtain ⟨gs, o, hcl, hsz, hev⟩ := clean_of n f t hnc ht
    exact ⟨gs.length, hsz, gs, o, hcl, rfl, hev⟩
  obtain ⟨t0, ht0, hPt0⟩ := hP s h
  have hex : ∃ t, P t := ⟨t0, hPt0⟩
  have hmin : Nat.find hex ≤ t0 := Nat.find_min' hex hPt0
  obtain ⟨gs, o, hcl, hlen, hev⟩ := Nat.find_spec hex
  have hok : ∀ g ∈ gs, Ok g := fun g hg => (clean_nok _ gs hcl g hg).1
  have ho : o < n + gs.length := by
    by_contra hge
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hev y, ← hev y']
    unfold val
    rw [List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp; omega),
      List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp; omega)]
  have hnd : ∀ p, p < gs.length → n + p = o ∨ ∃ (q : ℕ) (g : Gate), gs[q]? = some g ∧ n + p ∈ g.inputs := by
    intro p hp
    by_contra hcon
    push_neg at hcon
    obtain ⟨hpo, hno⟩ := hcon
    obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hp⟩
    obtain ⟨pre, post, rfl, hpl⟩ := split_at gs p g hg
    have hsz := del_gate n pre g post o f hok (by
      intro g' hg'
      obtain ⟨q, hq⟩ := List.mem_iff_getElem?.1 hg'
      have := hno (pre.length + 1 + q) g' (by
        rw [List.getElem?_append_right (by omega)]
        have e : pre.length + 1 + q - pre.length = q + 1 := by omega
        rw [e]; simpa using hq)
      rw [hpl]; exact this) (by rw [hpl]; exact fun e => hpo e.symm) hev
    obtain ⟨t', ht', hPt'⟩ := hP _ hsz
    have := Nat.find_min' hex hPt'
    simp at hlen
    omega
  refine ⟨gs.length, by omega, (liveList gs n o 0).map (val gs n), ?_, ?_⟩
  · have e : (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i))
        = (List.range n).map (val gs n) := by
      apply List.ext_getElem
      · simp
      · intro i h1 h2
        simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range]
        exact (val_input gs n ⟨i, by simpa using h1⟩).symm
    rw [e]
    exact (List.filter_sublist).map _
  · have hf : val gs n o = f := funext hev
    rw [← hf]
    exact run_live n gs o hcl ho hnd gs.length 0 (by omega)

end PEqualNP.Outside.L_meta_583_aux

namespace PEqualNP.Outside.L_meta_583_aux

theorem run_len {α inv meet join y s xs} (h : @Run α inv meet join y s xs) :
    xs.length ≤ s + 1 := by
  induction h with
  | done => simp
  | perm hp _ ih => rwa [←hp.length_eq]
  | one neg save h ih => cases save <;> simp_all [kept] <;> omega
  | two conj ka kb h ih => cases ka <;> cases kb <;> simp_all [kept] <;> omega

abbrev NatRun (m : Nat) := Run (· ^^^ m) (· &&& ·) (· ||| ·)

theorem run_bits {m y s xs} (h : NatRun m y s xs) (i j : Nat)
    (hm : m.testBit i = m.testBit j)
    (hw : ∀ w ∈ xs, w.testBit i = w.testBit j) : y.testBit i = y.testBit j := by
  induction h with
  | done => exact hw _ (by simp)
  | perm hp _ ih => exact ih (fun w h => hw w (hp.mem_iff.1 h))
  | one neg save h ih =>
    apply ih
    have ha := hw _ List.mem_cons_self
    intro w hmem
    cases neg <;> cases save <;> simp only [Bool.false_eq_true, ite_false, ite_true,
      kept, List.mem_cons] at hmem <;>
      first | (rcases hmem with rfl | hr; exact ha; exact hw _ (by simp [hr]))
            | (rcases hmem with rfl | hr; simp [ha,hm]; exact hw _ (by simp [hr]))
  | two conj ka kb h ih =>
    apply ih
    have ha := hw _ List.mem_cons_self
    have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro w hmem
    cases conj <;> cases ka <;> cases kb <;> simp only [Bool.false_eq_true,
      ite_false, ite_true, kept, List.mem_cons] at hmem <;>
      rcases hmem with rfl | hr <;> first | simp [ha,hb] | exact hw _ (by simp only [List.mem_cons]; tauto)

def diff (k w : Nat) : Nat := w ^^^ (w >>> k)

def cov (k : Nat) : List Nat → Nat
  | [] => 0
  | a :: t => diff k a ||| cov k t

theorem cov_bit (k i : Nat) (ws : List Nat) : (cov k ws).testBit i = true ↔
    ∃ a ∈ ws, a.testBit i ≠ a.testBit (k+i) := by
  induction ws with
  | nil => simp [cov]
  | cons a t ih =>
    simp only [cov, Nat.testBit_or, Bool.or_eq_true, ih, diff, Nat.testBit_xor,
      Nat.testBit_shiftRight, List.mem_cons]
    cases hx : a.testBit i <;> cases hy : a.testBit (k+i) <;> simp_all

def lo (k : Nat) := 2^k - 1
def mask (k : Nat) := lo (k+k)
def goal (k : Nat) := lo k <<< k

theorem required {k s ws} (h : NatRun (mask k) (goal k) s ws) :
    (cov k ws &&& lo k) = lo k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  by_cases hi : i < k
  · have hm : (mask k).testBit i = (mask k).testBit (k+i) := by
      simp [mask,lo,Nat.testBit_two_pow_sub_one,show i < k+k by omega,show k+i < k+k by omega]
    have hy : (goal k).testBit i ≠ (goal k).testBit (k+i) := by
      simp [goal,lo,Nat.testBit_shiftLeft,Nat.testBit_two_pow_sub_one,hi,show ¬ k ≤ i by omega]
    have hc : (cov k ws).testBit i = true := by
      apply (cov_bit k i ws).2
      by_contra! hh
      exact hy (run_bits h i (k+i) hm hh)
    simp [hc]
  · simp [lo,Nat.testBit_two_pow_sub_one,hi]

def keep_perm {α : Type} {xs ys : List α} (p : xs.Perm ys) (b : Bool) (a : α) :
    (kept b a xs).Perm (kept b a ys) := by cases b <;> simpa [kept] using p

def tagU (ws : List Nat) (a : Nat) (neg ka : Bool) :=
  4 * ws.idxOf a + 2 * neg.toNat + ka.toNat

def tagB (ws : List Nat) (a b : Nat) (conj ka kb : Bool) :=
  let j := ws.idxOf b
  48 + 8 * (j*(j+1)/2 + ws.idxOf a) + 4 * conj.toNat + 2 * ka.toNat + kb.toNat

def next (m : Nat) (slack : Nat) (ws : List Nat) (f : Nat → List Nat → Bool) : Bool :=
  ws.any fun a =>
    let ra := ws.erase a
    (slack ≥ 1 && ([false,true].any fun neg =>
      let w := if neg then a ^^^ m else a
      f (tagU ws a neg false) (w :: ra) || (slack ≥ 2 && f (tagU ws a neg true) (w :: a :: ra)))) ||
    ra.any fun b =>
      a ≤ b && (let r := ra.erase b
        [false,true].any fun conj =>
          let w := if conj then a &&& b else a ||| b
          f (tagB ws a b conj false false) (w :: r) || (slack ≥ 1 && (f (tagB ws a b conj true false) (w :: a :: r) || f (tagB ws a b conj false true) (w :: b :: r))) ||
            (slack ≥ 2 && f (tagB ws a b conj true true) (w :: a :: b :: r)))

theorem next_one {m y a rest} {neg save : Bool} {s ws} (p : (a :: rest).Perm ws)
    (h : NatRun m y s ((if neg then a ^^^ m else a) :: kept save a rest))
    (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, NatRun m y s ys → f t ys = true) :
    next m (s+2-ws.length) ws f = true := by
  have ha := p.mem_iff.1 List.mem_cons_self
  have pr : rest.Perm (ws.erase a) := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hh := run_len h
  have hl := p.length_eq
  simp only [List.length_cons] at hl hh
  have hsl : 1 ≤ s+2-ws.length := by cases save <;> simp [kept] at hh <;> omega
  apply List.any_eq_true.2 ⟨a,ha,?_⟩
  rw [Bool.or_eq_true]; left
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hsl,?_⟩
  apply List.any_eq_true.2 ⟨neg,by cases neg <;> simp,?_⟩
  have ht (t : Nat) := hf t _ (Run.perm ((keep_perm pr save a).cons _) h)
  cases save with
  | false => simp [kept] at ht; simp [ht]
  | true =>
    simp [kept] at ht hh
    have hsl2 : 2 ≤ s+2-ws.length := by omega
    simp [ht,hsl2]

theorem next_two_sorted {m y a b rest} {conj ka kb : Bool} {s ws} (hab : a ≤ b)
    (p : (a :: b :: rest).Perm ws)
    (h : NatRun m y s
      ((if conj then a &&& b else a ||| b) :: kept ka a (kept kb b rest)))
    (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, NatRun m y s ys → f t ys = true) :
    next m (s+2-ws.length) ws f = true := by
  have ha := p.mem_iff.1 List.mem_cons_self
  have pp := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hb := pp.mem_iff.1 List.mem_cons_self
  have pr := (pp.trans (List.perm_cons_erase hb)).cons_inv
  have hh := run_len h
  have hl := p.length_eq
  simp only [List.length_cons] at hl hh
  apply List.any_eq_true.2 ⟨a,ha,?_⟩
  rw [Bool.or_eq_true]; right
  apply List.any_eq_true.2 ⟨b,hb,?_⟩
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hab,?_⟩
  apply List.any_eq_true.2 ⟨conj,by cases conj <;> simp,?_⟩
  have ht (t : Nat) := hf t _ (Run.perm ((keep_perm (keep_perm pr kb b) ka a).cons _) h)
  cases ka <;> cases kb <;> simp [kept] at ht hh <;>
    simp only [ht, Bool.true_or, Bool.or_true, Bool.and_true, Bool.true_and] <;>
    first | (simp [show 2 ≤ s+2-ws.length by omega]) | (simp [show 1 ≤ s+2-ws.length by omega])

theorem next_two {m y a b rest} {conj ka kb : Bool} {s ws}
    (p : (a :: b :: rest).Perm ws)
    (h : NatRun m y s
      ((if conj then a &&& b else a ||| b) :: kept ka a (kept kb b rest)))
    (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, NatRun m y s ys → f t ys = true) :
    next m (s+2-ws.length) ws f = true := by
  rcases le_total a b with hab | hba
  · exact next_two_sorted hab p h f hf
  · apply next_two_sorted (conj:=conj) (ka:=kb) (kb:=ka) hba ((List.Perm.swap _ _ _).trans p) _ f hf
    have he : (if conj then a &&& b else a ||| b) = (if conj then b &&& a else b ||| a) := by
      cases conj <;> simp [Nat.and_comm, Nat.or_comm]
    rw [he] at h
    apply Run.perm (List.Perm.cons _ ?_) h
    cases ka <;> cases kb <;> simp [kept]
    exact List.Perm.swap _ _ _

theorem zero_done {α inv meet join y t ws} (h : @Run α inv meet join y t ws) :
    t = 0 → ws = [y] := by
  induction h with
  | done => simp
  | perm p h ih => intro ht; rw [ih ht] at p; exact List.perm_singleton.1 p.symm
  | one => simp
  | two => simp

theorem next_complete {m y t ws} (h : NatRun m y t ws) :
    ∀ s, t = s+1 → ∀ zs, ws.Perm zs → ∀ f : Nat → List Nat → Bool,
      (∀ (t : Nat) ys, NatRun m y s ys → f t ys = true) →
      next m (s+2-zs.length) zs f = true := by
  induction h with
  | done => simp
  | perm p h ih => intro s he zs q; exact ih s he zs (p.trans q)
  | one neg save h ih => intro s he zs p f hf; cases he; exact next_one p h f hf
  | two conj ka kb h ih => intro s he zs p f hf; cases he; exact next_two p h f hf

end PEqualNP.Outside.L_meta_583_aux

namespace PEqualNP.Outside.L_meta_583_aux
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

def pt (n : ℕ) (v : ℕ) : Fin n → Bool := fun i => v.testBit i

def encL {n : ℕ} (a : BFn n) : List ℕ → ℕ
  | [] => 0
  | v :: t => Nat.bit (a (pt n v)) (encL a t)

theorem encL_testBit {n : ℕ} (a : BFn n) : ∀ (l : List ℕ) (j : ℕ),
    (encL a l).testBit j = (l.map fun v => a (pt n v)).getD j false
  | [], j => by simp [encL]
  | v :: t, 0 => by simp [encL, Nat.testBit_bit_zero]
  | v :: t, j + 1 => by simp [encL, Nat.testBit_bit_succ, encL_testBit a t j]

theorem encL_inv {n : ℕ} (a : BFn n) (l : List ℕ) :
    encL (invF a) l = encL a l ^^^ (2 ^ l.length - 1) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor, Nat.testBit_two_pow_sub_one, encL_testBit, encL_testBit]
  by_cases h : j < l.length
  · simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    simp [h]

theorem encL_and {n : ℕ} (a b : BFn n) (l : List ℕ) :
    encL (meetF a b) l = encL a l &&& encL b l := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, encL_testBit, encL_testBit, encL_testBit]
  by_cases h : j < l.length
  · simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    rfl

theorem encL_or {n : ℕ} (a b : BFn n) (l : List ℕ) :
    encL (joinF a b) l = encL a l ||| encL b l := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_or, encL_testBit, encL_testBit, encL_testBit]
  by_cases h : j < l.length
  · simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    rfl

end PEqualNP.Outside.L_meta_583_aux

namespace PEqualNP.Outside.L_meta_583_aux

def moveBits (tag d w : Nat) : Nat :=
  ((w &&& tag) <<< d) ||| ((w >>> d) &&& tag)

theorem moved (tag d i w : Nat) (h : (tag &&& (tag <<< d)) = 0) :
    (moveBits tag d w).testBit i =
      (if tag.testBit i then w.testBit (d+i)
       else if (tag <<< d).testBit i then w.testBit (i-d) else false) := by
  have ht := congrArg (fun v : Nat => v.testBit i) h
  simp only [Nat.testBit_and, Nat.zero_testBit] at ht
  simp only [moveBits,Nat.testBit_or,Nat.testBit_shiftLeft,Nat.testBit_and,Nat.testBit_shiftRight] at *
  by_cases hi : d ≤ i <;> simp [hi] at * <;> grind

theorem move_hom (tag d : Nat) (h : (tag &&& (tag <<< d)) = 0) (a b : Nat) :
    moveBits tag d (a &&& b) = (moveBits tag d a &&& moveBits tag d b) ∧
    moveBits tag d (a ||| b) = (moveBits tag d a ||| moveBits tag d b) ∧
    moveBits tag d (a ^^^ b) = (moveBits tag d a ^^^ moveBits tag d b) := by
  refine ⟨?_,?_,?_⟩ <;> apply Nat.eq_of_testBit_eq <;> intro i <;>
    simp only [Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,moved tag d i _ h] <;>
    split_ifs <;> simp

theorem move_run {k s ws} (h : NatRun (mask k) (goal k) s ws) (tag d : Nat)
    (hz : (tag &&& (tag <<< d)) = 0) (hm : moveBits tag d (mask k) = mask k)
    (hy : moveBits tag d (goal k) = goal k) :
    NatRun (mask k) (goal k) s (ws.map (moveBits tag d)) := by
  rw [← hy]
  exact Run.map _ (fun a => (move_hom tag d hz a (mask k)).2.2.trans (by rw [hm]))
    (fun a b => (move_hom tag d hz a b).1) (fun a b => (move_hom tag d hz a b).2.1) h

end PEqualNP.Outside.L_meta_583_aux

namespace PEqualNP.Outside.L_meta_583_aux

theorem bits_le {m y s ws} (h : NatRun m y s ws) (hl : ws.length = s+1) (i j : Nat)
    (hw : ∀ a ∈ ws, a.testBit i ≤ a.testBit j) : y.testBit i ≤ y.testBit j := by
  induction h with
  | done => exact hw _ (by simp)
  | perm hp _ ih =>
    exact ih (hp.length_eq.trans hl) (fun a ha => hw a (hp.mem_iff.1 ha))
  | one neg save h ih =>
    have hh := run_len h
    cases save <;> simp [kept] at hh hl <;> omega
  | two conj ka kb h ih =>
    have hh := run_len h
    cases ka <;> cases kb <;> simp [kept] at hh hl <;> try omega
    apply ih (by simp [kept]; omega)
    have ha := hw _ List.mem_cons_self
    have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro a had
    simp only [kept, Bool.false_eq_true, ite_false, List.mem_cons] at had
    rcases had with rfl | ht
    · cases conj <;> simp only [ite_true, Bool.false_eq_true, ite_false, Nat.testBit_or,Nat.testBit_and] <;>
        first | exact Bool.or_le_or ha hb | exact Bool.and_le_and ha hb | grind
    · exact hw _ (by simp [ht])

def diffUp (k w : Nat) : Nat := (w >>> k) &&& (w ^^^ lo k)

def covUp (k : Nat) : List Nat → Nat
  | [] => 0
  | a :: t => diffUp k a ||| covUp k t

theorem covUp_bit (k i : Nat) (hi : i < k) (ws : List Nat) : (covUp k ws).testBit i = true ↔
    ∃ a ∈ ws, a.testBit i = false ∧ a.testBit (k+i) = true := by
  induction ws with
  | nil => simp [covUp]
  | cons a t ih =>
    simp [covUp, diffUp, lo, hi, ih, and_comm]

theorem required_up {k s ws} (h : NatRun (mask k) (goal k) s ws) (hl : ws.length = s+1) :
    (covUp k ws &&& lo k) = lo k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  by_cases hi : i < k
  · have hy : ¬ (goal k).testBit (k+i) ≤ (goal k).testBit i := by
      simp [goal,lo,Nat.testBit_shiftLeft,Nat.testBit_two_pow_sub_one,hi,show ¬ k ≤ i by omega]
    have hc : (covUp k ws).testBit i = true := by
      apply (covUp_bit k i hi ws).2
      by_contra! hh
      apply hy
      apply bits_le h hl
      intro a ha
      specialize hh a ha
      cases hx : a.testBit i <;> cases hy : a.testBit (k+i) <;> simp_all
    simp [hc]
  · simp [lo,Nat.testBit_two_pow_sub_one,hi]

def covers (k s : Nat) (ws : List Nat) : Bool :=
  if ws.length == s+1 then covUp k ws &&& lo k == lo k else cov k ws &&& lo k == lo k

theorem covers_ok {k s ws} (h : NatRun (mask k) (goal k) s ws) : covers k s ws = true := by
  by_cases he : ws.length = s+1
  · simp [covers,he,required_up h he]
  · simp [covers,he,required h]

end PEqualNP.Outside.L_meta_583_aux

namespace PEqualNP.Outside.L_meta_583_aux

def value6 (a b c d e f : Bool) : Nat :=
  let x := b.toNat+c.toNat
  let y := (!e).toNat+(!f).toNat
  if a then (if d then y else max x (max y (x+y-1))) else (if d then 0 else x)

theorem value6_and : ∀ a b c d e f g h i j l m : Bool,
    value6 (a && g) (b && h) (c && i) (d && j) (e && l) (f && m)
      ≤ value6 a b c d e f + value6 g h i j l m := by decide +kernel

theorem value6_or : ∀ a b c d e f g h i j l m : Bool,
    value6 (a || g) (b || h) (c || i) (d || j) (e || l) (f || m)
      ≤ value6 a b c d e f + value6 g h i j l m := by decide +kernel

theorem score_bound {m y s ws} (h : NatRun m y s ws) (hl : ws.length = s+1)
    (v : Nat → Nat) (hand : ∀ a b, v (a &&& b) ≤ v a + v b)
    (hor : ∀ a b, v (a ||| b) ≤ v a + v b) :
    v y ≤ (ws.map v).sum := by
  induction h with
  | done => simp
  | perm p h ih =>
    rw [← (p.map v).sum_eq]
    exact ih (p.length_eq.trans hl)
  | one neg save h ih =>
    have hh := run_len h
    cases save <;> simp [kept] at hh hl <;> omega
  | two conj ka kb h ih =>
    have hh := run_len h
    cases ka <;> cases kb <;> simp [kept] at hh hl <;> try omega
    have ih' := ih (by simp [kept]; omega)
    cases conj <;> simp [kept] at ih' ⊢ <;> first | grw [← Nat.add_assoc, ← hand]; exact ih' | grw [← Nat.add_assoc, ← hor]; exact ih'

def eval6 (a b c d e f v : Nat) := value6 (v.testBit a) (v.testBit b) (v.testBit c)
    (v.testBit d) (v.testBit e) (v.testBit f)

theorem eval6_bound {m y s ws} (h : NatRun m y s ws) (hl : ws.length = s+1)
    (a b c d e f : Nat) : eval6 a b c d e f y ≤ (ws.map (eval6 a b c d e f)).sum := by
  apply score_bound h hl
  · intro v w
    simpa only [eval6,Nat.testBit_and] using value6_and
      (v.testBit a) (v.testBit b) (v.testBit c) (v.testBit d) (v.testBit e) (v.testBit f)
      (w.testBit a) (w.testBit b) (w.testBit c) (w.testBit d) (w.testBit e) (w.testBit f)
  · intro v w
    simpa only [eval6,Nat.testBit_or] using value6_or
      (v.testBit a) (v.testBit b) (v.testBit c) (v.testBit d) (v.testBit e) (v.testBit f)
      (w.testBit a) (w.testBit b) (w.testBit c) (w.testBit d) (w.testBit e) (w.testBit f)

def scoreCheck (k s : Nat) (ws : List Nat) (code : Nat) : Bool :=
  if code = 0 then false else
    let a := code &&& 1023
    let b := (code >>> 10) &&& 1023
    let c := (code >>> 20) &&& 1023
    let d := (code >>> 30) &&& 1023
    let e := (code >>> 40) &&& 1023
    let f := (code >>> 50) &&& 1023
    ws.length == s+1 && (ws.map (eval6 a b c d e f)).sum < eval6 a b c d e f (goal k)

theorem scoreCheck_no {m k s ws} (h : NatRun m (goal k) s ws) (code : Nat) :
    scoreCheck k s ws code = false := by
  unfold scoreCheck
  split
  · rfl
  · dsimp only
    by_cases hl : ws.length = s+1
    · simp [hl,Nat.not_lt_of_ge (eval6_bound h hl _ _ _ _ _ _)]
    · simp [hl]

end PEqualNP.Outside.L_meta_583_aux

namespace PEqualNP.Outside.L_meta_583_aux

def span (f : Nat → Bool) : Nat → Nat → Bool
  | 0, _ => true
  | n+1, i => f i && span f n (i+1)

theorem span_ok {f n o} (h : span f n o = true) : ∀ i, o ≤ i → i < o+n → f i = true := by
  induction n generalizing o with
  | zero => omega
  | succ n ih =>
    simp only [span, Bool.and_eq_true] at h
    intro i hi hj
    rcases Nat.eq_or_lt_of_le hi with rfl | hi
    · exact h.1
    · exact ih h.2 i (by omega) (by omega)

theorem span_join {f a o b} (ha : span f a o = true) (hb : span f b (o+a) = true) :
    span f (a+b) o = true := by
  induction a generalizing o with
  | zero => simpa using hb
  | succ a ih =>
    simp only [span, Bool.and_eq_true] at ha
    rw [Nat.succ_add, span, Bool.and_eq_true]
    exact ⟨ha.1, ih ha.2 (by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hb)⟩

theorem extend_run {α inv meet join y s t a r} (h : @Run α inv meet join y s (a::r))
    (hle : s ≤ t) : Run inv meet join y t (a::r) := by
  induction t, hle using Nat.le_induction with
  | base => exact h
  | succ t hle ih => exact Run.one false false ih

end PEqualNP.Outside.L_meta_583_aux

namespace PEqualNP.Outside.L_meta_583_aux
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

def MOk (g : Gate) : Prop := Ok g ∧ g.op ≠ GateOp.not

def HasMono (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
  ∃ C : Circuit, (∀ g ∈ C.gates, MOk g) ∧ C.size ≤ s ∧
    ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x

theorem simplify_op (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, g.op = op := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; rfl)
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; rfl)
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; rfl)
  · simp at hg
  · simp at hg

theorem elim_mono (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, g.op ≠ GateOp.not) → (∀ g ∈ acc.2, g.op ≠ GateOp.not) →
      ∀ g ∈ (elim n gs acc).2, g.op ≠ GateOp.not := by
  induction gs with
  | nil => intro acc _ h; exact h
  | cons g gs ih =>
    intro acc hg h
    apply ih (elimStep n acc g) (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg'))
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · rw [simplify_op _ _ _ g' (by simpa using h1)]
      exact hg g List.mem_cons_self

theorem clean_of_mono (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ)
    (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (h : HasMono n f s) :
    ∃ (gs : List Gate) (o : ℕ), CleanL n gs ∧ (∀ g ∈ gs, g.op ≠ GateOp.not) ∧ gs.length ≤ s ∧
      ∀ x : Fin n → Bool, (wiresFrom gs (List.ofFn x)).getD o false = f x := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  have hok : ∀ g ∈ C.gates, Ok g := fun g hg => (ok g hg).1
  have hmo : ∀ g ∈ C.gates, g.op ≠ GateOp.not := fun g hg => (ok g hg).2
  have hmo' := elim_mono n C.gates (idStats n, []) hmo (by simp)
  set acc := elim n C.gates (idStats n, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom C.gates (List.ofFn y)) acc :=
    fun y => inv_elim n _ (by simp) C.gates _ _ hok (inv_id n y)
  have hval : ∀ y : Fin n → Bool,
      (acc.1.getD C.output (Stat.const false)).val (wiresFrom acc.2 (List.ofFn y)) = f y := by
    intro y
    rw [((hinv y).2 C.output).2, ← hev y]; rfl
  cases hst : acc.1.getD C.output (Stat.const false) with
  | const c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | wire j =>
    refine ⟨acc.2, j, ?_, hmo', ?_, ?_⟩
    · exact clean_elim n (List.ofFn fun _ : Fin n => false) (by simp) C.gates _ _ hok
        (inv_id n _) (by intro p g hp; simp at hp)
    · have := elim_len n C.gates (idStats n, [])
      rw [← hacc] at this
      simp only [List.length_nil, zero_add] at this
      omega
    · intro y
      have := hval y
      rw [hst] at this
      exact this

theorem del_gate_mono (n : ℕ) (pre : List Gate) (g : Gate) (post : List Gate) (o : ℕ) (f : BFn n)
    (hok : ∀ g' ∈ pre ++ g :: post, MOk g')
    (hno : ∀ g' ∈ post, n + pre.length ∉ g'.inputs) (ho : o ≠ n + pre.length)
    (hev : ∀ x, val (pre ++ g :: post) n o x = f x) :
    HasMono n f (pre.length + post.length) := by
  refine ⟨⟨pre ++ post.map (shGate (n + pre.length)), shift (n + pre.length) o⟩, ?_, ?_, ?_⟩
  · intro g' hg'
    rcases List.mem_append.1 hg' with h | h
    · exact hok g' (List.mem_append_left _ h)
    · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 h
      have := hok g0 (List.mem_append_right _ (List.mem_cons_of_mem _ hg0))
      exact ⟨⟨this.1.1, by simpa [shGate] using this.1.2⟩, this.2⟩
  · simp [Circuit.size]
  · intro x
    rw [← hev x]
    show (wiresFrom (pre ++ post.map (shGate (n + pre.length))) (List.ofFn x)).getD
      (shift (n + pre.length) o) false = _
    unfold val
    have h1 : wiresFrom (pre ++ g :: post) (List.ofFn x) = wiresFrom post
        (wiresFrom pre (List.ofFn x) ++
          [g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn x)).getD i false)]) := by
      rw [wiresFrom_append]; rfl
    have hl : (wiresFrom pre (List.ofFn x)).length = n + pre.length := by
      rw [length_wiresFrom]; simp
    rw [h1, wiresFrom_append]
    refine (relD_wires (n + pre.length) post _ _ hno ⟨by simp, by omega, ?_⟩).2.2 o ho
    intro a ha
    by_cases hlt : a < n + pre.length
    · have : shift (n + pre.length) a = a := by simp [shift, hlt]
      rw [this, List.getD_append _ _ _ _ (by omega)]
    · have : shift (n + pre.length) a = a - 1 := by simp [shift, hlt]
      rw [this, List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by simp; omega)]

open Classical in
theorem run_live_mono (n : ℕ) (inv : BFn n → BFn n) (gs : List Gate) (o : ℕ) (hcl : CleanL n gs)
    (hm : ∀ (q : ℕ) (g : Gate), gs[q]? = some g → g.op ≠ GateOp.not) (ho : o < n + gs.length)
    (hnd : ∀ p, p < gs.length → n + p = o ∨ ∃ (q : ℕ) (g : Gate), gs[q]? = some g ∧ n + p ∈ g.inputs) :
    ∀ d p, p + d = gs.length →
      Run inv meetF joinF (val gs n o) d ((liveList gs n o p).map (val gs n)) := by
  intro d
  induction d with
  | zero =>
    intro p hp
    have hperm : [o].Perm (liveList gs n o p) := by
      refine (List.perm_ext_iff_of_nodup (List.nodup_singleton o) (nodup_liveList _ _ _ _)).2 ?_
      intro a
      rw [mem_liveList, List.mem_singleton]
      constructor
      · rintro rfl; exact ⟨by omega, Or.inl rfl⟩
      · rintro ⟨_, h | ⟨q, hq, g', hg', _⟩⟩
        · exact h
        · have := (List.getElem?_eq_some_iff.1 hg').1
          omega
    exact Run.perm (hperm.map (val gs n)) Run.done
  | succ d ih =>
    intro p hp
    have hplt : p < gs.length := by omega
    obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hplt⟩
    have IH := ih (p + 1) (by omega)
    have hstep := live_succ n gs o hcl hnd p g hg
    have hin : ∀ a ∈ g.inputs, a ∈ liveList gs n o p := fun a ha =>
      (mem_liveList _ _ _ _ _).2 ⟨(hcl p g hg).lt a ha, Or.inr ⟨p, le_rfl, g, hg, ha⟩⟩
    have hnew : ∀ a ∈ liveList gs n o p, a ≠ n + p := fun a ha =>
      Nat.ne_of_lt ((mem_liveList _ _ _ _ _).1 ha).1
    have hvg := val_gate n gs p g hg (hcl p g hg).lt
    have hnd0 := nodup_liveList gs n o p
    
    have single : ∀ (j : ℕ) (neg : Bool), (∀ a, a ∈ g.inputs ↔ a = j) →
        val gs n (n + p) = (if neg then inv (val gs n j) else val gs n j) →
        Run inv meetF joinF (val gs n o) (d + 1)
          ((liveList gs n o p).map (val gs n)) := by
      intro j neg hmem hval
      have hj := hin j ((hmem j).2 rfl)
      have hp1 : (liveList gs n o p).Perm (j :: (liveList gs n o p).erase j) :=
        List.perm_cons_erase hj
      have hnr : ((liveList gs n o p).erase j).Nodup := hnd0.erase j
      have hp2 : (liveList gs n o (p + 1)).Perm
          ((n + p) :: kept (decide (Live gs o (p + 1) j)) j ((liveList gs n o p).erase j)) := by
        refine (List.perm_ext_iff_of_nodup (nodup_liveList _ _ _ _) ?_).2 ?_
        · refine List.nodup_cons.2 ⟨?_, nodup_kept _ _ _ hnr (by simp [hnd0.mem_erase_iff])⟩
          rw [mem_kept]
          rintro (⟨_, h⟩ | h)
          · exact hnew j hj h.symm
          · exact hnew _ (List.mem_of_mem_erase h) rfl
        · intro a
          rw [hstep a, List.mem_cons, mem_kept, hnd0.mem_erase_iff, hmem a]
          simp only [decide_eq_true_eq]
          constructor
          · rintro (h | ⟨h1, h2⟩)
            · exact Or.inl h
            · by_cases haj : a = j
              · exact Or.inr (Or.inl ⟨haj ▸ h2 haj, haj⟩)
              · exact Or.inr (Or.inr ⟨haj, h1⟩)
          · rintro (h | ⟨h1, rfl⟩ | ⟨h1, h2⟩)
            · exact Or.inl h
            · exact Or.inr ⟨hj, fun _ => h1⟩
            · exact Or.inr ⟨h2, fun h => absurd h h1⟩
      have IH' := Run.perm (hp2.map (val gs n)) IH
      rw [List.map_cons, kept_map, hval] at IH'
      exact Run.perm (hp1.map (val gs n)).symm (Run.one neg _ IH')
    rcases hcl p g hg with ⟨hop, j, hj, hinp⟩ | ⟨hop, j, k, hj, hk, hinp⟩
    · exact absurd hop (hm p g hg)
    · by_cases hjk : j = k
      · subst hjk
        apply single j false
        · intro a; simp [hinp]
        · funext x
          rw [hvg x, hinp]
          rcases hop with hop | hop <;> rw [hop] <;> simp [GateOp.eval]
      · have hjm := hin j (by simp [hinp])
        have hkm := hin k (by simp [hinp])
        have hke : k ∈ (liveList gs n o p).erase j :=
          (hnd0.mem_erase_iff).2 ⟨fun e => hjk e.symm, hkm⟩
        have hnr : ((liveList gs n o p).erase j).Nodup := hnd0.erase j
        have hnr2 : (((liveList gs n o p).erase j).erase k).Nodup := hnr.erase k
        have hp1 : (liveList gs n o p).Perm
            (j :: k :: ((liveList gs n o p).erase j).erase k) :=
          (List.perm_cons_erase hjm).trans ((List.perm_cons_erase hke).cons j)
        have hmr : ∀ a, a ∈ ((liveList gs n o p).erase j).erase k ↔
            a ≠ k ∧ a ≠ j ∧ a ∈ liveList gs n o p := by
          intro a
          rw [hnr.mem_erase_iff, hnd0.mem_erase_iff]
        have hp2 : (liveList gs n o (p + 1)).Perm
            ((n + p) :: kept (decide (Live gs o (p + 1) j)) j
              (kept (decide (Live gs o (p + 1) k)) k
                (((liveList gs n o p).erase j).erase k))) := by
          refine (List.perm_ext_iff_of_nodup (nodup_liveList _ _ _ _) ?_).2 ?_
          · refine List.nodup_cons.2 ⟨?_, nodup_kept _ _ _ (nodup_kept _ _ _ hnr2 ?_) ?_⟩
            · rw [mem_kept, mem_kept]
              rintro (⟨_, h⟩ | ⟨_, h⟩ | h)
              · exact hnew j hjm h.symm
              · exact hnew k hkm h.symm
              · exact hnew _ ((hmr _).1 h).2.2 rfl
            · rw [hmr]; simp
            · rw [mem_kept, hmr]
              rintro (⟨_, h⟩ | h)
              · exact hjk h
              · exact h.2.1 rfl
          · intro a
            rw [hstep a, List.mem_cons, mem_kept, mem_kept, hmr a]
            simp only [decide_eq_true_eq, hinp, List.mem_cons, List.not_mem_nil, or_false]
            constructor
            · rintro (h | ⟨h1, h2⟩)
              · exact Or.inl h
              · by_cases haj : a = j
                · exact Or.inr (Or.inl ⟨haj ▸ h2 (Or.inl haj), haj⟩)
                · by_cases hak : a = k
                  · exact Or.inr (Or.inr (Or.inl ⟨hak ▸ h2 (Or.inr hak), hak⟩))
                  · exact Or.inr (Or.inr (Or.inr ⟨hak, haj, h1⟩))
            · rintro (h | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, h2, h3⟩)
              · exact Or.inl h
              · exact Or.inr ⟨hjm, fun _ => h1⟩
              · exact Or.inr ⟨hkm, fun _ => h1⟩
              · exact Or.inr ⟨h3, fun h => by rcases h with h | h <;> contradiction⟩
        have IH' := Run.perm (hp2.map (val gs n)) IH
        have hval : val gs n (n + p) = (if decide (g.op = GateOp.and)
            then meetF (val gs n j) (val gs n k) else joinF (val gs n j) (val gs n k)) := by
          funext x
          rw [hvg x, hinp]
          rcases hop with hop | hop <;> rw [hop] <;> simp [GateOp.eval]
        rw [List.map_cons, kept_map, kept_map, hval] at IH'
        exact Run.perm (hp1.map (val gs n)).symm (Run.two _ _ _ IH')

theorem exists_run_mono {n : ℕ} (inv : BFn n → BFn n) (f : BFn n)
    (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (s : ℕ) (h : HasMono n f s) :
    ∃ s', s' ≤ s ∧ ∃ ws : List (BFn n),
      ws.Sublist (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i)) ∧
      Run inv meetF joinF f s' ws := by
  classical
  let P : ℕ → Prop := fun t => ∃ (gs : List Gate) (o : ℕ), CleanL n gs ∧
    (∀ g ∈ gs, g.op ≠ GateOp.not) ∧ gs.length = t ∧ ∀ x, val gs n o x = f x
  have hP : ∀ t, HasMono n f t → ∃ t', t' ≤ t ∧ P t' := by
    intro t ht
    obtain ⟨gs, o, hcl, hmo, hsz, hev⟩ := clean_of_mono n f t hnc ht
    exact ⟨gs.length, hsz, gs, o, hcl, hmo, rfl, hev⟩
  obtain ⟨t0, ht0, hPt0⟩ := hP s h
  have hex : ∃ t, P t := ⟨t0, hPt0⟩
  have hmin : Nat.find hex ≤ t0 := Nat.find_min' hex hPt0
  obtain ⟨gs, o, hcl, hmo, hlen, hev⟩ := Nat.find_spec hex
  have hok : ∀ g ∈ gs, MOk g := fun g hg => ⟨(clean_nok _ gs hcl g hg).1, hmo g hg⟩
  have ho : o < n + gs.length := by
    by_contra hge
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hev y, ← hev y']
    unfold val
    rw [List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp; omega),
      List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp; omega)]
  have hnd : ∀ p, p < gs.length → n + p = o ∨
      ∃ (q : ℕ) (g : Gate), gs[q]? = some g ∧ n + p ∈ g.inputs := by
    intro p hp
    by_contra hcon
    push_neg at hcon
    obtain ⟨hpo, hno⟩ := hcon
    obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hp⟩
    obtain ⟨pre, post, rfl, hpl⟩ := split_at gs p g hg
    have hsz := del_gate_mono n pre g post o f hok (by
      intro g' hg'
      obtain ⟨q, hq⟩ := List.mem_iff_getElem?.1 hg'
      have := hno (pre.length + 1 + q) g' (by
        rw [List.getElem?_append_right (by omega)]
        have e : pre.length + 1 + q - pre.length = q + 1 := by omega
        rw [e]; simpa using hq)
      rw [hpl]; exact this) (by rw [hpl]; exact fun e => hpo e.symm) hev
    obtain ⟨t', ht', hPt'⟩ := hP _ hsz
    have := Nat.find_min' hex hPt'
    simp at hlen
    omega
  refine ⟨gs.length, by omega, (liveList gs n o 0).map (val gs n), ?_, ?_⟩
  · have e : (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i))
        = (List.range n).map (val gs n) := by
      apply List.ext_getElem
      · simp
      · intro i h1 h2
        simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range]
        exact (val_input gs n ⟨i, by simpa using h1⟩).symm
    rw [e]
    exact (List.filter_sublist).map _
  · have hf : val gs n o = f := funext hev
    rw [← hf]
    exact run_live_mono n inv gs o hcl (fun q g hq => hmo g (List.mem_iff_getElem?.2 ⟨q, hq⟩))
      ho hnd gs.length 0 (by omega)

theorem bits_le0 {y s ws} (h : NatRun 0 y s ws) (i j : Nat)
    (hw : ∀ a ∈ ws, a.testBit i ≤ a.testBit j) : y.testBit i ≤ y.testBit j := by
  induction h with
  | done => exact hw _ (by simp)
  | perm hp _ ih => exact ih (fun a ha => hw a (hp.mem_iff.1 ha))
  | one neg save h ih =>
    apply ih
    intro w hmem
    apply hw
    cases neg <;> cases save <;>
      simp only [kept, Bool.false_eq_true, ite_false, ite_true, List.mem_cons, Nat.xor_zero] at hmem ⊢ <;>
      tauto
  | two conj ka kb h ih =>
    apply ih
    have ha := hw _ List.mem_cons_self
    have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro w hmem
    rcases List.mem_cons.1 hmem with rfl | hr
    · cases conj <;> simp only [ite_true, Bool.false_eq_true, ite_false, Nat.testBit_or,
        Nat.testBit_and] <;> grind
    · apply hw
      cases ka <;> cases kb <;>
        simp only [kept, Bool.false_eq_true, ite_false, ite_true, List.mem_cons] at hr ⊢ <;> tauto

theorem required_up0 {k s ws} (h : NatRun 0 (goal k) s ws) : (covUp k ws &&& lo k) = lo k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  by_cases hi : i < k
  · have hy : ¬ (goal k).testBit (k+i) ≤ (goal k).testBit i := by
      simp [goal,lo,Nat.testBit_shiftLeft,Nat.testBit_two_pow_sub_one,hi,show ¬ k ≤ i by omega]
    have hc : (covUp k ws).testBit i = true := by
      apply (covUp_bit k i hi ws).2
      by_contra! hh
      apply hy
      apply bits_le0 h
      intro a ha
      specialize hh a ha
      cases hx : a.testBit i <;> cases hy : a.testBit (k+i) <;> simp_all
    simp [hc]
  · simp [lo,Nat.testBit_two_pow_sub_one,hi]

def coversM (k : Nat) (ws : List Nat) : Bool := covUp k ws &&& lo k == lo k

theorem coversM_ok {k s ws} (h : NatRun 0 (goal k) s ws) : coversM k ws = true := by
  simp [coversM, required_up0 h]

theorem next_mono {m a b : Nat} {ws : List Nat} {f : Nat → List Nat → Bool} (hab : a ≤ b)
    (h : next m a ws f = true) : next m b ws f = true := by
  unfold next at h ⊢
  rw [List.any_eq_true] at h ⊢
  obtain ⟨x, hx, hh⟩ := h
  refine ⟨x, hx, ?_⟩
  have h1 : 1 ≤ a → 1 ≤ b := fun h => le_trans h hab
  have h2 : 2 ≤ a → 2 ≤ b := fun h => le_trans h hab
  simp only [Bool.or_eq_true, Bool.and_eq_true, List.any_eq_true, decide_eq_true_eq,
    ge_iff_le] at hh ⊢
  rcases hh with ⟨hs, neg, hneg, hP⟩ | ⟨y, hy, hxy, conj, hc, hQ⟩
  · left
    refine ⟨h1 hs, neg, hneg, ?_⟩
    rcases hP with hP | ⟨hs2, hP⟩
    · exact Or.inl hP
    · exact Or.inr ⟨h2 hs2, hP⟩
  · right
    refine ⟨y, hy, hxy, conj, hc, ?_⟩
    rcases hQ with (hQ | ⟨hs1, hQ⟩) | ⟨hs2, hQ⟩
    · exact Or.inl (Or.inl hQ)
    · exact Or.inl (Or.inr ⟨h1 hs1, hQ⟩)
    · exact Or.inr ⟨h2 hs2, hQ⟩

end PEqualNP.Outside.L_meta_583_aux


namespace PEqualNP.Outside.L_meta_583_aux

def fld (T w i : Nat) : Nat := (T >>> (w * i)) &&& (2 ^ w - 1)

def bsr (T w h : Nat) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | f + 1, lo, hi =>
    if lo + 1 < hi then
      (if fld T w ((lo + hi) / 2) ≤ h then bsr T w h f ((lo + hi) / 2) hi
       else bsr T w h f lo ((lo + hi) / 2))
    else lo

def hw (w : Nat) : Nat := (w % 11400714819323198549 + 317) ^ 3 % 11400714819323198549 + 1

def hz : List Nat → Nat
  | [] => 0
  | w :: t => hw w + hz t

def hk (zs : List Nat) : Nat := hz zs % 4294967291

def found (S : Nat → Nat → List Nat) (N : Nat → Nat) (idx : Nat → List Nat → Nat)
    (s : Nat) (zs : List Nat) : Bool :=
  decide (idx s zs < N s) && zs.isPerm (S s (idx s zs))

def scr (k s : Nat) (pool : List Nat) (zs : List Nat) : Bool :=
  zs.length == s + 1 && pool.any (scoreCheck k s zs)

theorem scr_no {k s : Nat} (pool : List Nat) {zs : List Nat}
    (h : NatRun (mask k) (goal k) s zs) : scr k s pool zs = false := by
  unfold scr
  rw [Bool.and_eq_false_iff]
  right
  rw [List.any_eq_false]
  intro x _
  rw [scoreCheck_no h x]
  simp

def bar (k : Nat) (S : Nat → Nat → List Nat) (N : Nat → Nat) (idx : Nat → List Nat → Nat)
    (ori : List Nat → List Nat) (pool : List Nat) : Nat → Nat → Bool
  | 0, i => !(S 0 i == [goal k])
  | s + 1, i =>
    let ws := S (s + 1) i
    !(next (mask k) (s + 2 - ws.length) ws fun _ zs =>
        covers k s zs && !(scr k s pool zs) && !(found S N idx s (ori zs)))

theorem bar_sound {k S N idx ori pool} {s i : Nat} (hb : bar k S N idx ori pool s i = true)
    (hr : ∀ {u ys}, NatRun (mask k) (goal k) u ys → NatRun (mask k) (goal k) u (ori ys))
    (h : NatRun (mask k) (goal k) s (S s i)) :
    ∃ q < s, ∃ j < N q, NatRun (mask k) (goal k) q (S q j) := by
  cases s with
  | zero => simp [bar, zero_done h rfl] at hb
  | succ s =>
    by_contra! hn
    let F (_ : Nat) (zs : List Nat) :=
      covers k s zs && !(scr k s pool zs) && !(found S N idx s (ori zs))
    have hF (tag : Nat) (zs) (hz : NatRun (mask k) (goal k) s zs) : F tag zs = true := by
      simp only [F, covers_ok hz, scr_no pool hz, Bool.not_false, Bool.true_and, found]
      simp only [Bool.not_eq_true', Bool.and_eq_false_imp, decide_eq_true_eq]
      intro hj
      by_contra! hp
      have p := List.isPerm_iff.1 (Bool.eq_true_of_not_eq_false hp)
      exact hn s (by omega) _ hj (Run.perm p (hr hz))
    have hN := next_complete h s rfl _ (List.Perm.refl _) F hF
    change !(next _ _ _ F) = true at hb
    rw [hN] at hb
    contradiction

theorem bar_all {k S N idx ori pool} {cap : Nat}
    (hr : ∀ {u ys}, NatRun (mask k) (goal k) u ys → NatRun (mask k) (goal k) u (ori ys))
    (hc : ∀ s ≤ cap, ∀ i < N s, bar k S N idx ori pool s i = true) :
    ∀ s ≤ cap, ∀ i < N s, ¬ NatRun (mask k) (goal k) s (S s i) := by
  intro s
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro hs i hi hh
    obtain ⟨q, hq, j, hj, h⟩ := bar_sound (hc s hs i hi) hr hh
    exact ih q hq (by omega) j hj h

def mv (m c : Nat) (ws : List Nat) : List Nat :=
  let a := ws.getD (c % 16) 0
  let b := ws.getD (c / 16 % 16) 0
  let op := c / 256 % 4
  let r := if op < 2 then ws.erase a else (ws.erase a).erase b
  (if op = 0 then a else if op = 1 then a ^^^ m else if op = 2 then a &&& b else a ||| b) ::
    kept (decide (c / 1024 % 2 = 1)) a (kept (decide (2 ≤ op ∧ c / 2048 % 2 = 1)) b r)

end PEqualNP.Outside.L_meta_583_aux


namespace PEqualNP.Outside.L_meta_583_aux

theorem scr_no0 {k s : Nat} (pool : List Nat) {zs : List Nat}
    (h : NatRun 0 (goal k) s zs) : scr k s pool zs = false := by
  unfold scr
  rw [Bool.and_eq_false_iff]
  right
  rw [List.any_eq_false]
  intro x _
  rw [scoreCheck_no h x]
  simp

def barM (k : Nat) (S : Nat → Nat → List Nat) (N : Nat → Nat) (idx : Nat → List Nat → Nat)
    (ori : List Nat → List Nat) (pool : List Nat) : Nat → Nat → Bool
  | 0, i => !(S 0 i == [goal k])
  | s + 1, i =>
    let ws := S (s + 1) i
    !(ws == [goal k]) && !(next 0 (s + 2 - ws.length) ws fun _ zs =>
        coversM k zs && !(scr k s pool zs) && !(zs.length == ws.length && zs.isPerm ws) &&
          !(found S N idx s (ori zs)))

theorem barM_all {k S N idx ori pool} {cap : Nat}
    (hr : ∀ {u ys}, NatRun 0 (goal k) u ys → NatRun 0 (goal k) u (ori ys))
    (hc : ∀ L ≤ cap, ∀ i < N L, barM k S N idx ori pool L i = true) :
    ∀ q L, q ≤ L → L ≤ cap → ∀ i < N L, ¬ NatRun 0 (goal k) q (S L i) := by
  intro q
  induction q using Nat.strong_induction_on with
  | ind q ih =>
    intro L hqL hL i hi h
    have hb := hc L hL i hi
    cases q with
    | zero =>
      have e := zero_done h rfl
      cases L with
      | zero => simp [barM, e] at hb
      | succ s => simp [barM, e] at hb
    | succ t =>
      cases L with
      | zero => omega
      | succ s =>
        let F (_ : Nat) (zs : List Nat) := coversM k zs && !(scr k s pool zs) &&
          !(zs.length == (S (s + 1) i).length && zs.isPerm (S (s + 1) i)) &&
          !(found S N idx s (ori zs))
        have hF (tag : Nat) (zs) (hz : NatRun 0 (goal k) t zs) : F tag zs = true := by
          have h1 : (zs.length == (S (s + 1) i).length && zs.isPerm (S (s + 1) i)) = false := by
            cases hp : zs.isPerm (S (s + 1) i) with
            | false => simp
            | true =>
              exfalso
              exact ih t (by omega) (s + 1) (by omega) hL i hi (Run.perm (List.isPerm_iff.1 hp) hz)
          have h2 : scr k s pool zs = false := by
            by_cases hts : t = s
            · subst hts; exact scr_no0 pool hz
            · have hl := run_len hz
              unfold scr
              have e : (zs.length == s + 1) = false := by
                rw [beq_eq_false_iff_ne]; omega
              rw [e]; rfl
          have h3 : found S N idx s (ori zs) = false := by
            cases hf : found S N idx s (ori zs) with
            | false => rfl
            | true =>
              exfalso
              simp only [found, Bool.and_eq_true, decide_eq_true_eq] at hf
              obtain ⟨hj, hp⟩ := hf
              exact ih t (by omega) s (by omega) (by omega) _ hj
                (Run.perm (List.isPerm_iff.1 hp) (hr hz))
          simp only [F, coversM_ok hz, h1, h2, h3, Bool.not_false, Bool.and_self]
        have hN := next_complete h t rfl _ (List.Perm.refl _) F hF
        have hN' := next_mono (show t + 2 - (S (s + 1) i).length ≤ s + 2 - (S (s + 1) i).length by
          omega) hN
        have hb2 : (!(next 0 (s + 2 - (S (s + 1) i).length) (S (s + 1) i) F)) = true :=
          (Bool.and_eq_true_iff.mp hb).2
        rw [hN'] at hb2
        contradiction

end PEqualNP.Outside.L_meta_583_aux


namespace PEqualNP.Outside.L_meta_583_aux

def dsw (K T d w : Nat) : Nat := (w &&& K) ||| moveBits T d w

theorem dsw_bit (K T d w i : Nat) (h : (T &&& (T <<< d)) = 0)
    (hK : (K &&& (T ||| (T <<< d))) = 0) :
    (dsw K T d w).testBit i = if K.testBit i then w.testBit i else (moveBits T d w).testBit i := by
  have hk := congrArg (fun v : Nat => v.testBit i) hK
  simp only [Nat.testBit_and, Nat.testBit_or, Nat.zero_testBit] at hk
  unfold dsw
  rw [Nat.testBit_or, Nat.testBit_and, moved T d i w h]
  cases hKi : K.testBit i with
  | false => simp
  | true =>
    rw [hKi] at hk
    cases h1 : T.testBit i <;> cases h2 : (T <<< d).testBit i <;> simp_all

theorem dsw_hom (K T d : Nat) (h : (T &&& (T <<< d)) = 0)
    (hK : (K &&& (T ||| (T <<< d))) = 0) (a b : Nat) :
    dsw K T d (a &&& b) = (dsw K T d a &&& dsw K T d b) ∧
    dsw K T d (a ||| b) = (dsw K T d a ||| dsw K T d b) := by
  refine ⟨?_, ?_⟩ <;> apply Nat.eq_of_testBit_eq <;> intro i <;>
    simp only [Nat.testBit_and, Nat.testBit_or, dsw_bit K T d _ i h hK, moved T d i _ h] <;>
    split_ifs <;> simp

theorem dsw_run {K T d y s ws} (h : NatRun 0 y s ws) (hz : (T &&& (T <<< d)) = 0)
    (hK : (K &&& (T ||| (T <<< d))) = 0) (hy : dsw K T d y = y) :
    NatRun 0 y s (ws.map (dsw K T d)) := by
  have h2 := Run.map (dsw K T d) (inv' := fun v : Nat => v ^^^ 0)
    (meet' := fun a b : Nat => a &&& b) (join' := fun a b : Nat => a ||| b) (fun a => by simp)
    (fun a b => (dsw_hom K T d hz hK a b).1) (fun a b => (dsw_hom K T d hz hK a b).2) h
  rw [hy] at h2
  exact h2

def okT (k : Nat) (t : Nat × Nat × Nat) : Bool :=
  (t.2.1 &&& (t.2.1 <<< t.2.2) == 0) && (t.1 &&& (t.2.1 ||| (t.2.1 <<< t.2.2)) == 0) &&
    (dsw t.1 t.2.1 t.2.2 (goal k) == goal k)

def appL : List (Nat × Nat × Nat) → List Nat → List Nat
  | [], ws => ws
  | t :: ts, ws => appL ts (ws.map (dsw t.1 t.2.1 t.2.2))

theorem appL_run {k : Nat} : ∀ (ts : List (Nat × Nat × Nat)) {s : Nat} {ws : List Nat},
    ts.all (okT k) = true → NatRun 0 (goal k) s ws → NatRun 0 (goal k) s (appL ts ws)
  | [], _, _, _, h => h
  | t :: ts, s, ws, hall, h => by
    simp only [List.all_cons, Bool.and_eq_true] at hall
    obtain ⟨ht, hts⟩ := hall
    simp only [okT, Bool.and_eq_true, beq_iff_eq] at ht
    obtain ⟨⟨h1, h2⟩, h3⟩ := ht
    exact appL_run ts hts (dsw_run h h1 h2 h3)

theorem getD_all {L : List (List (Nat × Nat × Nat))} {p : Nat × Nat × Nat → Bool}
    (h : L.all (fun l => l.all p) = true) (i : Nat) : (L.getD i []).all p = true := by
  rw [List.getD_eq_getElem?_getD]
  cases hi : L[i]? with
  | none => rfl
  | some l =>
    rw [List.all_eq_true] at h
    exact h l (List.mem_iff_getElem?.2 ⟨i, hi⟩)

def amin (F : Nat → Nat) : Nat → Nat → Nat → Nat
  | 0, b, _ => b
  | n + 1, b, i => if F i < F b then amin F n i (i + 1) else amin F n b (i + 1)

end PEqualNP.Outside.L_meta_583_aux


namespace PEqualNP.Outside.L_meta_583_aux
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

def rowsG : List ℕ := [15, 28, 42, 137, 184, 515, 610, 897, 1008, 15, 28, 70, 261, 340, 515, 610, 897, 1008, 15, 42, 28, 137, 184, 261, 340, 897, 1008, 15, 42, 70, 515, 610, 261, 340, 897, 1008, 15, 70, 28, 261, 340, 137, 184, 897, 1008, 15, 70, 42, 515, 610, 137, 184, 897, 1008, 15, 28, 137, 42, 184, 515, 897, 610, 1008, 15, 28, 261, 70, 340, 515, 897, 610, 1008, 15, 137, 28, 42, 184, 70, 340, 610, 1008, 15, 137, 261, 515, 897, 70, 340, 610, 1008, 15, 261, 28, 70, 340, 42, 184, 610, 1008, 15, 261, 137, 515, 897, 42, 184, 610, 1008, 15, 42, 137, 28, 184, 261, 897, 340, 1008, 15, 42, 515, 70, 610, 261, 897, 340, 1008, 15, 137, 42, 28, 184, 70, 610, 340, 1008, 15, 137, 515, 261, 897, 70, 610, 340, 1008, 15, 515, 42, 70, 610, 28, 184, 340, 1008, 15, 515, 137, 261, 897, 28, 184, 340, 1008, 15, 70, 261, 28, 340, 137, 897, 184, 1008, 15, 70, 515, 42, 610, 137, 897, 184, 1008, 15, 261, 70, 28, 340, 42, 610, 184, 1008, 15, 261, 515, 137, 897, 42, 610, 184, 1008, 15, 515, 70, 42, 610, 28, 340, 184, 1008, 15, 515, 261, 137, 897, 28, 340, 184, 1008, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 130, 130, 130, 130, 130, 130, 130, 130, 130, 130, 130, 130, 130, 130, 130, 130, 130, 130, 258, 258, 258, 258, 258, 258, 258, 258, 258, 258, 258, 258, 258, 258, 258, 258, 258, 258, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 132, 132, 132, 132, 132, 132, 132, 132, 132, 132, 132, 132, 132, 132, 132, 132, 132, 132, 516, 516, 516, 516, 516, 516, 516, 516, 516, 516, 516, 516, 516, 516, 516, 516, 516, 516, 72, 72, 72, 72, 72, 72, 72, 72, 72, 72, 72, 72, 72, 72, 72, 72, 72, 72, 264, 264, 264, 264, 264, 264, 264, 264, 264, 264, 264, 264, 264, 264, 264, 264, 264, 264, 520, 520, 520, 520, 520, 520, 520, 520, 520, 520, 520, 520, 520, 520, 520, 520, 520, 520]

def xsG : List ℕ := [0x3fffffffffffff0f80c3e03329943e030f80cca650f80c3e033299552a954aa552a9, 0xfffffffffffffc00000000000000187cca650f80c061f329943e0354aa552a954aa43e030f80cca65, 0x3fffffffffffff00000000000000000000000000032994061f0187d52a954aa552a90187cca650f80c061f329943e03, 0xfffffffffffffc000000000000000000000000000000000000000054aa552a954aa4ca650187c061f32994061f0187cca650187c061f, 0xffffc000000003fffff07830198c0663c1e0c06630198a055281548944a8154a05522512, 0x3ffff000000000000000000ffffc0000c0663c1e0cc6028154a05522512f07830198c0662a9408944a8154, 0xffffc000000000000000000000000003ffff000000000a055281548944b0198f07833180c0663c1e0cc6022512aa502a940, 0xffffc000000003ffff000000000000000000cc6033180f0782a9408944a8154aa5022512a0553c1e0c06630198, 0x3ffff000000000000000000ffffc0000000000000000000000aa5022512a05533180cc603c1e08944aa940aa5030198f07833180, 0xffffc000000003ffff0000000000000000000000000000000000008944aa940aa5022512aa502a940cc6033180f07833180cc603c1e0]

abbrev fG : BFn 10 := (fun x : Fin 10 → Bool => (x 0 && x 4) || (x 4 && x 1) || (x 0 && x 5) || (x 5 && x 2) || (x 0 && x 6) || (x 6 && x 3) || (x 1 && x 7) || (x 7 && x 2) || (x 1 && x 8) || (x 8 && x 3) || (x 2 && x 9) || (x 9 && x 3))

theorem rowsG_len : rowsG.length = 432 := by decide +kernel

theorem enc_inputsG :
    (List.ofFn fun (i : Fin 10) => (fun x : Fin 10 → Bool => x i)).map (fun a => encL a rowsG)
      = xsG := by decide +kernel

theorem enc_goalG : encL fG rowsG = goal 216 := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsG.sublists, zs ≠ xsG →
    (covUp 216 zs &&& lo 216) ≠ lo 216 := by decide +kernel

theorem no_subG (noRun : ∀ s ≤ 14, ¬ NatRun 0 (goal 216) s xsG) :
    ∀ s ≤ 14, ∀ zs : List ℕ, zs.Sublist xsG → NatRun 0 (goal 216) s zs → False := by
  intro s hs zs hz h
  by_cases e : zs = xsG
  · subst e; exact noRun s hs h
  · exact proper_failG zs (List.mem_sublists.2 hz) e (required_up0 h)

theorem mainG (noRun : ∀ s ≤ 14, ¬ NatRun 0 (goal 216) s xsG) :
    ∀ s : ℕ, HasMono 10 fG s → 15 ≤ s := by
  intro s h
  by_contra hlt
  obtain ⟨s', hs', ws, hsub, hrun⟩ :=
    exists_run_mono (fun a => a) fG ⟨fun _ => false, fun _ => true, by decide⟩ s h
  have hr : NatRun 0 (encL fG rowsG) s' (ws.map fun a => encL a rowsG) :=
    Run.map (fun a : BFn 10 => encL a rowsG) (fun a => by simp)
      (fun a b => encL_and a b rowsG) (fun a b => encL_or a b rowsG) hrun
  rw [enc_goalG] at hr
  refine no_subG noRun s' (by omega) _ ?_ hr
  rw [← enc_inputsG]
  exact hsub.map _

end PEqualNP.Outside.L_meta_583_aux

namespace PEqualNP.Outside.L_meta_583_aux

def NN : Nat → Nat
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 => 0
  | 5 => 0
  | 6 => 0
  | 7 => 0
  | 8 => 0
  | 9 => 75
  | 10 => 509
  | 11 => 989
  | 12 => 411
  | 13 => 12
  | 14 => 1
  | _ => 0

def HT : Nat → Nat
  | 9 => 0xbb8e23b2ba9cc996add4d3e7ac9055d2aa55104fa0d95fce9482119590f83fba83b80bd47ca8f776795da1e77768215a741f4965738975df674af4025dec60bd540148985359c4e65117d335486bfb1348647fc246a8e3e344713227435f4f3f41eeaff7410d78123f65fff83da211503b92e91d3a94a08735d2f30f3488db833208d92d31d110f3312eac062e2d9db62cf4f2552bab1b862a33bf2c29a9d65929752ebd23385892215c836120b5d6621ef8e2971e55ee471dfaab1b1d34f49c1d0416301a6faac51997af2e17ff479c170eff2f1666c1ed164c97bc13e43fbd13a230031360a9231299e69d10185e280ea26a0a0b5860e50af437c90a3d688a0a3c912109b5e39108c0b58f05d6f79205c84ff805a62045047eb7c903b153de02d9ef8a01d0d365012ed1ae
  | 10 => 0xfdf23beffdcde640f6018b09f41994faf12e0222eaadc5c7e99ff94be4482462e2bd4881db4a50d0dafe347cd18ec172cf9cf84cca0f38d4c9ffdb2cc628968bc58236bac3222692c1079640c0b1eb4bbaf83f8bba668940b7c8e098b7bb3a5eb5efe581b2b11d5bb1611ae6b0817701ac42d6f9ab192f84aadcbdb3a8087ba0a5bb6576a1b27c9ea02d6c149fd954429dab97bb9c4d759995cc8280952e05f4948211959167e0eb9043670490385abe8f46b8bc8bf5b4fb8b738b4689d3f9bd88a6eb32885c6f4f8753328486daa9c285e21c3885cc56da85a379a58522ac5883e7862681e999a77b660caa782672c977c3b07975bdf47575b6ed717339b36871021451707ea7606faf79e76f09acfd6e612f5f6c872acd6c25b15e6589623c61badb9b617a48d56146b38d5f636ccf5f1392715dbc14b35d9613335d2ce4295cb1b2305c7576f45bb36efe5b63de415b28bc5e5ac567615926904a58b7cb97584be26556d07662568503b1530bc75f52e7031552d2ef0c5187df1e4eeb5c504eac83e64e456bac4e3b6e964e1789774d72987c4cf62e9f4a58736049b36d0c49a17fc648a63683479c9106472aad1a46ce443a46a42465465de7624647353e44da1f5544713227427507de41ee0d8e414538784129bb5e4044cb6a3f103b373ec9145a3ebfb91f3df690fb3d8b8d583c3277b63c2de76a3c0fb82e3b89114e3ac493403a8d86fa39e1f21a39dce36f39ab653a3873548036f8c86a36bc91a835e3e3b0354a84303547d67534c98b3934ad942632c2b6ab326e37063240fc7d31a8fdc5317983df3074e2212f5216f92f3e2ddf2ea0d4c52e73893e2e49ceb42e2d9db62dde288a2dc1773f2d86834f2c7d9bbf2bfe7dbf2bf9111b2bdefca62bd655a52bc74c842bbda9e82a47b7e82a2731c528e3405527623a02260eabed254a577624dcb74e24d9282f249818a024922962247eaa75247baaad243d35a7240205f0238e1d202338589222d5ef0b228afa9222732e592213bc8d220d476a21ff822d21e02f2d2135e2e220d588a420ccbe3a2058118a204c93d91fc16ec01f59e7121ef5b5df1e957eb31df4ef021d9217871d8208001d6eaad91caaba8b1c7b70b71c4ee50c1c2896ae1c13d7471baef5ee1badb4f81ba25bae1b9e6c9e1b9e302b1b98ba151b86e96c1a9be8f219864191197348a31934e949190818f5187fe77b1846c15f17edb3c017d719c2176e3c78176d80cd16cc26e31666c1ed1666b4b216578762160a0ac815ffa37815fdf91215e21e5d157c392e1575c613155656c81547625c152fe45714f926b114bd42e3148401f313dc4b1e13a23003136e674513506b901321ada6132170c7131d35cb12ed328e12dad662129b918d129a348d12823b521274f29c1272aa5a1261c055122a8d981229c0c812041a1c11f0302111be28eb118eba9b117d997611685f64115f5fcd11438fff111e17d71117a22f110a82d110e98db910d2e6bd10a49c64107d0c55107b6f9310797b76103f968d1030c537100ac54b0fe71a450fd7384d0fc48aba0faccd5b0f9e29a80f9329850f7ce7970f6071e00f4b30fe0f2cf3080f0ede0d0eff0f0f0efd930e0ec2328a0e7c3b800e549a1c0deff11a0dc266f70db811650da68d380d7c72e00d78987b0d748b110d01a5020cce1e740cb74e7a0ca5b1890c98babe0c6385bf0c50d9dd0c1815170c13b47b0bf29c860be261d10bdfba020bbfdfaa0bbdcb5a0bb2e86f0b8194790b733f930b6396070b3a81de0b2daba10b26debf0b0d41bf0b0690230aec66580ae490ba0ada97a10ac32b230abfd5230a9f71660a95546f0a7951ca0a7059da0a5ce40c0a49fd880a2099bd0a15f8da0a0fd9a309f4199d09a99dda09a765780986ccc9096b5b0709667ca10910f9190906422608fd3e6b08fb0dbd08be689508b6c27508a114e8088f6dcc0882a7640876e172085a67c50854cdca0853a786083ebf3c082e2ed9082bf7d608241359082221b9081fc2ed0814506c08079dd507fc23bc07d51c9507ca8cbc079a3855079874ba079191af075ea1a90746d87e072e495c071aecd206fd97ec06e74ef006dd7e5e06bad6a306a937ce06a049a6069d4201069c1d1c0696888e068fb6cf067fe993067b7569066c006d0664edc706394dec0627a5e9060e65f105fc708105ec444d05be2e6605b25f6405abeb8405a2f38d059669430572fc920572dcdf056ca3b4056593aa055d93c905408f5c05173e9b0512f6d604e979d504dddc2804d13e9504b2084004aa634b04a0aa590499254d049879db04899d4c04887d54047c829a044db62d04479a5004448ecd0441ecc00425fd530424398e041aca750416da150415a0bf04072beb04014fc503ee1e1103da4d9e03bdf17f03bbe05403b153de03a3f406037ac3790365f324034ae181034a7bfb032d31b003200f82030cb6b30302830d02e4075402e32a7402de81ae02d41c4c02b0a235029760ce02958be1026fdc07026f762b026ef4ec026ac66c0265b64e02627272024b3e770219d863021645090213ae8e0201e82701f7c28101e5d55901d8eee101d4ba2a01c88f7f01bae6ca01a336e701a301de019a417d01932bda0192d79001811c08017b4964017a66f9017984b30174015601498e15012cb1300129302b0120dd510114b29b0111cda6010dc03c00f956f700e1f4f600da84cd00d5e9c300d52ae600d2037f00c7c1bd00c1791e00c03f0400a63d57009ada2d009a45ab008d4917008d083a0086a2c30073a0da0072acc300709509004ae0cc0040c11c002de9680029414a001a222b00199ceb0018f3b0001413de000e89f1000d6e6b
  | 11 => 0xfe36f7c0fe265ef4fd37f616fc6dae8bfbdf64f1fad9b4d4fa7f96e4f9312b13f918a5caf66198f5f593ebe5f55b1576f45a47dcf43d6ba9f4175abaf1f80b7df1d8dbb8f0d71bdaeffc588bed4aa3d6ed3b6498ecd18601ec8a2affec7f1c3fec73a60aec148fd5ebcf9491e8fcca7ce8eabf81e8e6b217e6c4fa35e62ccd1ee57b9645e56f3be7e4a35a27e48a6001e43322dbe37b41bde3630eaee315d136e2bd4881e009ca03df1edbeddea4620cde6f345dde68d290ddc01a98dd2bce8adcf28899dc5329aadbd802f9db874772db182551d94afb46d865eaeed612ed4ad4e15d9ad3f0fd8cd3ddc66cd34bd604d252ce88d21a57b1d0915383d0303460d0174c56cda7ec22cc7b428fcc53394ccc1ec913cc175b5bcb960960cb35b3d7cb1a810bca46fa8fc9ffdb2cc9c7e895c921651cc91ff9dfc8ad3c96c85bb2dec8432843c7a47c4bc78d2088c6d6e1e3c6bb04f9c56b2cd8c54828bbc53da330c4ebbdbcc4c2b835c4822ce5c3f0177fc3948ddec29f44dcc225edcac13c526ec13256f4bf70ad9fbf480a1cbe79a9f6be5e174dbd95c841bd68e72cbd0168d3bc663cbbba8a796ab9fe4cd6b902206db74bf618b7418c97b630a328b574cd1fb469c474b3a322f6b3403165b3272555b3007762b1695c2cb0db70ddb0817701b0788287affce4e2afefeb62ae083ac4ad7a36ffac55ef08ac302cbbaba9c886ab6a13a9ab4f352aaab96372aaaf1f1fa9f5b0b5a9c3a242a97f624fa95e67caa8f8a969a7ed5640a7c048afa74ed8aca5eb7c7ea4ce5882a4c825d9a46cd64ca45bec61a441e71da3d707d3a32593c4a31442f1a30d22e2a243c035a2288147a1ea8f01a1dfafcea1ba4807a1b27c9ea1188be0a0e054aba08dd6fda00ceea39f1e21239f19ffae9f112dd49e4889f99dd0984e9d9d44839d6428f69d1c0afd9d03ad6f9c3de98b9b9738bf9b4da6759b22df089ac9b2d49ac81a059a3ef81a9a185929990bc5f199006b829847d5ef982c3cfa97d2f4389707f3a5965c407395cb82ad95706f9a93baf41c939979db92d1755a92846ffb920f0f7791443b6a902a354a8ffef5998f3b552a8e97d02f8e8ab57d8e2786478da6c6658da09c8d8d509ef28c2e8f778bf505dc8bbeff428ba4381e8b652ec18b366d1a8b1e08108b095a008a91a4f68a83c0ae89e9723989db83d189d62b068937bbd588c0bb68887bd7e6886b60738858598c87b77a6b87645d9c8715bc6e86daa9c286cc0ae986329bea8597dfe98522ac5884fc2c48844c3de783c24e9c83bee4d2835b13888302afb6828f5ea5823952d681f1471281e92b6280f742308041b2537f6dcb447f6bb14a7f1494d27f121d867ed0674f7ec997297eb3538e7e0f358a7dd7c5147dca54827dbbe87c7d06692e7c312d4e7c19415d7c0d28f57b6a57807b0e43be7ad681fe7a6d861d7a494b757a0bb5227931ada9791fa2ae7911f1da786c6e99785f2de978507f1777ebdd9d77c3b079772ddb5d76f2136976f0b7f7766d5b667651552975f373f175a7dbce75609a5a75600aec7527c5ef74117d9c739bc63d7316856a72a893867218cb5771ccafab71827c737130a0f4712c6015707de24f7072fd8d6ff0a4a56fe427ba6f7064a76f09acfd6dac8e2f6d9aaa476d0834036cb0f4856c817f956c1855d26baa81c96b70bb996b35b9cb6a8a19a469c5eec269ba2a0a698a95506983a6e868daefab68a512df689f56e4689c83f9686acfd4684adf7d67dd115967c70db767b5f982678e81076765611b66c08d4a6647d07765835ce0658143e96522246564d93ae0649982e7649107d7643a114a642d4c65642835f563f326b463d77f9463b0ed076377a4fb633c173b6333d32b62f12462624f3ade621b089361ec13b161ba0fdb618b112e617f3500613578c261165efd60bb24f660b898bb609cab0d60819d1e600da7e6600686605fa3af715fa101005f8db1da5ed2085f5eba66485ea765c85e9ea09a5e5a21655e1548995e121fbb5db5e1a55db189c75d9df5a55d5a44af5cd792ef5cbb05c05cb743105c8f255e5c808ae75c681b205c625fb45c4e07d95c4c3e885c23ce815c0f08765bcaec8d5bc89b465bc62bcc5b9a3dd65b1b73755ad639fc5a3c3f665a29c2f6599234ac595f41395936664b591cb2af591c73ee58a02a8658926b9b5890960b580fe0b65802a42a57c203b557890598576aad57576149b95757b76f572cc78257203fca56d07662569d1ec0566c94a456224d6755d783a155b91add559f5c5b55603fe2552d58965520a0e95513c9d75508853154dcbd4554c70d8454b510fb54b1e2c85493b0d853a02ba252f778af52ea5dfd520edcef520b521751d698045189f7fc51888ac05149e91f5138e99250f9fe7d50c6b99050c2ae445089af135050a06e504d8dfc501e91fb4fed171a4f8774ea4f7789fa4f08b6174eeb5c504ee75abb4ec362314eaa81154e9dd7904e8aafb44e7900c84e62d4324e3019504e283f8a4e009e284ddd5bfe4dcaab6e4db3718a4d5a2eea4d57bb144ce25e444cb6bf854c64e26d4c642a5b4c1722eb4c0164a94be20c994bdb6b304bd67d404bc8b7a04bbfb8854b7564ee4b619c544b5431cc4a92446a4a573ae34a1609774a070bf54a01f5be49a17fc64998dda4488fec4b4867b1e0481e8d5247a71df346ef072546e759e24619d733453e06fc44a15ad3439d9d32434113644305b59942e8c88b42c9651342c2ff9742be3f0642bb174d42bb0369429bfcd142454e56422ce52a420576b4419a3f014193796a414663c641083f6440bd65524059d33f401e73753ff16beb3fdc6cd93f846c563f4fc96f3f4d32863f45cd183ed20a383d9156293d8764c63d7c7a853d4a7b813ccb45593cc003413cab2f573ca0c5113c87a0683c2de76a3c1007823bbf9a663b7386f13a883c503a58f1523a42f0163a2a93e23a07844e39bcad9e39b07c61398f48483933e4da39297c2438b4eb493890c27c388cb295387375823835c86e37a4675e37262eed37083c0636fa7e4436f4207a36b97d3c36b02d1436818b0936781e0c365cd10636553d17361d9d6c35b3463e35a32056359465a23578d2a4352cae9534ff540c34f7af5934f3aca134ea5f3a34bcc6f734b23cd134abf693344bd98c344643f2342d938f3416a17c340a4b7f33e9282933e7a6b333c0c8b43397710b3365397b333ef6d8332ccad232cbb1fe329bcf513264d2a331d8227a31bdfdce31bc294f31acae4b319cef0e30f560b530833ae83062c4b82fbf00872f9824fe2f3fe8222f3b0e4c2eeab6372e49ceb42db877452d990c232d86834f2d1b97272d1acca52d08ed462cf64a202cbfb1732ca4ca722c65fa772bf4cc972be452572b86224f2b7d20272b74fb512b7440502b65a7522b56dfea2aed601f2aead2452ae212652abd3e762abb63112ab192822a0a18ef29ec14d729bae34d2955a498294d656f29441cf22905007f28ebdc2028e5f8d928dbc97f28cf459228bfcd0628b57d1e28ae45dc28ac97fa2899b1bb2844d9fc282f1e7427f58ce127e861e927c93a9d2794086c277c6ee327667f92275b58ad2704980d26ea569d26e85a8926ab26f4267b99e0262123eb254f06df251e18f524f21a5b24bae1cd24a4de4a242da49823f836aa23dfa2aa23d087c623ce5d082395db92237d9f902375166b22fa86c422dbc91122d6343f22a6fdb721e02f2d21bb6c4d21a2024b219d61a7219531c621791e9721683b2d212c52dd21064e2120b3851f205221c91fd6b9d21fa6f57e1f8ac3c01f7fe2661f7784c61f3fda491ecae4b91e7e18ff1e7b42fc1e5581a61e51a9481ded46341ddd88921d955d5b1d4f0eea1d4b5e381cf289d01ce56f1e1cd753441c7b70b71c4ee50c1c3c3f9f1be5950e1bce25c81bc93b201bbc4e941ba9566b1b9711801b6b50471b6128f41b2f4eb41b03220e1af799f21ae314da1a9e589b1a8642681a53b6b719eb4cf419e289cd19540e1f193d5dbd19371f8e1905111b18bd166918a26d731891b7ce188eb3af1881a59518744aa3187152a2178802ec177c41631762564217454155170cf534169d2b1816890bc3167b929216641c73165d65e016590e3416578762163ec1d1163785961612340c15f08282157e311d157c392e1570760f1545ed5b152256c41512704f15120d7614d3f4e314970777148d558b14577c51144cbf9a1411ccaa1405ad7413f2998a13dd0d2e13aad7d91378c96613756cf213685e97135ce915133febcb1323c22112f9114c129acad31297b37d127c95b61273f1761250f1fe12199e7311e7497b11d7514711d3348a11b2350711abf9791183fcf81176f46d11685f641162cf92114e8d4711438fff11306f61112c255d1126ebf01126325e111e17d710fab7c010ea184610d4daf210b608e310783223104bf2e90fe9a4f70fd7384d0fc6c9090fc587490f83d8580ef131df0ed3dcdf0e9c6bf40e7deb7f0e6d667d0e5def800e2202880e0cd0dc0dec43320dcc20830d97d66e0d8554a30d5874570d38d6640d1a4f9f0d19d1a90cf2ecd90cbe70630c7831150c68d40b0c5482b30c39fcdd0c1815170c16a21d0bef51220be50a1f0bd2cc040bc3b5170bb489810bb103b40bad5caa0babed330ba545a20b9550220b7764c60b664a3c0b64244e0b6255970b3199760af3844f0ac411fe0ac1af9f0a44b7a70a31ba920a24becb0a18afad0a0fd9a30a07a8270a05965209ed1c5309cd77c409a99dda099daf7c098a28d309442936093e03d4093b7ab608fdb35508de961708dd8cf208d1826d08c6df2e08b0f9d808a4040208a114e8087c9a340876e172087050c8085af9a00858ca5b08450ff3083e0c61083dc9ac082221b90814506c07dfdcb107d255f307c329d607a7d736078c674a0748710b0746d87e07338aa1072be0db06fba5510696888e0675a3d80628d1ba05fcebbb05f157a805ec444d05d0389705ba815805b25f6405a2f38d0594ee19058a05ac0580fc55057fea86057d716c055d93c90524428704eb047e04e5863d04dde7d10499254d0497fbc2049523d40487529e04834d71047fa1b9047daba9047d7274045722dc04426912044221c1042a70c80416da150402956f03f0940e03b6c9e803aff6ea03acdb0603a55fec03a3f406039c205a03876eee034a678f0341cca70335f3b8031fb7e1031a391102f7c7ed02f5ae0402e91e4002e6b43b02df108c02d308e5029effdf029760ce026880d2026837910260ddd2025fc5ef025cd7ea0238bba8022f80fc022e3c34021b313f02183c480201e82701f8d1f701f52d8f01ee6a6b01ece35001de9a1c01da8cb201af509401a8c99001a01796019a417d018e4594018c064b01783db30167e99f0167a6a301641fdc015ecb360147a27e013ba468013aa2bb0133050b012cb1300129fb330129302b01285159011af1c601034d2700eab74600cf67090098b2240096c045007ae7640073e79200650ff3005b136b002ec670002c71df00279507002587d20018f3b0
  | 12 => 0xff38e983febf44a0fe842794fe265ef4fd517d97fb28864ff84615c0f7c8e94ef66198f5f48684def3f81810f30a4db4f3019272f134d948f08dfba7ee501c33ee3668d8ec7f1c3fec5c3f4ceb882efaea35646be985082de8fcca7ce53c4559e4a35a27e43f1091e3556e02e3191c75e30b2fb4e2bd4881e03f6f5de03c5a1de008f861df17fbb7decaa9f1de68d290de5b3dbade101ed9dcf120d6dc2833ebdb874772db182551d966f6f0d85ea673d746cc2ad6e163e8d405bb4cd3f0fd8cd316daead252ce88d20ea3c6d0ff4b7fd0c63844d0984103d068a10cd039326dcf1022d2ceaa2d91ce8a71c2ccc6bee4cb1a810bcaec5a89ca188506c9ea329bc7c75cd0c7915e67c78d2088c76a4b28c25771b7c1ce0b4bbf39a2c6bf2165d4bd73da0bbc3ee228bc0755b1bb55aac1bb1ffce3bae26fd8bab25205ba2ca114b82daee1b5a345e3b46235ffb3949d65b38a9fa3b380194eb2961158b26fbb51b2038cc3b1b3fc21b0ce22cfb0738b09b028b4b5af92166caef60ab8ae083ac4ad50254fad3a839dac5cf88fac302cbbab896226ab6a13a9aaebf182aab96372aaaf1f1faa8c49bfaa361daea9eaa2e1a7ed5640a665cb40a5eb7c7ea555501fa4a736cfa2cbf6079f3bb5a49eaddf009e00cc6d9dcec4b69d1c0afd9c28ed2e991730a9986563cc9839c06f9805c70a97888b22968b1a6796501a2095e57ead95706f9a951eaaf892d1755a910004c29039ebb0902a354a8fca53098f86ae338ed929e18eb90ac18dae48568da09c8d8b576f6989833ff0887af8ed879217aa86f244f986daa9c282e13e7f823952d681a6b1b37eda86677d7b0b5a7d750bf77d74934e7d06692e7c9122797b8ebfbc7b4db86d7b0e43be7ae3291b79e2e89b7931ada9791fa2ae7911f1da7640506175a310f5759cfaea74dcf7e37456aa01742c47ac7416ded17380d29172707494723fe1b171dff087718fb39e7165e9557159f7b0704999b36ea0566d6d2563926cc48a046c9ea5066c8ef84f6c1855d26b928e1b69c5eec2684adf7d642c9994641ee83363b0ed0762ccaf4a626074ed62179f816165fbe560fcdf5d60819d1e5ff831615faf5d5e5f04200e5e121fbb5e0185b05d9df5a55d04e7325cfc94b25cdd452d5cd792ef5c681b205c23ce815bdaaacf5bd5d2585b90dc895b7e40825b213db658a9b269583a79b257c203b557894465571380c7569d1ec0564d67b5551c31585513c9d752d77c7451e4b5c150e82dd95032079b4f7789fa4f6e85f34e3f70b74e3408344dcaab6e4da593af4c99a31c4b54e01049fb9fa54983f933496dbe104879514e476fbb7d4755390444986d50447c9fec43880f5342e1f7c242a491e341f79c2c41de78d1412dc89a411a661840bb1ce1405e46643f7767cf3f4fc96f3edb3faa3eb1a8913d9156293d50c4593cdd85e53c91dbbc3c57ec763b5508c63a92da813a6b00db3a58f15239e3a1de396ca3343936a4cb3883f09938455c823835c86e37bcc6fd3774bbb235ff086533f75ed2336f98cd332ccad232adec61321e90cf31bdc3b730b37d582fff136f2f9c2fdc2f19206f2cf64a202c8fb1922c5dd05b2c5b860e2bd272892bc8a4c92b56dfea2af7f07e29ec14d729ea805928bfcd06278503f5274882f22709a75a270940b826beeae3269dd9f825538e2525179c1324ef16b7242d52d7241501b522a6fdb722612e30220677f6214053b82134e7ef213297372072e1a3206ecedd203a534f1fd6b9d21f8c230f1f7784c61f1742791e86ae111e4df5b71e1716dd1ddd88921dc094ff1d05a0751cf211741b6128f41adec59419e289cd19523e811881a59517c6fad71727282616445e411518c0f914970777130a890612f9114c127c95b6124f8de611789c8b1168284e1132bdc510e8d08610abbf1510a8ad2f106ca4b30fa612d10f1b664a0e903ef50e3e86020e264c940dd9e1a50da9767b0d38d6640cd8f9ce0cbe8ebc0c8708310c8491860c39fcdd0bfbef020bcfc5980bad5caa0b22e0990b180c480afb3c9d0ae1a1310a76fa120a05d1c40a05965209df06d309d7ad4909ccfbd809bfd88f095b4dfc092dd18608f573c7087050c80869d26a083daf2c080ee36007c4d0ad078c674a077d6c130746333f07338aa107043a630696888e068beda7063e21510628d1ba05ec444d05c752de05a3e393055019e7047fa1b90417fad50416da1503ec845703a3f4060383f21402a557c1029760ce025fc5ef01a8aca8018e459401077be000e2939600bf8a26003aaa2800279507001e80dd
  | 13 => 0xc78d2088ac302cbbab6a13a98da09c8d7931ada95e121fbb57c203b55513c9d73d9156293835c86e078c674a0628d1ba
  | 14 => 0xe2bd4881
  | _ => 0

def PT : Nat → Nat
  | 9 => 0x9e8cc4d45318a2bc03414b546620680c65be1189954030131ac700a4c0e4175318b81a23514a8062af000c0cef019230173805780630e0dce01bb018c8ce7338578262ada80c64d1b1c00e463090f8c632d800c651581b8276731752626e0d280c65bfb9c00f573800f806303384cdd5b098b26a6314594260ccf44e015b098b98883246e006020688dc45d3183a5a137156c063068c4dc12681c03191320648e6309d98c55a1b9c02ea031919c2626d284c6013b9c001a53414ec063065c0e412681b8362631731ac720ad80c654209b9aef6320648c626a100cc03e09b087c63174118682c918c5d5e019888373511c8c60a43c4c913b018cab60315
  | 10 => 0x2c9020aa6ce668d600ca9e009a11ec6b91b8406490024c91ed3183004031058584091ba8814102b9c9ed5b2114984083d98c4c6a99a0314a6347a406a17d19dc05a9b89a18e204d61e40ae980d8e0f01b904d735155e240c2d1ad04429b8c756020a2a20f007d3c81376910280007381246e309780d8c742b1a25602047380649134a8058d058c951037041c0663a6bc81016610225e1330332040e6cdc8599799029517b8030a2f2036d9c402c01881f443410ae260b2400c911e01118eadb0380c1402eb18c0cf61302072821016af4817d0ee045a338b8f86b71634d62e0438e4e5121815b602161801633d944e018d058c3048204634ce2e92ce90d8d058b0c00b1422c97068384e8cc283903106341a89e408080d8d12a892809803822a2ee60312cd44c28bb831a07122b44624c681c6000b50184912171f24c2451b8850d039819c46383496d707b5c48101e75b9db843514bc266e0458ce8c28db807243207512e32615dd40a883a0526031a4f0c60a5bd88251779029175a43180c6326c00d06f7318c3760313b46cec00fd88113c31a005cf3a122c4e613080c68eaa9b00ea5a131028660c83cc907c3da8a5e13311806e327e2ae0e26438b2d6a3511850c697b80c6460058a88e6338019e6060e14d8479a9a025e139302c06140400ce0f6ab8a0ac638012e24124da8c540871a997d7208019e60c3f94dc1239910b1a13181802e2a3b84e405959c090263036ce040e5441dc04679121cb2391180162c2520c541e85c9d9c0318d14064859d0c1c7f59b00ea973878a670491b4e44105dc1f1f320504ee6a0309ac0c2929d08fc77371d1f606c680c5c1e6501bb1021008407400354c12266b9382a03800b0064023d88143c71c84cd12170450664ae00d4c06119259892061800e638510d4107319c194bb820b8c6c2a310c601e75b906c230112966029c58828d789a0017230316e460c2da8c16fa3ba0614038009e0606545de4046790a2d4f30304d66067e3680c3a09b8161139031826a0839ccc8a161022d733a1054c6606945ce0c2b9b818e3340058a6021390c280541a00c553901d1ae70348dc60cf7521a46131833c56e6201ce4013798381663502acc64c0490d44a881c00fcf73824c06e0752cd400511c800b33030ed874067c5ce005b9d00c42330072662e0310c282909a8894337157a66a00c80c1829798b032639002466340c20ce55ca99a0370380044666a3650dc419299822d23254984e703f94e0009118b0ac7360018460a35d8e402a39841231391064a7004829c58657982892aa01244462e32d4c19f3b903102238015aa6a01b4cc618909a906873601fe260a13b8c18775984050cb83341e60a202ce007cab8b174130448e07425d40c1c1971b80b613080eac6062794d007e5d01922131624cc6a02018d0146298baaa33501a48c2a1da0d402229c000d2308705242c695690f375901a2c53305fd263088b8c5c6b19828309338444062a1138c18c1b90b87703800a4a6e204c8e0488a1d0a0e73300a64722599cc2022b998030737305606800980c2056119802a23a0444863011d4cc0186999064e312015c60c5446dc01349849a42b930a926140e04d449101c0845637004526c62510e048e118a1670305088a6800c3ccc011a1d180b2380302070214b4e042171a84c20316114a7002340c48c6a1c80b35391084268013c4c144539a803093350e826101e54cc00681848b643a010d64047e2adcc3801980ff3340019460e5b00d0045018511013810d0e720151cc143a61830055320170e6c035b4e805cb983960d3401942607a0da88013418331a0714100a6a00138e806211a800813010a8860eb5a8884c7b1c804e7304045e68640a8c281189b98d2971913ee70027d4dc03431a8046030a25a272009b0c281941a806c3351168ae320d9cc242769c80788370085270027b4c187c9d00a463351206860c0e14c60aaa9a847e6350022c66e0708c403471b824703162d9060c1c30e005679c807043401ac66e03018c540621880e29330014060e0cd4c280b618404643900e8c6a01190e003669c886cc3171c6270005a0c1c6299b00788360004e6005441d402789838c3573826d87022dc0c0c0539a8030c33aa9c06a09198dc43c21c002ad39002446021700c5d5151b98789340388c6c640d4c10c0898c82a836004d66081550c0d3ca98420e737308646c014cccc422798504603051dee608fb84d083b299803a5360061266c0e08e842151c807563090bac62a05b0e400b39b0010e33629286c21490c5111918b068d380661c4081c50d807189a0042e330046670611c8c1c0b418a95433402cda6140e00e446b498312753a04c4c7401a2ce8040a9d0071239007566080ad8dc01101c9aa21383
  | 11 => 0x2120e210d13460b400d40319530a121405295240e0b8089c95891321d120326d568028a6980e801a90ee47051548c0c063fcd8fd55c8028af6557814087c22d006cb1a124e22301ec06461155ca07a01982121f7509006063658cc8d201808124f01039dec600ce98409a7bb16282274c82e7000829010907218b307071de8e08cb86d002401828020310062c8001cb280cb41303801623703444208483e4d1401a025222034241e866a88cc0770d9003a9a4009404423a81c240e4f8b8303f2700556401a1ad4408a5a80b803230383e325f80c0cd0b9041a20b820611ee69211c184c038426407170619ec8048be040947b210603021e6f7421118c4c690da829602301456e12668adc014afc08288f093304e0e0900c40510db99ea73033304e2e5f00c0c770b8c0195f811642e726882c285e6db80932b710305f126080c4c690da881caf430a42662921ae400927008e613a01d826645a3dc21072dc00134f982e036c2070390c2301981681a60050880865ae80c0739a8a131f50050fe60074bca46a01981261706130ce1406278d80c9b93829640000436e0049fcc88201808aa8604032deac03808d109079a8020a700309e0c329080c570180830af9309ee7223482e800b31d09966ba007436c21155c190105c80020a5035c36829280c140e8f818885205052de0a5d5c820d713851401350030dd0268c185091018a1e6023041c3680aa00c4c0e1b938eb5714051be4c060be000c57ca0294f2554406160a0fe240987ba018cf05060bec00623dd05c31019995b812a80606074d008791da89994b80380cc0a9206d400997c90180f863e6d742849be44227da89af77150aa0c680483e0174019831226070dc0602761080c147f9b8100b200387eae2c85ce01201d8098ba201ac06060a278dc18a7b1018ef26062becab896d800509998ef5b601fc4c201102d4c1467b222b47050391cc604a3c90e6791c11603400900408af118119341048e60380200068068d9849090718002aba1324c6a00811c200e4f938949a500503f0e3fa88405e05c0028bf69030bed2af488113f9118018f406344d60c0707d64a501030580330032def03080cc0d7038c9140341060beae074bd886005a081cee6217a3720a4bc80c182f2b80403300d017220806d008001a810333300619ed2530480c223d280ea271501c046004d3d509363010189f371eae46c0c1bc145e2db0844060205517000d80cc03201818e603701100646254ea004a41030f37ba00525e086881cc00e72018940b500100680048fe190705c80287f361dcce12082dc242a038b820670a062fe0429daa00183f840686b505784c0a0c1bc2417210381c1e100253e6c3f85c29978db0213079000697408082e440c378a818df350b0064a0e86d010907b1b12c60514ae41006378d4fa05d08284f494a26460848398c6b0189818bf190383d0e5998cc07f35850ca03030515c4a060fcc09101818ce63030f9c448255ee000e4a038fe171a08816a4074b9940b298b0a6fa60052de8a66a2d00dd35d00185409426de602605ce01d73028188e14044a6e6074900075adc081c14090245d003b91c216101180136e740623f080a4f8553345a00bc0b600424e0c1a02e40085dc8018af541a4f6e0238080c0e0a00827620703ae80a8a95c28180f8c12c0323544c60e0a0fcd00105180995b600100660468281c10a38283a4aa0130ae30009ee00e305038301e180e806602cc6dc4093728830c40605416a00998ce00912040d403504b836620c2be5cd105820ee371a5c657203a89c14395db0abb12031e6ce28032ec840c07988194f2449404600a5502009779a0a2672400416200c5f9890967c822acb63050bc620c5fc104c5b84892331900804608a8ed00268102292035228806260a5bc200e47b99aa4340032a8100280c406005a12492ba00327cf02100c0c0cb7820127f2027816e00c53a4c0c773a0305e5349c06600c27c40091a0181c3f10024dca80c5d0084c5b8d01ccf600529e50072be0ccb35d080f023809c462a1484c8c04811c03a67250311ef22f34dc00cbfb80fea6140a9ee720c23c1c18ba0227686040395d067e82e0018af92ae40b7138134c07d02dc060330a9680707061be2c1e9480c1a95c1a34760a0181742071f86418af12972020317ab4a699b2e000c9a00828cf240503c6c075bd4c1c0181828be81474062a55ac8c07505b81cd22031fc46140a338917b29180582230039fc2e2656d840cb72a12f73420503e620a3fc9c0e97048165321238a626248dce4142fbc8544719039fe269a108c19795d00026730061fed00c0bc90b82d018d21b710259d020e04c4c22ad318127e3106af7266c18cc01817120f23718128140c2f4ae481d2db808413311102626261adc400991805507181a4cc0c718981c4a038302603730309c0c1152e8d7301180fec3041816e346498cc0143f1a8304e6402806601600d04185204812de36131b4428ab2d801a13b889407160e55706064bc9c060db0b17223002c06e20000c418905029f22714062fd084000cc00645808297f672e296e60d36d84775b851ba0b70050fe0cc280cc15101828294e06032be280c43e0c1827aa0121e300303e700713d9c1497838fe87144241cca048fcc4c00dc00193e190389cce063fcc84c35b80188e25052df0a80a69c01a031a0ea370a02ea6a202808c0dd35b98305f871662c680a2be5509371881c4f09062fe862700cc05e3d389c27b510519f0c0c0784d8943020c73303051be64064fc4109b3a80713330031080e1508c5c0c3fba8416227030dee2069cc0c5e6bc00294405052fc68072bd949e05a80136f84179aee01f94cc01417c20300f58006d7201484c0c0c42020186e7143484060a03c5d2e05b80184e20080c4400a13dd0ac01018282e841e44e1200cad0001b5c881cef931fcf608063b8240825b80342b910309e12580081c099790868a7041cc07200819c8018b7818285e080509ce80c3fa1ce401918c15713108264636188c01817b385603305a00660062b8d00c4f0a8a68604124d6320c078500d81c80308e605c8ec120356e8c149790028f407179b6a049d29400c279498a53301dcd6e02f0dd800835981c712070251d246080c0c06131a0129f26050a812071380c187a040ea9a21152e46e191480c1555c8868b71401a4ec2009ed802d41980315e15050a8020c3d004092f19018df2507224168ac6e00014d980192e264241eca0c3bd8c18a791818ef640519c280d3ce441a59b09c706041fdef20049f8e0097fcb028ef75110e60641d8814067d9883a770506108060487a58e315b98120f500615ea6074b9cc0655b8960022707417003a82dc45e83a80289f3909ee76204a101079bb8b0121f301646e120e82e807621018286f0111204140c1781c7f75c801924020d02c14072b84ce799018288e0516c46640c2fd642a9d8c834831447404060713c1c0e3f8922823301cc26a00c0dc9c140f9c0353b710529cca3ad5c105903821ae271a02e66020a2fc580103c80130e2437536a01a3d8680c2f8b0693b810307e720d52e84390bc08188e240605c861535ce0188fcc02e0302568c4060594c600f09d00543b17040d6e00707c54a501130309f170519c8a062bd640c37c28183e39050bc600324dc45563820301e1606a86e21885e40182a0380e03300527c322f10d804c5b8c8196f84032bc0a070794c2401018301f280309c08072a80813319d054db18069d6280497d440c174001d2f02060a80a0c43a0c1427948351b810311e6806078e059138b0284e86060fcca0900e400e97090289e490e5b7023c8dc643b01d080403401fd97220a1b81005019803046230619f286ec2e00143f3380c8b140a8ae280082d4059ab8a024d220030e80a0c1b8140967b89a3061a0686f02065f8400eb791830de1924c2e2c24a98d009a7ca0194f280245cc87980cc42a258a0bd13900ee26840790e00220b89a769a60069e7020a3f8e418b70181af32341e56e0075b88c0c3a01910d3305c4d6e02bdc8dc0e9f010292e270615c201508c501f79b88fe13903e816e20894e8c18172a0a26707030dc6e04878d03979c0854c3180607e520fd0e4418774a018cf2000806203c998498989028175302052fcc80c3f85c01a9980127e7000434400fa4c84144f42802e3901e68e080c2791c2a498ca130730050e80c058888430999903cf303032fcc80c25ca03113b80195f210309c60060ba100629d08629b60145cc080339c501827a38ea9a200329d2803269843d31818fe7b31051fe6a0d01d841549a80123f381800e121f54e4414070b8308e631fdce080ad0cc11799180195e3235dcc0c65d6dc40c6f2b0304e730511c2c074781c4a03030286e95050e8060d45e44349dc00123e8401926020580e44e829180292402058c6060315e85153db80feaa910395f0e07238545ea3c8034f3510513cea0713e5c59338c82613390263ce2073ba4c1837020130f70061fe262f24d4009971080d7771024bc406b99c600c070b01b7380032feec0d29c50186f2c8128e94050dc702f14e002d41a000c5361061dcce073398059a38a8189e31062bcb0065fa141a8ba889ce350456b720060f9c009072809207183a806600eb29c0094a0300cb314
  | 12 => 0x979d00707d000ebf4700a0c0605d7dc0070f8b0006fa302c1e0a01aad40062fb88160ea0004bee20283c280607b800e0e630043eec02dfe000233818020f910101f2a0083a4403072180e1b510201f4000028c00707c00147f60008dc2602afe980001880004f460065e860317d440397b980e1f91000546405d79000807180072e730049e9001cacc0014d2800c04000041c06039bc0c07072a0060fa801956600283a000a3db08047e730041f44018bea40132018080e980041d4402838c80207c30040e0a014080003a5c1c0bb7d180854080111f440083e98008fc20080b90010080003039c40137898064f8300eff46008384c02070280a0e7600cbf200117c68012a02006ae72008fee60453cc00b5fc1806a4060197e6001079d801072a0065409004bca20343e5c035202806bf5001dff0e03afe5c02072180e1f5001c0e0c04838c0020a0301604000142e1403879400503050021f5401c0c0e0102e040202008066f21000df500086d88051fc30060a90012deca011b80c0107cb002bf980085e860083e48020fbb0141a600043ea40057dcc0302000008f6100e7e600083e84024fab0147e600081c42041ed4000bfba00c0b6002a1f260497d440b5d200046e530201ca0019be9805afbb004040001074800383e180107ca000640a001fea402dbe080281028020e9801e2c0c0097a40012f218060f8001c3f020447e04060db800254080105f3001cf9040b6302808af62004080202dae000045d0004060a00cdca00501000033f340122f210091ea60543a800902000116f730205f420033dd80387b40043f5a004081401cf8d403370a8027f63004bf500117da80392018012fa400436a00027d80070dc880e0ba0004bd280097dc00173018141f610041d42041be940347928000ea300cb72003038c002172b000af8101415000387d440205028020f510041ca0002ba04012548010bb60000166001cfdc800774c00e0e060251e600283dd0007f298008fa100036400583e840817cb0060a500201d4a0197a0c004588000ef100003ee40583d000137d1802671300c2810058381402120280e0b80001fca803bfc5c021a050040f0602c1e4a01b3dd80067cc0144fa70049ee8040790c0707830111e41018bec20383e8402378180e0ea101c1c0e01afda40337148020e7600c1c600096dc00857a98020fa0010d5200083e400047cb00a2f0402efce0003ba840232018066f2002017400203e400707d48011f820200800004fe4c0405a00066f100041cc6009fc8c0107500011ea40201460008798805a7d1014efa001e3e0e05dfe80005f3b00e0e430084c0a004be50010a0100204000195f26011bc4c0085c00000f320082c0c03bfe0c0355b000d3fa101c1c06003502006179080c0e700016806002501800a72080e7f9300d5eca03839180305c00060fa100e7d4603039800517cb00214060003d080283a58030750800ab820049ce003b180c0107290080fa50011c6200479c8005db00080ea50081f020087d88013b818040e8100417400083d400105c8000ff20014480c0013a50008a020011b4000d1e52010dc2800bbc0010bf60004bf480207994003fd10001f53004de06002be18003f5100e04000017ce6001bcc0015fc180c0f60000ff00028b908000398000ce74020fea0019bd800837500114b3001428140097da00b6b040009e52010280a024f90000a7308174f7301a7c860055d800047d30160f080011f40002fcc402078280e0fa4018dcc60386e040452010047e060001c60004ba4c049db8000cf5400d5c4a0031d00030794000f3600087e140183a98046d380014380002fe82058382000779080efa5000108000024cc000071900143400025e8002839500039d00026aa00081f2c0039e80049f190040e9600c1d200083a8c0165380040e1a
  | 13 => 0x15ee0000be5000074a000ce100009ea80007950001a0200084000029ce00043c400047a00002e40
  | _ => 0

def ELG : List (List (Nat × Nat × Nat)) := [[], [(0xffffffffffffffffffffffffffffffffffff00003ffffffffc0000ffffffffffffffffffffffffffffffffffff00003ffffffffc0000, 0x7fc00000000001ff000000000000000000000000000000000000007fc00000000001ff, 9), (0xfffffffffffffffffffffffffff000000000ffffc000000003fffffffffffffffffffffffffffffff000000000ffffc000000003ffff, 0x3ffff000000000ffffc000000000000000000000000000000000003ffff000000000ffffc0000, 18), (0xfffffffffffffffffffffffffff000000000000000000000000000fffffffffffffffffffffffffff, 0x3fffffffffffff00000000000000000000000000000000000000003fffffffffffff000000000000000000000000000, 54)], [(0xfffffffff00003ffffffffffffffffffffffffffc0000ffffffffffffffffff00003ffffffffffffffffffffffffffc0000fffffffff, 0x7fc00000000000000000000000000001ff000000000000000000007fc00000000000000000000000000001ff000000000, 9), (0xffffffffffffffffffffffffffffffffffff000000000000000000ffffffffffffffffffffffffffffffffffff000000000, 0x3ffff00000000000000000000000000000000000000003ffff00003ffff00000000000000000000000000000000000000003ffff, 18), (0xfffffffffffffc000000000000000000000000003ffffffffffffffffffffffffffc000000000000000000000000003fffffffffffff, 0xfffffffffffffc0000000000000000000000000000000000000000fffffffffffffc0000000000000, 54)], [(0xffffffffffffffffffffffffffffffffffffffffffe00007ffffffffffffffffffffffffffffffffffffffffffffffffe00007ffffff, 0xff8000000000000000000000000000000000000000000000000000ff8000000, 9), (0xffffffffffffffffffffffffffffffffffffffffc01ffff803ffffffffffffffffffffffffffffffffffffffffffffc01ffff803ffff, 0x7fc0000000000000000000000000000000000000000000000000007fc0000, 27), (0xffffc0000ffffc0000ffffffffffffffffffffffffffffffffffffffffc0000ffffc0000ffffffffffffffffffffffffffffffffffff, 0x3ffff00000000000000000000000000000000000000000000000003ffff000000000000000000000000000000000000, 36), (0xfffffffffff803ffffffffc01ffffffffffffffffffffffffffffffffffffffff803ffffffffc01fffffffffffffffffffffffffffff, 0x3fe0000000000000000000000000000000000000000000000000003fe00000000000000000000000000000, 45), (0xfffffffff007ffffffffffffe00ffffffffffffffffffffffffffffffffffff007ffffffffffffe00fffffffffffffffffffffffffff, 0x1ff0000000000000000000000000000000000000000000000000001ff000000000000000000000000000, 63), (0x3fffffffffffff00003fffffffffffffffffffffffffffffff00003fffffffffffff00003fffffffffffffffffffffffffffffff, 0xffffc0000000000000000000000000000000000000000000000000ffffc0000000000000000000000000000000, 72), (0xffffffffffffffffffffffffffffffffffffffffc0000ffffc0000ffffffffffffffffffffffffffffffffffffffffc0000ffffc0000, 0x3ffff00000000000000000000000000000000000000000000000003ffff, 36), (0x3fffffffffffff00000000000003fffffffffffff00000000000003fffffffffffff00000000000003fffffffffffff, 0xfffffffffffffc0000000000000000000000000000000000000000fffffffffffffc0000000000000, 108)], [(0xffffffffffffffffffffffffffffffffffffffffffe00007ffffffffffffffffffffffffffffffffffffffffffffffffe00007ffffff, 0xff8000000000000000000000000000000000000000000000000000ff8000000, 9), (0xffffffffffffffffffffffffffffffffffffffffc01ffff803ffffffffffffffffffffffffffffffffffffffffffffc01ffff803ffff, 0x7fc0000000000000000000000000000000000000000000000000007fc0000, 27), (0xffffc0000ffffc0000ffffffffffffffffffffffffffffffffffffffffc0000ffffc0000ffffffffffffffffffffffffffffffffffff, 0x3ffff00000000000000000000000000000000000000000000000003ffff000000000000000000000000000000000000, 36), (0xfffffffffff803ffffffffc01ffffffffffffffffffffffffffffffffffffffff803ffffffffc01fffffffffffffffffffffffffffff, 0x3fe0000000000000000000000000000000000000000000000000003fe00000000000000000000000000000, 45), (0xfffffffff007ffffffffffffe00ffffffffffffffffffffffffffffffffffff007ffffffffffffe00fffffffffffffffffffffffffff, 0x1ff0000000000000000000000000000000000000000000000000001ff000000000000000000000000000, 63), (0x3fffffffffffff00003fffffffffffffffffffffffffffffff00003fffffffffffff00003fffffffffffffffffffffffffffffff, 0xffffc0000000000000000000000000000000000000000000000000ffffc0000000000000000000000000000000, 72), (0xfffffffffffffffffffffffffffffffffffffffffffffff80001fffffffffffffffffffffffffffffffffffffffffffffffff80001ff, 0x3fe0000000000000000000000000000000000000000000000000003fe00, 9), (0xfffffffffffffffffffffffffffffffffffffffffffff007fffe00fffffffffffffffffffffffffffffffffffffffffffff007fffe00, 0x1ff0000000000000000000000000000000000000000000000000001ff, 27), (0xffffffffffffffffff00003ffff00003ffffffffffffffffffffffffffffffffffffffff00003ffff00003ffffffffffffffffffffff, 0xffffc0000000000000000000000000000000000000000000000000ffffc0000000000000000000000, 36), (0xffffffffffffffffffffffffe00fffffffff007fffffffffffffffffffffffffffffffffffffffe00fffffffff007fffffffffffffff, 0xff8000000000000000000000000000000000000000000000000000ff8000000000000000, 45), (0xffffffffffffffffffffffc01fffffffffffff803fffffffffffffffffffffffffffffffffffc01fffffffffffff803fffffffffffff, 0x7fc0000000000000000000000000000000000000000000000000007fc0000000000000, 63), (0xfffffffffffffc0000fffffffffffffc0000fffffffffffffffffffffffffffffffc0000fffffffffffffc0000ffffffffffffffffff, 0x3ffff00000000000000000000000000000000000000000000000003ffff000000000000000000, 72)], [(0xffffffffffffffffffffffc0000ffffffffffffffffff00003ffffffffffffffffffffffffffc0000ffffffffffffffffff00003ffff, 0x1ff000000000000000000007fc00000000000000000000000000001ff000000000000000000007fc0000, 9), (0xfffffffffffffc000000003ffffffffffffffffffffffffffffffffffffffffffffc000000003fffffffffffffffffffffffffffffff, 0xffffc0000000000000000000000000000000000000000000000000ffffc0000000000000000000000000000000, 18), (0xffffffffffffffffffffffffffffffffffffffffffe00ffffc01ffffffffffffffffffffffffffffffffffffffffffffe00ffffc01ff, 0x3fe0000000000000000000000000000000000000000000000000003fe00, 27), (0xffffffffffffffffffffffffffffffffffffffffc01ffffffffe00ffffffffffffffffffffffffffffffffffffffffc01ffffffffe00, 0x1ff0000000000000000000000000000000000000000000000000001ff, 45), (0xffffc0000ffffffffffffffffff00003ffffffffffffffffffffffffffc0000ffffffffffffffffff00003ffffffffffffffffffffff, 0xffffc0000000000000000000000000000000000000000000000000ffffc0000000000000000000000, 90), (0xfffffffffff803ffffffffffffffffffffff007ffffffffffffffffffffffffff803ffffffffffffffffffffff007fffffffffffffff, 0xff8000000000000000000000000000000000000000000000000000ff8000000000000000, 99), (0xfffffffff007ffffffffffffffffffffffffff803ffffffffffffffffffffff007ffffffffffffffffffffffffff803fffffffffffff, 0x7fc0000000000000000000000000000000000000000000000000007fc0000000000000, 117), (0x3ffffffffffffffffffffffffffc0000ffffffffffffffffff00003ffffffffffffffffffffffffffc0000ffffffffffffffffff, 0x3ffff00000000000000000000000000000000000000000000000003ffff000000000000000000, 126)], [(0x3ffffffffc0000ffffffffffffffffffffffffffffffffffff00003ffffffffc0000ffffffffffffffffffffffffffffffffffff, 0x7fc00000000001ff000000000000000000000000000000000000007fc00000000001ff000000000000000000000000000000000000, 9), (0xffffc000000003ffff000000000fffffffffffffffffffffffffffffffc000000003ffff000000000fffffffffffffffffffffffffff, 0xffffc000000003ffff000000000000000000000000000000000000ffffc000000003ffff000000000000000000000000000, 18), (0xfffffffffffffffffffffffffff000000000000000000000000000fffffffffffffffffffffffffff000000000000000000000000000, 0x3fffffffffffff00000000000000000000000000000000000000003fffffffffffff, 54)], [(0xfffffffff00003ffff00003ffffffffc0000ffffc0000ffffffffffffffffff00003ffff00003ffffffffc0000ffffc0000fffffffff, 0xffffc000000000000000003ffff000000000000000000000000000ffffc000000000000000003ffff000000000, 36), (0xff803ffffffffc01ffffffffffffffffffffff803ffffffffc01ffff803ffffffffc01ffffffffffffffffffffff803ffffffffc01ff, 0x3fe0000000000000000000000000000000003fe0000000000000003fe0000000000000000000000000000000003fe00, 45), (0x7ffffffffffffe00ffffffffffffffffff007ffffffffffffe00007ffffffffffffe00ffffffffffffffffff007ffffffffffffe00, 0x1ff0000000000000000000000000000000001ff0000000000000001ff0000000000000000000000000000000001ff, 63), (0xffffc0000fffffffffffffc000000003fffffffffffff00003ffffffffc0000fffffffffffffc000000003fffffffffffff00003ffff, 0x3ffff000000000000000000ffffc000000000000000000000000003ffff000000000000000000ffffc0000, 72)], [(0xff80001fffffffffffffffffffffffffffffffffffffffffffffffff80001fffffffffffffffffffffffffffffffffffffffffffffff, 0x3fe0000000000000000000000000000000000000000000000000003fe00000000000000000000000000000000000000000000000, 9), (0x7fffe00fffffffffffffffffffffffffffffffffffffffffffff007fffe00fffffffffffffffffffffffffffffffffffffffffffff, 0x1ff0000000000000000000000000000000000000000000000000001ff000000000000000000000000000000000000000000000, 27), (0xffffffffffffffffffffffc0000ffffc0000ffffffffffffffffffffffffffffffffffffffffc0000ffffc0000ffffffffffffffffff, 0x3ffff00000000000000000000000000000000000000000000000003ffff000000000000000000, 36), (0xfffffffffffffffe00fffffffff007fffffffffffffffffffffffffffffffffffffffe00fffffffff007ffffffffffffffffffffffff, 0xff8000000000000000000000000000000000000000000000000000ff8000000000000000000000000, 45), (0xfffffffffffffc01fffffffffffff803fffffffffffffffffffffffffffffffffffc01fffffffffffff803ffffffffffffffffffffff, 0x7fc0000000000000000000000000000000000000000000000000007fc0000000000000000000000, 63), (0xffffffffffffffffff00003fffffffffffff00003fffffffffffffffffffffffffffffff00003fffffffffffff00003fffffffffffff, 0xffffc0000000000000000000000000000000000000000000000000ffffc0000000000000, 72), (0x3ffff00003ffffffffffffffffffffffffffffffffffffffff00003ffff00003ffffffffffffffffffffffffffffffffffffffff, 0xffffc0000000000000000000000000000000000000000000000000ffffc0000000000000000000000000000000000000000, 36), (0xfffffffffffffc0000000000000fffffffffffffc0000000000000fffffffffffffc0000000000000fffffffffffffc0000000000000, 0x3fffffffffffff00000000000000000000000000000000000000003fffffffffffff, 108)], [(0xffffffe00ff803fffffffffffff007fc01ffffffffffffffffffffffffffe00ff803fffffffffffff007fc01ffffffffffffffffffff, 0xff803fe00000000000000000000000000000000000000000000000ff803fe00000000000000000000, 81), (0xffffc01ff007fffffffffffffffff803fe00ffffffffffffffffffffffc01ff007fffffffffffffffff803fe00ffffffffffffffffff, 0x7fc01ff000000000000000000000000000000000000000000000007fc01ff000000000000000000, 99), (0x3fffffffffffffffffffffffffffffff00003fffffffffffff00003fffffffffffffffffffffffffffffff00003fffffffffffff, 0xffffc0000000000000000000000000000000000000000000000000ffffc0000000000000, 144), (0xffffffffffffffffffffffc000000003ffffffffffffffffffffffffffffffffffffffffffffc000000003ffffffffffffffffffffff, 0xffffc0000000000000000000000000000000000000000000000000ffffc0000000000000000000000, 18), (0xfffffffffffffffe00ff803ffffffffc01ff007ffffffffffffffffffffffffffffffe00ff803ffffffffc01ff007fffffffffffffff, 0x3fe00ff800000000000000000000000000000000000000000000003fe00ff8000000000000000, 63), (0xfffffffffffffc01ff007ffffffffffffe00ff803ffffffffffffffffffffffffffc01ff007ffffffffffffe00ff803fffffffffffff, 0x1ff007fc00000000000000000000000000000000000000000000001ff007fc0000000000000, 81), (0x3ffffffffffffffffffffffffffc000000000000000000000000003ffffffffffffffffffffffffffc0000000000000, 0x3fffffffffffff00000000000000000000000000000000000000003fffffffffffff, 162)], [(0xffffffffffffffffffffffffe00007ffffffffffffffffffffffffffffffffffffffffffffffffe00007ffffffffffffffffffffffff, 0xff8000000000000000000000000000000000000000000000000000ff8000000000000000000000000, 9), (0xffffffffffffffffffffffc01ffff803ffffffffffffffffffffffffffffffffffffffffffffc01ffff803ffffffffffffffffffffff, 0x7fc0000000000000000000000000000000000000000000000000007fc0000000000000000000000, 27), (0xffffffffffffffffffff803ffffffffc01ffffffffffffffffffffffffffffffffffffffff803ffffffffc01ffffffffffffffffffff, 0x3fe0000000000000000000000000000000000000000000000000003fe00000000000000000000, 45), (0xffffffffffffffffff007ffffffffffffe00ffffffffffffffffffffffffffffffffffff007ffffffffffffe00ffffffffffffffffff, 0x1ff0000000000000000000000000000000000000000000000000001ff000000000000000000, 63), (0xfffffffffffffffe00ffffffffffffffffff007ffffffffffffffffffffffffffffffe00ffffffffffffffffff007fffffffffffffff, 0xff8000000000000000000000000000000000000000000000000000ff8000000000000000, 81), (0xfffffffffffffc01ffffffffffffffffffffff803ffffffffffffffffffffffffffc01ffffffffffffffffffffff803fffffffffffff, 0x7fc0000000000000000000000000000000000000000000000000007fc0000000000000, 99), (0xfffffffff00003ffff00003ffffffffc0000ffffc0000ffffffffffffffffff00003ffff00003ffffffffc0000ffffc0000fffffffff, 0x3ffff00003ffff00000000000000000000000000000000000000003ffff00003ffff000000000, 90), (0xff803fffffffffffffffffffe00007fffffffffffffffffffc01ffff803fffffffffffffffffffe00007fffffffffffffffffffc01ff, 0xff800000000000000000003fe00000000000000000000000000000ff800000000000000000003fe00, 99), (0x7fffffffffffffffffffc01ffff803fffffffffffffffffffe00007fffffffffffffffffffc01ffff803fffffffffffffffffffe00, 0x7fc00000000000000000001ff000000000000000000000000000007fc00000000000000000001ff, 117), (0xffffc0000ffffc0000ffffffffffffffffff00003ffff00003ffffffffc0000ffffc0000ffffffffffffffffff00003ffff00003ffff, 0xffffc0000ffffc0000000000000000000000000000000000000000ffffc0000ffffc0000, 126)], [(0xfffffffffffffffe00007ffffffffffffffffffffffffffffffffffffffffffffffffe00007fffffffffffffffffffffffffffffffff, 0xff8000000000000000000000000000000000000000000000000000ff8000000000000000000000000000000000, 9), (0xfffffffffffffc01ffff803ffffffffffffffffffffffffffffffffffffffffffffc01ffff803fffffffffffffffffffffffffffffff, 0x7fc0000000000000000000000000000000000000000000000000007fc0000000000000000000000000000000, 27), (0xfffffffff00003fffffffffffff00003fffffffffffffffffffffffffffffff00003fffffffffffff00003ffffffffffffffffffffff, 0xffffc0000000000000000000000000000000000000000000000000ffffc0000000000000000000000, 72), (0xff803fe00ffffffffffffffffffffffc01ff007fffffffffffffffff803fe00ffffffffffffffffffffffc01ff007fffffffffffffff, 0x3fe00ff800000000000000000000000000000000000000000000003fe00ff8000000000000000, 117), (0x7fc01ffffffffffffffffffffffffffe00ff803fffffffffffff007fc01ffffffffffffffffffffffffffe00ff803fffffffffffff, 0x1ff007fc00000000000000000000000000000000000000000000001ff007fc0000000000000, 135), (0xfffffffffffffc0000ffffc0000ffffffffffffffffffffffffffffffffffffffffc0000ffffc0000fffffffffffffffffffffffffff, 0x3ffff00000000000000000000000000000000000000000000000003ffff000000000000000000000000000, 36), (0xffffc0000fffffffffffffffffffffffffffffffc0000fffffffffffffc0000fffffffffffffffffffffffffffffffc0000fffffffff, 0x3ffff00000000000000000000000000000000000000000000000003ffff000000000, 144), (0xfffffffffff803fffffffffffffffffffffffffffffffffffc01fffffffffffff803fffffffffffffffffffffffffffffffffffc01ff, 0x3fe0000000000000000000000000000000000000000000000000003fe00, 153), (0xfffffffff007fffffffffffffffffffffffffffffffffffffffe00fffffffff007fffffffffffffffffffffffffffffffffffffffe00, 0x1ff0000000000000000000000000000000000000000000000000001ff, 171), (0x3ffffffffffffffffffffffffffffffffffffffff00003ffff00003ffffffffffffffffffffffffffffffffffffffff00003ffff, 0xffffc0000000000000000000000000000000000000000000000000ffffc0000, 180)], [(0xff80001fffffffffffffffffffffffffffffffffffffffffffffffff80001fffffffffffffffffffffffffffffffffffffffffffffff, 0x3fe0000000000000000000000000000000000000000000000000003fe00000000000000000000000000000000000000000000000, 9), (0x7fffe00fffffffffffffffffffffffffffffffffffffffffffff007fffe00fffffffffffffffffffffffffffffffffffffffffffff, 0x1ff0000000000000000000000000000000000000000000000000001ff000000000000000000000000000000000000000000000, 27), (0xffffffffffffffffffffffc0000ffffc0000ffffffffffffffffffffffffffffffffffffffffc0000ffffc0000ffffffffffffffffff, 0x3ffff00000000000000000000000000000000000000000000000003ffff000000000000000000, 36), (0xfffffffffffffffe00fffffffff007fffffffffffffffffffffffffffffffffffffffe00fffffffff007ffffffffffffffffffffffff, 0xff8000000000000000000000000000000000000000000000000000ff8000000000000000000000000, 45), (0xfffffffffffffc01fffffffffffff803fffffffffffffffffffffffffffffffffffc01fffffffffffff803ffffffffffffffffffffff, 0x7fc0000000000000000000000000000000000000000000000000007fc0000000000000000000000, 63), (0xffffffffffffffffff00003fffffffffffff00003fffffffffffffffffffffffffffffff00003fffffffffffff00003fffffffffffff, 0xffffc0000000000000000000000000000000000000000000000000ffffc0000000000000, 72), (0xffffffe00007ffffffffffffffffffffffffffffffffffffffffffffffffe00007ffffffffffffffffffffffffffffffffffffffffff, 0xff8000000000000000000000000000000000000000000000000000ff8000000000000000000000000000000000000000000, 9), (0xffffc01ffff803ffffffffffffffffffffffffffffffffffffffffffffc01ffff803ffffffffffffffffffffffffffffffffffffffff, 0x7fc0000000000000000000000000000000000000000000000000007fc0000000000000000000000000000000000000000, 27), (0xffffffffffffffffffffffffffffffffffff00003ffff00003ffffffffffffffffffffffffffffffffffffffff00003ffff00003ffff, 0xffffc0000000000000000000000000000000000000000000000000ffffc0000, 36), (0xfffffffffffffffffffffffffffff803ffffffffc01ffffffffffffffffffffffffffffffffffffffff803ffffffffc01fffffffffff, 0x3fe0000000000000000000000000000000000000000000000000003fe00000000000, 45), (0xfffffffffffffffffffffffffff007ffffffffffffe00ffffffffffffffffffffffffffffffffffff007ffffffffffffe00fffffffff, 0x1ff0000000000000000000000000000000000000000000000000001ff000000000, 63), (0xfffffffffffffffffffffffffffffffc0000fffffffffffffc0000fffffffffffffffffffffffffffffffc0000fffffffffffffc0000, 0x3ffff00000000000000000000000000000000000000000000000003ffff, 72)], [(0xffffffffffffffffffffffffe00007ffffffffffffffffffffffffffffffffffffffffffffffffe00007ffffffffffffffffffffffff, 0xff8000000000000000000000000000000000000000000000000000ff8000000000000000000000000, 9), (0xffffffffffffffffffffffc01ffff803ffffffffffffffffffffffffffffffffffffffffffffc01ffff803ffffffffffffffffffffff, 0x7fc0000000000000000000000000000000000000000000000000007fc0000000000000000000000, 27), (0xffffffffffffffffffff803ffffffffc01ffffffffffffffffffffffffffffffffffffffff803ffffffffc01ffffffffffffffffffff, 0x3fe0000000000000000000000000000000000000000000000000003fe00000000000000000000, 45), (0xffffffffffffffffff007ffffffffffffe00ffffffffffffffffffffffffffffffffffff007ffffffffffffe00ffffffffffffffffff, 0x1ff0000000000000000000000000000000000000000000000000001ff000000000000000000, 63), (0xfffffffffffffffe00ffffffffffffffffff007ffffffffffffffffffffffffffffffe00ffffffffffffffffff007fffffffffffffff, 0xff8000000000000000000000000000000000000000000000000000ff8000000000000000, 81), (0xfffffffffffffc01ffffffffffffffffffffff803ffffffffffffffffffffffffffc01ffffffffffffffffffffff803fffffffffffff, 0x7fc0000000000000000000000000000000000000000000000000007fc0000000000000, 99), (0xffffffe00ff80001ff007ffffffffffffe00ff80001ff007ffffffffffffe00ff80001ff007ffffffffffffe00ff80001ff007ffffff, 0x3fe00ff800000000000000000003fe00ff800000000000000000003fe00ff800000000000000000003fe00ff8000000, 27), (0xffffc01ff007fffe00ff803ffffffffc01ff007fffe00ff803ffffffffc01ff007fffe00ff803ffffffffc01ff007fffe00ff803ffff, 0x1ff007fc00000000000000000001ff007fc00000000000000000001ff007fc00000000000000000001ff007fc0000, 45), (0x3fffffffffffffffffc000000003fffffffffffffffffc000000003fffffffffffffffffc000000003fffffffffffffffffc0000, 0x3ffff00000000000000000000003ffff00000000000000000000003ffff00000000000000000000003ffff, 90)], [(0xffffc0000ffffffffffffffffff00003ffffffffffffffffffffffffffc0000ffffffffffffffffff00003ffffffffffffffffffffff, 0x1ff000000000000000000007fc00000000000000000000000000001ff000000000000000000007fc0000000000000000000000, 9), (0xfffffffffffffffffffffffffffffffc000000003ffffffffffffffffffffffffffffffffffffffffffffc000000003fffffffffffff, 0xffffc0000000000000000000000000000000000000000000000000ffffc0000000000000, 18), (0xff803ffff007ffffffffffffffffffffffffffffffffffffffffffff803ffff007ffffffffffffffffffffffffffffffffffffffffff, 0xff8000000000000000000000000000000000000000000000000000ff8000000000000000000000000000000000000000000, 27), (0x7ffffffff803ffffffffffffffffffffffffffffffffffffffff007ffffffff803ffffffffffffffffffffffffffffffffffffffff, 0x7fc0000000000000000000000000000000000000000000000000007fc0000000000000000000000000000000000000000, 45), (0xffffffffffffffffffffffc0000ffffffffffffffffff00003ffffffffffffffffffffffffffc0000ffffffffffffffffff00003ffff, 0xffffc0000000000000000000000000000000000000000000000000ffffc0000, 90), (0xfffffffffffffffe00ffffffffffffffffffffffc01ffffffffffffffffffffffffffe00ffffffffffffffffffffffc01fffffffffff, 0x3fe0000000000000000000000000000000000000000000000000003fe00000000000, 99), (0xfffffffffffffc01ffffffffffffffffffffffffffe00ffffffffffffffffffffffc01ffffffffffffffffffffffffffe00fffffffff, 0x1ff0000000000000000000000000000000000000000000000000001ff000000000, 117), (0xffffffffffffffffff00003ffffffffffffffffffffffffffc0000ffffffffffffffffff00003ffffffffffffffffffffffffffc0000, 0x3ffff00000000000000000000000000000000000000000000000003ffff, 126)], [(0xfffffffffff80001fffffffffffff80001fffffffffffffffffffffffffffffff80001fffffffffffff80001ffffffffffffffffffff, 0x3fe0000000000000003fe0000000000000000000000000000000003fe0000000000000003fe00000000000000000000, 9), (0xfffffffff007fffe00fffffffff007fffe00fffffffffffffffffffffffffff007fffe00fffffffff007fffe00ffffffffffffffffff, 0x1ff0000000000000001ff0000000000000000000000000000000001ff0000000000000001ff000000000000000000, 27), (0xffffffe00fffffffff007fffffffffffffffffffffffffffffffffffffffe00fffffffff007fffffffffffffffffffffffffffffffff, 0xff8000000000000000000000000000000000000000000000000000ff8000000000000000000000000000000000, 45), (0xffffc01fffffffffffff803fffffffffffffffffffffffffffffffffffc01fffffffffffff803fffffffffffffffffffffffffffffff, 0x7fc0000000000000000000000000000000000000000000000000007fc0000000000000000000000000000000, 63), (0xff803fffffffffffffffffc01fffffffffffffffffffffffffffffff803fffffffffffffffffc01fffffffffffffffffffffffffffff, 0x3fe0000000000000000000000000000000000000000000000000003fe00000000000000000000000000000, 81), (0x7fffffffffffffffffffffe00fffffffffffffffffffffffffff007fffffffffffffffffffffe00fffffffffffffffffffffffffff, 0x1ff0000000000000000000000000000000000000000000000000001ff000000000000000000000000000, 99), (0xfffffffffffffffffffffffffff00003ffff00003ffffffffffffffffffffffffffffffffffffffff00003ffff00003fffffffffffff, 0xffffc0000000000000000000000000000000000000000000000000ffffc0000000000000, 36), (0xfffffffff00003fffffffffffffffffffffffffffffff00003fffffffffffff00003fffffffffffffffffffffffffffffff00003ffff, 0xffffc0000000000000000000000000000000000000000000000000ffffc0000, 144), (0xff803fffffffffffffffffffffffffffffffffffc01fffffffffffff803fffffffffffffffffffffffffffffffffffc01fffffffffff, 0x3fe0000000000000000000000000000000000000000000000000003fe00000000000, 153), (0x7fffffffffffffffffffffffffffffffffffffffe00fffffffff007fffffffffffffffffffffffffffffffffffffffe00fffffffff, 0x1ff0000000000000000000000000000000000000000000000000001ff000000000, 171), (0xffffc0000ffffffffffffffffffffffffffffffffffffffffc0000ffffc0000ffffffffffffffffffffffffffffffffffffffffc0000, 0x3ffff00000000000000000000000000000000000000000000000003ffff, 180)], [(0xffffffe00ff803ffffff803fe00007fc01ffffffc01ff007ffffffffffffe00ff803ffffff803fe00007fc01ffffffc01ff007ffffff, 0xff803fe0000003fe00ff8000000000000000000000000000000000ff803fe0000003fe00ff8000000, 81), (0xffffc01ff007ffffff007fc01ffff803fe00ffffffe00ff803ffffffffc01ff007ffffff007fc01ffff803fe00ffffffe00ff803ffff, 0x7fc01ff0000001ff007fc0000000000000000000000000000000007fc01ff0000001ff007fc0000, 99), (0x3ffffffffc0000ffffffffffffffffff00003ffffffffc000000003ffffffffc0000ffffffffffffffffff00003ffffffffc0000, 0xffffc000000003ffff000000000000000000000000000000000000ffffc000000003ffff, 144)], [(0xfffffffff00003ffff00003ffffffffffffffffffffffffffffffffffffffff00003ffff00003fffffffffffffffffffffffffffffff, 0xffffc0000000000000000000000000000000000000000000000000ffffc0000000000000000000000000000000, 36), (0xff803ffffffffc01ffffffffffffffffffffffffffffffffffffffff803ffffffffc01ffffffffffffffffffffffffffffffffffffff, 0x3fe0000000000000000000000000000000000000000000000000003fe00000000000000000000000000000000000000, 45), (0x7ffffffffffffe00ffffffffffffffffffffffffffffffffffff007ffffffffffffe00ffffffffffffffffffffffffffffffffffff, 0x1ff0000000000000000000000000000000000000000000000000001ff000000000000000000000000000000000000, 63), (0xffffc0000fffffffffffffc0000fffffffffffffffffffffffffffffffc0000fffffffffffffc0000fffffffffffffffffffffffffff, 0x3ffff00000000000000000000000000000000000000000000000003ffff000000000000000000000000000, 72), (0xffffffffffffffffffff803fe00007fc01ffffffffffffffffffffffffffffffffffffffff803fe00007fc01ffffffffffffffffffff, 0xff803fe00000000000000000000000000000000000000000000000ff803fe00000000000000000000, 27), (0xffffffffffffffffff007fc01ffff803fe00ffffffffffffffffffffffffffffffffffff007fc01ffff803fe00ffffffffffffffffff, 0x7fc01ff000000000000000000000000000000000000000000000007fc01ff000000000000000000, 45), (0xfffffffffffffc0000ffffffffffffffffff00003ffffffffffffffffffffffffffc0000ffffffffffffffffff00003fffffffffffff, 0xffffc0000000000000000000000000000000000000000000000000ffffc0000000000000, 90), (0xffffffe00ff803ffffffffffffffffffffffffffc01ff007ffffffffffffe00ff803ffffffffffffffffffffffffffc01ff007ffffff, 0x3fe00ff800000000000000000000000000000000000000000000003fe00ff8000000, 135), (0xffffc01ff007ffffffffffffffffffffffffffffffe00ff803ffffffffc01ff007ffffffffffffffffffffffffffffffe00ff803ffff, 0x1ff007fc00000000000000000000000000000000000000000000001ff007fc0000, 153), (0x3ffffffffffffffffffffffffffffffffffffffffffffc000000003ffffffffffffffffffffffffffffffffffffffffffffc0000, 0x3ffff00000000000000000000000000000000000000000000000003ffff, 198)], [(0xffffffe00ff803fffffffffffff007fc01ffffffffffffffffffffffffffe00ff803fffffffffffff007fc01ffffffffffffffffffff, 0xff803fe00000000000000000000000000000000000000000000000ff803fe00000000000000000000, 81), (0xffffc01ff007fffffffffffffffff803fe00ffffffffffffffffffffffc01ff007fffffffffffffffff803fe00ffffffffffffffffff, 0x7fc01ff000000000000000000000000000000000000000000000007fc01ff000000000000000000, 99), (0x3fffffffffffffffffffffffffffffff00003fffffffffffff00003fffffffffffffffffffffffffffffff00003fffffffffffff, 0xffffc0000000000000000000000000000000000000000000000000ffffc0000000000000, 144), (0xfffffffff000000000ffffffffffffffffff000000000ffffffffffffffffff000000000ffffffffffffffffff000000000fffffffff, 0x3ffff00000000000000000000003ffff00000000000000000000003ffff00000000000000000000003ffff000000000, 18), (0xff803fe00fffffffff007fc01ffff803fe00fffffffff007fc01ffff803fe00fffffffff007fc01ffff803fe00fffffffff007fc01ff, 0xff803fe00000000000000000000ff803fe00000000000000000000ff803fe00000000000000000000ff803fe00, 63), (0x7fc01fffffffffffff803fe00007fc01fffffffffffff803fe00007fc01fffffffffffff803fe00007fc01fffffffffffff803fe00, 0x7fc01ff000000000000000000007fc01ff000000000000000000007fc01ff000000000000000000007fc01ff, 81)], [(0xfffffffffffffffe00007ffffffffffffffffffffffffffffffffffffffffffffffffe00007fffffffffffffffffffffffffffffffff, 0xff8000000000000000000000000000000000000000000000000000ff8000000000000000000000000000000000, 9), (0xfffffffffffffc01ffff803ffffffffffffffffffffffffffffffffffffffffffffc01ffff803fffffffffffffffffffffffffffffff, 0x7fc0000000000000000000000000000000000000000000000000007fc0000000000000000000000000000000, 27), (0xfffffffff00003fffffffffffff00003fffffffffffffffffffffffffffffff00003fffffffffffff00003ffffffffffffffffffffff, 0xffffc0000000000000000000000000000000000000000000000000ffffc0000000000000000000000, 72), (0xff803fe00ffffffffffffffffffffffc01ff007fffffffffffffffff803fe00ffffffffffffffffffffffc01ff007fffffffffffffff, 0x3fe00ff800000000000000000000000000000000000000000000003fe00ff8000000000000000, 117), (0x7fc01ffffffffffffffffffffffffffe00ff803fffffffffffff007fc01ffffffffffffffffffffffffffe00ff803fffffffffffff, 0x1ff007fc00000000000000000000000000000000000000000000001ff007fc0000000000000, 135), (0xffffffffffffffffffff80001fffffffffffff80001fffffffffffffffffffffffffffffff80001fffffffffffff80001fffffffffff, 0x3fe0000000000000003fe0000000000000000000000000000000003fe0000000000000003fe00000000000, 9), (0xffffffffffffffffff007fffe00fffffffff007fffe00fffffffffffffffffffffffffff007fffe00fffffffff007fffe00fffffffff, 0x1ff0000000000000001ff0000000000000000000000000000000001ff0000000000000001ff000000000, 27), (0xfffffffffffffffffffffffffffffffffe00fffffffff007fffffffffffffffffffffffffffffffffffffffe00fffffffff007ffffff, 0xff8000000000000000000000000000000000000000000000000000ff8000000, 45), (0xfffffffffffffffffffffffffffffffc01fffffffffffff803fffffffffffffffffffffffffffffffffffc01fffffffffffff803ffff, 0x7fc0000000000000000000000000000000000000000000000000007fc0000, 63), (0xfffffffffffffffffffffffffffff803fffffffffffffffffc01fffffffffffffffffffffffffffffff803fffffffffffffffffc01ff, 0x3fe0000000000000000000000000000000000000000000000000003fe00, 81), (0xfffffffffffffffffffffffffff007fffffffffffffffffffffe00fffffffffffffffffffffffffff007fffffffffffffffffffffe00, 0x1ff0000000000000000000000000000000000000000000000000001ff, 99)], [(0xfffffffffff80001fffffffffffff80001fffffffffffffffffffffffffffffff80001fffffffffffff80001ffffffffffffffffffff, 0x3fe0000000000000003fe0000000000000000000000000000000003fe0000000000000003fe00000000000000000000, 9), (0xfffffffff007fffe00fffffffff007fffe00fffffffffffffffffffffffffff007fffe00fffffffff007fffe00ffffffffffffffffff, 0x1ff0000000000000001ff0000000000000000000000000000000001ff0000000000000001ff000000000000000000, 27), (0xffffffe00fffffffff007fffffffffffffffffffffffffffffffffffffffe00fffffffff007fffffffffffffffffffffffffffffffff, 0xff8000000000000000000000000000000000000000000000000000ff8000000000000000000000000000000000, 45), (0xffffc01fffffffffffff803fffffffffffffffffffffffffffffffffffc01fffffffffffff803fffffffffffffffffffffffffffffff, 0x7fc0000000000000000000000000000000000000000000000000007fc0000000000000000000000000000000, 63), (0xff803fffffffffffffffffc01fffffffffffffffffffffffffffffff803fffffffffffffffffc01fffffffffffffffffffffffffffff, 0x3fe0000000000000000000000000000000000000000000000000003fe00000000000000000000000000000, 81), (0x7fffffffffffffffffffffe00fffffffffffffffffffffffffff007fffffffffffffffffffffe00fffffffffffffffffffffffffff, 0x1ff0000000000000000000000000000000000000000000000000001ff000000000000000000000000000, 99), (0xfffffffffffffffffffffffffffffffffe00007ffffffffffffffffffffffffffffffffffffffffffffffffe00007fffffffffffffff, 0xff8000000000000000000000000000000000000000000000000000ff8000000000000000, 9), (0xfffffffffffffffffffffffffffffffc01ffff803ffffffffffffffffffffffffffffffffffffffffffffc01ffff803fffffffffffff, 0x7fc0000000000000000000000000000000000000000000000000007fc0000000000000, 27), (0xffffffffffffffffffffffc0000fffffffffffffc0000fffffffffffffffffffffffffffffffc0000fffffffffffffc0000fffffffff, 0x3ffff00000000000000000000000000000000000000000000000003ffff000000000, 72), (0xfffffffffffffffe00ff803ffffffffffffffffffffff007fc01fffffffffffffffffe00ff803ffffffffffffffffffffff007fc01ff, 0xff803fe00000000000000000000000000000000000000000000000ff803fe00, 117), (0xfffffffffffffc01ff007ffffffffffffffffffffffffff803fe00fffffffffffffc01ff007ffffffffffffffffffffffffff803fe00, 0x7fc01ff000000000000000000000000000000000000000000000007fc01ff, 135)], [(0xffffffffffffffffff00003ffffffffc0000ffffffffffffffffffffffffffffffffffff00003ffffffffc0000ffffffffffffffffff, 0x7fc00000000001ff000000000000000000000000000000000000007fc00000000001ff000000000000000000, 9), (0xfffffffffffffffe00ffffc01ffff803ffff007ffffffffffffffffffffffffffffffe00ffffc01ffff803ffff007fffffffffffffff, 0x3fe00000000000ff800000000000000000000000000000000000003fe00000000000ff8000000000000000, 27), (0xfffffffffffffc01ffffffffe00007ffffffff803ffffffffffffffffffffffffffc01ffffffffe00007ffffffff803fffffffffffff, 0x1ff000000000007fc00000000000000000000000000000000000001ff000000000007fc0000000000000, 45), (0xfffffffff00003ffffffffffffffffffffffffffc0000ffffffffffffffffff00003ffffffffffffffffffffffffffc0000fffffffff, 0x3ffff00000000000000000000000000000000000000000000000003ffff000000000, 126), (0xff803fe00ffffffffffffffffffffffffffffffffffff007fc01ffff803fe00ffffffffffffffffffffffffffffffffffff007fc01ff, 0xff803fe00000000000000000000000000000000000000000000000ff803fe00, 171), (0x7fc01ffffffffffffffffffffffffffffffffffffffff803fe00007fc01ffffffffffffffffffffffffffffffffffffffff803fe00, 0x7fc01ff000000000000000000000000000000000000000000000007fc01ff, 189)], [(0xfffffffff00003ffff00003ffffffffffffffffffffffffffffffffffffffff00003ffff00003fffffffffffffffffffffffffffffff, 0xffffc0000000000000000000000000000000000000000000000000ffffc0000000000000000000000000000000, 36), (0xff803ffffffffc01ffffffffffffffffffffffffffffffffffffffff803ffffffffc01ffffffffffffffffffffffffffffffffffffff, 0x3fe0000000000000000000000000000000000000000000000000003fe00000000000000000000000000000000000000, 45), (0x7ffffffffffffe00ffffffffffffffffffffffffffffffffffff007ffffffffffffe00ffffffffffffffffffffffffffffffffffff, 0x1ff0000000000000000000000000000000000000000000000000001ff000000000000000000000000000000000000, 63), (0xffffc0000fffffffffffffc0000fffffffffffffffffffffffffffffffc0000fffffffffffffc0000fffffffffffffffffffffffffff, 0x3ffff00000000000000000000000000000000000000000000000003ffff000000000000000000000000000, 72), (0xfffffffffff803ffffffffffe00007ffffffffffc01ffffffffffffffffffffff803ffffffffffe00007ffffffffffc01fffffffffff, 0xff800000000003fe00000000000000000000000000000000000000ff800000000003fe00000000000, 63), (0xfffffffff007ffffffffffc01ffff803ffffffffffe00ffffffffffffffffff007ffffffffffc01ffff803ffffffffffe00fffffffff, 0x7fc00000000001ff000000000000000000000000000000000000007fc00000000001ff000000000, 81), (0xffffffe00fffffffffff803ffffffffc01fffffffffff007ffffffffffffe00fffffffffff803ffffffffc01fffffffffff007ffffff, 0x3fe00000000000ff800000000000000000000000000000000000003fe00000000000ff8000000, 99), (0xffffc01fffffffffff007ffffffffffffe00fffffffffff803ffffffffc01fffffffffff007ffffffffffffe00fffffffffff803ffff, 0x1ff000000000007fc00000000000000000000000000000000000001ff000000000007fc0000, 117), (0xff803ffffffffffe00ffffffffffffffffff007ffffffffffc01ffff803ffffffffffe00ffffffffffffffffff007ffffffffffc01ff, 0xff800000000003fe00000000000000000000000000000000000000ff800000000003fe00, 135), (0x7ffffffffffc01ffffffffffffffffffffff803ffffffffffe00007ffffffffffc01ffffffffffffffffffffff803ffffffffffe00, 0x7fc00000000001ff000000000000000000000000000000000000007fc00000000001ff, 153)], [(0xffffffffffffffffffffffffe00007ffffffffffffffffffffffffffffffffffffffffffffffffe00007ffffffffffffffffffffffff, 0xff8000000000000000000000000000000000000000000000000000ff8000000000000000000000000, 9), (0xffffffffffffffffffffffc01ffff803ffffffffffffffffffffffffffffffffffffffffffffc01ffff803ffffffffffffffffffffff, 0x7fc0000000000000000000000000000000000000000000000000007fc0000000000000000000000, 27), (0xffffffffffffffffffff803ffffffffc01ffffffffffffffffffffffffffffffffffffffff803ffffffffc01ffffffffffffffffffff, 0x3fe0000000000000000000000000000000000000000000000000003fe00000000000000000000, 45), (0xffffffffffffffffff007ffffffffffffe00ffffffffffffffffffffffffffffffffffff007ffffffffffffe00ffffffffffffffffff, 0x1ff0000000000000000000000000000000000000000000000000001ff000000000000000000, 63), (0xfffffffffffffffe00ffffffffffffffffff007ffffffffffffffffffffffffffffffe00ffffffffffffffffff007fffffffffffffff, 0xff8000000000000000000000000000000000000000000000000000ff8000000000000000, 81), (0xfffffffffffffc01ffffffffffffffffffffff803ffffffffffffffffffffffffffc01ffffffffffffffffffffff803fffffffffffff, 0x7fc0000000000000000000000000000000000000000000000000007fc0000000000000, 99), (0xfffffffffff803ffffffffffffffffffffffffffc01ffffffffffffffffffffff803ffffffffffffffffffffffffffc01fffffffffff, 0x3fe0000000000000000000000000000000000000000000000000003fe00000000000, 117), (0xfffffffff007ffffffffffffffffffffffffffffffe00ffffffffffffffffff007ffffffffffffffffffffffffffffffe00fffffffff, 0x1ff0000000000000000000000000000000000000000000000000001ff000000000, 135), (0xffffffe00ffffffffffffffffffffffffffffffffffff007ffffffffffffe00ffffffffffffffffffffffffffffffffffff007ffffff, 0xff8000000000000000000000000000000000000000000000000000ff8000000, 153), (0xffffc01ffffffffffffffffffffffffffffffffffffffff803ffffffffc01ffffffffffffffffffffffffffffffffffffffff803ffff, 0x7fc0000000000000000000000000000000000000000000000000007fc0000, 171), (0xff803ffffffffffffffffffffffffffffffffffffffffffffc01ffff803ffffffffffffffffffffffffffffffffffffffffffffc01ff, 0x3fe0000000000000000000000000000000000000000000000000003fe00, 189), (0x7ffffffffffffffffffffffffffffffffffffffffffffffffe00007ffffffffffffffffffffffffffffffffffffffffffffffffe00, 0x1ff0000000000000000000000000000000000000000000000000001ff, 207)]]

theorem ELG_ok : ELG.all (fun l => l.all (okT 216)) = true := by decide +kernel

def blkG (X g : Nat) : Nat :=
  ((X >>> (9 * g)) &&& 511) ||| (((X >>> (216 + 9 * g)) &&& 511) <<< 9)

def fpw (zs : List Nat) (g : Nat) : Nat := (zs.map fun w => hw (blkG w g)).sum

def keyG (zs : List Nat) (m g : Nat) : Nat :=
  if fpw zs g = m then hk (appL (ELG.getD g []) zs) else 2 ^ 64

def ori (zs : List Nat) : List Nat :=
  appL (ELG.getD (amin (keyG zs (fpw zs (amin (fpw zs) 23 0 1))) 23 0 1) []) zs

theorem ori_ok {u ys} (h : NatRun 0 (goal 216) u ys) : NatRun 0 (goal 216) u (ori ys) :=
  appL_run _ (getD_all ELG_ok _) h

def St : Nat → Nat → Nat → List Nat
  | 0, _, _ => xsG
  | d + 1, s, j =>
    let e := fld (PT s) 27 j
    appL (ELG.getD (e / 4096 % 32) []) (mv 0 (e % 4096) (St d (s + 1) (e / 131072)))

def S (s j : Nat) : List Nat := St (14 - s) s j

def idx (s : Nat) (zs : List Nat) : Nat := bsr (HT s) 32 (hk zs) 20 0 (NN s)

def poolG : List Nat := [0x80000544360ea, 0x34000057a360fc, 0x4000090e3a8d8, 0x800035443f0ea, 0x40000d203610e, 0x200003544360ea, 0xc00031564c920, 0x1c000058c43932, 0xc000094448156, 0x14000099e51168, 0x80002d443f0ea, 0x4000190e3f0d8, 0x400031323610e, 0x80000d563a944, 0x40002d0e3f0d8]

def Z (s : Nat) := barM 216 S NN idx ori poolG s

end PEqualNP.Outside.L_meta_583_aux

namespace PEqualNP.Outside.L_meta_583_aux

theorem h14y0 : span (Z 14) 1 0 = true := by decide +kernel
theorem z14 : span (Z 14) 1 0 = true := h14y0
theorem h13y0 : span (Z 13) 12 0 = true := by decide +kernel
theorem z13 : span (Z 13) 12 0 = true := h13y0
theorem h12y0 : span (Z 12) 40 0 = true := by decide +kernel
theorem h12y1 : span (Z 12) 40 40 = true := by decide +kernel
theorem h12y2 : span (Z 12) 40 80 = true := by decide +kernel
theorem h12y3 : span (Z 12) 40 120 = true := by decide +kernel
theorem h12y4 : span (Z 12) 40 160 = true := by decide +kernel
theorem h12y5 : span (Z 12) 40 200 = true := by decide +kernel
theorem h12y6 : span (Z 12) 40 240 = true := by decide +kernel
theorem h12y7 : span (Z 12) 40 280 = true := by decide +kernel
theorem h12y8 : span (Z 12) 40 320 = true := by decide +kernel
theorem h12y9 : span (Z 12) 40 360 = true := by decide +kernel
theorem h12y10 : span (Z 12) 11 400 = true := by decide +kernel
theorem z12 : span (Z 12) 411 0 = true := (@span_join (Z 12) 320 0 91 (@span_join (Z 12) 160 0 160 (@span_join (Z 12) 80 0 80 (@span_join (Z 12) 40 0 40 h12y0 h12y1) (@span_join (Z 12) 40 80 40 h12y2 h12y3)) (@span_join (Z 12) 80 160 80 (@span_join (Z 12) 40 160 40 h12y4 h12y5) (@span_join (Z 12) 40 240 40 h12y6 h12y7))) (@span_join (Z 12) 80 320 11 (@span_join (Z 12) 40 320 40 h12y8 h12y9) h12y10))
theorem h11y0 : span (Z 11) 40 0 = true := by decide +kernel
theorem h11y1 : span (Z 11) 40 40 = true := by decide +kernel
theorem h11y2 : span (Z 11) 40 80 = true := by decide +kernel
theorem h11y3 : span (Z 11) 40 120 = true := by decide +kernel
theorem h11y4 : span (Z 11) 40 160 = true := by decide +kernel
theorem h11y5 : span (Z 11) 40 200 = true := by decide +kernel
theorem h11y6 : span (Z 11) 40 240 = true := by decide +kernel
theorem h11y7 : span (Z 11) 40 280 = true := by decide +kernel
theorem h11y8 : span (Z 11) 40 320 = true := by decide +kernel
theorem h11y9 : span (Z 11) 40 360 = true := by decide +kernel
theorem h11y10 : span (Z 11) 40 400 = true := by decide +kernel
theorem h11y11 : span (Z 11) 40 440 = true := by decide +kernel
theorem h11y12 : span (Z 11) 40 480 = true := by decide +kernel
theorem h11y13 : span (Z 11) 40 520 = true := by decide +kernel
theorem h11y14 : span (Z 11) 40 560 = true := by decide +kernel
theorem h11y15 : span (Z 11) 40 600 = true := by decide +kernel
theorem h11y16 : span (Z 11) 40 640 = true := by decide +kernel
theorem h11y17 : span (Z 11) 40 680 = true := by decide +kernel
theorem h11y18 : span (Z 11) 40 720 = true := by decide +kernel
theorem h11y19 : span (Z 11) 40 760 = true := by decide +kernel
theorem h11y20 : span (Z 11) 40 800 = true := by decide +kernel
theorem h11y21 : span (Z 11) 40 840 = true := by decide +kernel
theorem h11y22 : span (Z 11) 40 880 = true := by decide +kernel
theorem h11y23 : span (Z 11) 40 920 = true := by decide +kernel
theorem h11y24 : span (Z 11) 29 960 = true := by decide +kernel
theorem z11 : span (Z 11) 989 0 = true := (@span_join (Z 11) 640 0 349 (@span_join (Z 11) 320 0 320 (@span_join (Z 11) 160 0 160 (@span_join (Z 11) 80 0 80 (@span_join (Z 11) 40 0 40 h11y0 h11y1) (@span_join (Z 11) 40 80 40 h11y2 h11y3)) (@span_join (Z 11) 80 160 80 (@span_join (Z 11) 40 160 40 h11y4 h11y5) (@span_join (Z 11) 40 240 40 h11y6 h11y7))) (@span_join (Z 11) 160 320 160 (@span_join (Z 11) 80 320 80 (@span_join (Z 11) 40 320 40 h11y8 h11y9) (@span_join (Z 11) 40 400 40 h11y10 h11y11)) (@span_join (Z 11) 80 480 80 (@span_join (Z 11) 40 480 40 h11y12 h11y13) (@span_join (Z 11) 40 560 40 h11y14 h11y15)))) (@span_join (Z 11) 320 640 29 (@span_join (Z 11) 160 640 160 (@span_join (Z 11) 80 640 80 (@span_join (Z 11) 40 640 40 h11y16 h11y17) (@span_join (Z 11) 40 720 40 h11y18 h11y19)) (@span_join (Z 11) 80 800 80 (@span_join (Z 11) 40 800 40 h11y20 h11y21) (@span_join (Z 11) 40 880 40 h11y22 h11y23))) h11y24))
theorem h10y0 : span (Z 10) 40 0 = true := by decide +kernel
theorem h10y1 : span (Z 10) 40 40 = true := by decide +kernel
theorem h10y2 : span (Z 10) 40 80 = true := by decide +kernel
theorem h10y3 : span (Z 10) 40 120 = true := by decide +kernel
theorem h10y4 : span (Z 10) 40 160 = true := by decide +kernel
theorem h10y5 : span (Z 10) 40 200 = true := by decide +kernel
theorem h10y6 : span (Z 10) 40 240 = true := by decide +kernel
theorem h10y7 : span (Z 10) 40 280 = true := by decide +kernel
theorem h10y8 : span (Z 10) 40 320 = true := by decide +kernel
theorem h10y9 : span (Z 10) 40 360 = true := by decide +kernel
theorem h10y10 : span (Z 10) 40 400 = true := by decide +kernel
theorem h10y11 : span (Z 10) 40 440 = true := by decide +kernel
theorem h10y12 : span (Z 10) 29 480 = true := by decide +kernel
theorem z10 : span (Z 10) 509 0 = true := (@span_join (Z 10) 320 0 189 (@span_join (Z 10) 160 0 160 (@span_join (Z 10) 80 0 80 (@span_join (Z 10) 40 0 40 h10y0 h10y1) (@span_join (Z 10) 40 80 40 h10y2 h10y3)) (@span_join (Z 10) 80 160 80 (@span_join (Z 10) 40 160 40 h10y4 h10y5) (@span_join (Z 10) 40 240 40 h10y6 h10y7))) (@span_join (Z 10) 160 320 29 (@span_join (Z 10) 80 320 80 (@span_join (Z 10) 40 320 40 h10y8 h10y9) (@span_join (Z 10) 40 400 40 h10y10 h10y11)) h10y12))
theorem h9y0 : span (Z 9) 40 0 = true := by decide +kernel
theorem h9y1 : span (Z 9) 35 40 = true := by decide +kernel
theorem z9 : span (Z 9) 75 0 = true := (@span_join (Z 9) 40 0 35 h9y0 h9y1)
theorem z8 : span (Z 8) 0 0 = true := rfl
theorem z7 : span (Z 7) 0 0 = true := rfl
theorem z6 : span (Z 6) 0 0 = true := rfl
theorem z5 : span (Z 5) 0 0 = true := rfl
theorem z4 : span (Z 4) 0 0 = true := rfl
theorem z3 : span (Z 3) 0 0 = true := rfl
theorem z2 : span (Z 2) 0 0 = true := rfl
theorem z1 : span (Z 1) 0 0 = true := rfl
theorem z0 : span (Z 0) 0 0 = true := rfl

theorem checked (L : Nat) (hL : L ≤ 14) : ∀ i < NN L, Z L i = true := by
  interval_cases L
  · exact fun i hi => span_ok z0 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z1 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z2 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z3 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z4 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z5 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z6 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z7 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z8 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z9 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z10 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z11 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z12 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z13 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z14 i (Nat.zero_le i) hi

theorem noRun (s : Nat) (hs : s ≤ 14) (h : NatRun 0 (goal 216) s xsG) : False := by
  have p : xsG.Perm (S 14 0) := List.Perm.refl _
  exact barM_all ori_ok checked s 14 hs (le_refl _) 0 (by decide) (Run.perm p h)

theorem hasMono : ∀ s : ℕ, HasMono 10 fG s → 15 ≤ s := mainG noRun

theorem edge_iff (x : Fin 10 → Bool) :
    fG x = true ↔ ∃ u v : Fin 10, (u.val, v.val) ∈ ([(0, 4), (4, 1), (0, 5), (5, 2), (0, 6), (6, 3), (1, 7), (7, 2), (1, 8), (8, 3), (2, 9), (9, 3)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true := by
  constructor
  · intro h
    simp only [fG, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with (((((((((((h | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) <;> exact ⟨_, _, by decide, h.1, h.2⟩
  · rintro ⟨u, v, he, hu, hv⟩
    fin_cases u <;> fin_cases v <;> simp_all

theorem core : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C →
    (∀ x : Fin 10 → Bool, (C.eval (List.ofFn x) = true ↔
      ∃ u v : Fin 10, (u.val, v.val) ∈ ([(0, 4), (4, 1), (0, 5), (5, 2), (0, 6), (6, 3), (1, 7), (7, 2), (1, 8), (8, 3), (2, 9), (9, 3)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) →
    15 ≤ C.size := by
  intro C hC h
  apply hasMono C.size
  refine ⟨C, fun g hg => ?_, le_rfl, fun x => ?_⟩
  · have hop : g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or := by simpa using (hC g hg).1
    refine ⟨⟨?_, (hC g hg).2⟩, ?_⟩
    · rcases hop with h1 | h1 <;> rw [h1] <;> simp
    · rcases hop with h1 | h1 <;> rw [h1] <;> simp
  · rw [Bool.eq_iff_iff, edge_iff]
    exact h x

end PEqualNP.Outside.L_meta_583_aux

theorem PEqualNP.Outside.L_meta_583 : ¬ (
  ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 14 ∧ (∀ x : Fin 10 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 10, (u.val, v.val) ∈ ([(0, 4), (4, 1), (0, 5), (5, 2), (0, 6), (6, 3), (1, 7), (7, 2), (1, 8), (8, 3), (2, 9), (9, 3)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true))
) := by
  rintro ⟨C, h_monotone, h_size, h_eval⟩
  exact Nat.not_succ_le_self 14 (Nat.le_trans (PEqualNP.Outside.L_meta_583_aux.core C h_monotone h_eval) h_size)
