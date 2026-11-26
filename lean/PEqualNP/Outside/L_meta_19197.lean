import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19197
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents PEqualNP.EdgeOwnership

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def W (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

theorem W_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    W (g :: gs) w = W gs (step w g) := rfl

theorem W_append (a b : List Gate) (w : List Bool) : W (a ++ b) w = W b (W a w) := by
  simp [W, List.foldl_append]

theorem W_snoc (gs : List Gate) (g : Gate) (w : List Bool) : W (gs ++ [g]) w = step (W gs w) g := by
  rw [W_append]; rfl

theorem step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

theorem W_length (gs : List Gate) :
    ∀ w : List Bool, (W gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [W]
  | cons g gs ih =>
    intro w
    rw [W_cons, ih, step_len, List.length_cons]
    omega

theorem getD_app_lt (l l2 : List Bool) (i : ℕ) (h : i < l.length) :
    (l ++ l2).getD i false = l.getD i false := by
  simp [List.getD, List.getElem?_append_left h]

theorem getD_app_len (l : List Bool) (v : Bool) : (l ++ [v]).getD l.length false = v := by
  simp [List.getD]

theorem getD_ge (l : List Bool) (i : ℕ) (h : l.length ≤ i) : l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem step_lt (w : List Bool) (g : Gate) (i : ℕ) (h : i < w.length) :
    (step w g).getD i false = w.getD i false := getD_app_lt w _ i h

theorem step_last (w : List Bool) (g : Gate) (k : ℕ) (hk : k = w.length) :
    (step w g).getD k false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  subst hk; exact getD_app_len w _

theorem W_prefix (gs : List Gate) :
    ∀ (w : List Bool) (i : ℕ), i < w.length → (W gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    rw [W_cons, ih (step w g) i (by rw [step_len]; omega)]
    exact getD_app_lt w _ i hi

theorem W_ge (gs : List Gate) (w : List Bool) (i : ℕ) (h : w.length + gs.length ≤ i) :
    (W gs w).getD i false = false := getD_ge _ _ (by rw [W_length]; exact h)

theorem W_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (W gs w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (W gs w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [W_cons]
    cases j with
    | zero =>
      have h1 : w.length < (step w g).length := by simp [step]
      rw [Nat.add_zero, W_prefix gs (step w g) w.length h1]
      simp only [List.getElem_cons_zero]
      rw [step_last w g w.length rfl]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [if_pos hi, W_prefix gs (step w g) i (by simp [step]; omega)]
        exact (step_lt w g i hi).symm
      · rw [if_neg hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (step w g) j hj'
      have hl : (step w g).length = w.length + 1 := step_len w g
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

theorem ofFn_getD {n : ℕ} (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    (List.ofFn x).getD u false = x ⟨u, hu⟩ := by
  simp [List.getD_eq_getElem?_getD, hu]

theorem gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

theorem getElem?_gateAt {C : Circuit} {j : ℕ} {g : Gate} (h : C.gates[j]? = some g) :
    gateAt C j = g ∧ j < C.gates.length := by
  have hj : j < C.gates.length := by
    by_contra hc; rw [List.getElem?_eq_none (by omega)] at h; cases h
  refine ⟨?_, hj⟩
  rw [gateAt_eq hj]
  rw [List.getElem?_eq_getElem hj] at h
  exact Option.some.inj h

theorem eval_and_iff (l : List ℕ) (f : ℕ → Bool) :
    GateOp.and.eval (l.map f) = true ↔ ∀ i ∈ l, f i = true := by
  simp [GateOp.eval]

theorem eval_or_iff (l : List ℕ) (f : ℕ → Bool) :
    GateOp.or.eval (l.map f) = true ↔ ∃ i ∈ l, f i = true := by
  simp [GateOp.eval]

theorem eval_or2 (a b : Bool) : GateOp.or.eval [a, b] = (a || b) := by
  cases a <;> cases b <;> rfl

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

theorem W_range_or2 (gf : ℕ → Gate) (N : ℕ) (w : List Bool) (j p q : ℕ) (hj : j < N)
    (hg : gf j = ⟨GateOp.or, [p, q]⟩) (hp : p < w.length + j) (hq : q < w.length + j) :
    (W ((List.range N).map gf) w).getD (w.length + j) false =
      ((W ((List.range N).map gf) w).getD p false || (W ((List.range N).map gf) w).getD q false) := by
  have hj' : j < ((List.range N).map gf).length := by
    rw [List.length_map, List.length_range]; exact hj
  rw [W_gate _ w j hj']
  have e : ((List.range N).map gf)[j] = gf j := by
    rw [List.getElem_map, List.getElem_range]
  rw [e, hg]
  simp only [List.map_cons, List.map_nil, hp, hq, ↓reduceIte]
  exact eval_or2 _ _

def abP (a : ℕ → ℕ) (b j : ℕ) : ℕ := if j = 0 then a 0 else b + j - 1

def abS (a : ℕ → ℕ) (n b j : ℕ) : ℕ :=
  if j = n - 1 then a (n - 1) else b + (n - 2) + (n - 2 - j)

def abG (a : ℕ → ℕ) (n b k : ℕ) : Gate :=
  if k < n - 2 then ⟨GateOp.or, [abP a b k, a (k + 1)]⟩
  else if k < 2 * (n - 2) then
    ⟨GateOp.or, [a (n - 2 - (k - (n - 2))), abS a n b (n - 2 - (k - (n - 2)) + 1)]⟩
  else ⟨GateOp.or, [abP a b (k - 2 * (n - 2)), abS a n b (k - 2 * (n - 2) + 2)]⟩

def allbut (a : ℕ → ℕ) (n b : ℕ) : List Gate := (List.range (3 * (n - 2))).map (abG a n b)

def allbutW (a : ℕ → ℕ) (n b i : ℕ) : ℕ :=
  if i = 0 then abS a n b 1 else if i = n - 1 then abP a b (n - 2) else b + 2 * (n - 2) + (i - 1)

theorem allbut_len (a : ℕ → ℕ) (n b : ℕ) : (allbut a n b).length = 3 * (n - 2) := by
  unfold allbut
  rw [List.length_map, List.length_range]

theorem abP_lt (a : ℕ → ℕ) (n b j k : ℕ) (ha : ∀ t, t < n → a t < b) (hn : 2 ≤ n)
    (hjk : j ≤ k) : abP a b j < b + k := by
  have h0 := ha 0 (by omega)
  unfold abP
  split_ifs <;> omega

theorem abS_lt (a : ℕ → ℕ) (n b j k : ℕ) (ha : ∀ t, t < n → a t < b) (hn : 2 ≤ n)
    (hjk : (n - 2) + (n - 2 - j) < k ∨ j = n - 1) : abS a n b j < b + k := by
  have h0 := ha (n - 1) (by omega)
  unfold abS
  split_ifs <;> omega

theorem allbut_gate (a : ℕ → ℕ) (n b : ℕ) (g : Gate) (hg : g ∈ allbut a n b) :
    g.op = GateOp.or ∧ g.inputs.length = 2 := by
  unfold allbut at hg
  obtain ⟨k, _, rfl⟩ := List.mem_map.mp hg
  unfold abG
  split_ifs <;> exact ⟨rfl, rfl⟩

theorem abP_val (a : ℕ → ℕ) (n b : ℕ) (w : List Bool) (hw : w.length = b) (hn : 2 ≤ n)
    (ha : ∀ t, t < n → a t < b) : ∀ j, j ≤ n - 2 →
    ((W (allbut a n b) w).getD (abP a b j) false = true ↔
      ∃ t, t ≤ j ∧ w.getD (a t) false = true) := by
  intro j
  induction j with
  | zero =>
    intro _
    have e : abP a b 0 = a 0 := by unfold abP; simp only [↓reduceIte]
    rw [e, W_prefix _ _ _ (by rw [hw]; exact ha 0 (by omega))]
    constructor
    · intro h; exact ⟨0, le_refl 0, h⟩
    · rintro ⟨t, ht, h⟩
      have : t = 0 := by omega
      subst this; exact h
  | succ j ih =>
    intro hj
    have e : abP a b (j + 1) = w.length + j := by
      unfold abP
      have : j + 1 ≠ 0 := by omega
      simp only [this, ↓reduceIte]
      omega
    have hg : abG a n b j = ⟨GateOp.or, [abP a b j, a (j + 1)]⟩ := by
      unfold abG
      have : j < n - 2 := by omega
      simp only [this, ↓reduceIte]
    have hq : a (j + 1) < b := ha (j + 1) (by omega)
    have key := W_range_or2 (abG a n b) (3 * (n - 2)) w j _ _ (by omega) hg
      (by rw [hw]; exact abP_lt a n b j j ha hn (le_refl j)) (by omega)
    rw [e]
    unfold allbut
    rw [key]
    have ih' := ih (by omega)
    unfold allbut at ih'
    rw [Bool.or_eq_true, ih', W_prefix _ _ _ (by rw [hw]; exact hq)]
    constructor
    · rintro (⟨t, ht, h⟩ | h)
      · exact ⟨t, by omega, h⟩
      · exact ⟨j + 1, le_refl _, h⟩
    · rintro ⟨t, ht, h⟩
      by_cases htj : t ≤ j
      · exact Or.inl ⟨t, htj, h⟩
      · have : t = j + 1 := by omega
        subst this; exact Or.inr h

theorem abS_val (a : ℕ → ℕ) (n b : ℕ) (w : List Bool) (hw : w.length = b) (hn : 2 ≤ n)
    (ha : ∀ t, t < n → a t < b) : ∀ d, d ≤ n - 2 →
    ((W (allbut a n b) w).getD (abS a n b (n - 1 - d)) false = true ↔
      ∃ t, n - 1 - d ≤ t ∧ t < n ∧ w.getD (a t) false = true) := by
  intro d
  induction d with
  | zero =>
    intro _
    have e : abS a n b (n - 1 - 0) = a (n - 1) := by
      unfold abS; simp only [Nat.sub_zero, ↓reduceIte]
    rw [e, W_prefix _ _ _ (by rw [hw]; exact ha (n - 1) (by omega))]
    constructor
    · intro h; exact ⟨n - 1, by omega, by omega, h⟩
    · rintro ⟨t, ht, ht2, h⟩
      have : t = n - 1 := by omega
      subst this; exact h
  | succ d ih =>
    intro hd
    have e : abS a n b (n - 1 - (d + 1)) = w.length + ((n - 2) + d) := by
      unfold abS
      have : n - 1 - (d + 1) ≠ n - 1 := by omega
      simp only [this, ↓reduceIte]
      omega
    have e1 : n - 2 - ((n - 2) + d - (n - 2)) = n - 1 - (d + 1) := by omega
    have e2 : n - 1 - (d + 1) + 1 = n - 1 - d := by omega
    have hg : abG a n b ((n - 2) + d) =
        ⟨GateOp.or, [a (n - 1 - (d + 1)), abS a n b (n - 1 - d)]⟩ := by
      unfold abG
      have h1 : ¬ ((n - 2) + d < n - 2) := by omega
      have h2 : (n - 2) + d < 2 * (n - 2) := by omega
      simp only [h1, h2, ↓reduceIte, e1, e2]
    have hp : a (n - 1 - (d + 1)) < b := ha _ (by omega)
    have key := W_range_or2 (abG a n b) (3 * (n - 2)) w ((n - 2) + d) _ _ (by omega) hg
      (by omega)
      (by rw [hw]; exact abS_lt a n b _ _ ha hn (by omega))
    rw [e]
    unfold allbut
    rw [key]
    have ih' := ih (by omega)
    unfold allbut at ih'
    rw [Bool.or_eq_true, ih', W_prefix _ _ _ (by rw [hw]; exact hp)]
    constructor
    · rintro (h | ⟨t, ht, ht2, h⟩)
      · exact ⟨n - 1 - (d + 1), le_refl _, by omega, h⟩
      · exact ⟨t, by omega, ht2, h⟩
    · rintro ⟨t, ht, ht2, h⟩
      by_cases htj : n - 1 - d ≤ t
      · exact Or.inr ⟨t, htj, ht2, h⟩
      · have : t = n - 1 - (d + 1) := by omega
        subst this; exact Or.inl h

theorem allbutW_lt (a : ℕ → ℕ) (n b i : ℕ) (hn : 2 ≤ n) (hi : i < n)
    (ha : ∀ t, t < n → a t < b) : allbutW a n b i < b + (allbut a n b).length := by
  rw [allbut_len]
  have h0 := ha 0 (by omega)
  have h1 := ha (n - 1) (by omega)
  unfold allbutW abS abP
  split_ifs <;> omega

theorem ab_split (n i : ℕ) (Q : ℕ → Prop) (h0 : ¬ i = 0) (h1 : ¬ i = n - 1) (hi : i < n) :
    ((∃ t, t ≤ i - 1 ∧ Q t) ∨ (∃ t, n - 1 - (n - 2 - i) ≤ t ∧ t < n ∧ Q t)) ↔
      ∃ t, t < n ∧ t ≠ i ∧ Q t := by
  constructor
  · rintro (⟨t, ht, h⟩ | ⟨t, ht, ht2, h⟩)
    · exact ⟨t, by omega, by omega, h⟩
    · exact ⟨t, ht2, by omega, h⟩
  · rintro ⟨t, ht, ht2, h⟩
    by_cases hti : t < i
    · exact Or.inl ⟨t, by omega, h⟩
    · exact Or.inr ⟨t, by omega, ht, h⟩

theorem allbut_val (a : ℕ → ℕ) (n b i : ℕ) (w : List Bool) (hw : w.length = b) (hn : 2 ≤ n)
    (hi : i < n) (ha : ∀ t, t < n → a t < b) :
    ((W (allbut a n b) w).getD (allbutW a n b i) false = true ↔
      ∃ t, t < n ∧ t ≠ i ∧ w.getD (a t) false = true) := by
  have hP := abP_val a n b w hw hn ha
  have hS := abS_val a n b w hw hn ha
  by_cases h0 : i = 0
  · have e : allbutW a n b i = abS a n b (n - 1 - (n - 2)) := by
      unfold allbutW
      simp only [h0, ↓reduceIte]
      congr 1; omega
    rw [e, hS (n - 2) (le_refl _)]
    constructor
    · rintro ⟨t, ht, ht2, h⟩
      exact ⟨t, ht2, by omega, h⟩
    · rintro ⟨t, ht, ht2, h⟩
      exact ⟨t, by omega, ht, h⟩
  by_cases h1 : i = n - 1
  · have e : allbutW a n b i = abP a b (n - 2) := by
      unfold allbutW
      split_ifs
      rfl
    rw [e, hP (n - 2) (le_refl _)]
    constructor
    · rintro ⟨t, ht, h⟩
      exact ⟨t, by omega, by omega, h⟩
    · rintro ⟨t, ht, ht2, h⟩
      exact ⟨t, by omega, h⟩
  · have e : allbutW a n b i = w.length + (2 * (n - 2) + (i - 1)) := by
      unfold allbutW
      simp only [h0, h1, ↓reduceIte]
      omega
    have e1 : 2 * (n - 2) + (i - 1) - 2 * (n - 2) = i - 1 := by omega
    have e2 : i - 1 + 2 = n - 1 - (n - 2 - i) := by omega
    have hg : abG a n b (2 * (n - 2) + (i - 1)) =
        ⟨GateOp.or, [abP a b (i - 1), abS a n b (n - 1 - (n - 2 - i))]⟩ := by
      unfold abG
      have g1 : ¬ (2 * (n - 2) + (i - 1) < n - 2) := by omega
      have g2 : ¬ (2 * (n - 2) + (i - 1) < 2 * (n - 2)) := by omega
      simp only [g1, g2, ↓reduceIte, e1, e2]
    have key := W_range_or2 (abG a n b) (3 * (n - 2)) w (2 * (n - 2) + (i - 1)) _ _ (by omega) hg
      (by rw [hw]; exact abP_lt a n b _ _ ha hn (by omega))
      (by rw [hw]; exact abS_lt a n b _ _ ha hn (by omega))
    have hP' := hP (i - 1) (by omega)
    have hS' := hS (n - 2 - i) (by omega)
    unfold allbut at hP' hS'
    rw [e]
    unfold allbut
    rw [key, Bool.or_eq_true, hP', hS']
    exact ab_split n i _ h0 h1 hi

theorem b_not_of_iff (a b : Bool) (h : a = true ↔ ¬ b = true) : a = !b := by
  cases a <;> cases b <;> simp_all

def drOrP (f : ℕ → ℕ) (c : ℕ) (l : List ℕ) : Gate :=
  ⟨GateOp.or, (l.filter fun i => decide (i < c)).map f⟩

def drOrN (f2 : ℕ → ℕ) (c : ℕ) (l : List ℕ) : Gate :=
  ⟨GateOp.and, (l.filter fun i => decide (i < c)).map f2⟩

def drAndP (f : ℕ → ℕ) (c : ℕ) (l : List ℕ) : Gate :=
  if l.all (fun i => decide (i < c)) = true then ⟨GateOp.and, l.map f⟩ else ⟨GateOp.or, []⟩

def drAndN (f2 : ℕ → ℕ) (c : ℕ) (l : List ℕ) : Gate :=
  if l.all (fun i => decide (i < c)) = true then ⟨GateOp.or, l.map f2⟩ else ⟨GateOp.and, []⟩

def drGp (f f2 : ℕ → ℕ) (c : ℕ) (g : Gate) : Gate :=
  match g.op with
  | GateOp.and => drAndP f c g.inputs
  | GateOp.not => drOrN f2 c (g.inputs.take 1)
  | _ => drOrP f c g.inputs

def drGn (f f2 : ℕ → ℕ) (c : ℕ) (g : Gate) : Gate :=
  match g.op with
  | GateOp.and => drAndN f2 c g.inputs
  | GateOp.not => drOrP f c (g.inputs.take 1)
  | _ => drOrN f2 c g.inputs

theorem drOrP_shape (f : ℕ → ℕ) (c : ℕ) (l : List ℕ) :
    ((drOrP f c l).op = GateOp.and ∨ (drOrP f c l).op = GateOp.or) ∧
      (drOrP f c l).inputs.length ≤ l.length := by
  refine ⟨Or.inr rfl, ?_⟩
  show ((l.filter fun i => decide (i < c)).map f).length ≤ l.length
  rw [List.length_map]
  exact List.length_filter_le _ _

theorem drOrN_shape (f2 : ℕ → ℕ) (c : ℕ) (l : List ℕ) :
    ((drOrN f2 c l).op = GateOp.and ∨ (drOrN f2 c l).op = GateOp.or) ∧
      (drOrN f2 c l).inputs.length ≤ l.length := by
  refine ⟨Or.inl rfl, ?_⟩
  show ((l.filter fun i => decide (i < c)).map f2).length ≤ l.length
  rw [List.length_map]
  exact List.length_filter_le _ _

theorem drAndP_shape (f : ℕ → ℕ) (c : ℕ) (l : List ℕ) :
    ((drAndP f c l).op = GateOp.and ∨ (drAndP f c l).op = GateOp.or) ∧
      (drAndP f c l).inputs.length ≤ l.length := by
  unfold drAndP
  split_ifs
  · refine ⟨Or.inl rfl, ?_⟩
    show (l.map f).length ≤ l.length
    rw [List.length_map]
  · exact ⟨Or.inr rfl, Nat.zero_le _⟩

theorem drAndN_shape (f2 : ℕ → ℕ) (c : ℕ) (l : List ℕ) :
    ((drAndN f2 c l).op = GateOp.and ∨ (drAndN f2 c l).op = GateOp.or) ∧
      (drAndN f2 c l).inputs.length ≤ l.length := by
  unfold drAndN
  split_ifs
  · refine ⟨Or.inr rfl, ?_⟩
    show (l.map f2).length ≤ l.length
    rw [List.length_map]
  · exact ⟨Or.inl rfl, Nat.zero_le _⟩

theorem dr_take_le (l : List ℕ) : (l.take 1).length ≤ l.length := by
  rw [List.length_take]; exact Nat.min_le_right _ _

theorem drGp_shape (f f2 : ℕ → ℕ) (c : ℕ) (g : Gate) :
    ((drGp f f2 c g).op = GateOp.and ∨ (drGp f f2 c g).op = GateOp.or) ∧
      (drGp f f2 c g).inputs.length ≤ g.inputs.length := by
  obtain ⟨op, l⟩ := g
  cases op with
  | and => exact drAndP_shape f c l
  | not =>
    have h := drOrN_shape f2 c (l.take 1)
    exact ⟨h.1, le_trans h.2 (dr_take_le l)⟩
  | or => exact drOrP_shape f c l
  | mod k => exact drOrP_shape f c l
  | maj => exact drOrP_shape f c l

theorem drGn_shape (f f2 : ℕ → ℕ) (c : ℕ) (g : Gate) :
    ((drGn f f2 c g).op = GateOp.and ∨ (drGn f f2 c g).op = GateOp.or) ∧
      (drGn f f2 c g).inputs.length ≤ g.inputs.length := by
  obtain ⟨op, l⟩ := g
  cases op with
  | and => exact drAndN_shape f2 c l
  | not =>
    have h := drOrP_shape f c (l.take 1)
    exact ⟨h.1, le_trans h.2 (dr_take_le l)⟩
  | or => exact drOrN_shape f2 c l
  | mod k => exact drOrN_shape f2 c l
  | maj => exact drOrN_shape f2 c l

theorem drOrP_eval (f : ℕ → ℕ) (c : ℕ) (Gd V : ℕ → Bool) (l : List ℕ)
    (H : ∀ i, i < c → Gd (f i) = V i) (H0 : ∀ i, ¬ i < c → V i = false) :
    (drOrP f c l).op.eval ((drOrP f c l).inputs.map Gd) = GateOp.or.eval (l.map V) := by
  show GateOp.or.eval (((l.filter fun i => decide (i < c)).map f).map Gd) = _
  rw [List.map_map, Bool.eq_iff_iff, eval_or_iff, eval_or_iff]
  constructor
  · rintro ⟨i, hi, h⟩
    obtain ⟨hil, hic⟩ := List.mem_filter.mp hi
    have hic' : i < c := of_decide_eq_true hic
    exact ⟨i, hil, by rw [← H i hic']; exact h⟩
  · rintro ⟨i, hi, h⟩
    have hic : i < c := by
      by_contra hc
      rw [H0 i hc] at h
      exact Bool.false_ne_true h
    exact ⟨i, List.mem_filter.mpr ⟨hi, decide_eq_true hic⟩, by
      show Gd (f i) = true
      rw [H i hic]; exact h⟩

theorem drOrN_eval (f2 : ℕ → ℕ) (c : ℕ) (Gd V : ℕ → Bool) (l : List ℕ)
    (H : ∀ i, i < c → Gd (f2 i) = !V i) (H0 : ∀ i, ¬ i < c → V i = false) :
    (drOrN f2 c l).op.eval ((drOrN f2 c l).inputs.map Gd) = !GateOp.or.eval (l.map V) := by
  show GateOp.and.eval (((l.filter fun i => decide (i < c)).map f2).map Gd) = _
  apply b_not_of_iff
  rw [List.map_map, eval_and_iff, eval_or_iff]
  constructor
  · rintro h ⟨i, hi, hv⟩
    have hic : i < c := by
      by_contra hc
      rw [H0 i hc] at hv
      exact Bool.false_ne_true hv
    have h1 : Gd (f2 i) = true := h i (List.mem_filter.mpr ⟨hi, decide_eq_true hic⟩)
    rw [H i hic, hv] at h1
    exact Bool.false_ne_true h1
  · intro h i hi
    obtain ⟨hil, hic⟩ := List.mem_filter.mp hi
    have hic' : i < c := of_decide_eq_true hic
    show Gd (f2 i) = true
    rw [H i hic']
    cases hv : V i with
    | false => rfl
    | true => exact absurd ⟨i, hil, hv⟩ h

theorem dr_all_lt (c : ℕ) (l : List ℕ) (h : l.all (fun i => decide (i < c)) = true) :
    ∀ i ∈ l, i < c := by
  intro i hi
  exact of_decide_eq_true (List.all_eq_true.mp h i hi)

theorem dr_and_false (c : ℕ) (V : ℕ → Bool) (l : List ℕ) (H0 : ∀ i, ¬ i < c → V i = false)
    (h : ¬ l.all (fun i => decide (i < c)) = true) : GateOp.and.eval (l.map V) = false := by
  cases hv : GateOp.and.eval (l.map V) with
  | false => rfl
  | true =>
    exfalso
    apply h
    rw [eval_and_iff] at hv
    apply List.all_eq_true.mpr
    intro i hi
    apply decide_eq_true
    by_contra hc
    have := hv i hi
    rw [H0 i hc] at this
    exact Bool.false_ne_true this

theorem drAndP_eval (f : ℕ → ℕ) (c : ℕ) (Gd V : ℕ → Bool) (l : List ℕ)
    (H : ∀ i, i < c → Gd (f i) = V i) (H0 : ∀ i, ¬ i < c → V i = false) :
    (drAndP f c l).op.eval ((drAndP f c l).inputs.map Gd) = GateOp.and.eval (l.map V) := by
  unfold drAndP
  split_ifs with hall
  · show GateOp.and.eval ((l.map f).map Gd) = _
    rw [List.map_map]
    congr 1
    apply List.map_congr_left
    intro i hi
    exact H i (dr_all_lt c l hall i hi)
  · rw [dr_and_false c V l H0 hall]
    rfl

theorem drAndN_eval (f2 : ℕ → ℕ) (c : ℕ) (Gd V : ℕ → Bool) (l : List ℕ)
    (H : ∀ i, i < c → Gd (f2 i) = !V i) (H0 : ∀ i, ¬ i < c → V i = false) :
    (drAndN f2 c l).op.eval ((drAndN f2 c l).inputs.map Gd) = !GateOp.and.eval (l.map V) := by
  unfold drAndN
  split_ifs with hall
  · show GateOp.or.eval ((l.map f2).map Gd) = _
    apply b_not_of_iff
    rw [List.map_map, eval_and_iff, eval_or_iff]
    constructor
    · rintro ⟨i, hi, h⟩ hc
      have h1 : Gd (f2 i) = true := h
      rw [H i (dr_all_lt c l hall i hi), hc i hi] at h1
      exact Bool.false_ne_true h1
    · intro h
      by_contra hc
      apply h
      intro i hi
      cases hv : V i with
      | true => rfl
      | false =>
        exfalso
        apply hc
        refine ⟨i, hi, ?_⟩
        show Gd (f2 i) = true
        rw [H i (dr_all_lt c l hall i hi), hv]
        rfl
  · rw [dr_and_false c V l H0 hall]
    rfl

theorem oneEach_len {n m : ℕ} (u : Fin n) (v : Fin m) : (oneEach u v).length = n + m := by
  unfold oneEach
  rw [List.length_append, List.length_ofFn, List.length_ofFn]

theorem oneEach_left {n m : ℕ} (u : Fin n) (v : Fin m) (t : ℕ) (ht : t < n) :
    (oneEach u v).getD t false = decide (t = u.val) := by
  unfold oneEach
  rw [List.getD_append _ _ _ _ (by rw [List.length_ofFn]; exact ht), ofFn_getD _ t ht]
  apply decide_eq_decide.mpr
  constructor
  · intro h; rw [← h]
  · intro h; exact Fin.ext h

theorem oneEach_right {n m : ℕ} (u : Fin n) (v : Fin m) (t : ℕ) (ht : t < m) :
    (oneEach u v).getD (n + t) false = decide (t = v.val) := by
  unfold oneEach
  rw [List.getD_append_right _ _ _ _ (by rw [List.length_ofFn]; omega), List.length_ofFn,
    Nat.add_sub_cancel_left, ofFn_getD _ t ht]
  apply decide_eq_decide.mpr
  constructor
  · intro h; rw [← h]
  · intro h; exact Fin.ext h

def drB (n m : ℕ) : ℕ := n + m + 3 * (n - 2) + 3 * (m - 2)

def drPos (n m s i : ℕ) : ℕ :=
  if i < n + m then i
  else if i < n + m + s then drB n m + 2 * (i - (n + m)) else drB n m + 2 * s

def drNeg (n m s i : ℕ) : ℕ :=
  if i < n then (if n = 1 then drB n m + 2 * s else allbutW id n (n + m) i)
  else if i < n + m then
    (if m = 1 then drB n m + 2 * s
      else allbutW (fun t => n + t) m (n + m + 3 * (n - 2)) (i - n))
  else drB n m + 2 * (i - (n + m)) + 1

theorem dr_inputs {n m : ℕ} (s : ℕ) (u : Fin n) (v : Fin m) (i : ℕ) (hi : i < n + m) :
    drPos n m s i < drB n m ∧
    (drNeg n m s i < drB n m ∨ drB n m + 2 * s ≤ drNeg n m s i) ∧
    (W (allbut (fun t => n + t) m (n + m + 3 * (n - 2)))
      (W (allbut id n (n + m)) (oneEach u v))).getD (drPos n m s i) false =
        (oneEach u v).getD i false ∧
    (W (allbut (fun t => n + t) m (n + m + 3 * (n - 2)))
      (W (allbut id n (n + m)) (oneEach u v))).getD (drNeg n m s i) false =
        !(oneEach u v).getD i false := by
  have hx : (oneEach u v).length = n + m := oneEach_len u v
  have hw1 : (W (allbut id n (n + m)) (oneEach u v)).length = n + m + 3 * (n - 2) := by
    rw [W_length, hx, allbut_len]
  have hw2 : (W (allbut (fun t => n + t) m (n + m + 3 * (n - 2)))
      (W (allbut id n (n + m)) (oneEach u v))).length = drB n m := by
    rw [W_length, hw1, allbut_len]
    rfl
  have hB : n + m ≤ drB n m := by unfold drB; omega
  have eP : drPos n m s i = i := by
    unfold drPos
    simp only [hi, ↓reduceIte]
  refine ⟨by rw [eP]; omega, ?_, ?_, ?_⟩
  · unfold drNeg
    split_ifs with h1 h2 h3
    · exact Or.inr (le_refl _)
    · have := allbutW_lt id n (n + m) i (by omega) h1 (fun t ht => by show t < n + m; omega)
      rw [allbut_len] at this
      unfold drB
      exact Or.inl (by omega)
    · exact Or.inr (le_refl _)
    · have := allbutW_lt (fun t => n + t) m (n + m + 3 * (n - 2)) (i - n) (by omega) (by omega)
        (fun t ht => by show n + t < n + m + 3 * (n - 2); omega)
      rw [allbut_len] at this
      unfold drB
      exact Or.inl (by omega)
  · rw [eP, W_prefix _ _ _ (by rw [hw1]; omega), W_prefix _ _ _ (by rw [hx]; exact hi)]
  · by_cases h1 : i < n
    · by_cases h2 : n = 1
      · have e : drNeg n m s i = drB n m + 2 * s := by
          unfold drNeg
          split_ifs
          rfl
        rw [e, getD_ge _ _ (by rw [hw2]; omega), oneEach_left u v i h1]
        have : i = u.val := by have := u.isLt; omega
        simp only [this, decide_true, Bool.not_true]
      · have e : drNeg n m s i = allbutW id n (n + m) i := by
          unfold drNeg
          split_ifs
          rfl
        have ha : ∀ t, t < n → id t < n + m := fun t ht => by show t < n + m; omega
        have hlt := allbutW_lt id n (n + m) i (by omega) h1 ha
        rw [allbut_len] at hlt
        rw [e, W_prefix _ _ _ (by rw [hw1]; exact hlt)]
        apply b_not_of_iff
        rw [allbut_val id n (n + m) i (oneEach u v) hx (by omega) h1 ha, oneEach_left u v i h1]
        constructor
        · rintro ⟨t, ht, hti, h⟩ hc
          have h' : (oneEach u v).getD t false = true := h
          rw [oneEach_left u v t ht] at h'
          have a1 : t = u.val := of_decide_eq_true h'
          have a2 : i = u.val := of_decide_eq_true hc
          omega
        · intro hc
          refine ⟨u.val, u.isLt, ?_, ?_⟩
          · intro e2
            exact hc (decide_eq_true e2.symm)
          · show (oneEach u v).getD u.val false = true
            rw [oneEach_left u v u.val u.isLt]
            exact decide_eq_true rfl
    · by_cases h2 : m = 1
      · have e : drNeg n m s i = drB n m + 2 * s := by
          unfold drNeg
          split_ifs
          rfl
        have ei : i = n + (i - n) := by omega
        rw [e, getD_ge _ _ (by rw [hw2]; omega), ei, oneEach_right u v (i - n) (by omega)]
        have : i - n = v.val := by have := v.isLt; omega
        simp only [this, decide_true, Bool.not_true]
      · have e : drNeg n m s i = allbutW (fun t => n + t) m (n + m + 3 * (n - 2)) (i - n) := by
          unfold drNeg
          split_ifs
          rfl
        have ha : ∀ t, t < m → (fun t => n + t) t < n + m + 3 * (n - 2) :=
          fun t ht => by show n + t < n + m + 3 * (n - 2); omega
        have hin : i - n < m := by omega
        have ei : i = n + (i - n) := by omega
        rw [e]
        apply b_not_of_iff
        rw [allbut_val (fun t => n + t) m (n + m + 3 * (n - 2)) (i - n) _ hw1 (by omega) hin ha]
        rw [ei, oneEach_right u v (i - n) hin, ← ei]
        constructor
        · rintro ⟨t, ht, hti, h⟩ hc
          have h' : (W (allbut id n (n + m)) (oneEach u v)).getD (n + t) false = true := h
          rw [W_prefix _ _ _ (by rw [hx]; omega), oneEach_right u v t ht] at h'
          have a1 : t = v.val := of_decide_eq_true h'
          have a2 : i - n = v.val := of_decide_eq_true hc
          omega
        · intro hc
          refine ⟨v.val, v.isLt, ?_, ?_⟩
          · intro e2
            exact hc (decide_eq_true e2.symm)
          · show (W (allbut id n (n + m)) (oneEach u v)).getD (n + v.val) false = true
            rw [W_prefix _ _ _ (by rw [hx]; have := v.isLt; omega), oneEach_right u v v.val v.isLt]
            exact decide_eq_true rfl

lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

lemma gateAt_here (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]


lemma coneFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

lemma coneStep_getD_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) :
    (coneStep n cs g).getD cs.length [] =
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => (w - n) :: cs.getD (w - n) []) := by
  simp [coneStep, List.getD_eq_getElem?_getD]

lemma coneStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (coneStep n cs g).getD m [] = cs.getD m [] := by
  simp [coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

lemma coneFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (coneStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (coneStep n cs g) (by simp [coneStep]; omega)]
    exact coneStep_getD_lt n cs g k hk

lemma inCone_iff (n : ℕ) (C : Circuit) (i k : ℕ) (hk : k < C.gates.length) :
    InCone n C i k ↔ ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧
      (i = w - n ∨ InCone n C i (w - n)) := by
  obtain ⟨pre, post, gk, hgs, hpre_len, hgk⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gk := by rw [gateAt_here C k hk]; exact hgk
  rw [hga]
  have hc : cones n C = post.foldl (coneStep n) (coneStep n (pre.foldl (coneStep n) []) gk) := by
    simp only [cones]
    rw [hgs, List.foldl_append, List.foldl_cons]
  have hl0 : (pre.foldl (coneStep n) []).length = k := by
    rw [coneFold_length]; simp [hpre_len]
  have hl1 : (coneStep n (pre.foldl (coneStep n) []) gk).length = k + 1 := by
    simp [coneStep, hl0]
  have h1 : (cones n C).getD k [] =
      (gk.inputs.filter (fun w => decide (n ≤ w ∧ w < n + k))).flatMap
        (fun w => (w - n) :: (pre.foldl (coneStep n) []).getD (w - n) []) := by
    rw [hc, coneFold_getD_lt n post _ k (by omega)]
    have h := coneStep_getD_last n (pre.foldl (coneStep n) []) gk
    rw [hl0] at h
    exact h
  have h2 : ∀ m, m < k → (cones n C).getD m [] = (pre.foldl (coneStep n) []).getD m [] := by
    intro m hm
    rw [hc, coneFold_getD_lt n post _ m (by omega)]
    exact coneStep_getD_lt n _ gk m (by omega)
  unfold InCone
  rw [h1]
  simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons]
  constructor
  · rintro ⟨w, ⟨hw, hn, hlt⟩, h⟩
    refine ⟨w, hw, hn, hlt, ?_⟩
    rcases h with h | h
    · exact Or.inl h
    · right
      rw [h2 (w - n) (by omega)]
      exact h
  · rintro ⟨w, hw, hn, hlt, h⟩
    refine ⟨w, ⟨hw, hn, hlt⟩, ?_⟩
    rcases h with h | h
    · exact Or.inl h
    · right
      rw [← h2 (w - n) (by omega)]
      exact h



def below (N : ℕ) (C : Circuit) (i j : ℕ) : Prop := i = j ∨ InCone N C i j

theorem below_trans (N : ℕ) (C : Circuit) (i r j : ℕ) (hj : j < C.gates.length)
    (a : below N C i r) (b : below N C r j) : below N C i j := by
  rcases a with rfl | a
  · exact b
  rcases b with rfl | b
  · exact Or.inr a
  right
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    obtain ⟨w,hw,lo,hi,rw|ancestor⟩ := (inCone_iff N C r j hj).mp b
    · exact (inCone_iff N C i j hj).mpr ⟨w,hw,lo,hi,Or.inr (rw ▸ a)⟩
    · exact (inCone_iff N C i j hj).mpr
        ⟨w,hw,lo,hi,Or.inr (ih (w-N) (by omega) (by omega) ancestor)⟩

theorem below_le (N : ℕ) (C : Circuit) (i j : ℕ) (hj : j < C.gates.length)
    (a : below N C i j) : i ≤ j := by
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    rcases a with rfl | a
    · omega
    obtain ⟨w,hw,lo,hi,ancestor⟩ := (inCone_iff N C i j hj).mp a
    have le := ih (w-N) (by omega) (by omega) ancestor
    omega

def shared (N : ℕ) (C : Circuit) (h p i : ℕ) : Prop :=
  below N C i h ∧ ∃ r < C.gates.length, below N C r h ∧ below N C i r ∧
    (C.output = N+r ∨ ∃ j < C.gates.length, ¬below N C j h ∧ j ≠ p ∧
      N+r ∈ (gateAt C j).inputs)

def posNeeded (N : ℕ) (C : Circuit) (h p i : ℕ) : Prop :=
  ¬below N C i h ∨ shared N C h p i

theorem prior_read (N : ℕ) (C : Circuit) (i j : ℕ) (hi : i < j) (hj : j < C.gates.length)
    (read : N+i ∈ (gateAt C j).inputs) : below N C i j := by
  exact Or.inr ((inCone_iff N C i j hj).mpr ⟨N+i,read,by omega,by omega,Or.inl (by omega)⟩)

theorem negative_read (N : ℕ) (C : Circuit) (h i j : ℕ) (hi : i < j)
    (hj : j < C.gates.length) (hh : h < C.gates.length) (read : N+i ∈ (gateAt C j).inputs)
    (need : below N C j h) : below N C i h :=
  below_trans N C i j h hh (prior_read N C i j hi hj read) need

theorem positive_read (N : ℕ) (C : Circuit) (h p i j : ℕ) (hi : i < j)
    (hj : j < C.gates.length) (np : j ≠ p) (read : N+i ∈ (gateAt C j).inputs)
    (need : posNeeded N C h p j) : posNeeded N C h p i := by
  by_cases inH : below N C i h
  · right
    refine ⟨inH,?_⟩
    rcases need with outside | ⟨_,r,hr,inr,jr,used⟩
    · exact ⟨i,by omega,inH,Or.inl rfl,Or.inr ⟨j,hj,outside,np,read⟩⟩
    · exact ⟨r,hr,inr,below_trans N C i j r hr (prior_read N C i j hi hj read) jr,used⟩
  · exact Or.inl inH

abbrev Domain (n m : ℕ) := Fin n × Fin m

def signal {n m : ℕ} (gs : List Gate) (i : ℕ) (x : Domain n m) : Bool :=
  (W gs (oneEach x.1 x.2)).getD i false

def carries {n m : ℕ} (gs : List Gate) (f : Domain n m → Bool) : Prop :=
  ∃ i : ℕ, ∀ x, signal gs i x = f x

theorem carry_keep {n m : ℕ} {f : Domain n m → Bool} {gs : List Gate}
    (c : carries gs f) (ext : List Gate) : carries (gs++ext) f := by
  obtain ⟨i,hi⟩ := c
  by_cases small : i < n+m+gs.length
  · refine ⟨i,fun x => ?_⟩
    rw [signal,W_append,W_prefix _ _ _ (by rw [W_length,oneEach_len]; exact small)]
    exact hi x
  · refine ⟨n+m+(gs++ext).length,fun x => ?_⟩
    rw [←hi x,signal,signal,W_ge _ _ _ (by rw [oneEach_len]),W_ge _ _ _ (by rw [oneEach_len]; omega)]

def signed (neg : Bool) (v : Bool) : Bool := if neg then !v else v

def lowerGate (neg : Bool) (f : ℕ → ℕ) (c : ℕ) (g : Gate) : Gate :=
  if neg then drGn f f c g else drGp f f c g

theorem lower_eval (neg : Bool) (f : ℕ → ℕ) (c : ℕ) (g : Gate)
    (U V : ℕ → Bool) (op : g.op = .and ∨ g.op = .or)
    (parents : ∀ i ∈ g.inputs, i < c → U (f i) = signed neg (V i))
    (late : ∀ i, ¬i < c → V i = false) :
    (lowerGate neg f c g).op.eval ((lowerGate neg f c g).inputs.map U) =
      signed neg (g.op.eval (g.inputs.map V)) := by
  let V' := fun i => if i < c then signed neg (U (f i)) else false
  have vals : g.inputs.map V' = g.inputs.map V := by
    apply List.map_congr_left
    intro i mem
    by_cases small : i < c
    · cases neg <;> simp [V',small,parents i mem small,signed]
    · simp [V',small,late i small]
  have far : ∀ i, ¬i < c → V' i = false := fun i hi => by simp [V',hi]
  obtain ⟨op0,l⟩ := g
  cases neg <;> rcases op with op|op <;> change op0 = _ at op <;> subst op0
  · change (drAndP f c l).op.eval ((drAndP f c l).inputs.map U) = GateOp.and.eval (l.map V)
    rw [←vals]; exact drAndP_eval f c U V' l (fun i hi => by simp [V',hi,signed]) far
  · change (drOrP f c l).op.eval ((drOrP f c l).inputs.map U) = GateOp.or.eval (l.map V)
    rw [←vals]; exact drOrP_eval f c U V' l (fun i hi => by simp [V',hi,signed]) far
  · change (drAndN f c l).op.eval ((drAndN f c l).inputs.map U) = !GateOp.and.eval (l.map V)
    rw [←vals]; exact drAndN_eval f c U V' l (fun i hi => by simp [V',hi,signed]) far
  · change (drOrN f c l).op.eval ((drOrN f c l).inputs.map U) = !GateOp.or.eval (l.map V)
    rw [←vals]; exact drOrN_eval f c U V' l (fun i hi => by simp [V',hi,signed]) far

theorem lower_one {n m : ℕ} (C : Circuit) (gs : List Gate) (j : ℕ) (hj : j < C.gates.length)
    (neg : Bool) (op : (gateAt C j).op = .and ∨ (gateAt C j).op = .or)
    (width : (gateAt C j).inputs.length ≤ 2)
    (parents : ∀ i ∈ (gateAt C j).inputs, i < n+m+j →
      carries gs (fun x : Domain n m => signed neg (signal C.gates i x))) :
    ∃ g : Gate, ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      carries (gs++[g]) (fun x : Domain n m => signed neg (signal C.gates (n+m+j) x)) := by
  classical
  let g := gateAt C j
  let c := n+m+j
  let pick := fun i => if h : i ∈ g.inputs ∧ i < c then (parents i h.1 h.2).choose else 0
  let q := lowerGate neg pick c g
  refine ⟨q,?_,n+m+gs.length,fun x => ?_⟩
  · have shape : (q.op = .and ∨ q.op = .or) ∧ q.inputs.length ≤ g.inputs.length := by
      cases neg with
      | false => exact drGp_shape pick pick c g
      | true => exact drGn_shape pick pick c g
    exact ⟨shape.1,shape.2.trans width⟩
  · let U := fun i => signal gs i x
    let V := fun i => if i < c then signal C.gates i x else false
    have term := lower_eval neg pick c g U V op (fun i mem hi => by
      simp only [pick,dif_pos (And.intro mem hi),V,if_pos hi]
      exact (parents i mem hi).choose_spec x) (fun i hi => by simp [V,hi])
    have gate := W_gate C.gates (oneEach x.1 x.2) j hj
    rw [oneEach_len,←gateAt_here C j hj] at gate
    change signal C.gates (n+m+j) x = g.op.eval (g.inputs.map V) at gate
    change signal (gs++[q]) (n+m+gs.length) x = signed neg (signal C.gates (n+m+j) x)
    rw [gate,←term]
    unfold signal
    rw [W_snoc,step_last _ _ _ (by rw [W_length,oneEach_len])]
    rfl

def marked (N : ℕ) (C : Circuit) (h h' i : ℕ) : Prop :=
  below N C i h ∨ below N C i h'

def needed (neg : Bool) (N : ℕ) (C : Circuit) (h h' j : ℕ) : Prop :=
  if neg then marked N C h h' j else True

def recorded (n m : ℕ) (C : Circuit) (h p k : ℕ) (gs : List Gate) : Prop :=
  (∀ i < n+m, ∀ neg, carries gs (fun x : Domain n m => signed neg (signal C.gates i x))) ∧
  ∀ j < k, ∀ neg, needed neg (n+m) C h p j →
    carries gs (fun x : Domain n m => signed neg (signal C.gates (n+m+j) x))

theorem record_extend {n m h p k : ℕ} {C : Circuit} {gs : List Gate}
    (base : recorded n m C h p k gs) (extra : List Gate) : recorded n m C h p k (gs++extra) :=
  ⟨fun i hi neg => carry_keep (base.1 i hi neg) extra,
   fun j hj neg nj => carry_keep (base.2 j hj neg nj) extra⟩

theorem record_next {n m h p k : ℕ} {C : Circuit} {gs : List Gate}
    (base : recorded n m C h p k gs)
    (new : ∀ neg, needed neg (n+m) C h p k →
      carries gs (fun x : Domain n m => signed neg (signal C.gates (n+m+k) x))) :
    recorded n m C h p (k+1) gs := by
  refine ⟨base.1,?_⟩
  intro j hj neg need
  by_cases same : j=k
  · exact same ▸ new neg (same ▸ need)
  · exact base.2 j (by omega) neg need



theorem parents2 {n m h k j : ℕ} {C : Circuit} {gs : List Gate}
    (old : recorded n m C h k j gs) (hj : j<C.gates.length)
    (hh : h<C.gates.length) (hk : k<C.gates.length) (neg : Bool)
    (need : needed neg (n+m) C h k j) :
    ∀ i ∈ (gateAt C j).inputs, i<n+m+j →
      carries gs (fun x : Domain n m => signed neg (signal C.gates i x)) := by
  intro i mem before
  by_cases raw : i<n+m
  · exact old.1 i raw neg
  obtain ⟨d,rfl⟩ : ∃ d, i=n+m+d := ⟨i-(n+m),by omega⟩
  apply old.2 d (by omega) neg
  cases neg with
  | false => trivial
  | true =>
    rcases need with a|b
    · exact Or.inl (negative_read _ C h d j (by omega) hj hh mem a)
    · exact Or.inr (negative_read _ C k d j (by omega) hj hk mem b)

theorem inverter_signal {n m h p : ℕ} {C : Circuit} (hp : p<C.gates.length) (hh : h<p)
    (notOp : (gateAt C p).op = .not)
    (read : (gateAt C p).inputs.head? = some (n+m+h)) (x : Domain n m) :
    signal C.gates (n+m+p) x = !signal C.gates (n+m+h) x := by
  have gate := W_gate C.gates (oneEach x.1 x.2) p hp
  rw [oneEach_len,←gateAt_here C p hp,notOp] at gate
  cases he : (gateAt C p).inputs with
  | nil => simp [he] at read
  | cons a l =>
    have eq : a=n+m+h := by simpa [he] using read
    simpa [signal,he,eq,GateOp.eval,show n+m+h < n+m+p by omega] using gate

def legal (g : Gate) : Prop := (g.op=.and ∨ g.op=.or) ∧ g.inputs.length ≤ 2

def front (n m : ℕ) : List Gate :=
  allbut id n (n+m) ++ allbut (fun t => n+t) m (n+m+3*(n-2))

theorem front_record (n m h p : ℕ) (C : Circuit) : recorded n m C h p 0 (front n m) := by
  refine ⟨?_,by simp⟩
  intro i hi neg
  cases neg with
  | false =>
    refine ⟨drPos n m C.gates.length i,fun x => ?_⟩
    change (W (front n m) (oneEach x.1 x.2)).getD _ false =
      (W C.gates (oneEach x.1 x.2)).getD i false
    rw [front,W_append,W_prefix C.gates (oneEach x.1 x.2) i (by rw [oneEach_len]; exact hi)]
    exact (dr_inputs C.gates.length x.1 x.2 i hi).2.2.1
  | true =>
    refine ⟨drNeg n m C.gates.length i,fun x => ?_⟩
    change (W (front n m) (oneEach x.1 x.2)).getD _ false =
      !(W C.gates (oneEach x.1 x.2)).getD i false
    rw [front,W_append,W_prefix C.gates (oneEach x.1 x.2) i (by rw [oneEach_len]; exact hi)]
    exact (dr_inputs C.gates.length x.1 x.2 i hi).2.2.2



def extra (N : ℕ) (C : Circuit) (p q h k j : ℕ) : Prop :=
  j≠p ∧ j≠q ∧ marked N C h k j

theorem skip_not {n m h k j d : ℕ} {C : Circuit} {gs : List Gate}
    (old : recorded n m C h k j gs) (hj : j<C.gates.length) (hd : d<j)
    (op : (gateAt C j).op=.not) (read : (gateAt C j).inputs.head?=some (n+m+d))
    (md : marked (n+m) C h k d) : recorded n m C h k (j+1) gs := by
  apply record_next old
  intro neg _
  cases neg with
  | false =>
    obtain ⟨i,wi⟩ := old.2 d hd true md
    refine ⟨i,fun x => ?_⟩
    simpa only [signed,Bool.false_eq_true,ite_false,ite_true,inverter_signal hj hd op read] using wi x
  | true =>
    obtain ⟨i,wi⟩ := old.2 d hd false (by trivial)
    refine ⟨i,fun x => ?_⟩
    simpa only [signed,Bool.false_eq_true,ite_false,ite_true,inverter_signal hj hd op read,Bool.not_not] using wi x

open Classical in
theorem next2 {n m p q h k j : ℕ} {C : Circuit} {gs : List Gate}
    (old : recorded n m C h k j gs) (hj : j<C.gates.length)
    (fan : FanInTwo C) (hp : p<C.gates.length) (hq : q<C.gates.length) (pq : p≠q)
    (opP : (gateAt C p).op=.not) (opQ : (gateAt C q).op=.not)
    (readP : (gateAt C p).inputs.head?=some (n+m+h)) (readQ : (gateAt C q).inputs.head?=some (n+m+k))
    (hh : h<p) (hk : k<q) (onlyNot : ∀ a<C.gates.length, (gateAt C a).op=.not → a=p ∨ a=q) :
    ∃ ext : List Gate, (∀ g ∈ ext, legal g) ∧
      ext.length + (if j=p then 1 else 0) + (if j=q then 1 else 0) ≤
        1 + (if extra (n+m) C p q h k j then 1 else 0) ∧ recorded n m C h k (j+1) (gs++ext) := by
  classical
  by_cases jp : j=p
  · subst j
    exact ⟨[],by simp,by simp [pq,extra],by simpa using skip_not old hp hh opP readP (Or.inl (Or.inl rfl))⟩
  by_cases jq : j=q
  · subst j
    exact ⟨[],by simp,by simp [jp,extra],by simpa using skip_not old hq hk opQ readQ (Or.inr (Or.inl rfl))⟩
  have good := fan (gateAt C j) (by rw [gateAt_here C j hj]; exact List.getElem_mem hj)
  have shape : (gateAt C j).op=.and ∨ (gateAt C j).op=.or := by
    have ops := good.1
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ops
    exact ops.elim Or.inl (fun t => t.elim Or.inr (fun no => ((onlyNot j hj no).elim jp jq).elim))
  obtain ⟨a,ga,pos⟩ := lower_one C gs j hj false shape good.2 (parents2 old hj (by omega) (by omega) false (by trivial))
  by_cases mc : marked (n+m) C h k j
  · have old' := record_extend old [a]
    obtain ⟨b,gb,neg⟩ := lower_one C (gs++[a]) j hj true shape good.2 (parents2 old' hj (by omega) (by omega) true mc)
    refine ⟨[a,b],?_,by simp [jp,jq,extra,mc],?_⟩
    · intro g mem
      simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
      rcases mem with rfl|rfl
      · exact ga
      · exact gb
    · apply record_next (record_extend old [a,b])
      intro sign _
      cases sign with
      | false => simpa [List.append_assoc] using carry_keep pos [b]
      | true => simpa [List.append_assoc] using neg
  · refine ⟨[a],by simpa [legal] using ga,by simp [jp,jq,extra,mc],?_⟩
    apply record_next (record_extend old [a])
    intro sign req
    cases sign with
    | false => exact pos
    | true => exact (mc req).elim

open Classical in
noncomputable def extraCount (N : ℕ) (C : Circuit) (p q h k t : ℕ) : ℕ :=
  ((Finset.range t).filter (extra N C p q h k)).card

open Classical in
theorem increment (N : ℕ) (C : Circuit) (p q h k t : ℕ) : extraCount N C p q h k (t+1) =
    extraCount N C p q h k t + (if extra N C p q h k t then 1 else 0) := by
  classical
  by_cases yes : extra N C p q h k t <;>
    simp [extraCount,Finset.range_add_one,Finset.filter_insert,yes,Finset.mem_filter]

theorem seen_succ (p t : ℕ) : (if p<t+1 then 1 else 0 : ℕ) =
    (if p<t then 1 else 0) + (if t=p then 1 else 0) := by
  split_ifs <;> omega

theorem whole2 {n m p q h k : ℕ} {C : Circuit}
    (fan : FanInTwo C) (hp : p<C.gates.length) (hq : q<C.gates.length) (pq : p≠q)
    (opP : (gateAt C p).op=.not) (opQ : (gateAt C q).op=.not)
    (readP : (gateAt C p).inputs.head?=some (n+m+h)) (readQ : (gateAt C q).inputs.head?=some (n+m+k))
    (hh : h<p) (hk : k<q) (onlyNot : ∀ a<C.gates.length, (gateAt C a).op=.not → a=p ∨ a=q)
    (t : ℕ) (ht : t≤C.gates.length) : ∃ gs, (∀ g ∈ gs, legal g) ∧
      gs.length + (if p<t then 1 else 0) + (if q<t then 1 else 0) ≤
        (front n m).length + t + extraCount (n+m) C p q h k t ∧ recorded n m C h k t gs := by
  classical
  induction t with
  | zero =>
    refine ⟨front n m,?_,by simp [extraCount],front_record n m h k C⟩
    intro g mem
    rcases List.mem_append.mp mem with a|a
    · obtain ⟨op,w⟩ := allbut_gate _ _ _ _ a
      exact ⟨Or.inr op,by omega⟩
    · obtain ⟨op,w⟩ := allbut_gate _ _ _ _ a
      exact ⟨Or.inr op,by omega⟩
  | succ t ih =>
    obtain ⟨gs,ok,cap,old⟩ := ih (by omega)
    obtain ⟨ext,ok',lim,new⟩ := next2 old (by omega) fan hp hq pq opP opQ readP readQ hh hk onlyNot
    refine ⟨gs++ext,fun g mem => (List.mem_append.mp mem).elim (ok g) (ok' g),?_,new⟩
    rw [List.length_append,seen_succ,seen_succ,increment]
    omega

theorem output_record {n m h p : ℕ} {C : Circuit} {gs : List Gate}
    (full : recorded n m C h p C.gates.length gs) :
    carries gs (fun x : Domain n m => signal C.gates C.output x) := by
  by_cases raw : C.output < n+m
  · exact full.1 C.output raw false
  let j := C.output-(n+m)
  have eq : C.output=n+m+j := by dsimp [j]; omega
  by_cases present : j<C.gates.length
  · have val := full.2 j present false (by trivial)
    rw [eq]
    exact val
  · refine ⟨n+m+gs.length,fun x => ?_⟩
    change (W gs (oneEach x.1 x.2)).getD (n+m+gs.length) false =
      (W C.gates (oneEach x.1 x.2)).getD C.output false
    rw [W_ge _ _ _ (by rw [oneEach_len]),W_ge _ _ _ (by rw [oneEach_len]; omega)]


end PEqualNP.Outside.L_meta_19197

open PEqualNP.Outside.L_meta_19197 in
theorem PEqualNP.Outside.L_meta_19197 : (∀ (n m s : ℕ) (A : Fin n → Fin m → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit) (p q h h' : ℕ), PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ s → PEqualNP.Represents.Represents A C → p < C.gates.length → q < C.gates.length → p ≠ q → (PEqualNP.MetaComplexity.NestedCover.gateAt C p).op = PEqualNP.CircuitLowerBounds.GateOp.not → (PEqualNP.MetaComplexity.NestedCover.gateAt C q).op = PEqualNP.CircuitLowerBounds.GateOp.not → (PEqualNP.MetaComplexity.NestedCover.gateAt C p).inputs.head? = some (n + m + h) → (PEqualNP.MetaComplexity.NestedCover.gateAt C q).inputs.head? = some (n + m + h') → h < p → h' < q → (∀ j < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.not → j = p ∨ j = q) → PEqualNP.Represents.RepSizeAtMost A (s - 2 + ((Finset.range C.gates.length).filter (fun i => i ≠ p ∧ i ≠ q ∧ ((i = h ∨ PEqualNP.EdgeOwnership.InCone (n + m) C i h) ∨ (i = h' ∨ PEqualNP.EdgeOwnership.InCone (n + m) C i h')))).card + ((3 * n - 6) + (3 * m - 6)))) := by
  classical
  intro n m s A C p q h k fan size rep hp hq pq opP opQ readP readQ hh hk onlyNot
  obtain ⟨gs,good,bound,rec⟩ := whole2 fan hp hq pq opP opQ readP readQ hh hk onlyNot C.gates.length le_rfl
  obtain ⟨out,wire⟩ := output_record rec
  refine ⟨⟨gs,out⟩,good,?_,fun u v => (wire (u,v)).trans (rep u v)⟩
  have sz : C.gates.length ≤ s := size
  simp only [front,List.length_append,allbut_len,hp,hq,ite_true] at bound
  change gs.length ≤ _
  have cap : gs.length ≤ s-2+extraCount (n+m) C p q h k C.gates.length + ((3*n-6)+(3*m-6)) := by omega
  apply cap.trans
  apply Nat.add_le_add_right
  apply Nat.add_le_add_left
  apply Finset.card_le_card
  intro i hi
  simpa only [Finset.mem_filter,extra,marked,below] using hi
