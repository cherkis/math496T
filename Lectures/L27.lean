import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/- # Lecture 27: Continuity, Connectedness, and the Intermediate Value Theorem (IVT)

New concepts: **ε-δ continuity, forward sequential continuity, subspace-open sets, connectedness, the Intermediate Value Theorem**
New tactics: **`lt_trichotomy`, `set ... with`**
New Mathlib API: **`lt_min`, `mul_le_mul_of_nonneg_left`, `mul_lt_mul_right`, `abs_of_pos`, `eq_or_lt_of_le`, `lt_or_eq_of_le`, `Set.union_comm`, `Set.inter_comm`**


Recall: **`ConvergesTo` (L24), `IsOpenSet` (L26), `exists_between_sup_minus_eps`, `le_csSup`, `csSup_le` (L22), `min_le_left`, `min_le_right` (L26), `abs_add_le`, `abs_mul`, `abs_of_nonpos`, `abs_lt`, `le_antisymm` (L20, L24, L25), `Set.mem_iUnion` (L11), `choose!` (L01, L18)**

## Overview

The Intermediate Value Theorem (IVT) is the first deep theorem that is *topological*:

 1. Continuity is the condition that preimages of open sets are open.
 2. `[a, b]` cannot be split into two disjoint nonempty open pieces — it is
    **connected**.
 3. A nowhere vanishing `f` would split `[a, b]` into the pieces where
    `f < 0` and where `f > 0`, a contradiction.

So IVT is really a statement about connectedness plus continuity — two
topological ideas, each good for its own reason.

(We wrap the lecture in `namespace L27` so our names
`ContinuousAt`, `IsConnected`, etc., do not collide
with their abstract Mathlib counterparts.)
-/

namespace L27

def IsOpenSet (U : Set ℝ) : Prop :=
  ∀ x ∈ U, ∃ ε > 0, ∀ y, |y - x| < ε → y ∈ U

def ConvergesTo (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n, N ≤ n → |a n - L| < ε

/-- Local copy of the sSup ε-approximation lemma from L22. -/
theorem exists_between_sup_minus_eps
    (S : Set ℝ) (hS : S.Nonempty) (_hB : BddAbove S) (ε : ℝ) (hε : 0 < ε) :
    ∃ x ∈ S, sSup S - ε < x := by
  by_contra! h
  have : sSup S ≤ sSup S - ε := by
    apply csSup_le hS
    exact h
  linarith


-- ============================================================================
-- ## Part 1: ε-δ continuity
-- ============================================================================

/-
A function `f : ℝ → ℝ` is **continuous at `c`** if
for every tolerance `ε > 0` there is
some `δ > 0` such that inputs within `δ` of `c`
produce outputs within `ε` of `f c`.

It is continuous on a set `S` if it is continuous at every point of `S`.
-/

def ContinuousAt (f : ℝ → ℝ) (c : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, |x - c| < δ → |f x - f c| < ε

def ContinuousOn (f : ℝ → ℝ) (S : Set ℝ) : Prop :=
  ∀ c ∈ S, ContinuousAt f c

example (c : ℝ) : ContinuousAt (fun x => 2 * x) c := by
  intro ε hε
  use ε/2, (by linarith)
  simp
  intro x h
  rw [← mul_sub, abs_mul, abs_of_nonneg zero_le_two]
  linarith

/-
For `f(x) = x²` the standard trick is the factorization
 `x² − c² = (x − c)(x + c)`.
If `|x − c| < 1` then `|x + c| ≤ 2|c| + 1`, so choosing
 `δ = min 1 (ε / (2|c| + 1))`
forces `|x² − c²| < ε`.
-/

#check mul_le_mul_of_nonneg_right
#check add_pos_of_nonneg_of_pos
#check mul_div_cancel₀
#check sub_add_cancel
example (a b : ℝ) : a - b + b = a := by exact?

example (c : ℝ) : ContinuousAt (fun x => x ^ 2) c := by
  intro ε hε
  use min 1 (ε / (2 * |c| + 1)), by positivity
  intro x hx
  simp
  -- have h1 : |x - c| < 1 := lt_of_lt_of_le hx (min_le_left _ _)
  -- or alternatively use calc
  rw [sq_sub_sq,abs_mul]
  nth_rw 1 [←sub_add_cancel x c]
  rw [add_assoc,← two_mul,add_comm]
  rw [← mul_div_cancel₀ ε (by positivity : 2*|c|+1 ≠ 0)]
  apply mul_lt_mul''
  . apply lt_of_le_of_lt (abs_add (2*c) (x-c))
    rw [abs_mul,abs_of_pos,add_lt_add_iff_left]
    apply lt_of_lt_of_le hx
    apply min_le_left
    exact two_pos
  . apply lt_of_lt_of_le hx
    apply min_le_right
  apply abs_nonneg
  apply abs_nonneg
/- alternative calc:
  calc
   |x ^ 2 - c ^ 2| = |(x-c + 2 * c)* (x-c)| := by ring
    _          ≤ (2*|c|+1)*|x-c| := by rw [abs_mul]
                                       apply mul_le_mul_of_nonneg_right _ (abs_nonneg (x-c))
                                       apply le_trans (abs_add (x-c) (2*c))
                                       rw [add_comm _ 1,abs_mul]; simp; apply le_of_lt; apply lt_of_lt_of_le hx; apply min_le_left
    _          < (2*|c|+1) * min 1 (ε / (2 * |c| + 1)) := by apply mul_lt_mul_of_pos_left hx; positivity
    _          ≤ (2*|c|+1) * (ε / (2 * |c| + 1)) := by apply mul_le_mul_of_nonneg_left; apply min_le_right; positivity
    _          ≤ ε := by rw [mul_div_cancel₀ ε (by positivity)]
-/

-- could use `field_simp`, `ring_nf`


-- **Practice**: `f x = x ^ 3` is continuous at every `c`.
example (c : ℝ) : ContinuousAt (fun x => 3 * x + 2) c := by
  sorry


-- ============================================================================
-- ## Part 2: Forward sequential continuity and sum of continuous functions
-- ============================================================================

/-
If `f` is continuous at `c` and `aₙ → c`, then `f(aₙ) → f c`.
The converse is proved in L28 Part 1 — completing the ε-δ/sequences dictionary.

The proof below introduces the **`min δ₁ δ₂`** pattern for combining two
thresholds — the analogue of `max N₁ N₂` from L24.
-/

theorem continuousAt_seq_forward {f : ℝ → ℝ} {c : ℝ} (hf : ContinuousAt f c) :
    ∀ a : ℕ → ℝ, ConvergesTo a c → ConvergesTo (fun n => f (a n)) (f c) := by
  intro a ha ε hε
  obtain ⟨δ, hδ, hfδ⟩ := hf ε hε
  obtain ⟨N, hN⟩ := ha δ hδ
  use N
  intro n hn
  apply hfδ (a n)
  apply hN n
  exact hn

theorem continuousAt_add {f g : ℝ → ℝ} {c : ℝ}
    (hf : ContinuousAt f c) (hg : ContinuousAt g c) :
    ContinuousAt (fun x => f x + g x) c := by
  intro ε hε
  obtain ⟨δ₁, hδ₁, hf'⟩ := hf (ε / 2) (by linarith)
  obtain ⟨δ₂, hδ₂, hg'⟩ := hg (ε / 2) (by linarith)
  use min δ₁ δ₂, lt_min hδ₁ hδ₂
  intro x hx
  have h1 := hf' x (lt_of_lt_of_le hx (min_le_left _ _))
  have h2 := hg' x (lt_of_lt_of_le hx (min_le_right _ _))
  calc |(f x + g x) - (f c + g c)|
      = |(f x - f c) + (g x - g c)| := by ring_nf
    _ ≤ |f x - f c| + |g x - g c| := abs_add_le _ _
    _ < ε / 2 + ε / 2 := by linarith
    _ = ε := by ring

-- **Practice**: `c * f` is continuous at the same point.
example (f : ℝ → ℝ) (c p : ℝ) (hf : ContinuousAt f p) :
    ContinuousAt (fun x => c * f x) p := by
  sorry


-- ============================================================================
-- ## Part 3: Subspace-open sets and connectedness
-- ============================================================================

/-
Topology on a subspace `S ⊆ ℝ` is built from open subsets of `ℝ` by intersecting with `S`.
A set `U ⊆ S` is **open in `S`** if `U = V ∩ S`
for some ambient-open `V`.

A pair `U, V ⊆ S` **separates** `S` if each is open in `S`, both are
nonempty, disjoint, and their union is all of `S`:
`U ∩ V = ∅`
`U ∪ V = S`.
`S` is **connected** if no separation exists.
-/

def IsOpenIn (U : Set ℝ) (S : Set ℝ) : Prop :=
  ∃ V : Set ℝ, IsOpenSet V ∧ U = V ∩ S

def Separates (U V S : Set ℝ) : Prop :=
  IsOpenIn U S ∧ IsOpenIn V S ∧ U ∪ V = S ∧
    U.Nonempty ∧ V.Nonempty ∧ U ∩ V = ∅

def IsConnected (S : Set ℝ) : Prop := ¬ ∃ U V, Separates U V S

/-
*Background motivation, not formalized:* `ℚ` is disconnected.  One cut is at
`√2`: the rationals below `√2` and the rationals above `√2` are each open in `ℚ`,
nonempty, disjoint, and cover `ℚ`, because `√2` is itself not a rational number.
The absence of `√2` from `ℚ` is exactly what makes `ℚ` fail to be connected.
-/

-- **Practice**: the two-point set `{a, b}` with `a ≠ b` is not connected.
example (a b : ℝ) (hab : a ≠ b) : ¬ IsConnected ({a, b} : Set ℝ) := by
  sorry


-- ============================================================================
-- ## Part 4: `[a, b]` is connected
-- ============================================================================

/-
We now prove the key topological fact underlying IVT: every closed interval
is connected.  The proof builds a sSup `c` of "how far the `U`-component
reaches from `a`" and derives a contradiction whichever of `U`, `V` contains
`c`.  The `c ∈ V` case relies on the sSup approximation theorem from L22.
-/

theorem Icc_connected (a b : ℝ) (hab : a ≤ b) :
    IsConnected (Set.Icc a b) := by
  /-
  Assume a separation `[a, b] = U ∪ V`, disjoint, nonempty, open in the
  subspace, and swap so `a ∈ U`.

  Let `T = {x ∈ [a, b] | [a, x] ⊆ U}` and let `c = sSup T`.

  If `c ∈ U`, openness pushes a bit right of `c`, contradiction to sup.
  If `c ∈ V`, openness of `V` plus points of `T` approaching `c` from the left
  gives a point in `U ∩ V`, contradiction.

  Hence no separation. So `[a, b]` connected.

  *Full Lean proof is in Addendum below.*
  -/
  sorry


-- ============================================================================
-- ## Part 5: The Intermediate Value Theorem (climax)
-- ============================================================================

/-
If `f` is continuous on `[a, b]` with `f a < 0 < f b`, then `f` takes the
value `0` somewhere strictly between `a` and `b`.

The proof: assume otherwise, and split `[a, b]` into the subspace-open
"negative" and "positive" pieces.  These separate `[a, b]`, contradicting
Part 4.
-/

lemma neg_neighborhood {f : ℝ → ℝ} {x : ℝ}
    (hf : ContinuousAt f x) (hx : f x < 0) :
    ∃ δ > 0, ∀ y, |y - x| < δ → f y < 0 := by
  obtain ⟨δ, hδ, hfδ⟩ := hf (- f x / 2) (by linarith)
  use δ, hδ
  intro y hy
  have h := hfδ y hy
  rw [abs_lt] at h
  linarith [h.2]

lemma pos_neighborhood {f : ℝ → ℝ} {x : ℝ}
    (hf : ContinuousAt f x) (hx : 0 < f x) :
    ∃ δ > 0, ∀ y, |y - x| < δ → 0 < f y := by
  obtain ⟨δ, hδ, hfδ⟩ := hf (f x / 2) (by linarith)
  use δ, hδ
  intro y hy
  have h := hfδ y hy
  rw [abs_lt] at h
  linarith [h.1]

/-- Local characterization of subspace-openness: if every point of `U` has an
ambient ε-neighborhood whose intersection with `S` lies in `U`, and `U ⊆ S`,
then `U` is open in `S`. -/
lemma isOpenIn_of_local (U S : Set ℝ) (hUS : U ⊆ S)
    (h : ∀ x ∈ U, ∃ ε > 0, ∀ y ∈ S, |y - x| < ε → y ∈ U) :
    IsOpenIn U S := by
  -- `choose!` extracts the tolerance function `ε : ℝ → ℝ` and its two
  -- properties simultaneously.  The ambient witness `V` is the union of
  -- the ε-balls centered at points of `U`.
  choose! ε hε_pos hε_prop using h
  dsimp [IsOpenIn]
  use ⋃ x ∈ U, {y : ℝ | |y - x| < ε x}
  constructor
  · -- `V` is ambient-open.
    intro y hy
    simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hy
    obtain ⟨x, hxU, hyx⟩ := hy
    use ε x - |y - x|, by linarith
    intro z hz
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    use x, hxU
    calc |z - x| = |(z - y) + (y - x)| := by ring_nf
      _ ≤ |z - y| + |y - x| := abs_add_le _ _
      _ < (ε x - |y - x|) + |y - x| := by linarith
      _ = ε x := by ring
  · -- `U = V ∩ S`.
    ext y
    simp only [Set.mem_inter_iff, Set.mem_iUnion, Set.mem_setOf_eq]
    constructor
    · intro hyU
      constructor
      use y
      use hyU
      simp
      exact hε_pos y hyU
      exact hUS hyU
    · rintro ⟨⟨x, hxU, hyx⟩, hyS⟩
      apply hε_prop x hxU y
      apply hyS
      exact hyx

theorem IVT (f : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hcont : ∀ c ∈ Set.Icc a b, ContinuousAt f c)
    (hfa : f a < 0) (hfb : 0 < f b) :
    ∃ c ∈ Set.Ioo a b, f c = 0 := by
  by_contra! hne
  set U : Set ℝ := Set.Icc a b ∩ {x | f x < 0} with hU_def
  set V : Set ℝ := Set.Icc a b ∩ {x | 0 < f x} with hV_def
  have hab_le : a ≤ b := le_of_lt hab
  apply Icc_connected a b hab_le
  use U, V
  unfold Separates
  -- Six goals: `U` and `V` open-in, their union is `[a, b]`, each is
  -- nonempty, their intersection is empty.
  refine ⟨?open_U, ?open_V, ?cover, ?neU, ?neV, ?disj⟩
  . apply isOpenIn_of_local U (Set.Icc a b) (fun _ hx => hx.1)
    intro x hx
    obtain ⟨δ, hδ, hδneg⟩ := neg_neighborhood (hcont x hx.1) hx.2
    use δ, hδ
    intro y hyS hyx
    constructor
    . exact hyS
    . exact hδneg y hyx
  . apply isOpenIn_of_local V (Set.Icc a b) (fun _ hx => hx.1)
    intro x hx
    obtain ⟨δ, hδ, hδpos⟩ := pos_neighborhood (hcont x hx.1) hx.2
    use δ, hδ
    intro y hyS hyx
    constructor
    . exact hyS
    . exact hδpos y hyx
  . ext x
    simp only [hU_def, hV_def, Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
    · intro hx
      -- `lt_trichotomy`: for any two reals, one of `<`, `=`, `>` holds.
      rcases lt_trichotomy (f x) 0 with h | h | h
      · exact Or.inl ⟨hx, h⟩
      · exfalso
        obtain ⟨hxa, hxb⟩ := hx
        rcases eq_or_lt_of_le hxa with heq | hxa'
        · rw [← heq] at h; linarith
        rcases eq_or_lt_of_le hxb with heq | hxb'
        · rw [heq] at h; linarith
        exact hne x ⟨hxa', hxb'⟩ h
      · exact Or.inr ⟨hx, h⟩
  . use a
    exact ⟨⟨le_refl a, hab_le⟩, hfa⟩
  . use b
    exact ⟨⟨hab_le, le_refl b⟩, hfb⟩
  . ext x
    simp only [hU_def, hV_def, Set.mem_inter_iff, Set.mem_empty_iff_false,
               iff_false, not_and, Set.mem_setOf_eq]
    intro ⟨_, h1⟩ ⟨_, h2⟩
    linarith


-- ============================================================================
-- ## Addendum: full proof that `[a, b]` is connected
-- ============================================================================

/-
This addendum contains the full supremum-based proof sketched in Part 4.
It is not used by the main lecture flow, which now keeps only the theorem
statement and the proof idea.
-/

/-- Main helper for the addendum proof: if `a ∈ U` and `U, V` separate
`[a, b]`, we derive `False`. -/
lemma no_sep_from_a_addendum {a b : ℝ} (hab : a ≤ b) {U V : Set ℝ}
    (openU : IsOpenIn U (Set.Icc a b)) (openV : IsOpenIn V (Set.Icc a b))
    (cover : U ∪ V = Set.Icc a b) (_neU : U.Nonempty) (neV : V.Nonempty)
    (disj : U ∩ V = ∅) (haU : a ∈ U) : False := by
  set T : Set ℝ := {x | x ∈ Set.Icc a b ∧ Set.Icc a x ⊆ U} with hT_def
  have haT : a ∈ T := by
    refine ⟨⟨le_refl a, hab⟩, ?_⟩
    intro y hy
    have : y = a := le_antisymm hy.2 hy.1
    rw [this]
    exact haU
  have hTne : T.Nonempty := ⟨a, haT⟩
  have hTbdd : BddAbove T := ⟨b, fun x hx => hx.1.2⟩
  set c := sSup T with hc_def
  have hac : a ≤ c := le_csSup hTbdd haT
  have hcb : c ≤ b := csSup_le hTne (fun x hx => hx.1.2)
  have hcIcc : c ∈ Set.Icc a b := ⟨hac, hcb⟩
  have hcUV : c ∈ U ∨ c ∈ V := by
    rw [← cover] at hcIcc
    exact hcIcc
  have hseg_below : ∀ x, a ≤ x → x < c → x ∈ U := by
    intro x hax hxc
    obtain ⟨s, hsT, hsx⟩ :=
      exists_between_sup_minus_eps T hTne hTbdd (c - x) (by linarith)
    exact hsT.2 ⟨hax, by linarith⟩
  rcases hcUV with hcU | hcV
  · obtain ⟨W, hWopen, hUeq⟩ := openU
    have hcW : c ∈ W := by
      rw [hUeq] at hcU
      exact hcU.1
    obtain ⟨δ, hδ, hball⟩ := hWopen c hcW
    by_cases hcb_eq : c = b
    · obtain ⟨v, hvV⟩ := neV
      have hvIcc : v ∈ Set.Icc a b := by
        rw [← cover]
        exact Or.inr hvV
      have hvU : v ∈ U := by
        by_cases hvc : v < c
        · exact hseg_below v hvIcc.1 hvc
        · push_neg at hvc
          have hvc' : v = c := le_antisymm (hcb_eq ▸ hvIcc.2) hvc
          rw [hvc']
          exact hcU
      have hcon : v ∈ U ∩ V := ⟨hvU, hvV⟩
      rw [disj] at hcon
      exact hcon
    · have hcb_lt : c < b := lt_of_le_of_ne hcb hcb_eq
      set t := min b (c + δ / 2) with ht_def
      have htb : t ≤ b := min_le_left _ _
      have htgt : c < t := by
        rw [ht_def]
        simp only [lt_min_iff]
        exact ⟨hcb_lt, by linarith⟩
      have hta : a ≤ t := le_of_lt (lt_of_le_of_lt hac htgt)
      have htT : t ∈ T := by
        refine ⟨⟨hta, htb⟩, ?_⟩
        intro x hx
        obtain ⟨hxa, hxt_le⟩ := hx
        by_cases hxc : x < c
        · exact hseg_below x hxa hxc
        push_neg at hxc
        rcases eq_or_lt_of_le hxc with hxc_eq | hxc_lt
        · rw [← hxc_eq]
          exact hcU
        have ht_le : t ≤ c + δ / 2 := min_le_right _ _
        have hxt : x ≤ c + δ / 2 := le_trans hxt_le ht_le
        have hxb : x ≤ b := le_trans hxt_le htb
        have hxW : x ∈ W := by
          apply hball
          rw [abs_of_pos (by linarith : (0 : ℝ) < x - c)]
          linarith
        rw [hUeq]
        exact ⟨hxW, ⟨hxa, hxb⟩⟩
      exact absurd (le_csSup hTbdd htT) (not_le.mpr htgt)
  · obtain ⟨W, hWopen, hVeq⟩ := openV
    have hcW : c ∈ W := by
      rw [hVeq] at hcV
      exact hcV.1
    obtain ⟨δ, hδ, hball⟩ := hWopen c hcW
    have hac_lt : a < c := by
      rcases lt_or_eq_of_le hac with h | h
      · exact h
      · exfalso
        have : a ∈ U ∩ V := ⟨haU, h ▸ hcV⟩
        rw [disj] at this
        exact this
    set η := min (δ / 2) ((c - a) / 2) with hη_def
    have hη_pos : 0 < η := by
      rw [hη_def]
      simp only [lt_min_iff]
      exact ⟨by linarith, by linarith⟩
    obtain ⟨x, hxT, hxlt⟩ :=
      exists_between_sup_minus_eps T hTne hTbdd η hη_pos
    have hxc : x ≤ c := le_csSup hTbdd hxT
    have hxU : x ∈ U := hxT.2 ⟨hxT.1.1, le_refl x⟩
    have hxδ : |x - c| < δ := by
      rw [abs_of_nonpos (by linarith : x - c ≤ 0)]
      have h1 : c - x < η := by linarith
      have h2 : η ≤ δ / 2 := min_le_left _ _
      linarith
    have hxW : x ∈ W := hball x hxδ
    have hxV : x ∈ V := by
      rw [hVeq]
      exact ⟨hxW, hxT.1⟩
    have hcon : x ∈ U ∩ V := ⟨hxU, hxV⟩
    rw [disj] at hcon
    exact hcon

theorem Icc_connected' (a b : ℝ) (hab : a ≤ b) :
    IsConnected (Set.Icc a b) := by
  rintro ⟨U, V, openU, openV, cover, neU, neV, disj⟩
  have haIcc : a ∈ Set.Icc a b := ⟨le_refl a, hab⟩
  have haUV : a ∈ U ∪ V := by
    rw [cover]
    exact haIcc
  rcases haUV with haU | haV
  · exact no_sep_from_a_addendum hab openU openV cover neU neV disj haU
  · refine no_sep_from_a_addendum hab openV openU ?_ neV neU ?_ haV
    · rw [Set.union_comm]
      exact cover
    · rw [Set.inter_comm]
      exact disj


-- ============================================================================
-- ## End-of-Lecture Exercises
-- ============================================================================

/- Warm-up -/

example (c p : ℝ) : ContinuousAt (fun _ : ℝ => c) p := by
  sorry

example (c p : ℝ) : ContinuousAt (fun x : ℝ => x + c) p := by
  sorry

/- Core -/

example (f g : ℝ → ℝ) (c : ℝ)
    (hf : ContinuousAt f c) (hg : ContinuousAt g c) :
    ContinuousAt (fun x => f x * g x) c := by
  sorry

example (a : ℝ) : IsConnected ({a} : Set ℝ) := by
  sorry

/- Challenging -/

example (f : ℝ → ℝ) (hcont : ∀ c, ContinuousAt f c)
    (hQ : ∀ q : ℚ, f (q : ℝ) = 0) : ∀ x, f x = 0 := by
  sorry

end L27
