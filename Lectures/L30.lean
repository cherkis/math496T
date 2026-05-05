import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/- # Lecture 30: Using Mathlib and AI

New tactic: **hint**
New concepts: **The Mathlib topology API on `ℝ` (`IsOpen`, `IsClosed`, `IsCompact`, `ContinuousOn`, `UniformContinuousOn`); the Heine–Cantor theorem.**

Recall: **`IsOpenSet`, `IsClosedSet`, `IsSeqCompact`, `ContinuousAt`, `ConvergesTo` (L24–L29), Heine–Borel sequential form and Cantor intersection (L29).**

## Overview

Every prior lecture built its tools from scratch; Mathlib already has them
all under different names.  Today we
- translate course-style predicates to their Mathlib counterparts (Part 1),
- collapse IVT and EVT to two-line proofs (Part 2),
- prove **Heine–Cantor** — continuous on compact implies uniformly continuous (Part 3), and
- meet the VS Code workflow that makes this practical (Part 4).

Look for the `-- search: ...` / `-- found: ...` markers above proofs: they
record the query that landed each lemma.  When you see only `-- search:`,
it is your turn — run the search yourself and fill the `sorry`.
-/

namespace L30

open Set Filter Topology Bornology

def IsOpenSet (U : Set ℝ) : Prop :=
  ∀ x ∈ U, ∃ ε > 0, ∀ y, |y - x| < ε → y ∈ U

def IsClosedSet (F : Set ℝ) : Prop := IsOpenSet Fᶜ

def ConvergesTo (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n, N ≤ n → |a n - L| < ε

def ContinuousAt (f : ℝ → ℝ) (c : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, |x - c| < δ → |f x - f c| < ε

def IsSeqCompactL30 (K : Set ℝ) : Prop :=
  ∀ a : ℕ → ℝ, (∀ n, a n ∈ K) →
    ∃ (s : ℕ → ℕ) (x : ℝ), x ∈ K ∧ StrictMono s ∧
      ConvergesTo (fun n => a (s n)) x

def UniformContinuousOn (f : ℝ → ℝ) (K : Set ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x ∈ K, ∀ y ∈ K, |x - y| < δ → |f x - f y| < ε


-- ============================================================================
-- ## Part 0: Rosetta stone
-- ============================================================================

/-
Dictionary, course-style ↔ Mathlib:

  `L30.IsOpenSet U`             ↔  `IsOpen U`
  `L30.IsClosedSet F`           ↔  `IsClosed F`
  `L30.IsSeqCompactL30 K`       ↔  `IsCompact K`            (on `ℝ`)
  `closed and bounded` on `ℝ`   ↔  `IsCompact K`
  `L30.ConvergesTo a L`         ↔  `Filter.Tendsto a atTop (𝓝 L)`
  `L30.ContinuousAt f c`        ↔  `ContinuousAt f c`       (filter form)
  `L30.UniformContinuousOn`     ↔  `UniformContinuousOn`

Two in-editor search commands; type either on a fresh line,
results appear in the InfoView.

 - `#leansearch "english query."` — natural-language search.  Phrase
   the query in **plain mathematical English** ("*continuous at a point
   epsilon delta definition.*"); the engine translates to Mathlib's
   internal vocabulary for you.  End the string with `.` or `?`.
 - `#loogle <pattern>` — type-pattern search; pattern is **unquoted**
   Lean code, `?a` is a pattern variable (repeated `?a` must match the
   same subterm), `_` is a wildcard, commas are AND.  Example:
   `#loogle IsCompact ?K, ContinuousOn ?f ?K, ∃ _ ∈ ?K, _`.  Useful
   *after* you know the Mathlib predicate names — typically once
   `#leansearch` has surfaced them.

The `hint` tactic and Mathlib's `exact?` / `apply?` / `rw?` close common
goals automatically and report which closer worked.
-/

#leansearch "limit of a sequence of uniformly continuous functions is continuous."
#loogle ContinuousOn ?f ?K , UniformContinuousOn ?f ?K

-- ============================================================================
-- ## Part 1: Bridges: course-style ↔ Mathlib
-- ============================================================================

/-! ### Bridge 1: open sets -/

/-- The course's `IsOpenSet` agrees with Mathlib's `IsOpen` on `ℝ`.
    `Metric.isOpen_iff` reduces `IsOpen` to ε-balls; `Real.dist_eq`
    rewrites `dist` as `|·-·|`. -/
-- search: #leansearch "open set every point has open ball inside."
-- found:  Metric.isOpen_iff
theorem isOpenSet_iff_isOpen (U : Set ℝ) : IsOpenSet U ↔ IsOpen U := by
  rw [Metric.isOpen_iff]; unfold IsOpenSet
  simp [Metric.ball, Real.dist_eq, abs_sub_comm, Set.subset_def]

/-- Mini-exercise 1.  Course-style closed agrees with Mathlib's. -/
-- search: #leansearch "complement of open is closed."
example (F : Set ℝ) : IsClosedSet F ↔ IsClosed F := by
  sorry

/-! ### Bridge 2: compactness as closed and bounded (Mathlib Heine–Borel) -/

-- search: #loogle IsCompact ?K ↔ IsClosed ?K ∧ Bornology.IsBounded ?K
-- found:  Metric.isCompact_iff_isClosed_bounded
example (K : Set ℝ) : IsCompact K ↔ IsClosed K ∧ IsBounded K :=
  Metric.isCompact_iff_isClosed_bounded

/-- Mini-exercise 2.  `[a, b]` is compact, directly from Heine–Borel. -/
-- search: #loogle IsCompact (Set.Icc _ _)
example (a b : ℝ) : IsCompact (Set.Icc a b) := by
  sorry

/-! ### Bridge 3: sequential compactness ↔ compactness on `ℝ` -/

/- On a metric space, `IsSeqCompact` and `IsCompact` agree.  The course's
   `L30.IsSeqCompact` uses `ConvergesTo`; bridge with `Metric.tendsto_atTop`. -/

/-- Forward direction of the seq-compact bridge:
    `L30.IsSeqCompact K → IsCompact K`. -/
-- search: #leansearch "sequence converges epsilon N definition."
-- found:  Metric.tendsto_atTop
theorem isCompact_of_isSeqCompact {K : Set ℝ} (hK : IsSeqCompactL30 K) :
    IsCompact K := by
  apply IsSeqCompact.isCompact -- This is Mathlib's IsSeqCompact, instead of our IsSeqCompactL30!
  intro a ha
  obtain ⟨s, x, hxK, hsmono, hconv⟩ := hK a ha
  refine ⟨x, hxK, s, hsmono, ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := hconv ε hε
  exact ⟨N, fun n hn => by simpa [Real.dist_eq] using hN n hn⟩

/-- Mini-exercise 3.  The reverse direction; mirror of the forward proof. -/
-- search: #leansearch "compact set is sequentially compact metric."
example {K : Set ℝ} (hK : IsCompact K) : IsSeqCompactL30 K := by
  sorry

/-- Mini-exercise 4.  Re-derive L29's `seqCompact_bounded` in two lines. -/
-- search: #leansearch "bounded set is contained in some closed ball around zero."
example {K : Set ℝ} (hK : IsSeqCompactL30 K) : ∃ M, ∀ x ∈ K, |x| ≤ M := by
  sorry

/-! ### Bridge 4: pointwise continuity -/

/-- The course's `ContinuousAt` agrees with Mathlib's. -/
-- search: #leansearch "continuous at a point epsilon delta definition."
-- found:  Metric.continuousAt_iff
theorem continuousAt_iff_continuousAt (f : ℝ → ℝ) (c : ℝ) :
    ContinuousAt f c ↔ _root_.ContinuousAt f c := by
    -- _root_.ContinuousAt is Mathlib's ContinuousAt, not our ContinuousAt
  rw [Metric.continuousAt_iff]
  unfold ContinuousAt
  simp [Real.dist_eq]

/-- Mini-exercise 5.  From the bridge above, deduce that course-style
    continuity on every point of a set yields Mathlib's `ContinuousOn`. -/
-- search: #leansearch "continuous on set iff continuous at every point."
example (f : ℝ → ℝ) (K : Set ℝ) (hf : ∀ c ∈ K, ContinuousAt f c) :
    ContinuousOn f K := by
  sorry


-- ============================================================================
-- ## Part 2: IVT and EVT — the two-line versions
-- ============================================================================

/- L26–L29 collapse into a few lines once the Mathlib names are in hand. -/

/-! ### IVT (Intermediate Value Theorem) -/

-- search: #leansearch "intermediate value theorem closed interval."
-- found:  intermediate_value_Icc
theorem ivt_mathlib {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a b)) {y : ℝ}
    (hy : y ∈ Set.Icc (f a) (f b)) : ∃ c ∈ Set.Icc a b, f c = y := by
  obtain ⟨c, hc, hfc⟩ := intermediate_value_Icc hab hf hy
  exact ⟨c, hc, hfc⟩

/-- Mini-exercise 6.  Every cubic `x ↦ x^3 + b*x + c` has a real root.
    Hint: at `x = -N` and `x = N` for sufficiently large `N`, the cubic
    has opposite signs. -/
-- try: tactic `hint`; or `#leansearch "intermediate value."`; or ask Copilot Chat
example (b c : ℝ) : ∃ x : ℝ, x^3 + b * x + c = 0 := by
  sorry

/-! ### EVT (Extreme Value Theorem) -/

/-- Mini-exercise 7.  EVT (max half) via Mathlib. -/
-- search: #loogle IsCompact ?K, ContinuousOn ?f ?K, ∃ _ ∈ ?K, ∀ _ ∈ ?K, _ ≤ _
example {K : Set ℝ} (hK : IsCompact K) (hKne : K.Nonempty)
    {f : ℝ → ℝ} (hf : ContinuousOn f K) :
    ∃ x ∈ K, ∀ y ∈ K, f y ≤ f x := by
  sorry

/-! ### Continuous image of a compact set is compact (synthesis) -/

/- Subsumes both EVT halves. -/
-- search: #loogle IsCompact ?K, ContinuousOn ?f ?K, IsCompact (?f '' ?K)
-- found:  IsCompact.image_of_continuousOn
theorem image_isCompact {K : Set ℝ} (hK : IsCompact K)
    {f : ℝ → ℝ} (hf : ContinuousOn f K) : IsCompact (f '' K) :=
  hK.image_of_continuousOn hf

/-- Mini-exercise 8.  Continuous image of `[a,b]` is closed and bounded.
    Combine `image_isCompact` with the Part-1 Heine–Borel bridge. -/
example {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a b)) :
    IsClosed (f '' Set.Icc a b) ∧ IsBounded (f '' Set.Icc a b) := by
  sorry


-- ============================================================================
-- ## Part 3: Heine–Cantor — the centerpiece
-- ============================================================================

/- *If `f` is continuous at every point of a sequentially compact `K`,*
*then for every `ε > 0` there is **one** `δ > 0`, independent of the point,*
*with `|x − y| < δ ⟹ |f x − f y| < ε` for all `x, y ∈ K`.*
   Compactness buys the uniform-in-the-point δ. -/

/-! ### The bridge for `UniformContinuousOn` -/

-- search: #leansearch "uniformly continuous on a set epsilon delta definition."
-- found:  Metric.uniformContinuousOn_iff
theorem uniformContinuousOn_iff_uniformContinuousOn (f : ℝ → ℝ) (K : Set ℝ) :
    UniformContinuousOn f K ↔ _root_.UniformContinuousOn f K := by
  rw [Metric.uniformContinuousOn_iff]
  unfold UniformContinuousOn
  simp [Real.dist_eq]

/-! ### The main theorem -/

-- search: #leansearch "continuous on compact set is uniformly continuous."
-- found:  IsCompact.uniformContinuousOn_of_continuous
theorem heine_cantor {K : Set ℝ} (hK : IsSeqCompactL30 K)
    {f : ℝ → ℝ} (hcont : ∀ c ∈ K, ContinuousAt f c) :
    UniformContinuousOn f K := by
  have hKc : IsCompact K := isCompact_of_isSeqCompact hK
  have hcontOn : ContinuousOn f K := fun c hc =>
    ((continuousAt_iff_continuousAt f c).mp (hcont c hc)).continuousWithinAt
  exact (uniformContinuousOn_iff_uniformContinuousOn f K).mpr
    (hKc.uniformContinuousOn_of_continuous hcontOn)

/-- Mini-exercise 9.  Every continuous function on `[a,b]` is uniformly
    continuous on `[a,b]`. -/
example (a b : ℝ) (f : ℝ → ℝ) (hf : ∀ c ∈ Set.Icc a b, ContinuousAt f c) :
    UniformContinuousOn f (Set.Icc a b) := by
  sorry

/-- Mini-exercise 10.  Uniform continuity *fails* on a non-compact set.
    Show that `f x = x^2` is **not** uniformly continuous on all of `ℝ`,
    using the pair `xₙ = n`, `yₙ = n + 1/(n+1)` for an `ε = 1` argument. -/
example : ¬ UniformContinuousOn (fun x : ℝ => x^2) Set.univ := by
  sorry


-- ============================================================================
-- ## Part 4: The VS Code workflow
-- ============================================================================

/-
### Reading the proof state

 - **Lean InfoView panel** — open with `Ctrl+Shift+Enter` (`Cmd` on
   macOS); shows the goal at the cursor.
 - **Hover** any identifier to see its type signature and docstring.
   Lemma names can be misleadingly similar (`continuous_iff` vs
   `Metric.continuous_iff` vs `Metric.continuousOn_iff`); hover and
   read.
 - **Problems pane** — errors, unsolved goals, `sorry` warnings.

### Inline Copilot suggestions  ←  the workflow you will use most

If you have GitHub Copilot Pro (free for students), the **Copilot Pro
panel** has a *Quick Settings* toggle that enables inline suggestions
for `.lean` files.  Turn it on once and forget about it.

Then, while you write Lean:

 - As soon as your cursor sits on a `sorry` or an incomplete tactic block,
   Copilot proposes the next line(s) as **ghost text** in the editor.
 - Press `Tab` to accept, `Ctrl+side arrow` to accept next word,
   `Esc` to reject, `Alt+]` / `Alt+[` to cycle through alternatives.
 - The suggestion is informed by your file's context — your
   definitions, the Mathlib lemmas in scope, and the goal state.
   Better context produces better suggestions.

How to use this well:

 1. **Write the statement first**, leaving `:= by sorry`.  Copilot's
    suggestions improve dramatically once it can see the goal.
 2. **Add a comment above the `sorry`** describing the
    strategy in plain English ("by IVT", "by Heine–Cantor on `[0,N]`
    plus a tail argument").  Copilot reads it.
    In fact, you can outline the whole proof as comments first.
 3. **Don't accept blindly.**  Move the cursor through what Copilot
    just inserted; the InfoView shows the goal after each line.
    If a step looks magical, hover the lemma it used.
 4. **If a suggestion is close but wrong**, edit it directly — Copilot
    re-suggests on the next character.  Faster than rejecting and
    starting over.

### When inline suggestions don't fire

 - **Closing tactics.**
   `hint` runs a battery of common closers (`exact?`, `aesop`, `omega`, `norm_num`, …) and reports which one worked.
   `exact?` / `apply?` / `rw?` search Mathlib for a single matching lemma or rewrite.
 - **`#leansearch "english query."`** and **`#loogle <pattern>`**
   are fall-back searches when you need a name Copilot didn't produce,
   or when you want to explore the API by hand.

### Copilot Chat sidebar (longer back-and-forth)

Inline suggestions handle one-line continuations.  For longer help,
open Copilot Chat (`Ctrl/Cmd+Alt+I`).

 1. Just open the file — Copilot reads it as context.
 2. Pose the goal in plain English: *"Prove the cubic-root example."*
 3. Ask for verification, not just code: *"Walk me through this proof."*
 4. `@workspace`/`@file` ask about your project's own definitions:
    *"@workspace where is `IsSeqCompactL30` defined and what is it about?"*

### `lean4-skills` slash commands

Type `/` in the Chat sidebar:

 - `/lean4:prove` — guided, cycle-by-cycle proving (best for learning).
 - `/lean4:autoprove` — hands-off attempt at the whole proof.
 - `/lean4:golf` — shortens a working proof without changing semantics.

### Worked example: inline suggestions, then golf
-/

  example : ∃ x ∈ Set.Icc (1 : ℝ) 2, x^4 - x - 1 = 0 := by sorry

/-
The proof has *moving parts*:
- continuity of a polynomial on an interval,
- sign of `f` at the endpoints,
- the right Mathlib form of IVT, and
- unpacking the existential.


Step 1.  Replace `sorry` with a blank line and add a one-line strategy
comment.

Step 2.  Watch Copilot's ghost text.  As you press `Tab` line by line,
or `Ctrl/Cmd+side arrow` see how the goal changes.

After each accepted line, glance at the InfoView: the goal shrinks.
Hover `continuous_pow`, `ContinuousOn.sub`, `intermediate_value_Icc`,
`Set.mem_Icc` to read what Copilot just used.

Step 3.  `/lean4:golf` rewrites the working proof (perhaps,in term mode).

Step 4.  If you want to just get the proof,
run `/lean4:autoprove` (or `/lean4:prove` for cycle-by-cycle stepping)
without inline help and see what the agent does end-to-end.

Step 5: To learn what the proof is about, run `/lean4:learn` and ask for an explanation of the proof, or of any lemma it used.

The recurring rhythm — **state ↦ suggestion ↦ verify ↦ accept** — is
the same loop the `-- search: ... / -- found: ...` markers in Parts 1–3
record by hand.
-/


-- ============================================================================
-- ## End-of-Lecture Exercises
-- ============================================================================

/- Warm-up -/

/-- L29's `seqCompact_closed` becomes a one-liner via the Part 1 bridges. -/
-- search: #leansearch "compact set is closed."
example {K : Set ℝ} (hK : IsSeqCompact K) : IsClosed K := by
  sorry

/- Core -/

/-- `Real.sqrt` is uniformly continuous on `[0, ∞)`.
    Two paths:
    (a) Find a Mathlib lemma directly.  Try
        `#leansearch "sqrt uniformly continuous."`.
    (b) Apply Heine–Cantor on `[0, N]` and a tail argument for `x ≥ N`. -/
example : UniformContinuousOn Real.sqrt (Set.Ici (0 : ℝ)) := by
  sorry

/-- Brouwer in 1D.  A continuous self-map of `[0,1]` has a fixed point.
    Hint: apply IVT to `g x = f x − x`. -/
example (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc (0 : ℝ) 1))
    (hmaps : ∀ x ∈ Set.Icc (0 : ℝ) 1, f x ∈ Set.Icc (0 : ℝ) 1) :
    ∃ c ∈ Set.Icc (0 : ℝ) 1, f c = c := by
  sorry

/- Challenging -/

/-- Dini's theorem on `[a,b]`.  A monotone (in `n`) sequence of continuous
    functions converging pointwise to a continuous limit on a compact set
    converges uniformly.

    Hint: search `#leansearch "Dini theorem monotone uniform convergence."`
    or `#loogle "TendstoUniformlyOn"`.  The relevant Mathlib name will
    begin with `tendstoUniformlyOn_` or live near `Monotone` /
    `Antitone` in `Topology.UniformSpace`. -/
example (a b : ℝ) (hab : a ≤ b)
    (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ)
    (hcontf : ∀ n, ContinuousOn (f n) (Set.Icc a b))
    (hcontg : ContinuousOn g (Set.Icc a b))
    (hmono : ∀ x ∈ Set.Icc a b, ∀ n, f n x ≤ f (n+1) x)
    (hpt : ∀ x ∈ Set.Icc a b, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x ∈ Set.Icc a b, |f n x - g x| < ε := by
  sorry

end L30
