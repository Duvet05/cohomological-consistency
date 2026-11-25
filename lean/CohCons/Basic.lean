import Mathlib

/-!
# Cohomological `k`-consistency: definitions and Section 2 of the note

* `Str L α`: relational structures over a signature `L` with carrier `α`.
* `PMap β α := β → Option α`: partial maps; `dom f` is the domain, `res f Y` the restriction.
  A family `H : Finset (PMap β α)` stands for the `k`-family `X ↦ {f ∈ H | dom f = X}`, and the
  integer variable `z_{X,f}` of the note is `z f` (the domain of `f` determines `X`).
* `Sys`, `Pinned`, `PinSolvable`: the system `L(B,H)` and its `(X,f)`-pinned version.
* `Stable`, `Accepts`: stable families (Definition 2.1) and acceptance via a nonempty one.
* `initial`, `Bad`, `Step`, `Run`, `Terminal`: the algorithm as a removal process.

Main results: `run_accepts_iff` (Lemma 2.2, for every order of removals),
`algAccepts_iff` (the algorithm's verdict equals `Accepts`) and `accepts_of_hom`
(Lemma 2.3(i)).
-/

open Finset Classical

noncomputable section

set_option linter.unusedSectionVars false

namespace CohCons

/-- A relational signature. -/
structure Sig where
  Sym : Type
  ar : Sym → ℕ

/-- A relational structure with carrier `α` over the signature `L`. -/
structure Str (L : Sig) (α : Type) where
  rel : (R : L.Sym) → Set (Fin (L.ar R) → α)

variable {L : Sig} {α β : Type}

/-- Homomorphisms. -/
def IsHom (B : Str L β) (A : Str L α) (h : β → α) : Prop :=
  ∀ R t, t ∈ B.rel R → h ∘ t ∈ A.rel R

/-- Partial maps. -/
abbrev PMap (β α : Type) := β → Option α

/-- The empty partial map. -/
def emp : PMap β α := fun _ => none

/-- Restriction of a partial map to `Y`. -/
def res (f : PMap β α) (Y : Finset β) : PMap β α := fun b => if b ∈ Y then f b else none

/-- Partial homomorphisms: every tuple of `B` inside the domain is mapped into `A`. -/
def IsPHom (B : Str L β) (A : Str L α) (f : PMap β α) : Prop :=
  ∀ R t a, t ∈ B.rel R → (∀ i, f (t i) = some (a i)) → a ∈ A.rel R

lemma res_apply_of_mem {f : PMap β α} {Y : Finset β} {b : β} (h : b ∈ Y) : res f Y b = f b := by
  simp [res, h]

lemma res_res (f : PMap β α) (X Y : Finset β) : res (res f X) Y = res f (Y ∩ X) := by
  funext b
  by_cases hY : b ∈ Y <;> by_cases hX : b ∈ X <;> simp [res, hX, hY]

lemma res_eq_of_agree {f g : PMap β α} {Y : Finset β} (h : ∀ b ∈ Y, f b = g b) :
    res f Y = res g Y := by
  funext b
  by_cases hb : b ∈ Y <;> simp [res, hb, h]

section dom

variable [Fintype β]

/-- The domain of a partial map. -/
def dom (f : PMap β α) : Finset β := univ.filter fun b => f b ≠ none

@[simp] lemma mem_dom {f : PMap β α} {b : β} : b ∈ dom f ↔ f b ≠ none := by
  simp [dom]

lemma dom_res (f : PMap β α) (Y : Finset β) : dom (res f Y) = Y ∩ dom f := by
  ext b
  by_cases h : b ∈ Y <;> simp [res, h]

lemma dom_res_of_subset {f : PMap β α} {Y : Finset β} (h : Y ⊆ dom f) : dom (res f Y) = Y := by
  rw [dom_res, Finset.inter_eq_left.mpr h]

lemma res_res_of_subset {f : PMap β α} {X Y : Finset β} (h : Y ⊆ X) :
    res (res f X) Y = res f Y := by
  rw [res_res, Finset.inter_eq_left.mpr h]

lemma res_dom (f : PMap β α) : res f (dom f) = f := by
  funext b
  by_cases h : f b = none <;> simp [res, h]

lemma dom_emp : dom (emp : PMap β α) = ∅ := by
  ext b; simp [emp]

lemma dom_eq_empty_iff (f : PMap β α) : dom f = ∅ ↔ f = emp := by
  constructor
  · intro h
    funext b
    have : b ∉ dom f := by rw [h]; exact Finset.notMem_empty b
    simpa [emp] using this
  · rintro rfl; exact dom_emp

/-- If `g` restricts to `f`, then `g` agrees with `f` on the domain of `f`. -/
lemma apply_eq_of_res_eq {f g : PMap β α} (h : res g (dom f) = f) {b : β} (hb : b ∈ dom f) :
    g b = f b := by
  rw [← h, res_apply_of_mem hb]

/-- A partial homomorphism maps every tuple inside its domain to a tuple of the template. -/
lemma IsPHom.exists_tuple {B : Str L β} {A : Str L α} {f : PMap β α} (hf : IsPHom B A f)
    {R : L.Sym} {t : Fin (L.ar R) → β} (ht : t ∈ B.rel R) (hdom : ∀ i, t i ∈ dom f) :
    ∃ a ∈ A.rel R, ∀ i, f (t i) = some (a i) := by
  have : ∀ i, ∃ x, f (t i) = some x := fun i =>
    Option.ne_none_iff_exists'.1 (mem_dom.1 (hdom i))
  choose a ha using this
  exact ⟨a, hf R t a ht ha, ha⟩

/-! ### The system `L(B,H)` -/

/-- The integer system `L(B,H)` at level `k`: equations (N) and (C). Equation (C) is stated
for `Y ⊆ X`; the instance `Y = X` holds automatically (`sys_iff_strict`). -/
def Sys (k : ℕ) (H : Finset (PMap β α)) (z : PMap β α → ℤ) : Prop :=
  (∀ X : Finset β, X.card ≤ k → ∑ f ∈ H with dom f = X, z f = 1) ∧
  (∀ X Y : Finset β, X.card ≤ k → Y ⊆ X → ∀ g ∈ H, dom g = Y →
      ∑ f ∈ H with dom f = X ∧ res f Y = g, z f = z g)

/-- The system exactly as written in the note, with (C) only for `Y ⊊ X`. -/
def SysStrict (k : ℕ) (H : Finset (PMap β α)) (z : PMap β α → ℤ) : Prop :=
  (∀ X : Finset β, X.card ≤ k → ∑ f ∈ H with dom f = X, z f = 1) ∧
  (∀ X Y : Finset β, X.card ≤ k → Y ⊂ X → ∀ g ∈ H, dom g = Y →
      ∑ f ∈ H with dom f = X ∧ res f Y = g, z f = z g)

lemma sys_iff_strict (k : ℕ) (H : Finset (PMap β α)) (z : PMap β α → ℤ) :
    Sys k H z ↔ SysStrict k H z := by
  constructor
  · rintro ⟨hN, hC⟩
    exact ⟨hN, fun X Y hX hYX => hC X Y hX hYX.subset⟩
  · rintro ⟨hN, hC⟩
    refine ⟨hN, fun X Y hX hYX g hg hgY => ?_⟩
    rcases hYX.ssubset_or_eq with h | rfl
    · exact hC X Y hX h g hg hgY
    · have : H.filter (fun f => dom f = Y ∧ res f Y = g) = {g} := by
        ext f
        simp only [mem_filter, mem_singleton]
        constructor
        · rintro ⟨-, hf, hfg⟩
          rw [← hfg, ← hf, res_dom]
        · rintro rfl
          exact ⟨hg, hgY, by rw [← hgY, res_dom]⟩
      rw [this, sum_singleton]

/-- The `(X,f₀)`-pinning, where `X = dom f₀`. -/
def Pinned (H : Finset (PMap β α)) (f₀ : PMap β α) (z : PMap β α → ℤ) : Prop :=
  ∀ f ∈ H, dom f = dom f₀ → z f = if f = f₀ then 1 else 0

/-- The `(X,f₀)`-pinned system has an integer solution. -/
def PinSolvable (k : ℕ) (H : Finset (PMap β α)) (f₀ : PMap β α) : Prop :=
  ∃ z, Sys k H z ∧ Pinned H f₀ z

/-! ### Stable families -/

/-- The solvability condition on a family. For `pin = true` it is (S3) of the note: every
pinned system has an integer solution (cohomological `k`-consistency). For `pin = false` it is
the existence of one unpinned solution (`ℤ`-affine `k`-consistency). -/
def Solvable (pin : Bool) (k : ℕ) (S : Finset (PMap β α)) : Prop :=
  match pin with
  | true => ∀ f ∈ S, PinSolvable k S f
  | false => ∃ z, Sys k S z

/-- Stable `k`-families (Definition 2.1). `phom` and `card_le` say that `S` is a `k`-family of
partial homomorphisms; `down`, `forth` are (S1), (S2), and `solv` is (S3) for `pin = true`.
For `pin = false` it is the condition of `ℤ`-affine `k`-consistency instead. -/
structure Stable (pin : Bool) (B : Str L β) (A : Str L α) (k : ℕ) (S : Finset (PMap β α)) :
    Prop where
  phom : ∀ f ∈ S, IsPHom B A f
  card_le : ∀ f ∈ S, (dom f).card ≤ k
  down : ∀ f ∈ S, ∀ Y ⊆ dom f, res f Y ∈ S
  forth : ∀ f ∈ S, ∀ X : Finset β, dom f ⊆ X → X.card ≤ k →
    ∃ g ∈ S, dom g = X ∧ res g (dom f) = f
  solv : Solvable pin k S

lemma Stable.pinned {B : Str L β} {A : Str L α} {k : ℕ} {S : Finset (PMap β α)}
    (hS : Stable true B A k S) : ∀ f ∈ S, PinSolvable k S f := hS.solv

/-- A family that is stable for the cohomological algorithm is stable for `ℤ`-affine
`k`-consistency: pinning at the empty map gives an unpinned solution. -/
lemma Stable.toAffine {B : Str L β} {A : Str L α} {k : ℕ} {S : Finset (PMap β α)}
    (hS : Stable true B A k S) (hemp : emp ∈ S) : Stable false B A k S where
  phom := hS.phom
  card_le := hS.card_le
  down := hS.down
  forth := hS.forth
  solv := by
    obtain ⟨z, hz, -⟩ := hS.pinned emp hemp
    exact ⟨z, hz⟩

/-- There is a nonempty stable `k`-family. For `pin = true` this is exactly acceptance by
cohomological `k`-consistency (Lemma 2.2, `algAccepts_iff`); for `pin = false` it is exactly
acceptance by `ℤ`-affine `k`-consistency (`affAlgAccepts_iff`). -/
def Accepts (pin : Bool) (k : ℕ) (B : Str L β) (A : Str L α) : Prop :=
  ∃ S, Stable pin B A k S ∧ emp ∈ S

/-- Cohomological `k`-consistency accepts only instances that `ℤ`-affine `k`-consistency
accepts. -/
theorem Accepts.toAffine {B : Str L β} {A : Str L α} {k : ℕ} (h : Accepts true k B A) :
    Accepts false k B A := by
  obtain ⟨S, hS, hemp⟩ := h
  exact ⟨S, hS.toAffine hemp, hemp⟩

/-! ### Zero extension -/

lemma sum_zero_ext {S H : Finset (PMap β α)} (hSH : S ⊆ H) (p : PMap β α → Prop)
    [DecidablePred p] (z : PMap β α → ℤ) :
    ∑ f ∈ H with p f, (if f ∈ S then z f else 0) = ∑ f ∈ S with p f, z f := by
  rw [← Finset.sum_filter, Finset.filter_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext f
  simp only [mem_filter]
  constructor
  · rintro ⟨-, hp, hS⟩; exact ⟨hS, hp⟩
  · rintro ⟨hS, hp⟩; exact ⟨hSH hS, hp, hS⟩

/-- A solution for a down-closed `S ⊆ H`, extended by zero, is a solution for `H`. -/
lemma sys_zero_ext {k : ℕ} {S H : Finset (PMap β α)} (hSH : S ⊆ H)
    (hdown : ∀ f ∈ S, ∀ Y ⊆ dom f, res f Y ∈ S) {z : PMap β α → ℤ} (hz : Sys k S z) :
    Sys k H (fun g => if g ∈ S then z g else 0) := by
  obtain ⟨hN, hC⟩ := hz
  refine ⟨?_, ?_⟩
  · intro X hX
    dsimp only
    rw [sum_zero_ext hSH]
    exact hN X hX
  · intro X Y hX hYX g hg hgY
    dsimp only
    rw [sum_zero_ext hSH (fun f => dom f = X ∧ res f Y = g)]
    by_cases hgS : g ∈ S
    · simp only [hgS, ↓reduceIte]
      exact hC X Y hX hYX g hgS hgY
    · simp only [hgS, ↓reduceIte]
      apply Finset.sum_eq_zero
      intro f hf
      rw [mem_filter] at hf
      exfalso
      apply hgS
      rw [← hf.2.2]
      exact hdown f hf.1 Y (by rw [hf.2.1]; exact hYX)

/-- A pinned solution for a down-closed `S ⊆ H`, extended by zero, is a pinned solution for
`H`. This is the step of Lemma 2.2 that needs care. -/
lemma pinSolvable_mono {k : ℕ} {S H : Finset (PMap β α)} (hSH : S ⊆ H)
    (hdown : ∀ f ∈ S, ∀ Y ⊆ dom f, res f Y ∈ S) {f₀ : PMap β α} (hf₀ : f₀ ∈ S)
    (h : PinSolvable k S f₀) : PinSolvable k H f₀ := by
  obtain ⟨z, hz, hP⟩ := h
  refine ⟨fun g => if g ∈ S then z g else 0, sys_zero_ext hSH hdown hz, ?_⟩
  · intro f hf hdomf
    by_cases hfS : f ∈ S
    · simp only [hfS, ↓reduceIte]
      exact hP f hfS hdomf
    · have hne : f ≠ f₀ := fun h => hfS (h ▸ hf₀)
      simp only [hfS, hne, ↓reduceIte]

/-! ### The algorithm -/

section algorithm

variable [Fintype α]

/-- Step 1: all partial homomorphisms with domain of size at most `k`. -/
def initial (B : Str L β) (A : Str L α) (k : ℕ) : Finset (PMap β α) :=
  univ.filter fun f => IsPHom B A f ∧ (dom f).card ≤ k

lemma mem_initial {B : Str L β} {A : Str L α} {k : ℕ} {f : PMap β α} :
    f ∈ initial B A k ↔ IsPHom B A f ∧ (dom f).card ≤ k := by
  simp [initial]

end algorithm

/-- `f` may be removed from `H`: by step (a) (a restriction is missing, or an extension is
missing) or by step (b) (the pinned system has no integer solution). -/
def Bad (k : ℕ) (H : Finset (PMap β α)) (f : PMap β α) : Prop :=
  (∃ Y ⊆ dom f, res f Y ∉ H) ∨
  (∃ X : Finset β, dom f ⊆ X ∧ X.card ≤ k ∧ ¬ ∃ g ∈ H, dom g = X ∧ res g (dom f) = f) ∨
  ¬ PinSolvable k H f

/-- One round of removals: any nonempty set of elements that are bad for the current family,
removed at once. Removing one element at a time is the special case of singletons. -/
def Step (k : ℕ) (H H' : Finset (PMap β α)) : Prop :=
  ∃ D ⊆ H, D.Nonempty ∧ (∀ f ∈ D, Bad k H f) ∧ H' = H \ D

/-- `H` is reachable from the initial family by removals. -/
def Run [Fintype α] (B : Str L β) (A : Str L α) (k : ℕ) (H : Finset (PMap β α)) : Prop :=
  Relation.ReflTransGen (Step k) (initial B A k) H

/-- No element can be removed any more: the loop has stopped. -/
def Terminal (k : ℕ) (H : Finset (PMap β α)) : Prop :=
  ∀ f ∈ H, ¬ Bad k H f

/-- Step 3: accept if `H(X)` is nonempty for every `X` of size at most `k`. -/
def Outcome (k : ℕ) (H : Finset (PMap β α)) : Prop :=
  ∀ X : Finset β, X.card ≤ k → ∃ f ∈ H, dom f = X

section algorithm

variable [Fintype α] {B : Str L β} {A : Str L α} {k : ℕ}

lemma run_subset {H : Finset (PMap β α)} (h : Run B A k H) : H ⊆ initial B A k := by
  induction h with
  | refl => exact subset_rfl
  | tail _ hstep ih =>
    obtain ⟨D, -, -, -, rfl⟩ := hstep
    exact Finset.sdiff_subset.trans ih

lemma not_bad {S H : Finset (PMap β α)} (hS : Stable true B A k S) (hSH : S ⊆ H)
    {f : PMap β α} (hf : f ∈ S) : ¬ Bad k H f := by
  rintro (⟨Y, hY, hres⟩ | ⟨X, hX, hXk, hno⟩ | hpin)
  · exact hres (hSH (hS.down f hf Y hY))
  · obtain ⟨g, hg, hgX, hgf⟩ := hS.forth f hf X hX hXk
    exact hno ⟨g, hSH hg, hgX, hgf⟩
  · exact hpin (pinSolvable_mono hSH hS.down hf (hS.pinned f hf))

/-- Every stable family stays inside the current family during every run. -/
lemma stable_subset_of_run {S H : Finset (PMap β α)} (hS : Stable true B A k S)
    (h : Run B A k H) : S ⊆ H := by
  induction h with
  | refl =>
    intro f hf
    rw [mem_initial]
    exact ⟨hS.phom f hf, hS.card_le f hf⟩
  | tail _ hstep ih =>
    obtain ⟨D, -, -, hbad, rfl⟩ := hstep
    intro f hf
    rw [Finset.mem_sdiff]
    exact ⟨ih hf, fun hD => not_bad hS ih hf (hbad f hD)⟩

lemma stable_of_terminal {H : Finset (PMap β α)} (hrun : Run B A k H) (hT : Terminal k H) :
    Stable true B A k H where
  phom f hf := (mem_initial.1 (run_subset hrun hf)).1
  card_le f hf := (mem_initial.1 (run_subset hrun hf)).2
  down f hf Y hY := by
    by_contra h
    exact hT f hf (Or.inl ⟨Y, hY, h⟩)
  forth f hf X hX hXk := by
    by_contra h
    exact hT f hf (Or.inr (Or.inl ⟨X, hX, hXk, h⟩))
  solv f hf := by
    by_contra h
    exact hT f hf (Or.inr (Or.inr h))

/-- **Lemma 2.2.** For every terminated run, in whatever order the removals were made, the
algorithm accepts if and only if there is a nonempty stable `k`-family. -/
theorem run_accepts_iff {H : Finset (PMap β α)} (hrun : Run B A k H) (hT : Terminal k H) :
    Outcome k H ↔ Accepts true k B A := by
  constructor
  · intro h
    refine ⟨H, stable_of_terminal hrun hT, ?_⟩
    obtain ⟨f, hf, hdom⟩ := h ∅ (by simp)
    rwa [(dom_eq_empty_iff f).1 hdom] at hf
  · rintro ⟨S, hS, hemp⟩ X hX
    obtain ⟨g, hg, hgX, -⟩ := hS.forth emp hemp X (by rw [dom_emp]; exact empty_subset X) hX
    exact ⟨g, stable_subset_of_run hS hrun hg, hgX⟩

/-- Every run can be continued until it stops. -/
theorem exists_terminal_run : ∃ H, Run B A k H ∧ Terminal k H := by
  suffices h : ∀ n, ∀ H : Finset (PMap β α), H.card = n → Run B A k H →
      ∃ H', Run B A k H' ∧ Terminal k H' from
    h _ _ rfl Relation.ReflTransGen.refl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro H hcard hrun
    by_cases hT : Terminal k H
    · exact ⟨H, hrun, hT⟩
    · unfold Terminal at hT
      push Not at hT
      obtain ⟨f, hf, hbad⟩ := hT
      have hstep : Step k H (H \ {f}) :=
        ⟨{f}, singleton_subset_iff.2 hf, singleton_nonempty f,
          fun g hg => by rw [mem_singleton.1 hg]; exact hbad, rfl⟩
      refine ih _ ?_ _ rfl (hrun.tail hstep)
      rw [← hcard, sdiff_singleton_eq_erase]
      exact card_erase_lt_of_mem hf

/-- The algorithm's verdict: some terminated run accepts. By `run_accepts_iff` all terminated
runs give the same verdict. -/
def AlgAccepts (k : ℕ) (B : Str L β) (A : Str L α) : Prop :=
  ∃ H, Run B A k H ∧ Terminal k H ∧ Outcome k H

theorem algAccepts_iff : AlgAccepts k B A ↔ Accepts true k B A := by
  constructor
  · rintro ⟨H, hrun, hT, hout⟩
    exact (run_accepts_iff hrun hT).1 hout
  · intro h
    obtain ⟨H, hrun, hT⟩ := exists_terminal_run (B := B) (A := A) (k := k)
    exact ⟨H, hrun, hT, (run_accepts_iff hrun hT).2 h⟩

/-- All terminated runs agree. -/
theorem outcome_independent {H H' : Finset (PMap β α)} (h : Run B A k H) (hT : Terminal k H)
    (h' : Run B A k H') (hT' : Terminal k H') : Outcome k H ↔ Outcome k H' :=
  (run_accepts_iff h hT).trans (run_accepts_iff h' hT').symm

end algorithm

/-! ### `ℤ`-affine `k`-consistency -/

section affine

variable [Fintype α] {B : Str L β} {A : Str L α} {k : ℕ}

/-- `S` is `k`-consistent: a `k`-family of partial homomorphisms with (S1) and (S2). -/
def Consistent (B : Str L β) (A : Str L α) (k : ℕ) (S : Finset (PMap β α)) : Prop :=
  (∀ f ∈ S, IsPHom B A f) ∧ (∀ f ∈ S, (dom f).card ≤ k) ∧
  (∀ f ∈ S, ∀ Y ⊆ dom f, res f Y ∈ S) ∧
  (∀ f ∈ S, ∀ X : Finset β, dom f ⊆ X → X.card ≤ k → ∃ g ∈ S, dom g = X ∧ res g (dom f) = f)

/-- The output `κ_k[B]` of the `k`-consistency algorithm: the largest `k`-consistent family. -/
def kcons (B : Str L β) (A : Str L α) (k : ℕ) : Finset (PMap β α) :=
  (initial B A k).filter fun f => ∃ S, Consistent B A k S ∧ f ∈ S

lemma subset_kcons {S : Finset (PMap β α)} (hS : Consistent B A k S) : S ⊆ kcons B A k := by
  intro f hf
  rw [kcons, mem_filter, mem_initial]
  exact ⟨⟨hS.1 f hf, hS.2.1 f hf⟩, S, hS, hf⟩

lemma consistent_kcons : Consistent B A k (kcons B A k) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro f hf
    exact (mem_initial.1 (mem_filter.1 hf).1).1
  · intro f hf
    exact (mem_initial.1 (mem_filter.1 hf).1).2
  · intro f hf Y hY
    obtain ⟨S, hS, hfS⟩ := (mem_filter.1 hf).2
    exact subset_kcons hS (hS.2.2.1 f hfS Y hY)
  · intro f hf X hX hXk
    obtain ⟨S, hS, hfS⟩ := (mem_filter.1 hf).2
    obtain ⟨g, hg, hgX, hgf⟩ := hS.2.2.2 f hfS X hX hXk
    exact ⟨g, subset_kcons hS hg, hgX, hgf⟩

/-- `ℤ`-affine `k`-consistency (Dalmau–Opršal; Lichter–Pago §5.1): accept if the system
`L(B, κ_k[B])` has an integer solution. -/
def AffAlgAccepts (k : ℕ) (B : Str L β) (A : Str L α) : Prop :=
  ∃ z, Sys k (kcons B A k) z

/-- `ℤ`-affine `k`-consistency accepts exactly when there is a nonempty `k`-consistent family
whose system `L(B,S)` has an integer solution, i.e. `Accepts false`. -/
theorem affAlgAccepts_iff : AffAlgAccepts k B A ↔ Accepts false k B A := by
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨h1, h2, h3, h4⟩ := consistent_kcons (B := B) (A := A) (k := k)
    refine ⟨kcons B A k, ⟨h1, h2, h3, h4, ⟨z, hz⟩⟩, ?_⟩
    have hN := hz.1 ∅ (by simp)
    obtain ⟨f, hf, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by rw [hN]; exact one_ne_zero)
    rw [mem_filter] at hf
    rw [← (dom_eq_empty_iff f).1 hf.2]
    exact hf.1
  · rintro ⟨S, hS, -⟩
    obtain ⟨z, hz⟩ := hS.solv
    have hcons : Consistent B A k S := ⟨hS.phom, hS.card_le, hS.down, hS.forth⟩
    exact ⟨_, sys_zero_ext (subset_kcons hcons) hS.down hz⟩

end affine

/-! ### Lemma 2.3(i): soundness -/

/-- **Lemma 2.3(i).** If `B → A`, the algorithm accepts `B` at every level. -/
theorem accepts_of_hom {pin : Bool} {B : Str L β} {A : Str L α} {h : β → α} (hh : IsHom B A h)
    (k : ℕ) : Accepts pin k B A := by
  let tot : PMap β α := fun b => some (h b)
  let S : Finset (PMap β α) :=
    ((univ : Finset (Finset β)).filter (fun X => X.card ≤ k)).image (res tot)
  have dom_tot : ∀ X, dom (res tot X) = X := fun X => by
    rw [dom_res]; ext b; simp [tot]
  have hmem : ∀ f, f ∈ S ↔ ∃ X : Finset β, X.card ≤ k ∧ res tot X = f := by
    intro f; simp [S]
  refine ⟨S, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rintro f hf R t a ht hta
    obtain ⟨X, -, rfl⟩ := (hmem f).1 hf
    have : a = h ∘ t := by
      funext i
      have := hta i
      by_cases hi : t i ∈ X
      · rw [res_apply_of_mem hi] at this
        exact (Option.some.inj this).symm
      · simp [res, hi] at this
    rw [this]
    exact hh R t ht
  · rintro f hf
    obtain ⟨X, hX, rfl⟩ := (hmem f).1 hf
    rwa [dom_tot]
  · rintro f hf Y hY
    obtain ⟨X, hX, rfl⟩ := (hmem f).1 hf
    rw [dom_tot] at hY
    rw [hmem]
    exact ⟨Y, (card_le_card hY).trans hX, (res_res_of_subset hY).symm⟩
  · rintro f hf X hX hXk
    obtain ⟨Y, -, rfl⟩ := (hmem f).1 hf
    rw [dom_tot] at hX ⊢
    exact ⟨res tot X, (hmem _).2 ⟨X, hXk, rfl⟩, dom_tot X, res_res_of_subset hX⟩
  · have hsys : Sys k S (fun _ => 1) := by
      refine ⟨?_, ?_⟩
      · intro X hX
        have : S.filter (fun f => dom f = X) = {res tot X} := by
          ext f
          simp only [mem_filter, hmem, mem_singleton]
          constructor
          · rintro ⟨⟨X', -, rfl⟩, hd⟩
            rw [dom_tot] at hd
            rw [hd]
          · rintro rfl
            exact ⟨⟨X, hX, rfl⟩, dom_tot X⟩
        rw [this, sum_singleton]
      · intro X Y hX hYX g hg hgY
        obtain ⟨Y', -, rfl⟩ := (hmem g).1 hg
        rw [dom_tot] at hgY
        subst hgY
        have : S.filter (fun f => dom f = X ∧ res f Y' = res tot Y') = {res tot X} := by
          ext f
          simp only [mem_filter, hmem, mem_singleton]
          constructor
          · rintro ⟨⟨X', -, rfl⟩, hd, -⟩
            rw [dom_tot] at hd
            rw [hd]
          · rintro rfl
            exact ⟨⟨X, hX, rfl⟩, dom_tot X, res_res_of_subset hYX⟩
        rw [this, sum_singleton]
    cases pin with
    | false => exact ⟨_, hsys⟩
    | true =>
      intro f₀ hf₀
      refine ⟨fun _ => 1, hsys, ?_⟩
      intro f hf hd
      obtain ⟨X, -, rfl⟩ := (hmem f).1 hf
      obtain ⟨X₀, -, rfl⟩ := (hmem f₀).1 hf₀
      rw [dom_tot, dom_tot] at hd
      subst hd
      simp
  · rw [hmem]
    refine ⟨∅, by simp, ?_⟩
    funext b
    simp [res, emp]

end dom

end CohCons
