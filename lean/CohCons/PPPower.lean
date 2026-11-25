import CohCons.Equality

/-!
# Lemma 3.2: pp-powers

A `d`-th pp-power `Δ` of `Γ` is given by one primitive positive formula `φ R` per symbol `R` of
`Δ`, with free variables `x_{a,i}` indexed by `(a, i) : Fin (ar R) × Fin d`. For a `Δ`-instance
`I`, `gadget φ I` is the instance `I^♯` of the note: universe `V × [d]` plus fresh elements
`(e, j)`, and one tuple per constraint `e` and atom of `φ_R`.
-/

open Finset Classical

noncomputable section

set_option linter.unusedSectionVars false

namespace CohCons

variable {L L' : Sig} {G V : Type}

/-- An atomic formula `S(w̄)` over `L` with variables in `X`. -/
structure Atom (L : Sig) (X : Type) where
  sym : L.Sym
  args : Fin (L.ar sym) → X

/-- A primitive positive formula `∃ y_1 … y_m. ⋀ atoms` with free variables `ι`; the bound
variables are `Fin m`. -/
structure PPFormula (L : Sig) (ι : Type) where
  m : ℕ
  atoms : List (Atom L (ι ⊕ Fin m))

/-- `Γ ⊨ φ(a)`. -/
def PPFormula.Holds {ι : Type} (Γ : Str L G) (φ : PPFormula L ι) (a : ι → G) : Prop :=
  ∃ w : Fin φ.m → G, ∀ q ∈ φ.atoms, Sum.elim a w ∘ q.args ∈ Γ.rel q.sym

/-- `Δ` is the `d`-th pp-power of `Γ` defined by the formulas `φ`:
`R^Δ = {(ā_1, …, ā_r) | Γ ⊨ φ_R(ā_1, …, ā_r)}`, where `a p.1 p.2` is coordinate `p.2` of
`ā_{p.1}`. -/
def IsPPPower (Γ : Str L G) (d : ℕ) (Δ : Str L' (Fin d → G))
    (φ : ∀ R : L'.Sym, PPFormula L (Fin (L'.ar R) × Fin d)) : Prop :=
  ∀ R a, a ∈ Δ.rel R ↔ (φ R).Holds Γ (fun p => a p.1 p.2)

/-- Constraints `e = (R, v̄)` with `v̄ ∈ R^I`. -/
abbrev Con (I : Str L' V) := Σ R : L'.Sym, {t : Fin (L'.ar R) → V // t ∈ I.rel R}

section gadget

variable {d : ℕ} (φ : ∀ R : L'.Sym, PPFormula L (Fin (L'.ar R) × Fin d))

/-- The universe of `I^♯`. -/
abbrev GU (I : Str L' V) := (V × Fin d) ⊕ (Σ e : Con I, Fin (φ e.1).m)

/-- The substitution `x_{a,i} ↦ (v_a, i)`, `y_j ↦ (e, j)` for the constraint `e`. -/
def gsub (I : Str L' V) (e : Con I) : (Fin (L'.ar e.1) × Fin d) ⊕ Fin (φ e.1).m → GU φ I :=
  Sum.elim (fun p => Sum.inl (e.2.1 p.1, p.2)) (fun j => Sum.inr ⟨e, j⟩)

@[simp] lemma gsub_inl (I : Str L' V) (e : Con I) (p : Fin (L'.ar e.1) × Fin d) :
    gsub φ I e (Sum.inl p) = Sum.inl (e.2.1 p.1, p.2) := rfl

@[simp] lemma gsub_inr (I : Str L' V) (e : Con I) (j : Fin (φ e.1).m) :
    gsub φ I e (Sum.inr j) = Sum.inr ⟨e, j⟩ := rfl

/-- The gadget instance `I^♯`: one tuple per constraint `e` and atom `q` of `φ_R`. -/
def gadget (I : Str L' V) : Str L (GU φ I) where
  rel s := {u | ∃ e : Con I, ∃ q ∈ (φ e.1).atoms,
    (⟨q.sym, gsub φ I e ∘ q.args⟩ : Σ s : L.Sym, Fin (L.ar s) → GU φ I) = ⟨s, u⟩}

/-- `I^♯ → Γ` implies `I → Δ`. -/
lemma hom_of_gadget_hom {Γ : Str L G} {Δ : Str L' (Fin d → G)} (hΔ : IsPPPower Γ d Δ φ)
    {I : Str L' V} {h : GU φ I → G} (hh : IsHom (gadget φ I) Γ h) :
    IsHom I Δ (fun v i => h (Sum.inl (v, i))) := by
  intro R t ht
  apply (hΔ R _).2
  refine ⟨fun j => h (Sum.inr ⟨⟨R, ⟨t, ht⟩⟩, j⟩), ?_⟩
  intro q hq
  have := hh q.sym (gsub φ I ⟨R, ⟨t, ht⟩⟩ ∘ q.args) ⟨⟨R, ⟨t, ht⟩⟩, q, hq, rfl⟩
  convert this using 2
  funext l
  rcases hql : q.args l with p | j <;> simp only [Function.comp_apply, hql] <;> rfl

/-- `tupOpt o = some a` iff `o i = some (a i)` for all `i`. -/
def tupOpt {n : ℕ} {α : Type} (o : Fin n → Option α) : Option (Fin n → α) :=
  if h : ∃ a : Fin n → α, ∀ i, o i = some (a i) then some (Classical.choose h) else none

lemma tupOpt_eq_some {n : ℕ} {α : Type} {o : Fin n → Option α} {a : Fin n → α} :
    tupOpt o = some a ↔ ∀ i, o i = some (a i) := by
  unfold tupOpt
  split_ifs with h
  · constructor
    · intro e
      rw [← Option.some.inj e]
      exact Classical.choose_spec h
    · intro ha
      congr 1
      funext i
      exact Option.some.inj ((Classical.choose_spec h i).symm.trans (ha i))
  · simp only [false_iff]
    intro ha
    exact h ⟨a, ha⟩

/-- The fixed witness `W_R(ā)` for `φ_R(ā)`. -/
def wit (Γ : Str L G) (R : L'.Sym) (a : Fin (L'.ar R) → Fin d → G) :
    Option (Fin (φ R).m → G) :=
  if h : (φ R).Holds Γ (fun p => a p.1 p.2) then some (Classical.choose h) else none

/-- The values of `ι_X(f)`: `(v,i) ↦ f(v)_i` and `(e,j) ↦ W_R(f(v̄))_j`. -/
def gval (Γ : Str L G) (I : Str L' V) (f : PMap V (Fin d → G)) : GU φ I → Option G
  | Sum.inl (v, i) => (f v).map (fun a => a i)
  | Sum.inr ⟨e, j⟩ => ((tupOpt (f ∘ e.2.1)).bind (wit φ Γ e.1)).map (fun w => w j)

/-- The elements of `V` that an element of `I^♯` depends on: `{v}` for `(v,i)` and
`sc(e)` for `(e,j)`. The shadow of `X` is `σ(X) = X.biUnion (shadow1 φ I)`. -/
def shadow1 (I : Str L' V) : GU φ I → Finset V
  | Sum.inl (v, _) => {v}
  | Sum.inr ⟨e, _⟩ => univ.image e.2.1

lemma gval_congr (Γ : Str L G) (I : Str L' V) (f f' : PMap V (Fin d → G)) (x : GU φ I)
    (h : ∀ v ∈ shadow1 φ I x, f v = f' v) : gval φ Γ I f x = gval φ Γ I f' x := by
  rcases x with ⟨v, i⟩ | ⟨e, j⟩
  · simp only [gval]
    rw [h v (by simp [shadow1])]
  · simp only [gval]
    have : f ∘ e.2.1 = f' ∘ e.2.1 :=
      funext fun l => h _ (by simp only [shadow1]; exact mem_image_of_mem _ (mem_univ l))
    rw [this]

variable [Fintype V]

/-- **Lemma 3.2.** Let `Δ` be a pp-power of `Γ` with arities at most `r` (and `r ≥ 1`). If
`C_{r(k+1)}(Δ)` accepts `I`, then `C_k(Γ)` accepts `I^♯`. -/
theorem accepts_gadget [Fintype L'.Sym] {pin : Bool} {Γ : Str L G} {Δ : Str L' (Fin d → G)}
    (hΔ : IsPPPower Γ d Δ φ) {r : ℕ} (hr : 1 ≤ r) (har : ∀ R, L'.ar R ≤ r) {I : Str L' V}
    {k : ℕ} (hacc : Accepts pin (r * (k + 1)) I Δ) : Accepts pin k (gadget φ I) Γ := by
  obtain ⟨S, hS, hemp⟩ := hacc
  have hsc : ∀ e : Con I, (univ.image e.2.1).card ≤ r := fun e =>
    card_image_le.trans (by rw [card_univ, Fintype.card_fin]; exact har _)
  have hsh_card : ∀ x, (shadow1 φ I x).card ≤ r := by
    rintro (⟨v, i⟩ | ⟨e, j⟩)
    · simpa [shadow1] using hr
    · exact hsc e
  have hσcard : ∀ X : Finset (GU φ I), (X.biUnion (shadow1 φ I)).card ≤ r * X.card := by
    intro X
    calc _ ≤ ∑ x ∈ X, (shadow1 φ I x).card := card_biUnion_le
      _ ≤ X.card • r := sum_le_card_nsmul _ _ _ (fun x _ => hsh_card x)
      _ = r * X.card := by rw [smul_eq_mul, mul_comm]
  let ι : Finset (GU φ I) → PMap V (Fin d → G) → PMap (GU φ I) G :=
    fun X f x => if x ∈ X then gval φ Γ I f x else none
  refine transfer hS hemp (fun X => X.biUnion (shadow1 φ I)) ι
    (fun X Y h => biUnion_subset_biUnion_of_subset_left _ h)
    (fun X hX => (hσcard X).trans (Nat.mul_le_mul_left r (by omega))) ?_ ?_ ?_
  -- domains
  · intro X _ f hf hfd
    ext x
    rw [mem_dom]
    by_cases hx : x ∈ X
    · simp only [ι, hx, ↓reduceIte, ne_eq, iff_true]
      have hsub : shadow1 φ I x ⊆ dom f := by rw [hfd]; exact subset_biUnion_of_mem _ hx
      rcases x with ⟨v, i⟩ | ⟨e, j⟩
      · have : f v ≠ none := mem_dom.1 (hsub (by simp [shadow1]))
        simpa [gval] using this
      · obtain ⟨a, ha, hfa⟩ := (hS.phom f hf).exists_tuple e.2.2
          (fun l => hsub (by simp only [shadow1]; exact mem_image_of_mem _ (mem_univ l)))
        have h1 : tupOpt (f ∘ e.2.1) = some a := tupOpt_eq_some.2 hfa
        have hH := (hΔ e.1 a).1 ha
        have h2 : wit φ Γ e.1 a = some (Classical.choose hH) := by simp [wit, hH]
        simp [gval, h1, h2]
    · simp [ι, hx]
  -- naturality
  · intro X Y _ hYX f _ _
    funext x
    by_cases hx : x ∈ Y
    · have hxX : x ∈ X := hYX hx
      simp only [res, ι, hx, hxX, ↓reduceIte]
      apply gval_congr
      intro v hv
      have : v ∈ Y.biUnion (shadow1 φ I) := subset_biUnion_of_mem _ hx hv
      exact (res_apply_of_mem this).symm
    · simp [res, ι, hx]
  -- partial homomorphisms
  · intro X hX f hf hfd s u b hu hb
    obtain ⟨e, q, hq, heq⟩ := hu
    cases heq
    have hbX : ∀ l, gsub φ I e (q.args l) ∈ X ∧
        gval φ Γ I f (gsub φ I e (q.args l)) = some (b l) := by
      intro l
      have := hb l
      by_cases h : gsub φ I e (q.args l) ∈ X
      · simp only [Function.comp, ι, h, ↓reduceIte] at this
        exact ⟨h, this⟩
      · simp [Function.comp, ι, h] at this
    have hcardZ : (X.biUnion (shadow1 φ I) ∪ univ.image e.2.1).card ≤ r * (k + 1) := by
      have h1 := card_union_le (X.biUnion (shadow1 φ I)) (univ.image e.2.1)
      have h2 := hσcard X
      have h3 := hsc e
      have h4 : r * X.card ≤ r * k := Nat.mul_le_mul_left r hX
      rw [mul_add, mul_one]
      omega
    obtain ⟨f', hf', hf'd, hf'r⟩ := hS.forth f hf (X.biUnion (shadow1 φ I) ∪ univ.image e.2.1)
      (by rw [hfd]; exact subset_union_left) hcardZ
    obtain ⟨a, ha, hfa⟩ := (hS.phom f' hf').exists_tuple e.2.2
      (fun l => by rw [hf'd]; exact mem_union_right _ (mem_image_of_mem _ (mem_univ l)))
    have hH := (hΔ e.1 a).1 ha
    have hw : ∀ q ∈ (φ e.1).atoms,
        Sum.elim (fun p => a p.1 p.2) (Classical.choose hH) ∘ q.args ∈ Γ.rel q.sym :=
      Classical.choose_spec hH
    suffices hbv : b = Sum.elim (fun p => a p.1 p.2) (Classical.choose hH) ∘ q.args by
      rw [hbv]
      exact hw q hq
    funext l
    obtain ⟨hlX, hlv⟩ := hbX l
    have hsub : shadow1 φ I (gsub φ I e (q.args l)) ⊆ dom f := by
      rw [hfd]; exact subset_biUnion_of_mem _ hlX
    rcases hql : q.args l with p | j
    · rw [hql, gsub_inl] at hlv hsub
      simp only [gval] at hlv
      have hv : e.2.1 p.1 ∈ dom f := hsub (by simp [shadow1])
      have : f (e.2.1 p.1) = some (a p.1) := by
        rw [← apply_eq_of_res_eq hf'r hv]
        exact hfa p.1
      rw [this, Option.map_some, Option.some.injEq] at hlv
      simp only [Function.comp_apply, hql]
      exact hlv.symm
    · rw [hql, gsub_inr] at hlv hsub
      simp only [gval] at hlv
      have hfa' : ∀ l', f (e.2.1 l') = some (a l') := fun l' => by
        have hv : e.2.1 l' ∈ dom f := hsub (by simp only [shadow1]; exact mem_image_of_mem _ (mem_univ l'))
        rw [← apply_eq_of_res_eq hf'r hv]
        exact hfa l'
      have h1 : tupOpt (f ∘ e.2.1) = some a := tupOpt_eq_some.2 hfa'
      have h2 : wit φ Γ e.1 a = some (Classical.choose hH) := by simp [wit, hH]
      rw [h1, Option.bind_some, h2, Option.map_some, Option.some.injEq] at hlv
      simp only [Function.comp_apply, hql]
      exact hlv.symm

end gadget

end CohCons
