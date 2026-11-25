import CohCons.Basic

/-!
# Transferring stable families

The proofs of Lemmas 2.3(ii), 3.1, 3.2 and 3.3 all push a stable family `S` for `(B, A)` forward
to a family `S'` for `(B', A')`. A set `X'` of the new instance is sent to a set `σ X'` of the old
one, and a partial map `f` with domain `σ X'` to a partial map `ι X' f` with domain `X'`,
naturally with respect to restriction. The new family is
`S' = {ι X' f | |X'| ≤ k', f ∈ S, dom f = σ X'}`, and pinned solutions are pushed forward by
summing over fibres:
`z' g = ∑ {z f | f ∈ S, dom f = σ (dom g), ι (dom g) f = g}`.

`transfer` proves that `S'` is stable once its members are partial homomorphisms; the latter is
the only part that differs between the lemmas. It holds for both solvability conditions
(`pin = true`: cohomological; `pin = false`: `ℤ`-affine `k`-consistency), since unpinned
solutions are pushed forward by the same formula.
-/

open Finset Classical

noncomputable section

set_option linter.unusedSectionVars false

namespace CohCons

variable {L L' : Sig} {α β α' β' : Type} [Fintype β] [Fintype β']

theorem transfer {pin : Bool} {B : Str L β} {A : Str L α} {B' : Str L' β'} {A' : Str L' α'}
    {k k' : ℕ} {S : Finset (PMap β α)} (hS : Stable pin B A k S) (hemp : emp ∈ S)
    (σ : Finset β' → Finset β) (ι : Finset β' → PMap β α → PMap β' α')
    (hmono : ∀ X Y : Finset β', Y ⊆ X → σ Y ⊆ σ X)
    (hcard : ∀ X : Finset β', X.card ≤ k' → (σ X).card ≤ k)
    (hdom : ∀ X : Finset β', X.card ≤ k' → ∀ f ∈ S, dom f = σ X → dom (ι X f) = X)
    (hnat : ∀ X Y : Finset β', X.card ≤ k' → Y ⊆ X → ∀ f ∈ S, dom f = σ X →
      res (ι X f) Y = ι Y (res f (σ Y)))
    (hphom : ∀ X : Finset β', X.card ≤ k' → ∀ f ∈ S, dom f = σ X → IsPHom B' A' (ι X f)) :
    Accepts pin k' B' A' := by
  let S' : Finset (PMap β' α') :=
    ((univ : Finset (Finset β')).filter (fun X => X.card ≤ k')).biUnion
      (fun X => (S.filter (fun f => dom f = σ X)).image (ι X))
  have hmem : ∀ g, g ∈ S' ↔ ∃ X : Finset β', X.card ≤ k' ∧ ∃ f ∈ S, dom f = σ X ∧ ι X f = g := by
    intro g
    simp only [S', mem_biUnion, mem_filter, mem_univ, true_and, mem_image]
    constructor
    · rintro ⟨X, hX, f, ⟨hf, hfd⟩, rfl⟩; exact ⟨X, hX, f, hf, hfd, rfl⟩
    · rintro ⟨X, hX, f, hf, hfd, rfl⟩; exact ⟨X, hX, f, ⟨hf, hfd⟩, rfl⟩
  have hsub : ∀ {X Y : Finset β'} {f : PMap β α}, Y ⊆ X → dom f = σ X → σ Y ⊆ dom f :=
    fun hYX hfd => by rw [hfd]; exact hmono _ _ hYX
  refine ⟨S', ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  -- partial homomorphisms
  · rintro g hg
    obtain ⟨X, hX, f, hf, hfd, rfl⟩ := (hmem g).1 hg
    exact hphom X hX f hf hfd
  -- sizes
  · rintro g hg
    obtain ⟨X, hX, f, hf, hfd, rfl⟩ := (hmem g).1 hg
    rw [hdom X hX f hf hfd]
    exact hX
  -- (S1)
  · rintro g hg Y hY
    obtain ⟨X, hX, f, hf, hfd, rfl⟩ := (hmem g).1 hg
    rw [hdom X hX f hf hfd] at hY
    rw [hnat X Y hX hY f hf hfd, hmem]
    exact ⟨Y, (card_le_card hY).trans hX, res f (σ Y), hS.down f hf _ (hsub hY hfd),
      dom_res_of_subset (hsub hY hfd), rfl⟩
  -- (S2)
  · rintro g hg X hX hXk
    obtain ⟨Y, hY, f, hf, hfd, rfl⟩ := (hmem g).1 hg
    rw [hdom Y hY f hf hfd] at hX ⊢
    obtain ⟨f', hf', hf'd, hf'r⟩ :=
      hS.forth f hf (σ X) (by rw [hfd]; exact hmono X Y hX) (hcard X hXk)
    refine ⟨ι X f', (hmem _).2 ⟨X, hXk, f', hf', hf'd, rfl⟩, hdom X hXk f' hf' hf'd, ?_⟩
    rw [hnat X Y hXk hX f' hf' hf'd, ← hfd, hf'r]
  -- (S3), or the single solution for `pin = false`: solutions are pushed forward fibrewise
  · have push : ∀ z : PMap β α → ℤ, Sys k S z →
        Sys k' S' (fun g => ∑ f ∈ S with dom f = σ (dom g) ∧ ι (dom g) f = g, z f) := by
      rintro z ⟨hN, hC⟩
      let z' : PMap β' α' → ℤ := fun g =>
        ∑ f ∈ S with dom f = σ (dom g) ∧ ι (dom g) f = g, z f
      refine ⟨?_, ?_⟩
      -- (N)
      · intro X hX
        calc ∑ g ∈ S' with dom g = X, z' g
            = ∑ g ∈ S' with dom g = X, ∑ f ∈ S with dom f = σ X ∧ ι X f = g, z f := by
              apply sum_congr rfl
              intro g hg
              rw [mem_filter] at hg
              simp only [z', hg.2]
          _ = ∑ f ∈ S with dom f = σ X, z f := by
              rw [← sum_fiberwise_of_maps_to (s := S.filter (fun f => dom f = σ X))
                (t := S'.filter (fun g => dom g = X)) (g := ι X)]
              · simp only [filter_filter]
              · intro f hf
                rw [mem_filter] at hf ⊢
                exact ⟨(hmem _).2 ⟨X, hX, f, hf.1, hf.2, rfl⟩, hdom X hX f hf.1 hf.2⟩
          _ = 1 := hN (σ X) (hcard X hX)
      -- (C)
      · intro X Y hX hYX g'' hg'' hg''d
        have hσ : σ Y ⊆ σ X := hmono X Y hYX
        calc ∑ g ∈ S' with dom g = X ∧ res g Y = g'', z' g
            = ∑ g ∈ S' with dom g = X ∧ res g Y = g'',
                ∑ f ∈ S with dom f = σ X ∧ ι X f = g, z f := by
              apply sum_congr rfl
              intro g hg
              rw [mem_filter] at hg
              simp only [z', hg.2.1]
          _ = ∑ f ∈ S with dom f = σ X ∧ res (ι X f) Y = g'', z f := by
              rw [← sum_fiberwise_of_maps_to
                (s := S.filter (fun f => dom f = σ X ∧ res (ι X f) Y = g''))
                (t := S'.filter (fun g => dom g = X ∧ res g Y = g'')) (g := ι X)]
              · apply sum_congr rfl
                intro g hg
                rw [mem_filter] at hg
                rw [filter_filter]
                apply sum_congr _ (fun _ _ => rfl)
                apply filter_congr
                intro f _
                constructor
                · rintro ⟨hfd, rfl⟩; exact ⟨⟨hfd, hg.2.2⟩, rfl⟩
                · rintro ⟨⟨hfd, -⟩, rfl⟩; exact ⟨hfd, rfl⟩
              · intro f hf
                rw [mem_filter] at hf ⊢
                exact ⟨(hmem _).2 ⟨X, hX, f, hf.1, hf.2.1, rfl⟩, hdom X hX f hf.1 hf.2.1, hf.2.2⟩
          _ = ∑ f ∈ S with dom f = σ X ∧ ι Y (res f (σ Y)) = g'', z f := by
              apply sum_congr _ (fun _ _ => rfl)
              apply filter_congr
              intro f hf
              constructor
              · rintro ⟨hfd, h⟩
                exact ⟨hfd, by rw [← hnat X Y hX hYX f hf hfd]; exact h⟩
              · rintro ⟨hfd, h⟩
                exact ⟨hfd, by rw [hnat X Y hX hYX f hf hfd]; exact h⟩
          _ = ∑ f'' ∈ S with dom f'' = σ Y ∧ ι Y f'' = g'',
                ∑ f ∈ S with dom f = σ X ∧ res f (σ Y) = f'', z f := by
              rw [← sum_fiberwise_of_maps_to
                (s := S.filter (fun f => dom f = σ X ∧ ι Y (res f (σ Y)) = g''))
                (t := S.filter (fun f'' => dom f'' = σ Y ∧ ι Y f'' = g''))
                (g := fun f => res f (σ Y))]
              · apply sum_congr rfl
                intro f'' hf''
                rw [mem_filter] at hf''
                rw [filter_filter]
                apply sum_congr _ (fun _ _ => rfl)
                apply filter_congr
                intro f _
                constructor
                · rintro ⟨⟨hfd, -⟩, h⟩; exact ⟨hfd, h⟩
                · rintro ⟨hfd, h⟩; exact ⟨⟨hfd, by rw [h]; exact hf''.2.2⟩, h⟩
              · intro f hf
                rw [mem_filter] at hf ⊢
                exact ⟨hS.down f hf.1 _ (by rw [hf.2.1]; exact hσ),
                  dom_res_of_subset (by rw [hf.2.1]; exact hσ), hf.2.2⟩
          _ = ∑ f'' ∈ S with dom f'' = σ Y ∧ ι Y f'' = g'', z f'' := by
              apply sum_congr rfl
              intro f'' hf''
              rw [mem_filter] at hf''
              exact hC (σ X) (σ Y) (hcard X hX) hσ f'' hf''.1 hf''.2.1
          _ = z' g'' := by simp only [z', hg''d]
    cases pin with
    | false =>
      obtain ⟨z, hz⟩ := hS.solv
      exact ⟨_, push z hz⟩
    | true =>
      rintro g₀ hg₀
      obtain ⟨X₀, hX₀, f₀, hf₀, hf₀d, rfl⟩ := (hmem g₀).1 hg₀
      obtain ⟨z, hz, hP⟩ := hS.pinned f₀ hf₀
      refine ⟨_, push z hz, ?_⟩
      intro g _ hgd
      rw [hdom X₀ hX₀ f₀ hf₀ hf₀d] at hgd
      simp only [hgd]
      rw [sum_congr rfl (g := fun f => if f = f₀ then (1 : ℤ) else 0)]
      · rw [sum_ite_eq']
        simp only [mem_filter, hf₀, hf₀d, true_and]
        by_cases h : g = ι X₀ f₀
        · simp [h]
        · simp [h, Ne.symm h]
      · intro f hf
        rw [mem_filter] at hf
        exact hP f hf.1 (by rw [hf.2.1, hf₀d])
  -- nonempty
  · obtain ⟨f, hf, hfd, -⟩ :=
      hS.forth emp hemp (σ ∅) (by rw [dom_emp]; exact empty_subset _) (hcard ∅ (by simp))
    have h1 : ι ∅ f = emp := (dom_eq_empty_iff _).1 (hdom ∅ (by simp) f hf hfd)
    rw [← h1, hmem]
    exact ⟨∅, by simp, f, hf, hfd, rfl⟩

/-- **Lemma 2.3(ii).** Acceptance is monotone in the level. -/
theorem accepts_mono {pin : Bool} {B : Str L β} {A : Str L α} {k k' : ℕ} (hk : k' ≤ k)
    (hacc : Accepts pin k B A) : Accepts pin k' B A := by
  obtain ⟨S, hS, hemp⟩ := hacc
  exact transfer hS hemp id (fun _ f => f) (fun _ _ h => h) (fun _ h => h.trans hk)
    (fun _ _ _ _ hfd => hfd) (fun _ _ _ _ _ _ _ => rfl) (fun _ _ f hf _ => hS.phom f hf)

/-- Composing a partial map with a map of templates. -/
def pcomp (h : α → α') (f : PMap β α) : PMap β α' := fun b => (f b).map h

/-- **Lemma 3.1.** A homomorphism of templates `A → A'` preserves acceptance at the same
level. -/
theorem accepts_of_template_hom {pin : Bool} {B : Str L β} {A : Str L α} {A' : Str L α'}
    {h : α → α'} (hh : IsHom A A' h) {k : ℕ} (hacc : Accepts pin k B A) : Accepts pin k B A' := by
  obtain ⟨S, hS, hemp⟩ := hacc
  refine transfer hS hemp id (fun _ f => pcomp h f) (fun _ _ h => h) (fun _ h => h) ?_ ?_ ?_
  · intro X _ f _ hfd
    change dom f = X at hfd
    rw [← hfd]
    ext b
    simp [pcomp]
  · intro X Y _ _ f _ _
    funext b
    by_cases hb : b ∈ Y <;> simp [pcomp, res, hb]
  · intro X _ f hf _ R t a ht hta
    have : ∀ i, ∃ x, f (t i) = some x ∧ h x = a i := fun i => by
      have := hta i
      simp only [pcomp, Option.map_eq_some_iff] at this
      exact this
    choose a₀ ha₀ using this
    have hA := hh R a₀ (hS.phom f hf R t a₀ ht (fun i => (ha₀ i).1))
    convert hA using 1
    funext i
    exact (ha₀ i).2.symm

end CohCons
