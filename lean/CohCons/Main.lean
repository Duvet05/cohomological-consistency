import CohCons.PPPower

/-!
# Theorem 4.1: closure under pp-constructions

* `size B` is `‖B‖ = |B| + ∑_R ar(R) |R^B|`.
* `Solves pin Γ k`: the algorithm at level `k ‖B‖` accepts exactly the instances `B → Γ`
  (soundness is automatic, `solves_iff`). `pin = true` is cohomological `k`-consistency and
  `pin = false` is `ℤ`-affine `k`-consistency (`algAccepts_iff`, `affAlgAccepts_iff`).
* `PPConstr T T'`: `T'` is the last member of a sequence starting at `T` in which each member is a
  pp-power of the previous one (formulas over `σ ∪ {eq}`) or homomorphically equivalent to it.
* `solves_of_ppConstr` (Theorem 4.1): there are constants `a, b, c` with
  `Solves T.Γ k → Solves T'.Γ (n ↦ a k(cn) + b)` for every nondecreasing `k`;
  `solves_const_of_ppConstr` and `solves_sublinear_of_ppConstr` are the two special cases.
-/

open Finset Classical

noncomputable section

set_option linter.unusedSectionVars false

namespace CohCons

variable {L L' : Sig} {G β V : Type}

/-- `‖B‖ = |B| + ∑_R ar(R) |R^B|`. -/
def size [Fintype L.Sym] [Fintype β] (B : Str L β) : ℕ :=
  Fintype.card β + ∑ R : L.Sym, L.ar R * (univ.filter (· ∈ B.rel R)).card

/-- The algorithm solves `CSP(Γ)` at level `k`: if it accepts `B` at level `k(‖B‖)` then
`B → Γ`. The converse holds at every level (`accepts_of_hom`), see `solves_iff`. -/
def Solves [Fintype L.Sym] (pin : Bool) (Γ : Str L G) (k : ℕ → ℕ) : Prop :=
  ∀ (β : Type) [Fintype β] (B : Str L β), Accepts pin (k (size B)) B Γ → ∃ h, IsHom B Γ h

lemma solves_iff [Fintype L.Sym] (pin : Bool) (Γ : Str L G) (k : ℕ → ℕ) :
    Solves pin Γ k ↔ ∀ (β : Type) [Fintype β] (B : Str L β),
      Accepts pin (k (size B)) B Γ ↔ ∃ h, IsHom B Γ h := by
  constructor
  · intro hs β _ B
    exact ⟨hs β B, fun ⟨h, hh⟩ => accepts_of_hom hh _⟩
  · intro hs β _ B
    exact (hs β B).1

/-- `Solves true` is about the algorithm of the note, run as a removal process. -/
lemma solves_true_iff [Fintype L.Sym] [Fintype G] (Γ : Str L G) (k : ℕ → ℕ) :
    Solves true Γ k ↔ ∀ (β : Type) [Fintype β] (B : Str L β),
      AlgAccepts (k (size B)) B Γ → ∃ h, IsHom B Γ h := by
  simp only [Solves, algAccepts_iff]

/-- `Solves false` is about `ℤ`-affine `k`-consistency as defined by Dalmau–Opršal. -/
lemma solves_false_iff [Fintype L.Sym] [Fintype G] (Γ : Str L G) (k : ℕ → ℕ) :
    Solves false Γ k ↔ ∀ (β : Type) [Fintype β] (B : Str L β),
      AffAlgAccepts (k (size B)) B Γ → ∃ h, IsHom B Γ h := by
  simp only [Solves, affAlgAccepts_iff]

lemma IsHom.comp {α γ : Type} {B : Str L β} {A : Str L α} {C : Str L γ} {h : β → α}
    {g : α → γ} (hh : IsHom B A h) (hg : IsHom A C g) : IsHom B C (g ∘ h) :=
  fun R t ht => hg R (h ∘ t) (hh R t ht)

/-! ### Sizes -/

/-- `‖J/≈‖ ≤ ‖J‖`. -/
theorem size_quot_le [Fintype L.Sym] [Fintype β] (J : Str L.withEq β) :
    size (quot J) ≤ size J := by
  unfold size
  have h1 : Fintype.card (Quotient (eqSetoid J)) ≤ Fintype.card β :=
    Fintype.card_le_of_surjective _ Quotient.mk_surjective
  have h2 : ∀ R : L.Sym, (univ.filter (· ∈ (quot J).rel R)).card ≤
      (univ.filter (· ∈ J.rel (some R))).card := by
    intro R
    calc (univ.filter (· ∈ (quot J).rel R)).card
        ≤ ((univ.filter (· ∈ J.rel (some R))).image
            (fun u i => Quotient.mk (eqSetoid J) (u i))).card := by
          apply card_le_card
          intro c hc
          rw [mem_filter] at hc
          obtain ⟨u, hu, rfl⟩ := hc.2
          exact mem_image.2 ⟨u, mem_filter.2 ⟨mem_univ _, hu⟩, rfl⟩
      _ ≤ _ := card_image_le
  have h3 : ∑ R : L.Sym, L.ar R * (univ.filter (· ∈ (quot J).rel R)).card ≤
      ∑ s : L.withEq.Sym, L.withEq.ar s * (univ.filter (· ∈ J.rel s)).card := by
    calc ∑ R : L.Sym, L.ar R * (univ.filter (· ∈ (quot J).rel R)).card
        ≤ ∑ R : L.Sym, L.withEq.ar (some R) * (univ.filter (· ∈ J.rel (some R))).card :=
          sum_le_sum fun R _ => Nat.mul_le_mul_left _ (h2 R)
      _ = ∑ s ∈ (univ : Finset L.Sym).image some,
            L.withEq.ar s * (univ.filter (· ∈ J.rel s)).card := by
          rw [sum_image (fun _ _ _ _ h => Option.some_injective _ h)]
      _ ≤ ∑ s : L.withEq.Sym, L.withEq.ar s * (univ.filter (· ∈ J.rel s)).card :=
          sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => Nat.zero_le _)
  omega

/-- The constant of the gadget construction. -/
def gconst [Fintype L.Sym] [Fintype L'.Sym] {d : ℕ}
    (φ : ∀ R : L'.Sym, PPFormula L (Fin (L'.ar R) × Fin d)) : ℕ :=
  d + ∑ R, (φ R).m + (∑ s : L.Sym, L.ar s) * ∑ R, (φ R).atoms.length

/-- `‖I^♯‖ ≤ c ‖I‖` when all arities of `Δ` are positive. -/
theorem size_gadget_le [Fintype L.Sym] [Fintype L'.Sym] [Fintype V] {d : ℕ}
    (φ : ∀ R : L'.Sym, PPFormula L (Fin (L'.ar R) × Fin d)) (hpos : ∀ R, 0 < L'.ar R)
    (I : Str L' V) : size (gadget φ I) ≤ gconst φ * size I := by
  set M := ∑ R, (φ R).m
  set A := ∑ R, (φ R).atoms.length
  set Rm := ∑ s : L.Sym, L.ar s
  set C := Fintype.card (Con I)
  set n := Fintype.card V
  have hC : C ≤ ∑ R, L'.ar R * (univ.filter (· ∈ I.rel R)).card := by
    simp only [C, Fintype.card_sigma]
    apply sum_le_sum
    intro R _
    rw [Fintype.card_subtype]
    exact Nat.le_mul_of_pos_left _ (hpos R)
  have hU : Fintype.card (GU φ I) ≤ d * n + M * C := by
    have hm : ∑ e : Con I, (φ e.1).m ≤ C * M := by
      calc ∑ e : Con I, (φ e.1).m ≤ ∑ _e : Con I, M :=
            sum_le_sum fun e _ =>
              single_le_sum (f := fun R => (φ R).m) (fun _ _ => Nat.zero_le _) (mem_univ e.1)
        _ = C * M := by simp [C]
    simp only [GU, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_sigma]
    nlinarith [hm]
  -- the tuples of `I^♯`
  let T : Finset (Σ s : L.Sym, Fin (L.ar s) → GU φ I) :=
    univ.sigma (fun s => univ.filter (· ∈ (gadget φ I).rel s))
  let F : (Σ e : Con I, Fin (φ e.1).atoms.length) → (Σ s : L.Sym, Fin (L.ar s) → GU φ I) :=
    fun x => ⟨((φ x.1.1).atoms.get x.2).sym, gsub φ I x.1 ∘ ((φ x.1.1).atoms.get x.2).args⟩
  have hT : T ⊆ univ.image F := by
    rintro ⟨s, u⟩ hx
    simp only [T, mem_sigma, mem_filter, mem_univ, true_and] at hx
    obtain ⟨e, q, hq, heq⟩ := hx
    obtain ⟨idx, rfl⟩ := List.mem_iff_get.1 hq
    exact mem_image.2 ⟨⟨e, idx⟩, mem_univ _, heq⟩
  have hTcard : T.card ≤ C * A := by
    calc T.card ≤ (univ.image F).card := card_le_card hT
      _ ≤ (univ : Finset (Σ e : Con I, Fin (φ e.1).atoms.length)).card := card_image_le
      _ = ∑ e : Con I, (φ e.1).atoms.length := by
          rw [card_univ, Fintype.card_sigma]; simp
      _ ≤ ∑ _e : Con I, A :=
          sum_le_sum fun e _ => single_le_sum (f := fun R => (φ R).atoms.length)
            (fun _ _ => Nat.zero_le _) (mem_univ e.1)
      _ = C * A := by simp [C]
  have hrel : ∑ s, L.ar s * (univ.filter (· ∈ (gadget φ I).rel s)).card ≤ Rm * T.card := by
    rw [card_sigma, mul_sum]
    apply sum_le_sum
    intro s _
    exact Nat.mul_le_mul_right _
      (single_le_sum (f := L.ar) (fun _ _ => Nat.zero_le _) (mem_univ s))
  have hsI : n + C ≤ size I := by unfold size; omega
  have hRT : Rm * T.card ≤ Rm * (C * A) := Nat.mul_le_mul_left _ hTcard
  calc size (gadget φ I)
      ≤ (d * n + M * C) + Rm * (C * A) := by unfold size; omega
    _ ≤ gconst φ * (n + C) := by
        have hg : gconst φ = d + M + Rm * A := rfl
        rw [hg]
        nlinarith [Nat.zero_le (d * C), Nat.zero_le (M * n), Nat.zero_le (Rm * A * n)]
    _ ≤ gconst φ * size I := Nat.mul_le_mul_left _ hsI

/-! ### pp-constructions -/

/-- A template: a finite signature and a structure over it. -/
structure Template where
  L : Sig
  [inst : Fintype L.Sym]
  G : Type
  Γ : Str L G

attribute [instance] Template.inst

/-- `PPConstr T T'`: `T'` is pp-constructible from `T`. Each step is homomorphic equivalence or
a pp-power whose formulas use the symbols of `Γ` and equality (`Γ.withEq`). As in the note, all
arities of the new signature are positive. -/
inductive PPConstr (T : Template) : Template → Prop
  | refl : PPConstr T T
  | homEquiv {L : Sig} [Fintype L.Sym] {G₁ G₂ : Type} {Γ₁ : Str L G₁} {Γ₂ : Str L G₂} :
      PPConstr T ⟨L, G₁, Γ₁⟩ → (∃ h, IsHom Γ₁ Γ₂ h) → (∃ h, IsHom Γ₂ Γ₁ h) →
      PPConstr T ⟨L, G₂, Γ₂⟩
  | power {L L' : Sig} [Fintype L.Sym] [Fintype L'.Sym] {G : Type} {Γ : Str L G} {d : ℕ}
      {Δ : Str L' (Fin d → G)} (φ : ∀ R : L'.Sym, PPFormula L.withEq (Fin (L'.ar R) × Fin d)) :
      PPConstr T ⟨L, G, Γ⟩ → IsPPPower Γ.withEq d Δ φ → (∀ R, 0 < L'.ar R) →
      PPConstr T ⟨L', Fin d → G, Δ⟩

/-- **Theorem 4.1.** If `T'` is pp-constructible from `T`, there are constants `a, b` and
`c ≥ 1` such that, for every nondecreasing `k`, if the algorithm solves `CSP(T)` at level `k`
then it solves `CSP(T')` at level `n ↦ a k(cn) + b`. -/
theorem solves_of_ppConstr {T T' : Template} (h : PPConstr T T') :
    ∃ a b c : ℕ, 1 ≤ c ∧ ∀ (pin : Bool) (k : ℕ → ℕ), Monotone k → Solves pin T.Γ k →
      Solves pin T'.Γ (fun n => a * k (c * n) + b) := by
  induction h with
  | refl =>
    refine ⟨1, 0, 1, le_rfl, fun pin k _ hk => ?_⟩
    have : (fun n => 1 * k (1 * n) + 0) = k := by funext n; simp
    rw [this]
    exact hk
  | @homEquiv L _ G₁ G₂ Γ₁ Γ₂ _ h12 h21 ih =>
    obtain ⟨a, b, c, hc, ih⟩ := ih
    refine ⟨a, b, c, hc, fun pin k hk hs β _ B hB => ?_⟩
    obtain ⟨g21, hg21⟩ := h21
    obtain ⟨g12, hg12⟩ := h12
    obtain ⟨g, hg⟩ := ih pin k hk hs β B (accepts_of_template_hom hg21 hB)
    exact ⟨g12 ∘ g, hg.comp hg12⟩
  | @power L L' _ _ G Γ d Δ φ _ hΔ hpos ih =>
    obtain ⟨a, b, c, hc, ih⟩ := ih
    set r := 1 + ∑ R : L'.Sym, L'.ar R with hr_def
    set ρ := ∑ R : L.Sym, L.ar R with hρ_def
    have hr : 1 ≤ r := by omega
    have har : ∀ R, L'.ar R ≤ r := fun R => by
      have := single_le_sum (f := L'.ar) (fun _ _ => Nat.zero_le _) (mem_univ R)
      omega
    have hρ : ∀ R, L.ar R ≤ ρ := fun R =>
      single_le_sum (f := L.ar) (fun _ _ => Nat.zero_le _) (mem_univ R)
    refine ⟨r * a, r * (b + ρ + 2), c * (gconst φ + 1), Nat.mul_pos (by omega) (Nat.succ_pos _),
      fun pin k hk hs V _ I hI => ?_⟩
    -- the level of the previous member of the sequence
    let k' : ℕ → ℕ := fun n => a * k (c * n) + b
    have hk' : Monotone k' := fun m n hmn =>
      Nat.add_le_add_right (Nat.mul_le_mul_left _ (hk (Nat.mul_le_mul_left _ hmn))) _
    have hs' : Solves pin Γ k' := ih pin k hk hs
    set n := size I
    set K := k' ((gconst φ + 1) * n)
    have hlevel : r * a * k (c * (gconst φ + 1) * n) + r * (b + ρ + 2) = r * (K + ρ + 1 + 1) := by
      simp only [K, k', mul_assoc]
      ring
    have hI' : Accepts pin (r * (K + ρ + 1 + 1)) I Δ := by
      rw [← hlevel]
      exact hI
    have h1 : Accepts pin (K + ρ + 1) (gadget φ I) Γ.withEq := accepts_gadget φ hΔ hr har hI'
    have h2 : Accepts pin K (quot (gadget φ I)) Γ := accepts_quot hρ h1
    have hsize : size (quot (gadget φ I)) ≤ (gconst φ + 1) * n :=
      (size_quot_le _).trans ((size_gadget_le φ hpos I).trans
        (Nat.mul_le_mul_right _ (Nat.le_succ _)))
    have h3 : Accepts pin (k' (size (quot (gadget φ I)))) (quot (gadget φ I)) Γ :=
      accepts_mono (hk' hsize) h2
    obtain ⟨g, hg⟩ := hs' _ _ h3
    exact ⟨_, hom_of_gadget_hom φ hΔ (hom_of_quot_hom hg)⟩

/-- Constant levels go to constant levels. -/
theorem solves_const_of_ppConstr {T T' : Template} (h : PPConstr T T') {pin : Bool} {k₀ : ℕ}
    (hs : Solves pin T.Γ (fun _ => k₀)) : ∃ k₁ : ℕ, Solves pin T'.Γ (fun _ => k₁) := by
  obtain ⟨a, b, c, -, hT⟩ := solves_of_ppConstr h
  exact ⟨a * k₀ + b, hT pin (fun _ => k₀) (fun _ _ _ => le_rfl) hs⟩

/-- `k ∈ o(n)`. -/
def Sublinear (k : ℕ → ℕ) : Prop :=
  Filter.Tendsto (fun n => (k n : ℝ) / n) Filter.atTop (nhds 0)

lemma sublinear_comp {k : ℕ → ℕ} (hk : Sublinear k) (a b c : ℕ) (hc : 1 ≤ c) :
    Sublinear (fun n => a * k (c * n) + b) := by
  unfold Sublinear at hk ⊢
  have hcn : Filter.Tendsto (fun n : ℕ => c * n) Filter.atTop Filter.atTop :=
    Filter.tendsto_id.const_mul_atTop' (by omega)
  have h1 : Filter.Tendsto (fun n : ℕ => (k (c * n) : ℝ) / ((c * n : ℕ) : ℝ))
      Filter.atTop (nhds 0) := hk.comp hcn
  have h2 : Filter.Tendsto (fun n : ℕ => (b : ℝ) / n) Filter.atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (b : ℝ)
  have h3 := (h1.const_mul ((a : ℝ) * c)).add h2
  rw [mul_zero, zero_add] at h3
  refine h3.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with n hn
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast (show c ≠ 0 by omega)
  push_cast
  field_simp

/-- Sublinear levels go to sublinear levels. -/
theorem solves_sublinear_of_ppConstr {T T' : Template} (h : PPConstr T T') {pin : Bool}
    {k : ℕ → ℕ} (hmono : Monotone k) (hsub : Sublinear k) (hs : Solves pin T.Γ k) :
    ∃ k' : ℕ → ℕ, Monotone k' ∧ Sublinear k' ∧ Solves pin T'.Γ k' := by
  obtain ⟨a, b, c, hc, hT⟩ := solves_of_ppConstr h
  refine ⟨fun n => a * k (c * n) + b, ?_, sublinear_comp hsub a b c hc, hT pin k hmono hs⟩
  exact fun m n hmn =>
    Nat.add_le_add_right (Nat.mul_le_mul_left _ (hmono (Nat.mul_le_mul_left _ hmn))) _

end CohCons
