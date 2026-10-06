import Mathlib.Topology.Constructions
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# The labels of the circle-base corner record at a point of the base curve (lane S-BCF03b; BCF03 G7)

Set-level kernel (no manifolds): `f : M → H` is the circle map with source `X` and base `B₀`,
`Rc ⊆ M₂` the circle remainder, `Bd ⊇ F ℓ ∩ M₂` the frontier of `M₂` containing the horizontal faces
`F ℓ` inside `M₂`, `V` the vertical face, and `Γ = f '' (Bd ∩ Rc)` the base curve. At a point `y` of
`Γ` carrying a corner record `(O, L, ψ)` (labels `Λ ⊕ Unit`, `inl ℓ` horizontal, `inr ()` vertical;
zero sets of `ψ s` in `C₁ = f '' Rc` = base points whose WHOLE circle fibre lies in the face of `s`;
all labels whose face contains the fibre over `y` belong to `L`), this file proves:

* `circleBase_labels_BCF`: `L` contains exactly ONE horizontal label `ℓ₀` and possibly the vertical
  one; there is an open `O' ⊆ O` around `y` on which `Γ = {ψ (inl ℓ₀) = 0} ∩ C₁`; and the vertical
  label belongs to `L` iff `y` is a rim base point `Rb y`.
-/

set_option autoImplicit false

open Set Function Topology

namespace DifferentialGeometry.Topology

variable {M H Λ : Type*} [TopologicalSpace H] [Finite Λ]

/-- **Labels of the corner record at a point of the base curve.** -/
theorem circleBase_labels_BCF {f : M → H} {X Rc Bd M₂ : Set M} {B₀ : Set H} {F : Λ → Set M}
    {V : Set M} (hRcM : Rc ⊆ M₂) (hRsat : ∀ q ∈ X, f q ∈ f '' Rc → q ∈ Rc)
    (hRcX : Rc ⊆ X) (hB : ∀ q ∈ X, f q ∈ B₀)
    (hdisj : ∀ ℓ ℓ', ℓ ≠ ℓ' → Disjoint (F ℓ ∩ M₂) (F ℓ' ∩ M₂)) (hFBd : ∀ ℓ, F ℓ ∩ M₂ ⊆ Bd)
    (hKcl : ∀ ℓ, ∃ G : Set H, IsClosed G ∧ ∀ y ∈ B₀, (X ∩ f ⁻¹' {y} ⊆ F ℓ ↔ y ∈ G))
    (hsat1 : ∀ p ∈ Bd ∩ Rc, ∃ ℓ, X ∩ f ⁻¹' {f p} ⊆ F ℓ) {Rb : H → Prop}
    (hRb1 : ∀ y ∈ f '' (Bd ∩ Rc), Rb y → X ∩ f ⁻¹' {y} ⊆ V)
    (hRb2 : ∀ y ∈ f '' (Bd ∩ Rc), X ∩ f ⁻¹' {y} ⊆ V → Rb y) {y : H}
    (hyΓ : y ∈ f '' (Bd ∩ Rc)) {O : Set H} (hO : IsOpen O) (hyO : y ∈ O)
    (L : Finset (Λ ⊕ Unit)) (ψ : Λ ⊕ Unit → H → ℝ)
    (hψ : ∀ s ∈ L, ψ s y = 0 ∧ {y' | y' ∈ O ∧ y' ∈ f '' Rc ∧ ψ s y' = 0} =
      {y' | y' ∈ O ∧ y' ∈ f '' Rc ∧ X ∩ f ⁻¹' {y'} ⊆ Sum.elim F (fun _ => V) s})
    (hcl : ∀ s, X ∩ f ⁻¹' {y} ⊆ Sum.elim F (fun _ => V) s → s ∈ L) :
    ∃ (ℓ₀ : Λ) (O' : Set H), IsOpen O' ∧ y ∈ O' ∧ O' ⊆ O ∧ Sum.inl ℓ₀ ∈ L ∧
      (∀ s ∈ L, s = Sum.inl ℓ₀ ∨ s = Sum.inr ()) ∧
      (∀ y' ∈ O' ∩ B₀, y' ∈ f '' (Bd ∩ Rc) ↔ (y' ∈ f '' Rc ∧ ψ (Sum.inl ℓ₀) y' = 0)) ∧
      (Sum.inr () ∈ L ↔ Rb y) := by
  classical
  obtain ⟨p₀, hp₀, rfl⟩ := hyΓ
  have hyC : f p₀ ∈ f '' Rc := ⟨p₀, hp₀.2, rfl⟩
  have hp₀X : p₀ ∈ X := hRcX hp₀.2
  have hp₀F : p₀ ∈ X ∩ f ⁻¹' {f p₀} := ⟨hp₀X, rfl⟩
  -- the horizontal label of the fibre over `f p₀`
  obtain ⟨ℓ₀, hℓ₀⟩ := hsat1 p₀ hp₀
  have hℓ₀L : Sum.inl ℓ₀ ∈ L := hcl _ hℓ₀
  -- every label of `L` has its face containing the fibre
  have hLfib : ∀ s ∈ L, X ∩ f ⁻¹' {f p₀} ⊆ Sum.elim F (fun _ => V) s := by
    intro s hs
    have hmem : f p₀ ∈ {y' | y' ∈ O ∧ y' ∈ f '' Rc ∧ ψ s y' = 0} := ⟨hyO, hyC, (hψ s hs).1⟩
    rw [(hψ s hs).2] at hmem
    exact hmem.2.2
  -- the fibre lies in `Rc ⊆ M₂`
  have hfibR : ∀ q ∈ X ∩ f ⁻¹' {f p₀}, q ∈ Rc := fun q hq =>
    hRsat q hq.1 (by
      have h : f q = f p₀ := hq.2
      rw [h]
      exact hyC)
  -- the horizontal faces meeting the fibre are `F ℓ₀` only
  have hone : ∀ ℓ, X ∩ f ⁻¹' {f p₀} ⊆ F ℓ → ℓ = ℓ₀ := by
    intro ℓ hℓ
    by_contra hne
    exact Set.disjoint_left.mp (hdisj ℓ ℓ₀ hne) ⟨hℓ hp₀F, hRcM (hfibR p₀ hp₀F)⟩
      ⟨hℓ₀ hp₀F, hRcM (hfibR p₀ hp₀F)⟩
  have hLh : ∀ s ∈ L, s = Sum.inl ℓ₀ ∨ s = Sum.inr () := by
    intro s hs
    rcases s with ℓ | u
    · exact Or.inl (congrArg Sum.inl (hone ℓ (hLfib _ hs)))
    · exact Or.inr (by rw [Subsingleton.elim u ()])
  -- the shrunk neighbourhood
  choose G hGc hGiff using hKcl
  let O' : Set H := O ∩ ⋂ ℓ : {ℓ // ℓ ≠ ℓ₀}, (G ℓ.1)ᶜ
  have hO'o : IsOpen O' := hO.inter (isOpen_iInter_of_finite fun ℓ => (hGc ℓ.1).isOpen_compl)
  have hyO' : f p₀ ∈ O' := by
    refine ⟨hyO, mem_iInter.mpr fun ℓ hℓ => ?_⟩
    exact (hGiff ℓ.1 _ (hB p₀ hp₀X)).not.mp (fun h => ℓ.2 (hone ℓ.1 h)) hℓ
  refine ⟨ℓ₀, O', hO'o, hyO', inter_subset_left, hℓ₀L, hLh, ?_, ?_⟩
  · intro y' hy'
    obtain ⟨hy'O', hy'B⟩ := hy'
    constructor
    · rintro ⟨q, hq, rfl⟩
      refine ⟨⟨q, hq.2, rfl⟩, ?_⟩
      obtain ⟨ℓ'', hℓ''⟩ := hsat1 q hq
      have hℓ''eq : ℓ'' = ℓ₀ := by
        by_contra hne
        exact (mem_iInter.mp hy'O'.2 ⟨ℓ'', hne⟩) ((hGiff ℓ'' _ hy'B).mp hℓ'')
      rw [hℓ''eq] at hℓ''
      have hmem : f q ∈ {y' | y' ∈ O ∧ y' ∈ f '' Rc ∧
          X ∩ f ⁻¹' {y'} ⊆ Sum.elim F (fun _ => V) (Sum.inl ℓ₀ : Λ ⊕ Unit)} :=
        ⟨hy'O'.1, mem_image_of_mem f hq.2, hℓ''⟩
      rw [← (hψ _ hℓ₀L).2] at hmem
      exact hmem.2.2
    · rintro ⟨⟨q, hqR, rfl⟩, hψ0⟩
      have hmem : f q ∈ {y' | y' ∈ O ∧ y' ∈ f '' Rc ∧ ψ (Sum.inl ℓ₀) y' = 0} :=
        ⟨hy'O'.1, mem_image_of_mem f hqR, hψ0⟩
      rw [(hψ _ hℓ₀L).2] at hmem
      have hqF : q ∈ F ℓ₀ := hmem.2.2 ⟨hRcX hqR, rfl⟩
      exact ⟨q, ⟨hFBd ℓ₀ ⟨hqF, hRcM hqR⟩, hqR⟩, rfl⟩
  · constructor
    · intro hv
      exact hRb2 _ ⟨p₀, hp₀, rfl⟩ (hLfib _ hv)
    · intro hR
      exact hcl _ (hRb1 _ ⟨p₀, hp₀, rfl⟩ hR)

end DifferentialGeometry.Topology
