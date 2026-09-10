import DifferentialGeometry.Geometry.Boundary.ModelCollarInverse
import DifferentialGeometry.Topology.Manifold.ModelRestriction
import Mathlib.Geometry.Manifold.Instances.Real

noncomputable section
open Set Filter Topology
open scoped ContDiff Manifold

namespace Poincare.Geometry.Boundary

open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) [hI : HasSmoothBoundary E H I]

set_option backward.isDefEq.respectTransparency false in
theorem exists_modelBoundary_collar_coordinates
    {f : hI.boundaryE × ℝ → E} {V : Set hI.boundaryE} {p : hI.boundaryE} {ρ : ℝ} {v : E}
    (hV : IsOpen V) (hp : p ∈ V) (hρ : 0 < ρ)
    (hf : ContDiffOn ℝ ∞ f (V ×ˢ Icc 0 ρ))
    (hzero : ∀ x ∈ V, f (x, 0) = modelBoundaryParam I x)
    (hderiv : HasDerivWithinAt (fun t ↦ f (p, t)) v (Icc 0 ρ) 0)
    (hinward : ∃ (w : hI.boundaryE) (c : ℝ), 0 < c ∧
      v = fderiv ℝ (modelBoundaryParam I) p w + c • hI.inwardCoordE) :
    ∃ d : OpenPartialHomeomorph (hI.boundaryE × EuclideanHalfSpace 1) H,
      (p, 0) ∈ d.source ∧
      d.source ⊆ V ×ˢ {t : EuclideanHalfSpace 1 | t.1 0 < ρ} ∧
      ContMDiffOn ((𝓘(ℝ, hI.boundaryE)).prod (𝓡∂ 1)) I ∞ d d.source ∧
      ContMDiffOn I ((𝓘(ℝ, hI.boundaryE)).prod (𝓡∂ 1)) ∞ d.symm d.target ∧
      d (p, 0) = hI.inclH (hI.boundaryI.symm p) ∧
      ∀ z ∈ d.source, I (d z) = f (z.1, z.2.1 0) := by
  obtain ⟨e, hpe, heV, he, hi, heq, hrange, _, _⟩ :=
    exists_modelBoundary_inverse_of_one_sided I hV hp hρ hf hzero hderiv hinward
  let T : EuclideanSpace ℝ (Fin 1) ≃L[ℝ] ℝ := PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)
  let L : (hI.boundaryE × EuclideanSpace ℝ (Fin 1)) ≃L[ℝ] (hI.boundaryE × ℝ) :=
    (ContinuousLinearEquiv.refl ℝ hI.boundaryE).prodCongr T
  let e' := L.toHomeomorph.toOpenPartialHomeomorph.trans e
  let J := (𝓘(ℝ, hI.boundaryE)).prod (𝓡∂ 1)
  have hLval : ∀ z, L z = (z.1, z.2 0) := fun _ ↦ rfl
  have he' : ContDiffOn ℝ ∞ e' e'.source :=
    he.comp L.contDiff.contDiffOn (fun z hz ↦ hz.2)
  have hi' : ContDiffOn ℝ ∞ e'.symm e'.target :=
    L.symm.contDiff.contDiffOn.comp (hi.mono inter_subset_left) (fun _ _ ↦ mem_univ _)
  have hside : e'.IsImage (range J) (range I) := by
    intro z hz
    have hh := hrange (L z) hz.2
    change e (L z) ∈ range I ↔ z ∈ range J
    rw [hh, hLval, ModelWithCorners.range_prod, range_modelWithCornersEuclideanHalfSpace]
    simp
  obtain ⟨d, hsource, _, hd, hdi, hdeq, _⟩ :=
    Poincare.Topology.Manifold.exists_modelRestriction J I e' he' hi' hside
  have hsource' : ∀ z ∈ d.source, (z.1, z.2.1 0) ∈ e.source := by
    intro z hz
    rw [hsource] at hz
    exact hz.2
  have hpD : (p, (0 : EuclideanHalfSpace 1)) ∈ d.source := by
    rw [hsource]
    exact ⟨mem_univ _, hpe⟩
  have hformula : ∀ z ∈ d.source, I (d z) = f (z.1, z.2.1 0) := by
    intro z hz
    rw [hdeq z hz]
    exact heq (z.1, z.2.1 0) (hsource' z hz) z.2.2
  refine ⟨d, hpD, (fun z hz ↦ ⟨(heV (hsource' z hz)).1, (heV (hsource' z hz)).2.2⟩), ?_, ?_, ?_, hformula⟩
  · rw [chartedSpaceSelf_prod]
    exact hd
  · rw [chartedSpaceSelf_prod]
    exact hdi
  · apply I.injective
    rw [hformula (p, 0) hpD]
    exact hzero p hp

end Poincare.Geometry.Boundary
