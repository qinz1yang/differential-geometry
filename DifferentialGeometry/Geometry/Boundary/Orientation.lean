import DifferentialGeometry.Geometry.Boundary.OutwardNormal
import Mathlib.Topology.VectorBundle.Riemannian


noncomputable section

open Set Function Topology Bundle Manifold MeasureTheory
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry
namespace Integral
namespace DivergenceTheorem
namespace WithBoundary

class HasOrientableBoundary
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [hI : HasSmoothBoundary E H I]
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] : Prop
where
  inwardCoord_chart_consistent :
    ∀ (α₀ α₁ : BoundaryManifold I M) (y : BoundaryManifold I M),
      (y : M) ∈ (chartAt H (α₀ : M)).source →
      (y : M) ∈ (chartAt H (α₁ : M)).source →
      ∃ c : ℝ, 0 < c ∧
        inwardCoordAt (M := M) α₀ y - c • inwardCoordAt (M := M) α₁ y ∈
          Set.range (boundaryInclusionMfderiv (M := M) y).toLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [hI : HasSmoothBoundary E H I] [IsManifold I ∞ M]

theorem inwardCoord_chart_consistent
    [HasOrientableBoundary (E := E) (H := H) (I := I) M]
    (α₀ α₁ : BoundaryManifold I M) (y : BoundaryManifold I M)
    (hα₀ : (y : M) ∈ (chartAt H (α₀ : M)).source)
    (hα₁ : (y : M) ∈ (chartAt H (α₁ : M)).source) :
    ∃ c : ℝ, 0 < c ∧
      inwardCoordAt (M := M) α₀ y - c • inwardCoordAt (M := M) α₁ y ∈
        Set.range (boundaryInclusionMfderiv (M := M) y).toLinearMap :=
  HasOrientableBoundary.inwardCoord_chart_consistent α₀ α₁ y hα₀ hα₁

omit [FiniteDimensional ℝ E] in
theorem inwardCoord_chart_consistent_self (α : BoundaryManifold I M)
    (y : BoundaryManifold I M) :
    ∃ c : ℝ, 0 < c ∧
      inwardCoordAt (M := M) α y - c • inwardCoordAt (M := M) α y ∈
        Set.range (boundaryInclusionMfderiv (M := M) y).toLinearMap := by
  refine ⟨1, by norm_num, ?_⟩
  simp only [one_smul, sub_self]
  exact ⟨0, map_zero _⟩

theorem outwardNormalAt_chart_invariance
    [HasOrientableBoundary (E := E) (H := H) (I := I) M]
    (g : SmoothRiemannianMetric I M) (α₀ α₁ : BoundaryManifold I M)
    {y : BoundaryManifold I M}
    (hy_α₀ : (y : M) ∈ (chartAt H (α₀ : M)).source)
    (hy_α₁ : (y : M) ∈ (chartAt H (α₁ : M)).source) :
    outwardNormalAt (M := M) g α₀ y = outwardNormalAt (M := M) g α₁ y := by
  obtain ⟨c, hc, h_w⟩ := inwardCoord_chart_consistent (M := M) α₀ α₁ y hy_α₀ hy_α₁
  exact outwardNormalAt_chart_invariance_of_orientation
    (M := M) g α₀ α₁ y hc h_w

theorem outwardNormalAt_eq_outwardNormal_on_chart
    [HasOrientableBoundary (E := E) (H := H) (I := I) M]
    (g : SmoothRiemannianMetric I M) (α₀ : BoundaryManifold I M)
    {y : BoundaryManifold I M}
    (hy : (y : M) ∈ (chartAt H (α₀ : M)).source) :
    outwardNormalAt (M := M) g α₀ y = outwardNormal (M := M) g y := by
  have hy_self : (y : M) ∈ (chartAt H (y : M)).source := mem_chart_source H (y : M)
  have h_chart_inv :
      outwardNormalAt (M := M) g α₀ y = outwardNormalAt (M := M) g y y :=
    outwardNormalAt_chart_invariance (M := M) g α₀ y hy hy_self
  rw [h_chart_inv, outwardNormalAt_self]

theorem outwardNormal_contMDiff
    [HasOrientableBoundary (E := E) (H := H) (I := I) M]
    (g : SmoothRiemannianMetric I M) :
    ContMDiff hI.boundaryI (I.prod 𝓘(ℝ, E)) ∞
      (fun x : BoundaryManifold I M =>
        TotalSpace.mk' E (boundaryInclusion I M x)
          (outwardNormal (M := M) g x)) := by
  intro x₀
  have h_smooth_at : ContMDiffAt hI.boundaryI (I.prod 𝓘(ℝ, E)) ∞
      (fun b : BoundaryManifold I M =>
        TotalSpace.mk' E (b : M) (outwardNormalAt (M := M) g x₀ b)) x₀ :=
    outwardNormalAt_section_contMDiffAt (M := M) g x₀
  set U : Set (BoundaryManifold I M) :=
    Subtype.val ⁻¹' (chartAt H (x₀ : M)).source with hU_def
  have hU_open : IsOpen U :=
    (chartAt H (x₀ : M)).open_source.preimage continuous_subtype_val
  have hU_mem : x₀ ∈ U := by
    change (x₀ : M) ∈ (chartAt H (x₀ : M)).source
    exact mem_chart_source H (x₀ : M)
  have hU_nhds : U ∈ 𝓝 x₀ := hU_open.mem_nhds hU_mem
  have h_eventually :
      (fun b : BoundaryManifold I M =>
          TotalSpace.mk' E (boundaryInclusion I M b)
            (outwardNormal (M := M) g b)) =ᶠ[𝓝 x₀]
        (fun b : BoundaryManifold I M =>
          TotalSpace.mk' E (b : M) (outwardNormalAt (M := M) g x₀ b)) := by
    refine Filter.eventually_of_mem hU_nhds ?_
    intro b hb_mem
    have h_eq : outwardNormalAt (M := M) g x₀ b = outwardNormal (M := M) g b :=
      outwardNormalAt_eq_outwardNormal_on_chart (M := M) g x₀ hb_mem
    change TotalSpace.mk' E (boundaryInclusion I M b) (outwardNormal (M := M) g b) =
        TotalSpace.mk' E (b : M) (outwardNormalAt (M := M) g x₀ b)
    simp only [boundaryInclusion_apply, h_eq]
  exact h_smooth_at.congr_of_eventuallyEq h_eventually

theorem outwardNormal_continuous
    [HasOrientableBoundary (E := E) (H := H) (I := I) M]
    (g : SmoothRiemannianMetric I M) :
    Continuous (fun x : BoundaryManifold I M =>
      TotalSpace.mk' E (boundaryInclusion I M x) (outwardNormal (M := M) g x)) :=
  (outwardNormal_contMDiff (M := M) g).continuous

theorem continuous_outwardNormal_inner
    [HasOrientableBoundary (I := I) M]
    (g : SmoothRiemannianMetric I M)
    (V : (x : BoundaryManifold I M) → TangentSpace I (x : M))
    (hV : Continuous (fun x : BoundaryManifold I M => TotalSpace.mk' E (x : M) (V x))) :
    Continuous (fun x : BoundaryManifold I M =>
      g.inner (x : M) (outwardNormal (M := M) g x) (V x)) := by
  have hg := g.contMDiff.continuous.comp (continuous_subtype_val :
    Continuous (fun x : BoundaryManifold I M => (x : M)))
  have hnu := outwardNormal_continuous g
  have h : Continuous (fun x : BoundaryManifold I M =>
      TotalSpace.mk' Real (E := Bundle.Trivial M Real) (x : M)
        (g.inner (x : M) (outwardNormal (M := M) g x) (V x))) :=
    hg.clm_bundle_apply₂ (F₁ := E) (F₂ := E) hnu hV
  apply continuous_iff_continuousAt.mpr
  intro x
  have hx := h.continuousAt (x := x)
  rw [FiberBundle.continuousAt_totalSpace] at hx
  exact hx.2

theorem continuous_outwardNormal_inner_smoothSection
    [HasOrientableBoundary (I := I) M]
    (g : SmoothRiemannianMetric I M)
    (V : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    Continuous (fun x : BoundaryManifold I M =>
      g.inner (x : M) (outwardNormal (M := M) g x) (V (x : M))) :=
  continuous_outwardNormal_inner g (fun x => V (x : M))
    (V.contMDiff.continuous.comp continuous_subtype_val)

end WithBoundary
end DivergenceTheorem
end Integral
end DifferentialGeometry
