import DifferentialGeometry.Geometry.Boundary.Normal.Outward
import DifferentialGeometry.Geometry.Metric.Basic

noncomputable section
open Set Function
open scoped ContDiff Manifold
open DifferentialGeometry

namespace Poincare.Geometry.Boundary

open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
open DifferentialGeometry.Integral.Measure

variable {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [hI : HasSmoothBoundary E H I] [IsManifold I ∞ M]

theorem exists_pos_inward_decomposition_iff (g : SmoothRiemannianMetric I M)
    (x : BoundaryManifold I M) (v : TangentSpace I x.1) :
    (∃ (w : TangentSpace hI.boundaryI x) (c : ℝ), 0 < c ∧
      v = boundaryInclusionMfderiv x w + c • inwardCoord x) ↔
      g.inner x.1 v (outwardNormal g x) < 0 := by
  have hi : g.inner x.1 (inwardCoord x) (outwardNormal g x) < 0 := by
    rw [g.symm]
    exact outwardNormal_inner_inwardCoord_neg g x
  have hformula : ∀ (w : TangentSpace hI.boundaryI x) (c : ℝ),
      g.inner x.1 (boundaryInclusionMfderiv x w + c • inwardCoord x) (outwardNormal g x) =
        c * g.inner x.1 (inwardCoord x) (outwardNormal g x) := by
    intro w c
    rw [map_add, add_apply, inner_dincl_outwardNormal, map_smul, smul_apply, zero_add]
    rfl
  constructor
  · rintro ⟨w, c, hc, rfl⟩
    rw [hformula]
    exact mul_neg_of_pos_of_neg hc hi
  · intro hv
    let L := (boundaryInclusionMfderiv x).toLinearMap
    have hinj : Function.Injective L := dincl_injective x
    have hdim : Module.finrank ℝ (LinearMap.range L) + 1 =
        Module.finrank ℝ (TangentSpace I x.1) := by
      rw [LinearMap.finrank_range_of_inj hinj]
      exact hI.finrank_boundaryE_succ
    have hquot : Module.finrank ℝ (TangentSpace I x.1 ⧸ LinearMap.range L) = 1 := by
      have hd := Submodule.finrank_quotient_add_finrank (LinearMap.range L)
      omega
    have htrans : inwardCoord x ∉ LinearMap.range L := InwardCoordTransverse_of_HasSmoothBoundary x
    have htop : LinearMap.range L ⊔ Submodule.span ℝ {inwardCoord x} = ⊤ :=
      (Submodule.sup_span_singleton_eq_top_iff htrans).2 hquot
    have hmem : v ∈ LinearMap.range L ⊔ Submodule.span ℝ {inwardCoord x} := htop ▸ Submodule.mem_top
    obtain ⟨z, ⟨w, rfl⟩, q, hq, heq⟩ := Submodule.mem_sup.mp hmem
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hq
    have heq' : v = boundaryInclusionMfderiv x w + c • inwardCoord x := heq.symm
    refine ⟨w, c, ?_, heq'⟩
    rw [heq', hformula] at hv
    nlinarith

end Poincare.Geometry.Boundary
