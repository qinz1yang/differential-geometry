import DifferentialGeometry.Topology.Manifold.BoundaryCollar.Conormal
import DifferentialGeometry.Geometry.Boundary.Model.EuclideanHalfSpace

open Set Function Topology
open scoped Manifold ContDiff
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
set_option autoImplicit false
noncomputable section

namespace Poincare.Manifold.BoundaryCollar

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) ∞ M]

theorem range_boundaryInclusionMfderiv_eq_ker_proj
    (y : BoundaryManifold (𝓡∂ n) M) :
    (boundaryInclusionMfderiv y).range =
      (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin n)).ker := by
  let B : EuclideanSpace ℝ (Fin (n - 1)) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    boundaryInclusionMfderiv y
  let L := EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin n)
  change B.range = L.ker
  have hcomp : L.comp B = 0 := by
    have heq : (chartHeight (n := n) (y : M)) ∘ boundaryInclusion (𝓡∂ n) M =ᶠ[𝓝 y]
        (fun _ => 0) := by
      filter_upwards [continuous_subtype_val.continuousAt.preimage_mem_nhds
        ((chartAt (EuclideanHalfSpace n) (y : M)).open_source.mem_nhds
          (mem_chart_source (EuclideanHalfSpace n) (y : M)))] with z hz
      exact (chartHeight_eq_zero_iff (n := n) (y : M) hz).mpr z.2
    have hh := mfderiv_comp y
      (((contMDiffOn_chartHeight (n := n) (k := ∞) (y : M)).contMDiffAt
        ((chartAt (EuclideanHalfSpace n) (y : M)).open_source.mem_nhds
          (mem_chart_source _ _))).mdifferentiableAt (by simp))
      ((boundaryInclusion_contMDiff (I := 𝓡∂ n) (M := M) y).mdifferentiableAt (by simp))
    have hchart : mfderiv (𝓡∂ n) 𝓘(ℝ, ℝ) (chartHeight (n := n) (y : M)) (y : M) = L := by
      rw [mfderiv_chartHeight (n := n) (y : M) (mem_chart_source _ _), mfderiv_extChartAt_self]
      exact ContinuousLinearMap.comp_id _
    erw [heq.mfderiv_eq, mfderiv_const, hchart] at hh
    exact hh.symm
  have hle : B.range ≤ L.ker := by
    rintro _ ⟨v, rfl⟩
    change L (B v) = 0
    exact congrArg (fun A : EuclideanSpace ℝ (Fin (n - 1)) →L[ℝ] ℝ => A v) hcomp
  have hB : Module.finrank ℝ B.range = n - 1 := by
    have hb : Function.Injective B := dincl_injective y
    rw [LinearMap.finrank_range_of_inj hb]
    exact finrank_euclideanSpace_fin
  have hLrange : L.range = ⊤ := by
    apply LinearMap.range_eq_top.mpr
    intro c
    exact ⟨EuclideanSpace.single (0 : Fin n) c, by simp [L, EuclideanSpace.proj]⟩
  have hL : Module.finrank ℝ L.ker = n - 1 := by
    have hh := L.toLinearMap.finrank_range_add_finrank_ker
    rw [hLrange] at hh
    simp only [finrank_top, Module.finrank_self, finrank_euclideanSpace_fin] at hh
    omega
  exact Submodule.eq_of_le_of_finrank_eq hle (hB.trans hL.symm)

theorem ker_mfderiv_chartHeight_eq_range_boundaryInclusion (p : M)
    (y : BoundaryManifold (𝓡∂ n) M)
    (hy : (y : M) ∈ (chartAt (EuclideanHalfSpace n) p).source) :
    (mfderiv (𝓡∂ n) 𝓘(ℝ, ℝ) (chartHeight (n := n) p) (y : M)).ker =
      (boundaryInclusionMfderiv y).range := by
  rw [range_boundaryInclusionMfderiv_eq_ker_proj]
  obtain ⟨c, hc, he⟩ := mfderiv_chartHeight_eq_pos_smul_proj (n := n) p hy y.2
  ext v
  change (mfderiv (𝓡∂ n) 𝓘(ℝ, ℝ) (chartHeight (n := n) p) (y : M)) v = 0 ↔
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin n)) v = 0
  erw [he]
  change c * (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin n)) v = 0 ↔
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin n)) v = 0
  exact mul_eq_zero.trans (or_iff_right (ne_of_gt hc))

end Poincare.Manifold.BoundaryCollar
