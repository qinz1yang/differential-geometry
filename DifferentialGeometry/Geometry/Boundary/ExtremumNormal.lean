import DifferentialGeometry.Topology.Manifold.LocalExtrema
import DifferentialGeometry.Geometry.Boundary.Normal.Derivative
import DifferentialGeometry.Geometry.Boundary.Model.EuclideanHalfSpace
import DifferentialGeometry.Geometry.Boundary.DefiningFunction.Basic

open scoped Manifold ContDiff Topology Convex

namespace DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Boundary

noncomputable section

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]

theorem mvfderiv_inwardCoord_nonpos_of_isLocalMax
    {f : M → ℝ} {x : BoundaryManifold (modelWithCornersEuclideanHalfSpace n) M}
    (hmax : IsLocalMax f (x : M)) :
    mvfderiv (modelWithCornersEuclideanHalfSpace n) f (x : M)
      (inwardCoord x) ≤ 0 := by
  have hin := inwardCoord_eq x
  change inwardCoord x = EuclideanSpace.single (0 : Fin n) (1 : ℝ) at hin
  rw [hin]
  apply hmax.mvfderiv_nonpos
  apply mem_posTangentConeAt_of_frequently_mem
  apply Filter.Eventually.frequently
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [range_modelWithCornersEuclideanHalfSpace]
  have hx : 0 ≤ (extChartAt (modelWithCornersEuclideanHalfSpace n) (x : M) (x : M)) 0 := by
    exact (chartAt (EuclideanHalfSpace n) (x : M) (x : M)).property
  change 0 ≤ (extChartAt (modelWithCornersEuclideanHalfSpace n) (x : M) (x : M)) 0 + t * _
  change 0 ≤ (extChartAt (modelWithCornersEuclideanHalfSpace n) (x : M) (x : M)) 0 +
    t * (EuclideanSpace.single (0 : Fin n) (1 : ℝ)).ofLp 0
  simpa only [PiLp.single_apply, ↓reduceIte, mul_one] using add_nonneg hx (le_of_lt ht)

theorem outwardNormal_eq_levelSetOutwardNormal_of_isLocalMax
    (g : SmoothRiemannianMetric (modelWithCornersEuclideanHalfSpace n) M)
    {f : M → ℝ} {x : BoundaryManifold (modelWithCornersEuclideanHalfSpace n) M}
    (hmax : IsLocalMax f (x : M))
    (hf : MDifferentiableAt (modelWithCornersEuclideanHalfSpace n) 𝓘(ℝ, ℝ) f (x : M))
    (hreg : mfderiv (modelWithCornersEuclideanHalfSpace n) 𝓘(ℝ, ℝ) f (x : M) ≠ 0) :
    outwardNormal g x = levelSetOutwardNormal g f (x : M) := by
  let J := modelWithCornersEuclideanHalfSpace n
  let V := normalSubspace g x
  let ν : TangentSpace J (x : M) := outwardNormal g x
  let G : TangentSpace J (x : M) := gradientFun g f (x : M)
  have hν : ν ∈ V := outwardNormal_mem_normalSubspace g x
  have hG : G ∈ V := by
    intro w
    rw [inner_gradientFun]
    have hmin : IsLocalMin (fun y : BoundaryManifold J M => -f (y : M)) x := by
      exact hmax.neg.comp_continuous (continuous_subtype_val.continuousAt)
    have hz := mfderiv_boundary_tangent_eq_zero_at_local_min hmin hf.neg w
    change mfderiv J 𝓘(ℝ, ℝ) (-f) (x : M) (boundaryInclusionMfderiv x w) = 0 at hz
    rw [mfderiv_neg] at hz
    exact neg_eq_zero.mp hz
  have hνunit : g.inner (x : M) ν ν = 1 := outwardNormal_norm_one g x
  have hνne : ν ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hνunit
    exact zero_ne_one hνunit
  let νV : V := ⟨ν, hν⟩
  let GV : V := ⟨G, hG⟩
  have hνV : νV ≠ 0 := by
    intro hz
    exact hνne (congrArg Subtype.val hz)
  obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one
    (normalSubspace_finrank_one g x) hνV GV
  have hcG : c • ν = G := congrArg Subtype.val hc
  have hGpos : 0 < g.inner (x : M) G G := by
    exact lt_of_le_of_ne (normGradSqFun_nonneg g f (x : M))
      (Ne.symm (mt normGradSqFun_eq_zero_iff.mp hreg))
  have hcne : c ≠ 0 := by
    intro hz
    have hGzero : G = 0 := by simpa only [hz, zero_smul] using hcG.symm
    rw [hGzero, map_zero] at hGpos
    exact (lt_irrefl 0) hGpos
  have hνin : g.inner (x : M) ν (inwardCoord x) < 0 :=
    outwardNormal_inner_inwardCoord_neg g x
  have hGin : g.inner (x : M) G (inwardCoord x) ≤ 0 := by
    rw [inner_gradientFun]
    exact mvfderiv_inwardCoord_nonpos_of_isLocalMax hmax
  have hcpos : 0 < c := by
    have heq : g.inner (x : M) G (inwardCoord x) =
        c * g.inner (x : M) ν (inwardCoord x) := by
      rw [← hcG, map_smul, smul_apply, smul_eq_mul]
    rw [heq] at hGin
    exact lt_of_le_of_ne (nonneg_of_mul_nonpos_left hGin hνin) (Ne.symm hcne)
  have hGG : g.inner (x : M) G G = c ^ 2 := by
    rw [← hcG]
    have hleft : g.inner (x : M) (c • ν) = c • g.inner (x : M) ν := map_smul _ _ _
    rw [hleft]
    change c * g.inner (x : M) ν (c • ν) = c ^ 2
    rw [map_smul]
    change c * (c * g.inner (x : M) ν ν) = c ^ 2
    rw [hνunit, mul_one, sq]
  rw [levelSetOutwardNormal_eq g f (x : M) hGpos]
  change ν = (Real.sqrt (g.inner (x : M) G G))⁻¹ • G
  rw [hGG, Real.sqrt_sq hcpos.le, ← hcG, smul_smul, inv_mul_cancel₀ hcne, one_smul]

end

end DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
