import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.SphereUnitFilling

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff Topology
open Set Function

namespace DifferentialGeometry.Topology

namespace BallChart

variable {n : ℕ} {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

noncomputable def closedBallHomeomorphBallImage (c : BallChart n I M) :
    Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 ≃ₜ
      {x : M // x ∈ c.chart '' Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1} where
  toFun x := ⟨c.chart x, ⟨(x : EuclideanSpace ℝ (Fin n)), x.2, rfl⟩⟩
  invFun y := ⟨c.chart.toPartialEquiv.invFun (y : M), by
    obtain ⟨x, hx, hxy⟩ := y.2
    have hinv : c.chart.toPartialEquiv.invFun (y : M) = x := by
      rw [← hxy]
      exact c.chart.toPartialEquiv.left_inv (c.closedBall_one_subset_source hx)
    rw [hinv]
    exact hx⟩
  left_inv x := by
    apply Subtype.ext
    change c.chart.toPartialEquiv.invFun (c.chart.toPartialEquiv.toFun
      (x : EuclideanSpace ℝ (Fin n))) = (x : EuclideanSpace ℝ (Fin n))
    exact c.chart.toPartialEquiv.left_inv (c.closedBall_one_subset_source x.2)
  right_inv y := by
    apply Subtype.ext
    obtain ⟨x, hx, hxy⟩ := y.2
    have h : c.chart.toPartialEquiv.toFun (c.chart.toPartialEquiv.invFun
        (c.chart.toPartialEquiv.toFun x)) = c.chart.toPartialEquiv.toFun x :=
      c.chart.toPartialEquiv.right_inv'
        (c.chart.toPartialEquiv.map_source (c.closedBall_one_subset_source hx))
    simpa only [hxy] using h
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact ContinuousOn.comp_continuous c.chart.contMDiffOn_toFun.continuousOn
      continuous_subtype_val (fun x => c.closedBall_one_subset_source x.2)
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ _
    have hcont : ContinuousOn c.chart.toPartialEquiv.invFun
        (c.chart '' Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :=
      c.chart.contMDiffOn_invFun.continuousOn.mono (by
        rintro y ⟨x, hx, rfl⟩
        exact c.chart.map_source (c.closedBall_one_subset_source hx))
    exact hcont.comp_continuous continuous_subtype_val (fun y => y.2)

@[simp]
theorem closedBallHomeomorphBallImage_apply (c : BallChart n I M)
    (x : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :
    (closedBallHomeomorphBallImage c x : M) = c.chart x := rfl

@[simp]
theorem closedBallHomeomorphBallImage_symm_apply (c : BallChart n I M)
    (y : {x : M // x ∈ c.chart '' Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1}) :
    ((closedBallHomeomorphBallImage c).symm y : EuclideanSpace ℝ (Fin n)) =
      c.chart.toPartialEquiv.invFun (y : M) := rfl

end BallChart

namespace SphereUnitFilling

theorem capHomeomorph_boundary (P : S3) (z : Metric.sphere (0 : E3) 1) :
    capHomeomorph P ((sphereBallChart P).boundaryMap (sphereAnti z)) =
      ⟨z, Metric.sphere_subset_closedBall z.2⟩ := by
  change capToBall P ((sphereBallChart P).boundaryMap (sphereAnti z)) = ⟨z, _⟩
  exact capToBall_boundary P z

theorem capToBall_radialRightClamp_val (P : S3) (z : Metric.sphere (0 : E3) 1)
    (p : ConnectedSumQuotient.CollarDomain) (hp : (p.2 : ℝ) < 0) :
    (capToBall P (ConnectedSumQuotient.radialRightClamp (sphereBallChart P) (sphereAnti z) p) :
      E3) = (1 + (p.2 : ℝ)) • (z : E3) := by
  have h1 : 1 ≤ 1 - (p.2 : ℝ) := by linarith [p.2.2.2]
  have h2 : 1 - (p.2 : ℝ) ≤ 3 / 2 := by linarith [p.2.2.1]
  have hρ : 1 - (p.2 : ℝ) ∈ Set.Icc (1 : ℝ) 2 := ⟨h1, by linarith⟩
  have hmax : max 1 (1 - (p.2 : ℝ)) = 1 - (p.2 : ℝ) := max_eq_right (by linarith)
  have hmain : (capToBall P
      (ConnectedSumQuotient.radialRightClamp (sphereBallChart P) (sphereAnti z) p) : E3) =
      (2 - (1 - (p.2 : ℝ))) • (z : E3) := by
    have h := congrArg (fun w : Metric.closedBall (0 : E3) 1 => (w : E3))
      (capToBall_radial P z h1 h2 hρ)
    simpa only [ConnectedSumQuotient.radialRightClamp, hmax, Subtype.coe_mk] using h
  rw [hmain]
  module

end SphereUnitFilling

end DifferentialGeometry.Topology
