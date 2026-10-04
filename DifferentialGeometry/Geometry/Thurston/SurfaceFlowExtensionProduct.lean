import DifferentialGeometry.Geometry.Thurston.EquivariantRoundMetricA3Algebra
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extension.Maximal.Time
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.ProductLine
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.Pullback
import DifferentialGeometry.Geometry.Metric.AddCircle
import DifferentialGeometry.Geometry.Metric.ModelChange
import DifferentialGeometry.Topology.Manifold.ModelWithCorners

/-!
# The circle product of a surface flow

Chapter 7, surface lemma U1, route (a), step a1 (lane U1E2), tier T1 of route E2 (D17 §4 as
corrected by review 17 §3). A Ricci flow `g(t)` on a surface `M` is turned into the Ricci flow
`G(t) = g(t) ⊕ dθ²` on the closed three-manifold `M × S¹` (`S¹ = AddCircle 1`), written in a
Euclidean model so that the three-dimensional extension criterion `extends_of_rmBounded` applies.

* `ricciTensor_eq_zero_of_modelReal`, `isSolutionOn_const_flatCircle`,
  `metricRm04At_flatCircle`: every metric on a one-manifold is flat, so the circle metric
  `AddCircle.flatMetric` is a constant Ricci flow and a flat factor.
* `circleProductModelEquiv`, `circleProductModel`, `circleProductChange`: the model
  `(I.prod 𝓘(ℝ, ℝ)).transContinuousLinearEquiv e` with `e : E × ℝ ≃L[ℝ] EuclideanSpace ℝ (Fin 3)`
  (when `finrank E = 2`) and the identity diffeomorphism into it.
* `circleProductFlow`, `isSolutionOn_circleProductFlow`: the product flow
  (`isSolutionOn_prod`) moved to that model (`IsSolutionOn.pullback`).
* `circleProductFlow_metric_pullback`: moving back gives `g(t).prod flatMetric`.
* `circleProductFlow_curvatureNormSq`: `|Rm_G|²(x, θ) = R_g(x)²`, from the model change
  (`riemannNormSq_cross`), the flat-factor formula `normSq0S_iterCov_rm04_prod_of_flat` at order
  zero, and the two-dimensional identity `|Rm|² = R²`, `normSq0S_metricRm04At_eq_sq_of_finrank_two`
  (lane P8, `EquivariantRoundMetricA3Algebra`).
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow
open Bundle Set
open scoped Manifold ContDiff

namespace GC.Geometry

local notation "S1" => AddCircle (1 : ℝ)
local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem ricciTensor_eq_zero_of_modelReal {N : Type*} [TopologicalSpace N] [ChartedSpace ℝ N]
    [IsManifold 𝓘(ℝ, ℝ) ∞ N] [T2Space N] (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) N) (y : N)
    (v w : TangentSpace 𝓘(ℝ, ℝ) y) : ricciTensor g y v w = 0 := by
  rw [ricciTensor_apply_basisSum]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [riemannOp_eq_zero_of_finrank_le_one (I := 𝓘(ℝ, ℝ)) (M := N)
    (cov := DifferentialGeometry.Geometry.Connection.LeviCivita (I := 𝓘(ℝ, ℝ)) g)
    (by simp) y _ _ _]
  simp

theorem isSolutionOn_const_flatCircle (D : RealTimeInterval) :
    IsSolutionOn (SolutionOn.const AddCircle.flatMetric D) :=
  isSolutionOn_const_of_ricciTensor_eq_zero _ (ricciTensor_eq_zero_of_modelReal _) D

theorem metricRm04At_flatCircle (y : S1) (w : Fin 4 → TangentSpace 𝓘(ℝ, ℝ) y) :
    metricRm04At AddCircle.flatMetric y w = 0 := by
  rw [metricRm04At_eq_zero_of_finrank_le_one AddCircle.flatMetric (by simp) y]
  rfl

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

def circleProductModelEquiv (hdim : Module.finrank ℝ E = 2) : (E × ℝ) ≃L[ℝ] E3 :=
  ContinuousLinearEquiv.ofFinrankEq (by simp [Module.finrank_prod, hdim])

variable (I) in
abbrev circleProductModel (hdim : Module.finrank ℝ E = 2) :
    ModelWithCorners ℝ E3 (ModelProd H ℝ) :=
  (I.prod 𝓘(ℝ, ℝ)).transContinuousLinearEquiv (circleProductModelEquiv hdim)

variable (I M) in
def circleProductChange (hdim : Module.finrank ℝ E = 2) :
    (M × S1) ≃ₘ⟮I.prod 𝓘(ℝ, ℝ), circleProductModel I hdim⟯ (M × S1) :=
  ContinuousLinearEquiv.toTransContinuousLinearEquiv _ _ _

def circleProductFlow (hdim : Module.finrank ℝ E = 2) {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) :
    SolutionOn (I := circleProductModel I hdim) (M := M × S1) D :=
  (S.prod (SolutionOn.const AddCircle.flatMetric D)).pullback (circleProductChange I M hdim).symm

theorem isSolutionOn_circleProductFlow [BoundarylessManifold I M]
    (hdim : Module.finrank ℝ E = 2) {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S) :
    IsSolutionOn (circleProductFlow hdim S) :=
  IsSolutionOn.pullback _ (isSolutionOn_prod S hS _ (isSolutionOn_const_flatCircle D)) _

omit [I.Boundaryless] in
theorem circleProductFlow_metric_pullback (hdim : Module.finrank ℝ E = 2)
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (t : ℝ) :
    Diffeomorph.pullbackMetricCross ((circleProductFlow hdim S).family.metric t)
      (circleProductChange I M hdim) = (S.family.metric t).prod AddCircle.flatMetric :=
  SmoothRiemannianMetric.pullback_transContinuousLinearEquiv _ _

theorem circleProductFlow_curvatureNormSq [CompactSpace M] [BoundarylessManifold I M]
    (hdim : Module.finrank ℝ E = 2) {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : ℝ) (p : M × S1) :
    curvatureNormSq (circleProductFlow hdim S) (circleProductFlow hdim S).base.rm04 t p =
      S.scalar t p.1 ^ 2 := by
  rw [curvatureNormSq_apply]
  change Tensor0SBundle.normSq0S
      (Diffeomorph.pullbackMetricCross ((S.family.metric t).prod AddCircle.flatMetric)
        (circleProductChange I M hdim).symm) p 4
      (metricRm04 (Diffeomorph.pullbackMetricCross
        ((S.family.metric t).prod AddCircle.flatMetric) (circleProductChange I M hdim).symm) p) =
    S.scalar t p.1 ^ 2
  rw [metricRm04_apply, CheegerGromovCompactness.riemannNormSq_cross]
  have h := normSq0S_iterCov_rm04_prod_of_flat (S.family.metric t) AddCircle.flatMetric
    metricRm04At_flatCircle 0 p
  exact h.trans (normSq0S_metricRm04At_eq_sq_of_finrank_two hdim (S.family.metric t) p.1)

end GC.Geometry
