import DifferentialGeometry.Geometry.Curvature.Bounds.SectionalPerturbationUpper
import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspMetricEquivalence
import DifferentialGeometry.Geometry.Collapse.BoundaryScale.FirstScaleInterior
import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CurvatureBuffers
import DifferentialGeometry.Geometry.Collapse.BoundaryScale.AnalyticData

/-!
# Consumers of lane B-1 (F-a general and order-zero, BSA03 interior)

* The exact model (error `0`): a metric of constant curvature `-1/4` with Riemann operator
  bounded by `10` is pinched in `[-1/2, -1/8]` (`sectional_pinching_of_exact_cusp_model`).
* A perturbed metric: `C²`-error `ε ≤ 1/4000` from such a model forces a negative plane, hence
  `R_p < 3` by W4-BSA's kernel (`curvatureRadius_lt_three_of_small_metric_derivatives`), and, on the
  unit ball, `1 ≤ R_p` (`one_le_curvatureRadius_of_small_metric_derivatives`): the two BSA01 scale
  clauses composed by `exact` with `BoundaryScale/CurvatureBuffers.lean`.
* Every collar of a nearly cuspidal boundary with `δ ≤ 1/100` has `|dz| ≤ 1.01`
  (`NearlyCuspidalBoundary.abs_height_deriv_le`).
* BSA03 at interior centres feeds W4-BSA's exact attainment
  (`ballVolume_firstVolumeScale_eq_of_pos`).
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.SmoothRiemannianMetric (abs_metric_inner_le_sqrt_metric_quadratic)
open GC.Endpoint Bundle
open scoped Manifold ContDiff ENNReal
namespace DifferentialGeometry.Geometry.Collapse
universe u

section Model

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [BoundarylessManifold I M]

/-- The exact model (metric error `0`): constant curvature `-1/4` and `|R_G| ≤ 10` at `x` give the
BSA01 pinching `-1/2 ≤ sec ≤ -1/8` for `G` itself. -/
theorem sectional_pinching_of_exact_cusp_model (G : SmoothRiemannianMetric I M) (x : M) {K : ℝ}
    (hK : K ≤ 10)
    (hmodel : ∀ u v w : TangentSpace I x,
      let r := riemannOp (LeviCivita G) x u v w
      Real.sqrt (G.inner x r r) ≤
        K * Real.sqrt (G.inner x u u) * Real.sqrt (G.inner x v v) *
          Real.sqrt (G.inner x w w))
    (hconst : ∀ u v : TangentSpace I x,
      metricRm04StandardAt G x u v v u =
        -(1 / 4 : ℝ) * (G.inner x u u * G.inner x v v - (G.inner x u v) ^ 2)) :
    SectionalBoundedBelowAt G x (-(1 / 2)) ∧
      ∀ u v : TangentSpace I x,
        metricRm04StandardAt G x u v v u ≤
          -((1 / 8 : ℝ) * (G.inner x u u * G.inner x v v - (G.inner x u v) ^ 2)) :=
  cusp_sectional_pinching_of_small_metric_derivatives G G x (by norm_num) hK
    (fun k _ => (metricDerivNorm_self k G G x).le) hmodel hconst

/-- A perturbed metric, BSA01's `R_p < 3`: a `C²`-error `ε ≤ 1/4000` from a `-1/4` model at `p`
and one `g`-nondegenerate plane give `curvatureRadius g p < 3`. -/
theorem curvatureRadius_lt_three_of_small_metric_derivatives
    (g G : SmoothRiemannianMetric I M) (p : M) {ε K : ℝ} (hε : ε ≤ 1 / 4000) (hK : K ≤ 10)
    (hsmall : ∀ k : ℕ, k ≤ 2 → metricDerivNorm k g G G p ≤ ε)
    (hmodel : ∀ u v w : TangentSpace I p,
      let r := riemannOp (LeviCivita G) p u v w
      Real.sqrt (G.inner p r r) ≤
        K * Real.sqrt (G.inner p u u) * Real.sqrt (G.inner p v v) *
          Real.sqrt (G.inner p w w))
    (hconst : ∀ u v : TangentSpace I p,
      metricRm04StandardAt G p u v v u =
        -(1 / 4 : ℝ) * (G.inner p u u * G.inner p v v - (G.inner p u v) ^ 2))
    (v w : TangentSpace I p) (hgram : 0 < g.inner p v v * g.inner p w w - g.inner p v w ^ 2) :
    curvatureRadius g p < 3 := by
  have h := (cusp_sectional_pinching_of_small_metric_derivatives g G p hε hK hsmall hmodel
    hconst).2 v w
  exact curvatureRadius_lt_three_of_negative_plane g p v w hgram (by linarith)

/-- A perturbed metric, BSA01's `1 ≤ R_p`: a `C²`-error `ε ≤ 1/4000` from `-1/4` models at every
point of the unit ball gives `1 ≤ curvatureRadius g p`. -/
theorem one_le_curvatureRadius_of_small_metric_derivatives
    (g G : SmoothRiemannianMetric I M) (p : M) {ε K : ℝ} (hε : ε ≤ 1 / 4000) (hK : K ≤ 10)
    (hsmall : ∀ q ∈ riemannianBallOf g p 1, ∀ k : ℕ, k ≤ 2 → metricDerivNorm k g G G q ≤ ε)
    (hmodel : ∀ q ∈ riemannianBallOf g p 1, ∀ u v w : TangentSpace I q,
      let r := riemannOp (LeviCivita G) q u v w
      Real.sqrt (G.inner q r r) ≤
        K * Real.sqrt (G.inner q u u) * Real.sqrt (G.inner q v v) *
          Real.sqrt (G.inner q w w))
    (hconst : ∀ q ∈ riemannianBallOf g p 1, ∀ u v : TangentSpace I q,
      metricRm04StandardAt G q u v v u =
        -(1 / 4 : ℝ) * (G.inner q u u * G.inner q v v - (G.inner q u v) ^ 2)) :
    1 ≤ curvatureRadius g p := by
  refine one_le_curvatureRadius_of_sectional_ball g p fun q hq u v => ?_
  have h := (cusp_sectional_pinching_of_small_metric_derivatives g G q hε hK (hsmall q hq)
    (hmodel q hq) (hconst q hq)).1 u v
  have hcs := abs_metric_inner_le_sqrt_metric_quadratic g q u v
  have hsq : (g.inner q u v) ^ 2 ≤ g.inner q u u * g.inner q v v := by
    have h2 := sq_le_sq' (abs_le.mp hcs).1 (abs_le.mp hcs).2
    rwa [mul_pow, Real.sq_sqrt (metric_inner_self_nonneg g q u),
      Real.sq_sqrt (metric_inner_self_nonneg g q v)] at h2
  nlinarith

end Model

/-- Every collar of a nearly cuspidal boundary with `δ ≤ 1/100` has `|dz| ≤ 1.01` on its whole
domain (BSA01's `|dz|` clause at the level of the embeddings). -/
theorem NearlyCuspidalBoundary.abs_height_deriv_le {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ}
    (B : NearlyCuspidalBoundary W g K δ) (hδ : δ ≤ 1 / 100) (i : Fin B.count)
    {p : CuspHalfSpace} (hp : p ∈ cuspDomain) (v : TangentSpace halfCollarModel p) :
    |v.2 0| ≤ 1.01 * Real.sqrt (g.inner ((B.collar i).toFun p)
      (mfderiv halfCollarModel W.model (B.collar i).toFun p v)
      (mfderiv halfCollarModel W.model (B.collar i).toFun p v)) :=
  (B.collar i).abs_height_deriv_le_of_le_hundredth hδ hp v

/-- BSA03 at interior centres composed with W4-BSA's exact attainment: at a centre with positive
boundary distance the ball of radius `r_p(w)` has volume exactly `w r_p(w)³`. -/
theorem ballVolume_firstVolumeScale_eq_of_distanceToBoundary_pos (W : CompactCarrier.{u})
    (g : SmoothRiemannianMetric W.model W.Carrier) (p : W.Carrier)
    (hd : 0 < distanceToBoundary W g p) {w : ℝ} (hw : 0 < w)
    (hwc : w < euclideanThreeUnitBallVolume) :
    ballVolume g p (firstVolumeScale g p w) = ENNReal.ofReal (w * firstVolumeScale g p w ^ 3) :=
  ballVolume_firstVolumeScale_eq_of_pos g p hw
    (firstVolumeScale_pos_of_distanceToBoundary_pos W g p hd hw hwc)

end DifferentialGeometry.Geometry.Collapse
