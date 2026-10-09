import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.CovariantDerivative.Tail
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.DuhamelWindow_S57
import DifferentialGeometry.Geometry.Metric.Tensor.Scaling
import DifferentialGeometry.Geometry.Connection.LeviCivita.Scaling
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Scaling
import DifferentialGeometry.Geometry.Metric.DerivativeScaleENorm

set_option autoImplicit false

/-!
# CH12-S81 / G1: parabolic-rescaling bookkeeping for the reference-jet bound (`hReferenceJets`)

For a Ricci flow `S` and `t > 0`, the rescaled sequence `qSeq_S81 S t τ = t⁻¹ • S.metric (t τ)` is again a
Ricci flow in `τ`.  The Ricci tower `∇_{·}^s Ric` is invariant under constant scaling of the metric
(Levi-Civita connection and Ricci tensor are), the `(0,k)`-norm scales by `c^(-k/2)`, and
`∇_h^q (c g) = c ∇_h^q g`.  These are the translations used to feed the unit-scale all-order tower
`covOrder_tower_const` / `ric_bound_field_on` and to bring its conclusion back to scale `r`.
-/

noncomputable section
open Set Bundle Manifold DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Metric
open scoped Manifold ContDiff Topology
namespace GC.LongTime.Ch12

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

/-- the rescaled sequence `τ ↦ t⁻¹ • S.metric (t τ)` (constant in the sequence index). -/
def qSeq_S81 {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (t : ℝ) (ht : 0 < t) :
    ℕ → ℝ → SmoothRiemannianMetric I M :=
  fun _ τ => scaleMetric t⁻¹ (inv_pos.2 ht) (S.base.metric (t * τ))

omit [CompleteSpace E] in
/-- the Ricci tower is invariant under scaling the metric whose Ricci tensor is taken. -/
theorem ricCovTower_scaleMetric_left_S81 (c : ℝ) (hc : 0 < c) (g h : SmoothRiemannianMetric I M)
    (s : ℕ) :
    ricCovTower (I := I) (scaleMetric c hc g) h s = ricCovTower (I := I) g h s := by
  unfold ricCovTower
  simp only [lcConn_scaleMetric]

/-- the Ricci tower is invariant under scaling the reference metric. -/
theorem ricCovTower_scaleMetric_right_S81 (c : ℝ) (hc : 0 < c) (g h : SmoothRiemannianMetric I M)
    (s : ℕ) :
    ricCovTower (I := I) g (scaleMetric c hc h) s = ricCovTower (I := I) g h s := by
  unfold ricCovTower
  exact DifferentialGeometry.Geometry.Tensor.iterCov_scaleMetric h c hc 2 _ s

omit [CompleteSpace E] in
/-- `nablaRicReal` of the rescaled sequence is that of the flow at the unscaled time. -/
theorem nablaRicReal_qSeq_S81 {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (h : SmoothRiemannianMetric I M) {t : ℝ} (ht : 0 < t) (q i : ℕ) (τ : ℝ) (x : M) :
    nablaRicReal (I := I) (qSeq_S81 S t ht) h q i τ x =
      nablaRicReal (I := I) (fun _ s => S.base.metric s) h q 0 (t * τ) x := by
  unfold nablaRicReal qSeq_S81
  simp only [ricCovTower_scaleMetric_left_S81]

variable [I.Boundaryless] in
/-- the order-`q` derivative of the rescaled metric evolves by `-2 ∇^q Ric` (unit time scale). -/
theorem qSeq_hasDerivAt_S81 {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) (h : SmoothRiemannianMetric I M) {t : ℝ} (ht : 0 < t) (q i : ℕ)
    {τ : ℝ} (hτ : t * τ ∈ D.regular) (x : M) (v : Fin (q + 2) → TangentSpace I x) :
    HasDerivAt (fun τ' => metricCovDeriv (I := I) (qSeq_S81 S t ht i τ') h q x v)
      (((-2 : ℝ) • nablaRicReal (I := I) (qSeq_S81 S t ht) h q i τ x) v) τ := by
  have hF := metricCovDeriv_hasDerivAt_S57 S hS h q hτ x v
  have hc : HasDerivAt (fun τ' : ℝ => t * τ') t τ := by
    simpa using (hasDerivAt_id τ).const_mul t
  have hcomp := (hF.comp τ hc).const_mul t⁻¹
  have hfun : (fun τ' => metricCovDeriv (I := I) (qSeq_S81 S t ht i τ') h q x v) =
      fun τ' => t⁻¹ * (metricCovDeriv (I := I) (S.base.metric (t * τ')) h q x v) := by
    funext τ'
    simp only [qSeq_S81, metricCovDeriv_scaleMetric_left]
    rfl
  rw [hfun, nablaRicReal_qSeq_S81]
  refine HasDerivAt.congr_deriv hcomp ?_
  simp only [smul_apply, smul_eq_mul]
  field_simp

end GC.LongTime.Ch12
