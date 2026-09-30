import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.StaticWindowVolume
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.WindowRadius
import DifferentialGeometry.Geometry.Comparison.OpenEmbeddingBallCompactness

set_option autoImplicit false
noncomputable section
open Set Function Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Metric DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
  {d : normalizedDatum g x₀ δ k} {A : ℝ} {hA : 0 < A} {D : ℝ}
  {m : ℕ} {ε : ℝ}

theorem exists_window_intrinsic_ball_control
    (w : CanonicalStaticInsertionWitness d A hA D m ε)
    (heps : ε ≤ 1 / 2) {ρ : ℝ} (hρ : 0 < ρ) (hρD : ρ < D) :
    ∃ p : standardCapWindow D, p.val = 0 ∧
      IsCompact {y : standardCapWindow D |
        riemannianEDistOf w.windowMetric p y ≤ ENNReal.ofReal (ρ / 4)} ∧
      ({y : standardCapWindow D |
        riemannianEDistOf w.windowMetric p y ≤ ENNReal.ofReal (ρ / 4)} ⊆
        {y : standardCapWindow D | ‖y.val‖ ≤ ρ}) ∧
      (∀ x : standardCapWindow D, ‖x.val‖ ≤ ρ / 32 →
        riemannianEDistOf w.windowMetric p x ≤ ENNReal.ofReal (ρ / 8)) := by
  let p : standardCapWindow D := ⟨0, by
    change ‖(0 : ThreeSpace)‖ < D + 1
    simp only [norm_zero]
    linarith⟩
  have hid : IsLocalDiffeomorph ThreeModel ThreeModel ∞ (@id (standardCapWindow D)) :=
    (Diffeomorph.refl ThreeModel (standardCapWindow D) ∞).isLocalDiffeomorph
  have hmodel : riemannianClosedBallOf metric p.val ρ = Metric.closedBall 0 ρ := by
    ext x
    change riemannianEDistOf metric 0 x ≤ ENNReal.ofReal ρ ↔ dist x 0 ≤ ρ
    rw [edist_zero, dist_zero_right, ENNReal.ofReal_le_ofReal_iff hρ.le]
  have hsource : riemannianClosedBallOf metric p.val ρ ⊆ standardCapWindow D := by
    intro x hx
    have hh : ‖x‖ ≤ ρ := by simpa only [hmodel, Metric.mem_closedBall, dist_zero_right] using hx
    change ‖x‖ < D + 1
    linarith
  have hcpt : IsCompact (riemannianClosedBallOf metric p.val ρ) := by
    rw [hmodel]
    exact isCompact_closedBall 0 ρ
  have hnorm (x : standardCapWindow D)
      (hx : x.val ∈ riemannianClosedBallOf metric p.val ρ) : ‖x.val‖ ≤ ρ := by
    simpa only [hmodel, Metric.mem_closedBall, dist_zero_right] using hx
  have hlow (x : standardCapWindow D)
      (hx : x.val ∈ riemannianClosedBallOf metric p.val ρ)
      (v : TangentSpace ThreeModel x) :
      metric.inner x.val v v ≤ (2 : ℝ)^2 * w.windowMetric.inner (id x)
        (mfderiv ThreeModel ThreeModel id x v) (mfderiv ThreeModel ThreeModel id x v) := by
    rw [mfderiv_id]
    change metric.inner x.val v v ≤ 2^2 * w.windowMetric.inner x v v
    have hb := (w.window_inner_bounds heps ((hnorm x hx).trans_lt hρD) v).1
    rw [standardCapMetric_eq_metric, SmoothRiemannianMetric.restrictOpen_inner] at hb
    have hn := metric_inner_self_nonneg w.windowMetric x v
    nlinarith
  have hcap := ball_subset_image_of_metric_lower_on_opens w.windowMetric metric
    (standardCapWindow D) id hid injective_id p hρ (by norm_num : (0 : ℝ) < 2)
    hcpt hsource hlow
  have hsub : {y : standardCapWindow D |
      riemannianEDistOf w.windowMetric p y ≤ ENNReal.ofReal (ρ/4)} ⊆
      {y : standardCapWindow D | ‖y.val‖ ≤ ρ} := by
    intro y hy
    have hy' : y ∈ riemannianBallOf w.windowMetric (id p) (ρ/2) :=
      hy.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < ρ/2)).mpr
        (by linarith))
    obtain ⟨z,hz,hzy⟩ := hcap hy'
    change z = y at hzy
    subst y
    exact hnorm z hz
  have hc : IsCompact {y : standardCapWindow D |
      riemannianEDistOf w.windowMetric p y ≤ ENNReal.ofReal (ρ/4)} :=
    isCompact_riemannianClosedBallOf_of_metric_lower_on_opens w.windowMetric metric
      (standardCapWindow D) id hid injective_id p hρ (by norm_num : (0 : ℝ) < 2)
      (by linarith : ρ/4 < ρ/2) hcpt hsource hlow
  refine ⟨p,rfl,hc,hsub,?_⟩
  obtain ⟨q,hq,hinner⟩ := window_image_closedBall_subset_ball_of_metric_upper
    w.windowMetric (r := ρ/32) (R := ρ) (by positivity) (by linarith) hρD
    id hid injective_id (by
      intro x hx v
      rw [mfderiv_id]
      change w.windowMetric.inner x v v ≤ 2 * metric.inner x.val v v
      have hb := (w.window_inner_bounds heps (hx.trans_lt hρD) v).2
      rw [standardCapMetric_eq_metric, SmoothRiemannianMetric.restrictOpen_inner] at hb
      have hn := metric_inner_self_nonneg metric x.val v
      nlinarith)
  have hqp : q = p := Subtype.ext hq
  subst q
  intro x hx
  have hb := hinner (mem_image_of_mem id hx)
  change riemannianEDistOf w.windowMetric p x < ENNReal.ofReal (2*(ρ/32)) at hb
  exact hb.le.trans (ENNReal.ofReal_le_ofReal (by linarith))

end DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness
