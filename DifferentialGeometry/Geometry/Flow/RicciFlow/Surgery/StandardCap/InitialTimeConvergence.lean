import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.InitialTimeConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.InitialWindowBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Curvature.MovingShi

noncomputable section
open Set Filter Bundle Manifold
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Metric DifferentialGeometry.Geometry.Neck
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

theorem metric_cp_convergence_on_standard_cap_at_vanishing_age
    (D r R : ℝ) (hrR : r < R) (hRD : R ≤ D) (N : ℕ)
    (J : ℕ → RealTimeInterval) (age error : ℕ → ℝ)
    (hage : ∀ n, 0 ≤ age n) (hagelim : Tendsto age atTop (𝓝 0))
    (herror : ∀ n, 0 ≤ error n ∧ error n ≤ 1 / 2)
    (herrorlim : Tendsto error atTop (𝓝 0))
    (S : ∀ n, SolutionOn (I := ThreeModel) (M := standardCapWindow D) (J n))
    (hS : ∀ n, IsSolutionOn (S n))
    (hcarrier : ∀ n, Icc 0 (age n) ⊆ (J n).carrier)
    (hregular : ∀ n, Ioo 0 (age n) ⊆ (J n).regular)
    (hgram : ∀ n (p : standardCapWindow D) (i j : Fin (Module.finrank ℝ ThreeSpace)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ, ℝ) ∞
        (fun q : ℝ × standardCapWindow D => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix
          ((S n).base.metric q.1) p q.2 i j)
        (Icc 0 (age n) ×ˢ (trivializationAt ThreeSpace (TangentSpace ThreeModel) p).baseSet))
    (hinitial : ∀ n j, j ≤ N → ∀ x : standardCapWindow D, ‖x.val‖ < R →
      metricDerivNorm j ((S n).base.metric 0) (metric.restrictOpen (standardCapWindow D))
        (metric.restrictOpen (standardCapWindow D)) x ≤ error n)
    (C : ℕ → ℝ)
    (hcurv : ∀ n j, j ≤ N → ∀ t ∈ Icc 0 (age n), ∀ x : standardCapWindow D,
      ‖x.val‖ < R → curvDerivNorm j ((S n).base.metric t) x ≤ C j) :
    MetricCPConvergenceOn {x : standardCapWindow D | ‖x.val‖ ≤ r} N
      (fun n => (S n).base.metric (age n))
      (metric.restrictOpen (standardCapWindow D))
      (metric.restrictOpen (standardCapWindow D)) := by
  let U : Set (standardCapWindow D) := {x | ‖x.val‖ < R}
  let V : Set (standardCapWindow D) := {x | ‖x.val‖ ≤ r}
  let gRef := metric.restrictOpen (standardCapWindow D)
  have hU : IsOpen U := isOpen_lt (continuous_norm.comp continuous_subtype_val) continuous_const
  have hVU : V ⊆ U := fun _ hx => hx.trans_lt hrR
  have hV : IsCompact V := by
    have hc : IsCompact {x : ThreeSpace | ‖x‖ ≤ r} := by
      simpa only [Metric.closedBall, dist_zero_right] using isCompact_closedBall (0 : ThreeSpace) r
    exact _root_.Topology.IsInducing.subtypeVal.isCompact_preimage' hc (by
      intro x hx
      refine ⟨⟨x, ?_⟩, rfl⟩
      change ‖x‖ < D + 1
      change ‖x‖ ≤ r at hx
      linarith)
  obtain ⟨K, hK, hRic⟩ := exists_movingShiBoundOn_constant_of_curvature_derivative_bounds
    (I := ThreeModel) (M := standardCapWindow D) N C
  apply metric_cp_convergence_on_at_vanishing_time_of_finite_ricci_bounds U hU gRef N
    (Λ := 2) (by norm_num) hK
    (fun _ => 1 / 2) (by intros; norm_num) J age hage hagelim hcarrier hregular S hS hgram
    ?_ ?_ (fun n => hRic (fun _ t => (S n).base.metric t) U 0 (age n)
      (fun j hj _ t ht x hx => hcurv n j hj t ht x hx)) hV hVU ?_
  · intro n
    refine ⟨by norm_num, ?_⟩
    intro x hx v
    have hb := inner_bounds_of_metricDerivNorm_le gRef ((S n).base.metric 0) x
      ((hinitial n 0 (Nat.zero_le N) x hx).trans (herror n).2) v
    have hn := metric_inner_self_nonneg gRef x v
    constructor
    · simpa only [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num,
        show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] using hb.1
    · linarith [hb.2]
  · intro n j hj hjN x hx
    have hb := covNorm_le_add j ((S n).base.metric 0) gRef gRef x
    have hz : metricCovDerivNorm j gRef gRef x = 0 := by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
      exact covNorm_self_succ gRef k x
    rw [hz, zero_add] at hb
    exact hb.trans ((hinitial n j hjN x hx).trans (herror n).2)
  · intro epsilon hepsilon
    obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp (herrorlim.eventually (Iio_mem_nhds hepsilon))
    refine ⟨n₀, fun n hn => ?_⟩
    exact (metricDerivNormSupOn_le_of_forall V N _ _ _ (error n) (herror n).1
      (fun j hj x hx => hinitial n j hj x (hVU hx))).trans_lt (hn₀ n hn)

universe u

private local instance : Fact (Module.finrank ℝ ThreeSpace = 3) := ⟨by simp⟩

theorem metric_cp_convergence_on_insertion_window_at_vanishing_age
    (D r R : ℝ) (hrR : r < R) (hRD : R ≤ D) (N : ℕ)
    (P : ℕ → Type u) [∀ n, TopologicalSpace (P n)] [∀ n, ChartedSpace ThreeSpace (P n)]
    [∀ n, IsManifold ThreeModel ∞ (P n)] [∀ n, T2Space (P n)]
    (g : ∀ n, SmoothRiemannianMetric ThreeModel (P n)) (x : ∀ n, P n)
    (delta : ℕ → ℝ) (order m : ℕ → ℕ)
    (datum : ∀ n, normalizedDatum (g n) (x n) (delta n) (order n))
    (A error : ℕ → ℝ) (hA : ∀ n, 0 < A n)
    (w : ∀ n, CanonicalStaticInsertionWitness (datum n) (A n) (hA n) D (m n) (error n))
    (hm : ∀ n, N ≤ m n) (herror : ∀ n, error n ≤ 1 / 2)
    (herrorlim : Tendsto error atTop (𝓝 0))
    (J : ℕ → RealTimeInterval) (age : ℕ → ℝ)
    (hage : ∀ n, 0 ≤ age n) (hagelim : Tendsto age atTop (𝓝 0))
    (S : ∀ n, SolutionOn (I := ThreeModel) (M := standardCapWindow D) (J n))
    (hS : ∀ n, IsSolutionOn (S n))
    (hcarrier : ∀ n, Icc 0 (age n) ⊆ (J n).carrier)
    (hregular : ∀ n, Ioo 0 (age n) ⊆ (J n).regular)
    (hzero : ∀ n, (S n).base.metric 0 = (w n).windowMetric)
    (hgram : ∀ n (p : standardCapWindow D) (i j : Fin (Module.finrank ℝ ThreeSpace)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ, ℝ) ∞
        (fun q : ℝ × standardCapWindow D => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix
          ((S n).base.metric q.1) p q.2 i j)
        (Icc 0 (age n) ×ˢ (trivializationAt ThreeSpace (TangentSpace ThreeModel) p).baseSet))
    (C : ℕ → ℝ)
    (hcurv : ∀ n j, j ≤ N → ∀ t ∈ Icc 0 (age n), ∀ p : standardCapWindow D,
      ‖p.val‖ < R → curvDerivNorm j ((S n).base.metric t) p ≤ C j) :
    MetricCPConvergenceOn {p : standardCapWindow D | ‖p.val‖ ≤ r} N
      (fun n => (S n).base.metric (age n))
      (metric.restrictOpen (standardCapWindow D))
      (metric.restrictOpen (standardCapWindow D)) := by
  apply metric_cp_convergence_on_standard_cap_at_vanishing_age D r R hrR hRD N J age error
    hage hagelim (fun n => ⟨(w n).accuracy_pos.le, herror n⟩) herrorlim
    S hS hcarrier hregular hgram ?_ C hcurv
  intro n j hj p hp
  rw [hzero n]
  have hclose := (w n).properties.window_close
  change metricDerivENormSupOn
    {p : standardCapWindow D | (riemannianEDistOf metric 0 p.val).toReal < D} (m n)
    (w n).windowMetric (metric.restrictOpen (standardCapWindow D))
    (metric.restrictOpen (standardCapWindow D)) < ENNReal.ofReal (error n) at hclose
  simp only [distance_zero] at hclose
  exact (DifferentialGeometry.Geometry.Metric.metricDerivNorm_lt_of_sup_lt
    _ _ _ _ _ hclose (hj.trans (hm n)) (hp.trans_le hRD)).le

end DifferentialGeometry.PDE.RicciFlow.StandardCap
