import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.Scalar
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Limit.Metric.ScalarConvergence
import Mathlib.Topology.Sequences
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StaticCap
import DifferentialGeometry.Geometry.Metric.Convergence.Curvature.ScalarPerturbation
import DifferentialGeometry.Geometry.Curvature.RicciRestriction
import DifferentialGeometry.Geometry.Metric.DerivativeENorm
import DifferentialGeometry.Topology.SigmaCompactOpen

set_option autoImplicit false
noncomputable section
open Set Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Metric DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff Topology ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
private local instance (V : TopologicalSpace.Opens ThreeSpace) : SigmaCompactSpace V :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel V.isOpen)

theorem exists_uniform_window_scalar_bounds_of_metric_close
    (D R : ℝ) (hRD : R < D + 1) :
    ∃ ε C : ℝ, 0 < ε ∧ 1 ≤ C ∧
      ∀ g : SmoothRiemannianMetric ThreeModel (standardCapWindow D),
        metricDerivENormSupOn {x : standardCapWindow D | ‖x.val‖ ≤ R} 2
          g (metric.restrictOpen (standardCapWindow D))
          (metric.restrictOpen (standardCapWindow D)) < ENNReal.ofReal ε →
        ∀ x : standardCapWindow D, ‖x.val‖ ≤ R →
          1/2 < metricScalarAt g x ∧ metricScalarAt g x < C := by
  let K : Set (standardCapWindow D) := {x | ‖x.val‖ ≤ R}
  let gRef := metric.restrictOpen (standardCapWindow D)
  have hK : IsCompact K := by
    have hc : IsCompact {x : ThreeSpace | ‖x‖ ≤ R} := by
      simpa only [Metric.closedBall,dist_zero_right] using isCompact_closedBall (0 : ThreeSpace) R
    exact _root_.Topology.IsInducing.subtypeVal.isCompact_preimage' hc (by
      intro x hx
      refine ⟨⟨x,?_⟩,rfl⟩
      change ‖x‖ < D+1
      change ‖x‖ ≤ R at hx
      linarith)
  obtain ⟨B,hB⟩ := hK.bddAbove_image (metricScalar_smooth gRef).continuous.continuousOn
  obtain ⟨ε,hε,hclose⟩ := exists_abs_metricScalarAt_sub_lt gRef hK (c := 1/2) (by norm_num)
  refine ⟨ε,max 1 (B+1),hε,le_max_left _ _,?_⟩
  intro g hg x hx
  have herr := hclose g (fun y hy j hj =>
    (metricDerivNorm_lt_of_sup_lt K 2 g gRef gRef hg hj hy).le) x hx
  have hsc : metricScalarAt gRef x = metricScalarAt metric x.val :=
    metricScalarAt_restrictOpen metric (standardCapWindow D) x
  have hlower : 1 ≤ metricScalarAt gRef x := hsc.symm ▸ one_le_metricScalarAt x.val
  have hupper : metricScalarAt gRef x ≤ B := hB (mem_image_of_mem _ hx)
  constructor
  · linarith [(abs_lt.mp herr).1]
  · have hh : metricScalarAt g x < B+1 := by linarith [(abs_lt.mp herr).2]
    exact hh.trans_le (le_max_right _ _)

open Filter in
theorem exists_subseq_marked_scalar_limit_of_metric_cp_convergence
    (D r : ℝ) (htr : transitionEnd ≤ r) (hrD : r < D + 1)
    (N : ℕ) (hN : 2 ≤ N)
    (gSeq : ℕ → SmoothRiemannianMetric ThreeModel (standardCapWindow D))
    (hconv : MetricCPConvergenceOn {x : standardCapWindow D | ‖x.val‖ ≤ r} N gSeq
      (metric.restrictOpen (standardCapWindow D))
      (metric.restrictOpen (standardCapWindow D)))
    (u : ℕ → standardCapWindow D) (hu : ∀ n, ‖(u n).val‖ ≤ transitionEnd) :
    ∃ (φ : ℕ → ℕ) (uLim : standardCapWindow D), StrictMono φ ∧
      ‖uLim.val‖ ≤ transitionEnd ∧ Tendsto (u ∘ φ) atTop (𝓝 uLim) ∧
      Tendsto (fun n => metricScalarAt (gSeq (φ n)) (u (φ n))) atTop
        (𝓝 (metricScalarAt (metric.restrictOpen (standardCapWindow D)) uLim)) ∧
      1 ≤ metricScalarAt (metric.restrictOpen (standardCapWindow D)) uLim ∧
      ∀ᶠ n in atTop, 1 / 2 < metricScalarAt (gSeq n) (u n) := by
  let K : Set (standardCapWindow D) := {x | ‖x.val‖ ≤ r}
  let A : Set (standardCapWindow D) := {x | ‖x.val‖ ≤ transitionEnd}
  let gRef := metric.restrictOpen (standardCapWindow D)
  have hcompact (s : ℝ) (hs : s < D + 1) :
      IsCompact {x : standardCapWindow D | ‖x.val‖ ≤ s} := by
    have hc : IsCompact {x : ThreeSpace | ‖x‖ ≤ s} := by
      simpa only [Metric.closedBall, dist_zero_right] using
        isCompact_closedBall (0 : ThreeSpace) s
    exact _root_.Topology.IsInducing.subtypeVal.isCompact_preimage' hc (by
      intro x hx
      refine ⟨⟨x, ?_⟩, rfl⟩
      exact hx.trans_lt hs)
  have hK : IsCompact K := hcompact r hrD
  have hA : IsCompact A := hcompact transitionEnd (htr.trans_lt hrD)
  have htwo : MetricCPConvergenceOn K 2 gSeq gRef gRef := by
    intro ε hε
    obtain ⟨n₀, hn₀⟩ := hconv (ε / 2) (half_pos hε)
    refine ⟨n₀, fun n hn => ?_⟩
    apply lt_of_le_of_lt (metricDerivNormSupOn_le_of_forall K 2 (gSeq n) gRef gRef
      (ε / 2) (half_pos hε).le ?_) (half_lt_self hε)
    intro j hj x hx
    exact (derivNorm_le_sup hK (hj.trans hN) (gSeq n) gRef gRef hx).trans (hn₀ n hn).le
  have hdiff := htwo.tendsto_metricScalarAt_sub_of_eventually_mem hK
    (Eventually.of_forall fun n => (hu n).trans htr)
  obtain ⟨uLim, huLim, φ, hφ, hlim⟩ := hA.tendsto_subseq hu
  have hscalar : Tendsto (fun n => metricScalarAt (gSeq (φ n)) (u (φ n))) atTop
      (𝓝 (metricScalarAt gRef uLim)) := by
    have href := (metricScalar_smooth gRef).continuous.continuousAt.tendsto.comp hlim
    simpa only [Function.comp_def, sub_add_cancel, zero_add] using
      (hdiff.comp hφ.tendsto_atTop).add href
  have hlower (x : standardCapWindow D) : 1 ≤ metricScalarAt gRef x := by
    rw [metricScalarAt_restrictOpen]
    exact one_le_metricScalarAt x.val
  refine ⟨φ, uLim, hφ, huLim, hlim, hscalar, hlower uLim, ?_⟩
  filter_upwards [hdiff.eventually (Ioi_mem_nhds (show -(1 / 2 : ℝ) < 0 by norm_num))]
    with n hn
  have hb := hlower (u n)
  linarith

open Filter in
theorem eventually_half_lt_metricScalarAt_of_metric_cp_convergence
    {D r : ℝ} (hrD : r < D + 1) {N : ℕ} (hN : 2 ≤ N)
    (g : ℕ → SmoothRiemannianMetric ThreeModel (standardCapWindow D))
    (hconv : MetricCPConvergenceOn {x : standardCapWindow D | ‖x.val‖ ≤ r} N g
      (metric.restrictOpen (standardCapWindow D))
      (metric.restrictOpen (standardCapWindow D))) :
    ∀ᶠ n in atTop, ∀ x : standardCapWindow D, ‖x.val‖ ≤ r →
      1 / 2 < metricScalarAt (g n) x := by
  let K : Set (standardCapWindow D) := {x | ‖x.val‖ ≤ r}
  let gRef := metric.restrictOpen (standardCapWindow D)
  have hK : IsCompact K := by
    have hc : IsCompact {x : ThreeSpace | ‖x‖ ≤ r} := by
      simpa only [Metric.closedBall, dist_zero_right] using isCompact_closedBall (0 : ThreeSpace) r
    exact _root_.Topology.IsInducing.subtypeVal.isCompact_preimage' hc (by
      intro x hx
      exact ⟨⟨x, hx.trans_lt hrD⟩, rfl⟩)
  obtain ⟨ε, hε, hclose⟩ := exists_abs_metricScalarAt_sub_lt gRef hK
    (c := 1 / 2) (by norm_num)
  obtain ⟨n₀, hn₀⟩ := hconv ε hε
  filter_upwards [eventually_ge_atTop n₀] with n hn
  intro x hx
  have herr := hclose (g n) (fun y hy j hj =>
    (derivNorm_le_sup hK (hj.trans hN) (g n) gRef gRef hy).trans (hn₀ n hn).le) x hx
  have hlower : 1 ≤ metricScalarAt gRef x := by
    rw [metricScalarAt_restrictOpen]
    exact one_le_metricScalarAt x.val
  linarith [(abs_lt.mp herr).1]


open Filter in
theorem exists_uniform_scalar_bound_on_core_of_metric_cp_convergence :
    ∃ C : ℝ, 0 < C ∧ ∀ D : ℝ, transitionEnd < D + 1 →
      ∀ N : ℕ, 2 ≤ N →
      ∀ g : ℕ → SmoothRiemannianMetric ThreeModel (standardCapWindow D),
      MetricCPConvergenceOn {x : standardCapWindow D | ‖x.val‖ ≤ transitionEnd} N g
        (metric.restrictOpen (standardCapWindow D)) (metric.restrictOpen (standardCapWindow D)) →
      ∀ᶠ n in atTop, ∀ x : standardCapWindow D, ‖x.val‖ ≤ transitionEnd →
        metricScalarAt (g n) x ≤ C := by
  have hK : IsCompact {x : ThreeSpace | ‖x‖ ≤ transitionEnd} := by
    simpa only [Metric.closedBall, dist_zero_right] using
      isCompact_closedBall (0 : ThreeSpace) transitionEnd
  obtain ⟨B, hB⟩ := hK.bddAbove_image (metricScalar_smooth metric).continuous.continuousOn
  let C := max B 0 + 1
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro D hD N hN g hconv
  let K : Set (standardCapWindow D) := {x | ‖x.val‖ ≤ transitionEnd}
  let gRef := metric.restrictOpen (standardCapWindow D)
  have hcompact : IsCompact K :=
    _root_.Topology.IsInducing.subtypeVal.isCompact_preimage' hK (by
      intro x hx
      exact ⟨⟨x, hx.trans_lt hD⟩, rfl⟩)
  have htwo : MetricCPConvergenceOn K 2 g gRef gRef := by
    intro eps heps
    obtain ⟨N0, hN0⟩ := hconv (eps / 2) (half_pos heps)
    refine ⟨N0, fun n hn => lt_of_le_of_lt
      (metricDerivNormSupOn_le_of_forall K 2 _ _ _ (eps / 2) (half_pos heps).le ?_)
      (half_lt_self heps)⟩
    intro j hj x hx
    exact (derivNorm_le_sup hcompact (hj.trans hN) _ _ _ hx).trans (hN0 n hn).le
  have hu := htwo.tendstoUniformlyOn_metricScalarAt hcompact
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hu (1 : ℝ) zero_lt_one] with n hn
  intro x hx
  have he := hn x hx
  rw [Real.dist_eq, metricScalarAt_restrictOpen] at he
  have hb : metricScalarAt metric x.val ≤ B := hB ⟨x.val, hx, rfl⟩
  have hc : B ≤ C - 1 := by dsimp only [C]; linarith [le_max_left B 0]
  have herr := (abs_lt.mp he).1
  linarith


end DifferentialGeometry.PDE.RicciFlow.StandardCap
