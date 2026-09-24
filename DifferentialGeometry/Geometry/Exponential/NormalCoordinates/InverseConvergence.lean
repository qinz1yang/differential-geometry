import DifferentialGeometry.Geometry.Exponential.NormalCoordinates.Convergence
import DifferentialGeometry.Analysis.Calculus.Inverse.MovingInverse

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace DifferentialGeometry.CheegerGromovCompactness
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]

theorem exists_metricSpray_diagonal_inverse_convergence
    {U : Set E} (hU : IsOpen U)
    {B : ℕ → E → E →L[ℝ] E →L[ℝ] ℝ} {BInf : E → E →L[ℝ] E →L[ℝ] ℝ}
    (hB : ∀ n, ContDiffOn ℝ ∞ (B n) U) (hBInf : ContDiffOn ℝ ∞ BInf U)
    (hco : ∀ n z, z ∈ U → IsCoercive (B n z))
    (hcoInf : ∀ z, z ∈ U → IsCoercive (BInf z))
    (hconv : MapCInfConvergenceOnCompacts U B BInf)
    {qStage qInf δStage δInf : ℝ} (hqInf : 0 < qInf) (hq : qInf < qStage)
    (hδStage : 0 < δStage) (hδInf : 0 < δInf)
    {Φ : ℕ → (E × E) → ℝ → E × E} {ΦInf : (E × E) → ℝ → E × E}
    {e : ℕ → OpenPartialHomeomorph (E × E) (E × E)}
    {eInf : OpenPartialHomeomorph (E × E) (E × E)}
    (hΦ : ∀ n z, z ∈ Metric.ball (0 : E × E) qInf →
      Φ n z 0 = z ∧ IsIntegralCurveOn (Φ n z)
        (fun _ => MetricKoszul.metricSpray (B n)) (Icc 0 1))
    (hΦInf : ∀ z, z ∈ Metric.ball (0 : E × E) qInf →
      ΦInf z 0 = z ∧ IsIntegralCurveOn (ΦInf z)
        (fun _ => MetricKoszul.metricSpray BInf) (Icc 0 1))
    (hstay : ∀ n z, z ∈ Metric.ball (0 : E × E) qInf →
      ∀ t ∈ Icc (0 : ℝ) 1, (Φ n z t).1 ∈ U)
    (hstayInf : ∀ z, z ∈ Metric.ball (0 : E × E) qInf →
      ∀ t ∈ Icc (0 : ℝ) 1, (ΦInf z t).1 ∈ U)
    (he : ∀ n, (e n : E × E → E × E) = fun z => (z.1, (Φ n z 1).1))
    (heInf : (eInf : E × E → E × E) = fun z => (z.1, (ΦInf z 1).1))
    (hsource : ∀ n, (e n).source = Metric.ball (0 : E × E) qStage)
    (hInfSource : eInf.source = Metric.ball (0 : E × E) qInf)
    (hInfZero : eInf 0 = 0)
    (hsmooth : ∀ n, ContDiffOn ℝ ∞ (e n : E × E → E × E) (e n).source)
    (hInfSmooth : ContDiffOn ℝ ∞ (eInf : E × E → E × E) eInf.source)
    (hInfSymmSmooth : ContDiffOn ℝ ∞ eInf.symm eInf.target)
    (htarget : ∀ n, Metric.closedBall (0 : E × E) δStage ⊆ (e n).target)
    (hInfTarget : Metric.closedBall (0 : E × E) δInf ⊆ eInf.target) :
    MapCInfConvergenceOnCompacts (Metric.ball (0 : E × E) qInf)
        (fun n => (e n : E × E → E × E)) eInf ∧
      ∃ δ : ℝ, 0 < δ ∧ δ < min δStage δInf ∧
        eInf.symm '' Metric.closedBall (0 : E × E) δ ⊆ Metric.ball 0 qInf ∧
        (∀ᶠ n in atTop, MapsTo (e n).symm (Metric.closedBall 0 δ) (Metric.ball 0 qInf)) ∧
        MapCInfConvergenceOnCompacts (Metric.ball (0 : E × E) δ)
          (fun n => ((e n).symm : E × E → E × E)) eInf.symm := by
  have hforwardFormula := normalDiag_end_convergence hU Metric.isOpen_ball hB hBInf hco hcoInf
    hconv hΦ hΦInf hstay hstayInf
  have hforward : MapCInfConvergenceOnCompacts (Metric.ball (0 : E × E) qInf)
      (fun n => (e n : E × E → E × E)) eInf :=
    hforwardFormula.congr Metric.isOpen_ball
      (fun n z _ => congrFun (he n) z) (fun z _ => congrFun heInf z)
  have hclosure : closure (Metric.ball (0 : E × E) qInf) ⊆ Metric.ball 0 qStage := by
    exact (closure_minimal Metric.ball_subset_closedBall Metric.isClosed_closedBall).trans
      (Metric.closedBall_subset_ball hq)
  have hstage : ∀ᶠ n in atTop,
      closure (Metric.ball (0 : E × E) qInf) ⊆ (e n).source := by
    exact Eventually.of_forall fun n => by rw [hsource n]; exact hclosure
  have hstageSmooth : ∀ n, ContDiffOn ℝ ∞ (e n : E × E → E × E)
      (Metric.ball (0 : E × E) qInf) := by
    intro n
    apply (hsmooth n).mono
    rw [hsource n]
    exact Metric.ball_subset_ball hq.le
  have htargetMin : ∀ n, Metric.closedBall (0 : E × E) (min δStage δInf) ⊆ (e n).target :=
    fun n => (Metric.closedBall_subset_closedBall (min_le_left _ _)).trans (htarget n)
  have hInfTargetMin : Metric.closedBall (0 : E × E) (min δStage δInf) ⊆ eInf.target :=
    (Metric.closedBall_subset_closedBall (min_le_right _ _)).trans hInfTarget
  have hzeroSource : (0 : E × E) ∈ eInf.source := by
    rw [hInfSource]
    simpa only [Metric.mem_ball, dist_self] using hqInf
  have hzero : eInf.symm 0 = 0 := by
    simpa only [hInfZero] using eInf.left_inv hzeroSource
  have hbase : eInf.symm 0 ∈ Metric.ball (0 : E × E) qInf := by
    rw [hzero]
    simpa only [Metric.mem_ball, dist_self] using hqInf
  refine ⟨hforward, ?_⟩
  exact Analysis.OpenPartialHomeomorph.exists_symm_convergenceOn_ball Metric.isOpen_ball
    hforward hstage hstageSmooth (lt_min hδStage hδInf) htargetMin hInfTargetMin
    (hInfSmooth.mono interior_subset)
    (hInfSymmSmooth.mono (Metric.ball_subset_closedBall.trans hInfTargetMin)) hbase

end DifferentialGeometry.CheegerGromovCompactness

end
