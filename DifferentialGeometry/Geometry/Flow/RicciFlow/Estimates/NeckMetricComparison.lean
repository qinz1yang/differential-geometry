import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.LocalPullback
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.ShrinkingCylinder
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.Solution.MetricDifference
import DifferentialGeometry.Geometry.Neck.NormalizedDatum
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Open

noncomputable section
open Set Manifold
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Metric
open scoped Manifold ContDiff
namespace DifferentialGeometry.PDE.RicciFlow

private abbrev Model := (𝓡 2).prod 𝓘(ℝ)
private abbrev Param := EuclideanSpace ℝ (Fin 2) × ℝ
private abbrev Space := EuclideanSpace ℝ (Fin 3)
private instance : NeZero (Module.finrank ℝ Param) := ⟨by simp [Param]⟩
private instance : Fact (Module.finrank ℝ Space = 3) := ⟨by simp⟩
private instance : Fact (Module.finrank ℝ Space = 2 + 1) := ⟨by simp⟩

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Space M]
  [IsManifold (𝓡 3) ∞ M] [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval} (S : SolutionOn (I := 𝓡 3) (M := M) D)
  {g : SmoothRiemannianMetric (𝓡 3) M} {δ : ℝ} {k : ℕ} {x₀ : M}
  (d : normalizedDatum g x₀ δ k)

def cylinderBufferSolution (δ : ℝ) :
    SolutionOn (I := Model) (M := bufferedCylinder δ)
      (RealTimeInterval.closedOpen (-2) 1 (by norm_num)) :=
  ({ base.metric := shrinkingCylinderMetric (E := Space) } :
    SolutionOn (I := Model) (M := Metric.sphere (0 : Space) 1 × ℝ)
      (RealTimeInterval.closedOpen (-2) 1 (by norm_num))).localPullback
        Subtype.val (DifferentialGeometry.isLocalDiffeomorph_subtype_val (bufferedCylinder δ))

theorem cylinderBufferSolution_isSolutionOn (δ : ℝ) : IsSolutionOn (cylinderBufferSolution δ) :=
  (shrinkingCylinderMetric_isSolutionOn_interval (E := Space) (by norm_num : (-2 : ℝ) < 1)
    le_rfl).localPullback Subtype.val _

theorem cylinderBufferSolution_metric_zero (δ : ℝ) :
    (cylinderBufferSolution δ).base.metric 0 = referenceMetric δ := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  change (localPullMetric (shrinkingCylinderMetric (E := Space) 0) Subtype.val
    (DifferentialGeometry.isLocalDiffeomorph_subtype_val (bufferedCylinder δ))).inner x v w = _
  rw [localPullMetric_inner,shrinkingCylinderMetric_zero,mfderiv_subtype_val_apply,
    mfderiv_subtype_val_apply]
  rfl

private theorem cylinder_metric_error_from_terminal
    {D : RealTimeInterval} (U : SolutionOn (I := Model) (M := bufferedCylinder δ) D)
    (hU : IsSolutionOn U) (hc : Icc (-1 : ℝ) 0 ⊆ D.carrier)
    (hr : Ioo (-1 : ℝ) 0 ⊆ D.regular) (q : ℕ) (x : bufferedCylinder δ) {L : ℝ}
    (hb : ∀ t ∈ Ioo (-1 : ℝ) 0,
      Real.sqrt (normSq0S (referenceMetric δ) x (q + 2)
        ((covDerivOfField (referenceMetric δ) (solutionRicField U t) q) x -
         (covDerivOfField (referenceMetric δ) (solutionRicField (cylinderBufferSolution δ) t) q) x)) ≤ L)
    {t : ℝ} (ht : t ∈ Ioc (-1 : ℝ) 0) :
    metricDerivNorm q (U.base.metric t) ((cylinderBufferSolution δ).base.metric t) (referenceMetric δ) x ≤
      metricDerivNorm q (U.base.metric 0) (referenceMetric δ) (referenceMetric δ) x + 2 * L * (-t) := by
  let : SigmaCompactSpace (bufferedCylinder δ) := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen Model (bufferedCylinder δ).isOpen)
  have hmc : Icc (-1 : ℝ) 0 ⊆ (RealTimeInterval.closedOpen (-2) 1 (by norm_num)).carrier := by
    intro t ht
    exact ⟨by linarith [ht.1],by linarith [ht.2]⟩
  have hmr : Ioo (-1 : ℝ) 0 ⊆ (RealTimeInterval.closedOpen (-2) 1 (by norm_num)).regular := by
    intro t ht
    exact ⟨by linarith [ht.1],by linarith [ht.2]⟩
  calc
    _ ≤ metricDerivNorm q (U.base.metric 0) ((cylinderBufferSolution δ).base.metric 0)
        (referenceMetric δ) x + 2 * L * (0 - t) := by
      exact metricDerivNorm_le_terminal_add_of_ricci_difference_bound
        (E := Param) (I := Model)
        (M := bufferedCylinder δ) (D := D)
        (D' := RealTimeInterval.closedOpen (-2) 1 (by norm_num))
        U (cylinderBufferSolution δ) hU (cylinderBufferSolution_isSolutionOn δ)
        (referenceMetric δ) q x (by norm_num : (-1 : ℝ) < 0) hc hmc hr hmr hb ht
    _ = _ := by rw [cylinderBufferSolution_metric_zero,zero_sub]

theorem fixed_neck_chart_metric_error_le_of_ricci_difference
    (hS : IsSolutionOn S)
    (Phi : bufferedCylinder δ → M) (hPhi : IsLocalDiffeomorph Model (𝓡 3) ∞ Phi)
    (hterminal : localPullMetric (S.base.metric 0) Phi hPhi = d.normalizedMetric)
    (hcarrier : Icc (-1 : ℝ) 0 ⊆ D.carrier)
    (hregular : Ioo (-1 : ℝ) 0 ⊆ D.regular)
    (q : ℕ) (hq : q ≤ k) (x : bufferedCylinder δ) (hx : x ∈ controlledCylinder δ)
    {L : ℝ}
    (hbound : ∀ v ∈ Ioo (-1 : ℝ) 0,
      Real.sqrt (normSq0S (referenceMetric δ) x (q + 2)
        ((covDerivOfField (referenceMetric δ) (solutionRicField (S.localPullback Phi hPhi) v) q) x -
         (covDerivOfField (referenceMetric δ) (solutionRicField (cylinderBufferSolution δ) v) q) x)) ≤ L)
    {v : ℝ} (hv : v ∈ Ioc (-1 : ℝ) 0) :
    metricDerivNorm q ((S.localPullback Phi hPhi).base.metric v)
      ((cylinderBufferSolution δ).base.metric v) (referenceMetric δ) x < δ + 2 * L * (-v) := by
  have hb := cylinder_metric_error_from_terminal (S.localPullback Phi hPhi)
    (hS.localPullback Phi hPhi) hcarrier hregular q x hbound hv
  have hzero : metricDerivNorm q ((S.localPullback Phi hPhi).base.metric 0)
      (referenceMetric δ) (referenceMetric δ) x < δ := by
    change metricDerivNorm q (localPullMetric (S.base.metric 0) Phi hPhi) _ _ _ < _
    rw [hterminal]
    exact metricDerivNorm_lt_of_sup_lt (controlledCylinder δ) k d.normalizedMetric
      (referenceMetric δ) (referenceMetric δ) d.error_lt hq hx
  exact hb.trans_lt (add_lt_add_left hzero (2 * L * (-v)))

end DifferentialGeometry.PDE.RicciFlow
