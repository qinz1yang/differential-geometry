import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Norm.TensorReference
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.NeckCylindricalChartBridge
import DifferentialGeometry.Geometry.Metric.Convergence.Naturality.CrossTensorPullback
import DifferentialGeometry.Geometry.Metric.Convergence.Naturality.OpenTensorJets
import DifferentialGeometry.Geometry.Metric.PullbackScaling

noncomputable section

open Set Filter Manifold
open DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open scoped Manifold ContDiff Topology BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] [T2Space M] [SigmaCompactSpace M]

private local instance neckSigmaCompact (δ : ℝ) : SigmaCompactSpace (neckBuffer δ) :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen NeckCylinderModel
      (neckBuffer δ).isOpen)

omit [T2Space M] [SigmaCompactSpace M] in
private theorem NormalizedNeck.exists_open_jet_bound
    {h : SmoothRiemannianMetric ThreeModel M} {δ : ℝ} {k : ℕ}
    (N : NormalizedNeck h δ k) (hδ : δ < 1 / 4) :
    ∃ U : Set (neckBuffer δ), IsOpen U ∧ neckClosedTest δ ⊆ U ∧
      ∀ x ∈ U, ∀ j ≤ k, metricDerivNorm j N.normalizedMetric
        (roundCylinderMetric.restrictOpen (neckBuffer δ))
        (roundCylinderMetric.restrictOpen (neckBuffer δ)) x ≤ 1 / 4 := by
  let gC := roundCylinderMetric.restrictOpen (neckBuffer δ)
  let U : Set (neckBuffer δ) := ⋂ j : Fin (k + 1),
    {x | metricDerivNorm j N.normalizedMetric gC gC x < 1 / 4}
  have hU : IsOpen U := isOpen_iInter_of_finite fun j =>
    isOpen_lt (metricDerivNorm_cont j N.normalizedMetric gC gC) continuous_const
  refine ⟨U, hU, ?_, ?_⟩
  · intro x hx
    apply mem_iInter.mpr
    intro j
    exact ((derivNorm_le_sup (isCompact_neckClosedTest δ) (Nat.le_of_lt_succ j.2)
      N.normalizedMetric gC gC hx).trans_lt N.closeness).trans hδ
  · intro x hx j hj
    exact (mem_iInter.mp hx ⟨j, Nat.lt_succ_of_le hj⟩).le

theorem exists_normalizedNeck_tensor_pullback_bound
    {δ : ℝ} (hδ : δ < 1 / 4) (k : ℕ) {qmin qmax : ℝ} (hqmin : 0 < qmin) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (h : SmoothRiemannianMetric ThreeModel M),
      ∀ (N : NormalizedNeck h δ k), qmin ≤ N.scale → N.scale ≤ qmax →
      ∀ A : Tensor0SField (I := ThreeModel) (M := M) ∞ 2,
      ∀ r ≤ k, ∀ x ∈ neckClosedTest δ,
        tensor02CovDerivNormWith r
          (pullbackTensor02FieldCross N.cylindricalChart.chart
            (restrictOpen0S 2 (V := N.cylindricalChart.target) A))
          (roundCylinderMetric.restrictOpen (neckBuffer δ))
          (roundCylinderMetric.restrictOpen (neckBuffer δ)) x ≤
        D * ∑ j ∈ Finset.range (k + 1), tensor02CovDerivNormWith j A h h (N.chart x) := by
  obtain ⟨C, B, hC, hB, hcontrol⟩ :=
    exists_uniform_reference_bounds_of_scaled_metric_jets (I := NeckCylinderModel)
      (M := neckBuffer δ) (qmax := qmax) k hqmin
  obtain ⟨D, hD, hcompare⟩ :=
    exists_uniform_tensor02_covariant_norm_reference_bound (I := NeckCylinderModel)
      (M := neckBuffer δ) k hC hB
  refine ⟨D, hD, ?_⟩
  intro h N hlo hhi A r hr x hx
  obtain ⟨U, hU, hKU, hjets⟩ := N.exists_open_jet_bound hδ
  let V := N.cylindricalChart.target
  let Φ : neckBuffer δ ≃ₘ⟮NeckCylinderModel, ThreeModel⟯ V := N.cylindricalChart.chart
  let gP := Diffeomorph.pullbackMetricCross (h.restrictOpen V) Φ
  let gC := roundCylinderMetric.restrictOpen (neckBuffer δ)
  have heq : scaleMetric N.scale N.scale_pos gP = N.normalizedMetric := by
    rw [← Diffeomorph.pullbackMetricCross_scaleMetric]
    exact N.cylindricalChart_pullbackMetricCross
  have hscaled : ∀ y ∈ U, ∀ j ≤ k,
      metricDerivNorm j (scaleMetric N.scale N.scale_pos gP) gC gC y ≤ 1 / 4 := by
    rw [heq]
    exact hjets
  obtain ⟨hequiv, hjet⟩ := hcontrol U hU gP gC N.scale N.scale_pos hlo hhi hscaled
  let Ap := pullbackTensor02FieldCross Φ (restrictOpen0S 2 (V := V) A)
  have hbound := hcompare U hU gP gC hequiv hjet Ap r hr x (hKU hx)
  have hnat (j : ℕ) : tensor02CovDerivNormWith j Ap gP gP x =
      tensor02CovDerivNormWith j A h h (N.chart x) := by
    let _ : SigmaCompactSpace V := isSigmaCompact_iff_sigmaCompactSpace.mp
      (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel V.isOpen)
    have hpull := tensor02CovDerivNormWith_pullbackTensor02FieldCross
      (h.restrictOpen V) (h.restrictOpen V) Φ (restrictOpen0S 2 (V := V) A) j x
    have hrest := tensor02CovDerivNormWith_restrictOpen0S V h h A j (Φ x)
    exact hpull.trans (hrest.trans (congrArg (fun y => tensor02CovDerivNormWith j A h h y)
      (N.cylindricalChart_chart_apply x)))
  exact hbound.trans_eq (congrArg (fun a => D * a)
    (Finset.sum_congr rfl fun j _ => hnat j))

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology


namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck

universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] [T2Space M] [SigmaCompactSpace M]
  {g : SmoothRiemannianMetric ThreeModel M}

def tensorPullback
    {δ : ℝ} {k : ℕ}
    (N : NormalizedNeck g δ k)
    (A : Tensor0SField (I := ThreeModel) (M := M) ∞ 2) :
    Tensor0SField (I := NeckCylinderModel) (M := neckBuffer δ) ∞ 2 :=
  let V := N.cylindricalChart.target
  let Φ : neckBuffer δ ≃ₘ⟮NeckCylinderModel, ThreeModel⟯ V := N.cylindricalChart.chart
  pullbackTensor02FieldCross Φ (restrictOpen0S 2 (V := V) A)

omit [T2Space M] [SigmaCompactSpace M] in
theorem tensorPullback_apply
    {δ : ℝ} {k : ℕ}
    (N : NormalizedNeck g δ k)
    (A : Tensor0SField (I := ThreeModel) (M := M) ∞ 2)
    (z : neckBuffer δ) (w : Fin 2 → TangentSpace NeckCylinderModel z) :
    N.tensorPullback A z w =
      A (N.chart z) (fun j => mfderiv NeckCylinderModel ThreeModel N.chart z (w j)) := by
  let V := N.cylindricalChart.target
  let Φ : neckBuffer δ ≃ₘ⟮NeckCylinderModel, ThreeModel⟯ V := N.cylindricalChart.chart
  have hmap : (fun y : neckBuffer δ => (Φ y).1) = N.chart :=
    funext N.cylindricalChart_chart_apply
  have hd : mfderiv NeckCylinderModel ThreeModel Φ z =
      mfderiv NeckCylinderModel ThreeModel N.chart z := by
    rw [← DifferentialGeometry.mfderiv_subtypeVal_comp, hmap]
  have hp := pullbackTensor02FieldCross_apply Φ (restrictOpen0S 2 (V := V) A) z w
  have he : A (Φ z).1 (fun j => mfderiv NeckCylinderModel ThreeModel Φ z (w j)) =
      A (N.chart z) (fun j => mfderiv NeckCylinderModel ThreeModel N.chart z (w j)) := by
    have hslots := congrArg (fun d : (EuclideanSpace ℝ (Fin 2) × ℝ) →L[ℝ] ThreeSpace =>
      A (Φ z).1 (fun j => d (w j))) hd
    exact hslots.trans (congrArg (fun y : M =>
      A y (fun j => mfderiv NeckCylinderModel ThreeModel N.chart z (w j)))
        (N.cylindricalChart_chart_apply z))
  exact hp.trans he



omit [T2Space M] [SigmaCompactSpace M] in
theorem tensorPullback_sub {δ : ℝ} {k : ℕ} (N : NormalizedNeck g δ k)
    (A B : Tensor0SField (I := ThreeModel) (M := M) ∞ 2) :
    N.tensorPullback (A - B) = N.tensorPullback A - N.tensorPullback B := by
  ext z w
  change N.tensorPullback (A - B) z w = N.tensorPullback A z w - N.tensorPullback B z w
  rw [N.tensorPullback_apply, N.tensorPullback_apply, N.tensorPullback_apply]
  rfl

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck
