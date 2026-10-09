import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HamiltonIveyPinching
import DifferentialGeometry.Geometry.Curvature.OperatorScaling
import DifferentialGeometry.Geometry.Curvature.DimensionThree.SectionalScalarBounds
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciLowerBound
import DifferentialGeometry.Geometry.Curvature.Bounds.RicciOperatorNorm

set_option autoImplicit false
noncomputable section
open Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff BigOperators
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u

private theorem abs_ricciTensor_le_nine_mul_sqrt_normSq
    {X : Type u} [TopologicalSpace X] [ChartedSpace ThreeSpace X]
    [IsManifold ThreeModel ∞ X] [T2Space X]
    (g : SmoothRiemannianMetric ThreeModel X) (x : X)
    (ξ : TangentSpace ThreeModel x) :
    |ricciTensor g x ξ ξ| ≤
      9 * Real.sqrt (normSq0S g x 4 (metricRm04At g x)) * g.inner x ξ ξ := by
  let n := Module.finrank ℝ (TangentSpace ThreeModel x)
  obtain ⟨basis, hON⟩ :=
    DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis g x
  have hcomp : ∀ i j : Fin n,
      |metricRicciAt g x (vec2 (basis i) (basis j))| ≤
        (n : ℝ) * Real.sqrt (normSq0S g x 4 (metricRm04At g x)) := by
    intro i j
    simpa only [n, Fintype.card_fin] using metricRicciComp_le g basis hON i j
  have hunit : ∀ v : TangentSpace ThreeModel x, g.inner x v v = 1 →
      |metricRicciAt g x (vec2 v v)| ≤
        (n : ℝ) ^ 2 * Real.sqrt (normSq0S g x 4 (metricRm04At g x)) := by
    intro v hv
    have h := ricci_unitSphere_le_of_componentBound g (metricRicciAt g x) basis hON
      (R := (n : ℝ) * Real.sqrt (normSq0S g x 4 (metricRm04At g x)))
      (mul_nonneg (Nat.cast_nonneg n) (Real.sqrt_nonneg _)) hcomp v hv
    nlinarith
  have hray := tensor02_quadForm_abs_le_of_unit_bound g (metricRicciAt g x) hunit ξ
  rw [metricRicciAt_apply_eq_ricciTensor] at hray
  have hdim : n = 3 := by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3
    simp
  simpa only [hdim, Nat.cast_ofNat, show (3 : ℝ) ^ 2 = 9 by norm_num] using hray

/-- A uniform bound from normalized Hamilton–Ivey pinching on the same metric. -/
theorem exists_uniform_curvature_bound_of_scaled_fixedHamiltonIveyRegion
    (K : ℝ) (hK : 4 ≤ K) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (X : Type u) [TopologicalSpace X] [ChartedSpace ThreeSpace X]
        [IsManifold ThreeModel ∞ X] [T2Space X]
        (g : SmoothRiemannianMetric ThreeModel X) (x : X) (a Q : ℝ),
        0 < Q → 1 ≤ Q * a →
        InFixedHamiltonIveyRegion g a x → metricScalarAt g x ≤ 8 * K * Q →
        normSq0S g x 4 (metricRm04At g x) ≤ (C * Q) ^ 2 ∧
          ∀ ξ : TangentSpace ThreeModel x,
            ricciTensor g x ξ ξ ≤ (C * Q) * g.inner x ξ ξ := by
  obtain ⟨Phi, hPhi, hbound⟩ :=
    exists_admissiblePinchingFunction_neg_le_of_fixedHamiltonIveyRegion
      (a₀ := 1) (by norm_num)
  let k := Phi (8 * K)
  have hk : 0 < k := hPhi.pos _
  have hKpos : 0 < K := lt_of_lt_of_le (by norm_num) hK
  let cRm := 2 * Real.sqrt 3 * (4 * K + 2 * k)
  have hcRm : 0 < cRm := by dsimp [cRm]; positivity
  have hc : cRm ≤ max 1 (9 * cRm) :=
    (show cRm ≤ 9 * cRm by linarith).trans (le_max_right _ _)
  refine ⟨max 1 (9 * cRm), le_max_left _ _, ?_⟩
  intro X _ _ _ _ g x a Q hQ htime hfixed hR
  let gQ := scaleMetric Q hQ g
  have hscalarQ : metricScalarAt gQ x = metricScalarAt g x / Q := by
    dsimp only [gQ]
    rw [metricScalarAt_scaleMetric]
    ring
  have hleastQ :
      leastCurvatureOperatorEigenvalueAt gQ x (metricAlgebraicCurvatureTensorAt gQ x) =
        leastCurvatureOperatorEigenvalueAt g x (metricAlgebraicCurvatureTensorAt g x) / Q :=
    DifferentialGeometry.Geometry.Curvature.leastCurvatureOperatorEigenvalueAt_scaleMetric
      g Q hQ x
  have hmem := (mem_fixedHamiltonIveyRegion_scale_iff hQ a (metricScalarAt g x)
    (2 * leastCurvatureOperatorEigenvalueAt g x (metricAlgebraicCurvatureTensorAt g x))).mpr
    ((inFixedHamiltonIveyRegion_iff_mem_fixedHamiltonIveyRegion g a x).mp hfixed)
  have hmemQ :
      (metricScalarAt gQ x,
        2 * leastCurvatureOperatorEigenvalueAt gQ x (metricAlgebraicCurvatureTensorAt gQ x)) ∈
        fixedHamiltonIveyRegion (Q * a) := by
    rw [hscalarQ, hleastQ]
    simpa only [mul_div_assoc] using hmem
  have hRQ : metricScalarAt gQ x ≤ 8 * K := by
    rw [hscalarQ]
    exact (div_le_iff₀ hQ).mpr hR
  have hneg := (hbound (Q * a) htime _ _ hmemQ).trans (hPhi.mono hRQ)
  have hoperatorQ :
      curvatureOperatorLowerBoundAt gQ x (metricAlgebraicCurvatureTensorAt gQ x) k := by
    obtain ⟨basis, horth⟩ := exists_orthonormalBasisAt gQ x (by
      change Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3
      simp)
    apply (curvatureOperatorLowerBoundAt_iff_neg_leastCurvatureOperatorEigenvalueAt_le
      basis horth).mpr
    change -(2 * leastCurvatureOperatorEigenvalueAt gQ x
      (metricAlgebraicCurvatureTensorAt gQ x)) ≤ k at hneg
    linarith
  have hoperator :
      curvatureOperatorLowerBoundAt g x (metricAlgebraicCurvatureTensorAt g x) (Q * k) :=
    (curvatureOperatorLowerBoundAt_scaleMetric_iff g Q hQ x k).mp hoperatorQ
  have hsectional := sectionalBoundedBelowAt_of_curvatureOperatorLowerBoundAt g x hoperator
  have hnorm := sqrt_normSq0S_le_of_sectional_lower_scalar_upper g x
    (by change Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3; simp)
    (mul_nonneg hQ.le hk.le) hsectional hR
  have hB : 0 ≤ 8 * K * Q := by positivity
  have hnorm' : Real.sqrt (normSq0S g x 4 (metricRm04At g x)) ≤ cRm * Q := by
    calc
      _ ≤ 2 * Real.sqrt 3 * (max (8 * K * Q) 0 / 2 + 2 * (Q * k)) := hnorm
      _ = cRm * Q := by rw [max_eq_left hB]; dsimp only [cRm]; ring
  have hnormC : Real.sqrt (normSq0S g x 4 (metricRm04At g x)) ≤
      max 1 (9 * cRm) * Q :=
    hnorm'.trans (mul_le_mul_of_nonneg_right hc hQ.le)
  refine ⟨(Real.sqrt_le_iff.mp hnormC).2, ?_⟩
  intro ξ
  have hinner := DifferentialGeometry.metric_inner_self_nonneg g x ξ
  calc
    ricciTensor g x ξ ξ ≤ |ricciTensor g x ξ ξ| := le_abs_self _
    _ ≤ 9 * Real.sqrt (normSq0S g x 4 (metricRm04At g x)) * g.inner x ξ ξ :=
      abs_ricciTensor_le_nine_mul_sqrt_normSq g x ξ
    _ ≤ 9 * (cRm * Q) * g.inner x ξ ξ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hnorm' (by norm_num)) hinner
    _ = ((9 * cRm) * Q) * g.inner x ξ ξ := by ring
    _ ≤ (max 1 (9 * cRm) * Q) * g.inner x ξ ξ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right _ _) hQ.le) hinner

/-- Actual stage and incoming terminal metrics, including closed birth and horizon slices. -/
theorem exists_uniform_curvature_bound_on_history_slices
    (K : ℝ) (hK : 4 ≤ K) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (H : ObservedHistory.{u}) (parameters : CutoffParameters)
        (records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H i parameters)
        (a₀ : ℝ), 0 < a₀ →
        (∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x) →
        (∀ x, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) x) →
        (∀ (j : Fin (H.eventCount + 1)) (s : ℝ), s ∈ H.stageDomain j →
          ∀ (x : (H.stage j).Carrier) (Q : ℝ),
            0 < Q → 1 ≤ Q * (a₀ + s) →
            metricScalarAt (H.stageMetric j s) x ≤ 8 * K * Q →
            normSq0S (H.stageMetric j s) x 4 (metricRm04At (H.stageMetric j s) x) ≤
                (C * Q) ^ 2 ∧
              ∀ ξ : TangentSpace ThreeModel x,
                ricciTensor (H.stageMetric j s) x ξ ξ ≤
                  (C * Q) * (H.stageMetric j s).inner x ξ ξ) ∧
        (∀ (i : Fin H.eventCount)
          (x : (H.event i).incoming.terminalRegularOpen) (Q : ℝ),
          0 < Q → 1 ≤ Q * (a₀ + H.time i.succ) →
          metricScalarAt (H.event i).terminal.metric x ≤ 8 * K * Q →
          normSq0S (H.event i).terminal.metric x 4
              (metricRm04At (H.event i).terminal.metric x) ≤ (C * Q) ^ 2 ∧
            ∀ ξ : TangentSpace ThreeModel x,
              ricciTensor (H.event i).terminal.metric x ξ ξ ≤
                (C * Q) * (H.event i).terminal.metric.inner x ξ ξ) := by
  obtain ⟨C, hC, hpoint⟩ :=
    exists_uniform_curvature_bound_of_scaled_fixedHamiltonIveyRegion.{u} K hK
  refine ⟨C, hC, ?_⟩
  intro H parameters records a₀ ha₀ hfixed hscalar
  have hhistory := H.fixedHamiltonIveyRegion_and_scalar_lower records ha₀ hfixed hscalar
  constructor
  · intro j s hs x Q hQ htime hR
    exact hpoint _ (H.stageMetric j s) x (a₀ + s) Q hQ htime
      (hhistory.1 j s hs x).1 hR
  · intro i x Q hQ htime hR
    exact hpoint _ (H.event i).terminal.metric x (a₀ + H.time i.succ) Q hQ htime
      (hhistory.2 i x).1 hR

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
