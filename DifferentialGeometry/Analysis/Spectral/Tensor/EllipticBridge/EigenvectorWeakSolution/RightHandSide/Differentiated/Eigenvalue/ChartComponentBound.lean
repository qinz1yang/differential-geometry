import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.RightHandSide.Differentiated.Energy.UniformBound
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.IteratedRegularity.HigherOrderSobolevBounds
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Geometry.Curvature

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2

open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))


omit [CompleteSpace E] in
private lemma iteratedPartial_wkpNorm_le_of_chart_perK
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (eigenvectorConstant : ℕ → ℝ) (eigenvectorExponent : ℕ → ℕ)
    (eigenvector_bound : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s) (K' : ℕ),
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K' 2
          (eigenvectorChartComponentFun (I := I) (M := M)
            g r s i α P₀)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (eigenvectorConstant K' * (i.fst.val)⁻¹ ^ (eigenvectorExponent K')) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖) :
    ∀ (i : TensorEigenIdx (I := I) (M := M) g r s) (j : ℕ),
      j ≤ m + 1 →
      ∀ (idx : Fin j → Fin (Module.finrank ℝ E)) (K' : ℕ),
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (2 + K') 2
            (eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s i α P₀ j idx)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal (eigenvectorConstant (K' + m + 3) *
              (i.fst.val)⁻¹ ^ (eigenvectorExponent (K' + m + 3))) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i‖ := by
  classical
  intro i j hj idx K'
  have h_chart_compact :
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K' + m + 3) 2
          (eigenvectorChartComponentFun (I := I) (M := M)
            g r s i α P₀)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (eigenvectorConstant (K' + m + 3) *
            (i.fst.val)⁻¹ ^ (eigenvectorExponent (K' + m + 3))) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖ :=
    eigenvector_bound i (K' + m + 3)
  have h_chart_compact_memWkp :
      MemWkp (d := Module.finrank ℝ E) ((2 + K') + j) 2
          (eigenvectorChartComponentFun (I := I) (M := M)
            g r s i α P₀)
          (chartTargetEuclid (I := I) (M := M) α) :=
    eigenvector_chartComponent_memWkp_arbitrary (I := I) (M := M)
      g r s i ((2 + K') + j) α P₀
  obtain ⟨_, h_partial⟩ :=
    eigenvectorChartIteratedPartial_wkpNorm_le_of_memWkp
      (I := I) (M := M) g r s i α P₀ j (2 + K') h_chart_compact_memWkp idx
  have h_order_le : (2 + K') + j ≤ K' + m + 3 := by omega
  have h_mono :
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) ((2 + K') + j) 2
          (eigenvectorChartComponentFun (I := I) (M := M)
            g r s i α P₀)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K' + m + 3) 2
            (eigenvectorChartComponentFun (I := I) (M := M)
              g r s i α P₀)
            (chartTargetEuclid (I := I) (M := M) α) :=
    wkpNorm_mono_order (d := Module.finrank ℝ E) h_order_le _ _
  exact h_partial.trans (h_mono.trans h_chart_compact)

omit [CompleteSpace E] in
theorem eigenvectorChartRHSDiff_eLpNorm_le_chartcpt
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (l : Fin m → Fin (Module.finrank ℝ E))
    (h_pou : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (m + 1 + 0) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) :
            EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β))
    (eigenvectorConstant : ℕ → ℝ) (eigenvectorExponent : ℕ → ℕ) (eigenvectorConstant_nonneg : ∀ K', 0 ≤ eigenvectorConstant K')
    (eigenvector_bound : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s) (K' : ℕ),
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K' 2
          (eigenvectorChartComponentFun (I := I) (M := M)
            g r s i α P₀)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (eigenvectorConstant K' * (i.fst.val)⁻¹ ^ (eigenvectorExponent K')) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖)
    (highResolventConstant : ℕ → ℝ) (highResolventExponent : ℕ → ℕ) (highResolventConstant_nonneg : ∀ K', 0 ≤ highResolventConstant K')
    (highResolvent_bound : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (β : M) (Q : TensorCompIdx (E := E) r s) (K' : ℕ),
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K' + 1) 2
          (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
              (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                (eigenvectorResolvent (I := I) (M := M) g r s i))
              β Q : Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) β)
        ≤ ENNReal.ofReal (highResolventConstant K' * (i.fst.val)⁻¹ ^ (highResolventExponent K')) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖)
    (lowResolventConstant : ℕ → ℝ) (lowResolventExponent : ℕ → ℕ) (lowResolventConstant_nonneg : ∀ K', 0 ≤ lowResolventConstant K')
    (lowResolvent_bound : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (β : M) (Q : TensorCompIdx (E := E) r s) (K' : ℕ),
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K' 2
          (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
              (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                (eigenvectorResolvent (I := I) (M := M) g r s i))
              β Q : Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) β)
        ≤ ENNReal.ofReal (lowResolventConstant K' * (i.fst.val)⁻¹ ^ (lowResolventExponent K')) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖)
    (partialConstant : ℕ → ℝ) (partialExponent : ℕ → ℕ) (partialConstant_nonneg : ∀ K', 0 ≤ partialConstant K')
    (partial_bound : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (P : TensorCompIdx (E := E) r s) (k : Fin (Module.finrank ℝ E)) (K' : ℕ),
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K' 2
          (fun y => ((partialLpLimit (I := I) (M := M)
              g r s i α P k :
              Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (partialConstant K' * (i.fst.val)⁻¹ ^ (partialExponent K')) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖)
    (componentConstant : ℕ → ℝ) (componentExponent : ℕ → ℕ) (componentConstant_nonneg : ∀ K', 0 ≤ componentConstant K')
    (component_bound : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (p : TensorCompIdx (E := E) r s) (K' : ℕ),
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K' 2
          (fun y => ((componentLpLimit (I := I) (M := M)
              g r s i α p :
              Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (componentConstant K' * (i.fst.val)⁻¹ ^ (componentExponent K')) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖)
    (crossRightConstant : ℕ → ℝ) (crossRightExponent : ℕ → ℕ) (crossRightConstant_nonneg : ∀ K', 0 ≤ crossRightConstant K')
    (crossRight_bound : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (P : TensorCompIdx (E := E) r s) (K' : ℕ),
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K' 2
          (fun y => ((crossRightLimitComponent (I := I) (M := M)
              g r s i α P :
              Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (crossRightConstant K' * (i.fst.val)⁻¹ ^ (crossRightExponent K')) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖)
    (cutoffConstant : ℕ → ℝ) (cutoffExponent : ℕ → ℕ) (cutoffConstant_nonneg : ∀ K', 0 ≤ cutoffConstant K')
    (cutoff_bound : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (P : TensorCompIdx (E := E) r s) (k : Fin (Module.finrank ℝ E)) (K' : ℕ),
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K' 2
          (fun y => ((cutoffPartialLpLimit (I := I) (M := M)
              g r s i α P k :
              Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (cutoffConstant K' * (i.fst.val)⁻¹ ^ (cutoffExponent K')) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖) :
    ∃ (C : ℝ) (e : ℕ), 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm (eigenvectorChartRHSDiff (I := I) (M := M)
            g r s i α P₀ m l) 2
          ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal (C * (i.fst.val)⁻¹ ^ e) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i‖ := by
  classical
  obtain ⟨Cwk, hCwk_nn, hCwk_bd⟩ :=
    eigenvectorChartRHSDiff_eLpNorm_le_uniform (I := I) (M := M)
      g r s α P₀ m l h_pou
  set Citer : ℕ → ℝ := fun K' => eigenvectorConstant (K' + m + 3) with hCiter_def
  set eIter : ℕ → ℕ := fun K' => eigenvectorExponent (K' + m + 3) with heIter_def
  have hCiter_nn : ∀ K', 0 ≤ Citer K' := fun K' => eigenvectorConstant_nonneg (K' + m + 3)
  have hCiter_bd :
      ∀ (i : TensorEigenIdx (I := I) (M := M) g r s) (j : ℕ),
        j ≤ m + 1 →
        ∀ (idx : Fin j → Fin (Module.finrank ℝ E)) (K' : ℕ),
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (2 + K') 2
              (eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s i α P₀ j idx)
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal (Citer K' * (i.fst.val)⁻¹ ^ (eIter K')) *
              ENNReal.ofReal
                ‖tensorResolventEigenbasisVec (I := I) (M := M)
                  (tensorResolventL2_isCompactOperator (I := I) (M := M)
                    g r s) i‖ :=
    iteratedPartial_wkpNorm_le_of_chart_perK (I := I) (M := M)
      g r s α P₀ m eigenvectorConstant eigenvectorExponent eigenvector_bound
  obtain ⟨Caggr, eAggr, hCaggr_nn, hCaggr_bd⟩ :=
    diffRHSAggregate_le_energy_perK (I := I) (M := M)
      g r s α P₀ m 0 l
      eigenvectorConstant eigenvectorExponent eigenvectorConstant_nonneg eigenvector_bound
      highResolventConstant highResolventExponent highResolventConstant_nonneg highResolvent_bound
      lowResolventConstant lowResolventExponent lowResolventConstant_nonneg lowResolvent_bound
      partialConstant partialExponent partialConstant_nonneg partial_bound
      componentConstant componentExponent componentConstant_nonneg component_bound
      crossRightConstant crossRightExponent crossRightConstant_nonneg crossRight_bound
      cutoffConstant cutoffExponent cutoffConstant_nonneg cutoff_bound
      Citer eIter hCiter_nn hCiter_bd
  refine ⟨Cwk * Caggr, eAggr + 1, mul_nonneg hCwk_nn hCaggr_nn, fun i => ?_⟩
  have hμ_unit : i.fst.val ∈ Set.Ioc (0 : ℝ) 1 := by
    have h_norm :
        ‖tensorResolventEigenbasisVec (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M)
            g r s) i‖ = 1 :=
      (tensorResolventEigenbasisVec_orthonormal (I := I) (M := M)
        (g := g) (r := r) (s := s)
        (tensorResolventL2_isCompactOperator (I := I) (M := M)
          g r s)).norm_eq_one i
    exact tensorResolvent_eigenvalue_mem_unit_interval (I := I) (M := M) g r s
      (tensorResolventEigenbasisVec_mem (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M)
          g r s) i)
      (by
        intro h_zero
        rw [h_zero, norm_zero] at h_norm
        exact one_ne_zero h_norm.symm)
  have hμ_pos : 0 < i.fst.val := hμ_unit.1
  have hμ_le_one : i.fst.val ≤ 1 := hμ_unit.2
  have hμ_inv_nn : 0 ≤ (i.fst.val)⁻¹ := le_of_lt (inv_pos.mpr hμ_pos)
  have hμ_inv_ge_one : (1 : ℝ) ≤ (i.fst.val)⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hμ_pos]; simpa using hμ_le_one
  set Rhs : ℝ≥0∞ := ENNReal.ofReal
      ‖tensorResolventEigenbasisVec (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M)
          g r s) i‖ with hRhs_def
  calc eLpNorm (eigenvectorChartRHSDiff (I := I) (M := M)
          g r s i α P₀ m l) 2
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α))
      ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * Cwk) *
          diffRHSAggregate (I := I) (M := M)
            g r s i α P₀ m 0 l := hCwk_bd i
    _ ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * Cwk) *
          (ENNReal.ofReal (Caggr * (i.fst.val)⁻¹ ^ eAggr) * Rhs) :=
        mul_le_mul' (le_refl _) (hCaggr_bd i)
    _ = ENNReal.ofReal ((Cwk * Caggr) * (i.fst.val)⁻¹ ^ (eAggr + 1)) * Rhs := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        rw [pow_succ, mul_comm ((i.fst.val)⁻¹ ^ eAggr) (i.fst.val)⁻¹]
        ring

omit [CompleteSpace E] in
theorem eigenvectorChartRHSDiff_wkpNormOne_le_chartcpt
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (l : Fin m → Fin (Module.finrank ℝ E))
    (h_pou : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (m + 1 + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) :
            EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β))
    (eigenvectorConstant : ℕ → ℝ) (eigenvectorExponent : ℕ → ℕ) (eigenvectorConstant_nonneg : ∀ K', 0 ≤ eigenvectorConstant K')
    (eigenvector_bound : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s) (K' : ℕ),
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K' 2
          (eigenvectorChartComponentFun (I := I) (M := M)
            g r s i α P₀)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (eigenvectorConstant K' * (i.fst.val)⁻¹ ^ (eigenvectorExponent K')) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖)
    (highResolventConstant : ℕ → ℝ) (highResolventExponent : ℕ → ℕ) (highResolventConstant_nonneg : ∀ K', 0 ≤ highResolventConstant K')
    (highResolvent_bound : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (β : M) (Q : TensorCompIdx (E := E) r s) (K' : ℕ),
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K' + 1) 2
          (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
              (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                (eigenvectorResolvent (I := I) (M := M) g r s i))
              β Q : Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) β)
        ≤ ENNReal.ofReal (highResolventConstant K' * (i.fst.val)⁻¹ ^ (highResolventExponent K')) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖)
    (lowResolventConstant : ℕ → ℝ) (lowResolventExponent : ℕ → ℕ) (lowResolventConstant_nonneg : ∀ K', 0 ≤ lowResolventConstant K')
    (lowResolvent_bound : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (β : M) (Q : TensorCompIdx (E := E) r s) (K' : ℕ),
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K' 2
          (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
              (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                (eigenvectorResolvent (I := I) (M := M) g r s i))
              β Q : Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) β)
        ≤ ENNReal.ofReal (lowResolventConstant K' * (i.fst.val)⁻¹ ^ (lowResolventExponent K')) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖)
    (partialConstant : ℕ → ℝ) (partialExponent : ℕ → ℕ) (partialConstant_nonneg : ∀ K', 0 ≤ partialConstant K')
    (partial_bound : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (P : TensorCompIdx (E := E) r s) (k : Fin (Module.finrank ℝ E)) (K' : ℕ),
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K' 2
          (fun y => ((partialLpLimit (I := I) (M := M)
              g r s i α P k :
              Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (partialConstant K' * (i.fst.val)⁻¹ ^ (partialExponent K')) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖)
    (componentConstant : ℕ → ℝ) (componentExponent : ℕ → ℕ) (componentConstant_nonneg : ∀ K', 0 ≤ componentConstant K')
    (component_bound : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (p : TensorCompIdx (E := E) r s) (K' : ℕ),
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K' 2
          (fun y => ((componentLpLimit (I := I) (M := M)
              g r s i α p :
              Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (componentConstant K' * (i.fst.val)⁻¹ ^ (componentExponent K')) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖)
    (crossRightConstant : ℕ → ℝ) (crossRightExponent : ℕ → ℕ) (crossRightConstant_nonneg : ∀ K', 0 ≤ crossRightConstant K')
    (crossRight_bound : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (P : TensorCompIdx (E := E) r s) (K' : ℕ),
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K' 2
          (fun y => ((crossRightLimitComponent (I := I) (M := M)
              g r s i α P :
              Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (crossRightConstant K' * (i.fst.val)⁻¹ ^ (crossRightExponent K')) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖)
    (cutoffConstant : ℕ → ℝ) (cutoffExponent : ℕ → ℕ) (cutoffConstant_nonneg : ∀ K', 0 ≤ cutoffConstant K')
    (cutoff_bound : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (P : TensorCompIdx (E := E) r s) (k : Fin (Module.finrank ℝ E)) (K' : ℕ),
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K' 2
          (fun y => ((cutoffPartialLpLimit (I := I) (M := M)
              g r s i α P k :
              Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (cutoffConstant K' * (i.fst.val)⁻¹ ^ (cutoffExponent K')) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖) :
    ∃ (C : ℝ) (e : ℕ), 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) 1 2
            (eigenvectorChartRHSDiff (I := I) (M := M)
              g r s i α P₀ m l)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal (C * (i.fst.val)⁻¹ ^ e) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i‖ := by
  classical
  obtain ⟨Cwk, hCwk_nn, hCwk_bd⟩ :=
    eigenvectorChartRHSDiff_wkpNorm_le_uniform (I := I) (M := M)
      g r s α P₀ m 1 l h_pou
  set Citer : ℕ → ℝ := fun K' => eigenvectorConstant (K' + m + 3) with hCiter_def
  set eIter : ℕ → ℕ := fun K' => eigenvectorExponent (K' + m + 3) with heIter_def
  have hCiter_nn : ∀ K', 0 ≤ Citer K' := fun K' => eigenvectorConstant_nonneg (K' + m + 3)
  have hCiter_bd :
      ∀ (i : TensorEigenIdx (I := I) (M := M) g r s) (j : ℕ),
        j ≤ m + 1 →
        ∀ (idx : Fin j → Fin (Module.finrank ℝ E)) (K' : ℕ),
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (2 + K') 2
              (eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s i α P₀ j idx)
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal (Citer K' * (i.fst.val)⁻¹ ^ (eIter K')) *
              ENNReal.ofReal
                ‖tensorResolventEigenbasisVec (I := I) (M := M)
                  (tensorResolventL2_isCompactOperator (I := I) (M := M)
                    g r s) i‖ :=
    iteratedPartial_wkpNorm_le_of_chart_perK (I := I) (M := M)
      g r s α P₀ m eigenvectorConstant eigenvectorExponent eigenvector_bound
  obtain ⟨Caggr, eAggr, hCaggr_nn, hCaggr_bd⟩ :=
    diffRHSAggregate_le_energy_perK (I := I) (M := M)
      g r s α P₀ m 1 l
      eigenvectorConstant eigenvectorExponent eigenvectorConstant_nonneg eigenvector_bound
      highResolventConstant highResolventExponent highResolventConstant_nonneg highResolvent_bound
      lowResolventConstant lowResolventExponent lowResolventConstant_nonneg lowResolvent_bound
      partialConstant partialExponent partialConstant_nonneg partial_bound
      componentConstant componentExponent componentConstant_nonneg component_bound
      crossRightConstant crossRightExponent crossRightConstant_nonneg crossRight_bound
      cutoffConstant cutoffExponent cutoffConstant_nonneg cutoff_bound
      Citer eIter hCiter_nn hCiter_bd
  refine ⟨Cwk * Caggr, eAggr + 1, mul_nonneg hCwk_nn hCaggr_nn, fun i => ?_⟩
  have hμ_unit : i.fst.val ∈ Set.Ioc (0 : ℝ) 1 := by
    have h_norm :
        ‖tensorResolventEigenbasisVec (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M)
            g r s) i‖ = 1 :=
      (tensorResolventEigenbasisVec_orthonormal (I := I) (M := M)
        (g := g) (r := r) (s := s)
        (tensorResolventL2_isCompactOperator (I := I) (M := M)
          g r s)).norm_eq_one i
    exact tensorResolvent_eigenvalue_mem_unit_interval (I := I) (M := M) g r s
      (tensorResolventEigenbasisVec_mem (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M)
          g r s) i)
      (by
        intro h_zero
        rw [h_zero, norm_zero] at h_norm
        exact one_ne_zero h_norm.symm)
  have hμ_pos : 0 < i.fst.val := hμ_unit.1
  have hμ_le_one : i.fst.val ≤ 1 := hμ_unit.2
  have hμ_inv_nn : 0 ≤ (i.fst.val)⁻¹ := le_of_lt (inv_pos.mpr hμ_pos)
  set Rhs : ℝ≥0∞ := ENNReal.ofReal
      ‖tensorResolventEigenbasisVec (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M)
          g r s) i‖ with hRhs_def
  calc iteratedWeakSobolevNorm (d := Module.finrank ℝ E) 1 2
          (eigenvectorChartRHSDiff (I := I) (M := M)
            g r s i α P₀ m l)
          (chartTargetEuclid (I := I) (M := M) α)
      ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * Cwk) *
          diffRHSAggregate (I := I) (M := M)
            g r s i α P₀ m 1 l := hCwk_bd i
    _ ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * Cwk) *
          (ENNReal.ofReal (Caggr * (i.fst.val)⁻¹ ^ eAggr) * Rhs) :=
        mul_le_mul' (le_refl _) (hCaggr_bd i)
    _ = ENNReal.ofReal ((Cwk * Caggr) * (i.fst.val)⁻¹ ^ (eAggr + 1)) * Rhs := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        rw [pow_succ, mul_comm ((i.fst.val)⁻¹ ^ eAggr) (i.fst.val)⁻¹]
        ring

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry
