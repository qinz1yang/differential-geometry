import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.RightHandSide.Chart.Sobolev.EnergyBound
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.RightHandSide.Differentiated.Sobolev.Bounds
import DifferentialGeometry.Analysis.Estimates.WeightedSums
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Estimates (sum_le_of_le_ofReal_mul)
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
private lemma vec_norm_eq_one
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    ‖tensorResolventEigenbasisVec (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M)
          g r s) i‖ = 1 :=
  (tensorResolventEigenbasisVec_orthonormal (I := I) (M := M)
    (g := g) (r := r) (s := s)
    (tensorResolventL2_isCompactOperator (I := I) (M := M)
      g r s)).norm_eq_one i

omit [CompleteSpace E] in
private lemma eigenvalue_pos
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    0 < i.fst.val :=
  (tensorResolvent_eigenvalue_mem_unit_interval (I := I) (M := M) g r s
    (tensorResolventEigenbasisVec_mem (I := I) (M := M)
      (tensorResolventL2_isCompactOperator (I := I) (M := M)
        g r s) i)
    (by
      intro h_zero
      have h_norm := vec_norm_eq_one (I := I) (M := M) g r s i
      rw [h_zero, norm_zero] at h_norm
      exact one_ne_zero h_norm.symm)).1

omit [CompleteSpace E] in
private lemma eigenvalue_le_one
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    i.fst.val ≤ 1 :=
  (tensorResolvent_eigenvalue_mem_unit_interval (I := I) (M := M) g r s
    (tensorResolventEigenbasisVec_mem (I := I) (M := M)
      (tensorResolventL2_isCompactOperator (I := I) (M := M)
        g r s) i)
    (by
      intro h_zero
      have h_norm := vec_norm_eq_one (I := I) (M := M) g r s i
      rw [h_zero, norm_zero] at h_norm
      exact one_ne_zero h_norm.symm)).2

omit [CompleteSpace E] in
lemma rhsZeroAggregate_le_energy_perK
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (K : ℕ)
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
      (P : TensorCompIdx (E := E) r s) (l : Fin (Module.finrank ℝ E)) (K' : ℕ),
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K' 2
          (fun y => ((cutoffPartialLpLimit (I := I) (M := M)
              g r s i α P l :
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
        rhsZeroAggregate (I := I) (M := M) g r s i α P₀ K
          ≤ ENNReal.ofReal (C * (i.fst.val)⁻¹ ^ e) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i‖ := by
  classical
  set e_max : ℕ :=
    max (max (max (max (max (max (max
      (eigenvectorExponent K) (highResolventExponent K)) (highResolventExponent (K + 1))) (lowResolventExponent K)) (partialExponent K))
      (componentExponent K)) (crossRightExponent K)) (cutoffExponent K) with he_max_def
  set Cqtot : ℝ := (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) * highResolventConstant K
    with hCqtot_def
  set Cmid_α : ℝ := (transportChartCenters (I := I) (M := M) α).sum fun β =>
        Cqtot + ((transportChartCenters (I := I) (M := M) β).card : ℝ) * Cqtot
    with hCmid_α_def
  set Clow_α : ℝ :=
    ((transportChartCenters (I := I) (M := M) α).card : ℝ) *
      ((Fintype.card (TensorCompIdx (E := E) r s) : ℝ) * lowResolventConstant K) with hClow_α_def
  set partialConstant' : ℝ := (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) *
        ((Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) * partialConstant K) with hCpar'_def
  set componentConstant' : ℝ := (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) * componentConstant K
    with hCcom'_def
  set crossRightConstant' : ℝ := (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) * crossRightConstant K
    with hCcR'_def
  set cutoffConstant' : ℝ := (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) *
        ((Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) * cutoffConstant K) with hCcut'_def
  set Cagg : ℝ := eigenvectorConstant K + Cmid_α + Clow_α + partialConstant' + componentConstant' + crossRightConstant' + cutoffConstant'
    with hCagg_def
  have hCqtot_nn : 0 ≤ Cqtot := by
    have : (0 : ℝ) ≤ (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) := by
      exact_mod_cast Nat.zero_le _
    exact mul_nonneg this (highResolventConstant_nonneg K)
  have hCmid_α_nn : 0 ≤ Cmid_α := by
    refine Finset.sum_nonneg (fun β _ => ?_)
    have h1 : (0 : ℝ) ≤ ((transportChartCenters (I := I) (M := M) β).card : ℝ) := by
      exact_mod_cast Nat.zero_le _
    exact add_nonneg hCqtot_nn (mul_nonneg h1 hCqtot_nn)
  have hClow_α_nn : 0 ≤ Clow_α := by
    have hT : (0 : ℝ) ≤ ((transportChartCenters (I := I) (M := M) α).card : ℝ) := by
      exact_mod_cast Nat.zero_le _
    have hQ : (0 : ℝ) ≤ (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) := by
      exact_mod_cast Nat.zero_le _
    exact mul_nonneg hT (mul_nonneg hQ (lowResolventConstant_nonneg K))
  have hCpar'_nn : 0 ≤ partialConstant' := by
    have hQ : (0 : ℝ) ≤ (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) := by
      exact_mod_cast Nat.zero_le _
    have hk : (0 : ℝ) ≤ (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) := by
      exact_mod_cast Nat.zero_le _
    exact mul_nonneg hQ (mul_nonneg hk (partialConstant_nonneg K))
  have hCcom'_nn : 0 ≤ componentConstant' := by
    have hQ : (0 : ℝ) ≤ (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) := by
      exact_mod_cast Nat.zero_le _
    exact mul_nonneg hQ (componentConstant_nonneg K)
  have hCcR'_nn : 0 ≤ crossRightConstant' := by
    have hQ : (0 : ℝ) ≤ (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) := by
      exact_mod_cast Nat.zero_le _
    exact mul_nonneg hQ (crossRightConstant_nonneg K)
  have hCcut'_nn : 0 ≤ cutoffConstant' := by
    have hQ : (0 : ℝ) ≤ (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) := by
      exact_mod_cast Nat.zero_le _
    have hk : (0 : ℝ) ≤ (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) := by
      exact_mod_cast Nat.zero_le _
    exact mul_nonneg hQ (mul_nonneg hk (cutoffConstant_nonneg K))
  have hCagg_nn : 0 ≤ Cagg := by
    refine add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg
      (add_nonneg ?_ hCmid_α_nn) hClow_α_nn) hCpar'_nn) hCcom'_nn) hCcR'_nn) hCcut'_nn
    exact eigenvectorConstant_nonneg K
  refine ⟨Cagg, e_max, hCagg_nn, fun i => ?_⟩
  have hμ_pos : 0 < i.fst.val :=
    eigenvalue_pos (I := I) (M := M) g r s i
  have hμ_le_one : i.fst.val ≤ 1 :=
    eigenvalue_le_one (I := I) (M := M) g r s i
  have hμ_inv_nn : 0 ≤ (i.fst.val)⁻¹ := le_of_lt (inv_pos.mpr hμ_pos)
  have hμ_inv_ge_one : (1 : ℝ) ≤ (i.fst.val)⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hμ_pos]; simpa using hμ_le_one
  have hpow_e_max_pos : 0 < (i.fst.val)⁻¹ ^ e_max :=
    pow_pos (inv_pos.mpr hμ_pos) _
  have hpow_e_max_nn : 0 ≤ (i.fst.val)⁻¹ ^ e_max := hpow_e_max_pos.le
  have hEig_le : eigenvectorExponent K ≤ e_max := by
    refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_left _ _); refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_left _ _); refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_left _ _); exact le_max_left _ _
  have hResH_le : highResolventExponent K ≤ e_max := by
    refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_left _ _); refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_left _ _); refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_left _ _); exact le_max_right _ _
  have hResH1_le : highResolventExponent (K + 1) ≤ e_max := by
    refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_left _ _); refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_left _ _); refine le_trans ?_ (le_max_left _ _)
    exact le_max_right _ _
  have hResL_le : lowResolventExponent K ≤ e_max := by
    refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_left _ _); refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_left _ _); exact le_max_right _ _
  have hPar_le : partialExponent K ≤ e_max := by
    refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_left _ _); refine le_trans ?_ (le_max_left _ _)
    exact le_max_right _ _
  have hCom_le : componentExponent K ≤ e_max := by
    refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_left _ _); exact le_max_right _ _
  have hCcR_le : crossRightExponent K ≤ e_max := by
    refine le_trans ?_ (le_max_left _ _); exact le_max_right _ _
  have hCcut_le : cutoffExponent K ≤ e_max := le_max_right _ _
  have hpow_dom : ∀ a, a ≤ e_max → (i.fst.val)⁻¹ ^ a ≤ (i.fst.val)⁻¹ ^ e_max :=
    fun _a ha => pow_le_pow_right₀ hμ_inv_ge_one ha
  set Rhs : ℝ≥0∞ := ENNReal.ofReal
      ‖tensorResolventEigenbasisVec (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M)
          g r s) i‖ with hRhs_def
  set Rhs_effective : ℝ≥0∞ := ENNReal.ofReal ((i.fst.val)⁻¹ ^ e_max) * Rhs
    with hRhs_effective_def
  have h_bridge : ∀ (w : ℝ≥0∞) (Cval : ℝ) (a : ℕ),
      0 ≤ Cval → a ≤ e_max →
      w ≤ ENNReal.ofReal (Cval * (i.fst.val)⁻¹ ^ a) * Rhs →
      w ≤ ENNReal.ofReal Cval * Rhs_effective := by
    intro w Cval a hCval_nn ha hw
    have hpow_le : (i.fst.val)⁻¹ ^ a ≤ (i.fst.val)⁻¹ ^ e_max := hpow_dom a ha
    have hCmul_le : Cval * (i.fst.val)⁻¹ ^ a ≤ Cval * (i.fst.val)⁻¹ ^ e_max :=
      mul_le_mul_of_nonneg_left hpow_le hCval_nn
    have h_eNN_le : ENNReal.ofReal (Cval * (i.fst.val)⁻¹ ^ a)
          ≤ ENNReal.ofReal (Cval * (i.fst.val)⁻¹ ^ e_max) :=
      ENNReal.ofReal_le_ofReal hCmul_le
    have h_step : w ≤ ENNReal.ofReal (Cval * (i.fst.val)⁻¹ ^ e_max) * Rhs := by
      refine hw.trans ?_
      exact mul_le_mul_of_nonneg_right h_eNN_le (by exact zero_le)
    have h_rw : ENNReal.ofReal (Cval * (i.fst.val)⁻¹ ^ e_max) * Rhs
          = ENNReal.ofReal Cval * Rhs_effective := by
      rw [hRhs_effective_def, ENNReal.ofReal_mul hCval_nn, mul_assoc]
    exact h_step.trans_eq h_rw
  have hS1 :
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
          (eigenvectorChartComponentFun (I := I) (M := M)
            g r s i α P₀)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (eigenvectorConstant K) * Rhs_effective :=
    h_bridge _ (eigenvectorConstant K) (eigenvectorExponent K) (eigenvectorConstant_nonneg K) hEig_le (eigenvector_bound i K)
  have hS2_inner : ∀ β ∈ transportChartCenters (I := I) (M := M) α,
      ((∑ Q : TensorCompIdx (E := E) r s,
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K + 1) 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                  (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                    (eigenvectorResolvent (I := I) (M := M) g r s i))
                  β Q : Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) :
                  EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β))
        + ∑ β' ∈ transportChartCenters (I := I) (M := M) β,
            ∑ Q : TensorCompIdx (E := E) r s,
              iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K + 1) 2
                (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                    (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                      (eigenvectorResolvent (I := I) (M := M) g r s i))
                    β' Q : Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β')) :
                    EuclN → ℝ) y)
                (chartTargetEuclid (I := I) (M := M) β'))
        ≤ ENNReal.ofReal
            (Cqtot + ((transportChartCenters (I := I) (M := M) β).card : ℝ) *
              Cqtot) * Rhs_effective := by
    intro β _hβ
    have h_inner_β :
        (∑ Q : TensorCompIdx (E := E) r s,
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K + 1) 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                  (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                    (eigenvectorResolvent (I := I) (M := M) g r s i))
                  β Q : Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) :
                  EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β))
          ≤ ENNReal.ofReal Cqtot * Rhs_effective := by
      have h_each : ∀ Q ∈ (Finset.univ : Finset (TensorCompIdx (E := E) r s)),
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K + 1) 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                  (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                    (eigenvectorResolvent (I := I) (M := M) g r s i))
                  β Q : Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) :
                  EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β)
            ≤ ENNReal.ofReal (highResolventConstant K) * Rhs_effective := fun Q _hQ =>
        h_bridge _ (highResolventConstant K) (highResolventExponent K) (highResolventConstant_nonneg K) hResH_le
          (highResolvent_bound i β Q K)
      have h_sum := sum_le_of_le_ofReal_mul
        (Finset.univ : Finset (TensorCompIdx (E := E) r s))
        (fun Q => iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K + 1) 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                  (eigenvectorResolvent (I := I) (M := M) g r s i))
                β Q : Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) :
                EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β))
        (fun _Q => highResolventConstant K) Rhs_effective (fun _ _ => highResolventConstant_nonneg K) h_each
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at h_sum
      exact h_sum.trans_eq (by rw [hCqtot_def])
    have h_inner_β' :
        (∑ β' ∈ transportChartCenters (I := I) (M := M) β,
          ∑ Q : TensorCompIdx (E := E) r s,
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K + 1) 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                  (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                    (eigenvectorResolvent (I := I) (M := M) g r s i))
                  β' Q : Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β')) :
                  EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β'))
        ≤ ENNReal.ofReal
            (((transportChartCenters (I := I) (M := M) β).card : ℝ) * Cqtot) *
            Rhs_effective := by
      have h_perβ' : ∀ β' ∈ transportChartCenters (I := I) (M := M) β,
          (∑ Q : TensorCompIdx (E := E) r s,
              iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K + 1) 2
                (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                    (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                      (eigenvectorResolvent (I := I) (M := M) g r s i))
                    β' Q : Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β')) :
                    EuclN → ℝ) y)
                (chartTargetEuclid (I := I) (M := M) β'))
            ≤ ENNReal.ofReal Cqtot * Rhs_effective := by
        intro β' _hβ'
        have h_each : ∀ Q ∈ (Finset.univ : Finset (TensorCompIdx (E := E) r s)),
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K + 1) 2
                (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                    (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                      (eigenvectorResolvent (I := I) (M := M) g r s i))
                    β' Q : Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β')) :
                    EuclN → ℝ) y)
                (chartTargetEuclid (I := I) (M := M) β')
              ≤ ENNReal.ofReal (highResolventConstant K) * Rhs_effective := fun Q _hQ =>
          h_bridge _ (highResolventConstant K) (highResolventExponent K) (highResolventConstant_nonneg K) hResH_le
            (highResolvent_bound i β' Q K)
        have h_sum := sum_le_of_le_ofReal_mul
          (Finset.univ : Finset (TensorCompIdx (E := E) r s))
          (fun Q => iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K + 1) 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                  (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                    (eigenvectorResolvent (I := I) (M := M) g r s i))
                  β' Q : Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β')) :
                  EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β'))
          (fun _Q => highResolventConstant K) Rhs_effective (fun _ _ => highResolventConstant_nonneg K) h_each
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at h_sum
        exact h_sum.trans_eq (by rw [hCqtot_def])
      have h_sum := sum_le_of_le_ofReal_mul
        (transportChartCenters (I := I) (M := M) β)
        (fun β' => ∑ Q : TensorCompIdx (E := E) r s,
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K + 1) 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                  (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                    (eigenvectorResolvent (I := I) (M := M) g r s i))
                  β' Q : Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β')) :
                  EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β'))
        (fun _β' => Cqtot) Rhs_effective (fun _ _ => hCqtot_nn) h_perβ'
      rw [Finset.sum_const, nsmul_eq_mul] at h_sum
      exact h_sum
    have h_total :=
      add_le_add h_inner_β h_inner_β'
    refine h_total.trans (le_of_eq ?_)
    have hN : 0 ≤ ((transportChartCenters (I := I) (M := M) β).card : ℝ) := by
      exact_mod_cast Nat.zero_le _
    rw [ENNReal.ofReal_add hCqtot_nn (mul_nonneg hN hCqtot_nn), add_mul]
  have hS2 :
      (∑ β ∈ transportChartCenters (I := I) (M := M) α,
        ((∑ Q : TensorCompIdx (E := E) r s,
              iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K + 1) 2
                (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                    (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                      (eigenvectorResolvent (I := I) (M := M) g r s i))
                    β Q : Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) :
                    EuclN → ℝ) y)
                (chartTargetEuclid (I := I) (M := M) β))
          + ∑ β' ∈ transportChartCenters (I := I) (M := M) β,
              ∑ Q : TensorCompIdx (E := E) r s,
                iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K + 1) 2
                  (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                      (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                        (eigenvectorResolvent (I := I) (M := M)
                          g r s i))
                      β' Q :
                      Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β')) :
                      EuclN → ℝ) y)
                  (chartTargetEuclid (I := I) (M := M) β')))
      ≤ ENNReal.ofReal Cmid_α * Rhs_effective := by
    have h_perβ_nn :
        ∀ β ∈ transportChartCenters (I := I) (M := M) α,
          0 ≤ Cqtot +
              ((transportChartCenters (I := I) (M := M) β).card : ℝ) * Cqtot := by
      intro β _hβ
      have hN : (0 : ℝ) ≤
          ((transportChartCenters (I := I) (M := M) β).card : ℝ) := by
        exact_mod_cast Nat.zero_le _
      exact add_nonneg hCqtot_nn (mul_nonneg hN hCqtot_nn)
    have h_sum := sum_le_of_le_ofReal_mul
      (transportChartCenters (I := I) (M := M) α)
      (fun β => (∑ Q : TensorCompIdx (E := E) r s,
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K + 1) 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                  (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                    (eigenvectorResolvent (I := I) (M := M) g r s i))
                  β Q : Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) :
                  EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β))
        + ∑ β' ∈ transportChartCenters (I := I) (M := M) β,
            ∑ Q : TensorCompIdx (E := E) r s,
              iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K + 1) 2
                (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                    (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                      (eigenvectorResolvent (I := I) (M := M)
                        g r s i))
                    β' Q :
                    Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β')) :
                    EuclN → ℝ) y)
                (chartTargetEuclid (I := I) (M := M) β'))
      (fun β => Cqtot +
        ((transportChartCenters (I := I) (M := M) β).card : ℝ) * Cqtot)
      Rhs_effective h_perβ_nn hS2_inner
    exact h_sum.trans_eq (by rw [hCmid_α_def])
  have hS3 :
      (∑ β ∈ transportChartCenters (I := I) (M := M) α,
        ∑ Q : TensorCompIdx (E := E) r s,
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                  (eigenvectorResolvent (I := I) (M := M) g r s i))
                β Q : Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) :
                EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β))
      ≤ ENNReal.ofReal Clow_α * Rhs_effective := by
    have h_perβ : ∀ β ∈ transportChartCenters (I := I) (M := M) α,
        (∑ Q : TensorCompIdx (E := E) r s,
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                  (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                    (eigenvectorResolvent (I := I) (M := M) g r s i))
                  β Q : Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) :
                  EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β))
          ≤ ENNReal.ofReal
              ((Fintype.card (TensorCompIdx (E := E) r s) : ℝ) * lowResolventConstant K) *
            Rhs_effective := by
      intro β _hβ
      have h_each : ∀ Q ∈ (Finset.univ : Finset (TensorCompIdx (E := E) r s)),
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                  (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                    (eigenvectorResolvent (I := I) (M := M) g r s i))
                  β Q : Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) :
                  EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β)
            ≤ ENNReal.ofReal (lowResolventConstant K) * Rhs_effective := fun Q _hQ =>
        h_bridge _ (lowResolventConstant K) (lowResolventExponent K) (lowResolventConstant_nonneg K) hResL_le
          (lowResolvent_bound i β Q K)
      have h_sum := sum_le_of_le_ofReal_mul
        (Finset.univ : Finset (TensorCompIdx (E := E) r s))
        (fun Q => iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                  (eigenvectorResolvent (I := I) (M := M) g r s i))
                β Q : Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) :
                EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β))
        (fun _Q => lowResolventConstant K) Rhs_effective (fun _ _ => lowResolventConstant_nonneg K) h_each
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at h_sum
      exact h_sum
    have hQ_nn : (0 : ℝ) ≤
        (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) * lowResolventConstant K := by
      have hQ : (0 : ℝ) ≤ (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) := by
        exact_mod_cast Nat.zero_le _
      exact mul_nonneg hQ (lowResolventConstant_nonneg K)
    have h_sum := sum_le_of_le_ofReal_mul
      (transportChartCenters (I := I) (M := M) α)
      (fun β => ∑ Q : TensorCompIdx (E := E) r s,
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                  (eigenvectorResolvent (I := I) (M := M) g r s i))
                β Q : Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) :
                EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β))
      (fun _β => (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) * lowResolventConstant K)
      Rhs_effective (fun _ _ => hQ_nn) h_perβ
    rw [Finset.sum_const, nsmul_eq_mul] at h_sum
    exact h_sum.trans_eq (by rw [hClow_α_def])
  have hS4 :
      (∑ P : TensorCompIdx (E := E) r s,
        ∑ k : Fin (Module.finrank ℝ E),
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((partialLpLimit (I := I) (M := M)
                g r s i α P k :
              Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α))
      ≤ ENNReal.ofReal partialConstant' * Rhs_effective := by
    have h_perP : ∀ P ∈ (Finset.univ : Finset (TensorCompIdx (E := E) r s)),
        (∑ k : Fin (Module.finrank ℝ E),
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (fun y => ((partialLpLimit (I := I) (M := M)
                  g r s i α P k :
                Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
                EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal
              ((Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) * partialConstant K) *
            Rhs_effective := by
      intro P _hP
      have h_each : ∀ k ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ E))),
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (fun y => ((partialLpLimit (I := I) (M := M)
                  g r s i α P k :
                Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
                EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal (partialConstant K) * Rhs_effective := fun k _hk =>
        h_bridge _ (partialConstant K) (partialExponent K) (partialConstant_nonneg K) hPar_le (partial_bound i P k K)
      have h_sum := sum_le_of_le_ofReal_mul
        (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
        (fun k => iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((partialLpLimit (I := I) (M := M)
                g r s i α P k :
              Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α))
        (fun _k => partialConstant K) Rhs_effective (fun _ _ => partialConstant_nonneg K) h_each
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at h_sum
      exact h_sum
    have hk_nn : (0 : ℝ) ≤
        (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) * partialConstant K := by
      have hk : (0 : ℝ) ≤ (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) := by
        exact_mod_cast Nat.zero_le _
      exact mul_nonneg hk (partialConstant_nonneg K)
    have h_sum := sum_le_of_le_ofReal_mul
      (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun P => ∑ k : Fin (Module.finrank ℝ E),
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((partialLpLimit (I := I) (M := M)
                g r s i α P k :
              Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α))
      (fun _P => (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) * partialConstant K)
      Rhs_effective (fun _ _ => hk_nn) h_perP
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at h_sum
    exact h_sum.trans_eq (by rw [hCpar'_def])
  have hS5 :
      (∑ p : TensorCompIdx (E := E) r s,
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
          (fun y => ((componentLpLimit (I := I) (M := M)
              g r s i α p :
            Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
            EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α))
      ≤ ENNReal.ofReal componentConstant' * Rhs_effective := by
    have h_each : ∀ p ∈ (Finset.univ : Finset (TensorCompIdx (E := E) r s)),
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((componentLpLimit (I := I) (M := M)
                g r s i α p :
              Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal (componentConstant K) * Rhs_effective := fun p _hp =>
      h_bridge _ (componentConstant K) (componentExponent K) (componentConstant_nonneg K) hCom_le (component_bound i p K)
    have h_sum := sum_le_of_le_ofReal_mul
      (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun p => iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
          (fun y => ((componentLpLimit (I := I) (M := M)
              g r s i α p :
            Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
            EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α))
      (fun _p => componentConstant K) Rhs_effective (fun _ _ => componentConstant_nonneg K) h_each
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at h_sum
    exact h_sum.trans_eq (by rw [hCcom'_def])
  have hS6 :
      (∑ P : TensorCompIdx (E := E) r s,
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
          (fun y => ((crossRightLimitComponent (I := I) (M := M)
              g r s i α P :
            Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
            EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α))
      ≤ ENNReal.ofReal crossRightConstant' * Rhs_effective := by
    have h_each : ∀ P ∈ (Finset.univ : Finset (TensorCompIdx (E := E) r s)),
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((crossRightLimitComponent (I := I) (M := M)
                g r s i α P :
              Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal (crossRightConstant K) * Rhs_effective := fun P _hP =>
      h_bridge _ (crossRightConstant K) (crossRightExponent K) (crossRightConstant_nonneg K) hCcR_le (crossRight_bound i P K)
    have h_sum := sum_le_of_le_ofReal_mul
      (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun P => iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
          (fun y => ((crossRightLimitComponent (I := I) (M := M)
              g r s i α P :
            Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
            EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α))
      (fun _P => crossRightConstant K) Rhs_effective (fun _ _ => crossRightConstant_nonneg K) h_each
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at h_sum
    exact h_sum.trans_eq (by rw [hCcR'_def])
  have hS7 :
      (∑ P : TensorCompIdx (E := E) r s,
        ∑ l : Fin (Module.finrank ℝ E),
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((cutoffPartialLpLimit (I := I) (M := M)
                g r s i α P l :
              Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α))
      ≤ ENNReal.ofReal cutoffConstant' * Rhs_effective := by
    have h_perP : ∀ P ∈ (Finset.univ : Finset (TensorCompIdx (E := E) r s)),
        (∑ l : Fin (Module.finrank ℝ E),
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (fun y => ((cutoffPartialLpLimit (I := I) (M := M)
                  g r s i α P l :
                Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
                EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal
              ((Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) * cutoffConstant K) *
            Rhs_effective := by
      intro P _hP
      have h_each : ∀ l ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ E))),
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (fun y => ((cutoffPartialLpLimit (I := I) (M := M)
                  g r s i α P l :
                Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
                EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal (cutoffConstant K) * Rhs_effective := fun l _hl =>
        h_bridge _ (cutoffConstant K) (cutoffExponent K) (cutoffConstant_nonneg K) hCcut_le (cutoff_bound i P l K)
      have h_sum := sum_le_of_le_ofReal_mul
        (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
        (fun l => iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((cutoffPartialLpLimit (I := I) (M := M)
                g r s i α P l :
              Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α))
        (fun _l => cutoffConstant K) Rhs_effective (fun _ _ => cutoffConstant_nonneg K) h_each
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at h_sum
      exact h_sum
    have hk_nn : (0 : ℝ) ≤
        (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) * cutoffConstant K := by
      have hk : (0 : ℝ) ≤ (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) := by
        exact_mod_cast Nat.zero_le _
      exact mul_nonneg hk (cutoffConstant_nonneg K)
    have h_sum := sum_le_of_le_ofReal_mul
      (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun P => ∑ l : Fin (Module.finrank ℝ E),
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((cutoffPartialLpLimit (I := I) (M := M)
                g r s i α P l :
              Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α))
      (fun _P => (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) * cutoffConstant K)
      Rhs_effective (fun _ _ => hk_nn) h_perP
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at h_sum
    exact h_sum.trans_eq (by rw [hCcut'_def])
  rw [rhsZeroAggregate]
  have hp1 : 0 ≤ eigenvectorConstant K + Cmid_α := add_nonneg (eigenvectorConstant_nonneg K) hCmid_α_nn
  have hp2 : 0 ≤ eigenvectorConstant K + Cmid_α + Clow_α := add_nonneg hp1 hClow_α_nn
  have hp3 : 0 ≤ eigenvectorConstant K + Cmid_α + Clow_α + partialConstant' := add_nonneg hp2 hCpar'_nn
  have hp4 : 0 ≤ eigenvectorConstant K + Cmid_α + Clow_α + partialConstant' + componentConstant' :=
    add_nonneg hp3 hCcom'_nn
  have hp5 : 0 ≤ eigenvectorConstant K + Cmid_α + Clow_α + partialConstant' + componentConstant' + crossRightConstant' :=
    add_nonneg hp4 hCcR'_nn
  have h_expand :
      ENNReal.ofReal Cagg
        = ENNReal.ofReal (eigenvectorConstant K) + ENNReal.ofReal Cmid_α + ENNReal.ofReal Clow_α
          + ENNReal.ofReal partialConstant' + ENNReal.ofReal componentConstant' + ENNReal.ofReal crossRightConstant'
          + ENNReal.ofReal cutoffConstant' := by
    rw [hCagg_def, ENNReal.ofReal_add hp5 hCcut'_nn,
      ENNReal.ofReal_add hp4 hCcR'_nn,
      ENNReal.ofReal_add hp3 hCcom'_nn,
      ENNReal.ofReal_add hp2 hCpar'_nn,
      ENNReal.ofReal_add hp1 hClow_α_nn,
      ENNReal.ofReal_add (eigenvectorConstant_nonneg K) hCmid_α_nn]
  have h_sum_bound :
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
          (eigenvectorChartComponentFun (I := I) (M := M)
            g r s i α P₀)
          (chartTargetEuclid (I := I) (M := M) α)
        + (∑ β ∈ transportChartCenters (I := I) (M := M) α,
          ((∑ Q : TensorCompIdx (E := E) r s,
                iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K + 1) 2
                  (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                      (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                        (eigenvectorResolvent (I := I) (M := M)
                          g r s i))
                      β Q :
                      Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) :
                      EuclN → ℝ) y)
                  (chartTargetEuclid (I := I) (M := M) β))
            + ∑ β' ∈ transportChartCenters (I := I) (M := M) β,
                ∑ Q : TensorCompIdx (E := E) r s,
                  iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K + 1) 2
                    (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                        (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                          (eigenvectorResolvent (I := I) (M := M)
                            g r s i))
                        β' Q :
                        Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β')) :
                        EuclN → ℝ) y)
                    (chartTargetEuclid (I := I) (M := M) β')))
        + (∑ β ∈ transportChartCenters (I := I) (M := M) α,
          ∑ Q : TensorCompIdx (E := E) r s,
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                  (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                    (eigenvectorResolvent (I := I) (M := M) g r s i))
                  β Q : Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) :
                  EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β))
        + (∑ P : TensorCompIdx (E := E) r s,
          ∑ k : Fin (Module.finrank ℝ E),
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (fun y => ((partialLpLimit (I := I) (M := M)
                  g r s i α P k :
                Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
                EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) α))
        + (∑ p : TensorCompIdx (E := E) r s,
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((componentLpLimit (I := I) (M := M)
                g r s i α p :
              Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α))
        + (∑ P : TensorCompIdx (E := E) r s,
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((crossRightLimitComponent (I := I) (M := M)
                g r s i α P :
              Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α))
        + (∑ P : TensorCompIdx (E := E) r s,
          ∑ l : Fin (Module.finrank ℝ E),
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (fun y => ((cutoffPartialLpLimit (I := I) (M := M)
                  g r s i α P l :
                Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
                EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) α))
        ≤ ENNReal.ofReal Cagg * Rhs_effective := by
    rw [h_expand, add_mul, add_mul, add_mul, add_mul, add_mul, add_mul]
    refine add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
      (add_le_add ?_ hS2) hS3) hS4) hS5) hS6) hS7
    exact hS1
  refine h_sum_bound.trans (le_of_eq ?_)
  rw [hRhs_effective_def, ← mul_assoc, ← ENNReal.ofReal_mul hCagg_nn]

omit [CompleteSpace E] in
theorem diffRHSAggregate_le_energy_perK
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (l : Fin m → Fin (Module.finrank ℝ E))
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
      (P : TensorCompIdx (E := E) r s) (l : Fin (Module.finrank ℝ E)) (K' : ℕ),
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K' 2
          (fun y => ((cutoffPartialLpLimit (I := I) (M := M)
              g r s i α P l :
              Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (cutoffConstant K' * (i.fst.val)⁻¹ ^ (cutoffExponent K')) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖)
    (Citer : ℕ → ℝ) (eIter : ℕ → ℕ) (hCiter_nn : ∀ K', 0 ≤ Citer K')
    (hCiter_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s) (j : ℕ),
      j ≤ m + 1 → ∀ (idx : Fin j → Fin (Module.finrank ℝ E)) (K' : ℕ),
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (2 + K') 2
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ j idx)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (Citer K' * (i.fst.val)⁻¹ ^ (eIter K')) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖) :
    ∃ (C : ℝ) (e : ℕ), 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        diffRHSAggregate (I := I) (M := M)
            g r s i α P₀ m K l
          ≤ ENNReal.ofReal (C * (i.fst.val)⁻¹ ^ e) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i‖ := by
  classical
  set e_max : ℕ := (Finset.range (m + 2)).sup (fun j =>
      max (max (max (max (max (max (max (max
        (eigenvectorExponent (K + j)) (highResolventExponent (K + j))) (highResolventExponent (K + j + 1)))
        (lowResolventExponent (K + j))) (partialExponent (K + j))) (componentExponent (K + j))) (crossRightExponent (K + j)))
        (cutoffExponent (K + j))) (eIter (K + j))) with he_max_def
  have hEig_le : ∀ j ≤ m + 1, eigenvectorExponent (K + j) ≤ e_max := by
    intro j hj
    have hj_mem : j ∈ Finset.range (m + 2) := Finset.mem_range.mpr (by omega)
    refine le_trans ?_ (Finset.le_sup (f := fun j' =>
      max (max (max (max (max (max (max (max
        (eigenvectorExponent (K + j')) (highResolventExponent (K + j'))) (highResolventExponent (K + j' + 1)))
        (lowResolventExponent (K + j'))) (partialExponent (K + j'))) (componentExponent (K + j'))) (crossRightExponent (K + j')))
        (cutoffExponent (K + j'))) (eIter (K + j'))) hj_mem)
    refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_left _ _); refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_left _ _); refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_left _ _); refine le_trans ?_ (le_max_left _ _)
    exact le_max_left _ _
  have hResH_le : ∀ j ≤ m + 1, highResolventExponent (K + j) ≤ e_max := by
    intro j hj
    have hj_mem : j ∈ Finset.range (m + 2) := Finset.mem_range.mpr (by omega)
    refine le_trans ?_ (Finset.le_sup (f := fun j' =>
      max (max (max (max (max (max (max (max
        (eigenvectorExponent (K + j')) (highResolventExponent (K + j'))) (highResolventExponent (K + j' + 1)))
        (lowResolventExponent (K + j'))) (partialExponent (K + j'))) (componentExponent (K + j'))) (crossRightExponent (K + j')))
        (cutoffExponent (K + j'))) (eIter (K + j'))) hj_mem)
    refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_left _ _); refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_left _ _); refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_left _ _); refine le_trans ?_ (le_max_left _ _)
    exact le_max_right _ _
  have hResH1_le : ∀ j ≤ m + 1, highResolventExponent (K + j + 1) ≤ e_max := by
    intro j hj
    have hj_mem : j ∈ Finset.range (m + 2) := Finset.mem_range.mpr (by omega)
    refine le_trans ?_ (Finset.le_sup (f := fun j' =>
      max (max (max (max (max (max (max (max
        (eigenvectorExponent (K + j')) (highResolventExponent (K + j'))) (highResolventExponent (K + j' + 1)))
        (lowResolventExponent (K + j'))) (partialExponent (K + j'))) (componentExponent (K + j'))) (crossRightExponent (K + j')))
        (cutoffExponent (K + j'))) (eIter (K + j'))) hj_mem)
    refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_left _ _); refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_left _ _); refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_left _ _); exact le_max_right _ _
  have hResL_le : ∀ j ≤ m + 1, lowResolventExponent (K + j) ≤ e_max := by
    intro j hj
    have hj_mem : j ∈ Finset.range (m + 2) := Finset.mem_range.mpr (by omega)
    refine le_trans ?_ (Finset.le_sup (f := fun j' =>
      max (max (max (max (max (max (max (max
        (eigenvectorExponent (K + j')) (highResolventExponent (K + j'))) (highResolventExponent (K + j' + 1)))
        (lowResolventExponent (K + j'))) (partialExponent (K + j'))) (componentExponent (K + j'))) (crossRightExponent (K + j')))
        (cutoffExponent (K + j'))) (eIter (K + j'))) hj_mem)
    refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_left _ _); refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_left _ _); refine le_trans ?_ (le_max_left _ _)
    exact le_max_right _ _
  have hPar_le : ∀ j ≤ m + 1, partialExponent (K + j) ≤ e_max := by
    intro j hj
    have hj_mem : j ∈ Finset.range (m + 2) := Finset.mem_range.mpr (by omega)
    refine le_trans ?_ (Finset.le_sup (f := fun j' =>
      max (max (max (max (max (max (max (max
        (eigenvectorExponent (K + j')) (highResolventExponent (K + j'))) (highResolventExponent (K + j' + 1)))
        (lowResolventExponent (K + j'))) (partialExponent (K + j'))) (componentExponent (K + j'))) (crossRightExponent (K + j')))
        (cutoffExponent (K + j'))) (eIter (K + j'))) hj_mem)
    refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_left _ _); refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_left _ _); exact le_max_right _ _
  have hCom_le : ∀ j ≤ m + 1, componentExponent (K + j) ≤ e_max := by
    intro j hj
    have hj_mem : j ∈ Finset.range (m + 2) := Finset.mem_range.mpr (by omega)
    refine le_trans ?_ (Finset.le_sup (f := fun j' =>
      max (max (max (max (max (max (max (max
        (eigenvectorExponent (K + j')) (highResolventExponent (K + j'))) (highResolventExponent (K + j' + 1)))
        (lowResolventExponent (K + j'))) (partialExponent (K + j'))) (componentExponent (K + j'))) (crossRightExponent (K + j')))
        (cutoffExponent (K + j'))) (eIter (K + j'))) hj_mem)
    refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_left _ _); refine le_trans ?_ (le_max_left _ _)
    exact le_max_right _ _
  have hCcR_le : ∀ j ≤ m + 1, crossRightExponent (K + j) ≤ e_max := by
    intro j hj
    have hj_mem : j ∈ Finset.range (m + 2) := Finset.mem_range.mpr (by omega)
    refine le_trans ?_ (Finset.le_sup (f := fun j' =>
      max (max (max (max (max (max (max (max
        (eigenvectorExponent (K + j')) (highResolventExponent (K + j'))) (highResolventExponent (K + j' + 1)))
        (lowResolventExponent (K + j'))) (partialExponent (K + j'))) (componentExponent (K + j'))) (crossRightExponent (K + j')))
        (cutoffExponent (K + j'))) (eIter (K + j'))) hj_mem)
    refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_left _ _); exact le_max_right _ _
  have hCcut_le : ∀ j ≤ m + 1, cutoffExponent (K + j) ≤ e_max := by
    intro j hj
    have hj_mem : j ∈ Finset.range (m + 2) := Finset.mem_range.mpr (by omega)
    refine le_trans ?_ (Finset.le_sup (f := fun j' =>
      max (max (max (max (max (max (max (max
        (eigenvectorExponent (K + j')) (highResolventExponent (K + j'))) (highResolventExponent (K + j' + 1)))
        (lowResolventExponent (K + j'))) (partialExponent (K + j'))) (componentExponent (K + j'))) (crossRightExponent (K + j')))
        (cutoffExponent (K + j'))) (eIter (K + j'))) hj_mem)
    refine le_trans ?_ (le_max_left _ _); exact le_max_right _ _
  have hIter_le : ∀ j ≤ m + 1, eIter (K + j) ≤ e_max := by
    intro j hj
    have hj_mem : j ∈ Finset.range (m + 2) := Finset.mem_range.mpr (by omega)
    refine le_trans ?_ (Finset.le_sup (f := fun j' =>
      max (max (max (max (max (max (max (max
        (eigenvectorExponent (K + j')) (highResolventExponent (K + j'))) (highResolventExponent (K + j' + 1)))
        (lowResolventExponent (K + j'))) (partialExponent (K + j'))) (componentExponent (K + j'))) (crossRightExponent (K + j')))
        (cutoffExponent (K + j'))) (eIter (K + j'))) hj_mem)
    exact le_max_right _ _
  obtain ⟨Cbase_m, eBase_m, hCbase_m_nn, hCbase_m_bd⟩ :=
    rhsZeroAggregate_le_energy_perK (I := I) (M := M)
      g r s α P₀ (K + m)
      eigenvectorConstant eigenvectorExponent eigenvectorConstant_nonneg eigenvector_bound
      highResolventConstant highResolventExponent highResolventConstant_nonneg highResolvent_bound
      lowResolventConstant lowResolventExponent lowResolventConstant_nonneg lowResolvent_bound
      partialConstant partialExponent partialConstant_nonneg partial_bound
      componentConstant componentExponent componentConstant_nonneg component_bound
      crossRightConstant crossRightExponent crossRightConstant_nonneg crossRight_bound
      cutoffConstant cutoffExponent cutoffConstant_nonneg cutoff_bound
  refine ⟨Cbase_m + (m : ℝ) *
      (((Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) + 1) *
        (Finset.range (m + 1)).sup' ⟨0, by simp⟩ (fun j => Citer (K + j))),
    max eBase_m e_max, ?_, fun i => ?_⟩
  · have h0 : 0 ≤ (m : ℝ) := by exact_mod_cast Nat.zero_le _
    have h1 : (0 : ℝ) ≤ (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) := by
        exact_mod_cast Nat.zero_le _
      linarith
    have h2 : 0 ≤ (Finset.range (m + 1)).sup' ⟨0, by simp⟩
        (fun j => Citer (K + j)) := by
      have h_mem : (0 : ℕ) ∈ Finset.range (m + 1) :=
        Finset.mem_range.mpr (by omega)
      have h_at_zero :
          Citer (K + 0) ≤ (Finset.range (m + 1)).sup'
              ⟨0, by simp⟩ (fun j => Citer (K + j)) :=
        Finset.le_sup' (fun j => Citer (K + j)) h_mem
      exact (hCiter_nn (K + 0)).trans h_at_zero
    exact add_nonneg hCbase_m_nn (mul_nonneg h0 (mul_nonneg h1 h2))
  have hμ_pos : 0 < i.fst.val :=
    eigenvalue_pos (I := I) (M := M) g r s i
  have hμ_le_one : i.fst.val ≤ 1 :=
    eigenvalue_le_one (I := I) (M := M) g r s i
  have hμ_inv_nn : 0 ≤ (i.fst.val)⁻¹ := le_of_lt (inv_pos.mpr hμ_pos)
  have hμ_inv_ge_one : (1 : ℝ) ≤ (i.fst.val)⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hμ_pos]; simpa using hμ_le_one
  have hpow_dom : ∀ a b, a ≤ b → (i.fst.val)⁻¹ ^ a ≤ (i.fst.val)⁻¹ ^ b :=
    fun _a _b hab => pow_le_pow_right₀ hμ_inv_ge_one hab
  set e_out : ℕ := max eBase_m e_max with he_out_def
  set Rhs : ℝ≥0∞ := ENNReal.ofReal
      ‖tensorResolventEigenbasisVec (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M)
          g r s) i‖ with hRhs_def
  set Rhs_effective : ℝ≥0∞ := ENNReal.ofReal ((i.fst.val)⁻¹ ^ e_out) * Rhs
    with hRhs_effective_def
  have h_bridge : ∀ (w : ℝ≥0∞) (Cval : ℝ) (a : ℕ),
      0 ≤ Cval → a ≤ e_out →
      w ≤ ENNReal.ofReal (Cval * (i.fst.val)⁻¹ ^ a) * Rhs →
      w ≤ ENNReal.ofReal Cval * Rhs_effective := by
    intro w Cval a hCval_nn ha hw
    have hpow_le : (i.fst.val)⁻¹ ^ a ≤ (i.fst.val)⁻¹ ^ e_out := hpow_dom a e_out ha
    have hCmul_le : Cval * (i.fst.val)⁻¹ ^ a ≤ Cval * (i.fst.val)⁻¹ ^ e_out :=
      mul_le_mul_of_nonneg_left hpow_le hCval_nn
    have h_eNN_le : ENNReal.ofReal (Cval * (i.fst.val)⁻¹ ^ a)
          ≤ ENNReal.ofReal (Cval * (i.fst.val)⁻¹ ^ e_out) :=
      ENNReal.ofReal_le_ofReal hCmul_le
    have h_step : w ≤ ENNReal.ofReal (Cval * (i.fst.val)⁻¹ ^ e_out) * Rhs := by
      refine hw.trans ?_
      exact mul_le_mul_of_nonneg_right h_eNN_le (by exact zero_le)
    have h_rw : ENNReal.ofReal (Cval * (i.fst.val)⁻¹ ^ e_out) * Rhs
          = ENNReal.ofReal Cval * Rhs_effective := by
      rw [hRhs_effective_def, ENNReal.ofReal_mul hCval_nn, mul_assoc]
    exact h_step.trans_eq h_rw
  have h_head_bound :
      ∀ (m'' K' : ℕ) (l' : Fin (m'' + 1) → Fin (Module.finrank ℝ E)),
        m'' + 1 ≤ m + 1 → eIter K' ≤ e_out →
        diffRHSHead (I := I) (M := M) g r s i α P₀ m'' K' l'
          ≤ ENNReal.ofReal
              (((Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) + 1) *
                Citer K') * Rhs_effective := by
    intro m'' K' l' hm''_le_succ h_eIter_le
    rw [diffRHSHead]
    have hm''_le : m'' ≤ m + 1 := Nat.le_of_succ_le hm''_le_succ
    have h_first_each : ∀ a ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ E))),
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (2 + K') 2
            (eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s i α P₀ (m'' + 1) (Fin.cons a (Fin.init l')))
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal (Citer K') * Rhs_effective := fun a _ha =>
      h_bridge _ (Citer K') (eIter K') (hCiter_nn K') h_eIter_le
        (hCiter_bd i (m'' + 1) hm''_le_succ (Fin.cons a (Fin.init l')) K')
    have h_first :
        (∑ a : Fin (Module.finrank ℝ E),
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (2 + K') 2
              (eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s i α P₀ (m'' + 1) (Fin.cons a (Fin.init l')))
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal
              ((Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) * Citer K') *
            Rhs_effective := by
      have h_sum := sum_le_of_le_ofReal_mul
        (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
        (fun a => iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (2 + K') 2
            (eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s i α P₀ (m'' + 1) (Fin.cons a (Fin.init l')))
            (chartTargetEuclid (I := I) (M := M) α))
        (fun _ => Citer K') Rhs_effective (fun _ _ => hCiter_nn K') h_first_each
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at h_sum
      exact h_sum
    have h_second :
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (2 + K') 2
            (eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s i α P₀ m'' (Fin.init l'))
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal (Citer K') * Rhs_effective :=
      h_bridge _ (Citer K') (eIter K') (hCiter_nn K') h_eIter_le
        (hCiter_bd i m'' hm''_le (Fin.init l') K')
    have h_total :
        (∑ a : Fin (Module.finrank ℝ E),
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (2 + K') 2
              (eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s i α P₀ (m'' + 1) (Fin.cons a (Fin.init l')))
              (chartTargetEuclid (I := I) (M := M) α))
          + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (2 + K') 2
              (eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s i α P₀ m'' (Fin.init l'))
              (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal
            ((Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) * Citer K') * Rhs_effective
          + ENNReal.ofReal (Citer K') * Rhs_effective := add_le_add h_first h_second
    refine h_total.trans (le_of_eq ?_)
    have hQ_nn : (0 : ℝ) ≤
        (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) * Citer K' := by
      have hQ : (0 : ℝ) ≤ (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) := by
        exact_mod_cast Nat.zero_le _
      exact mul_nonneg hQ (hCiter_nn K')
    rw [← add_mul, ← ENNReal.ofReal_add hQ_nn (hCiter_nn K')]
    congr 2
    ring
  have h_base_at_Km :
      rhsZeroAggregate (I := I) (M := M) g r s i α P₀ (K + m)
        ≤ ENNReal.ofReal Cbase_m * Rhs_effective :=
    h_bridge _ Cbase_m eBase_m hCbase_m_nn (le_max_left _ _)
      (hCbase_m_bd i)
  set Chead_max : ℝ :=
      ((Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) + 1) *
        (Finset.range (m + 1)).sup' ⟨0, by simp⟩ (fun j => Citer (K + j))
    with hChead_max_def
  have hChead_max_nn : 0 ≤ Chead_max := by
    have h1 : (0 : ℝ) ≤ (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) := by
        exact_mod_cast Nat.zero_le _
      linarith
    have h2 : 0 ≤ (Finset.range (m + 1)).sup' ⟨0, by simp⟩
        (fun j => Citer (K + j)) := by
      have h_at_zero :
          Citer (K + 0) ≤ (Finset.range (m + 1)).sup'
              ⟨0, by simp⟩ (fun j => Citer (K + j)) :=
        Finset.le_sup' (fun j => Citer (K + j))
          (Finset.mem_range.mpr (by omega))
      exact (hCiter_nn (K + 0)).trans h_at_zero
    exact mul_nonneg h1 h2
  have h_bare :
      ∀ (m'' : ℕ), m'' ≤ m → ∀ (l' : Fin m'' → Fin (Module.finrank ℝ E)),
        diffRHSAggregate (I := I) (M := M) g r s i α P₀
            m'' (K + (m - m'')) l'
          ≤ ENNReal.ofReal (Cbase_m + (m'' : ℝ) * Chead_max) * Rhs_effective := by
    intro m'' hm''_le l'
    induction m'' with
    | zero =>
        have : K + (m - 0) = K + m := by simp
        rw [this]
        rw [show diffRHSAggregate (I := I) (M := M)
              g r s i α P₀ 0 (K + m) l' =
            rhsZeroAggregate (I := I) (M := M)
              g r s i α P₀ (K + m) from rfl]
        have : ((0 : ℕ) : ℝ) * Chead_max = 0 := by simp
        rw [show (Cbase_m + ((0 : ℕ) : ℝ) * Chead_max) = Cbase_m from by
          rw [this]; ring]
        exact h_base_at_Km
    | succ m''' ih =>
        have hm'''_le : m''' ≤ m := Nat.le_of_succ_le hm''_le
        have h_pos : 1 ≤ m - m''' := by omega
        have h_shift : K + (m - (m''' + 1)) + 1 = K + (m - m''') := by
          have : m - (m''' + 1) + 1 = m - m''' := by omega
          omega
        rw [show diffRHSAggregate (I := I) (M := M)
              g r s i α P₀ (m''' + 1) (K + (m - (m''' + 1))) l' =
            diffRHSHead (I := I) (M := M)
              g r s i α P₀ m''' (K + (m - (m''' + 1))) l' +
              diffRHSAggregate (I := I) (M := M)
                g r s i α P₀ m''' (K + (m - (m''' + 1)) + 1)
                (Fin.init l') from rfl]
        have h_rec_eq :
            diffRHSAggregate (I := I) (M := M)
                g r s i α P₀ m''' (K + (m - (m''' + 1)) + 1)
                (Fin.init l')
              = diffRHSAggregate (I := I) (M := M)
                g r s i α P₀ m''' (K + (m - m''')) (Fin.init l') := by
          rw [h_shift]
        rw [h_rec_eq]
        have h_rec := ih hm'''_le (Fin.init l')
        have h_eIter_le_local : eIter (K + (m - (m''' + 1))) ≤ e_out := by
          have h_idx : m - (m''' + 1) ≤ m + 1 := by omega
          have h_in := hIter_le (m - (m''' + 1)) h_idx
          exact h_in.trans (le_max_right _ _)
        have hm'''_succ_le : m''' + 1 ≤ m + 1 := by omega
        have h_head := h_head_bound m''' (K + (m - (m''' + 1))) l'
          hm'''_succ_le h_eIter_le_local
        have h_in_range : m - (m''' + 1) ∈ Finset.range (m + 1) :=
          Finset.mem_range.mpr (by omega)
        have h_Citer_le :
            Citer (K + (m - (m''' + 1)))
              ≤ (Finset.range (m + 1)).sup' ⟨0, by simp⟩
                  (fun j => Citer (K + j)) :=
          Finset.le_sup' (fun j => Citer (K + j)) h_in_range
        have h_card_nn : (0 : ℝ) ≤
            (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) + 1 := by
          have : (0 : ℝ) ≤ (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) := by
            exact_mod_cast Nat.zero_le _
          linarith
        have h_upgrade_real :
            ((Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) + 1) *
                Citer (K + (m - (m''' + 1)))
              ≤ Chead_max := by
          rw [hChead_max_def]
          exact mul_le_mul_of_nonneg_left h_Citer_le h_card_nn
        have h_upgrade :
            ENNReal.ofReal
                (((Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) + 1) *
                  Citer (K + (m - (m''' + 1))))
              ≤ ENNReal.ofReal Chead_max := ENNReal.ofReal_le_ofReal h_upgrade_real
        have h_head_up :
            diffRHSHead (I := I) (M := M) g r s i α P₀
                m''' (K + (m - (m''' + 1))) l'
              ≤ ENNReal.ofReal Chead_max * Rhs_effective := by
          refine h_head.trans ?_
          exact mul_le_mul_of_nonneg_right h_upgrade (by exact zero_le)
        have h_combine :
            diffRHSHead (I := I) (M := M) g r s i α P₀
                m''' (K + (m - (m''' + 1))) l'
              + diffRHSAggregate (I := I) (M := M)
                  g r s i α P₀ m''' (K + (m - m''')) (Fin.init l')
            ≤ ENNReal.ofReal Chead_max * Rhs_effective
                + ENNReal.ofReal (Cbase_m + (m''' : ℝ) * Chead_max) * Rhs_effective :=
          add_le_add h_head_up h_rec
        refine h_combine.trans (le_of_eq ?_)
        have hCprev_nn : 0 ≤ Cbase_m + (m''' : ℝ) * Chead_max := by
          have hm''' : (0 : ℝ) ≤ (m''' : ℝ) := by exact_mod_cast Nat.zero_le _
          exact add_nonneg hCbase_m_nn (mul_nonneg hm''' hChead_max_nn)
        rw [← add_mul, ← ENNReal.ofReal_add hChead_max_nn hCprev_nn]
        congr 2
        push_cast
        ring
  have h_at_m := h_bare m (le_refl _) l
  have h_K_eq : K + (m - m) = K := by simp
  rw [h_K_eq] at h_at_m
  have hCtotal_nn : 0 ≤ Cbase_m + (m : ℝ) * Chead_max := by
    have hm_nn : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.zero_le _
    exact add_nonneg hCbase_m_nn (mul_nonneg hm_nn hChead_max_nn)
  have h_rw_back :
      ENNReal.ofReal (Cbase_m + (m : ℝ) * Chead_max) * Rhs_effective
        = ENNReal.ofReal ((Cbase_m + (m : ℝ) * Chead_max) *
              (i.fst.val)⁻¹ ^ e_out) * Rhs := by
    rw [hRhs_effective_def, ← mul_assoc, ← ENNReal.ofReal_mul hCtotal_nn]
  exact h_at_m.trans_eq h_rw_back

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
