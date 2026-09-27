import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.RightHandSide.Differentiated.Eigenvalue.SharpSobolevBounds
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

open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl
open DifferentialGeometry.Analysis.Sobolev.Chart
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

section MainResults

open DifferentialGeometry.Analysis.Spectral in
structure EigenvectorChartRightHandSideDifferentiatedSharpWkpBoundsUpToOrder
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (N : ℕ) where
  resolventComponentRegularity : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s) (K' : ℕ)
    (β : M) (Q : TensorCompIdx (E := E) r s),
    K' ≤ N →
    MemWkp (d := Module.finrank ℝ E) K' 2
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M) g r s i))
          β Q : Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) :
          EuclN → ℝ) y)
      (chartTargetEuclid (I := I) (M := M) β)
  eigenvectorConstant : ℕ → ℝ
  eigenvectorExponent : ℕ → ℕ
  eigenvectorConstant_nonneg : ∀ K', 0 ≤ eigenvectorConstant K'
  eigenvector_bound : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s) (K' : ℕ),
    K' ≤ N →
    iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K' 2
        (eigenvectorChartComponentFun (I := I) (M := M)
          g r s i α P₀)
        (chartTargetEuclid (I := I) (M := M) α)
      ≤ ENNReal.ofReal (eigenvectorConstant K' * (i.fst.val)⁻¹ ^ (eigenvectorExponent K')) *
        ENNReal.ofReal
          ‖tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M)
              g r s) i‖
  highResolventConstant : ℕ → ℝ
  highResolventExponent : ℕ → ℕ
  highResolventConstant_nonneg : ∀ K', 0 ≤ highResolventConstant K'
  highResolvent_bound : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
    (β : M) (Q : TensorCompIdx (E := E) r s) (K' : ℕ),
    K' + 1 ≤ N →
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
              g r s) i‖
  lowResolventConstant : ℕ → ℝ
  lowResolventExponent : ℕ → ℕ
  lowResolventConstant_nonneg : ∀ K', 0 ≤ lowResolventConstant K'
  lowResolvent_bound : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
    (β : M) (Q : TensorCompIdx (E := E) r s) (K' : ℕ),
    K' ≤ N →
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
              g r s) i‖
  partialConstant : ℕ → ℝ
  partialExponent : ℕ → ℕ
  partialConstant_nonneg : ∀ K', 0 ≤ partialConstant K'
  partial_bound : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
    (P : TensorCompIdx (E := E) r s) (k : Fin (Module.finrank ℝ E)) (K' : ℕ),
    K' + 1 ≤ N →
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
              g r s) i‖
  componentConstant : ℕ → ℝ
  componentExponent : ℕ → ℕ
  componentConstant_nonneg : ∀ K', 0 ≤ componentConstant K'
  component_bound : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
    (p : TensorCompIdx (E := E) r s) (K' : ℕ),
    K' ≤ N →
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
              g r s) i‖
  crossRightConstant : ℕ → ℝ
  crossRightExponent : ℕ → ℕ
  crossRightConstant_nonneg : ∀ K', 0 ≤ crossRightConstant K'
  crossRight_bound : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
    (P : TensorCompIdx (E := E) r s) (K' : ℕ),
    K' ≤ N →
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
              g r s) i‖
  cutoffConstant : ℕ → ℝ
  cutoffExponent : ℕ → ℕ
  cutoffConstant_nonneg : ∀ K', 0 ≤ cutoffConstant K'
  cutoff_bound : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
    (P : TensorCompIdx (E := E) r s) (l : Fin (Module.finrank ℝ E)) (K' : ℕ),
    K' + 1 ≤ N →
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
              g r s) i‖

open DifferentialGeometry.Analysis.Spectral in
omit [CompleteSpace E] in
private lemma sharpDiffBdd_diff_memWkp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (N : ℕ)
    (H : EigenvectorChartRightHandSideDifferentiatedSharpWkpBoundsUpToOrder (I := I) (M := M) g r s α P₀ N)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (m K' : ℕ) (hN : m + 1 + K' ≤ N) (l : Fin m → Fin (Module.finrank ℝ E)) :
    MemWkp (d := Module.finrank ℝ E) K' 2
      (eigenvectorChartRHSDiff (I := I) (M := M) g r s i α P₀ m l)
      (chartTargetEuclid (I := I) (M := M) α) :=
  eigenvectorChartRHSDiff_memWkp (I := I) (M := M) g r s i α P₀
    m K' l (fun β Q => H.resolventComponentRegularity i (m + 1 + K') β Q hN)

open DifferentialGeometry.Analysis.Spectral in
omit [CompleteSpace E] in
lemma rhsZeroAggregate_le_energy_perK_bdd
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (K N : ℕ)
    (hKN : K + 1 ≤ N)
    (H : EigenvectorChartRightHandSideDifferentiatedSharpWkpBoundsUpToOrder (I := I) (M := M) g r s α P₀ N) :
    ∃ (C : ℝ) (e : ℕ), 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        rhsZeroAggregate (I := I) (M := M) g r s i α P₀ K
          ≤ ENNReal.ofReal (C * (i.fst.val)⁻¹ ^ e) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i‖ := by
  classical
  have hK_le_N : K ≤ N := by omega
  set Cqtot : ℝ := (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) * H.highResolventConstant K
    with hCqtot_def
  set Cmid_α : ℝ := (transportChartCenters (I := I) (M := M) α).sum fun β =>
        Cqtot + ((transportChartCenters (I := I) (M := M) β).card : ℝ) * Cqtot
    with hCmid_α_def
  set Clow_α : ℝ :=
    ((transportChartCenters (I := I) (M := M) α).card : ℝ) *
      ((Fintype.card (TensorCompIdx (E := E) r s) : ℝ) * H.lowResolventConstant K) with hClow_α_def
  set partialConstant' : ℝ := (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) *
        ((Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) * H.partialConstant K) with hCpar'_def
  set componentConstant' : ℝ := (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) * H.componentConstant K
    with hCcom'_def
  set crossRightConstant' : ℝ := (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) * H.crossRightConstant K
    with hCcR'_def
  set cutoffConstant' : ℝ := (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) *
        ((Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) * H.cutoffConstant K) with hCcut'_def
  set Cagg : ℝ := H.eigenvectorConstant K + Cmid_α + Clow_α + partialConstant' + componentConstant' + crossRightConstant' + cutoffConstant'
    with hCagg_def
  set e_max : ℕ :=
    max (max (max (max (max (max (max
      (H.eigenvectorExponent K) (H.highResolventExponent K)) (H.highResolventExponent (K + 1))) (H.lowResolventExponent K)) (H.partialExponent K))
      (H.componentExponent K)) (H.crossRightExponent K)) (H.cutoffExponent K) with he_max_def
  have hCqtot_nn : 0 ≤ Cqtot := by
    have : (0 : ℝ) ≤ (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) := by
      exact_mod_cast Nat.zero_le _
    exact mul_nonneg this (H.highResolventConstant_nonneg K)
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
    exact mul_nonneg hT (mul_nonneg hQ (H.lowResolventConstant_nonneg K))
  have hCpar'_nn : 0 ≤ partialConstant' := by
    have hQ : (0 : ℝ) ≤ (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) := by
      exact_mod_cast Nat.zero_le _
    have hk : (0 : ℝ) ≤ (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) := by
      exact_mod_cast Nat.zero_le _
    exact mul_nonneg hQ (mul_nonneg hk (H.partialConstant_nonneg K))
  have hCcom'_nn : 0 ≤ componentConstant' := by
    have hQ : (0 : ℝ) ≤ (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) := by
      exact_mod_cast Nat.zero_le _
    exact mul_nonneg hQ (H.componentConstant_nonneg K)
  have hCcR'_nn : 0 ≤ crossRightConstant' := by
    have hQ : (0 : ℝ) ≤ (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) := by
      exact_mod_cast Nat.zero_le _
    exact mul_nonneg hQ (H.crossRightConstant_nonneg K)
  have hCcut'_nn : 0 ≤ cutoffConstant' := by
    have hQ : (0 : ℝ) ≤ (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) := by
      exact_mod_cast Nat.zero_le _
    have hk : (0 : ℝ) ≤ (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) := by
      exact_mod_cast Nat.zero_le _
    exact mul_nonneg hQ (mul_nonneg hk (H.cutoffConstant_nonneg K))
  have hCagg_nn : 0 ≤ Cagg := by
    refine add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg
      (add_nonneg ?_ hCmid_α_nn) hClow_α_nn) hCpar'_nn) hCcom'_nn) hCcR'_nn) hCcut'_nn
    exact H.eigenvectorConstant_nonneg K
  refine ⟨Cagg, e_max, hCagg_nn, fun i => ?_⟩
  have hvec_norm : ‖tensorResolventEigenbasisVec (I := I) (M := M)
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s) i‖
      = 1 :=
    (tensorResolventEigenbasisVec_orthonormal (I := I) (M := M)
      (g := g) (r := r) (s := s)
      (tensorResolventL2_isCompactOperator (I := I) (M := M)
        g r s)).norm_eq_one i
  have hμ_unit : i.fst.val ∈ Set.Ioc (0 : ℝ) 1 :=
    tensorResolvent_eigenvalue_mem_unit_interval (I := I) (M := M) g r s
      (tensorResolventEigenbasisVec_mem (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M)
          g r s) i)
      (by
        intro h_zero
        rw [h_zero, norm_zero] at hvec_norm
        exact one_ne_zero hvec_norm.symm)
  have hμ_pos : 0 < i.fst.val := hμ_unit.1
  have hμ_le_one : i.fst.val ≤ 1 := hμ_unit.2
  have hμ_inv_ge_one : (1 : ℝ) ≤ (i.fst.val)⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hμ_pos]; simpa using hμ_le_one
  have hEig_le : H.eigenvectorExponent K ≤ e_max := by
    refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_left _ _); refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_left _ _); refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_left _ _); exact le_max_left _ _
  have hResH_le : H.highResolventExponent K ≤ e_max := by
    refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_left _ _); refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_left _ _); refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_left _ _); exact le_max_right _ _
  have hResL_le : H.lowResolventExponent K ≤ e_max := by
    refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_left _ _); refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_left _ _); exact le_max_right _ _
  have hPar_le : H.partialExponent K ≤ e_max := by
    refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_left _ _); refine le_trans ?_ (le_max_left _ _)
    exact le_max_right _ _
  have hCom_le : H.componentExponent K ≤ e_max := by
    refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_left _ _); exact le_max_right _ _
  have hCcR_le : H.crossRightExponent K ≤ e_max := by
    refine le_trans ?_ (le_max_left _ _); exact le_max_right _ _
  have hCcut_le : H.cutoffExponent K ≤ e_max := le_max_right _ _
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
        ≤ ENNReal.ofReal (H.eigenvectorConstant K) * Rhs_effective :=
    h_bridge _ (H.eigenvectorConstant K) (H.eigenvectorExponent K) (H.eigenvectorConstant_nonneg K) hEig_le
      (H.eigenvector_bound i K hK_le_N)
  have hS2_inner : ∀ β ∈ transportChartCenters (I := I) (M := M) α,
      ((∑ Q : TensorCompIdx (E := E) r s,
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K + 1) 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                  (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                    (eigenvectorResolvent (I := I) (M := M)
                      g r s i))
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
                    (eigenvectorResolvent (I := I) (M := M)
                      g r s i))
                  β Q : Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) :
                  EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β))
          ≤ ENNReal.ofReal Cqtot * Rhs_effective := by
      have h_each : ∀ Q ∈ (Finset.univ : Finset (TensorCompIdx (E := E) r s)),
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K + 1) 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                  (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                    (eigenvectorResolvent (I := I) (M := M)
                      g r s i))
                  β Q : Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) :
                  EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β)
            ≤ ENNReal.ofReal (H.highResolventConstant K) * Rhs_effective := fun Q _hQ =>
        h_bridge _ (H.highResolventConstant K) (H.highResolventExponent K) (H.highResolventConstant_nonneg K) hResH_le
          (H.highResolvent_bound i β Q K hKN)
      have h_sum := sum_le_of_le_ofReal_mul
        (Finset.univ : Finset (TensorCompIdx (E := E) r s))
        (fun Q => iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K + 1) 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                  (eigenvectorResolvent (I := I) (M := M)
                    g r s i))
                β Q : Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) :
                EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β))
        (fun _Q => H.highResolventConstant K) Rhs_effective (fun _ _ => H.highResolventConstant_nonneg K) h_each
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at h_sum
      exact h_sum.trans_eq (by rw [hCqtot_def])
    have h_inner_β' :
        (∑ β' ∈ transportChartCenters (I := I) (M := M) β,
          ∑ Q : TensorCompIdx (E := E) r s,
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K + 1) 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                  (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                    (eigenvectorResolvent (I := I) (M := M)
                      g r s i))
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
                      (eigenvectorResolvent (I := I) (M := M)
                        g r s i))
                    β' Q : Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β')) :
                    EuclN → ℝ) y)
                (chartTargetEuclid (I := I) (M := M) β'))
            ≤ ENNReal.ofReal Cqtot * Rhs_effective := by
        intro β' _hβ'
        have h_each : ∀ Q ∈ (Finset.univ : Finset (TensorCompIdx (E := E) r s)),
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K + 1) 2
                (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                    (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                      (eigenvectorResolvent (I := I) (M := M)
                        g r s i))
                    β' Q : Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β')) :
                    EuclN → ℝ) y)
                (chartTargetEuclid (I := I) (M := M) β')
              ≤ ENNReal.ofReal (H.highResolventConstant K) * Rhs_effective := fun Q _hQ =>
          h_bridge _ (H.highResolventConstant K) (H.highResolventExponent K) (H.highResolventConstant_nonneg K) hResH_le
            (H.highResolvent_bound i β' Q K hKN)
        have h_sum := sum_le_of_le_ofReal_mul
          (Finset.univ : Finset (TensorCompIdx (E := E) r s))
          (fun Q => iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K + 1) 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                  (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                    (eigenvectorResolvent (I := I) (M := M)
                      g r s i))
                  β' Q : Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β')) :
                  EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β'))
          (fun _Q => H.highResolventConstant K) Rhs_effective (fun _ _ => H.highResolventConstant_nonneg K) h_each
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at h_sum
        exact h_sum.trans_eq (by rw [hCqtot_def])
      have h_sum := sum_le_of_le_ofReal_mul
        (transportChartCenters (I := I) (M := M) β)
        (fun β' => ∑ Q : TensorCompIdx (E := E) r s,
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K + 1) 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                  (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                    (eigenvectorResolvent (I := I) (M := M)
                      g r s i))
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
                      (eigenvectorResolvent (I := I) (M := M)
                        g r s i))
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
                    (eigenvectorResolvent (I := I) (M := M)
                      g r s i))
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
                  (eigenvectorResolvent (I := I) (M := M)
                    g r s i))
                β Q : Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) :
                EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β))
      ≤ ENNReal.ofReal Clow_α * Rhs_effective := by
    have h_perβ : ∀ β ∈ transportChartCenters (I := I) (M := M) α,
        (∑ Q : TensorCompIdx (E := E) r s,
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                  (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                    (eigenvectorResolvent (I := I) (M := M)
                      g r s i))
                  β Q : Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) :
                  EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β))
          ≤ ENNReal.ofReal
              ((Fintype.card (TensorCompIdx (E := E) r s) : ℝ) * H.lowResolventConstant K) *
            Rhs_effective := by
      intro β _hβ
      have h_each : ∀ Q ∈ (Finset.univ : Finset (TensorCompIdx (E := E) r s)),
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                  (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                    (eigenvectorResolvent (I := I) (M := M)
                      g r s i))
                  β Q : Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) :
                  EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β)
            ≤ ENNReal.ofReal (H.lowResolventConstant K) * Rhs_effective := fun Q _hQ =>
        h_bridge _ (H.lowResolventConstant K) (H.lowResolventExponent K) (H.lowResolventConstant_nonneg K) hResL_le
          (H.lowResolvent_bound i β Q K hK_le_N)
      have h_sum := sum_le_of_le_ofReal_mul
        (Finset.univ : Finset (TensorCompIdx (E := E) r s))
        (fun Q => iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                  (eigenvectorResolvent (I := I) (M := M)
                    g r s i))
                β Q : Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) :
                EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β))
        (fun _Q => H.lowResolventConstant K) Rhs_effective (fun _ _ => H.lowResolventConstant_nonneg K) h_each
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at h_sum
      exact h_sum
    have hQ_nn : (0 : ℝ) ≤
        (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) * H.lowResolventConstant K := by
      have hQ : (0 : ℝ) ≤ (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) := by
        exact_mod_cast Nat.zero_le _
      exact mul_nonneg hQ (H.lowResolventConstant_nonneg K)
    have h_sum := sum_le_of_le_ofReal_mul
      (transportChartCenters (I := I) (M := M) α)
      (fun β => ∑ Q : TensorCompIdx (E := E) r s,
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                  (eigenvectorResolvent (I := I) (M := M)
                    g r s i))
                β Q : Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) :
                EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β))
      (fun _β => (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) * H.lowResolventConstant K)
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
              ((Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) * H.partialConstant K) *
            Rhs_effective := by
      intro P _hP
      have h_each : ∀ k ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ E))),
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (fun y => ((partialLpLimit (I := I) (M := M)
                  g r s i α P k :
                Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
                EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal (H.partialConstant K) * Rhs_effective := fun k _hk =>
        h_bridge _ (H.partialConstant K) (H.partialExponent K) (H.partialConstant_nonneg K) hPar_le
          (H.partial_bound i P k K hKN)
      have h_sum := sum_le_of_le_ofReal_mul
        (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
        (fun k => iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((partialLpLimit (I := I) (M := M)
                g r s i α P k :
              Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α))
        (fun _k => H.partialConstant K) Rhs_effective (fun _ _ => H.partialConstant_nonneg K) h_each
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at h_sum
      exact h_sum
    have hk_nn : (0 : ℝ) ≤
        (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) * H.partialConstant K := by
      have hk : (0 : ℝ) ≤ (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) := by
        exact_mod_cast Nat.zero_le _
      exact mul_nonneg hk (H.partialConstant_nonneg K)
    have h_sum := sum_le_of_le_ofReal_mul
      (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun P => ∑ k : Fin (Module.finrank ℝ E),
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((partialLpLimit (I := I) (M := M)
                g r s i α P k :
              Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α))
      (fun _P => (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) * H.partialConstant K)
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
          ≤ ENNReal.ofReal (H.componentConstant K) * Rhs_effective := fun p _hp =>
      h_bridge _ (H.componentConstant K) (H.componentExponent K) (H.componentConstant_nonneg K) hCom_le
        (H.component_bound i p K hK_le_N)
    have h_sum := sum_le_of_le_ofReal_mul
      (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun p => iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
          (fun y => ((componentLpLimit (I := I) (M := M)
              g r s i α p :
            Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
            EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α))
      (fun _p => H.componentConstant K) Rhs_effective (fun _ _ => H.componentConstant_nonneg K) h_each
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
          ≤ ENNReal.ofReal (H.crossRightConstant K) * Rhs_effective := fun P _hP =>
      h_bridge _ (H.crossRightConstant K) (H.crossRightExponent K) (H.crossRightConstant_nonneg K) hCcR_le
        (H.crossRight_bound i P K hK_le_N)
    have h_sum := sum_le_of_le_ofReal_mul
      (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun P => iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
          (fun y => ((crossRightLimitComponent (I := I) (M := M)
              g r s i α P :
            Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
            EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α))
      (fun _P => H.crossRightConstant K) Rhs_effective (fun _ _ => H.crossRightConstant_nonneg K) h_each
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
              ((Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) * H.cutoffConstant K) *
            Rhs_effective := by
      intro P _hP
      have h_each : ∀ l ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ E))),
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (fun y => ((cutoffPartialLpLimit (I := I) (M := M)
                  g r s i α P l :
                Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
                EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal (H.cutoffConstant K) * Rhs_effective := fun l _hl =>
        h_bridge _ (H.cutoffConstant K) (H.cutoffExponent K) (H.cutoffConstant_nonneg K) hCcut_le
          (H.cutoff_bound i P l K hKN)
      have h_sum := sum_le_of_le_ofReal_mul
        (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
        (fun l => iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((cutoffPartialLpLimit (I := I) (M := M)
                g r s i α P l :
              Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α))
        (fun _l => H.cutoffConstant K) Rhs_effective (fun _ _ => H.cutoffConstant_nonneg K) h_each
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at h_sum
      exact h_sum
    have hk_nn : (0 : ℝ) ≤
        (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) * H.cutoffConstant K := by
      have hk : (0 : ℝ) ≤ (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) := by
        exact_mod_cast Nat.zero_le _
      exact mul_nonneg hk (H.cutoffConstant_nonneg K)
    have h_sum := sum_le_of_le_ofReal_mul
      (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun P => ∑ l : Fin (Module.finrank ℝ E),
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((cutoffPartialLpLimit (I := I) (M := M)
                g r s i α P l :
              Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α))
      (fun _P => (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) * H.cutoffConstant K)
      Rhs_effective (fun _ _ => hk_nn) h_perP
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at h_sum
    exact h_sum.trans_eq (by rw [hCcut'_def])
  rw [rhsZeroAggregate]
  have hp1 : 0 ≤ H.eigenvectorConstant K + Cmid_α := add_nonneg (H.eigenvectorConstant_nonneg K) hCmid_α_nn
  have hp2 : 0 ≤ H.eigenvectorConstant K + Cmid_α + Clow_α := add_nonneg hp1 hClow_α_nn
  have hp3 : 0 ≤ H.eigenvectorConstant K + Cmid_α + Clow_α + partialConstant' := add_nonneg hp2 hCpar'_nn
  have hp4 : 0 ≤ H.eigenvectorConstant K + Cmid_α + Clow_α + partialConstant' + componentConstant' :=
    add_nonneg hp3 hCcom'_nn
  have hp5 : 0 ≤ H.eigenvectorConstant K + Cmid_α + Clow_α + partialConstant' + componentConstant' + crossRightConstant' :=
    add_nonneg hp4 hCcR'_nn
  have h_expand :
      ENNReal.ofReal Cagg
        = ENNReal.ofReal (H.eigenvectorConstant K) + ENNReal.ofReal Cmid_α
          + ENNReal.ofReal Clow_α + ENNReal.ofReal partialConstant' + ENNReal.ofReal componentConstant'
          + ENNReal.ofReal crossRightConstant' + ENNReal.ofReal cutoffConstant' := by
    rw [hCagg_def, ENNReal.ofReal_add hp5 hCcut'_nn,
      ENNReal.ofReal_add hp4 hCcR'_nn,
      ENNReal.ofReal_add hp3 hCcom'_nn,
      ENNReal.ofReal_add hp2 hCpar'_nn,
      ENNReal.ofReal_add hp1 hClow_α_nn,
      ENNReal.ofReal_add (H.eigenvectorConstant_nonneg K) hCmid_α_nn]
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
                    (eigenvectorResolvent (I := I) (M := M)
                      g r s i))
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

open DifferentialGeometry.Analysis.Spectral in
omit [CompleteSpace E] in
private lemma sharpDiffBdd_level_zero_wkpNorm
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (K N : ℕ)
    (hKN : K + 1 ≤ N)
    (H : EigenvectorChartRightHandSideDifferentiatedSharpWkpBoundsUpToOrder (I := I) (M := M) g r s α P₀ N) :
    ∃ (C : ℝ) (e : ℕ), 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (eigenvectorChartRHS (I := I) (M := M) g r s i α P₀)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal (C * (i.fst.val)⁻¹ ^ e) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i‖ := by
  classical
  obtain ⟨Cagg, eAgg, hCagg_nn, hCagg_bd⟩ :=
    rhsZeroAggregate_le_energy_perK_bdd (I := I) (M := M)
      g r s α P₀ K N hKN H
  have h_pou : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β) := fun i β Q =>
    H.resolventComponentRegularity i (K + 1) β Q hKN
  obtain ⟨Cmu, hCmu_nn, hCmu_bd⟩ :=
    eigenvectorChartRHS_wkpNorm_le_uniform (I := I) (M := M)
      g r s α P₀ K h_pou
  refine ⟨Cmu * Cagg, eAgg + 1, mul_nonneg hCmu_nn hCagg_nn, fun i => ?_⟩
  have hμ_inv_nn : (0 : ℝ) ≤ (i.fst.val)⁻¹ :=
    sharpDiff_eigen_inv_nn (I := I) (M := M) g r s i
  have hμ_inv_pow_nn : (0 : ℝ) ≤ (i.fst.val)⁻¹ ^ eAgg :=
    pow_nonneg hμ_inv_nn _
  have hCmu_aux := hCmu_bd i
  have hCagg_aux := hCagg_bd i
  change iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
        (eigenvectorChartRHS (I := I) (M := M) g r s i α P₀)
        (chartTargetEuclid (I := I) (M := M) α)
      ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * Cmu) *
        rhsZeroAggregate (I := I) (M := M) g r s i α P₀ K
        at hCmu_aux
  refine le_trans hCmu_aux ?_
  refine le_trans (mul_le_mul' (le_refl _) hCagg_aux) ?_
  rw [show ENNReal.ofReal ((i.fst.val)⁻¹ * Cmu) =
      ENNReal.ofReal (i.fst.val)⁻¹ * ENNReal.ofReal Cmu from
    ENNReal.ofReal_mul hμ_inv_nn]
  rw [show ENNReal.ofReal (Cagg * (i.fst.val)⁻¹ ^ eAgg) =
      ENNReal.ofReal Cagg * ENNReal.ofReal ((i.fst.val)⁻¹ ^ eAgg) from
    ENNReal.ofReal_mul hCagg_nn]
  rw [show ENNReal.ofReal (Cmu * Cagg * (i.fst.val)⁻¹ ^ (eAgg + 1)) =
      ENNReal.ofReal Cmu * ENNReal.ofReal Cagg *
        ENNReal.ofReal ((i.fst.val)⁻¹ ^ eAgg) * ENNReal.ofReal (i.fst.val)⁻¹ by
    rw [show Cmu * Cagg * (i.fst.val)⁻¹ ^ (eAgg + 1) =
        Cmu * Cagg * (i.fst.val)⁻¹ ^ eAgg * (i.fst.val)⁻¹ from by ring,
      ENNReal.ofReal_mul (mul_nonneg (mul_nonneg hCmu_nn hCagg_nn) hμ_inv_pow_nn),
      ENNReal.ofReal_mul (mul_nonneg hCmu_nn hCagg_nn),
      ENNReal.ofReal_mul hCmu_nn]]
  ring_nf
  exact le_refl _

open DifferentialGeometry.Analysis.Spectral in
omit [CompleteSpace E] in
private lemma sharpDiffBdd_recursion
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (N : ℕ)
    (H : EigenvectorChartRightHandSideDifferentiatedSharpWkpBoundsUpToOrder (I := I) (M := M) g r s α P₀ N) :
    ∀ (m : ℕ) (K : ℕ) (_ : K + m + 1 ≤ N)
      (l : Fin m → Fin (Module.finrank ℝ E)),
      ∃ (C : ℝ) (e : ℕ), 0 ≤ C ∧
        ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (eigenvectorChartRHSDiff (I := I) (M := M)
                g r s i α P₀ m l)
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal (C * (i.fst.val)⁻¹ ^ e) *
              ENNReal.ofReal
                ‖tensorResolventEigenbasisVec (I := I) (M := M)
                  (tensorResolventL2_isCompactOperator (I := I) (M := M)
                    g r s) i‖ := by
  classical
  intro m
  induction m with
  | zero =>
      intro K hKN _l
      have hK1_le_N : K + 1 ≤ N := by simpa using hKN
      obtain ⟨C, e, hC_nn, hC_bd⟩ :=
        sharpDiffBdd_level_zero_wkpNorm (I := I) (M := M)
          g r s α P₀ K N hK1_le_N H
      refine ⟨C, e, hC_nn, fun i => ?_⟩
      have h_eq : eigenvectorChartRHSDiff (I := I) (M := M)
          g r s i α P₀ 0 _l =
          eigenvectorChartRHS (I := I) (M := M) g r s i α P₀ :=
        eigenvectorChartRHSDiff_zero (I := I) (M := M)
          g r s i α P₀ _l
      rw [h_eq]
      exact hC_bd i
  | succ m ih =>
      intro K hKN l
      have hKN_K : K + m + 1 ≤ N := by omega
      have hKN_K1 : (K + 1) + m + 1 ≤ N := by omega
      obtain ⟨C_K, e_K, hC_K_nn, hC_K_bd⟩ := ih K hKN_K (Fin.init l)
      obtain ⟨C_K1, e_K1, hC_K1_nn, hC_K1_bd⟩ := ih (K + 1) hKN_K1 (Fin.init l)
      have hKN_diff : m + 1 + (K + 1) ≤ N := by omega
      have h_prev_mem_succ : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
          MemWkp (d := Module.finrank ℝ E) (K + 1) 2
            (eigenvectorChartRHSDiff (I := I) (M := M)
              g r s i α P₀ m (Fin.init l))
            (chartTargetEuclid (I := I) (M := M) α) := fun i =>
        sharpDiffBdd_diff_memWkp (I := I) (M := M) g r s α P₀ N H i
          m (K + 1) hKN_diff (Fin.init l)
      have h_prev_ae_zero : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
          eigenvectorChartRHSDiff (I := I) (M := M)
              g r s i α P₀ m (Fin.init l)
            =ᵐ[(volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α \
                chartPouKernel (I := I) (M := M) α)] (fun _ => (0 : ℝ)) :=
        fun i =>
          eigenvectorChartRHSDiff_ae_zero_off_chartPouKernel
            (I := I) (M := M) g r s i α P₀ m (Fin.init l)
      have hKN_KmP1 : K + m + 1 ≤ N := hKN_K
      have hAtomA_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
          (a : Fin (Module.finrank ℝ E)),
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal (H.eigenvectorConstant (K + m + 1) *
              (i.fst.val)⁻¹ ^ (H.eigenvectorExponent (K + m + 1))) *
              ENNReal.ofReal
                ‖tensorResolventEigenbasisVec
                  (I := I) (M := M)
                  (tensorResolventL2_isCompactOperator
                    (I := I) (M := M) g r s) i‖ := by
        intro i a
        have h_chart_compact_mem :
            MemWkp (d := Module.finrank ℝ E) (K + (m + 1)) 2
              (eigenvectorChartComponentFun (I := I) (M := M)
                g r s i α P₀)
              (chartTargetEuclid (I := I) (M := M) α) :=
          eigenvector_chartComponent_memWkp_arbitrary
            (I := I) (M := M) g r s i (K + (m + 1)) α P₀
        have h_bridge :=
          (eigenvectorChartIteratedPartial_wkpNorm_le_of_memWkp
            (I := I) (M := M) g r s i α P₀ (m + 1) K
            h_chart_compact_mem
            (Fin.cons a (Fin.init l))).2
        refine le_trans h_bridge ?_
        have h_eig := H.eigenvector_bound i (K + (m + 1)) (by omega)
        have h_arith : K + m + 1 = K + (m + 1) := by ring
        rw [h_arith]
        exact h_eig
      have hAtomB_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
          (a b : Fin (Module.finrank ℝ E)),
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartialOrZero
                (d := Module.finrank ℝ E) 2 b
                (eigenvectorChartIteratedPartial (I := I) (M := M)
                  g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
                (chartTargetEuclid (I := I) (M := M) α))
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal (H.eigenvectorConstant (K + m + 2) *
              (i.fst.val)⁻¹ ^ (H.eigenvectorExponent (K + m + 2))) *
              ENNReal.ofReal
                ‖tensorResolventEigenbasisVec
                  (I := I) (M := M)
                  (tensorResolventL2_isCompactOperator
                    (I := I) (M := M) g r s) i‖ := by
        intro i a b
        have h_chosen := wkpNorm_chosenWeakPartial_le (d := Module.finrank ℝ E)
          (p := 2) (Ω := chartTargetEuclid (I := I) (M := M) α) K
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l))) b
        refine le_trans h_chosen ?_
        have h_chart_compact_mem :
            MemWkp (d := Module.finrank ℝ E) ((K + 1) + (m + 1)) 2
              (eigenvectorChartComponentFun (I := I) (M := M)
                g r s i α P₀)
              (chartTargetEuclid (I := I) (M := M) α) :=
          eigenvector_chartComponent_memWkp_arbitrary
            (I := I) (M := M) g r s i ((K + 1) + (m + 1)) α P₀
        have h_bridge :=
          (eigenvectorChartIteratedPartial_wkpNorm_le_of_memWkp
            (I := I) (M := M) g r s i α P₀ (m + 1) (K + 1)
            h_chart_compact_mem
            (Fin.cons a (Fin.init l))).2
        refine le_trans h_bridge ?_
        have h_eig := H.eigenvector_bound i ((K + 1) + (m + 1)) (by omega)
        have h_arith : K + m + 2 = (K + 1) + (m + 1) := by ring
        rw [h_arith]
        exact h_eig
      have hAtomC_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s),
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s i α P₀ m (Fin.init l))
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal (H.eigenvectorConstant (K + m) *
              (i.fst.val)⁻¹ ^ (H.eigenvectorExponent (K + m))) *
              ENNReal.ofReal
                ‖tensorResolventEigenbasisVec
                  (I := I) (M := M)
                  (tensorResolventL2_isCompactOperator
                    (I := I) (M := M) g r s) i‖ := by
        intro i
        have h_chart_compact_mem :
            MemWkp (d := Module.finrank ℝ E) (K + m) 2
              (eigenvectorChartComponentFun (I := I) (M := M)
                g r s i α P₀)
              (chartTargetEuclid (I := I) (M := M) α) :=
          eigenvector_chartComponent_memWkp_arbitrary
            (I := I) (M := M) g r s i (K + m) α P₀
        have h_bridge :=
          (eigenvectorChartIteratedPartial_wkpNorm_le_of_memWkp
            (I := I) (M := M) g r s i α P₀ m K
            h_chart_compact_mem
            (Fin.init l)).2
        refine le_trans h_bridge ?_
        exact H.eigenvector_bound i (K + m) (by omega)
      have hAtomD_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s),
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (eigenvectorChartRHSDiff (I := I) (M := M)
                g r s i α P₀ m (Fin.init l))
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal (C_K * (i.fst.val)⁻¹ ^ e_K) *
              ENNReal.ofReal
                ‖tensorResolventEigenbasisVec
                  (I := I) (M := M)
                  (tensorResolventL2_isCompactOperator
                    (I := I) (M := M) g r s) i‖ := hC_K_bd
      have hAtomE_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s),
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartialOrZero
                (d := Module.finrank ℝ E) 2 (l (Fin.last m))
                (eigenvectorChartRHSDiff (I := I) (M := M)
                  g r s i α P₀ m (Fin.init l))
                (chartTargetEuclid (I := I) (M := M) α))
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal (C_K1 * (i.fst.val)⁻¹ ^ e_K1) *
              ENNReal.ofReal
                ‖tensorResolventEigenbasisVec
                  (I := I) (M := M)
                  (tensorResolventL2_isCompactOperator
                    (I := I) (M := M) g r s) i‖ := by
        intro i
        have h_chosen := wkpNorm_chosenWeakPartial_le (d := Module.finrank ℝ E)
          (p := 2) (Ω := chartTargetEuclid (I := I) (M := M) α) K
          (eigenvectorChartRHSDiff (I := I) (M := M)
            g r s i α P₀ m (Fin.init l)) (l (Fin.last m))
        exact le_trans h_chosen (hC_K1_bd i)
      obtain ⟨Cnum, eNum, hCnum_nn, hCnum_bd⟩ :=
        eigenvectorChartRHSDiffNumerator_wkpNorm_le_chartcpt_sharp
          (I := I) (M := M) g r s α P₀ m K l
          (fun i => eigenvectorChartRHSDiff (I := I) (M := M)
            g r s i α P₀ m (Fin.init l))
          (H.eigenvectorConstant (K + m + 1)) (H.eigenvectorExponent (K + m + 1)) (H.eigenvectorConstant_nonneg _) hAtomA_bd
          (H.eigenvectorConstant (K + m + 2)) (H.eigenvectorExponent (K + m + 2)) (H.eigenvectorConstant_nonneg _) hAtomB_bd
          (H.eigenvectorConstant (K + m)) (H.eigenvectorExponent (K + m)) (H.eigenvectorConstant_nonneg _) hAtomC_bd
          C_K e_K hC_K_nn hAtomD_bd
          C_K1 e_K1 hC_K1_nn hAtomE_bd
          h_prev_mem_succ h_prev_ae_zero
      obtain ⟨Cden, hCden_nn, hCden_bd⟩ :=
        sharpDiff_wkpNorm_coef_mul_factor_le_uniform (I := I) (M := M) α K
          (one_div_densityOnEuclid_contDiffOn
            (I := I) (M := M) g α)
      refine ⟨Cden * Cnum, eNum, mul_nonneg hCden_nn hCnum_nn, fun i => ?_⟩
      set numFun : EuclN → ℝ :=
        eigenvectorChartRHSDiffNumerator (I := I) (M := M)
          g r s i α P₀ m l
          (eigenvectorChartRHSDiff (I := I) (M := M)
            g r s i α P₀ m (Fin.init l)) with hnumFun_def
      set Q : EuclN → ℝ := fun y =>
        (1 / densityOnEuclid (I := I) g α y) * numFun y with hQ_def
      have h_num_memWkp : MemWkp (d := Module.finrank ℝ E) K 2 numFun
          (chartTargetEuclid (I := I) (M := M) α) := by
        rw [hnumFun_def]
        refine eigenvectorChartRHSDiffNumerator_memWkp_of_iter
          (I := I) (M := M) g r s i α P₀ m K l ?_ ?_ ?_
        · intro j idx
          have h_chart_compact_mem :
              MemWkp (d := Module.finrank ℝ E) ((2 + K) + j) 2
                (eigenvectorChartComponentFun (I := I) (M := M)
                  g r s i α P₀)
                (chartTargetEuclid (I := I) (M := M) α) :=
            eigenvector_chartComponent_memWkp_arbitrary
              (I := I) (M := M) g r s i ((2 + K) + j) α P₀
          exact (eigenvectorChartIteratedPartial_wkpNorm_le_of_memWkp
            (I := I) (M := M) g r s i α P₀ j (2 + K)
            h_chart_compact_mem idx).1
        · exact h_prev_mem_succ i
        · exact h_prev_ae_zero i
      have h_num_ae_zero :
          numFun =ᵐ[(volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α \
              chartPouKernel (I := I) (M := M) α)]
            (fun _ : EuclN => (0 : ℝ)) := by
        rw [hnumFun_def]
        exact eigenvectorChartRHSDiffNumerator_ae_zero_off_chartPouKernel
          (I := I) (M := M) g r s i α P₀ m l (h_prev_ae_zero i)
      have h_Q_props := hCden_bd numFun h_num_memWkp h_num_ae_zero
      have h_Q_bd : iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 Q
            (chartTargetEuclid (I := I) (M := M) α) ≤
          ENNReal.ofReal Cden *
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 numFun
              (chartTargetEuclid (I := I) (M := M) α) := h_Q_props.2
      have h_Q_ae_zero : Q =ᵐ[(volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α \
            chartPouKernel (I := I) (M := M) α)]
          (fun _ : EuclN => (0 : ℝ)) := by
        filter_upwards [h_num_ae_zero] with y hy
        rw [hQ_def]
        simp [hy]
      have h_diff_eq : eigenvectorChartRHSDiff (I := I) (M := M)
          g r s i α P₀ (m + 1) l =
          Set.indicator (chartPouKernel (I := I) (M := M) α) Q := by
        rw [eigenvectorChartRHSDiff_succ]
        funext y
        rw [hQ_def, hnumFun_def]
        rcases Classical.em (y ∈ chartPouKernel (I := I) (M := M) α) with
          h_mem | h_mem
        · rw [Set.indicator_of_mem h_mem, Set.indicator_of_mem h_mem,
            one_div, mul_comm, ← div_eq_mul_inv]
        · rw [Set.indicator_of_notMem h_mem, Set.indicator_of_notMem h_mem]
      rw [h_diff_eq]
      have h_strip := sharpDiff_wkpNorm_indicator_eq (I := I) (M := M) α K
        (Q := Q) h_Q_ae_zero
      rw [h_strip]
      have hCnum_bd_i : iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 numFun
            (chartTargetEuclid (I := I) (M := M) α) ≤
          ENNReal.ofReal (Cnum * (i.fst.val)⁻¹ ^ eNum) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i‖ := by
        rw [hnumFun_def]
        exact hCnum_bd i
      refine le_trans h_Q_bd ?_
      refine le_trans (mul_le_mul' (le_refl _) hCnum_bd_i) ?_
      have hμ_inv_pow_nn : (0 : ℝ) ≤ (i.fst.val)⁻¹ ^ eNum := by
        exact pow_nonneg (sharpDiff_eigen_inv_nn
          (I := I) (M := M) g r s i) _
      rw [show ENNReal.ofReal (Cnum * (i.fst.val)⁻¹ ^ eNum) =
          ENNReal.ofReal Cnum * ENNReal.ofReal ((i.fst.val)⁻¹ ^ eNum) from
        ENNReal.ofReal_mul hCnum_nn]
      rw [show ENNReal.ofReal (Cden * Cnum * (i.fst.val)⁻¹ ^ eNum) =
          ENNReal.ofReal Cden * ENNReal.ofReal Cnum *
            ENNReal.ofReal ((i.fst.val)⁻¹ ^ eNum) by
        rw [ENNReal.ofReal_mul (mul_nonneg hCden_nn hCnum_nn),
          ENNReal.ofReal_mul hCden_nn]]
      ring_nf
      exact le_refl _

open DifferentialGeometry.Analysis.Spectral in
omit [CompleteSpace E] in
theorem eigenvectorChartRHSDiff_wkpNorm_le_chartcpt_sharp_bdd
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (l : Fin m → Fin (Module.finrank ℝ E))
    (H : EigenvectorChartRightHandSideDifferentiatedSharpWkpBoundsUpToOrder (I := I) (M := M)
      g r s α P₀ (K + m + 1)) :
    ∃ (C : ℝ) (e : ℕ), 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (eigenvectorChartRHSDiff (I := I) (M := M)
              g r s i α P₀ m l)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal (C * (i.fst.val)⁻¹ ^ e) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i‖ :=
  sharpDiffBdd_recursion (I := I) (M := M) g r s α P₀ (K + m + 1)
    H m K (le_refl _) l

end MainResults

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
