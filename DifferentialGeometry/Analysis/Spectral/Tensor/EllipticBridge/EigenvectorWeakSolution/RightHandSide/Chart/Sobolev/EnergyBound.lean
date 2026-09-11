import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.RightHandSide.Chart.LpEnergyBound
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.RightHandSide.Chart.Sobolev.Bound
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

section MainResults


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
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s) i)
    (by
      intro h_zero
      have h_norm := vec_norm_eq_one (I := I) (M := M) g r s i
      rw [h_zero, norm_zero] at h_norm
      exact one_ne_zero h_norm.symm)).1


omit [CompleteSpace E] in
theorem eigenvectorChartRHS_wkpNorm_le_energy_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (K : ℕ)
    (h_pou : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β))
    (h_eig : ∃ eigenvectorConstant : ℝ, 0 ≤ eigenvectorConstant ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (tensorResolventEigenbasisVec (I := I) (M := M)
                  (tensorResolventL2_isCompactOperator (I := I)
                    (M := M) g r s) i) α P₀ :
              Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal eigenvectorConstant *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i‖)
    (h_resHigh : ∃ highResolventConstant : ℝ, 0 ≤ highResolventConstant ∧
      ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
        (β : M) (Q : TensorCompIdx (E := E) r s),
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K + 1) 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                  (eigenvectorResolvent (I := I) (M := M) g r s i))
                β Q : Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) :
                EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β)
          ≤ ENNReal.ofReal highResolventConstant *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i‖)
    (h_resLow : ∃ lowResolventConstant : ℝ, 0 ≤ lowResolventConstant ∧
      ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
        (β : M) (Q : TensorCompIdx (E := E) r s),
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                  (eigenvectorResolvent (I := I) (M := M) g r s i))
                β Q : Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) :
                EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β)
          ≤ ENNReal.ofReal lowResolventConstant *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i‖)
    (h_partial : ∃ partialConstant : ℝ, 0 ≤ partialConstant ∧
      ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
        (P : TensorCompIdx (E := E) r s) (k : Fin (Module.finrank ℝ E)),
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((partialLpLimit (I := I) (M := M)
                g r s i α P k :
                Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
                EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal partialConstant *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i‖)
    (h_component : ∃ componentConstant : ℝ, 0 ≤ componentConstant ∧
      ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
        (p : TensorCompIdx (E := E) r s),
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((componentLpLimit (I := I) (M := M)
                g r s i α p :
                Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
                EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal componentConstant *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i‖)
    (h_crossRight : ∃ crossRightConstant : ℝ, 0 ≤ crossRightConstant ∧
      ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
        (P : TensorCompIdx (E := E) r s),
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((crossRightLimitComponent (I := I) (M := M)
                g r s i α P :
                Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
                EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal crossRightConstant *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i‖)
    (h_cutoff : ∃ cutoffConstant : ℝ, 0 ≤ cutoffConstant ∧
      ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
        (P : TensorCompIdx (E := E) r s) (l : Fin (Module.finrank ℝ E)),
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((cutoffPartialLpLimit (I := I) (M := M)
                g r s i α P l :
                Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
                EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal cutoffConstant *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i‖) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (eigenvectorChartRHS (I := I) (M := M) g r s i α P₀)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal (C * (i.fst.val)⁻¹) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i‖ := by
  classical
  obtain ⟨Crhs, hCrhs_nn, hCrhs_bd⟩ :=
    eigenvectorChartRHS_wkpNorm_le_uniform (I := I) (M := M)
      g r s α P₀ K h_pou
  obtain ⟨eigenvectorConstant, eigenvectorConstant_nonneg, eigenvector_bound⟩ := h_eig
  obtain ⟨highResolventConstant, highResolventConstant_nonneg, highResolvent_bound⟩ := h_resHigh
  obtain ⟨lowResolventConstant, lowResolventConstant_nonneg, lowResolvent_bound⟩ := h_resLow
  obtain ⟨partialConstant, partialConstant_nonneg, partial_bound⟩ := h_partial
  obtain ⟨componentConstant, componentConstant_nonneg, component_bound⟩ := h_component
  obtain ⟨crossRightConstant, crossRightConstant_nonneg, crossRight_bound⟩ := h_crossRight
  obtain ⟨cutoffConstant, cutoffConstant_nonneg, cutoff_bound⟩ := h_cutoff
  set TCard : ℕ := (transportChartCenters (I := I) (M := M) α).card with hTCard_def
  set Cqtot : ℝ := (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) * highResolventConstant
    with hCqtot_def
  set Cmid : ℝ := ((transportChartCenters (I := I) (M := M) α).sum fun β =>
        Cqtot + ((transportChartCenters (I := I) (M := M) β).card : ℝ) * Cqtot)
    with hCmid_def
  set Clow : ℝ := (TCard : ℝ) * ((Fintype.card (TensorCompIdx (E := E) r s) : ℝ) *
        lowResolventConstant) with hClow_def
  set partialConstant' : ℝ := (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) *
        ((Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) * partialConstant) with hCpar'_def
  set componentConstant' : ℝ := (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) * componentConstant
    with hCcom'_def
  set crossRightConstant' : ℝ := (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) * crossRightConstant
    with hCcR'_def
  set cutoffConstant' : ℝ := (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) *
        ((Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) * cutoffConstant) with hCcut'_def
  set Cagg : ℝ := eigenvectorConstant + Cmid + Clow + partialConstant' + componentConstant' + crossRightConstant' + cutoffConstant' with hCagg_def
  have hCqtot_nn : 0 ≤ Cqtot := by
    have : (0 : ℝ) ≤ (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) := by
      exact_mod_cast Nat.zero_le _
    exact mul_nonneg this highResolventConstant_nonneg
  have hCmid_nn : 0 ≤ Cmid := by
    refine Finset.sum_nonneg (fun β _ => ?_)
    have h1 : (0 : ℝ) ≤ ((transportChartCenters (I := I) (M := M) β).card : ℝ) := by
      exact_mod_cast Nat.zero_le _
    exact add_nonneg hCqtot_nn (mul_nonneg h1 hCqtot_nn)
  have hClow_nn : 0 ≤ Clow := by
    have hT : (0 : ℝ) ≤ (TCard : ℝ) := by exact_mod_cast Nat.zero_le _
    have hQ : (0 : ℝ) ≤ (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) := by
      exact_mod_cast Nat.zero_le _
    exact mul_nonneg hT (mul_nonneg hQ lowResolventConstant_nonneg)
  have hCpar'_nn : 0 ≤ partialConstant' := by
    have hQ : (0 : ℝ) ≤ (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) := by
      exact_mod_cast Nat.zero_le _
    have hk : (0 : ℝ) ≤ (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) := by
      exact_mod_cast Nat.zero_le _
    exact mul_nonneg hQ (mul_nonneg hk partialConstant_nonneg)
  have hCcom'_nn : 0 ≤ componentConstant' := by
    have hQ : (0 : ℝ) ≤ (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) := by
      exact_mod_cast Nat.zero_le _
    exact mul_nonneg hQ componentConstant_nonneg
  have hCcR'_nn : 0 ≤ crossRightConstant' := by
    have hQ : (0 : ℝ) ≤ (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) := by
      exact_mod_cast Nat.zero_le _
    exact mul_nonneg hQ crossRightConstant_nonneg
  have hCcut'_nn : 0 ≤ cutoffConstant' := by
    have hQ : (0 : ℝ) ≤ (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) := by
      exact_mod_cast Nat.zero_le _
    have hk : (0 : ℝ) ≤ (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) := by
      exact_mod_cast Nat.zero_le _
    exact mul_nonneg hQ (mul_nonneg hk cutoffConstant_nonneg)
  have hCagg_nn : 0 ≤ Cagg := by
    refine add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg
      (add_nonneg ?_ hCmid_nn) hClow_nn) hCpar'_nn) hCcom'_nn) hCcR'_nn) hCcut'_nn
    exact eigenvectorConstant_nonneg
  refine ⟨Crhs * Cagg, mul_nonneg hCrhs_nn hCagg_nn, fun i => ?_⟩
  have hμ_pos : 0 < i.fst.val :=
    eigenvalue_pos (I := I) (M := M) g r s i
  have hμ_inv_nn : 0 ≤ (i.fst.val)⁻¹ := le_of_lt (inv_pos.mpr hμ_pos)
  set Rhs : ℝ≥0∞ := ENNReal.ofReal
      ‖tensorResolventEigenbasisVec (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M)
          g r s) i‖ with hRhs_def
  have hS1 :
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
          (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
              (tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I)
                  (M := M) g r s) i) α P₀ :
            Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal eigenvectorConstant * Rhs := eigenvector_bound i
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
              Cqtot) * Rhs := by
    intro β _hβ
    have h_inner_β : (∑ Q : TensorCompIdx (E := E) r s,
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K + 1) 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                  (eigenvectorResolvent (I := I) (M := M) g r s i))
                β Q : Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) :
                EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β))
        ≤ ENNReal.ofReal Cqtot * Rhs := by
      have h_each : ∀ Q ∈ (Finset.univ : Finset (TensorCompIdx (E := E) r s)),
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K + 1) 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                  (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                    (eigenvectorResolvent (I := I) (M := M)
                      g r s i))
                  β Q : Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) :
                  EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β)
            ≤ ENNReal.ofReal highResolventConstant * Rhs := fun Q _hQ => highResolvent_bound i β Q
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
        (fun _Q => highResolventConstant) Rhs (fun _ _ => highResolventConstant_nonneg) h_each
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at h_sum
      exact h_sum.trans_eq (by rw [hCqtot_def])
    have h_inner_β' : (∑ β' ∈ transportChartCenters (I := I) (M := M) β,
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
            Rhs := by
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
            ≤ ENNReal.ofReal Cqtot * Rhs := by
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
              ≤ ENNReal.ofReal highResolventConstant * Rhs := fun Q _hQ => highResolvent_bound i β' Q
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
          (fun _Q => highResolventConstant) Rhs (fun _ _ => highResolventConstant_nonneg) h_each
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
        (fun _β' => Cqtot) Rhs (fun _ _ => hCqtot_nn) h_perβ'
      rw [Finset.sum_const, nsmul_eq_mul] at h_sum
      exact h_sum
    have h_total :
        (∑ Q : TensorCompIdx (E := E) r s,
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
                  (chartTargetEuclid (I := I) (M := M) β')
        ≤ ENNReal.ofReal Cqtot * Rhs +
            ENNReal.ofReal
              (((transportChartCenters (I := I) (M := M) β).card : ℝ) *
                Cqtot) * Rhs := by
      exact add_le_add h_inner_β h_inner_β'
    refine h_total.trans (le_of_eq ?_)
    have hN : 0 ≤ ((transportChartCenters (I := I) (M := M) β).card : ℝ) := by
      exact_mod_cast Nat.zero_le _
    rw [ENNReal.ofReal_add hCqtot_nn (mul_nonneg hN hCqtot_nn), add_mul]
  have hS2 : (∑ β ∈ transportChartCenters (I := I) (M := M) α,
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
      ≤ ENNReal.ofReal Cmid * Rhs := by
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
      Rhs h_perβ_nn hS2_inner
    exact h_sum.trans_eq (by rw [hCmid_def])
  have hS3 : (∑ β ∈ transportChartCenters (I := I) (M := M) α,
        ∑ Q : TensorCompIdx (E := E) r s,
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                  (eigenvectorResolvent (I := I) (M := M)
                    g r s i))
                β Q : Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) :
                EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β))
      ≤ ENNReal.ofReal Clow * Rhs := by
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
              ((Fintype.card (TensorCompIdx (E := E) r s) : ℝ) * lowResolventConstant) * Rhs := by
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
            ≤ ENNReal.ofReal lowResolventConstant * Rhs := fun Q _hQ => lowResolvent_bound i β Q
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
        (fun _Q => lowResolventConstant) Rhs (fun _ _ => lowResolventConstant_nonneg) h_each
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at h_sum
      exact h_sum
    have hQ_nn : (0 : ℝ) ≤
        (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) * lowResolventConstant := by
      have hQ : (0 : ℝ) ≤ (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) := by
        exact_mod_cast Nat.zero_le _
      exact mul_nonneg hQ lowResolventConstant_nonneg
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
      (fun _β => (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) * lowResolventConstant)
      Rhs (fun _ _ => hQ_nn) h_perβ
    rw [Finset.sum_const, nsmul_eq_mul] at h_sum
    exact h_sum.trans_eq (by rw [hClow_def, hTCard_def])
  have hS4 : (∑ P : TensorCompIdx (E := E) r s,
        ∑ k : Fin (Module.finrank ℝ E),
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((partialLpLimit (I := I) (M := M)
                g r s i α P k :
              Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α))
      ≤ ENNReal.ofReal partialConstant' * Rhs := by
    have h_perP : ∀ P ∈ (Finset.univ : Finset (TensorCompIdx (E := E) r s)),
        (∑ k : Fin (Module.finrank ℝ E),
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (fun y => ((partialLpLimit (I := I) (M := M)
                  g r s i α P k :
                Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
                EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal
              ((Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) * partialConstant) * Rhs := by
      intro P _hP
      have h_each : ∀ k ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ E))),
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (fun y => ((partialLpLimit (I := I) (M := M)
                  g r s i α P k :
                Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
                EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal partialConstant * Rhs := fun k _hk => partial_bound i P k
      have h_sum := sum_le_of_le_ofReal_mul
        (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
        (fun k => iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((partialLpLimit (I := I) (M := M)
                g r s i α P k :
              Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α))
        (fun _k => partialConstant) Rhs (fun _ _ => partialConstant_nonneg) h_each
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at h_sum
      exact h_sum
    have hk_nn : (0 : ℝ) ≤
        (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) * partialConstant := by
      have hk : (0 : ℝ) ≤ (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) := by
        exact_mod_cast Nat.zero_le _
      exact mul_nonneg hk partialConstant_nonneg
    have h_sum := sum_le_of_le_ofReal_mul
      (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun P => ∑ k : Fin (Module.finrank ℝ E),
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((partialLpLimit (I := I) (M := M)
                g r s i α P k :
              Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α))
      (fun _P => (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) * partialConstant)
      Rhs (fun _ _ => hk_nn) h_perP
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at h_sum
    exact h_sum.trans_eq (by rw [hCpar'_def])
  have hS5 : (∑ p : TensorCompIdx (E := E) r s,
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
          (fun y => ((componentLpLimit (I := I) (M := M)
              g r s i α p :
            Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
            EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α))
      ≤ ENNReal.ofReal componentConstant' * Rhs := by
    have h_each : ∀ p ∈ (Finset.univ : Finset (TensorCompIdx (E := E) r s)),
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((componentLpLimit (I := I) (M := M)
                g r s i α p :
              Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal componentConstant * Rhs := fun p _hp => component_bound i p
    have h_sum := sum_le_of_le_ofReal_mul
      (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun p => iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
          (fun y => ((componentLpLimit (I := I) (M := M)
              g r s i α p :
            Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
            EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α))
      (fun _p => componentConstant) Rhs (fun _ _ => componentConstant_nonneg) h_each
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at h_sum
    exact h_sum.trans_eq (by rw [hCcom'_def])
  have hS6 : (∑ P : TensorCompIdx (E := E) r s,
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
          (fun y => ((crossRightLimitComponent (I := I) (M := M)
              g r s i α P :
            Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
            EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α))
      ≤ ENNReal.ofReal crossRightConstant' * Rhs := by
    have h_each : ∀ P ∈ (Finset.univ : Finset (TensorCompIdx (E := E) r s)),
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((crossRightLimitComponent (I := I) (M := M)
                g r s i α P :
              Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal crossRightConstant * Rhs := fun P _hP => crossRight_bound i P
    have h_sum := sum_le_of_le_ofReal_mul
      (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun P => iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
          (fun y => ((crossRightLimitComponent (I := I) (M := M)
              g r s i α P :
            Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
            EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α))
      (fun _P => crossRightConstant) Rhs (fun _ _ => crossRightConstant_nonneg) h_each
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at h_sum
    exact h_sum.trans_eq (by rw [hCcR'_def])
  have hS7 : (∑ P : TensorCompIdx (E := E) r s,
        ∑ l : Fin (Module.finrank ℝ E),
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((cutoffPartialLpLimit (I := I) (M := M)
                g r s i α P l :
              Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α))
      ≤ ENNReal.ofReal cutoffConstant' * Rhs := by
    have h_perP : ∀ P ∈ (Finset.univ : Finset (TensorCompIdx (E := E) r s)),
        (∑ l : Fin (Module.finrank ℝ E),
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (fun y => ((cutoffPartialLpLimit (I := I) (M := M)
                  g r s i α P l :
                Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
                EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal
              ((Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) * cutoffConstant) * Rhs := by
      intro P _hP
      have h_each : ∀ l ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ E))),
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (fun y => ((cutoffPartialLpLimit (I := I) (M := M)
                  g r s i α P l :
                Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
                EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal cutoffConstant * Rhs := fun l _hl => cutoff_bound i P l
      have h_sum := sum_le_of_le_ofReal_mul
        (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
        (fun l => iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((cutoffPartialLpLimit (I := I) (M := M)
                g r s i α P l :
              Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α))
        (fun _l => cutoffConstant) Rhs (fun _ _ => cutoffConstant_nonneg) h_each
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at h_sum
      exact h_sum
    have hk_nn : (0 : ℝ) ≤
        (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) * cutoffConstant := by
      have hk : (0 : ℝ) ≤ (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) := by
        exact_mod_cast Nat.zero_le _
      exact mul_nonneg hk cutoffConstant_nonneg
    have h_sum := sum_le_of_le_ofReal_mul
      (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun P => ∑ l : Fin (Module.finrank ℝ E),
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((cutoffPartialLpLimit (I := I) (M := M)
                g r s i α P l :
              Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α))
      (fun _P => (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) * cutoffConstant)
      Rhs (fun _ _ => hk_nn) h_perP
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at h_sum
    exact h_sum.trans_eq (by rw [hCcut'_def])
  have h_aggr_total :
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (tensorResolventEigenbasisVec (I := I) (M := M)
                  (tensorResolventL2_isCompactOperator (I := I)
                    (M := M) g r s) i) α P₀ :
              Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α)
          + (∑ β ∈ transportChartCenters (I := I) (M := M) α,
              ((∑ Q : TensorCompIdx (E := E) r s,
                  iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K + 1) 2
                    (fun y => ((tensorL2ChartComponent (I := I) (M := M)
                        g r s
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
                        (fun y => ((tensorL2ChartComponent (I := I) (M := M)
                            g r s
                            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                              (eigenvectorResolvent (I := I)
                                (M := M) g r s i))
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
                (fun y => ((crossRightLimitComponent (I := I)
                    (M := M) g r s i α P :
                  Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
                  EuclN → ℝ) y)
                (chartTargetEuclid (I := I) (M := M) α))
          + (∑ P : TensorCompIdx (E := E) r s,
              ∑ l : Fin (Module.finrank ℝ E),
                iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
                  (fun y => ((cutoffPartialLpLimit (I := I)
                      (M := M) g r s i α P l :
                    Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
                    EuclN → ℝ) y)
                  (chartTargetEuclid (I := I) (M := M) α))
        ≤ ENNReal.ofReal Cagg * Rhs := by
    have hp1 : 0 ≤ eigenvectorConstant + Cmid := add_nonneg eigenvectorConstant_nonneg hCmid_nn
    have hp2 : 0 ≤ eigenvectorConstant + Cmid + Clow := add_nonneg hp1 hClow_nn
    have hp3 : 0 ≤ eigenvectorConstant + Cmid + Clow + partialConstant' := add_nonneg hp2 hCpar'_nn
    have hp4 : 0 ≤ eigenvectorConstant + Cmid + Clow + partialConstant' + componentConstant' := add_nonneg hp3 hCcom'_nn
    have hp5 : 0 ≤ eigenvectorConstant + Cmid + Clow + partialConstant' + componentConstant' + crossRightConstant' :=
      add_nonneg hp4 hCcR'_nn
    have h_expand :
        ENNReal.ofReal Cagg
          = ENNReal.ofReal eigenvectorConstant + ENNReal.ofReal Cmid + ENNReal.ofReal Clow
            + ENNReal.ofReal partialConstant' + ENNReal.ofReal componentConstant' + ENNReal.ofReal crossRightConstant'
            + ENNReal.ofReal cutoffConstant' := by
      rw [hCagg_def, ENNReal.ofReal_add hp5 hCcut'_nn,
        ENNReal.ofReal_add hp4 hCcR'_nn,
        ENNReal.ofReal_add hp3 hCcom'_nn,
        ENNReal.ofReal_add hp2 hCpar'_nn,
        ENNReal.ofReal_add hp1 hClow_nn,
        ENNReal.ofReal_add eigenvectorConstant_nonneg hCmid_nn]
    rw [h_expand, add_mul, add_mul, add_mul, add_mul, add_mul, add_mul]
    refine add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
      (add_le_add ?_ hS2) hS3) hS4) hS5) hS6) hS7
    exact hS1
  refine le_trans (hCrhs_bd i) ?_
  refine le_trans (mul_le_mul' (le_refl _) h_aggr_total) (le_of_eq ?_)
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), hRhs_def,
    show (i.fst.val)⁻¹ * Crhs * Cagg = Crhs * Cagg * (i.fst.val)⁻¹ by ring]

end MainResults

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
