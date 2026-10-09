import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4Provenance
import DifferentialGeometry.Geometry.Fibration.ActualCfs15StageOutputMean

/-!
# `Cfs15StageOutput` at the register's stage accuracies `Ξ_j(Γ_j)` (register V4)

External draft 59 §2.4 (D59-3) bound to FC39's register V4 on its shared early data
`earlyDataSharedV4 K`: at every stage `st` and index `j`, the register's own modulus value
`Ξ_j(Γ_j)` carries CFS15's jet-order-`K` object (`Ξ_range`) and CFS12's interior condition, so the
stage output is built from THAT object (`cfs15StageOutput_of_modulusAtV2_C15`); locality, (SM) and
(SMV) are then the theorems `Cfs15StageOutput.locality_of_cloud_C15`, `mean_of_cloud_C15`,
`smv_of_cloud_C15` on the same output.

* `earlyDataSharedV4_stageOutput_C15 st j`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Filter
open scoped ContDiff Manifold Topology
open GC.MetricGeometry DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

/-- **The stage output at the register's accuracy.** For a stage `st` of register V4's shared
early data and an index `j` there is an early weight constant `c_w ≥ 0` such that every cloud with
CFS15's hypotheses at quality `Γ_j` (buffer `128Ξ_j(Γ_j)⁻¹`, ratio `5/3`, planes of dimension
`k_j`) has a `Cfs15StageOutput k_j K (Ξ_j(Γ_j)) c_w S T r P`, built from the register's own
jet-order-`K` object `Ξ_range`. -/
theorem earlyDataSharedV4_stageOutput_C15 {K : ℕ} (st : ClosedStage (earlyDataSharedV4 K))
    (j : Fin 3) :
    ∃ cw : ℝ, 0 ≤ cw ∧
      ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
        (S T : Set H), S ⊆ T → TotallyBounded S →
        ∀ (r : H → ℝ) (P : H → Submodule ℝ H),
        (∀ x ∈ S, Module.finrank ℝ (P x) = gafStageDim j) →
        ∀ rmin R : ℝ, 0 < rmin → (∀ x ∈ S, rmin ≤ r x) → (∀ x ∈ S, r x ≤ R) →
        (∀ x ∈ T, ∀ y ∈ T,
          dist y x ≤ 128 * ((earlyDataSharedV4 K).Ξ j (st.Γ j))⁻¹ * max (r y) (r x) →
          r x / (5 / 3) ≤ r y ∧ r y ≤ (5 / 3) * r x) →
        (∀ x ∈ S, hausdorffEDist (T ∩ ball x (r x / st.Γ j))
          ((AffineSubspace.mk' x (P x) : Set H) ∩ ball x (r x / st.Γ j)) ≤
            ENNReal.ofReal (st.Γ j * r x)) →
        Nonempty (Cfs15StageOutput (gafStageDim j) K ((earlyDataSharedV4 K).Ξ j (st.Γ j)) cw
          S T r P) :=
  cfs15StageOutput_of_modulusAtV2_C15 (Ξ := (earlyDataSharedV4 K).Ξ j) (st.Γ_pos j)
    (modulusSharedV4_atV2_VAL6 K j (st.Γ_pos j) (st.Γ_lt_sharedRange_VAL6 j))
    (earlyDataSharedV4_stage_mean_VAL6 st j).1

end DifferentialGeometry.Geometry.Collapse
