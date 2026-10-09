import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialStepRetention
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalCapScalar
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.IdentifiedHistoryPinching

set_option autoImplicit false
noncomputable section
open Set DifferentialGeometry DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff NNReal Topology

namespace GC.GeneralFlow
universe u

/-- The canonical windows are retained in the actual old native class. -/
theorem PreparedSpatialStepRetention.oldNative_hasCanonicalWindows
    {pBase : CutoffParameters} {C : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    {E B Bnext d eta εcut Dcut : ℝ} {mcut : ℕ}
    {L : PreparedSpatialState pBase C P g E B}
    {R : PreparedSpatialState pBase C P g B Bnext}
    (W : PreparedSpatialStepRetention L R d eta εcut Dcut mcut) :
    ∀ i b, ((W.oldNativeRecords i).static b).hasCanonicalWindow := by
  exact W.oldNative_class.2.2.2.2.2.1

/-- Uniform cap-core scalar quality applies to the same selected old-native records. -/
theorem exists_old_native_cap_scalar_quality
    (Dstar : ℝ) (hDstar : StandardCap.transitionEnd < Dstar) :
    ∃ εcap : ℝ, 0 < εcap ∧
    ∀ {pBase : CutoffParameters} {C : ClosedBirthConstants}
      {P : OrientedThreeStage.{u}} {g : P.Metric}
      {E B Bnext d eta εcut Dcut : ℝ} {mcut : ℕ}
      {L : PreparedSpatialState pBase C P g E B}
      {R : PreparedSpatialState pBase C P g B Bnext}
      (W : PreparedSpatialStepRetention L R d eta εcut Dcut mcut),
      Dstar ≤ L.prepared.parameters.modelRadius →
      L.prepared.parameters.modelAccuracy ≤ εcap →
      2 ≤ L.prepared.parameters.modelOrder →
      ∀ i b z, ((W.oldNativeRecords i).static b).neck.scale / 2 ≤
        metricScalarAt ((W.oldNativeRecords i).static b).witness.metric
          (((W.oldNativeRecords i).static b).witness.cap z) := by
  obtain ⟨εcap, hεcap, hcap⟩ :=
    exists_presented_cap_scalar_lower_bound_of_canonical_window_core.{u} Dstar hDstar
  refine ⟨εcap, hεcap, ?_⟩
  intro pBase C P g E B Bnext d eta εcut Dcut mcut L R W hD hε hm i b z
  have hD' : Dstar ≤ W.oldNativeParameters.modelRadius := by
    rw [W.oldNative_class.2.1]
    exact hD
  have hε' : W.oldNativeParameters.modelAccuracy ≤ εcap := by
    rw [W.oldNative_class.2.2.2.1]
    exact hε
  have hm' : 2 ≤ W.oldNativeParameters.modelOrder := by
    rw [W.oldNative_class.2.2.1]
    exact hm
  exact hcap (W.oldNative.toHistory.event i) hD' hε' hm'
    ((W.oldNativeRecords i).static b) (W.oldNative_hasCanonicalWindows i b) z

/-- The class radius bound separates every actual static scale from its own threshold. -/
theorem PreparedSpatialStepRetention.static_scale_gt_sixteen_own_threshold_of_class_bound
    {pBase : CutoffParameters} {C : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    {E B Bnext d eta εcut Dcut : ℝ} {mcut : ℕ}
    {L : PreparedSpatialState pBase C P g E B}
    {R : PreparedSpatialState pBase C P g B Bnext}
    (W : PreparedSpatialStepRetention L R d eta εcut Dcut mcut)
    (hsmall : 32 * L.prepared.Qall * L.prepared.radiusBound ^ 2 ≤ 1) :
    ∀ (i : Fin W.oldNative.eventCount)
      (b : (W.oldNative.toHistory.event i).RetainedBoundaryIndex),
      16 * L.prepared.Qall < ((W.oldNativeRecords i).static b).neck.scale := by
  intro i b
  have hpos : 0 < 2 * L.prepared.radiusBound ^ 2 :=
    mul_pos (by norm_num) (sq_pos_of_pos L.prepared.radiusBound_pos)
  have hbound : 16 * L.prepared.Qall ≤ (2 * L.prepared.radiusBound ^ 2)⁻¹ := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ hpos).mpr
    nlinarith only [hsmall]
  exact hbound.trans_lt
    (W.oldNative_class.inv_two_mul_sq_lt_static_scale L.prepared.recenter_bound i b)

/-- Fix the actual native initial metric before all future extensions and fine records. -/
theorem PreparedSpatialState.exists_pinching_for_old_native_extensions
    {pBase : CutoffParameters} {C : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric} {E B : ℝ}
    (L : PreparedSpatialState pBase C P g E B) :
    ∃ phi : ℝ → ℝ, Perelman.AdmissiblePinchingFunction phi ∧
    ∀ {Bnext d eta εcut Dcut : ℝ} {mcut : ℕ}
      {R : PreparedSpatialState pBase C P g B Bnext}
      (W : PreparedSpatialStepRetention L R d eta εcut Dcut mcut),
      W.oldNative.EventSlabsPinched phi ∧
      ∀ hfinal : W.oldNative.time (Fin.last W.oldNative.eventCount) < W.oldNative.horizon,
        Perelman.PhiAlmostNonnegative (W.oldNative.finalSlab hfinal).flow
          (Icc (W.oldNative.time (Fin.last W.oldNative.eventCount)) W.oldNative.horizon) phi := by
  obtain ⟨phi, hphi, hpinch⟩ :=
    exists_pinching_certificates_for_identified_histories L.nativeStage L.nativeMetric
  refine ⟨phi, hphi, ?_⟩
  intro Bnext d eta εcut Dcut mcut R W
  exact hpinch W.oldNative W.oldNativeInitial W.oldNativeParameters W.oldNativeRecords

end GC.GeneralFlow
