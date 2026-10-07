import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.StrongNativeLayerC12X
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialStepRetention
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialChain

/-!
# Native layer on the prepared chain (C12X, S16 G6, part b)

`hnative_of_classFull_C12X` proves the native hypothesis `hnative` frozen by O-C12X-S16D
(`state-O-C12X-S16D.md`, `[FROZEN] G6 interface`) for the old native `(W m).oldNative` of every
retention step (astra `Kplus`), threshold `((S.state m).radius ^ 2)⁻¹`, accuracy `C.epsilon` on the
diagonal, constants `C1 C2`.

Per step `m` the native layer `native_strongFull_of_classFull_C12X` is applied to the prepared
class `(S.state m).prepared` (`P₀ g₀` = native stage / metric, `B = 3 ^ m - shift`, `κ` = class
`kappa`, thresholds `qcan ≤ qs` of the class; noncollapsing from `prepared.control`, estimates
`oldNative_estimates`).  Its constants are chosen per step (`choose`); what remains explicit:

* `C.epsilon ≤ εStrong_C12X` (binder `hεs`);
* smallness of the prepared class against the class constants of step `m`;
* `C1hOf m ≤ C1`, `C2hOf m ≤ C2`, `qhOf m ≤ ((S.state m).radius ^ 2)⁻¹` (R-S16 D-1: no uniform
  constants here).  Pinching is not a hypothesis (Hamilton–Ivey, inside the native layer);
  `qs ≤ qhOf m` is part of the output (threshold alignment R-S16 D-4).
-/

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace GC.GeneralFlow

universe u

/-- **S16 G6**: the frozen `hnative` of O-C12X-S16D from the class Full theorem, with the per-step
class constants exhibited and the remaining premises (smallness, constant comparison) explicit. -/
theorem hnative_of_classFull_C12X {pBase : CutoffParameters} {C : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric} (S : PreparedSpatialChain pBase C P g)
    (εcut Dcut : ℕ → ℝ) (mcut : ℕ → ℕ)
    (W : ∀ m, PreparedSpatialStepRetention (S.state m) (S.state (m + 1))
      (S.accuracy m) (1 / ((m : ℝ) + 2)) (εcut m) (Dcut m) (mcut m))
    (C1 C2 : ℝ) (hεs : C.epsilon ≤ εStrong_C12X.{u}) :
    ∃ (C1hOf C2hOf qhOf δmaxOf ρmaxOf εcapOf DcapOf : ℕ → ℝ) (mcapOf : ℕ → ℕ),
      (∀ m, 1 ≤ C1hOf m ∧ 1 ≤ C2hOf m ∧ (S.state m).prepared.qs ≤ qhOf m ∧ 0 < δmaxOf m ∧
        0 < ρmaxOf m ∧ 0 < εcapOf m ∧ 0 < DcapOf m) ∧
      ((∀ m, (S.state m).prepared.parameters.modelAccuracy ≤ εcapOf m ∧
          DcapOf m ≤ (S.state m).prepared.parameters.modelRadius ∧
          mcapOf m ≤ (S.state m).prepared.parameters.modelOrder ∧
          (S.state m).prepared.deltaBound ≤ δmaxOf m ∧
          (S.state m).prepared.radiusBound ≤ ρmaxOf m) →
        (∀ m, C1hOf m ≤ C1 ∧ C2hOf m ≤ C2 ∧ qhOf m ≤ ((S.state m).radius ^ 2)⁻¹) →
        ∀ m : ℕ,
          (W m).oldNative.EventSlabsStronglyCanonicalFull_C12X C.epsilon C.epsilon C1 C2
            (((S.state m).radius ^ 2)⁻¹) (Fin.last (W m).oldNative.eventCount) ∧
          ∀ hfinal : (W m).oldNative.time (Fin.last (W m).oldNative.eventCount) <
              (W m).oldNative.horizon,
            (W m).oldNative.StronglyCanonicalBeforeFull_C12X
              (Fin.last (W m).oldNative.eventCount)
              (((W m).oldNative.finalSlab hfinal).restrictIncoming le_rfl hfinal le_rfl)
              C.epsilon C.epsilon C1 C2 (((S.state m).radius ^ 2)⁻¹) (W m).oldNative.horizon) := by
  have hB : ∀ m, 0 < (3 : ℝ) ^ m - (S.state m).shift := fun m =>
    (S.state m).native.horizon_nonneg.trans_lt (S.state m).native_lt_capacity
  have hA := fun m => native_strongFull_of_classFull_C12X (S.state m).nativeStage
    (S.state m).nativeMetric _ C.epsilon (hB m) C.epsilon_pos hεs C.C1 C.C2 C.C1s C.C2s
    (S.state m).prepared.qcan (S.state m).prepared.qs C.tauMin C.Ctime C.Cgrad
    (S.state m).prepared.kappa C.C1_ge_one C.C2_ge_one C.C1s_ge_one C.C2s_ge_one
    (S.state m).prepared.qcan_pos (S.state m).prepared.qcan_le_qs C.tauMin_pos
    (S.state m).prepared.kappa_pos
  choose C1hOf C2hOf qhOf δmaxOf ρmaxOf εcapOf DcapOf mcapOf hC1h hC2h hqh hδ hρ hεc hD hX
    using hA
  refine ⟨C1hOf, C2hOf, qhOf, δmaxOf, ρmaxOf, εcapOf, DcapOf, mcapOf,
    fun m => ⟨hC1h m, hC2h m, hqh m, hδ m, hρ m, hεc m, hD m⟩, fun hsmall hQ m => ?_⟩
  obtain ⟨hacc, hrad, hord, hδb, hρb⟩ := hsmall m
  obtain ⟨hC1, hC2, hq⟩ := hQ m
  have hhor : (W m).oldNative.horizon ≤ (3 : ℝ) ^ m - (S.state m).shift :=
    (W m).oldNative_horizon.le
  have hctl := (S.state m).prepared.control (W m).oldNative (W m).oldNativeInitial
    (W m).oldNativeParameters (W m).oldNativeRecords hhor (W m).oldNative_class
  obtain ⟨hev, hfin⟩ := hX m _ _ _ hacc hrad hord hδb hρb (S.state m).prepared.recenter_bound
    (W m).oldNative (W m).oldNativeInitial (W m).oldNativeParameters (W m).oldNativeRecords hhor
    (W m).oldNative_class hctl.1 (W m).oldNative_estimates
  exact ⟨fun j hj => RetainedCoreHistory.stronglyCanonicalBeforeFull_mono_C12X hC1 hC2 hq
      (hev j hj),
    fun hfinal => RetainedCoreHistory.stronglyCanonicalBeforeFull_mono_C12X hC1 hC2 hq
      (hfin hfinal)⟩

/-- Consumer (type alignment): the conclusion is the frozen S16D `hnative` binder, verbatim
(text copied from `build-logs/scratch/O-C12X-S16D/G6iface.lean`); a premise-free use projects it
to the tree's truncated `EventSlabsStronglyCanonical` on every old native. -/
example {pBase : CutoffParameters} {C : ClosedBirthConstants} {P : OrientedThreeStage.{u}}
    {g : P.Metric} (S : PreparedSpatialChain pBase C P g) (εcut Dcut : ℕ → ℝ) (mcut : ℕ → ℕ)
    (W : ∀ m, PreparedSpatialStepRetention (S.state m) (S.state (m + 1))
      (S.accuracy m) (1 / ((m : ℝ) + 2)) (εcut m) (Dcut m) (mcut m))
    (C1 C2 : ℝ) (hεs : C.epsilon ≤ εStrong_C12X.{u}) :
    ∃ (C1hOf C2hOf qhOf δmaxOf ρmaxOf εcapOf DcapOf : ℕ → ℝ) (mcapOf : ℕ → ℕ),
      (∀ m, (S.state m).prepared.parameters.modelAccuracy ≤ εcapOf m ∧
          DcapOf m ≤ (S.state m).prepared.parameters.modelRadius ∧
          mcapOf m ≤ (S.state m).prepared.parameters.modelOrder ∧
          (S.state m).prepared.deltaBound ≤ δmaxOf m ∧
          (S.state m).prepared.radiusBound ≤ ρmaxOf m) →
      (∀ m, C1hOf m ≤ C1 ∧ C2hOf m ≤ C2 ∧ qhOf m ≤ ((S.state m).radius ^ 2)⁻¹) →
      (∀ m : ℕ,
        (W m).oldNative.EventSlabsStronglyCanonicalFull_C12X C.epsilon C.epsilon C1 C2
          (((S.state m).radius ^ 2)⁻¹) (Fin.last (W m).oldNative.eventCount) ∧
        ∀ hfinal : (W m).oldNative.time (Fin.last (W m).oldNative.eventCount) <
            (W m).oldNative.horizon,
          (W m).oldNative.StronglyCanonicalBeforeFull_C12X
            (Fin.last (W m).oldNative.eventCount)
            (((W m).oldNative.finalSlab hfinal).restrictIncoming le_rfl hfinal le_rfl)
            C.epsilon C.epsilon C1 C2 (((S.state m).radius ^ 2)⁻¹) (W m).oldNative.horizon) ∧
      ∀ m : ℕ, (W m).oldNative.EventSlabsStronglyCanonical C.epsilon C.epsilon C1 C2
          (((S.state m).radius ^ 2)⁻¹) (Fin.last (W m).oldNative.eventCount) := by
  obtain ⟨C1hOf, C2hOf, qhOf, δmaxOf, ρmaxOf, εcapOf, DcapOf, mcapOf, -, h⟩ :=
    hnative_of_classFull_C12X S εcut Dcut mcut W C1 C2 hεs
  refine ⟨C1hOf, C2hOf, qhOf, δmaxOf, ρmaxOf, εcapOf, DcapOf, mcapOf, fun hsmall hQ => ?_⟩
  have hnative := h hsmall hQ
  exact ⟨hnative, fun m => (hnative m).1.toEventSlabsStronglyCanonical⟩

end GC.GeneralFlow

end
