import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CapKcapMain_S73

/-!
# CH12-S73, group 3: `CompatibleUpgradedCapRecords_v2_S73` and `hKcap_v2_S73` (lead request after review R4, D-R4-4)

`v2 := v1 ∧ age clause`, the age clause being `nominalRadius_old ^ 2 ≤ eventTime` for every old record.
That clause is the record field `GeometricCutoffRecord.nominal_time` of the profile's own records, so
`compat_v2_of_v1_S73` proves it from `Hp` alone: the clause adds no hypothesis beyond `v1`.  (It is exactly
the fact used inside `capScale_facts_S58` at `hNt`/`htj'` to get `s.time ≤ 2 * eventTime` from `θ * Ccmp ≤ 1`.)
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace GC.LongTime.Ch12

universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ}

/-- `[FROZEN] CH12-S73 CompatibleUpgradedCapRecords_v2`: S58's supply shape together with the age clause
`(nominal radius of the old record)² ≤ (its event time)` (lead-authorised def, review R4 D-R4-4). -/
def CompatibleUpgradedCapRecords_v2_S73 (Hp : GC.LongTime.AnalyticSurgeryProfile F δ) : Prop :=
  CompatibleUpgradedCapRecords_S58 Hp ∧
    ∀ (n : ℕ) (i : Fin (F.tower.history n).eventCount)
      (b' : ((F.tower.history n).toHistory.event i).RetainedBoundaryIndex),
      ((Hp.records n i).nominalRadius ⟨b'.1.1⟩) ^ 2 ≤ (F.tower.history n).time i.succ

/-- v2 → v1 adapter. -/
theorem compat_v1_of_v2_S73 {Hp : GC.LongTime.AnalyticSurgeryProfile F δ}
    (h : CompatibleUpgradedCapRecords_v2_S73 Hp) : CompatibleUpgradedCapRecords_S58 Hp := h.1

/-- The age clause is automatic (record field `nominal_time`): v1 → v2. -/
theorem compat_v2_of_v1_S73 {Hp : GC.LongTime.AnalyticSurgeryProfile F δ}
    (h : CompatibleUpgradedCapRecords_S58 Hp) : CompatibleUpgradedCapRecords_v2_S73 Hp :=
  ⟨h, fun n i _b' => (Hp.records n i).nominal_time _⟩

/-- `hKcap_S73` with the v2 supply shape (same conclusion, `hKcap_S48_shape` verbatim). -/
theorem hKcap_v2_S73 (Hp : GC.LongTime.AnalyticSurgeryProfile F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    (hP3 : P3_O2 Hp) (hcompat : CompatibleUpgradedCapRecords_v2_S73 Hp)
    (Ctime : ℝ≥0) (hP2 : P2_O2 Hp Ctime) :
    ∀ A : ℝ, 0 < A → ∃ Q _T θ : ℝ, 1 ≤ Q ∧ 0 < θ ∧ ∀ Dcap : ℝ, StandardCap.transitionEnd < Dcap →
      ∃ T' : ℝ, ∀ s : RegularSlice F.observation, T' ≤ s.time → ∀ T₀ : ℝ, T' ≤ T₀ → T₀ ≤ s.time →
      ∀ (p : CutoffParameters)
        (records : ∀ i : Fin (sliceHistoryR_O3 F s).eventCount,
          T₀ - θ ≤ (sliceHistoryR_O3 F s).time i.succ →
          GeometricCutoffRecord (sliceHistoryR_O3 F s).toHistory i p),
        (p.delta = Hp.parameters.delta ∧ p.neckRadius = Hp.parameters.neckRadius ∧
          p.fixed = Hp.parameters.fixed ∧ p.recenterConstant = Hp.parameters.recenterConstant ∧
          32 * (Dcap + 1 + 4 * A) + 2 ≤ p.modelRadius ∧
          (∀ i hi b, linkedCanonicalWindow_O2 ((records i hi).static b))) →
        ∀ y : s.stage.Carrier,
        (∃ (j : Fin (sliceHistoryR_O3 F s).eventCount)
            (hj : T₀ - θ ≤ (sliceHistoryR_O3 F s).time j.succ)
            (hl : j.succ ≤ Fin.last (sliceHistoryR_O3 F s).eventCount)
            (B : BackwardPointTrace (sliceHistoryR_O3 F s).toHistory j.succ
              (Fin.last (sliceHistoryR_O3 F s).eventCount) hl y)
            (b : ((sliceHistoryR_O3 F s).toHistory.event j).RetainedBoundaryIndex)
            (x : standardCapWindow p.modelRadius),
            B.point j.succ le_rfl hl = ((records j hj).static b).window x ∧ ‖x.val‖ < Dcap + 1 ∧
              s.time - (sliceHistoryR_O3 F s).time j.succ ≤
                θ * (((records j hj).static b).neck.scale)⁻¹) →
        ∀ z ∈ riemannianBallOf s.metric y (A / Real.sqrt (metricScalarAt s.metric y)),
          metricScalarAt s.metric z ≤ Q * metricScalarAt s.metric y :=
  hKcap_S73 Hp hdec hP3 (compat_v1_of_v2_S73 hcompat) Ctime hP2

end GC.LongTime.Ch12
