import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.MicroZeroOrderDoubled_O23
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.MicroSliceKernelThetaL_S44
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.LateLinkedWitness_S48

/-!
# CH12-O29, group 3: the A-indexed cap predicate and `hcap` from the K-cap (`[FROZEN] CH12-O29 G3`)

* `kcapPt_O29 Hp hKcap Dcap hD`: the split predicate of `hKcan_v2_of_branchesA_O23` — `y` is a recent cap
  point in the sense of the K-cap of `[FROZEN v2] CH12-S48` at `Dcap A`, with that K-cap's `θ(A)` and
  threshold `T'(A)` (chosen by `Classical.choose`).
* `hcap_of_Kcap_O29`: the K-cap binder `hcap` for this predicate.
-/

set_option autoImplicit false
noncomputable section
open Set Filter
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff Topology NNReal ENNReal
namespace GC.LongTime.Ch12
universe u
variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ}

/-- The A-indexed cap predicate (brief O29 (d)). -/
def kcapPt_O29 (Hp : GC.LongTime.AnalyticSurgeryProfile F δ)
    (hKcap :
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
            metricScalarAt s.metric z ≤ Q * metricScalarAt s.metric y)
    (Dcap : ℝ → ℝ) (hD : ∀ A : ℝ, StandardCap.transitionEnd < Dcap A) :
    ℝ → ∀ s : RegularSlice F.observation, s.stage.Carrier → Prop :=
  fun A s y =>
    if hA : 0 < A then
      let θ : ℝ := (hKcap A hA).choose_spec.choose_spec.choose
      let T' : ℝ := ((hKcap A hA).choose_spec.choose_spec.choose_spec.2.2 (Dcap A) (hD A)).choose
      ∃ T₀ : ℝ, T' ≤ T₀ ∧ T₀ ≤ s.time ∧
      ∃ (p : CutoffParameters)
        (records : ∀ i : Fin (sliceHistoryR_O3 F s).eventCount,
          T₀ - θ ≤ (sliceHistoryR_O3 F s).time i.succ →
          GeometricCutoffRecord (sliceHistoryR_O3 F s).toHistory i p),
      (p.delta = Hp.parameters.delta ∧ p.neckRadius = Hp.parameters.neckRadius ∧
          p.fixed = Hp.parameters.fixed ∧ p.recenterConstant = Hp.parameters.recenterConstant ∧
          32 * (Dcap A + 1 + 4 * A) + 2 ≤ p.modelRadius ∧
          (∀ i hi b, linkedCanonicalWindow_O2 ((records i hi).static b))) ∧
      (∃ (j : Fin (sliceHistoryR_O3 F s).eventCount)
            (hj : T₀ - θ ≤ (sliceHistoryR_O3 F s).time j.succ)
            (hl : j.succ ≤ Fin.last (sliceHistoryR_O3 F s).eventCount)
            (B : BackwardPointTrace (sliceHistoryR_O3 F s).toHistory j.succ
              (Fin.last (sliceHistoryR_O3 F s).eventCount) hl y)
            (b : ((sliceHistoryR_O3 F s).toHistory.event j).RetainedBoundaryIndex)
            (x : standardCapWindow p.modelRadius),
            B.point j.succ le_rfl hl = ((records j hj).static b).window x ∧ ‖x.val‖ < Dcap A + 1 ∧
              s.time - (sliceHistoryR_O3 F s).time j.succ ≤
                θ * (((records j hj).static b).neck.scale)⁻¹)
    else False

/-- `hcap` (K-cap binder of `hKcan_v2_of_branchesA_O23`) for `kcapPt_O29`. -/
theorem hcap_of_Kcap_O29 (Hp : GC.LongTime.AnalyticSurgeryProfile F δ)
    (hKcap :
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
            metricScalarAt s.metric z ≤ Q * metricScalarAt s.metric y)
    (Dcap : ℝ → ℝ) (hD : ∀ A : ℝ, StandardCap.transitionEnd < Dcap A) :
    ∀ A : ℝ, 0 < A → ∃ Q Λ T : ℝ, 1 ≤ Q ∧ 1 ≤ Λ ∧
      ∀ s : RegularSlice F.observation, T ≤ s.time → ∀ y : s.stage.Carrier,
        (Hp.parameters.neckRadius s.time ^ 2)⁻¹ ≤ metricScalarAt s.metric y →
        Λ ≤ metricScalarAt s.metric y → kcapPt_O29 Hp hKcap Dcap hD A s y →
        ∀ z ∈ riemannianBallOf s.metric y (A / Real.sqrt (metricScalarAt s.metric y)),
          metricScalarAt s.metric z ≤ Q * metricScalarAt s.metric y := by
  intro A hA
  have hspec := (hKcap A hA).choose_spec.choose_spec.choose_spec
  have hT' := (hspec.2.2 (Dcap A) (hD A)).choose_spec
  refine ⟨(hKcap A hA).choose, 1, (hspec.2.2 (Dcap A) (hD A)).choose, hspec.1, le_rfl, ?_⟩
  intro s hs y _ _ hc z hz
  simp only [kcapPt_O29, hA, ↓reduceDIte] at hc
  obtain ⟨T₀, hT₀, hT₀s, p, records, hrec, hcp⟩ := hc
  exact hT' s (hT₀.trans hT₀s) T₀ hT₀ hT₀s p records hrec y hcp z hz

end GC.LongTime.Ch12
