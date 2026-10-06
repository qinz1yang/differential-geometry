import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.MicroGlueSliceKernel
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.MicroP5Linked_O13

/-!
# CH12-S44, group 2: the θ-kernel on `P5Linked_O13` records with window radius `≥ 32 (Dcap+1) + 2`

`micro_slice_scalar_bound_thetaL_S44` is `micro_slice_scalar_bound_theta_O13` (CH12-O13 G2) with
`hP5 : P5_O3 Hp` replaced by `P5Linked_O13 Hp`, and the returned records additionally carry
(a) the profile parameters' `delta`, `neckRadius`, `fixed`, `recenterConstant`,
(b) `linkedCanonicalWindow_O2` on every static cap, and
(c) model radius `≥ 32 (Dcap + 1) + 2`, so that the cap-window kernel
`..._of_radius_lower_bound` can be run with `r := Dcap + 1`, `D := 32 r + 1`, `Dbig := p.modelRadius`
(closing the window-radius gap `Dcap + 1` versus `capCoreRadius_O2`).
Same proof as G2; `P5Linked_O13` is applied at the radius `max Rrad (32 (Dcap+1) + 2)`.
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

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
  {δ : ℝ → ℝ}

theorem micro_slice_scalar_bound_thetaL_S44 (Hp : GC.LongTime.AnalyticSurgeryProfile F δ)
    (hP4 : P4_O2 Hp) (Ctime : ℝ≥0) (hP2 : P2_O2 Hp Ctime) (hP5 : P5Linked_O13 Hp)
    (w : ℝ) (hw : 0 < w) (A : ℝ) (hA : 0 < A) (Cq θ : ℝ) (hθ : 0 < θ) :
    ∃ Q Λ Dcap T : ℝ, 1 ≤ Q ∧ 1 ≤ Λ ∧ StandardCap.transitionEnd < Dcap ∧
    ∀ s : RegularSlice F.observation, T ≤ s.time →
    ∃ (p : CutoffParameters)
      (records : ∀ i : Fin (sliceHistoryR_O3 F s).eventCount,
        T - θ ≤ (sliceHistoryR_O3 F s).time i.succ →
        GeometricCutoffRecord (sliceHistoryR_O3 F s).toHistory i p),
      p.delta = Hp.parameters.delta ∧ p.neckRadius = Hp.parameters.neckRadius ∧
      p.fixed = Hp.parameters.fixed ∧ p.recenterConstant = Hp.parameters.recenterConstant ∧
      32 * (Dcap + 1) + 2 ≤ p.modelRadius ∧
      (∀ i hi b, linkedCanonicalWindow_O2 ((records i hi).static b)) ∧
      ∀ (p₀ y : s.stage.Carrier) (r : ℝ), 0 < r →
        (∀ x ∈ riemannianBallOf s.metric p₀ r, SectionalBoundedBelowAt s.metric x (-(r ^ 2)⁻¹)) →
        ENNReal.ofReal (w * r ^ 3) ≤
          riemannianVolumeMeasure ThreeModel s.stage.Carrier s.metric
            (riemannianBallOf s.metric p₀ r) →
        y ∈ riemannianBallOf s.metric p₀ (r / 8) →
        (Hp.parameters.neckRadius s.time ^ 2)⁻¹ ≤ Cq * metricScalarAt s.metric y →
        Λ ≤ metricScalarAt s.metric y → Λ ≤ metricScalarAt s.metric y * s.time →
        Λ ≤ r / 8 * Real.sqrt (metricScalarAt s.metric y) →
        (¬ ∃ (j : Fin (sliceHistoryR_O3 F s).eventCount)
          (hj : T - θ ≤ (sliceHistoryR_O3 F s).time j.succ)
          (hl : j.succ ≤ Fin.last (sliceHistoryR_O3 F s).eventCount)
          (B : BackwardPointTrace (sliceHistoryR_O3 F s).toHistory j.succ
            (Fin.last (sliceHistoryR_O3 F s).eventCount) hl y)
          (b : ((sliceHistoryR_O3 F s).toHistory.event j).RetainedBoundaryIndex)
          (x : standardCapWindow p.modelRadius),
          B.point j.succ le_rfl hl = ((records j hj).static b).window x ∧ ‖x.val‖ < Dcap + 1 ∧
            s.time - (sliceHistoryR_O3 F s).time j.succ ≤
              θ * (((records j hj).static b).neck.scale)⁻¹) →
        ∀ z ∈ riemannianBallOf s.metric y (A / Real.sqrt (metricScalarAt s.metric y)),
          metricScalarAt s.metric z ≤ Q * metricScalarAt s.metric y := by
  obtain ⟨κ, hκ, hvolκ⟩ := local_volume_of_volume_test_O3.{u} w hw
  obtain ⟨phi, hphi, hpin⟩ := slice_pinching_O3 Hp
  obtain ⟨Q, Λ, Dcap, Rrad, ζ₀, hQ, hΛ, hD, hDR, hζ, hker⟩ :=
    exists_scalar_bound_at_distance_of_not_capWindowPoint_closed_late_O3L.{u} (ε := Hp.epsilon)
      hP4 κ Hp.C1 Hp.C2 hκ Ctime ⟨Hp.C2, by linarith [Hp.C2_ge_one]⟩ hphi A hA Cq θ hθ
  obtain ⟨T₅, hT₅⟩ := hP5 (max Rrad (32 * (Dcap + 1) + 2)) ζ₀ 2 hζ
  refine ⟨Q, Λ, Dcap, T₅ + θ, hQ, hΛ, hD, fun s hs => ?_⟩
  obtain ⟨p, hpd, hpn, hpf, hpc, hRp', hζp, hmp, recs, hlink⟩ := hT₅ (sliceIndexR_O3 F s)
  have hRp : Rrad ≤ p.modelRadius := (le_max_left _ _).trans hRp'
  have hcan : ∀ i hi b, ((recs i hi).static b).hasCanonicalWindow := fun i hi b =>
    linkedCanonicalWindow_hasCanonicalWindow_O2 _ (hlink i hi b)
  let H₀ := F.tower.history (sliceIndexR_O3 F s)
  let k := sliceStageR_O3 F s
  let records : ∀ i : Fin (sliceHistoryR_O3 F s).eventCount,
      T₅ + θ - θ ≤ (sliceHistoryR_O3 F s).time i.succ →
      GeometricCutoffRecord (sliceHistoryR_O3 F s).toHistory i p := fun i hi =>
    H₀.geometricCutoffRecordOfPrefix k
      (recs (Fin.castLE (Nat.le_of_lt_succ k.isLt) i) (by
        have : T₅ + θ - θ = T₅ := by ring
        rw [this] at hi; exact hi))
  refine ⟨p, records, hpd, hpn, hpf, hpc, (le_max_right _ _).trans hRp', fun i hi b => hlink _ _ b, ?_⟩
  intro p₀ y r hr hsec hvol hy hqy hΛy hΛt hρ hnot z hz
  have hm := sliceSlabR_metric_time_O3 F s
  have hrad := Hp.parameters.neckRadius_pos s.time s.positive.le
  have hq : 0 < (Hp.parameters.neckRadius s.time ^ 2)⁻¹ := by positivity
  have hloc := hvolκ s.stage.Carrier s.metric p₀ r hr hsec hvol y hy
  rw [← hm] at hloc hqy hΛy hΛt hρ hz ⊢
  obtain ⟨hpin1, hpin2, -⟩ := hpin s
  exact hker (sliceHistoryR_O3 F s) rfl (sliceSlabR_O3 F s) (sliceSlabR_initial_O3 F s)
    (T₅ + θ - θ) records (fun i hi b => hcan _ _ b) hRp (le_trans (by norm_num) hmp) hζp
    (by linarith) y _ (r / 8) hq hqy hΛy hΛt (sliceSlab_canonical_O3 Hp s)
    (sliceHistory_eventSlabsDerivative_O3 Hp s Ctime _ hP2 le_rfl)
    (sliceSlab_derivative_O3 Hp s Ctime _ hP2 le_rfl) (sliceSlab_gradient_O3 Hp s _ le_rfl)
    hpin1 hpin2 hloc hρ hnot z hz

end GC.LongTime.Ch12
