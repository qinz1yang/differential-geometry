import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.KcoreEscapePos_O29
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.KcanCentreVolume_O14

/-!
# CH12-O31, group 1: re-centred witnesses at the escape (`[FROZEN] CH12-O31` G1)

KL70.2 step (a'), volume part.  Along an escaping sequence (`hNoEscPos` data) no canonical witness
at the base point `y n` is guaranteed (`R(y n)` may sit exactly at the strict threshold).  For every
level `lam > 1` and every radius `r > ρ` (the escape radius), the intermediate value theorem on the
path-connected ball `B(y n, r/√R(y n))` (which eventually contains `z n`, where `R(z n)/R(y n) → ∞`)
gives `w` with `R(w) = lam · R(y n)`, strictly above the threshold.  At `w` we take the `hStrong`
witness (`[FROZEN] CH12-O23 hStrong`), keep its strong-neck clause, and add the normalized centre
volume `vol B(w, b) ≥ κ b³` (`b ≤ C2^{-1/2}`, metric scaled by `R(w)`) of
`centre_volume_of_witness_O14`; `κ = κ(ε, C1, C2)` is uniform (no `κ(t)`).
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian Set Filter
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff ENNReal NNReal

namespace GC.LongTime.Ch12

universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
  {δ : ℝ → ℝ}

/-- **Re-centred witness supply** (`[FROZEN] CH12-O31` G1). -/
theorem exists_recentred_witness_O31 (Hp : GC.LongTime.AnalyticSurgeryProfile F δ)
    (hStrong : ∃ T : ℝ, ∀ s : RegularSlice F.observation, T ≤ s.time →
      ∀ x : s.stage.Carrier,
      ∀ hR : (Hp.parameters.neckRadius s.time ^ 2)⁻¹ < metricScalarAt s.metric x,
      ∃ W : SpatialCanonicalWitness s.metric Hp.epsilon Hp.C1 Hp.C2 x,
        W.capTubeHasNeckChart Hp.epsilon ∧
        ∀ nk, W.alternative = SpatialCanonicalAlternative.neck nk →
          ∃ (U : TopologicalSpace.Opens s.stage.Carrier) (hxU : x ∈ U)
            (S : SolutionOn (I := ThreeModel) (M := U)
              (RealTimeInterval.closed (s.time - (metricScalarAt s.metric x)⁻¹) s.time
                (sub_le_self _ (inv_nonneg.mpr
                  (lt_of_le_of_lt (inv_nonneg.mpr (sq_nonneg _)) hR).le)))),
            IsSolutionOn S ∧ S.base.metric s.time = s.metric.restrictOpen U ∧
            Nonempty (StrongNeck S Hp.epsilon ⟨x, hxU⟩ s.time)) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (s : ℕ → RegularSlice F.observation)
      (y z : ∀ n, (s n).stage.Carrier) (ρ : ℝ),
      Tendsto (fun n => (s n).time) atTop atTop →
      (∀ n, (Hp.parameters.neckRadius (s n).time ^ 2)⁻¹ ≤
        metricScalarAt (s n).metric (y n)) →
      Tendsto (fun n => metricScalarAt (s n).metric (y n)) atTop atTop →
      Tendsto (fun n => metricScalarAt (s n).metric (z n) /
        metricScalarAt (s n).metric (y n)) atTop atTop →
      (∀ r : ℝ, ρ < r → ∀ᶠ n in atTop, z n ∈ riemannianBallOf (s n).metric (y n)
        (r / Real.sqrt (metricScalarAt (s n).metric (y n)))) →
      ∀ lam : ℝ, 1 < lam → ∀ r : ℝ, ρ < r → ∀ᶠ n in atTop,
        ∃ w : (s n).stage.Carrier,
          w ∈ riemannianBallOf (s n).metric (y n)
            (r / Real.sqrt (metricScalarAt (s n).metric (y n))) ∧
          metricScalarAt (s n).metric w = lam * metricScalarAt (s n).metric (y n) ∧
          ∃ hR : (Hp.parameters.neckRadius (s n).time ^ 2)⁻¹ < metricScalarAt (s n).metric w,
          ∃ W : SpatialCanonicalWitness (s n).metric Hp.epsilon Hp.C1 Hp.C2 w,
            W.capTubeHasNeckChart Hp.epsilon ∧
            (W.alternative.requiresVolume → ∀ b : ℝ, 0 < b → b ≤ (Real.sqrt Hp.C2)⁻¹ →
              ENNReal.ofReal (κ * b ^ 3) ≤
                riemannianVolumeMeasure ThreeModel (s n).stage.Carrier
                  (scaleMetric (metricScalarAt (s n).metric w) W.Q_pos (s n).metric)
                  (riemannianBallOf
                    (scaleMetric (metricScalarAt (s n).metric w) W.Q_pos (s n).metric) w b)) ∧
            ∀ nk, W.alternative = SpatialCanonicalAlternative.neck nk →
              ∃ (U : TopologicalSpace.Opens (s n).stage.Carrier) (hxU : w ∈ U)
                (S : SolutionOn (I := ThreeModel) (M := U)
                  (RealTimeInterval.closed
                    ((s n).time - (metricScalarAt (s n).metric w)⁻¹) (s n).time
                    (sub_le_self _ (inv_nonneg.mpr
                      (lt_of_le_of_lt (inv_nonneg.mpr (sq_nonneg _)) hR).le)))),
                IsSolutionOn S ∧ S.base.metric (s n).time = (s n).metric.restrictOpen U ∧
                Nonempty (StrongNeck S Hp.epsilon ⟨w, hxU⟩ (s n).time) := by
  obtain ⟨κ, hκ, hvol⟩ := centre_volume_of_witness_O14.{u} Hp.epsilon Hp.C1 Hp.C2
    (lt_of_lt_of_le one_pos Hp.C2_ge_one)
  obtain ⟨T, hT⟩ := hStrong
  refine ⟨κ, hκ, ?_⟩
  intro s y z ρ htime hneck hRy hratio hesc lam hlam r hr
  filter_upwards [hesc r hr, hratio.eventually (eventually_gt_atTop lam),
    htime.eventually (eventually_ge_atTop T), hRy.eventually (eventually_ge_atTop 1)]
    with n hz hc hTn hR1
  set g' := (s n).metric with hg'
  set Ry : ℝ := metricScalarAt g' (y n) with hRydef
  have hRpos : 0 < Ry := lt_of_lt_of_le one_pos hR1
  have hsq : 0 < Real.sqrt Ry := Real.sqrt_pos.mpr hRpos
  have hr0 : 0 < r := by
    by_contra hneg
    rw [not_lt] at hneg
    have hle : r / Real.sqrt Ry ≤ 0 := div_nonpos_of_nonpos_of_nonneg hneg hsq.le
    change riemannianEDistOf g' (y n) (z n) < ENNReal.ofReal (r / Real.sqrt Ry) at hz
    rw [ENNReal.ofReal_of_nonpos hle] at hz
    exact ENNReal.not_lt_zero hz
  have hzR : lam * Ry < metricScalarAt g' (z n) := (lt_div_iff₀ hRpos).mp hc
  -- intermediate value on the path-connected ball
  have hB := (isPathConnected_riemannianBallOf g' (y n)
    (div_pos hr0 hsq)).isConnected.isPreconnected
  have hcont : Continuous (metricScalarAt g') := (metricScalar_smooth g').continuous
  have hyB : y n ∈ riemannianBallOf g' (y n) (r / Real.sqrt Ry) := by
    change riemannianEDistOf g' (y n) (y n) < ENNReal.ofReal _
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr (div_pos hr0 hsq)
  have hmid : lam * Ry ∈ Icc (metricScalarAt g' (y n)) (metricScalarAt g' (z n)) := by
    constructor
    · rw [← hRydef]; nlinarith
    · exact hzR.le
  obtain ⟨w, hwB, hw⟩ := hB.intermediate_value hyB hz hcont.continuousOn hmid
  have hq : (Hp.parameters.neckRadius (s n).time ^ 2)⁻¹ < metricScalarAt (s n).metric w := by
    have := hneck n
    change _ ≤ Ry at this
    change _ < metricScalarAt g' w
    rw [hw]; nlinarith
  obtain ⟨W, hchart, hstrong⟩ := hT (s n) hTn w hq
  exact ⟨w, hwB, hw, hq, W, hchart, fun hreq b hb hbC => hvol W hchart hreq b hb hbC, hstrong⟩

end GC.LongTime.Ch12
