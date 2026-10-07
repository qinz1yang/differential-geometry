import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.KcoreEscape_O29
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornGeometry
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SpatialBoundedCurvatureAtDistance

/-!
# CH12-O29, group 2: the escape radius is at least `1/4` (`[FROZEN v2] CH12-O29 G2`)

`hNoEsc_of_pos_O29`: `hNoEsc` from `hStrong` (`[FROZEN] CH12-O23 hStrong`) and `hNoEscPos`
(= `hNoEsc` with the extra premise `1 / 4 ≤ ρ`).  No canonical witness at the base point is used
(it may sit exactly at the strict threshold): if `z ∈ B(y, r/√R(y))`, `r < 1/4`, had
`R(z) > (2|C2|+2) R(y)`, the intermediate value theorem on the path-connected ball gives `w` with
`R(w) = 2 R(y)` (strictly above the threshold); the hStrong witness at `w` bounds `R(z) ≤ 2 C2 R(y)`
since `d(w, z) < 2r/√R(y) < 1/√(2R(y))`.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian Set Filter
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff ENNReal NNReal

namespace GC.LongTime.Ch12

universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
  {δ : ℝ → ℝ}

/-- **Escape radius `≥ 1/4`** (`[FROZEN v2] CH12-O29 G2`). -/
theorem hNoEsc_of_pos_O29 (Hp : GC.LongTime.AnalyticSurgeryProfile F δ)
    (capPt : ℝ → ∀ s : RegularSlice F.observation, s.stage.Carrier → Prop)
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
            Nonempty (StrongNeck S Hp.epsilon ⟨x, hxU⟩ s.time))
    (hNoEscPos : ∀ A : ℝ, 0 < A → ∀ (s : ℕ → RegularSlice F.observation)
      (y z : ∀ n, (s n).stage.Carrier) (ρ : ℝ),
      Tendsto (fun n => (s n).time) atTop atTop →
      (∀ n, (Hp.parameters.neckRadius (s n).time ^ 2)⁻¹ ≤
        metricScalarAt (s n).metric (y n)) →
      Tendsto (fun n => metricScalarAt (s n).metric (y n)) atTop atTop →
      (∀ n, ¬ capPt A (s n) (y n)) →
      0 ≤ ρ → ρ ≤ A →
      (∀ n, z n ∈ riemannianBallOf (s n).metric (y n)
        (A / Real.sqrt (metricScalarAt (s n).metric (y n)))) →
      Tendsto (fun n => metricScalarAt (s n).metric (z n) /
        metricScalarAt (s n).metric (y n)) atTop atTop →
      (∀ r : ℝ, r < ρ → ∃ C : ℝ, ∀ᶠ n in atTop,
        ∀ w ∈ riemannianBallOf (s n).metric (y n)
          (r / Real.sqrt (metricScalarAt (s n).metric (y n))),
          metricScalarAt (s n).metric w ≤ C * metricScalarAt (s n).metric (y n)) →
      (∀ r : ℝ, ρ < r → ∀ᶠ n in atTop, z n ∈ riemannianBallOf (s n).metric (y n)
        (r / Real.sqrt (metricScalarAt (s n).metric (y n)))) →
      1 / 4 ≤ ρ →
      False)
    :
    ∀ A : ℝ, 0 < A → ∀ (s : ℕ → RegularSlice F.observation)
      (y z : ∀ n, (s n).stage.Carrier) (ρ : ℝ),
      Tendsto (fun n => (s n).time) atTop atTop →
      (∀ n, (Hp.parameters.neckRadius (s n).time ^ 2)⁻¹ ≤
        metricScalarAt (s n).metric (y n)) →
      Tendsto (fun n => metricScalarAt (s n).metric (y n)) atTop atTop →
      (∀ n, ¬ capPt A (s n) (y n)) →
      0 ≤ ρ → ρ ≤ A →
      (∀ n, z n ∈ riemannianBallOf (s n).metric (y n)
        (A / Real.sqrt (metricScalarAt (s n).metric (y n)))) →
      Tendsto (fun n => metricScalarAt (s n).metric (z n) /
        metricScalarAt (s n).metric (y n)) atTop atTop →
      (∀ r : ℝ, r < ρ → ∃ C : ℝ, ∀ᶠ n in atTop,
        ∀ w ∈ riemannianBallOf (s n).metric (y n)
          (r / Real.sqrt (metricScalarAt (s n).metric (y n))),
          metricScalarAt (s n).metric w ≤ C * metricScalarAt (s n).metric (y n)) →
      (∀ r : ℝ, ρ < r → ∀ᶠ n in atTop, z n ∈ riemannianBallOf (s n).metric (y n)
        (r / Real.sqrt (metricScalarAt (s n).metric (y n)))) →
      False := by
  intro A hA s y z ρ htime hneck hRy hcap hρ0 hρA hzA hratio hbdd hesc
  refine hNoEscPos A hA s y z ρ htime hneck hRy hcap hρ0 hρA hzA hratio hbdd hesc ?_
  obtain ⟨T, hT⟩ := hStrong
  by_contra hρ1
  rw [not_le] at hρ1
  set r : ℝ := (ρ + 1 / 4) / 2 with hr
  have hr0 : 0 < r := by rw [hr]; linarith
  have hr1 : r < 1 / 4 := by rw [hr]; linarith
  have h1 := hesc r (by rw [hr]; linarith)
  have h2 := hratio.eventually (eventually_gt_atTop (2 * |Hp.C2| + 2))
  have h3 := htime.eventually (eventually_ge_atTop T)
  have h4 := hRy.eventually (eventually_ge_atTop 1)
  obtain ⟨n, hz, hc2, hTn, hR1⟩ := (h1.and (h2.and (h3.and h4))).exists
  set g' := (s n).metric with hg'
  set Ry : ℝ := metricScalarAt g' (y n) with hRydef
  have hRpos : 0 < Ry := lt_of_lt_of_le one_pos hR1
  have hsq : 0 < Real.sqrt Ry := Real.sqrt_pos.mpr hRpos
  have hzR : (2 * |Hp.C2| + 2) * Ry < metricScalarAt g' (z n) := (lt_div_iff₀ hRpos).mp hc2
  -- intermediate value on the path-connected ball
  have hB := (isPathConnected_riemannianBallOf g' (y n)
    (div_pos hr0 hsq)).isConnected.isPreconnected
  have hcont : Continuous (metricScalarAt g') := (metricScalar_smooth g').continuous
  have hyB : y n ∈ riemannianBallOf g' (y n) (r / Real.sqrt Ry) := by
    change riemannianEDistOf g' (y n) (y n) < ENNReal.ofReal _
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr (div_pos hr0 hsq)
  have hmid : 2 * Ry ∈ Icc (metricScalarAt g' (y n)) (metricScalarAt g' (z n)) := by
    constructor
    · rw [← hRydef]; linarith
    · nlinarith [abs_nonneg Hp.C2]
  obtain ⟨w, hwB, hw⟩ := hB.intermediate_value hyB hz hcont.continuousOn hmid
  have hq : (Hp.parameters.neckRadius (s n).time ^ 2)⁻¹ < metricScalarAt (s n).metric w := by
    have := hneck n
    change _ ≤ Ry at this
    change _ < metricScalarAt g' w
    rw [hw]; linarith
  obtain ⟨W, -, -⟩ := hT (s n) hTn w hq
  have hsqrt2 : Real.sqrt 2 < 3 / 2 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hzw : z n ∈ riemannianBallOf (s n).metric w (Real.sqrt (metricScalarAt (s n).metric w))⁻¹ := by
    change riemannianEDistOf g' w (z n) < ENNReal.ofReal (Real.sqrt (metricScalarAt g' w))⁻¹
    have hwy : riemannianEDistOf g' w (y n) < ENNReal.ofReal (r / Real.sqrt Ry) := by
      rw [riemannianEDistOf_comm]; exact hwB
    have hyz : riemannianEDistOf g' (y n) (z n) < ENNReal.ofReal (r / Real.sqrt Ry) := hz
    calc riemannianEDistOf g' w (z n)
        ≤ riemannianEDistOf g' w (y n) + riemannianEDistOf g' (y n) (z n) :=
          riemannianEDistOf_triangle g' w (y n) (z n)
      _ < ENNReal.ofReal (r / Real.sqrt Ry) + ENNReal.ofReal (r / Real.sqrt Ry) :=
          ENNReal.add_lt_add hwy hyz
      _ = ENNReal.ofReal (r / Real.sqrt Ry + r / Real.sqrt Ry) :=
          (ENNReal.ofReal_add (div_pos hr0 hsq).le (div_pos hr0 hsq).le).symm
      _ ≤ ENNReal.ofReal (Real.sqrt (metricScalarAt g' w))⁻¹ := by
          apply ENNReal.ofReal_le_ofReal
          rw [hw, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), mul_inv]
          have h2pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
          have h2r : 2 * r ≤ (Real.sqrt 2)⁻¹ := by
            rw [le_inv_comm₀ (by linarith) h2pos, inv_eq_one_div, le_div_iff₀ (by linarith)]
            nlinarith [mul_lt_mul_of_pos_right hsqrt2 hr0]
          rw [show r / Real.sqrt Ry + r / Real.sqrt Ry = (2 * r) * (Real.sqrt Ry)⁻¹ by ring]
          exact mul_le_mul_of_nonneg_right h2r (inv_nonneg.mpr hsq.le)
  have hb := (W.scalar_bounds_of_mem_ball hzw).2
  change metricScalarAt g' (z n) ≤ Hp.C2 * metricScalarAt g' w at hb
  rw [hw] at hb
  have : Hp.C2 * (2 * Ry) ≤ (2 * |Hp.C2|) * Ry := by
    nlinarith [le_abs_self Hp.C2]
  linarith

end GC.LongTime.Ch12
