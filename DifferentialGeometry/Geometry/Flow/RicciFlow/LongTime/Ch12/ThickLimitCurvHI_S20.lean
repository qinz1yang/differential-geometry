import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickLimitSeedReduce_O5
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.ExteriorDiskFlow
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HamiltonIveyCurvatureBound
import DifferentialGeometry.Geometry.Comparison.SectionalLowerBoundScaling
import DifferentialGeometry.Geometry.Curvature.Bounds.SectionalNorm

/-!
# CH12-S20 / C2 `hcurv`, group HI: Hamilton–Ivey conversion at a regular slice

A normalised scalar-curvature upper bound `R(t⁻¹ g(t)) ≤ K` at a point `y` of a regular slice
gives `sec(t⁻¹ g(t)) ≥ -C(K)` at `y`, with `C(K)` independent of the slice, the time, the point
and the history (profile pinching with `a = pinchingShift + t`).
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Tensor0SBundle
open GC.LongTime Set Filter
open scoped Manifold ContDiff ENNReal Topology
namespace GC.LongTime.Ch12
universe u

/-- The profile pinching transfers from `postMetric` to the metric of a regular slice. -/
theorem slice_inFixedHamiltonIveyRegion_S20 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} (H : AnalyticSurgeryProfile F δ)
    (s : RegularSlice F.observation) (y : s.stage.Carrier) :
    InFixedHamiltonIveyRegion s.metric (H.pinchingShift + s.time) y := by
  have key : ∀ (Y : OrientedThreeStage.{u}) (hY : postStage F.observation s.time = Y)
      (m : Y.Metric), HEq (postMetric F.observation s.time) m → ∀ z : Y.Carrier,
      InFixedHamiltonIveyRegion m (H.pinchingShift + s.time) z := by
    intro Y hY m hm z
    subst hY
    have := eq_of_heq hm
    subst this
    exact H.pinching s.time s.positive.le z
  exact key s.stage (postStage_regularSlice F.observation s) s.metric
    (postMetric_regularSlice F.observation s) y

/-- **HI.**  Normalised scalar upper bound `≤ K` gives normalised sectional lower bound
`-C(K)`, `C(K) = 2√3 (max K 0 / 2 + max K (e⁴))`. -/
theorem sec_lower_of_normScalar_le_S20 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} (H : AnalyticSurgeryProfile F δ)
    (s : RegularSlice F.observation) (y : s.stage.Carrier) {K : ℝ}
    (hK : metricScalarAt s.normalizedMetric y ≤ K) :
    SectionalBoundedBelowAt s.normalizedMetric y
      (-(2 * Real.sqrt 3 * (max K 0 / 2 + max K (Real.exp 4)))) := by
  have ht := s.positive
  have hsc : metricScalarAt s.normalizedMetric y = s.time * metricScalarAt s.metric y := by
    change metricScalarAt (scaleMetric s.time⁻¹ _ s.metric) y = _
    rw [metricScalarAt_scaleMetric, inv_inv]
  have hB : metricScalarAt s.metric y ≤ K / s.time := by
    rw [le_div_iff₀ ht]; nlinarith
  have hpos : 0 < H.pinchingShift + s.time := by linarith [H.pinchingShift_pos]
  have hbd := sqrt_normSq0S_le_of_fixedHamiltonIveyRegion s.metric y hpos le_rfl
    (slice_inFixedHamiltonIveyRegion_S20 H s y) hB
  have hbd2 : Real.sqrt (normSq0S s.metric y 4 (metricRm04At s.metric y)) ≤
      2 * Real.sqrt 3 * (max K 0 / 2 + max K (Real.exp 4)) / s.time := by
    refine hbd.trans ?_
    have h1 : max (K / s.time) 0 ≤ max K 0 / s.time := by
      rw [← zero_div s.time, ← max_div_div_right ht.le]; simp
    have h2 : max (K / s.time) (Real.exp 4 / (H.pinchingShift + s.time)) ≤
        max K (Real.exp 4) / s.time := by
      refine max_le ?_ ?_
      · exact div_le_div_of_nonneg_right (le_max_left _ _) ht.le
      · refine le_trans ?_ (div_le_div_of_nonneg_right (le_max_right K (Real.exp 4)) ht.le)
        exact div_le_div_of_nonneg_left (Real.exp_pos 4).le ht (by linarith [H.pinchingShift_pos])
    have h23 : 0 ≤ 2 * Real.sqrt 3 := by positivity
    calc 2 * Real.sqrt 3 * (max (K / s.time) 0 / 2 +
          max (K / s.time) (Real.exp 4 / (H.pinchingShift + s.time)))
        ≤ 2 * Real.sqrt 3 * (max K 0 / s.time / 2 + max K (Real.exp 4) / s.time) := by
          gcongr
      _ = _ := by field_simp
  have hsec := sectionalBoundedBelowAt_neg_of_sqrt_normSq0S_le s.metric y hbd2
  have := hsec.scaleMetric s.time⁻¹ (inv_pos.mpr ht)
  have heq : -(2 * Real.sqrt 3 * (max K 0 / 2 + max K (Real.exp 4)) / s.time) / s.time⁻¹ =
      -(2 * Real.sqrt 3 * (max K 0 / 2 + max K (Real.exp 4))) := by
    field_simp
  rw [heq] at this
  exact this

/-- Reduction: `hcurv` from a normalised scalar upper bound on fixed normalised balls about a
seeded centre. -/
theorem hcurv_of_scalar_upper_S20 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} (H : AnalyticSurgeryProfile F δ)
    (hscal : ∀ a v L : ℝ, 0 < a → 0 < v → 0 < L → ∃ K : ℝ,
      ∀ S : LatePointSequence_S13 F,
        (∀ j, HasNormalizedSeed_S13 (S.slices j) (S.point j) a v) →
        ∀ᶠ j in atTop, ∀ y ∈ riemannianBallOf (S.slices j).normalizedMetric (S.point j) L,
          metricScalarAt (S.slices j).normalizedMetric y ≤ K) :
    ∀ a v L : ℝ, 0 < a → 0 < v → 0 < L → ∃ Λ : ℝ, 0 ≤ Λ ∧
      ∀ S : LatePointSequence_S13 F,
        (∀ j, HasNormalizedSeed_S13 (S.slices j) (S.point j) a v) →
        ∀ᶠ j in atTop, ∀ y ∈ riemannianBallOf (S.slices j).normalizedMetric (S.point j) L,
          SectionalBoundedBelowAt (S.slices j).normalizedMetric y (-Λ) := by
  intro a v L ha hv hL
  obtain ⟨K, hK⟩ := hscal a v L ha hv hL
  refine ⟨2 * Real.sqrt 3 * (max K 0 / 2 + max K (Real.exp 4)), ?_, ?_⟩
  · have : 0 ≤ max K (Real.exp 4) := (Real.exp_pos 4).le.trans (le_max_right _ _)
    positivity
  · intro S hS
    refine (hK S hS).mono fun j hj y hy => ?_
    exact sec_lower_of_normScalar_le_S20 H (S.slices j) y (hj y hy)

end GC.LongTime.Ch12
