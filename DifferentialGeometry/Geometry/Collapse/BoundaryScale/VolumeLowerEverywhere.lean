import DifferentialGeometry.Geometry.Collapse.BoundaryScale.AnalyticData
import DifferentialGeometry.Geometry.Collapse.BoundaryScale.FirstScaleEverywhere

/-!
# BSA06 volume lower bound at every centre, without Bishop–Gromov (route R3, statement L)

Blueprint 207B, BSA06 (`B:7979`), volume clause, and LPA01's centre bound `v_* = w'/(24 I(1))`,
`I(1) = ∫₀¹ sinh²`. For every `p`, every `w' > 0` and every `0 < ρ ≤ 2 r_p(w')`:
`w'/(24 I(1)) ≤ w'/8 ≤ vol B(p, ρ)/ρ³`.
* below the first volume scale the ball volume is strictly above the barrier
  (`lt_ballVolume_toReal_of_lt_firstVolumeScale`);
* at and above it, monotonicity and the attained barrier at `u = r_p(w')` give
  `vol B(p, ρ) ≥ w' u³ ≥ w' ρ³/8`;
* `sinh t ≥ t` on `[0, 1]` gives `24 I(1) ≥ 8`.
No comparison geometry, no boundary depth, no curvature and no standing inequality is used: this
replaces `volume_lower_at_modified_scale_of_standing` (`AnalyticData.lean`), whose `hdepth`
needed the convex-boundary comparison BSA02, for all of its consumers.
-/

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry GC.Endpoint
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry.Geometry.Collapse

universe u

/-- `∫₀¹ sinh² ≥ 1/3`, from `sinh t ≥ t` on `[0, 1]`. -/
theorem one_third_le_integral_sinh_sq : (1 / 3 : ℝ) ≤ ∫ t in (0 : ℝ)..1, Real.sinh t ^ 2 := by
  have hpow : (∫ t in (0 : ℝ)..1, t ^ 2) = 1 / 3 := by
    rw [integral_pow]
    norm_num
  rw [← hpow]
  refine intervalIntegral.integral_mono_on zero_le_one ?_ ?_ ?_
  · exact (continuous_pow 2).intervalIntegrable 0 1
  · exact (Real.continuous_sinh.pow 2).intervalIntegrable 0 1
  · intro t ht
    exact pow_le_pow_left₀ ht.1 (Real.self_le_sinh_iff.mpr ht.1) 2

/-- `24 ∫₀¹ sinh² ≥ 8`; in particular the LPA01 constant is positive. -/
theorem eight_le_twentyFour_mul_integral_sinh_sq :
    (8 : ℝ) ≤ 24 * ∫ t in (0 : ℝ)..1, Real.sinh t ^ 2 := by
  linarith [one_third_le_integral_sinh_sq]

section General

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

/-- L.1: on any compact manifold (boundary allowed), `0 < ρ ≤ 2 r_p(w')` gives
`w'/8 ≤ vol B(p, ρ)/ρ³`. -/
theorem div_cube_ge_of_le_two_mul_firstVolumeScale (g : SmoothRiemannianMetric I M) (p : M)
    {w' ρ : ℝ} (hw' : 0 < w') (hρ : 0 < ρ) (hρu : ρ ≤ 2 * firstVolumeScale g p w') :
    w' / 8 ≤ (ballVolume g p ρ).toReal / ρ ^ 3 := by
  have hρ3 : 0 < ρ ^ 3 := pow_pos hρ 3
  rw [le_div_iff₀ hρ3]
  rcases lt_or_ge ρ (firstVolumeScale g p w') with hlt | hge
  · have h := lt_ballVolume_toReal_of_lt_firstVolumeScale g p hρ hlt
    nlinarith
  · have hu : 0 < firstVolumeScale g p w' := by linarith
    have hatt := le_ballVolume_toReal_firstVolumeScale_of_pos g p hu
    have hmono := ballVolume_toReal_monotone g p hge
    have hcube : ρ ^ 3 ≤ 8 * firstVolumeScale g p w' ^ 3 := by
      have h2 : ρ ^ 3 ≤ (2 * firstVolumeScale g p w') ^ 3 :=
        pow_le_pow_left₀ hρ.le hρu 3
      linarith [show (2 * firstVolumeScale g p w') ^ 3 = 8 * firstVolumeScale g p w' ^ 3 by ring]
    nlinarith

/-- L.2: the BSA06/LPA01 volume clause `w'/(24 I(1)) ≤ vol B(p, ρ)/ρ³` for `0 < ρ ≤ 2 r_p(w')`,
with only `0 < w'`. -/
theorem volume_lower_at_modified_scale_of_pos (g : SmoothRiemannianMetric I M) (p : M)
    {w' ρ : ℝ} (hw' : 0 < w') (hρ : 0 < ρ) (hρu : ρ ≤ 2 * firstVolumeScale g p w') :
    0 < w' / (24 * ∫ t in (0 : ℝ)..1, Real.sinh t ^ 2) ∧
      w' / (24 * ∫ t in (0 : ℝ)..1, Real.sinh t ^ 2) ≤ (ballVolume g p ρ).toReal / ρ ^ 3 := by
  have h8 := eight_le_twentyFour_mul_integral_sinh_sq
  have hI : 0 < 24 * ∫ t in (0 : ℝ)..1, Real.sinh t ^ 2 := by linarith
  refine ⟨div_pos hw' hI, ?_⟩
  exact (div_le_div_of_nonneg_left hw'.le (by norm_num) h8).trans
    (div_cube_ge_of_le_two_mul_firstVolumeScale g p hw' hρ hρu)

end General

section Carrier

variable (W : CompactCarrier.{u}) (g : SmoothRiemannianMetric W.model W.Carrier)

/-- BSA06, volume clause, at EVERY centre of a compact carrier (boundary included), in the
standing-sequence form: `1 ≤ n` and `n⁻¹ ≤ w'` only serve to make `w'` positive. This is
`volume_lower_at_modified_scale_of_standing` without its depth hypothesis (and without the
unused standing inequality). -/
theorem volume_lower_at_modified_scale_of_standing_everywhere (p : W.Carrier) {n w' ρ : ℝ}
    (hn : 1 ≤ n) (hwn : n⁻¹ ≤ w') (hρ : 0 < ρ) (hρu : ρ ≤ 2 * firstVolumeScale g p w') :
    0 < w' / (24 * ∫ t in (0 : ℝ)..1, Real.sinh t ^ 2) ∧
      w' / (24 * ∫ t in (0 : ℝ)..1, Real.sinh t ^ 2) ≤ (ballVolume g p ρ).toReal / ρ ^ 3 :=
  volume_lower_at_modified_scale_of_pos g p ((inv_pos.mpr (zero_lt_one.trans_le hn)).trans_le hwn)
    hρ hρu

/-- The verbatim hypothesis list of `volume_lower_at_modified_scale_of_standing` minus `hdepth`. -/
example (p : W.Carrier) {n w' ρ : ℝ} (hn : 1 ≤ n)
    (hstand : ENNReal.ofReal (2 * n * firstVolumeScale g p n⁻¹) < curvatureRadius g p)
    (hwn : n⁻¹ ≤ w') (hρ : 0 < ρ) (hρu : ρ ≤ 2 * firstVolumeScale g p w') :
    0 < w' / (24 * ∫ t in (0 : ℝ)..1, Real.sinh t ^ 2) ∧
      w' / (24 * ∫ t in (0 : ℝ)..1, Real.sinh t ^ 2) ≤ (ballVolume g p ρ).toReal / ρ ^ 3 :=
  Function.const _ (volume_lower_at_modified_scale_of_standing_everywhere W g p hn hwn hρ hρu) hstand

/-- Consumer: for `0 < w' < ω₃/4`, at EVERY point (boundary included) the modified scales
`ρ ∈ (0, 2 r_p(w')]` exist and all carry the LPA01 centre bound; in particular `ρ = r_p(w')` and
`ρ = 2 r_p(w')`. -/
theorem exists_modified_scale_volume_lower (p : W.Carrier) {w' : ℝ} (hw' : 0 < w')
    (hwc : w' < euclideanThreeUnitBallVolume / 4) :
    0 < firstVolumeScale g p w' ∧
      ∀ ρ ∈ Ioc 0 (2 * firstVolumeScale g p w'),
        w' / (24 * ∫ t in (0 : ℝ)..1, Real.sinh t ^ 2) ≤ (ballVolume g p ρ).toReal / ρ ^ 3 := by
  refine ⟨firstVolumeScale_pos_everywhere W g p hw' hwc, fun ρ hρ => ?_⟩
  exact (volume_lower_at_modified_scale_of_pos g p hw' hρ.1 hρ.2).2

end Carrier

end DifferentialGeometry.Geometry.Collapse
