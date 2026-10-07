import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SliceSeeds_CX2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.L862PrefixSectional_O37
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.RecentProtection_CX2

/-!
# CH12-O69 G1: multi-time Prop 84.1(c) along a seed strip (`hBig`, `[FROZEN] CH12-O69 G1-out`)

`seedStrip_big_O69 Hp : hBig` (text = binder type of `frozen_hBig_O69`,
`build-logs/ch12/scratch/FrozenO69.lean`).  At every time `w` of a seed strip
`SeedStrip(y, a, σ r, ℓ r², w_*)` on `N := sliceTowerHistory_CX2 s` (exact text of the strip
hypothesis of `frozen_hU_O57`), the single-time enlargement `enlarged_rm_bound_of_seed_O4`
(tower index `sliceTowerIndex_CX2 s`, seed ratio `20σ/A`, radius `A r / 20`) gives
`|Rm| ≤ B/r²` on `B_w(Y w, A r)`; `R ≤ 9|Rm|` (`scalar_le_nine_rm_bound_CX2`) and the pinching
budget `sectional_of_scalar_prefix_O37` give `R ≤ B/r²` and `sec ≥ -r⁻²` there.

Constants: `B := 9 · 400 K₀ / A²`, `T₁ := 4 T₀ᴼ⁴`, `b₁ := min (b/2) (min (10 ρ₀ / A) (1/(2(1+ℓ))))`;
`b₁` forces `(1+ℓ) r² ≤ u/4`, hence every strip time satisfies `w ≥ u - (1+ℓ) r² ≥ u/4`.
-/

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
  DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Geometry.Riemannian.VolumeComparison DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow
open scoped NNReal Manifold ContDiff

namespace GC.LongTime.Ch12

universe u

/-- Time arithmetic of a strip below a window: `w ≥ a - ℓ r² ≥ u - (1+ℓ) r²` and
`(1+ℓ) r² ≤ u/4` give `u ≤ 4 w`. -/
theorem strip_time_ge_O69 {ℓ b₁ u r a a' w : ℝ} (hℓ : 0 < ℓ) (hb₁ : 0 < b₁)
    (hb₁ℓ : b₁ ≤ 1 / (2 * (1 + ℓ))) (hu : 0 ≤ u) (hr : 0 < r) (hrb : r ≤ b₁ * Real.sqrt u)
    (hua : u - r ^ 2 ≤ a) (ha' : a' = a - ℓ * r ^ 2) (hw : a' ≤ w) : u ≤ 4 * w := by
  have hsq : r ^ 2 ≤ b₁ ^ 2 * u := by
    have h1 : r ^ 2 ≤ (b₁ * Real.sqrt u) ^ 2 := pow_le_pow_left₀ hr.le hrb 2
    rwa [mul_pow, Real.sq_sqrt hu] at h1
  have hb2 : b₁ ^ 2 * (1 + ℓ) ≤ 1 / 4 := by
    have h1 : b₁ * (2 * (1 + ℓ)) ≤ 1 := by
      have h2 : 0 < 2 * (1 + ℓ) := by positivity
      calc b₁ * (2 * (1 + ℓ)) ≤ 1 / (2 * (1 + ℓ)) * (2 * (1 + ℓ)) :=
            mul_le_mul_of_nonneg_right hb₁ℓ h2.le
        _ = 1 := by field_simp
    nlinarith [hb₁, hℓ]
  have h3 : (1 + ℓ) * r ^ 2 ≤ u / 4 := by nlinarith [hsq, hb2, hℓ]
  nlinarith [h3]

/-- `√u ≤ 2 √w` from `u ≤ 4 w`. -/
theorem sqrt_le_two_sqrt_O69 {u w : ℝ} (h : u ≤ 4 * w) : Real.sqrt u ≤ 2 * Real.sqrt w := by
  have h4 : Real.sqrt (4 * w) = 2 * Real.sqrt w := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    congr 1
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  rw [← h4]
  exact Real.sqrt_le_sqrt h

/-- **G1** (`[FROZEN] CH12-O69 G1-out`, text = binder of `frozen_hBig_O69`): multi-time 84.1(c)
along a seed strip, with `R ≤ B/r²` and `sec ≥ -r⁻²` on the large balls `B_w(Y w, A r)`. -/
theorem seedStrip_big_O69 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} (Hp : AnalyticSurgeryProfile F δ) :
    ∀ σ ℓ wst A : ℝ, 0 < σ → σ ≤ 1 → 0 < ℓ → 0 < wst → 0 < A →
      ∃ B T₁ b₁ : ℝ, 0 < B ∧ 0 < T₁ ∧ 0 < b₁ ∧
      ∀ s : RegularSlice F.observation, let N := sliceTowerHistory_CX2 s;
      ∀ (u : Icc (0 : ℝ) N.horizon), T₁ ≤ (u : ℝ) → (u : ℝ) ≤ s.time →
      ∀ (r : ℝ), 0 < r → r ≤ b₁ * Real.sqrt u →
      ∀ (a : Icc (0 : ℝ) N.horizon), a ≤ u → (u : ℝ) - r ^ 2 ≤ a →
      ∀ (y : (N.stageAt a).Carrier) (a' : Icc (0 : ℝ) N.horizon) (ha' : a' ≤ a)
        (Y : BackwardPointTrace N (N.activeStage a') (N.activeStage a) (N.activeStage_mono ha') y),
        (a' : ℝ) = a - ℓ * r ^ 2 →
        (∀ (w : Icc (0 : ℝ) N.horizon) (haw : a' ≤ w) (hwa : w ≤ a),
          hasSmallParabolicCurvature N w
            (Y.point (N.activeStage w) (N.activeStage_mono haw) (N.activeStage_mono hwa))
            (σ * r) ∧
          ENNReal.ofReal (wst * (σ * r) ^ 3) ≤
            ballVolume (N.stageMetric (N.activeStage w) w)
              (Y.point (N.activeStage w) (N.activeStage_mono haw) (N.activeStage_mono hwa))
              (σ * r)) →
        ∀ (w : Icc (0 : ℝ) N.horizon) (haw : a' ≤ w) (hwa : w ≤ a),
          ∀ q ∈ riemannianBallOf (N.stageMetric (N.activeStage w) w)
              (Y.point (N.activeStage w) (N.activeStage_mono haw) (N.activeStage_mono hwa)) (A * r),
            Real.sqrt (normSq0S (N.stageMetric (N.activeStage w) w) q 4
              (metricRm04At (N.stageMetric (N.activeStage w) w) q)) ≤ B / r ^ 2 ∧
            metricScalarAt (N.stageMetric (N.activeStage w) w) q ≤ B / r ^ 2 ∧
            SectionalBoundedBelowAt (N.stageMetric (N.activeStage w) w) q (-(r ^ 2)⁻¹) := by
  intro σ ℓ wst A hσ _hσ1 hℓ hwst hA
  have hratio : 0 < 20 * σ / A := by positivity
  obtain ⟨T₀, ρ₀, K₀, hT₀, hρ₀, hK₀, hbound⟩ := enlarged_rm_bound_of_seed_O4 Hp hratio hwst
  set Bm : ℝ := 400 * K₀ / A ^ 2 with hBm
  have hBm0 : 0 < Bm := by positivity
  set B : ℝ := 9 * Bm with hB
  have hB0 : 0 < B := by positivity
  obtain ⟨b, hb, hsec⟩ := sectional_of_scalar_prefix_O37 Hp hB0.le
  set b₁ : ℝ := min (b / 2) (min (10 * ρ₀ / A) (1 / (2 * (1 + ℓ)))) with hb₁
  have hb₁0 : 0 < b₁ := by positivity
  have hb₁b : b₁ ≤ b / 2 := min_le_left _ _
  have hb₁ρ : b₁ ≤ 10 * ρ₀ / A := (min_le_right _ _).trans (min_le_left _ _)
  have hb₁ℓ : b₁ ≤ 1 / (2 * (1 + ℓ)) := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨B, 4 * T₀, b₁, hB0, by positivity, hb₁0, ?_⟩
  intro s N u hTu hus r hr hrb a hau hua y a' ha' Y ha'eq hstrip w haw hwa q hq
  -- time arithmetic
  have hw4 : (u : ℝ) ≤ 4 * w :=
    strip_time_ge_O69 hℓ hb₁0 hb₁ℓ u.2.1 hr hrb hua ha'eq haw
  have hwT : T₀ ≤ (w : ℝ) := by linarith
  have hsq : Real.sqrt u ≤ 2 * Real.sqrt w := sqrt_le_two_sqrt_O69 hw4
  have hrw : r ≤ 2 * b₁ * Real.sqrt w := by
    calc r ≤ b₁ * Real.sqrt u := hrb
      _ ≤ b₁ * (2 * Real.sqrt w) := mul_le_mul_of_nonneg_left hsq hb₁0.le
      _ = 2 * b₁ * Real.sqrt w := by ring
  have hsw : 0 ≤ Real.sqrt w := Real.sqrt_nonneg _
  -- 84.1(c) at time `w`, radius `A r / 20`
  have hr' : 0 < A * r / 20 := by positivity
  have hr'ρ : A * r / 20 ≤ ρ₀ * Real.sqrt w := by
    have h1 : A * r ≤ A * (2 * b₁ * Real.sqrt w) := mul_le_mul_of_nonneg_left hrw hA.le
    have h2 : A * (2 * b₁) ≤ 20 * ρ₀ := by
      have := mul_le_mul_of_nonneg_left hb₁ρ hA.le
      rw [mul_div_cancel₀ _ hA.ne'] at this
      linarith
    have h3 : A * (2 * b₁ * Real.sqrt w) ≤ 20 * ρ₀ * Real.sqrt w := by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right h2 hsw
    linarith
  have hseedr : 20 * σ / A * (A * r / 20) = σ * r := by field_simp
  have hseedR : (20 : ℝ) * (A * r / 20) = A * r := by ring
  obtain ⟨hpar, hvol⟩ := hstrip w haw hwa
  have hRm := hbound (sliceTowerIndex_CX2 s) w
    (Y.point (N.activeStage w) (N.activeStage_mono haw) (N.activeStage_mono hwa))
    (A * r / 20) hr' hwT hr'ρ (by rw [hseedr]; exact hpar) (by rw [hseedr]; exact hvol) q
    (by rw [hseedR]; exact hq)
  have hRmB : Real.sqrt (normSq0S (N.stageMetric (N.activeStage w) w) q 4
      (metricRm04At (N.stageMetric (N.activeStage w) w) q)) ≤ Bm / r ^ 2 := by
    refine hRm.trans (le_of_eq ?_)
    rw [hBm]; field_simp; ring
  have hR : metricScalarAt (N.stageMetric (N.activeStage w) w) q ≤ B / r ^ 2 := by
    rw [hB]; exact scalar_le_nine_rm_bound_CX2 _ _ q hRmB
  refine ⟨hRmB.trans ?_, hR, ?_⟩
  · exact div_le_div_of_nonneg_right (by rw [hB]; linarith) (by positivity)
  · refine hsec s w (hwa.trans hau |>.trans' le_rfl |> fun h => le_trans h hus) q r hr ?_ hR
    calc r ≤ 2 * b₁ * Real.sqrt w := hrw
      _ ≤ b * Real.sqrt w := mul_le_mul_of_nonneg_right (by linarith) hsw

end GC.LongTime.Ch12
