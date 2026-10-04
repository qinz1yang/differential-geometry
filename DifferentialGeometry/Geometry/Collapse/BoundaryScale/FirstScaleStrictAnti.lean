import DifferentialGeometry.Geometry.Collapse.BoundaryScale.FirstScaleEverywhere
import DifferentialGeometry.Geometry.Collapse.BoundaryScale.FirstScaleGeneral

/-!
# BSA03 at every centre of a compact carrier: strict anti-monotonicity (route R3, statement F)

Blueprint 207B, BSA03 (`B:7764`). On a compact carrier with boundary, for every centre `p`
(boundary points included) and `0 < w < ω₃/4`, the first volume scale is positive, attained
(`vol B(p, r_p(w)) = w r_p(w)³`) and the volume is above the barrier below it
(`firstVolumeScale_spec_everywhere`, X88). The new piece here is the strict anti-monotonicity in
the parameter on `(0, ω₃/4)`, the boundary analogue of `firstVolumeScale_strictAntiOn`
(`FirstCrossingScale.lean`, which needs a boundaryless model). It follows from the attained
equality alone; no comparison geometry is used.
-/

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry GC.Endpoint
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry.Geometry.Collapse

universe u

variable (W : CompactCarrier.{u}) (g : SmoothRiemannianMetric W.model W.Carrier)

/-- BSA03, parameter monotonicity: `w ↦ r_p(w)` is strictly antitone on `(0, ω₃/4)` at every
centre `p` of a compact carrier, boundary points included. -/
theorem firstVolumeScale_strictAntiOn_everywhere (p : W.Carrier) :
    StrictAntiOn (firstVolumeScale g p) (Ioo 0 (euclideanThreeUnitBallVolume / 4)) := by
  intro w₁ hw₁ w₂ hw₂ hlt
  obtain ⟨hr₁, he₁, -⟩ := firstVolumeScale_spec_everywhere W g p hw₁.1 hw₁.2
  obtain ⟨-, he₂, hb₂⟩ := firstVolumeScale_spec_everywhere W g p hw₂.1 hw₂.2
  by_contra! hle
  rcases hle.eq_or_lt with heq | hgt
  · rw [← heq, he₁] at he₂
    exact (mul_lt_mul_of_pos_right hlt (pow_pos hr₁ 3)).ne he₂
  · have hh := hb₂ (firstVolumeScale g p w₁) hr₁ hgt
    rw [he₁] at hh
    linarith [mul_lt_mul_of_pos_right hlt (pow_pos hr₁ 3)]

/-- BSA03 at every centre, all clauses: for `0 < w < ω₃/4` the first volume scale is positive and
attained with the volume above the barrier below it, and for `0 < w₁ < w₂ < ω₃/4` the scales are
strictly ordered, `r_p(w₂) < r_p(w₁)`. -/
theorem firstVolumeScale_bsa03_everywhere (p : W.Carrier) :
    (∀ w : ℝ, 0 < w → w < euclideanThreeUnitBallVolume / 4 →
      0 < firstVolumeScale g p w ∧
        (ballVolume g p (firstVolumeScale g p w)).toReal = w * firstVolumeScale g p w ^ 3 ∧
        ∀ r : ℝ, 0 < r → r < firstVolumeScale g p w → w * r ^ 3 < (ballVolume g p r).toReal) ∧
      ∀ w₁ w₂ : ℝ, 0 < w₁ → w₁ < w₂ → w₂ < euclideanThreeUnitBallVolume / 4 →
        firstVolumeScale g p w₂ < firstVolumeScale g p w₁ := by
  refine ⟨fun w hw hwc => firstVolumeScale_spec_everywhere W g p hw hwc, ?_⟩
  intro w₁ w₂ hw₁ h₁₂ hw₂
  exact firstVolumeScale_strictAntiOn_everywhere W g p ⟨hw₁, h₁₂.trans hw₂⟩
    ⟨hw₁.trans h₁₂, hw₂⟩ h₁₂

/-- Consumer: the two scales of BSA05 (`w` and `w' = w/(2S³)`, `S = 1 + 2/Λ`) are strictly ordered
at every centre: `r_p(w) < r_p(w')`. -/
theorem firstVolumeScale_lt_modified_everywhere (p : W.Carrier) {Λ w : ℝ} (hΛ : 0 < Λ)
    (hw : 0 < w) (hwc : w < euclideanThreeUnitBallVolume / 4) :
    firstVolumeScale g p w < firstVolumeScale g p (w / (2 * (1 + 2 / Λ) ^ 3)) := by
  have hS : 1 < 1 + 2 / Λ := by have := div_pos two_pos hΛ; linarith
  have hden : 1 < 2 * (1 + 2 / Λ) ^ 3 := by
    have : 1 < (1 + 2 / Λ) ^ 3 := one_lt_pow₀ hS (by norm_num)
    linarith
  have hw' : 0 < w / (2 * (1 + 2 / Λ) ^ 3) := div_pos hw (by linarith)
  have hlt : w / (2 * (1 + 2 / Λ) ^ 3) < w := div_lt_self hw hden
  exact (firstVolumeScale_bsa03_everywhere W g p).2 _ _ hw' hlt hwc

end DifferentialGeometry.Geometry.Collapse
