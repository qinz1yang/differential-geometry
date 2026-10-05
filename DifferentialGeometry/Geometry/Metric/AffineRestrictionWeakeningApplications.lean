import DifferentialGeometry.Geometry.Metric.AffineRestrictionWeakening

/-!
# Consumers of the slack-aware restriction (B:10923)

* `plane_cloud_test_weakening`: a set lying exactly on its affine plane near the centre passes the
  quality-`δ` test once it passes the quality-`Γ` test with `Γ < δ/8` (here trivially, error `0`).
* `affine_restriction_line_example`: on `ℝ`, the line `⊤` restricted to `B̄(0, r)` is within `6e`
  of itself — the closed-ball lemma with `S = A`.
-/

set_option autoImplicit false

open Set Metric
open scoped ENNReal

namespace GC.MetricGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The plane itself passes every weakened test. -/
theorem plane_cloud_test_weakening {A : AffineSubspace ℝ E} {x : E} (hxA : x ∈ A)
    {ρ Γ δ : ℝ} (hρ : 0 < ρ) (hΓ : 0 < Γ) (hΓδ : Γ < δ / 8) :
    hausdorffEDist ((A : Set E) ∩ ball x (ρ / δ)) ((A : Set E) ∩ ball x (ρ / δ)) ≤
      ENNReal.ofReal (δ * ρ) :=
  cloud_test_weakening (S := (A : Set E)) hxA hxA hρ hΓ hΓδ
    ((hausdorffEDist_self).trans_le zero_le)

/-- The closed-ball lemma on `ℝ` with `S = A = ⊤`. -/
theorem affine_restriction_line_example {e r : ℝ} (he : 0 < e) (hr : 0 < r) :
    hausdorffEDist ((⊤ : AffineSubspace ℝ ℝ) ∩ closedBall (0 : ℝ) r)
        (((⊤ : AffineSubspace ℝ ℝ) : Set ℝ) ∩ closedBall (0 : ℝ) r) ≤ ENNReal.ofReal (6 * e) :=
  affine_restriction_closedBall (S := ((⊤ : AffineSubspace ℝ ℝ) : Set ℝ))
    (AffineSubspace.mem_top ℝ ℝ 0) (AffineSubspace.mem_top ℝ ℝ 0) he hr le_rfl
    ((hausdorffEDist_self).trans_le zero_le)

end GC.MetricGeometry
