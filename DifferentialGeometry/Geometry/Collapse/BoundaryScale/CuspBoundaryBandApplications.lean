import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspBoundaryBandUpperDistance

/-!
# Consumer of the boundary-band upper distance: small flat ellipsoids lie in metric balls

`CuspEmbedding.image_subset_ball_flat` (upper inclusion of statement V.2, `e(E_{r/λ₊}) ⊆ B_g(q, r)`
with `λ₊ = √(1 + δ)`): the image of the flat ellipsoid
`{(t', z') : (z - z')² + d_q(t, t')² < (r / √(1 + δ))²}` of the cusp domain around `p = (t, z)`
lies in the open `g`-ball of radius `r > 0` around `e p`, for every height `z ≥ 0` (boundary
centres included).
-/

set_option autoImplicit false

noncomputable section

open Set DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint
open scoped Manifold ENNReal

namespace DifferentialGeometry.Geometry.Collapse

universe u

/-- The image of a small flat ellipsoid of the cusp domain lies in the `g`-ball of radius `r`. -/
theorem CuspEmbedding.image_subset_ball_flat {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ} {X : Set W.Carrier}
    (e : CuspEmbedding W g K δ X) (hδ : -1 < δ) {p : CuspHalfSpace} (hp : p ∈ cuspDomain)
    {r : ℝ} (hr : 0 < r) :
    e.toFun '' {p' : CuspHalfSpace | p' ∈ cuspDomain ∧ (p.2.val 0 - p'.2.val 0) ^ 2 +
        (riemannianEDistOf e.cusp.torusMetric p.1 p'.1).toReal ^ 2 <
          (r / Real.sqrt (1 + δ)) ^ 2} ⊆
      {y | riemannianEDistOf g (e.toFun p) y < ENNReal.ofReal r} := by
  rintro _ ⟨p', ⟨hp'd, hQ⟩, rfl⟩
  have hlam : 0 < Real.sqrt (1 + δ) := Real.sqrt_pos.mpr (by linarith)
  refine lt_of_le_of_lt (e.riemannianEDistOf_le_flat hp hp'd) ?_
  rw [ENNReal.ofReal_lt_ofReal_iff hr]
  have hsq : Real.sqrt ((p.2.val 0 - p'.2.val 0) ^ 2 +
      (riemannianEDistOf e.cusp.torusMetric p.1 p'.1).toReal ^ 2) < r / Real.sqrt (1 + δ) :=
    (Real.sqrt_lt' (by positivity)).mpr hQ
  calc Real.sqrt (1 + δ) * Real.sqrt ((p.2.val 0 - p'.2.val 0) ^ 2 +
        (riemannianEDistOf e.cusp.torusMetric p.1 p'.1).toReal ^ 2)
      < Real.sqrt (1 + δ) * (r / Real.sqrt (1 + δ)) := mul_lt_mul_of_pos_left hsq hlam
    _ = r := by field_simp

end DifferentialGeometry.Geometry.Collapse
