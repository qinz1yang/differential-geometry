import DifferentialGeometry.Analysis.InnerProductSpace.ProjectedGraphRank

/-!
# Projected rank at every preimage from one reference graph (SGP05, EGP07)

Blueprint 207B, SGP05 (`lem:fibration-slim-all-preimage-rank`, B:4667–4709). At a core center `x`
choose a reference `i` and `T_x = DΦ_i(η_i(p))`. For EVERY preimage `q` of `x` the full marker forces
`η_i(q) = η_i(p)` (`eq_of_full_marker_block`), so the SAME `T_x` is compared with
`D(π F)_q`; the reference-axis test gives `9/10 < ‖R_i dη_i(q)‖ ≤ 2`. FC06 in dimension one
(`projected_rank_of_one_dimensional_reference`) then gives: the projection onto `A_x⁰ = im T_x`
is onto, the normal error is at most `e`, and the singular values on the kernel complement lie in
`[1/2, 3C]`. The statements are generic over the packet (slim or edge): `T` is any linear map
`ℝ → H` with an identity component (`‖z‖ ≤ ‖T z‖`).
-/

set_option autoImplicit false
open scoped InnerProductSpace

namespace ContinuousLinearMap

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The adjoint of a real covector `L : V → ℝ` is bounded below by `‖L‖`. -/
theorem norm_mul_le_norm_adjoint_apply_of_real_target [CompleteSpace V] (L : V →L[ℝ] ℝ)
    (z : ℝ) : ‖L‖ * ‖z‖ ≤ ‖L.adjoint z‖ := by
  have hz : L.adjoint z = z • L.adjoint 1 := by
    rw [← map_smul, smul_eq_mul, mul_one]
  have hnorm : ‖L.adjoint‖ ≤ ‖L.adjoint 1‖ := by
    refine L.adjoint.opNorm_le_bound (norm_nonneg _) (fun w => ?_)
    rw [show L.adjoint w = w • L.adjoint 1 by rw [← map_smul, smul_eq_mul, mul_one],
      norm_smul, mul_comm]
  have hiso : ‖L.adjoint‖ = ‖L‖ := LinearIsometryEquiv.norm_map _ L
  rw [hz, norm_smul, mul_comm (‖z‖)]
  rw [hiso] at hnorm
  exact mul_le_mul_of_nonneg_right hnorm (norm_nonneg z)

variable [FiniteDimensional ℝ V]

/-- SGP05/EGP07: FC06 in dimension one. A reference graph derivative `T : ℝ → H` with identity
component and `‖T‖ ≤ C`, a coordinate differential with `9/10 < ‖dη‖ ≤ 2`, and an actual
differential `D` with `‖D - T dη‖ ≤ e < 2/5`, `e ≤ C`, give a surjective projection onto
`im T`, normal error at most `e`, and singular values in `[1/2, 3C]` on the kernel complement. -/
theorem projected_rank_of_one_dimensional_reference (T : ℝ →L[ℝ] H)
    (hT : ∀ z, ‖z‖ ≤ ‖T z‖) {C e : ℝ} (hTC : ‖T‖ ≤ C) (dη : V →L[ℝ] ℝ)
    (hlow : 9 / 10 < ‖dη‖) (hup : ‖dη‖ ≤ 2) (D : V →L[ℝ] H)
    (hD : ‖D - T.comp dη‖ ≤ e) (he : e < 2 / 5) (heC : e ≤ C) :
    let P := T.range.orthogonalProjectionOnto.comp D
    Function.Surjective P ∧ ‖D - T.range.subtypeL.comp P‖ ≤ e ∧
      ∀ v ∈ P.kerᗮ, 1 / 2 * ‖v‖ ≤ ‖P v‖ ∧ ‖P v‖ ≤ 3 * C * ‖v‖ := by
  have hadj : ∀ z, 9 / 10 * ‖z‖ ≤ ‖dη.adjoint z‖ := fun z =>
    (mul_le_mul_of_nonneg_right hlow.le (norm_nonneg z)).trans
      (norm_mul_le_norm_adjoint_apply_of_real_target dη z)
  obtain ⟨hsurj, hnormal, hsv⟩ := projected_range_surjective_of_approximation T dη D
    (by norm_num : (0 : ℝ) < 9 / 10) (by linarith) hadj hT hTC hup hD
  refine ⟨hsurj, hnormal, fun v hv => ?_⟩
  obtain ⟨h1, h2⟩ := hsv v hv
  have hv0 := norm_nonneg v
  constructor
  · nlinarith
  · nlinarith

end ContinuousLinearMap

namespace DifferentialGeometry.Analysis

/-- SGP05/SGP06/EGP07: a full marker recovers the coordinate exactly. If the reference block of
`F(q)` is `(R ζ η, R ζ)` and equals the block `(R a, R)` of a full-marker center, then `ζ = 1` and
`η = a`. -/
theorem eq_of_full_marker_block {R ζ η a : ℝ} (hR : 0 < R) (hvec : R * ζ * η = R * a)
    (hmarker : R * ζ = R) : ζ = 1 ∧ η = a := by
  have hζ : ζ = 1 := by
    have := mul_left_cancel₀ hR.ne' (hmarker.trans (mul_one R).symm)
    exact this
  refine ⟨hζ, ?_⟩
  rw [hζ, mul_one] at hvec
  exact mul_left_cancel₀ hR.ne' hvec

end DifferentialGeometry.Analysis
