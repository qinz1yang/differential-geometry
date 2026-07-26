import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.BallRetraction

/-!
# Mixed estimates through radial retraction

This file packages the algebra which transfers a two-scale nonlinear estimate
through a bounded linear symmetry operation followed by radial retraction.
The application is the low-regularity Ricci--DeTurck dense extension, but the
result is independent of geometry.
-/

noncomputable section

open scoped InnerProductSpace

namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable {Z : Type*} [NormedAddCommGroup Z]

/-- A pointwise real inequality between continuous functions extends from a
dense subset to the whole space.  This is the closure step used after proving
a mixed estimate on smooth spectral representatives. -/
theorem dense_le_of_cont {W : Type*} [TopologicalSpace W]
    {D : Set W} (hD : Dense D) {f q : W → ℝ}
    (hf : Continuous f) (hq : Continuous q)
    (hDle : ∀ w ∈ D, f w ≤ q w) : ∀ w, f w ≤ q w := by
  intro w
  have hclosed : IsClosed {z | f z ≤ q z} := isClosed_le hf hq
  have hsub : D ⊆ {z | f z ≤ q z} := fun z hz ↦ hDle z hz
  exact closure_minimal hsub hclosed (hD w)

/-- A continuous linear image cannot grow under radial retraction. -/
theorem norm_map_ball_le {R : ℝ} (hR : 0 ≤ R) (J : X →L[ℝ] Y) (x : X) :
    ‖J (ballRetraction R x)‖ ≤ ‖J x‖ := by
  have hfac0 : 0 ≤ min 1 (R / ‖x‖) :=
    le_min zero_le_one (div_nonneg hR (norm_nonneg x))
  have hfac1 : min 1 (R / ‖x‖) ≤ 1 := min_le_left _ _
  rw [ballRetraction, map_smul, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hfac0]
  simpa only [one_mul] using
    mul_le_mul_of_nonneg_right hfac1 (norm_nonneg (J x))

/-- Transfer one mixed two-scale estimate through radial retraction after a
map which is bounded in both the high norm and the lower view `J`.

The first new high-norm coefficient is the ordinary product of the high and
low bounds.  The second comes from differentiating the radial scale factor and
is proportional to `R⁻¹`; the lower coefficient is unchanged except for the
low-norm bound. -/
theorem radial_mixed
    (J : X →L[ℝ] Y) (N : X → Z)
    {R A B cH cL : ℝ}
    (hR : 0 < R) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hcH : 0 ≤ cH) (hcL : 0 ≤ cL)
    (x y sx sy : X)
    (hJx : ‖J sx‖ ≤ cL * ‖J x‖)
    (hJy : ‖J sy‖ ≤ cL * ‖J y‖)
    (hhigh : ‖sx - sy‖ ≤ cH * ‖x - y‖)
    (hlow : ‖J (sx - sy)‖ ≤ cL * ‖J (x - y)‖)
    (hbase :
      ‖N (ballRetraction R sx) - N (ballRetraction R sy)‖ ≤
        A * max ‖J (ballRetraction R sx)‖ ‖J (ballRetraction R sy)‖ *
            ‖ballRetraction R sx - ballRetraction R sy‖ +
          B * ‖J (ballRetraction R sx - ballRetraction R sy)‖) :
    ‖N (ballRetraction R sx) - N (ballRetraction R sy)‖ ≤
      (A * cL * cH + B * (1 / R) * cL * cH) *
          max ‖J x‖ ‖J y‖ * ‖x - y‖ +
        (B * cL) * ‖J (x - y)‖ := by
  have hRinv : 0 ≤ 1 / R := by positivity
  have hmax0 : 0 ≤ max ‖J x‖ ‖J y‖ :=
    le_trans (norm_nonneg _) (le_max_left _ _)
  have hmax : max ‖J sx‖ ‖J sy‖ ≤ cL * max ‖J x‖ ‖J y‖ := by
    apply max_le
    · exact hJx.trans
        (mul_le_mul_of_nonneg_left (le_max_left _ _) hcL)
    · exact hJy.trans
        (mul_le_mul_of_nonneg_left (le_max_right _ _) hcL)
  have hmaxBall :
      max ‖J (ballRetraction R sx)‖ ‖J (ballRetraction R sy)‖ ≤
        cL * max ‖J x‖ ‖J y‖ := by
    apply max_le
    · exact (norm_map_ball_le hR.le J sx).trans
        (hJx.trans (mul_le_mul_of_nonneg_left (le_max_left _ _) hcL))
    · exact (norm_map_ball_le hR.le J sy).trans
        (hJy.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) hcL))
  have hdistBall :
      ‖ballRetraction R sx - ballRetraction R sy‖ ≤ cH * ‖x - y‖ := by
    have hnonexp := (lipschitzWith_ballRetraction (X := X) hR.le).dist_le_mul sx sy
    rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm] at hnonexp
    exact hnonexp.trans hhigh
  have hcorr :
      (1 / R) * max ‖J sx‖ ‖J sy‖ * ‖sx - sy‖ ≤
        (1 / R) * (cL * max ‖J x‖ ‖J y‖) *
          (cH * ‖x - y‖) := by
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left hmax hRinv
    · exact hhigh
    · exact norm_nonneg _
    · exact mul_nonneg hRinv (mul_nonneg hcL hmax0)
  have hlowBall :
      ‖J (ballRetraction R sx - ballRetraction R sy)‖ ≤
        cL * ‖J (x - y)‖ +
          (1 / R) * (cL * max ‖J x‖ ‖J y‖) *
            (cH * ‖x - y‖) := by
    exact (norm_map_ballRetraction_sub_le hR J sx sy).trans
      (add_le_add hlow hcorr)
  have hfirst :
      A * max ‖J (ballRetraction R sx)‖ ‖J (ballRetraction R sy)‖ *
          ‖ballRetraction R sx - ballRetraction R sy‖ ≤
        A * (cL * max ‖J x‖ ‖J y‖) * (cH * ‖x - y‖) := by
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left hmaxBall hA
    · exact hdistBall
    · exact norm_nonneg _
    · exact mul_nonneg hA (mul_nonneg hcL hmax0)
  calc
    ‖N (ballRetraction R sx) - N (ballRetraction R sy)‖
        ≤ A * max ‖J (ballRetraction R sx)‖ ‖J (ballRetraction R sy)‖ *
              ‖ballRetraction R sx - ballRetraction R sy‖ +
            B * ‖J (ballRetraction R sx - ballRetraction R sy)‖ := hbase
    _ ≤ A * (cL * max ‖J x‖ ‖J y‖) * (cH * ‖x - y‖) +
          B * (cL * ‖J (x - y)‖ +
            (1 / R) * (cL * max ‖J x‖ ‖J y‖) *
              (cH * ‖x - y‖)) :=
      add_le_add hfirst (mul_le_mul_of_nonneg_left hlowBall hB)
    _ = (A * cL * cH + B * (1 / R) * cL * cH) *
          max ‖J x‖ ‖J y‖ * ‖x - y‖ +
        (B * cL) * ‖J (x - y)‖ := by ring

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear

end
