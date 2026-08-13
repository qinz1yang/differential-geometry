import DifferentialGeometry.Analysis.Calculus.BallRetraction
open DifferentialGeometry.Analysis.Calculus
noncomputable section

open scoped InnerProductSpace

namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear

section Normed

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable {Z : Type*} [NormedAddCommGroup Z]

theorem dense_le_of_cont {W : Type*} [TopologicalSpace W]
    {D : Set W} (hD : Dense D) {f q : W → ℝ}
    (hf : Continuous f) (hq : Continuous q)
    (hDle : ∀ w ∈ D, f w ≤ q w) : ∀ w, f w ≤ q w := by
  intro w
  have hclosed : IsClosed {z | f z ≤ q z} := isClosed_le hf hq
  have hsub : D ⊆ {z | f z ≤ q z} := fun z hz ↦ hDle z hz
  exact closure_minimal hsub hclosed (hD w)

theorem norm_map_ball_le {R : ℝ} (hR : 0 ≤ R) (J : X →L[ℝ] Y) (x : X) :
    ‖J (ballRetraction R x)‖ ≤ ‖J x‖ := by
  have hfac0 : 0 ≤ min 1 (R / ‖x‖) :=
    le_min zero_le_one (div_nonneg hR (norm_nonneg x))
  have hfac1 : min 1 (R / ‖x‖) ≤ 1 := min_le_left _ _
  rw [ballRetraction, map_smul, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hfac0]
  simpa only [one_mul] using
    mul_le_mul_of_nonneg_right hfac1 (norm_nonneg (J x))

end Normed

section RadialMixed

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable {Z : Type*} [NormedAddCommGroup Z]

private theorem radial_mixed_of_ball_bound
    (J : X →L[ℝ] Y) (N : X → Z)
    {R A B cH cL κ : ℝ}
    (hR : 0 < R) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hcL : 0 ≤ cL)
    (x y sx sy : X)
    (hJx : ‖J sx‖ ≤ cL * ‖J x‖)
    (hJy : ‖J sy‖ ≤ cL * ‖J y‖)
    (hhigh : ‖sx - sy‖ ≤ cH * ‖x - y‖)
    (hlow : ‖J (sx - sy)‖ ≤ cL * ‖J (x - y)‖)
    (hdistBall :
      ‖ballRetraction R sx - ballRetraction R sy‖ ≤
        κ * (cH * ‖x - y‖))
    (hbase :
      ‖N (ballRetraction R sx) - N (ballRetraction R sy)‖ ≤
        A * max ‖J (ballRetraction R sx)‖ ‖J (ballRetraction R sy)‖ *
            ‖ballRetraction R sx - ballRetraction R sy‖ +
          B * ‖J (ballRetraction R sx - ballRetraction R sy)‖) :
    ‖N (ballRetraction R sx) - N (ballRetraction R sy)‖ ≤
      (A * cL * κ * cH + B * (1 / R) * cL * cH) *
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
        A * (cL * max ‖J x‖ ‖J y‖) *
          (κ * (cH * ‖x - y‖)) := by
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
    _ ≤ A * (cL * max ‖J x‖ ‖J y‖) *
          (κ * (cH * ‖x - y‖)) +
          B * (cL * ‖J (x - y)‖ +
            (1 / R) * (cL * max ‖J x‖ ‖J y‖) *
              (cH * ‖x - y‖)) :=
      add_le_add hfirst (mul_le_mul_of_nonneg_left hlowBall hB)
    _ = (A * cL * κ * cH + B * (1 / R) * cL * cH) *
          max ‖J x‖ ‖J y‖ * ‖x - y‖ +
        (B * cL) * ‖J (x - y)‖ := by ring

theorem radial_mixed
    (J : X →L[ℝ] Y) (N : X → Z)
    {R A B cH cL : ℝ}
    (hR : 0 < R) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hcL : 0 ≤ cL)
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
      (2 * A * cL * cH + B * (1 / R) * cL * cH) *
          max ‖J x‖ ‖J y‖ * ‖x - y‖ +
        (B * cL) * ‖J (x - y)‖ := by
  have hdist :
      ‖ballRetraction R sx - ballRetraction R sy‖ ≤
        2 * (cH * ‖x - y‖) := by
    have hret :=
      (lipschitzWith_ballRetraction (X := X) hR.le).dist_le_mul sx sy
    rw [dist_eq_norm, dist_eq_norm] at hret
    exact hret.trans
      (mul_le_mul_of_nonneg_left hhigh (by norm_num))
  have h := radial_mixed_of_ball_bound J N hR hA hB hcL
    x y sx sy hJx hJy hhigh hlow hdist hbase
  convert h using 1 ; ring

end RadialMixed

section Hilbert

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable {Z : Type*} [NormedAddCommGroup Z]

theorem radial_mixed_one
    (J : X →L[ℝ] Y) (N : X → Z)
    {R A B cH cL : ℝ}
    (hR : 0 < R) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hcL : 0 ≤ cL)
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
  have hdist :
      ‖ballRetraction R sx - ballRetraction R sy‖ ≤
        1 * (cH * ‖x - y‖) := by
    have hret :=
      (lipschitzWith_one_ballRetraction (X := X) hR.le).dist_le_mul sx sy
    rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm] at hret
    simpa only [one_mul] using hret.trans hhigh
  have h := radial_mixed_of_ball_bound J N hR hA hB hcL
    x y sx sy hJx hJy hhigh hlow hdist hbase
  convert h using 1 ; ring

end Hilbert

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear

end
