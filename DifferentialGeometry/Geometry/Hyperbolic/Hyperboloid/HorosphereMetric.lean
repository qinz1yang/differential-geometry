import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.HorosphereCoordinates
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.RiemannianMetric

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.Hyperboloid

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

private def horosphereSpace (h : ℝ) (z : ℂ) : E₃ :=
  WithLp.toLp 2 ![-h / 2 + 1 / (2 * h) + (h / 8) * ‖z‖ ^ 2,
    (h / 2) * z.re, (h / 2) * z.im]

private theorem horosphere_space (h : ℝ) (hh : 0 < h) (z : ℂ) :
    ((northPoleHorosphereHomeomorph h hh).symm z).val.space = horosphereSpace h z := by
  have hs := congrArg Prod.snd (northPoleHorosphereHomeomorph_symm_coordinates h hh z)
  dsimp only at hs
  rw [hs]
  apply PiLp.ext
  intro i
  fin_cases i
  · dsimp [horosphereSpace]
    ring
  · rfl
  · rfl

private theorem contDiff_horosphereSpace (h : ℝ) {n : ℕ∞ω} : ContDiff ℝ n (horosphereSpace h) := by
  let L := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm
  have hf : ContDiff ℝ n (fun z : ℂ => ![-h / 2 + 1 / (2 * h) + (h / 8) * ‖z‖ ^ 2,
      (h / 2) * z.re, (h / 2) * z.im]) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i
    · exact contDiff_const.add (contDiff_const.mul (contDiff_norm_sq ℝ))
    · exact contDiff_const.mul Complex.reCLM.contDiff
    · exact contDiff_const.mul Complex.imCLM.contDiff
  exact L.contDiff.comp hf

theorem contMDiff_northPoleHorosphereHomeomorph_symm (h : ℝ) (hh : 0 < h) {n : ℕ∞ω} :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E₃) n
      (fun z : ℂ => ((northPoleHorosphereHomeomorph h hh).symm z).val) := by
  have he : (fun z : ℂ => ((northPoleHorosphereHomeomorph h hh).symm z).val) =
      ofSpace ∘ horosphereSpace h := by
    funext z
    apply Hyperboloid.ext
    exact horosphere_space h hh z
  rw [he]
  exact contMDiff_ofSpace.comp (contDiff_horosphereSpace h).contMDiff

private def horosphereSpaceDerivative (h : ℝ) (z : ℂ) : ℂ →L[ℝ] E₃ :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi ![(h / 8) • (2 • innerSL ℝ z),
      (h / 2) • Complex.reCLM, (h / 2) • Complex.imCLM])

private theorem hasFDerivAt_horosphereSpace (h : ℝ) (z : ℂ) :
    HasFDerivAt (horosphereSpace h) (horosphereSpaceDerivative h z) z := by
  have hpi : HasFDerivAt
      (fun w : ℂ => ![-h / 2 + 1 / (2 * h) + (h / 8) * ‖w‖ ^ 2,
        (h / 2) * w.re, (h / 2) * w.im])
      (ContinuousLinearMap.pi ![(h / 8) • (2 • innerSL ℝ z),
        (h / 2) • Complex.reCLM, (h / 2) • Complex.imCLM]) z := by
    apply hasFDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact (((hasStrictFDerivAt_norm_sq z).hasFDerivAt.const_smul (h / 8)).const_add
        (-h / 2 + 1 / (2 * h)))
    · exact Complex.reCLM.hasFDerivAt.const_smul (h / 2)
    · exact Complex.imCLM.hasFDerivAt.const_smul (h / 2)
  exact ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap.hasFDerivAt).comp z hpi

private theorem fderiv_horosphereSpace_apply (h : ℝ) (z u : ℂ) :
    fderiv ℝ (horosphereSpace h) z u =
      WithLp.toLp 2 ![h / 4 * inner ℝ z u, h / 2 * u.re, h / 2 * u.im] := by
  rw [(hasFDerivAt_horosphereSpace h z).fderiv]
  apply PiLp.ext
  intro i
  fin_cases i
  · simp [horosphereSpaceDerivative, smul_eq_mul]
    ring
  · rfl
  · rfl

private theorem mvfderiv_space_horosphere_apply (h : ℝ) (hh : 0 < h) (z u : ℂ) :
    let P : ℂ → Hyperboloid E₃ := fun w => ((northPoleHorosphereHomeomorph h hh).symm w).val
    mvfderiv 𝓘(ℝ, E₃) spaceDiffeomorph (P z)
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E₃) P z ((NormedSpace.fromTangentSpace (𝕜 := ℝ) z).symm u)) =
        WithLp.toLp 2 ![h / 4 * inner ℝ z u, h / 2 * u.re, h / 2 * u.im] := by
  let P : ℂ → Hyperboloid E₃ := fun w => ((northPoleHorosphereHomeomorph h hh).symm w).val
  dsimp only
  have hp := (contMDiff_northPoleHorosphereHomeomorph_symm h hh (n := ∞)).mdifferentiableAt
    (x := z) (by simp)
  have hs : MDifferentiableAt 𝓘(ℝ, E₃) 𝓘(ℝ, E₃) spaceDiffeomorph (P z) :=
    (contMDiff_space (E := E₃) (n := ∞)).mdifferentiableAt (by simp)
  have he : spaceDiffeomorph ∘ P = horosphereSpace h := funext (horosphere_space h hh)
  rw [← mvfderiv_comp_apply z hs hp, he, mvfderiv_eq_fderiv]
  change fderiv ℝ (horosphereSpace h) z u = _
  exact fderiv_horosphereSpace_apply h z u

theorem riemannianMetric_inner_northPoleHorosphereHomeomorph_symm
    (h : ℝ) (hh : 0 < h) (z u v : ℂ) :
    let P : ℂ → Hyperboloid E₃ := fun w => ((northPoleHorosphereHomeomorph h hh).symm w).val
    riemannianMetric.inner (P z)
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E₃) P z ((NormedSpace.fromTangentSpace (𝕜 := ℝ) z).symm u))
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E₃) P z ((NormedSpace.fromTangentSpace (𝕜 := ℝ) z).symm v)) =
        (h ^ 2 / 4) * inner ℝ u v := by
  let P : ℂ → Hyperboloid E₃ := fun w => ((northPoleHorosphereHomeomorph h hh).symm w).val
  dsimp only
  let V : ℂ → E₃ := fun a => WithLp.toLp 2 ![h / 4 * inner ℝ z a, h / 2 * a.re, h / 2 * a.im]
  have hspace : (P z).space = horosphereSpace h z := horosphere_space h hh z
  have htime : (P z).time = h / 2 + 1 / (2 * h) + h * ‖z‖ ^ 2 / 8 :=
    congrArg Prod.fst (northPoleHorosphereHomeomorph_symm_coordinates h hh z)
  have hin (a : ℂ) : inner ℝ (P z).space (V a) = (P z).time * (h / 4 * inner ℝ z a) := by
    rw [hspace, htime]
    simp only [horosphereSpace, V, PiLp.inner_apply, Fin.sum_univ_succ,
      Fin.sum_univ_zero, add_zero, Real.inner_apply]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_succ]
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.inner, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    field_simp
    ring
  rw [riemannianMetric_inner]
  change inner ℝ
      (mvfderiv 𝓘(ℝ, E₃) spaceDiffeomorph (P z)
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E₃) P z ((NormedSpace.fromTangentSpace (𝕜 := ℝ) z).symm u)))
      (mvfderiv 𝓘(ℝ, E₃) spaceDiffeomorph (P z)
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E₃) P z ((NormedSpace.fromTangentSpace (𝕜 := ℝ) z).symm v))) -
      inner ℝ (P z).space (mvfderiv 𝓘(ℝ, E₃) spaceDiffeomorph (P z)
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E₃) P z ((NormedSpace.fromTangentSpace (𝕜 := ℝ) z).symm u))) *
      inner ℝ (P z).space (mvfderiv 𝓘(ℝ, E₃) spaceDiffeomorph (P z)
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E₃) P z ((NormedSpace.fromTangentSpace (𝕜 := ℝ) z).symm v))) /
      (1 + ‖(P z).space‖ ^ 2) = _
  rw [mvfderiv_space_horosphere_apply, mvfderiv_space_horosphere_apply]
  change inner ℝ (V u) (V v) - inner ℝ (P z).space (V u) * inner ℝ (P z).space (V v) /
    (1 + ‖(P z).space‖ ^ 2) = _
  rw [hin, hin, ← (P z).time_sq]
  have hcancel : (P z).time * (h / 4 * inner ℝ z u) *
      ((P z).time * (h / 4 * inner ℝ z v)) / (P z).time ^ 2 =
        (h / 4 * inner ℝ z u) * (h / 4 * inner ℝ z v) := by
    field_simp [(P z).time_pos.ne']
  rw [hcancel]
  simp only [V, PiLp.inner_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Real.inner_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_succ, Complex.inner, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

end DifferentialGeometry.Hyperboloid
