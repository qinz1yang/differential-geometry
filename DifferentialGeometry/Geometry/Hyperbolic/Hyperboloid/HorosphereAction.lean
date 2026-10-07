import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.HorosphereCoordinates
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.Boundary

namespace DifferentialGeometry.Hyperboloid

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

private theorem horosphere_null_decomposition (h : ℝ) (hh : 0 < h) (z : ℂ) :
    ((((northPoleHorosphereHomeomorph h hh).symm z).val.time,
      ((northPoleHorosphereHomeomorph h hh).symm z).val.space) : ℝ × E₃) =
      (1 / (2 * h)) • (1, (sphereNorthPole : E₃)) +
        (h * (‖z‖ ^ 2 + 4) / 8) • (1, ((stereographicComplex.symm z).val : E₃)) := by
  rw [northPoleHorosphereHomeomorph_symm_coordinates, stereographicComplex_symm_coe,
    sphereNorthPole_coe]
  apply Prod.ext
  · change h / 2 + 1 / (2 * h) + h * ‖z‖ ^ 2 / 8 =
      (1 / (2 * h)) * 1 + (h * (‖z‖ ^ 2 + 4) / 8) * 1
    ring
  · apply PiLp.ext
    intro i
    have hz : ‖z‖ ^ 2 + 4 ≠ 0 := by positivity
    fin_cases i
    · change -h / 2 + 1 / (2 * h) + h * ‖z‖ ^ 2 / 8 =
        1 / (2 * h) * 1 + (h * (‖z‖ ^ 2 + 4) / 8) * ((‖z‖ ^ 2 - 4) / (‖z‖ ^ 2 + 4))
      field_simp
      ring
    · change h / 2 * z.re = 1 / (2 * h) * 0 +
        (h * (‖z‖ ^ 2 + 4) / 8) * (4 * z.re / (‖z‖ ^ 2 + 4))
      field_simp
      ring
    · change h / 2 * z.im = 1 / (2 * h) * 0 +
        (h * (‖z‖ ^ 2 + 4) / 8) * (4 * z.im / (‖z‖ ^ 2 + 4))
      field_simp
      ring

private theorem lorentzExtension_null_image (e : Hyperboloid E₃ ≃ᵢ Hyperboloid E₃)
    (ξ : Metric.sphere (0 : E₃) 1) :
    lorentzExtension e (1, (ξ : E₃)) = (lorentzExtension e (1, (ξ : E₃))).1 •
      (1, (boundaryHomeomorph e ξ : E₃)) := by
  have ha := (lorentzExtension_sphere_time_pos e ξ).ne'
  have h := congrArg (fun z : E₃ => (lorentzExtension e (1, (ξ : E₃))).1 • z)
    (boundaryHomeomorph_apply_coe e ξ)
  apply Prod.ext
  · simp
  · change (lorentzExtension e (1, (ξ : E₃))).2 =
      (lorentzExtension e (1, (ξ : E₃))).1 • (boundaryHomeomorph e ξ : E₃)
    simpa only [smul_smul, mul_inv_cancel₀ ha, one_smul] using h.symm

private theorem lorentzForm_north_stereographic (z : ℂ) :
    lorentzForm E₃ (1, (sphereNorthPole : E₃))
      (1, ((stereographicComplex.symm z).val : E₃)) = -8 / (‖z‖ ^ 2 + 4) := by
  rw [lorentzForm_apply, sphereNorthPole_coe, EuclideanSpace.inner_single_left,
    map_one, one_mul, one_mul, stereographicComplex_symm_coe]
  change (‖z‖ ^ 2 - 4) / (‖z‖ ^ 2 + 4) - 1 = -8 / (‖z‖ ^ 2 + 4)
  have hd : ‖z‖ ^ 2 + 4 ≠ 0 := by positivity
  field_simp
  ring

theorem isometryEquiv_northPoleHorosphereHomeomorph_symm
    (e : Hyperboloid E₃ ≃ᵢ Hyperboloid E₃)
    (hn : boundaryHomeomorph e sphereNorthPole = sphereNorthPole)
    (h : ℝ) (hh : 0 < h) (z : ℂ) :
    let scale := (lorentzExtension e (1, (sphereNorthPole : E₃))).1
    let H : ℂ → ℂ := fun w => stereographicComplex
      ⟨boundaryHomeomorph e (stereographicComplex.symm w).val, by
        intro hp
        exact (stereographicComplex.symm w).property
          ((boundaryHomeomorph e).injective (hp.trans hn.symm))⟩
    e ((northPoleHorosphereHomeomorph h hh).symm z).val =
      ((northPoleHorosphereHomeomorph (h / scale)
        (div_pos hh (lorentzExtension_sphere_time_pos e sphereNorthPole))).symm (H z)).val := by
  let scale := (lorentzExtension e (1, (sphereNorthPole : E₃))).1
  let H : ℂ → ℂ := fun w => stereographicComplex
    ⟨boundaryHomeomorph e (stereographicComplex.symm w).val, by
      intro hp
      exact (stereographicComplex.symm w).property
        ((boundaryHomeomorph e).injective (hp.trans hn.symm))⟩
  dsimp only
  have hscalePos : 0 < scale := lorentzExtension_sphere_time_pos e sphereNorthPole
  let μ := (lorentzExtension e (1, ((stereographicComplex.symm z).val : E₃))).1
  have hμ : 0 < μ := lorentzExtension_sphere_time_pos e (stereographicComplex.symm z).val
  have heH : boundaryHomeomorph e (stereographicComplex.symm z).val =
      (stereographicComplex.symm (H z)).val := by
    exact (congrArg Subtype.val (stereographicComplex.symm_apply_apply
      ⟨boundaryHomeomorph e (stereographicComplex.symm z).val, by
        intro hp
        exact (stereographicComplex.symm z).property
          ((boundaryHomeomorph e).injective (hp.trans hn.symm))⟩)).symm
  have hN : lorentzExtension e (1, (sphereNorthPole : E₃)) = scale • (1, (sphereNorthPole : E₃)) := by
    simpa only [hn] using lorentzExtension_null_image e sphereNorthPole
  have hL : lorentzExtension e (1, ((stereographicComplex.symm z).val : E₃)) =
      μ • (1, ((stereographicComplex.symm (H z)).val : E₃)) := by
    simpa only [heH] using lorentzExtension_null_image e (stereographicComplex.symm z).val
  have hd : ‖z‖ ^ 2 + 4 ≠ 0 := by positivity
  have hD : ‖H z‖ ^ 2 + 4 ≠ 0 := by positivity
  have hpair := (lorentzExtension e).map_app
    (1, ((stereographicComplex.symm z).val : E₃)) (1, (sphereNorthPole : E₃))
  rw [hN, hL] at hpair
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul,
    lorentzForm_north_stereographic] at hpair
  have hscale : μ * (‖z‖ ^ 2 + 4) = (‖H z‖ ^ 2 + 4) / scale := by
    field_simp [hd, hD] at hpair
    apply (eq_div_iff hscalePos.ne').mpr
    nlinarith only [hpair]
  have hcoefficient : (h * (‖z‖ ^ 2 + 4) / 8) * μ =
      (h / scale) * (‖H z‖ ^ 2 + 4) / 8 := by
    calc
      _ = h / 8 * (μ * (‖z‖ ^ 2 + 4)) := by ring
      _ = _ := by rw [hscale]; ring
  have hfirst : (1 / (2 * h)) * scale = 1 / (2 * (h / scale)) := by field_simp
  let y := ((northPoleHorosphereHomeomorph (h / scale) (div_pos hh hscalePos)).symm (H z)).val
  have hcoords : ((e ((northPoleHorosphereHomeomorph h hh).symm z).val).time,
      (e ((northPoleHorosphereHomeomorph h hh).symm z).val).space) = (y.time, y.space) := by
    dsimp only [y]
    rw [← lorentzExtension_apply, horosphere_null_decomposition, map_add, map_smul, map_smul,
      hN, hL, smul_smul, smul_smul, hcoefficient, hfirst, horosphere_null_decomposition]
  exact Hyperboloid.ext (congrArg Prod.snd hcoords)

end DifferentialGeometry.Hyperboloid
