import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.BoundaryPlaneAffine
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.BoundaryTransitivity
import Mathlib.Topology.MetricSpace.Contracting

noncomputable section

namespace DifferentialGeometry.Hyperboloid

local notation "E3" => EuclideanSpace ℝ (Fin 3)

private theorem exists_fixedPoint_smul_linearIsometryEquiv_add
    (L : ℂ ≃ₗᵢ[ℝ] ℂ) (scale : ℝ) (hs : 0 < scale) (hne : scale ≠ 1) (b : ℂ) :
    ∃ z : ℂ, scale • L z + b = z := by
  let H (z : ℂ) := scale • L z + b
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hc : ContractingWith ⟨scale, hs.le⟩ H := by
      refine ⟨hlt, LipschitzWith.of_dist_le_mul ?_⟩
      intro z w
      change dist (scale • L z + b) (scale • L w + b) ≤ scale * dist z w
      rw [dist_add_right, dist_eq_norm, ← smul_sub, norm_smul,
        Real.norm_eq_abs, abs_of_pos hs, ← dist_eq_norm, L.dist_map]
    exact ⟨hc.fixedPoint H, hc.fixedPoint_isFixedPt⟩
  · let G (z : ℂ) := L.symm (scale⁻¹ • (z - b))
    have hinv : 0 < scale⁻¹ := inv_pos.mpr hs
    have hc : ContractingWith ⟨scale⁻¹, hinv.le⟩ G := by
      refine ⟨(inv_lt_one₀ hs).mpr hgt, LipschitzWith.of_dist_le_mul ?_⟩
      intro z w
      change dist (L.symm (scale⁻¹ • (z - b))) (L.symm (scale⁻¹ • (w - b))) ≤
        scale⁻¹ * dist z w
      rw [L.symm.dist_map, dist_eq_norm, ← smul_sub,
        show (z - b) - (w - b) = z - w by abel,
        norm_smul, Real.norm_eq_abs, abs_of_pos hinv, ← dist_eq_norm]
    have hinverse (z : ℂ) : H (G z) = z := by
      change scale • L (L.symm (scale⁻¹ • (z - b))) + b = z
      rw [L.apply_symm_apply, smul_smul, mul_inv_cancel₀ hs.ne', one_smul, sub_add_cancel]
    let z := hc.fixedPoint G
    have hz : G z = z := hc.fixedPoint_isFixedPt
    refine ⟨z, ?_⟩
    change H z = z
    exact (congrArg H hz).symm.trans (hinverse z)

private theorem exists_north_boundary_fixedPoint_ne_of_time_ne_one
    (e : Hyperboloid E3 ≃ᵢ Hyperboloid E3)
    (hn : boundaryHomeomorph e sphereNorthPole = sphereNorthPole)
    (hscale : (lorentzExtension e (1, (sphereNorthPole : E3))).1 ≠ 1) :
    ∃ ξ : Metric.sphere (0 : E3) 1,
      ξ ≠ sphereNorthPole ∧ boundaryHomeomorph e ξ = ξ := by
  let scale := (lorentzExtension e (1, (sphereNorthPole : E3))).1
  have hs : 0 < scale := lorentzExtension_sphere_time_pos e sphereNorthPole
  let H (z : ℂ) := stereographicComplex
    ⟨boundaryHomeomorph e (stereographicComplex.symm z).val, by
      intro hp
      exact (stereographicComplex.symm z).property
        ((boundaryHomeomorph e).injective (hp.trans hn.symm))⟩
  obtain ⟨L, hL⟩ := exists_stereographicComplex_similarity e hn
  change ∀ z : ℂ, H z = scale • L z + H 0 at hL
  obtain ⟨z, hz⟩ := exists_fixedPoint_smul_linearIsometryEquiv_add L scale hs hscale (H 0)
  have hfix : H z = z := (hL z).trans hz
  refine ⟨(stereographicComplex.symm z).val, (stereographicComplex.symm z).property, ?_⟩
  have hh := congrArg (fun w : ℂ => (stereographicComplex.symm w).val) hfix
  simpa only [H, stereographicComplex.symm_apply_apply] using hh

theorem exists_boundary_fixedPoint_ne_of_lorentzExtension_time_ne_one
    (e : Hyperboloid E3 ≃ᵢ Hyperboloid E3) (ξ : Metric.sphere (0 : E3) 1)
    (hξ : boundaryHomeomorph e ξ = ξ)
    (hscale : (lorentzExtension e (1, (ξ : E3))).1 ≠ 1) :
    ∃ η : Metric.sphere (0 : E3) 1, η ≠ ξ ∧ boundaryHomeomorph e η = η := by
  obtain ⟨C, hC0, hCξ⟩ := exists_isometryEquiv_origin_fixed_boundary_eq ξ sphereNorthPole
  have hCnull0 : lorentzExtension C (1, 0) = (1, 0) := by
    simpa only [origin_time, origin_space, hC0] using lorentzExtension_apply C (origin : Hyperboloid E3)
  have hCtime (v : ℝ × E3) : (lorentzExtension C v).1 = v.1 := by
    have hp := (lorentzExtension C).map_app v (1, 0)
    rw [hCnull0] at hp
    simp only [lorentzForm_apply, inner_zero_left, one_mul, zero_sub] at hp
    linarith only [hp]
  have hCnull : lorentzExtension C (1, (ξ : E3)) = (1, (sphereNorthPole : E3)) := by
    have hp := boundaryHomeomorph_apply_coe C ξ
    rw [hCξ, hCtime] at hp
    simp only [inv_one, one_smul] at hp
    exact Prod.ext (hCtime _) hp.symm
  have hCinvnull : lorentzExtension C.symm (1, (sphereNorthPole : E3)) = (1, (ξ : E3)) := by
    rw [lorentzExtension_symm, ← hCnull]
    exact (lorentzExtension C).toLinearEquiv.symm_apply_apply _
  have hCinv : boundaryHomeomorph C.symm sphereNorthPole = ξ := by
    rw [← boundaryHomeomorph_symm, ← hCξ]
    exact (boundaryHomeomorph C).symm_apply_apply ξ
  let f := C.symm.trans (e.trans C)
  have hn : boundaryHomeomorph f sphereNorthPole = sphereNorthPole := by
    simp only [f, boundaryHomeomorph_trans, Homeomorph.trans_apply]
    rw [hCinv, hξ, hCξ]
  let scale := (lorentzExtension e (1, (ξ : E3))).1
  have hs : 0 < scale := lorentzExtension_sphere_time_pos e ξ
  have hAnull : lorentzExtension e (1, (ξ : E3)) = scale • (1, (ξ : E3)) := by
    have hp := boundaryHomeomorph_apply_coe e ξ
    rw [hξ] at hp
    change (ξ : E3) = scale⁻¹ • (lorentzExtension e (1, (ξ : E3))).2 at hp
    have hm := congrArg (fun w : E3 => scale • w) hp
    simp only [smul_smul, mul_inv_cancel₀ hs.ne', one_smul] at hm
    apply Prod.ext
    · change scale = scale * 1
      rw [mul_one]
    · exact hm.symm
  have hfn : lorentzExtension f (1, (sphereNorthPole : E3)) =
      scale • (1, (sphereNorthPole : E3)) := by
    simp only [f, lorentzExtension_trans]
    change lorentzExtension C (lorentzExtension e
      (lorentzExtension C.symm (1, (sphereNorthPole : E3)))) = _
    rw [hCinvnull, hAnull, map_smul, hCnull]
  have hfscale : (lorentzExtension f (1, (sphereNorthPole : E3))).1 ≠ 1 := by
    have hh := congrArg Prod.fst hfn
    change (lorentzExtension f (1, (sphereNorthPole : E3))).1 = scale * 1 at hh
    rw [mul_one] at hh
    rwa [hh]
  obtain ⟨ζ, hζne, hζfix⟩ := exists_north_boundary_fixedPoint_ne_of_time_ne_one f hn hfscale
  refine ⟨boundaryHomeomorph C.symm ζ, ?_, ?_⟩
  · intro heq
    apply hζne
    have hh := congrArg (boundaryHomeomorph C) heq
    rw [← boundaryHomeomorph_symm, (boundaryHomeomorph C).apply_symm_apply, hCξ] at hh
    exact hh
  · have hh := congrArg (boundaryHomeomorph C.symm) hζfix
    simp only [f, boundaryHomeomorph_trans, Homeomorph.trans_apply] at hh
    rw [← boundaryHomeomorph_symm, (boundaryHomeomorph C).symm_apply_apply] at hh
    exact hh

theorem exists_fixedPoint_ne_northPole_of_lorentzExtension_time_ne_one
    (e : Hyperboloid E3 ≃ᵢ Hyperboloid E3)
    (hn : boundaryHomeomorph e sphereNorthPole = sphereNorthPole)
    (hscale : (lorentzExtension e (1, (sphereNorthPole : E3))).1 ≠ 1) :
    ∃ ξ : Metric.sphere (0 : E3) 1,
      ξ ≠ sphereNorthPole ∧ boundaryHomeomorph e ξ = ξ :=
  exists_boundary_fixedPoint_ne_of_lorentzExtension_time_ne_one e sphereNorthPole hn hscale

end DifferentialGeometry.Hyperboloid
