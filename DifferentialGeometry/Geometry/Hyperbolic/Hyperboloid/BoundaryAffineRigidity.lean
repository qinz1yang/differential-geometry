import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.BoundaryInversion
import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv
import Mathlib.Tactic.Module

noncomputable section

namespace DifferentialGeometry.Hyperboloid

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "S2" => Metric.sphere (0 : E3) 1
local notation "inv₂" => EuclideanGeometry.inversion (0 : ℂ) 2

private theorem inversion_zero_two_smul (z : ℂ) : inv₂ z = (4 / ‖z‖ ^ 2 : ℝ) • z := by
  simp only [EuclideanGeometry.inversion, dist_zero_right, vsub_eq_sub, sub_zero,
    vadd_eq_add, add_zero]
  congr 1
  norm_num [div_pow]

private theorem similarity_of_inversion_intertwining (L M : ℂ ≃ₗ[ℝ] ℂ)
    (h : ∀ z : ℂ, z ≠ 0 → M (inv₂ z) = inv₂ (L z)) :
    ∃ c : ℝ, 0 < c ∧ ∃ Q : ℂ ≃ₗᵢ[ℝ] ℂ, ∀ z : ℂ, L z = c • Q z := by
  let T := M.trans L.symm
  let r (z : ℂ) := ‖z‖ ^ 2 / ‖L z‖ ^ 2
  have hrad (z : ℂ) (hz : z ≠ 0) : T z = r z • z := by
    have hn : ‖z‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hz)
    have hh := congrArg L.symm (h z hz)
    simp only [inversion_zero_two_smul, map_smul, L.symm_apply_apply] at hh
    have hh' := congrArg (fun w : ℂ => (‖z‖ ^ 2 / 4 : ℝ) • w) hh
    rw [smul_smul, smul_smul] at hh'
    have hleft : (‖z‖ ^ 2 / 4 : ℝ) * (4 / ‖z‖ ^ 2) = 1 := by field_simp [hn]
    have hright : (‖z‖ ^ 2 / 4 : ℝ) * (4 / ‖L z‖ ^ 2) = r z := by
      dsimp only [r]
      ring
    rw [hleft, one_smul, hright] at hh'
    exact hh'
  have h1 : T 1 = r 1 • (1 : ℂ) := hrad 1 one_ne_zero
  have hI : T Complex.I = r Complex.I • Complex.I := hrad _ Complex.I_ne_zero
  have hsum : T (1 + Complex.I) = r (1 + Complex.I) • (1 + Complex.I) :=
    hrad _ (by intro hzero; have := congrArg Complex.re hzero; norm_num at this)
  rw [map_add, h1, hI] at hsum
  have hre := congrArg Complex.re hsum
  have him := congrArg Complex.im hsum
  simp only [Complex.add_re, Complex.smul_re, Complex.one_re, Complex.I_re,
    smul_eq_mul, mul_one, mul_zero, add_zero] at hre
  simp only [Complex.add_im, Complex.smul_im, Complex.one_im, Complex.I_im,
    smul_eq_mul, mul_one, mul_zero, zero_add] at him
  have hrI : r Complex.I = r 1 := him.trans hre.symm
  have hT (z : ℂ) : T z = r 1 • z := by
    have hz : z.re • (1 : ℂ) + z.im • Complex.I = z := by
      apply Complex.ext <;> simp
    rw [← hz, map_add, map_smul, map_smul, h1, hI, hrI]
    module
  have hratio (z : ℂ) (hz : z ≠ 0) : r z = r 1 := by
    apply smul_left_injective ℝ hz
    exact (hrad z hz).symm.trans (hT z)
  let c := ‖L 1‖
  have hc : 0 < c := by
    apply norm_pos_iff.mpr
    exact fun hzero => one_ne_zero (L.injective (hzero.trans L.map_zero.symm))
  have hnorm (z : ℂ) : ‖L z‖ = c * ‖z‖ := by
    by_cases hz : z = 0
    · simp [hz]
    have hz' : L z ≠ 0 := fun hzero => hz (L.injective (hzero.trans L.map_zero.symm))
    have hn : ‖L z‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hz')
    have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc.ne'
    have hh := hratio z hz
    change ‖z‖ ^ 2 / ‖L z‖ ^ 2 = ‖(1 : ℂ)‖ ^ 2 / c ^ 2 at hh
    simp only [norm_one, one_pow] at hh
    have hsquare : ‖L z‖ ^ 2 = (c * ‖z‖) ^ 2 := by
      have heq := (div_eq_div_iff hn hc2).mp hh
      nlinarith only [heq]
    exact (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg hc.le (norm_nonneg _))).mp hsquare
  let Q : ℂ ≃ₗᵢ[ℝ] ℂ :=
    { toLinearEquiv := L.trans (LinearEquiv.smulOfNeZero ℝ ℂ c⁻¹ (inv_ne_zero hc.ne'))
      norm_map' := by
        intro z
        change ‖c⁻¹ • L z‖ = ‖z‖
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc), hnorm]
        field_simp [hc.ne'] }
  refine ⟨c, hc, Q, ?_⟩
  intro z
  change L z = c • (c⁻¹ • L z)
  rw [smul_smul, mul_inv_cancel₀ hc.ne', one_smul]

private theorem inverse_north_ne_of_move (e : Hyperboloid E3 ≃ᵢ Hyperboloid E3)
    (he : boundaryHomeomorph e sphereNorthPole ≠ sphereNorthPole) :
    (boundaryHomeomorph e).symm sphereNorthPole ≠ sphereNorthPole := by
  intro h
  apply he
  calc
    boundaryHomeomorph e sphereNorthPole =
        boundaryHomeomorph e ((boundaryHomeomorph e).symm sphereNorthPole) :=
      congrArg (boundaryHomeomorph e) h.symm
    _ = sphereNorthPole := (boundaryHomeomorph e).apply_symm_apply _

private theorem north_fixed_of_affine_stereographic (H : S2 ≃ₜ S2) (A : ℂ ≃ᵃ[ℝ] ℂ)
    (hA : ∀ z : ℂ, H (stereographicComplex.symm z).val =
      (stereographicComplex.symm (A z)).val) :
    H sphereNorthPole = sphereNorthPole := by
  by_contra hn
  let ξ : {ξ : S2 // ξ ≠ sphereNorthPole} := ⟨H sphereNorthPole, hn⟩
  let z := stereographicComplex ξ
  have hz : (stereographicComplex.symm z).val = H sphereNorthPole :=
    congrArg Subtype.val (stereographicComplex.symm_apply_apply ξ)
  have heq := hA (A.symm z)
  rw [A.apply_symm_apply, hz] at heq
  exact (stereographicComplex.symm (A.symm z)).property (H.injective heq)

theorem exists_similarity_of_affine_boundary_conjugacy
    (H : S2 ≃ₜ S2)
    (A : ℂ ≃ᵃ[ℝ] ℂ)
    (hA : ∀ z : ℂ, H (stereographicComplex.symm z).val =
      (stereographicComplex.symm (A z)).val)
    (e e' : Hyperboloid E3 ≃ᵢ Hyperboloid E3)
    (he : boundaryHomeomorph e sphereNorthPole ≠ sphereNorthPole)
    (heq : ∀ ξ : S2, H (boundaryHomeomorph e ξ) = boundaryHomeomorph e' (H ξ)) :
    ∃ c : ℝ, 0 < c ∧ ∃ Q : ℂ ≃ₗᵢ[ℝ] ℂ, ∀ z : ℂ, A.linear z = c • Q z := by
  have hHn := north_fixed_of_affine_stereographic H A hA
  have he' : boundaryHomeomorph e' sphereNorthPole ≠ sphereNorthPole := by
    intro hp
    have hh := heq sphereNorthPole
    rw [hHn, hp] at hh
    exact he (H.injective (hh.trans hHn.symm))
  let a := stereographicComplex
    ⟨(boundaryHomeomorph e).symm sphereNorthPole, inverse_north_ne_of_move e he⟩
  let b := stereographicComplex ⟨boundaryHomeomorph e sphereNorthPole, he⟩
  let a' := stereographicComplex
    ⟨(boundaryHomeomorph e').symm sphereNorthPole, inverse_north_ne_of_move e' he'⟩
  let b' := stereographicComplex ⟨boundaryHomeomorph e' sphereNorthPole, he'⟩
  have hchi : Function.Injective (fun z : ℂ => (stereographicComplex.symm z).val) := by
    intro z w hzw
    exact stereographicComplex.symm.injective (Subtype.ext hzw)
  have ha : (stereographicComplex.symm a).val = (boundaryHomeomorph e).symm sphereNorthPole :=
    congrArg Subtype.val (stereographicComplex.symm_apply_apply _)
  have hb : (stereographicComplex.symm b).val = boundaryHomeomorph e sphereNorthPole :=
    congrArg Subtype.val (stereographicComplex.symm_apply_apply _)
  have ha' : (stereographicComplex.symm a').val = (boundaryHomeomorph e').symm sphereNorthPole :=
    congrArg Subtype.val (stereographicComplex.symm_apply_apply _)
  have hb' : (stereographicComplex.symm b').val = boundaryHomeomorph e' sphereNorthPole :=
    congrArg Subtype.val (stereographicComplex.symm_apply_apply _)
  have hAa : A a = a' := by
    apply hchi
    change (stereographicComplex.symm (A a)).val =
      (stereographicComplex.symm a').val
    rw [← hA a, ha, ha']
    apply (boundaryHomeomorph e').injective
    calc
      boundaryHomeomorph e' (H ((boundaryHomeomorph e).symm sphereNorthPole)) =
          H (boundaryHomeomorph e ((boundaryHomeomorph e).symm sphereNorthPole)) := (heq _).symm
      _ = sphereNorthPole := by rw [Homeomorph.apply_symm_apply, hHn]
      _ = boundaryHomeomorph e' ((boundaryHomeomorph e').symm sphereNorthPole) :=
        ((boundaryHomeomorph e').apply_symm_apply _).symm
  have hAb : A b = b' := by
    apply hchi
    change (stereographicComplex.symm (A b)).val =
      (stereographicComplex.symm b').val
    rw [← hA b, hb, hb', heq, hHn]
  obtain ⟨s, hs, Q, hQ⟩ := exists_stereographicComplex_inversion_similarity e he
  change ∀ z : ℂ, z ≠ a → boundaryHomeomorph e (stereographicComplex.symm z).val =
    (stereographicComplex.symm (b + s • Q (inv₂ (z - a)))).val at hQ
  obtain ⟨s', hs', Q', hQ'⟩ := exists_stereographicComplex_inversion_similarity e' he'
  change ∀ z : ℂ, z ≠ a' → boundaryHomeomorph e' (stereographicComplex.symm z).val =
    (stereographicComplex.symm (b' + s' • Q' (inv₂ (z - a')))).val at hQ'
  have hplane (z : ℂ) (hz : z ≠ a) :
      A (b + s • Q (inv₂ (z - a))) = b' + s' • Q' (inv₂ (A z - a')) := by
    have hAz : A z ≠ a' := by
      intro haz
      exact hz (A.injective (haz.trans hAa.symm))
    apply hchi
    calc
      (stereographicComplex.symm (A (b + s • Q (inv₂ (z - a))))).val =
          H (stereographicComplex.symm (b + s • Q (inv₂ (z - a)))).val := (hA _).symm
      _ = H (boundaryHomeomorph e (stereographicComplex.symm z).val) := congrArg H (hQ z hz).symm
      _ = boundaryHomeomorph e' (H (stereographicComplex.symm z).val) := heq _
      _ = boundaryHomeomorph e' (stereographicComplex.symm (A z)).val := congrArg _ (hA z)
      _ = _ := hQ' (A z) hAz
  let L := A.linear
  have hadd (x y : ℂ) : A (x + y) = A x + L y := by
    simpa only [vadd_eq_add, add_comm] using A.map_vadd x y
  have hinter (z : ℂ) (hz : z ≠ 0) :
      L (s • Q (inv₂ z)) = s' • Q' (inv₂ (L z)) := by
    have hza : a + z ≠ a := by intro hh; exact hz (add_eq_left.mp hh)
    have hh := hplane (a + z) hza
    have hh' := hh
    rw [hadd] at hh'
    rw [hAb] at hh'
    have hArg : A (a + z) - a' = L z := by
      rw [hadd, hAa]
      exact add_sub_cancel_left _ _
    rw [hArg, add_sub_cancel_left] at hh'
    exact add_left_cancel hh'
  let S := Q.toLinearEquiv.trans (LinearEquiv.smulOfNeZero ℝ ℂ s hs.ne')
  let S' := Q'.toLinearEquiv.trans (LinearEquiv.smulOfNeZero ℝ ℂ s' hs'.ne')
  let M := S.trans (L.trans S'.symm)
  have hM (z : ℂ) (hz : z ≠ 0) : M (inv₂ z) = inv₂ (L z) := by
    change S'.symm (L (S (inv₂ z))) = _
    have hh : L (S (inv₂ z)) = S' (inv₂ (L z)) := hinter z hz
    rw [hh, S'.symm_apply_apply]
  exact similarity_of_inversion_intertwining L M hM

end DifferentialGeometry.Hyperboloid
