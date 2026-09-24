import DifferentialGeometry.Topology.Manifold.SphereOrientationIsotopy
import DifferentialGeometry.Topology.Manifold.StereographicAntipodal
import DifferentialGeometry.Topology.Diffeomorph.SphereIsotopy

section

set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.Manifold

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "S2" => Metric.sphere (0 : E3) 1

private local instance sphereDimension : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

private theorem exists_norm_preserving_extension_of_positive_radial_derivative
    (f : S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2) (v : S2)
    (hpos : 0 < (fderiv ℝ (sphereRadialExtension f) (v : E3)).toLinearMap.det) :
    ∃ D : E3 ≃ₘ[ℝ] E3, (∀ x, ‖D x‖ = ‖x‖) ∧
      ∀ (z : S2) (r : ℝ), r ∈ Icc (1 / 2 : ℝ) (3 / 2) →
        D (r • (z : E3)) = r • (f z : E3) := by
  obtain ⟨J, hJ, hJi, hJ0, hJ1⟩ :=
    (sphere_isotopy_iff_positive_radial_derivative f v).mpr hpos
  let A (t : ℝ) := J (1 - t)
  have ht : ContMDiff (𝓘(ℝ).prod (𝓡 2)) (𝓘(ℝ).prod (𝓡 2)) ∞
      (fun q : ℝ × S2 => (1 - q.1, q.2)) :=
    (contMDiff_const.sub contMDiff_fst).prodMk contMDiff_snd
  have hA : ContMDiff (𝓘(ℝ).prod (𝓡 2)) (𝓡 2) ∞
      (fun q : ℝ × S2 => A q.1 q.2) := hJ.comp ht
  have hAi : ContMDiff (𝓘(ℝ).prod (𝓡 2)) (𝓡 2) ∞
      (fun q : ℝ × S2 => (A q.1).symm q.2) := hJi.comp ht
  have hA0 : A 0 = Diffeomorph.refl (𝓡 2) S2 ∞ := by
    simpa only [A, sub_zero] using hJ1
  have hA1 : A 1 = f := by
    simpa only [A, sub_self] using hJ0
  obtain ⟨H, _hH, _hHi, _hH0, hnorm, _hfixed, hcollar, _himages⟩ :=
    Diffeomorph.exists_isotopy_extension_sphere_product_collar (d := 2) A hA hAi hA0
  refine ⟨H 1, fun x => (hnorm 1 x).1, ?_⟩
  intro z r hr
  simpa only [hA1] using (hcollar 1 z r hr).1

private theorem sphereRadialExtension_antipodal :
    sphereRadialExtension (sphereAntipodalDiffeomorph (E := E3) (n := 2)) =
      fun x : E3 => -x := by
  funext x
  by_cases hx : x = 0
  · simp [sphereRadialExtension, hx]
  · rw [sphereRadialExtension_of_ne_zero _ hx]
    change ‖x‖ • -(‖x‖⁻¹ • x) = -x
    rw [smul_neg, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx), one_smul]

theorem exists_norm_preserving_diffeomorph_extension_sphere_collar
    (f : S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2) :
    ∃ D : E3 ≃ₘ[ℝ] E3, (∀ x, ‖D x‖ = ‖x‖) ∧
      ∀ (z : S2) (r : ℝ), r ∈ Icc (1 / 2 : ℝ) (3 / 2) →
        D (r • (z : E3)) = r • (f z : E3) := by
  let v : S2 := ⟨EuclideanSpace.single 0 1, by simp⟩
  by_cases hpos : 0 < (fderiv ℝ (sphereRadialExtension f) (v : E3)).toLinearMap.det
  · exact exists_norm_preserving_extension_of_positive_radial_derivative f v hpos
  · have hne := det_fderiv_sphereRadialExtension_ne_zero f (ne_zero_of_mem_unit_sphere v)
    have hneg : (fderiv ℝ (sphereRadialExtension f) (v : E3)).toLinearMap.det < 0 :=
      lt_of_le_of_ne (le_of_not_gt hpos) hne
    let antipodal := sphereAntipodalDiffeomorph (E := E3) (n := 2)
    let g := f.trans antipodal
    have hradial : sphereRadialExtension g = fun x : E3 => -sphereRadialExtension f x := by
      change sphereRadialExtension ((antipodal : S2 → S2) ∘ f) = _
      rw [sphereRadialExtension_comp, sphereRadialExtension_antipodal]
      rfl
    have hder : fderiv ℝ (sphereRadialExtension g) (v : E3) =
        -fderiv ℝ (sphereRadialExtension f) (v : E3) := by
      rw [hradial, fderiv_fun_neg]
    have hdet : (fderiv ℝ (sphereRadialExtension g) (v : E3)).toLinearMap.det =
        -(fderiv ℝ (sphereRadialExtension f) (v : E3)).toLinearMap.det := by
      rw [hder]
      change LinearMap.det (-(fderiv ℝ (sphereRadialExtension f) (v : E3)).toLinearMap) = _
      rw [← neg_one_smul ℝ (fderiv ℝ (sphereRadialExtension f) (v : E3)).toLinearMap,
        LinearMap.det_smul]
      norm_num
    have hgpos : 0 < (fderiv ℝ (sphereRadialExtension g) (v : E3)).toLinearMap.det := by
      rw [hdet]
      exact neg_pos.mpr hneg
    obtain ⟨D, hnorm, hcollar⟩ :=
      exists_norm_preserving_extension_of_positive_radial_derivative g v hgpos
    refine ⟨D.trans (ContinuousLinearEquiv.neg ℝ).toDiffeomorph, ?_, ?_⟩
    · intro x
      change ‖-D x‖ = ‖x‖
      rw [norm_neg, hnorm]
    · intro z r hr
      change -D (r • (z : E3)) = r • (f z : E3)
      rw [hcollar z r hr]
      change -(r • -(f z : E3)) = r • (f z : E3)
      rw [smul_neg, neg_neg]

theorem exists_norm_preserving_diffeomorph_extension_sphere
    (f : S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2) :
    ∃ D : E3 ≃ₘ[ℝ] E3, (∀ x, ‖D x‖ = ‖x‖) ∧
      ∀ z : S2, D (z : E3) = (f z : E3) := by
  obtain ⟨D, hnorm, hcollar⟩ := exists_norm_preserving_diffeomorph_extension_sphere_collar f
  exact ⟨D, hnorm, fun z => by
    simpa only [one_smul] using hcollar z 1 (by norm_num)⟩

end DifferentialGeometry.Topology.Manifold

end

end
