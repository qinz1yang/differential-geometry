import DifferentialGeometry.Geometry.Metric.RadialField
import DifferentialGeometry.Bundle.TangentSpace
import DifferentialGeometry.Geometry.Metric.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Basis.SMul

noncomputable section
open DifferentialGeometry Set
open scoped Manifold InnerProductSpace
namespace DifferentialGeometry.Geometry.Riemannian
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

theorem exists_radial_orthonormalBasis {x : E3} (hx : x ≠ 0) :
    ∃ b : OrthonormalBasis (Fin 3) ℝ E3, b 0 = NormedSpace.normalize x := by
  have hON : Orthonormal ℝ (({0} : Set (Fin 3)).domRestrict
      (fun _ : Fin 3 => NormedSpace.normalize x)) := by
    rw [orthonormal_iff_ite]
    intro i j
    have hij : i = j := Subtype.ext (i.property.trans j.property.symm)
    simp only [hij, ↓reduceIte, Set.domRestrict_apply, real_inner_self_eq_norm_sq,
      NormedSpace.norm_normalize hx, one_pow]
  obtain ⟨b, hb⟩ := hON.exists_orthonormalBasis_extension_of_card_eq
    (by simp : Module.finrank ℝ E3 = Fintype.card (Fin 3))
  exact ⟨b, hb 0 (by simp)⟩

def radialMetricBasis (a : ℝ → ℝ) {x : E3} (hx : x ≠ 0) (hane : a ‖x‖ ≠ 0)
    (b : OrthonormalBasis (Fin 3) ℝ E3) : Module.Basis (Fin 3) ℝ (TangentSpace 𝓘(ℝ, E3) x) :=
  (b.toBasis.isUnitSMul (w := fun i : Fin 3 => if i = 0 then 1 else ‖x‖ / a ‖x‖)
    (fun i => by
      split_ifs
      · exact isUnit_one
      · exact isUnit_iff_ne_zero.mpr (div_ne_zero (norm_ne_zero_iff.mpr hx) hane))).map
    (tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E3)) x).symm.toLinearEquiv

theorem radialMetricBasis_apply (a : ℝ → ℝ) {x : E3} (hx : x ≠ 0) (hane : a ‖x‖ ≠ 0)
    (b : OrthonormalBasis (Fin 3) ℝ E3) (i : Fin 3) :
    radialMetricBasis a hx hane b i =
      (tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E3)) x).symm
        ((if i = 0 then 1 else ‖x‖ / a ‖x‖) • b i) := by
  simp only [radialMetricBasis, Module.Basis.map_apply, Module.Basis.isUnitSMul_apply,
    OrthonormalBasis.coe_toBasis, ContinuousLinearEquiv.coe_toLinearEquiv]

theorem radialMetricBasis_zero (a : ℝ → ℝ) {x : E3} (hx : x ≠ 0) (hane : a ‖x‖ ≠ 0)
    (b : OrthonormalBasis (Fin 3) ℝ E3) (hb : b 0 = NormedSpace.normalize x) :
    radialMetricBasis a hx hane b 0 =
      (tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E3)) x).symm
        (NormedSpace.normalize x) := by
  simp only [radialMetricBasis_apply, ↓reduceIte, one_smul, hb]

theorem radialMetricBasis_of_ne_zero (a : ℝ → ℝ) {x : E3} (hx : x ≠ 0)
    (hane : a ‖x‖ ≠ 0) (b : OrthonormalBasis (Fin 3) ℝ E3) {i : Fin 3} (hi : i ≠ 0) :
    radialMetricBasis a hx hane b i =
      (tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E3)) x).symm
        ((‖x‖ / a ‖x‖) • b i) := by
  simp only [radialMetricBasis_apply, hi, ↓reduceIte]

theorem inner_radial_orthonormalBasis {x : E3}
    (b : OrthonormalBasis (Fin 3) ℝ E3) (hb : b 0 = NormedSpace.normalize x) (i : Fin 3) :
    ⟪x, b i⟫_ℝ = if i = 0 then ‖x‖ else 0 := by
  calc
    ⟪x, b i⟫_ℝ = ‖x‖ * ⟪b 0, b i⟫_ℝ := by
      nth_rw 1 [← NormedSpace.norm_smul_normalize x]
      rw [← hb, real_inner_smul_left]
    _ = if i = 0 then ‖x‖ else 0 := by
      rw [b.inner_eq_ite]
      by_cases hi : i = 0 <;> simp [hi, eq_comm]

theorem metric_inner_radialMetricBasis
    (g : SmoothRiemannianMetric 𝓘(ℝ, E3) E3) {a : ℝ → ℝ} {x : E3}
    (hg : tangentBilinearFormToModel x (g.inner x) = radialBilinearField a x)
    (hx : x ≠ 0) (hane : a ‖x‖ ≠ 0) (b : OrthonormalBasis (Fin 3) ℝ E3)
    (hb : b 0 = NormedSpace.normalize x) (i j : Fin 3) :
    g.inner x (radialMetricBasis a hx hane b i) (radialMetricBasis a hx hane b j) =
      if i = j then 1 else 0 := by
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  rw [radialMetricBasis_apply, radialMetricBasis_apply,
    ← tangentBilinearFormToModel_apply, hg, radialBilinearField_apply]
  simp only [real_inner_smul_left, real_inner_smul_right, b.inner_eq_ite,
    inner_radial_orthonormalBasis b hb]
  by_cases hi : i = 0 <;> by_cases hj : j = 0
  · subst i
    subst j
    simp [hn]
  · subst i
    simp [hj, hn, Ne.symm hj]
  · subst j
    simp [hi, hn]
  · by_cases hij : i = j
    · simp only [hj, hij, ↓reduceIte, mul_one, mul_zero, zero_div, add_zero]
      field_simp
    · simp [hi, hj, hij]

end DifferentialGeometry.Geometry.Riemannian
