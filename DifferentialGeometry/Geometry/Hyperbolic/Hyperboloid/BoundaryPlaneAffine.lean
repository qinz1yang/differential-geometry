import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.BoundaryPlaneMetric
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.Topology.Algebra.ConstMulAction

noncomputable section

namespace DifferentialGeometry.Hyperboloid

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem exists_stereographicComplex_similarity
    (e : Hyperboloid E3 ≃ᵢ Hyperboloid E3)
    (hn : boundaryHomeomorph e sphereNorthPole = sphereNorthPole) :
    let scale := (lorentzExtension e (1, (sphereNorthPole : E3))).1
    let H : ℂ → ℂ := fun z => stereographicComplex
      ⟨boundaryHomeomorph e (stereographicComplex.symm z).val, by
        intro hp
        exact (stereographicComplex.symm z).property
          ((boundaryHomeomorph e).injective (hp.trans hn.symm))⟩
    ∃ L : ℂ ≃ₗᵢ[ℝ] ℂ, ∀ z : ℂ, H z = scale • L z + H 0 := by
  let scale := (lorentzExtension e (1, (sphereNorthPole : E3))).1
  have hs : 0 < scale := lorentzExtension_sphere_time_pos e sphereNorthPole
  have hnonpole (ξ : Metric.sphere (0 : E3) 1) :
      ξ ≠ sphereNorthPole ↔ boundaryHomeomorph e ξ ≠ sphereNorthPole := by
    constructor
    · intro hξ hp
      exact hξ ((boundaryHomeomorph e).injective (hp.trans hn.symm))
    · intro hξ hp
      exact hξ (hp ▸ hn)
  let H : ℂ ≃ₜ ℂ := stereographicComplex.symm.trans
    (((boundaryHomeomorph e).subtype hnonpole).trans stereographicComplex)
  change ∃ L : ℂ ≃ₗᵢ[ℝ] ℂ, ∀ z : ℂ, H z = scale • L z + H 0
  have hH (z : ℂ) : H z = stereographicComplex
      ⟨boundaryHomeomorph e (stereographicComplex.symm z).val,
        (hnonpole _).mp (stereographicComplex.symm z).property⟩ := by
    change stereographicComplex (((boundaryHomeomorph e).subtype hnonpole)
      (stereographicComplex.symm z)) = _
    apply congrArg stereographicComplex
    apply Subtype.ext
    rfl
  have hmetric (z w : ℂ) : dist (H z) (H w) = scale * dist z w := by
    have hh := dist_stereographicComplex_boundaryHomeomorph e hn
      (stereographicComplex.symm z) (stereographicComplex.symm w)
    rw [hH z, hH w]
    simpa only [scale, stereographicComplex.apply_symm_apply] using hh
  let Uhome : ℂ ≃ₜ ℂ := H.trans (Homeomorph.smulOfNeZero (scale⁻¹ : ℝ) (inv_ne_zero hs.ne'))
  let U : ℂ ≃ᵢ ℂ :=
    { toEquiv := Uhome.toEquiv
      isometry_toFun := Isometry.of_dist_eq fun z w => by
        change dist (scale⁻¹ • H z) (scale⁻¹ • H w) = dist z w
        rw [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr hs), ← dist_eq_norm, hmetric,
          ← mul_assoc, inv_mul_cancel₀ hs.ne', one_mul] }
  let L := U.toRealLinearIsometryEquiv
  refine ⟨L, ?_⟩
  intro z
  have hL : L z = scale⁻¹ • H z - scale⁻¹ • H 0 :=
    U.toRealLinearIsometryEquiv_apply z
  have hm := congrArg (fun w : ℂ => scale • w) hL
  rw [smul_sub, smul_smul, smul_smul, mul_inv_cancel₀ hs.ne', one_smul, one_smul] at hm
  exact (sub_eq_iff_eq_add).mp hm.symm

end DifferentialGeometry.Hyperboloid
