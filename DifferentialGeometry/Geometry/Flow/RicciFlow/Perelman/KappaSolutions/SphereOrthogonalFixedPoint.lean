import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CylinderDeckAlgebra
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

local notation "SphereAmbient" => EuclideanSpace ℝ (Fin 3)
local notation "SphereTwo" => Metric.sphere (0 : SphereAmbient) 1
local notation "OrthogonalThree" => SphereAmbient ≃ₗᵢ[ℝ] SphereAmbient

theorem sphereOrthogonal_exists_nonzero_square_fixed (A : OrthogonalThree) :
    ∃ v : SphereAmbient, v ≠ 0 ∧ A (A v) = v := by
  classical
  let L : SphereAmbient →ₗ[ℝ] SphereAmbient := A.toLinearMap - A.symm.toLinearMap
  have hadj : LinearMap.adjoint L = -L := by
    simp only [L, map_sub, LinearIsometryEquiv.adjoint_toLinearMap_eq_symm,
      LinearIsometryEquiv.symm_symm, neg_sub]
  let b := EuclideanSpace.basisFun (Fin 3) ℝ
  let B : Matrix (Fin 3) (Fin 3) ℝ := LinearMap.toMatrix b.toBasis b.toBasis L
  have htranspose : B.transpose = -B := by
    have ht := LinearMap.toMatrix_adjoint b b L
    rw [hadj, map_neg] at ht
    simpa only [B, Matrix.conjTranspose_eq_transpose_of_trivial] using ht.symm
  have hdet := congrArg Matrix.det htranspose
  rw [Matrix.det_transpose, Matrix.det_neg] at hdet
  norm_num at hdet
  have hzero : Matrix.det B = 0 := by linarith
  have hdetL : LinearMap.det L = 0 :=
    (LinearMap.det_toMatrix b.toBasis L).symm.trans hzero
  have hker : LinearMap.ker L ≠ ⊥ :=
    LinearMap.det_eq_zero_iff_ker_ne_bot.mp hdetL
  obtain ⟨v, hvker, hv⟩ := (LinearMap.ker L).ne_bot_iff.mp hker
  have hLv : L v = 0 := hvker
  change A v - A.symm v = 0 at hLv
  have hAv : A v = A.symm v := sub_eq_zero.mp hLv
  refine ⟨v, hv, ?_⟩
  rw [hAv, A.apply_symm_apply]

theorem sphereOrthogonal_square_has_fixed_point (A : OrthogonalThree) :
    ∃ y : SphereTwo, A (A (y : SphereAmbient)) = (y : SphereAmbient) := by
  obtain ⟨v, hv, hfixed⟩ := sphereOrthogonal_exists_nonzero_square_fixed A
  have hnorm : ‖(‖v‖⁻¹ : ℝ) • v‖ = 1 := norm_smul_inv_norm hv
  let y : SphereTwo := ⟨(‖v‖⁻¹ : ℝ) • v, by
    simpa only [Metric.mem_sphere, dist_zero_right] using hnorm⟩
  refine ⟨y, ?_⟩
  change A (A ((‖v‖⁻¹ : ℝ) • v)) = (‖v‖⁻¹ : ℝ) • v
  simp only [map_smul, hfixed]

theorem sphereOrthogonal_square_eq_one_of_mem_free_subgroup
    (G : Subgroup OrthogonalThree)
    (hfree : ∀ A : OrthogonalThree, A ∈ G → A ≠ 1 →
      ∀ y : SphereTwo, A (y : SphereAmbient) ≠ (y : SphereAmbient))
    (A : OrthogonalThree) (hA : A ∈ G) : A * A = 1 := by
  by_contra hne
  obtain ⟨y, hy⟩ := sphereOrthogonal_square_has_fixed_point A
  apply hfree (A * A) (G.mul_mem hA hA) hne y
  exact hy

theorem sphereOrthogonal_eq_one_or_neg_of_mem_free_subgroup
    (G : Subgroup OrthogonalThree)
    (hfree : ∀ A : OrthogonalThree, A ∈ G → A ≠ 1 →
      ∀ y : SphereTwo, A (y : SphereAmbient) ≠ (y : SphereAmbient))
    (A : OrthogonalThree) (hA : A ∈ G) :
    A = 1 ∨ A = LinearIsometryEquiv.neg ℝ := by
  classical
  by_cases hne : A = 1
  · exact Or.inl hne
  right
  have hsquare := sphereOrthogonal_square_eq_one_of_mem_free_subgroup G hfree A hA
  have hinvolution : Function.Involutive (A : SphereAmbient → SphereAmbient) := by
    intro v
    exact congrArg (fun B : OrthogonalThree => B v) hsquare
  exact cylinderDeck_involution_eq_neg_of_sphere_free A hinvolution (hfree A hA hne)

theorem sphereOrthogonal_free_subgroup_eq_bot_or_antipodal
    (G : Subgroup OrthogonalThree)
    (hfree : ∀ A : OrthogonalThree, A ∈ G → A ≠ 1 →
      ∀ y : SphereTwo, A (y : SphereAmbient) ≠ (y : SphereAmbient)) :
    G = ⊥ ∨ G = Subgroup.zpowers (LinearIsometryEquiv.neg ℝ : OrthogonalThree) := by
  classical
  by_cases hneg : (LinearIsometryEquiv.neg ℝ : OrthogonalThree) ∈ G
  · right
    apply le_antisymm
    · intro A hA
      rcases sphereOrthogonal_eq_one_or_neg_of_mem_free_subgroup G hfree A hA with
        h | h
      · rw [h]
        exact Subgroup.one_mem _
      · rw [h]
        exact Subgroup.mem_zpowers _
    · exact Subgroup.zpowers_le.mpr hneg
  · left
    apply (Subgroup.eq_bot_iff_forall G).mpr
    intro A hA
    rcases sphereOrthogonal_eq_one_or_neg_of_mem_free_subgroup G hfree A hA with
      h | h
    · exact h
    · exact False.elim (hneg (h ▸ hA))

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
