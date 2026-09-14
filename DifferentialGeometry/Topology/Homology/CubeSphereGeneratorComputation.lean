import DifferentialGeometry.Topology.Homology.CubeSphereMayerVietorisAlignment
import DifferentialGeometry.Topology.Homology.SphereGeneratorCriterion

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology ContinuousMap Set Module
open scoped Topology

universe u

namespace DifferentialGeometry.Topology

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology



private theorem intLinearEquiv_apply_eq_mul (e : ℤ ≃ₗ[ℤ] ℤ) (z : ℤ) :
    e z = z * e 1 := by
  have h : z • (1 : ℤ) = z := by simp
  calc e z = e (z • (1 : ℤ)) := by rw [h]
    _ = z • e 1 := map_zsmul e z 1
    _ = z * e 1 := smul_eq_mul z (e 1)



private theorem intLinearEquiv_apply_one_eq_or_eq_neg (e : ℤ ≃ₗ[ℤ] ℤ) :
    e 1 = 1 ∨ e 1 = -1 := by
  obtain ⟨y, hy⟩ := e.surjective 1
  have hy1 : y * e 1 = 1 := by rw [← intLinearEquiv_apply_eq_mul e y, hy]
  exact Int.eq_one_or_neg_one_of_mul_eq_one (by rw [mul_comm]; exact hy1)



private theorem intLinearEquiv_apply_eq_or_eq_neg (e : ℤ ≃ₗ[ℤ] ℤ) (z : ℤ) :
    e z = z ∨ e z = -z := by
  rw [intLinearEquiv_apply_eq_mul]
  rcases intLinearEquiv_apply_one_eq_or_eq_neg e with h | h
  · rw [h, mul_one]
    exact Or.inl rfl
  · rw [h, mul_neg, mul_one]
    exact Or.inr rfl



private theorem not_exists_intLinearEquiv_apply_three_eq_one :
    ¬ ∃ e : ℤ ≃ₗ[ℤ] ℤ, e (3 : ℤ) = 1 := by
  rintro ⟨e, he⟩
  rcases intLinearEquiv_apply_eq_or_eq_neg e 3 with h | h <;> rw [h] at he <;> norm_num at he



private theorem apply_eq_or_apply_eq_neg_of_linearEquiv {M : Type*} [AddCommGroup M]
    [Module ℤ M] {N : Type*} [AddCommGroup N] [Module ℤ N]
    (e₁ : M ≃ₗ[ℤ] ℤ) (e₂ : N ≃ₗ[ℤ] ℤ) (τ : M ≃ₗ[ℤ] N) (x : M) :
    e₂ (τ x) = e₁ x ∨ e₂ (τ x) = - e₁ x := by
  have hcoe : (e₁.symm.trans (τ.trans e₂)) (e₁ x) = e₂ (τ x) := by
    rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  rw [← hcoe]
  exact intLinearEquiv_apply_eq_or_eq_neg _ _



private theorem exists_linearEquiv_iff_coordinate {M : Type*} [AddCommGroup M] [Module ℤ M]
    {N : Type*} [AddCommGroup N] [Module ℤ N]
    (e₁ : M ≃ₗ[ℤ] ℤ) (e₂ : N ≃ₗ[ℤ] ℤ) (u : M) (s : N) :
    (∃ τ : M ≃ₗ[ℤ] N, τ u = s ∨ τ u = -s) ↔
      e₁ u = e₂ s ∨ e₁ u = - e₂ s := by
  constructor
  · rintro ⟨τ, hτ | hτ⟩
    · have h := apply_eq_or_apply_eq_neg_of_linearEquiv e₁ e₂ τ u
      simp only [hτ] at h
      rcases h with h | h
      · exact Or.inl h.symm
      · exact Or.inr (by simpa using (congrArg Neg.neg h).symm)
    · have h := apply_eq_or_apply_eq_neg_of_linearEquiv e₁ e₂ τ u
      simp only [hτ, map_neg] at h
      rcases h with h | h
      · exact Or.inr h.symm
      · exact Or.inl (neg_inj.mp h).symm
  · rintro (h | h)
    · exact ⟨e₁.trans e₂.symm, Or.inl (by
        rw [LinearEquiv.trans_apply, h, LinearEquiv.symm_apply_apply])⟩
    · exact ⟨e₁.trans e₂.symm, Or.inr (by
        rw [LinearEquiv.trans_apply, h, map_neg, LinearEquiv.symm_apply_apply])⟩



def HasCubeSquareAlignment : Prop :=
  ∃ τ : CubeSphereMayerVietorisSource.{u} ≃ₗ[ℤ]
      integralSingularHomology 2 (liftedHomotopySphere.{u} 1),
    τ (hurewiczCubeClass cubeSphereUnliftedLoop.{u}) = squareSphereFundamentalClass.{u} ∨
      τ (hurewiczCubeClass cubeSphereUnliftedLoop.{u}) =
        -squareSphereFundamentalClass.{u}



abbrev cubeSphereUnliftedCollapseCoordinate : ℤ :=
  integralSphereTopHomologyEquiv 2 (liftedSphereSpace.{u} 2) (liftedSphereSpace_finrank 2)
    (hurewiczCubeClass cubeSphereUnliftedLoop.{u})



abbrev squareSphereCollapseCoordinate : ℤ :=
  integralLiftedSphereTopEquiv.{u} 1 squareSphereFundamentalClass.{u}



abbrev CubeSphereCollapseIsGenerator : Prop :=
  IsSphereHomologyGenerator.{u} 2 cubeSphereFundamentalClass.{u}



abbrev SquareSphereCollapseIsGenerator : Prop :=
  IsSphereHomologyGenerator.{u} 1 squareSphereFundamentalClass.{u}



theorem hasCubeSquareAlignment_iff_exists_canonical_alignment :
    HasCubeSquareAlignment.{u} ↔
      ∃ τ : CubeSphereMayerVietorisSource.{u} ≃ₗ[ℤ]
          integralSingularHomology 2 (liftedHomotopySphere.{u} 1),
        integralSphereHomologyShiftEquiv_cubeSphereFundamentalClass
          (LinearEquiv.refl ℤ CubeSphereMayerVietorisSource.{u}) τ :=
  Iff.rfl



theorem hasCubeSquareAlignment_of_integralSphereHomologyShiftEquiv_cubeSphereFundamentalClass
    {B : Type u} [AddCommGroup B] [Module ℤ B]
    (f : CubeSphereMayerVietorisSource.{u} ≃ₗ[ℤ] B)
    (τ : B ≃ₗ[ℤ] integralSingularHomology 2 (liftedHomotopySphere.{u} 1))
    (halign : integralSphereHomologyShiftEquiv_cubeSphereFundamentalClass f τ) :
    HasCubeSquareAlignment.{u} :=
  ⟨f.trans τ, halign⟩



theorem hasCubeSquareAlignment_iff_coordinate :
    HasCubeSquareAlignment.{u} ↔
      cubeSphereUnliftedCollapseCoordinate.{u} = squareSphereCollapseCoordinate.{u} ∨
        cubeSphereUnliftedCollapseCoordinate.{u} = -squareSphereCollapseCoordinate.{u} :=
  exists_linearEquiv_iff_coordinate
    (integralSphereTopHomologyEquiv 2 (liftedSphereSpace.{u} 2) (liftedSphereSpace_finrank 2))
    (integralLiftedSphereTopEquiv.{u} 1)
    (hurewiczCubeClass cubeSphereUnliftedLoop.{u}) squareSphereFundamentalClass.{u}



theorem hasCubeSquareAlignment_iff_liftedSphereTopEquiv :
    HasCubeSquareAlignment.{u} ↔
      integralLiftedSphereTopEquiv.{u} 2 cubeSphereFundamentalClass.{u} =
          integralLiftedSphereTopEquiv.{u} 1 squareSphereFundamentalClass.{u} ∨
        integralLiftedSphereTopEquiv.{u} 2 cubeSphereFundamentalClass.{u} =
          - integralLiftedSphereTopEquiv.{u} 1 squareSphereFundamentalClass.{u} := by
  rw [hasCubeSquareAlignment_iff_coordinate, cubeSphereUnliftedCollapseCoordinate,
    squareSphereCollapseCoordinate, ← integralLiftedSphereTopEquiv_cubeSphereFundamentalClass]



theorem
    cubeSphereCollapseIsGenerator_iff_squareSphereCollapseIsGenerator_of_cubeSquareAlignment
    (halign : HasCubeSquareAlignment.{u}) :
    CubeSphereCollapseIsGenerator.{u} ↔ SquareSphereCollapseIsGenerator.{u} :=
  isSphereHomologyGenerator_cubeSphereFundamentalClass_iff_squareSphereFundamentalClass
    (LinearEquiv.refl ℤ CubeSphereMayerVietorisSource.{u})
    (integralSphereTopHomologyEquiv 2 (liftedSphereSpace.{u} 2) (liftedSphereSpace_finrank 2))
    halign.choose halign.choose_spec



theorem cubeSphereCollapseIsGenerator_of_cubeSquareAlignment_and_squareSphereCollapseIsGenerator
    (halign : HasCubeSquareAlignment.{u})
    (hsq : SquareSphereCollapseIsGenerator.{u}) :
    CubeSphereCollapseIsGenerator.{u} :=
  (cubeSphereCollapseIsGenerator_iff_squareSphereCollapseIsGenerator_of_cubeSquareAlignment
    halign).mpr hsq



theorem squareSphereCollapseIsGenerator_of_cubeSquareAlignment_and_cubeSphereCollapseIsGenerator
    (halign : HasCubeSquareAlignment.{u})
    (hc : CubeSphereCollapseIsGenerator.{u}) :
    SquareSphereCollapseIsGenerator.{u} :=
  (cubeSphereCollapseIsGenerator_iff_squareSphereCollapseIsGenerator_of_cubeSquareAlignment
    halign).mp hc



theorem hasCubeSquareAlignment_of_cubeSphereCollapseIsGenerator_and_squareSphereCollapseIsGenerator
    (hc : CubeSphereCollapseIsGenerator.{u})
    (hsq : SquareSphereCollapseIsGenerator.{u}) :
    HasCubeSquareAlignment.{u} := by
  rw [hasCubeSquareAlignment_iff_liftedSphereTopEquiv]
  rcases isSphereHomologyGenerator_cubeSphereFundamentalClass_iff_coordinate.mp hc with h | h <;>
    rcases isSphereHomologyGenerator_squareSphereFundamentalClass_iff_coordinate.mp hsq
      with h' | h' <;>
    omega



theorem not_forall_exists_linearEquiv_apply_eq_one_of_exists_linearEquiv_apply_eq_one :
    ¬ ∀ (M : Type) [AddCommGroup M] [Module ℤ M] (N : Type) [AddCommGroup N] [Module ℤ N]
        (u : M) (s : N),
      (∃ e : N ≃ₗ[ℤ] ℤ, e s = 1) → ∃ e : M ≃ₗ[ℤ] ℤ, e u = 1 := by
  intro h
  have h3 : ∃ e : ℤ ≃ₗ[ℤ] ℤ, e (3 : ℤ) = 1 :=
    h ℤ ℤ 3 1 ⟨LinearEquiv.refl ℤ ℤ, rfl⟩
  exact not_exists_intLinearEquiv_apply_three_eq_one h3



theorem
    not_forall_exists_linearEquiv_apply_eq_one_of_exists_linearEquiv_apply_eq_or_eq_neg :
    ¬ ∀ (M : Type) [AddCommGroup M] [Module ℤ M] (N : Type) [AddCommGroup N] [Module ℤ N]
        (u : M) (s : N),
      (∃ τ : M ≃ₗ[ℤ] N, τ u = s ∨ τ u = -s) →
        ∃ e : M ≃ₗ[ℤ] ℤ, e u = 1 := by
  intro h
  have h3 : ∃ e : ℤ ≃ₗ[ℤ] ℤ, e (3 : ℤ) = 1 :=
    h ℤ ℤ 3 3 ⟨LinearEquiv.refl ℤ ℤ, Or.inl rfl⟩
  exact not_exists_intLinearEquiv_apply_three_eq_one h3



theorem
    not_forall_exists_linearEquiv_apply_eq_or_eq_neg_of_exists_linearEquiv_apply_eq_one :
    ¬ ∀ (M : Type) [AddCommGroup M] [Module ℤ M] (N : Type) [AddCommGroup N] [Module ℤ N]
        (u : M) (s : N),
      (∃ e : M ≃ₗ[ℤ] ℤ, e u = 1) →
        ∃ τ : M ≃ₗ[ℤ] N, τ u = s ∨ τ u = -s := by
  intro h
  obtain ⟨τ, hτ⟩ := h ℤ ℤ 1 3 ⟨LinearEquiv.refl ℤ ℤ, rfl⟩
  rcases hτ with hτ | hτ <;>
    rcases intLinearEquiv_apply_eq_or_eq_neg τ 1 with h' | h' <;>
    rw [h'] at hτ <;> norm_num at hτ

end DifferentialGeometry.Topology
