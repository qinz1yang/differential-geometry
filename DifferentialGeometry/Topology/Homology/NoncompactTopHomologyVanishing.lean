import DifferentialGeometry.Topology.Homology.ChainSupportCompact
import DifferentialGeometry.Topology.Homology.SphereTopHomology
import DifferentialGeometry.Topology.Homology.SphereHomologyVanishing
import DifferentialGeometry.Topology.Homology.RadialHomotopy
import DifferentialGeometry.Topology.Homology.Homotopy
import DifferentialGeometry.Topology.FundamentalGroup.Sphere

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology ContinuousMap Set
open scoped Topology

universe u

namespace DifferentialGeometry.Topology

def integralCompactSupportZeroCocycles (X : Type u) [TopologicalSpace X] :
    Submodule ℤ (X → ℤ) where
  carrier := {f | IsLocallyConstant f ∧ ∃ K : Set X, IsCompact K ∧ ∀ x : X, x ∉ K → f x = 0}
  zero_mem' := ⟨IsLocallyConstant.const 0, ⟨∅, isCompact_empty, fun x _ => rfl⟩⟩
  add_mem' := by
    rintro f g ⟨hf, K, hKc, hK⟩ ⟨hg, L, hLc, hL⟩
    refine ⟨hf.add hg, K ∪ L, hKc.union hLc, fun x hx => ?_⟩
    have hxK : x ∉ K := fun h => hx (Or.inl h)
    have hxL : x ∉ L := fun h => hx (Or.inr h)
    rw [Pi.add_apply, hK x hxK, hL x hxL, add_zero]
  smul_mem' := by
    rintro c f ⟨hf, K, hKc, hK⟩
    have hsmul : (c • f : X → ℤ) = Function.const X c * f := by
      funext x
      simp [Pi.smul_apply, Pi.mul_apply]
    rw [hsmul]
    exact ⟨(IsLocallyConstant.const c).mul hf, K, hKc, fun x hx => by
      rw [Pi.mul_apply, hK x hx, mul_zero]⟩

theorem subsingleton_integralCompactSupportZeroCocycles (X : Type u) [TopologicalSpace X]
    [ConnectedSpace X] [NoncompactSpace X] :
    Subsingleton (integralCompactSupportZeroCocycles X) := by
  refine ⟨fun f g => ?_⟩
  have hmem : (f - g : X → ℤ) ∈ integralCompactSupportZeroCocycles X :=
    (integralCompactSupportZeroCocycles X).sub_mem f.2 g.2
  obtain ⟨hlc, K, hKc, hK⟩ := hmem
  have hfun : (f - g : X → ℤ) = 0 := by
    funext x
    let x₀ : X := Classical.choice (inferInstance : Nonempty X)
    have hconst : (f - g : X → ℤ) x = (f - g : X → ℤ) x₀ :=
      hlc.apply_eq_of_isPreconnected isPreconnected_univ (Set.mem_univ x) (Set.mem_univ x₀)
    have hnotCompact : ¬ CompactSpace X := not_compactSpace_iff.mpr inferInstance
    have hKne : K ≠ Set.univ := fun hKuniv =>
      hnotCompact (isCompact_univ_iff.mp (hKuniv ▸ hKc))
    obtain ⟨y, hy⟩ := (Set.ne_univ_iff_exists_notMem K).mp hKne
    have hconst_y : (f - g : X → ℤ) y = (f - g : X → ℤ) x₀ :=
      hlc.apply_eq_of_isPreconnected isPreconnected_univ (Set.mem_univ y) (Set.mem_univ x₀)
    calc (f - g : X → ℤ) x = (f - g : X → ℤ) x₀ := hconst
      _ = (f - g : X → ℤ) y := hconst_y.symm
      _ = 0 := hK y hy
  exact sub_eq_zero.mp (Subtype.ext hfun)

def noncompactPoincareDualityThreeZero (X : Type u) [TopologicalSpace X] : Prop :=
  Nonempty (integralSingularHomology 3 X ≃ₗ[ℤ] ↥(integralCompactSupportZeroCocycles X))

theorem subsingleton_integralSingularHomology_three_of_noncompactPoincareDualityThreeZero
    {X : Type u} [TopologicalSpace X] [ConnectedSpace X] [NoncompactSpace X]
    (h : noncompactPoincareDualityThreeZero X) :
    Subsingleton (integralSingularHomology 3 X) := by
  obtain ⟨e⟩ := h
  exact ⟨fun a b => e.injective
    (@Subsingleton.elim _ (subsingleton_integralCompactSupportZeroCocycles X) (e a) (e b))⟩

theorem noncompactPoincareDualityThreeZero_of_subsingleton (X : Type u) [TopologicalSpace X]
    [Subsingleton (integralSingularHomology 3 X)]
    [Subsingleton ↥(integralCompactSupportZeroCocycles X)] :
    noncompactPoincareDualityThreeZero X :=
  ⟨{ toFun := 0
     invFun := 0
     map_add' := fun a b => by simp
     map_smul' := fun c a => by simp
     left_inv := fun a => Subsingleton.elim _ _
     right_inv := fun a => Subsingleton.elim _ _ }⟩

theorem subsingleton_integralSingularHomology_three_euclideanThree :
    Subsingleton (integralSingularHomology 3 (EuclideanSpace ℝ (Fin 3))) :=
  integralSingularHomology_subsingleton_of_contractible 3 (by norm_num)
    (EuclideanSpace ℝ (Fin 3))

theorem noncompactPoincareDualityThreeZero_euclideanThree :
    noncompactPoincareDualityThreeZero (EuclideanSpace ℝ (Fin 3)) :=
  @noncompactPoincareDualityThreeZero_of_subsingleton (EuclideanSpace ℝ (Fin 3)) inferInstance
    (subsingleton_integralSingularHomology_three_euclideanThree)
    (subsingleton_integralCompactSupportZeroCocycles (EuclideanSpace ℝ (Fin 3)))

theorem subsingleton_integralSingularHomology_three_compl_origin_threeSpace :
    Subsingleton (integralSingularHomology 3 ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 3)))) := by
  exact ⟨fun a b => (integralPuncturedSpaceSphereHomologyEquiv
    (EuclideanSpace ℝ (Fin 3)) 3).injective
    (integralSphereHomology_subsingleton 2 3 (EuclideanSpace ℝ (Fin 3))
      (by simp) (by norm_num) (by norm_num) |>.allEq _ _)⟩

theorem not_subsingleton_integralSingularHomology_three_sphereThree :
    ¬ Subsingleton (integralSingularHomology 3 SphereThree) := by
  intro h
  let e := integralSphereTopHomologyEquiv 2 (EuclideanSpace ℝ (Fin 4)) (by simp)
  have hZ : Subsingleton ℤ :=
    ⟨fun a b => e.symm.injective (h.allEq (e.symm a) (e.symm b))⟩
  exact (zero_ne_one : (0 : ℤ) ≠ 1) (hZ.allEq 0 1)

theorem not_noncompactPoincareDualityThreeZero_sphereTwo :
    ¬ noncompactPoincareDualityThreeZero SphereTwo := by
  rintro ⟨e⟩
  have hH3 : Subsingleton (integralSingularHomology 3 SphereTwo) :=
    integralSphereHomology_subsingleton 2 3 (EuclideanSpace ℝ (Fin 3))
      (by simp) (by norm_num) (by norm_num)
  have hsub : Subsingleton ↥(integralCompactSupportZeroCocycles SphereTwo) :=
    ⟨fun a b => e.symm.injective (hH3.allEq (e.symm a) (e.symm b))⟩
  have hmem : (1 : SphereTwo → ℤ) ∈ integralCompactSupportZeroCocycles SphereTwo :=
    ⟨IsLocallyConstant.const 1,
      ⟨Set.univ, isCompact_univ_iff.mpr inferInstance, fun x hx => absurd hx (by simp)⟩⟩
  have hone : (1 : SphereTwo → ℤ) ≠ 0 := by
    intro hzero
    have hval := congrFun hzero (Classical.choice (inferInstance : Nonempty SphereTwo))
    exact one_ne_zero hval
  have hEq := hsub.allEq (⟨(1 : SphereTwo → ℤ), hmem⟩ :
    ↥(integralCompactSupportZeroCocycles SphereTwo)) 0
  exact hone (congrArg Subtype.val hEq)

end DifferentialGeometry.Topology
