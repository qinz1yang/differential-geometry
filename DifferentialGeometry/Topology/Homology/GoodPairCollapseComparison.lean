import DifferentialGeometry.Topology.Homology.RelativeReducedCollapse
import DifferentialGeometry.Topology.Homology.RelativeHomeomorphism
import DifferentialGeometry.Topology.Homology.GoodPairQuotientIsomorphism

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology ContinuousMap Set

open scoped Topology

namespace DifferentialGeometry.Topology

variable {P Q R : Type} [TopologicalSpace P] [TopologicalSpace Q] [TopologicalSpace R]
  {X : Type} [TopologicalSpace X]

theorem integralRelativeHomologyMap_congr {n : ℕ} {A : Set P} {B : Set Q} {f g : C(P, Q)}
    (h : f = g) (hf : MapsTo f A B) (hg : MapsTo g A B) :
    integralRelativeHomologyMap n f hf = integralRelativeHomologyMap n g hg := by
  subst h
  exact congrArg (fun k => integralRelativeHomologyMap n f k) (Subsingleton.elim hf hg)

theorem integralRelativeReducedEquiv_apply_absoluteToRelative {B : Set Q} (m : ℕ) (hm : 0 < m)
    (hB : B.Subsingleton) (hne : B.Nonempty) (z : integralSingularHomology (m + 1) Q) :
    integralRelativeReducedEquiv m hm hB hne (integralAbsoluteToRelative (m + 1) B z) =
      integralReducedSingularHomologyEquiv m Q z := by
  unfold integralRelativeReducedEquiv
  rw [LinearEquiv.trans_apply]
  exact congrArg (integralReducedSingularHomologyEquiv m Q)
    (LinearEquiv.symm_apply_apply _ z)

theorem integralRelativeReducedEquiv_natural {B : Set Q} {C : Set R} (m : ℕ) (hm : 0 < m)
    (g : C(Q, R)) (hg : MapsTo g B C) (hB : B.Subsingleton) (hne : B.Nonempty)
    (hC : C.Subsingleton) (hneC : C.Nonempty) (y : integralRelativeHomology (m + 1) B) :
    (DifferentialGeometry.Homology.reducedSingularHomologyMap (ModuleCat.of ℤ ℤ)
        (TopCat.ofHom g) (m + 1)).hom (integralRelativeReducedEquiv m hm hB hne y) =
      integralRelativeReducedEquiv m hm hC hneC (integralRelativeHomologyMap (m + 1) g hg y) := by
  obtain ⟨z, hz⟩ := (LinearEquiv.ofBijective (integralAbsoluteToRelative (m + 1) B)
    (integralAbsoluteToRelative_bijective_of_subsingleton hB hne (by omega))).surjective y
  have hz' : integralAbsoluteToRelative (m + 1) B z = y := hz
  rw [← hz']
  have hnat : integralAbsoluteToRelative (m + 1) C (integralSingularHomologyMap (m + 1) g z) =
      integralRelativeHomologyMap (m + 1) g hg (integralAbsoluteToRelative (m + 1) B z) :=
    LinearMap.congr_fun (integralAbsoluteToRelative_natural (m + 1) g hg) z
  rw [integralRelativeReducedEquiv_apply_absoluteToRelative m hm hB hne z, ← hnat,
    integralRelativeReducedEquiv_apply_absoluteToRelative m hm hC hneC]
  exact integralReducedSingularHomologyEquiv_naturality m g z

theorem integralRelativeReducedComparison_natural {A : Set P} {B : Set Q} {C : Set R}
    (m : ℕ) (hm : 0 < m) (f : C(P, Q)) (hf : MapsTo f A B) (hB : B.Subsingleton)
    (hne : B.Nonempty) (g : C(Q, R)) (hg : MapsTo g B C) (hC : C.Subsingleton)
    (hneC : C.Nonempty) :
    integralRelativeReducedComparison m hm (g.comp f) (hg.comp hf) hC hneC =
      (DifferentialGeometry.Homology.reducedSingularHomologyMap (ModuleCat.of ℤ ℤ)
        (TopCat.ofHom g) (m + 1)).hom.comp
        (integralRelativeReducedComparison m hm f hf hB hne) := by
  refine LinearMap.ext fun y => ?_
  unfold integralRelativeReducedComparison
  simp only [LinearMap.comp_apply]
  rw [integralRelativeHomologyMap_comp, LinearMap.comp_apply]
  exact (integralRelativeReducedEquiv_natural m hm g hg hB hne hC hneC
    (integralRelativeHomologyMap (m + 1) f hf y)).symm

theorem collapseRelativeComparison_bijective_of_subsingleton {A : Set X} (hA : A.Subsingleton)
    (n : ℕ) : Function.Bijective (collapseRelativeComparison n A) := by
  have hq : IsHomeomorph fun x => collapseMap A x := isHomeomorph_collapseMap_of_subsingleton hA
  let e : X ≃ₜ collapseSpace A := IsHomeomorph.homeomorph (fun x => collapseMap A x) hq
  have he' : MapsTo e.symm (collapseMap A '' A) A := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' : e.symm ((collapseMap A) x) = x := by
      change e.symm (e x) = x
      exact e.symm_apply_apply x
    rw [hx']
    exact hx
  have hiso : Function.Bijective (integralRelativeHomologyMap n
      (⟨e, e.continuous⟩ : C(X, collapseSpace A)) (collapseMap_mapsTo A)) := by
    have h := ConcreteCategory.bijective_of_isIso
      (integralRelativeHomologyHomeomorphIso n e A (collapseMap A '' A)
        (collapseMap_mapsTo A) he').hom
    change Function.Bijective (integralRelativeHomologyMap n
      (⟨e, e.continuous⟩ : C(X, collapseSpace A)) (collapseMap_mapsTo A)) at h
    exact h
  have hmap : collapseRelativeComparison n A = integralRelativeHomologyMap n
      (⟨e, e.continuous⟩ : C(X, collapseSpace A)) (collapseMap_mapsTo A) := by
    unfold collapseRelativeComparison
    exact integralRelativeHomologyMap_congr (h := by ext x; rfl) _ _
  rwa [← hmap] at hiso

theorem collapseRelativeComparisonQuasiIso_of_subsingleton {A : Set X} (hA : A.Subsingleton) :
    CollapseComparisonQuasiIso A :=
  fun n => collapseRelativeComparison_bijective_of_subsingleton hA n

theorem collapseReducedComparison_bijective_of_subsingleton {A : Set X} (hA : A.Subsingleton)
    (hne : A.Nonempty) (m : ℕ) (hm : 0 < m) :
    Function.Bijective (collapseReducedComparison m hm A hne) :=
  (bijective_collapseReducedComparison_iff m hm A hne).mpr
    (collapseRelativeComparison_bijective_of_subsingleton hA (m + 1))

theorem not_eq_zero_collapseReducedComparison_liftedSphere
    (b : liftedHomotopySphere.{0} 1) :
    collapseReducedComparison 1 (by norm_num) ({b} : Set (liftedHomotopySphere.{0} 1))
      (singleton_nonempty b) ≠ 0 := by
  intro hzero
  refine not_subsingleton_integralRelativeHomology_singleton_liftedSphere b ⟨fun x y => ?_⟩
  exact (collapseReducedComparison_bijective_of_subsingleton
    (subsingleton_singleton (a := b)) (singleton_nonempty b) 1 (by norm_num)).1 (by
      rw [hzero]
      rfl)

end DifferentialGeometry.Topology
