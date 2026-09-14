import DifferentialGeometry.Topology.Homology.CollapseQuotientComparison

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology ContinuousMap Set Module
open scoped Topology

universe u

namespace DifferentialGeometry.Topology

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

def collapseSetoid (A : Set X) : Setoid X where
  r x y := x = y ∨ (x ∈ A ∧ y ∈ A)
  iseqv := ⟨fun x => Or.inl rfl,
    fun h => h.elim (fun h => Or.inl h.symm) (fun h => Or.inr ⟨h.2, h.1⟩),
    fun h1 h2 => by
      rcases h1 with rfl | ⟨hx, hy⟩
      · exact h2
      · rcases h2 with rfl | ⟨_, hz⟩
        · exact Or.inr ⟨hx, hy⟩
        · exact Or.inr ⟨hx, hz⟩⟩

abbrev collapseSpace (A : Set X) : Type u := Quotient (collapseSetoid A)

def collapseMap (A : Set X) : C(X, collapseSpace A) :=
  ⟨@Quotient.mk' X (collapseSetoid A), continuous_quotient_mk'⟩

theorem collapseMap_eq_of_mem {A : Set X} {x y : X} (hx : x ∈ A) (hy : y ∈ A) :
    collapseMap A x = collapseMap A y :=
  Quotient.sound (Or.inr ⟨hx, hy⟩)

theorem collapseMap_mapsTo (A : Set X) : MapsTo (collapseMap A) A (collapseMap A '' A) :=
  fun x hx => ⟨x, hx, rfl⟩

theorem collapseMap_image_subsingleton (A : Set X) : (collapseMap A '' A).Subsingleton := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  exact collapseMap_eq_of_mem hx hy

theorem collapseMap_image_nonempty {A : Set X} (hA : A.Nonempty) :
    (collapseMap A '' A).Nonempty :=
  hA.image (collapseMap A)

theorem collapseMap_image_eq_singleton {A : Set X} {a : X} (ha : a ∈ A) :
    collapseMap A '' A = {collapseMap A a} :=
  (collapseMap_image_subsingleton A).eq_singleton_of_mem ⟨a, ha, rfl⟩

theorem collapseMap_image_empty :
    collapseMap (∅ : Set X) '' ∅ = (∅ : Set (collapseSpace (∅ : Set X))) :=
  image_empty _

theorem not_nonempty_collapseMap_image_empty :
    ¬ (collapseMap (∅ : Set X) '' ∅).Nonempty := by
  rw [collapseMap_image_empty]
  rintro ⟨x, hx⟩
  exact hx

theorem collapseMap_injective_of_subsingleton {A : Set X} (hA : A.Subsingleton) :
    Function.Injective (collapseMap A) := by
  intro x y hxy
  rcases Quotient.exact hxy with h | ⟨hx, hy⟩
  · exact h
  · exact hA hx hy

theorem not_injective_collapseMap_of_exists_ne {A : Set X} {x y : X} (hx : x ∈ A) (hy : y ∈ A)
    (hxy : x ≠ y) : ¬ Function.Injective (collapseMap A) :=
  fun h => hxy (h (collapseMap_eq_of_mem hx hy))

theorem isQuotientMap_collapseMap (A : Set X) : Topology.IsQuotientMap fun x => collapseMap A x :=
  isQuotientMap_quotient_mk'

theorem isHomeomorph_collapseMap_of_subsingleton {A : Set X} (hA : A.Subsingleton) :
    IsHomeomorph fun x => collapseMap A x :=
  isHomeomorph_iff_isQuotientMap_injective.mpr
    ⟨isQuotientMap_collapseMap A, collapseMap_injective_of_subsingleton hA⟩

theorem integralAbsoluteToRelative_bijective_of_subsingleton {A : Set X} (hA : A.Subsingleton)
    (hne : A.Nonempty) {n : ℕ} (hn : 1 < n) :
    Function.Bijective (integralAbsoluteToRelative n A) := by
  obtain ⟨b, hb⟩ := hne
  have h : A = {b} := hA.eq_singleton_of_mem hb
  subst h
  exact integralAbsoluteToRelative_singleton_bijective b hn

def collapseRelativeChains (A : Set X) :
    integralRelativeChains A ⟶ integralRelativeChains (collapseMap A '' A) :=
  integralRelativeChainMap (collapseMap A) (collapseMap_mapsTo A)

def collapseRelativeComparison (n : ℕ) (A : Set X) :
    integralRelativeHomology n A →ₗ[ℤ] integralRelativeHomology n (collapseMap A '' A) :=
  integralRelativeHomologyMap n (collapseMap A) (collapseMap_mapsTo A)

def CollapseComparisonQuasiIso (A : Set X) : Prop :=
  ∀ n, Function.Bijective (collapseRelativeComparison n A)

theorem collapseRelativeComparison_absoluteToRelative (n : ℕ) (A : Set X) :
    (integralAbsoluteToRelative n (collapseMap A '' A)).comp
        (integralSingularHomologyMap n (collapseMap A)) =
      (collapseRelativeComparison n A).comp (integralAbsoluteToRelative n A) :=
  integralAbsoluteToRelative_natural n (collapseMap A) (collapseMap_mapsTo A)

theorem collapseRelativeComparison_connecting (n : ℕ) (A : Set X) :
    (integralSingularHomologyMap n
        (singularPairRestriction (collapseMap A) (collapseMap_mapsTo A))).comp
        (integralRelativeConnecting n A) =
      (integralRelativeConnecting n (collapseMap A '' A)).comp
        (collapseRelativeComparison (n + 1) A) :=
  integralRelativeConnecting_natural n (collapseMap A) (collapseMap_mapsTo A)

section

variable {P Q : Type} [TopologicalSpace P] [TopologicalSpace Q]

noncomputable def integralRelativeReducedEquiv {B : Set Q} (m : ℕ) (hm : 0 < m)
    (hB : B.Subsingleton) (hne : B.Nonempty) :
    integralRelativeHomology (m + 1) B ≃ₗ[ℤ]
      DifferentialGeometry.Homology.reducedSingularHomology (ModuleCat.of ℤ ℤ) (TopCat.of Q)
        (m + 1) :=
  (LinearEquiv.ofBijective (integralAbsoluteToRelative (m + 1) B)
    (integralAbsoluteToRelative_bijective_of_subsingleton hB hne (by omega))).symm.trans
    (integralReducedSingularHomologyEquiv m Q)

noncomputable def integralRelativeReducedComparison (m : ℕ) (hm : 0 < m) (f : C(P, Q))
    {A : Set P} {B : Set Q} (hf : MapsTo f A B) (hB : B.Subsingleton) (hne : B.Nonempty) :
    integralRelativeHomology (m + 1) A →ₗ[ℤ]
      DifferentialGeometry.Homology.reducedSingularHomology (ModuleCat.of ℤ ℤ) (TopCat.of Q)
        (m + 1) :=
  (integralRelativeReducedEquiv m hm hB hne).toLinearMap.comp
    (integralRelativeHomologyMap (m + 1) f hf)

theorem bijective_integralRelativeHomologyMap_iff_integralRelativeReducedComparison
    (m : ℕ) (hm : 0 < m) (f : C(P, Q)) {A : Set P} {B : Set Q} (hf : MapsTo f A B)
    (hB : B.Subsingleton) (hne : B.Nonempty) :
    Function.Bijective (integralRelativeHomologyMap (m + 1) f hf) ↔
      Function.Bijective (integralRelativeReducedComparison m hm f hf hB hne) := by
  have hb : Function.Bijective fun z => integralRelativeReducedEquiv m hm hB hne z :=
    (integralRelativeReducedEquiv m hm hB hne).bijective
  have h := (Equiv.comp_bijective (integralRelativeHomologyMap (m + 1) f hf)
    (Equiv.ofBijective _ hb)).symm
  simpa only [integralRelativeReducedComparison, LinearMap.coe_comp, LinearEquiv.coe_toLinearMap,
    Equiv.coe_ofBijective, Function.comp_apply] using h

noncomputable def collapseReducedComparison (m : ℕ) (hm : 0 < m) (A : Set P) (hA : A.Nonempty) :
    integralRelativeHomology (m + 1) A →ₗ[ℤ]
      DifferentialGeometry.Homology.reducedSingularHomology (ModuleCat.of ℤ ℤ)
        (TopCat.of (collapseSpace A)) (m + 1) :=
  integralRelativeReducedComparison m hm (collapseMap A) (collapseMap_mapsTo A)
    (collapseMap_image_subsingleton A) (collapseMap_image_nonempty hA)

theorem bijective_collapseReducedComparison_iff (m : ℕ) (hm : 0 < m) (A : Set P)
    (hA : A.Nonempty) :
    Function.Bijective (collapseReducedComparison m hm A hA) ↔
      Function.Bijective (collapseRelativeComparison (m + 1) A) := by
  simpa only [collapseReducedComparison, collapseRelativeComparison] using
    (bijective_integralRelativeHomologyMap_iff_integralRelativeReducedComparison m hm
      (collapseMap A) (collapseMap_mapsTo A) (collapseMap_image_subsingleton A)
      (collapseMap_image_nonempty hA)).symm

theorem bijective_collapseReducedComparison_of_quasiIso {A : Set P} (hA : A.Nonempty)
    (h : CollapseComparisonQuasiIso A) (m : ℕ) (hm : 0 < m) :
    Function.Bijective (collapseReducedComparison m hm A hA) :=
  (bijective_collapseReducedComparison_iff m hm A hA).mpr (h (m + 1))

theorem cubeSphereCollapseComparison_bijective_iff_reduced :
    Function.Bijective cubeSphereCollapseComparison ↔
      Function.Bijective (integralRelativeReducedComparison 2 (by norm_num)
        (cubeSphereCollapse.{0} 2).val cubeSphereCollapse_mapsTo subsingleton_singleton
        (singleton_nonempty (ULift.up (cubeSphereBasepoint 2)))) := by
  simpa only [cubeSphereCollapseComparison] using
    (bijective_integralRelativeHomologyMap_iff_integralRelativeReducedComparison 2 (by norm_num)
      (cubeSphereCollapse.{0} 2).val cubeSphereCollapse_mapsTo subsingleton_singleton
      (singleton_nonempty (ULift.up (cubeSphereBasepoint 2))))

end

end DifferentialGeometry.Topology
