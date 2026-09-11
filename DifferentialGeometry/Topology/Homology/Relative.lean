import DifferentialGeometry.Topology.Homology.Algebra.FiniteType
import DifferentialGeometry.Topology.Homology.EulerCharacteristic
import Mathlib.Topology.Category.TopCat.EpiMono

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology
noncomputable section
universe u

namespace DifferentialGeometry.Homology
variable (X : TopCat.{u}) (s : Set X) {k : Type u} [Ring k] (R : ModuleCat.{u} k)


def relativeInclusion :
    ((singularChainComplexFunctor (ModuleCat.{u} k)).obj R).obj (TopCat.of s) ⟶
      ((singularChainComplexFunctor (ModuleCat.{u} k)).obj R).obj X :=
  ((singularChainComplexFunctor (ModuleCat.{u} k)).obj R).map
    (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(s, X)))

instance : Mono (relativeInclusion X s R) := by
  have : Mono (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(s, X))) :=
    (TopCat.mono_iff_injective _).mpr Subtype.val_injective
  unfold relativeInclusion
  infer_instance


def relativeChainComplex : ChainComplex (ModuleCat.{u} k) ℕ :=
  cokernel (relativeInclusion X s R)


def relativeProjection :
    ((singularChainComplexFunctor (ModuleCat.{u} k)).obj R).obj X ⟶
      relativeChainComplex X s R :=
  cokernel.π (relativeInclusion X s R)


@[reassoc (attr := simp)]
theorem relativeInclusion_projection :
    relativeInclusion X s R ≫ relativeProjection X s R = 0 :=
  cokernel.condition _


def relativeShortComplex : ShortComplex (ChainComplex (ModuleCat.{u} k) ℕ) :=
  ShortComplex.mk (relativeInclusion X s R) (relativeProjection X s R)
    (relativeInclusion_projection X s R)


theorem relativeShortExact : (relativeShortComplex X s R).ShortExact where
  exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)
  mono_f := inferInstanceAs (Mono (relativeInclusion X s R))
  epi_g := inferInstanceAs (Epi (cokernel.π (relativeInclusion X s R)))

def relativeChainQuotientIso (n : ℕ) :
    (relativeChainComplex X s R).X n ≅
      ModuleCat.of k
        ((((singularChainComplexFunctor (ModuleCat.{u} k)).obj R).obj X).X n ⧸
          LinearMap.range ((relativeInclusion X s R).f n).hom) :=
  PreservesCokernel.iso (_root_.HomologicalComplex.eval _ _ n) (relativeInclusion X s R) ≪≫
    ModuleCat.cokernelIsoRangeQuotient ((relativeInclusion X s R).f n)

@[reassoc (attr := simp)]
theorem relativeProjection_quotientIso (n : ℕ) :
    (relativeProjection X s R).f n ≫ (relativeChainQuotientIso X s R n).hom =
      ModuleCat.ofHom (LinearMap.range ((relativeInclusion X s R).f n).hom).mkQ := by
  exact (PreservesCokernel.π_iso_hom_assoc
    (_root_.HomologicalComplex.eval _ _ n) (relativeInclusion X s R)
    (ModuleCat.cokernelIsoRangeQuotient
      ((_root_.HomologicalComplex.eval _ _ n).map (relativeInclusion X s R))).hom).trans
        (ModuleCat.cokernel_π_cokernelIsoRangeQuotient_hom _)


def relativeHomology (n : ℕ) : ModuleCat.{u} k :=
  (relativeChainComplex X s R).homology n


def relativeConnecting (n : ℕ) :
    relativeHomology X s R (n + 1) ⟶
      ((singularHomologyFunctor (ModuleCat.{u} k) n).obj R).obj (TopCat.of s) :=
  (relativeShortExact X s R).δ (n + 1) n rfl


theorem relative_homology_exact_subspace (n : ℕ) :
    (ShortComplex.mk (relativeConnecting X s R n)
      (_root_.HomologicalComplex.homologyMap (relativeInclusion X s R) n)
      ((relativeShortExact X s R).δ_comp (n + 1) n rfl)).Exact :=
  (relativeShortExact X s R).homology_exact₁ (n + 1) n rfl


theorem relative_homology_exact_absolute (n : ℕ) :
    ((relativeShortComplex X s R).map
      (_root_.HomologicalComplex.homologyFunctor (ModuleCat.{u} k) (ComplexShape.down ℕ) n)).Exact :=
  (relativeShortExact X s R).homology_exact₂ n


theorem relative_homology_exact_relative (n : ℕ) :
    (ShortComplex.mk (_root_.HomologicalComplex.homologyMap (relativeProjection X s R) (n + 1))
      (relativeConnecting X s R n)
      ((relativeShortExact X s R).comp_δ (n + 1) n rfl)).Exact :=
  (relativeShortExact X s R).homology_exact₃ (n + 1) n rfl

section Field
variable (k : Type u) [Field k]


theorem finiteHomologyType_relativeChainComplex
    (hs : finiteHomologyType k (TopCat.of s)) (hX : finiteHomologyType k X) :
    DifferentialGeometry.HomologicalComplex.finiteHomologyType (relativeChainComplex X s (ModuleCat.of k k)) :=
  DifferentialGeometry.HomologicalComplex.finiteHomologyType_last
    (relativeShortComplex X s (ModuleCat.of k k)) (relativeShortExact X s (ModuleCat.of k k)) hs hX

def relativeEulerChar : ℤ :=
  (relativeChainComplex X s (ModuleCat.of k k)).homologyEulerChar

theorem relativeEulerChar_eq_sub
    (hs : finiteHomologyType k (TopCat.of s)) (hX : finiteHomologyType k X) :
    relativeEulerChar X s k = eulerChar k X - eulerChar k (TopCat.of s) := by
  let S := relativeShortComplex X s (ModuleCat.of k k)
  have hr := finiteHomologyType_relativeChainComplex X s k hs hX
  have : ∀ n, FiniteDimensional k (S.X₁.homology n) := hs.1
  have : ∀ n, FiniteDimensional k (S.X₂.homology n) := hX.1
  have : ∀ n, FiniteDimensional k (S.X₃.homology n) := hr.1
  have h := DifferentialGeometry.HomologicalComplex.homologyEulerChar_additive S
    (relativeShortExact X s (ModuleCat.of k k)) hs.2 hX.2 hr.2
  change eulerChar k X = eulerChar k (TopCat.of s) + relativeEulerChar X s k at h
  omega

end Field
end DifferentialGeometry.Homology
