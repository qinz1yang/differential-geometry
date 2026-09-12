import DifferentialGeometry.Topology.Homology.Homotopy
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.HomologicalComplexAbelian









noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology ContinuousMap

universe u

namespace DifferentialGeometry.Topology

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]


abbrev integralSingularChainMap (f : C(X, Y)) : integralSingularChains X ⟶ integralSingularChains Y :=
  ((singularChainComplexFunctor (ModuleCat.{u} ℤ)).obj integralSingularCoefficients).map (TopCat.ofHom f)


def singularSubspaceInclusion (A : Set X) : C(A, X) := ⟨Subtype.val, continuous_subtype_val⟩


instance integralSingularChainMap_subspace_mono (A : Set X) :
    Mono (integralSingularChainMap (singularSubspaceInclusion A)) := by
  have : Mono (TopCat.ofHom (singularSubspaceInclusion A)) :=
    (TopCat.mono_iff_injective _).mpr Subtype.val_injective
  exact inferInstanceAs (Mono
    (((singularChainComplexFunctor (ModuleCat.{u} ℤ)).obj integralSingularCoefficients).map
      (TopCat.ofHom (singularSubspaceInclusion A))))



def integralRelativeChains (A : Set X) : ChainComplex (ModuleCat.{u} ℤ) ℕ :=
  cokernel (integralSingularChainMap (singularSubspaceInclusion A))


def integralRelativeChainSequence (A : Set X) : ShortComplex (ChainComplex (ModuleCat.{u} ℤ) ℕ) :=
  ShortComplex.mk (integralSingularChainMap (singularSubspaceInclusion A))
    (cokernel.π _) (cokernel.condition _)


theorem integralRelativeChainSequence_shortExact (A : Set X) :
    (integralRelativeChainSequence A).ShortExact where
  exact := (integralRelativeChainSequence A).exact_of_g_is_cokernel (cokernelIsCokernel _)
  mono_f := integralSingularChainMap_subspace_mono A
  epi_g := inferInstanceAs (Epi (cokernel.π (integralSingularChainMap (singularSubspaceInclusion A))))


abbrev integralRelativeHomology (n : ℕ) (A : Set X) : ModuleCat.{u} ℤ :=
  (integralRelativeChains A).homology n


def integralAbsoluteToRelative (n : ℕ) (A : Set X) :
    integralSingularHomology n X →ₗ[ℤ] integralRelativeHomology n A :=
  (HomologicalComplex.homologyMap (integralRelativeChainSequence A).g n).hom


def integralRelativeConnecting (n : ℕ) (A : Set X) :
    integralRelativeHomology (n + 1) A →ₗ[ℤ] integralSingularHomology n A :=
  ((integralRelativeChainSequence_shortExact A).δ (n + 1) n (by simp)).hom


theorem integralRelative_exact_absolute (n : ℕ) (A : Set X) :
    Function.Exact (integralSingularHomologyMap n (singularSubspaceInclusion A))
      (integralAbsoluteToRelative n A) :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
    ((integralRelativeChainSequence_shortExact A).homology_exact₂ n)


theorem integralRelative_exact_relative (n : ℕ) (A : Set X) :
    Function.Exact (integralAbsoluteToRelative (n + 1) A) (integralRelativeConnecting n A) :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
    ((integralRelativeChainSequence_shortExact A).homology_exact₃ (n + 1) n (by simp))


theorem integralRelative_exact_subspace (n : ℕ) (A : Set X) :
    Function.Exact (integralRelativeConnecting n A)
      (integralSingularHomologyMap n (singularSubspaceInclusion A)) :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
    ((integralRelativeChainSequence_shortExact A).homology_exact₁ (n + 1) n (by simp))


theorem integralAbsoluteToRelative_injective_of_subsingleton (n : ℕ) (A : Set X)
    (h : Subsingleton (integralSingularHomology n A)) :
    Function.Injective (integralAbsoluteToRelative n A) := by
  intro a b hab
  have hz : integralAbsoluteToRelative n A (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  have hex := LinearMap.exact_iff.mp (integralRelative_exact_absolute n A)
  have hmem : a - b ∈ LinearMap.range
      (integralSingularHomologyMap n (singularSubspaceInclusion A)) := by
    rw [← hex]
    exact LinearMap.mem_ker.mpr hz
  obtain ⟨x, hx⟩ := LinearMap.mem_range.mp hmem
  have hx0 : x = 0 := h.allEq x 0
  rw [hx0, map_zero] at hx
  exact sub_eq_zero.mp hx.symm



def integralRelativeConnectingEquivOfContractible [ContractibleSpace X]
    (n : ℕ) (hn : n ≠ 0) (A : Set X) :
    integralRelativeHomology (n + 1) A ≃ₗ[ℤ] integralSingularHomology n A := by
  let := integralSingularHomology_subsingleton_of_contractible n hn X
  let := integralSingularHomology_subsingleton_of_contractible (n + 1) (by omega) X
  exact ((integralRelativeChainSequence_shortExact A).δIso (n + 1) n (by simp)
    (ModuleCat.isZero_of_subsingleton (integralSingularHomology (n + 1) X))
    (ModuleCat.isZero_of_subsingleton (integralSingularHomology n X))).toLinearEquiv

end DifferentialGeometry.Topology
