import DifferentialGeometry.Topology.Homology.Relative
import DifferentialGeometry.Topology.Homology.Reduced
import DifferentialGeometry.Topology.Homology.Algebra.Augment

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped ZeroObject
noncomputable section
universe u
namespace Poincare.Homology
variable (X : TopCat.{u}) (s : Set X) {k : Type u} [Ring k] (R : ModuleCat.{u} k)


def augmentedRelativeChainComplex : ChainComplex (ModuleCat.{u} k) ℕ :=
  (relativeChainComplex X s R).augment (0 : (relativeChainComplex X s R).X 0 ⟶ 0) (by simp)


def augmentedRelativeProjection :
    augmentedSingularChainComplex R X ⟶ augmentedRelativeChainComplex X s R :=
  Poincare.ChainComplex.augmentMap (d_singularAugmentation R X) (by simp)
    (relativeProjection X s R) (0 : R ⟶ 0) (by simp)


@[simp]
theorem augmentedRelativeProjection_f_zero :
    (augmentedRelativeProjection X s R).f 0 = (0 : R ⟶ 0) := rfl


@[simp]
theorem augmentedRelativeProjection_f_succ (n : ℕ) :
    (augmentedRelativeProjection X s R).f (n + 1) = (relativeProjection X s R).f n := rfl


abbrev augmentedRelativeShortComplex : ShortComplex (ChainComplex (ModuleCat.{u} k) ℕ) :=
  ShortComplex.mk
    (augmentedSingularChainMap R
      (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(s, X))))
    (augmentedRelativeProjection X s R) (by
      apply HomologicalComplex.Hom.ext
      funext n
      cases n with
      | zero => change 𝟙 R ≫ (0 : R ⟶ 0) = 0; simp
      | succ n =>
        exact congrArg (fun f => f.f n) (relativeInclusion_projection X s R))


theorem augmentedRelativeShortExact : (augmentedRelativeShortComplex X s R).ShortExact := by
  rw [HomologicalComplex.shortExact_iff_degreewise_shortExact]
  intro n
  cases n with
  | zero =>
    have hmono : Mono (𝟙 R) := inferInstance
    have hepi : Epi (0 : R ⟶ 0) := inferInstance
    refine { exact := ?_, mono_f := hmono, epi_g := hepi }
    apply (ShortComplex.exact_iff_epi _ (by rfl)).mpr
    change Epi (𝟙 R)
    infer_instance
  | succ n =>
    exact (HomologicalComplex.shortExact_iff_degreewise_shortExact _).mp
      (relativeShortExact X s R) n

private def relativePositiveShortComplexIso (n : ℕ) :
    (augmentedRelativeChainComplex X s R).sc' (n + 3) (n + 2) (n + 1) ≅
      (relativeChainComplex X s R).sc' (n + 2) (n + 1) n :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by change 𝟙 _ ≫ (relativeChainComplex X s R).d _ _ =
      (relativeChainComplex X s R).d _ _ ≫ 𝟙 _; simp)
    (by change 𝟙 _ ≫ (relativeChainComplex X s R).d _ _ =
      (relativeChainComplex X s R).d _ _ ≫ 𝟙 _; simp)


def augmentedRelativeHomologySuccIso (n : ℕ) :
    (augmentedRelativeChainComplex X s R).homology (n + 2) ≅
      relativeHomology X s R (n + 1) :=
  (augmentedRelativeChainComplex X s R).homologyIsoSc' (n + 3) (n + 2) (n + 1)
    (by simp) (by simp) ≪≫
    ShortComplex.homologyMapIso (relativePositiveShortComplexIso X s R n) ≪≫
      ((relativeChainComplex X s R).homologyIsoSc' (n + 2) (n + 1) n
        (by simp) (by simp)).symm

def relativeReducedConnectingIso [ContractibleSpace X] (n : ℕ) :
    relativeHomology X s R (n + 1) ≅ reducedSingularHomology R (TopCat.of s) n :=
  (augmentedRelativeHomologySuccIso X s R n).symm ≪≫
    (augmentedRelativeShortExact X s R).δIso (n + 2) (n + 1) rfl
      (isZero_reducedSingularHomology_of_contractible R X (n + 1))
      (isZero_reducedSingularHomology_of_contractible R X n)

@[reassoc (attr := simp)]
theorem augmentedRelativeHomologySuccIso_connecting [ContractibleSpace X] (n : ℕ) :
    (augmentedRelativeHomologySuccIso X s R n).hom ≫
      (relativeReducedConnectingIso X s R n).hom =
        (augmentedRelativeShortExact X s R).δ (n + 2) (n + 1) rfl := by
  change _ ≫ (_ ≫ _) = _
  erw [Iso.hom_inv_id_assoc]
  rfl

end Poincare.Homology
