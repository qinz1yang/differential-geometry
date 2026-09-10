import Mathlib.AlgebraicTopology.SingularSet
import Mathlib.Topology.ContinuousMap.Sigma
import Mathlib.CategoryTheory.Limits.Types.Coproducts
import Mathlib.Topology.Category.TopCat.Limits.Products

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
namespace Poincare.TopCat
universe u
variable {ι : Type u} (X : ι → TopCat.{u})


def singularSigmaCofan : Cofan (fun i => TopCat.toSSet.obj (X i)) :=
  Cofan.mk (TopCat.toSSet.obj (TopCat.of (Σ i, X i)))
    (fun i => TopCat.toSSet.map (TopCat.sigmaι X i))


def singularSigmaCofanIsColimit : IsColimit (singularSigmaCofan X) := by
  apply evaluationJointlyReflectsColimits
  intro n
  refine (Cofan.isColimitMapCoconeEquiv ((evaluation _ (Type u)).obj n) _ (singularSigmaCofan X)).symm ?_
  apply Classical.choice
  apply (Cofan.nonempty_isColimit_iff_bijective_fromSigma _).mpr
  constructor
  · intro a b hab
    have hh : (ContinuousMap.sigmaMk (X := fun i => ↥(X i)) a.1).comp ((X a.1).toSSetObjEquiv n a.2) =
        (ContinuousMap.sigmaMk (X := fun i => ↥(X i)) b.1).comp ((X b.1).toSSetObjEquiv n b.2) :=
      congrArg ((TopCat.of (Σ i, X i)).toSSetObjEquiv n) hab
    have h : (⟨a.1, (X a.1).toSSetObjEquiv n a.2⟩ : Σ i, C(stdSimplex ℝ (Fin (n.unop.len + 1)), X i)) =
        ⟨b.1, (X b.1).toSSetObjEquiv n b.2⟩ := ContinuousMap.isEmbedding_sigmaMk_comp.injective hh
    obtain ⟨i,a⟩ := a
    obtain ⟨j,b⟩ := b
    have hij : i = j := congrArg Sigma.fst h
    subst j
    have he := (Sigma.mk.inj h).2
    congr
    exact ((X i).toSSetObjEquiv n).injective (eq_of_heq he)
  · intro σ
    obtain ⟨i,g,hg⟩ := ((TopCat.of (Σ i, X i)).toSSetObjEquiv n σ).exists_lift_sigma
    refine ⟨⟨i, ((X i).toSSetObjEquiv n).symm g⟩, ?_⟩
    apply ((TopCat.of (Σ i, X i)).toSSetObjEquiv n).injective
    change (ContinuousMap.sigmaMk (X := fun i => ↥(X i)) i).comp ((X i).toSSetObjEquiv n (((X i).toSSetObjEquiv n).symm g)) = _
    rw [Equiv.apply_symm_apply]
    exact hg.symm
end Poincare.TopCat
