import DifferentialGeometry.Topology.LocalDegree.ClosedBall
import DifferentialGeometry.Topology.LocalDegree.FiniteSetLocal
import DifferentialGeometry.Topology.LocalDegree.FiniteZeros
import DifferentialGeometry.Topology.Homology.Local.ClosedBallFiniteSet
import DifferentialGeometry.Topology.ClosedBall.Extension

set_option autoImplicit false
noncomputable section
open CategoryTheory Set Metric Filter
open scoped Topology
namespace Poincare.LocalDegree
open Poincare.Homology
section GlobalAux
variable {d : ℕ} {a : EuclideanSpace ℝ (Fin (d + 1))} {r : ℝ}
  (hr : 0 < r) (f : C(EuclideanSpace ℝ (Fin (d + 1)), EuclideanSpace ℝ (Fin (d + 1))))
  (hfinite : {x | f x = 0}.Finite) (hball : {x | f x = 0} ⊆ ball a r)


private theorem euclideanBallDegree_eq_finsum_of_finite_zeroSet :
    euclideanBallDegree hr (f.restrict (closedBall a r))
      (fun _ hy hz => (ne_of_lt (hball hz)) (mem_sphere.mp hy)) =
    ∑ᶠ p : {x | f x = 0}, euclideanLocalDegree f p.val
      (isolatedZero_of_continuous_finite_zeroSet f.continuous hfinite p.property) := by
  classical
  let E := EuclideanSpace ℝ (Fin (d + 1))
  let Z : Set E := {x | f x = 0}
  let A := ModuleCat.of ℤ ℤ
  let m : relativeHomology (TopCat.of E) Zᶜ A (d + 1) ⟶
      relativeHomology (TopCat.of E) ({0}ᶜ : Set E) A (d + 1) :=
    Poincare.Homology.relativeHomologyMap A (X := TopCat.of E) (Y := TopCat.of E)
      (s := Zᶜ) (t := ({0}ᶜ : Set E)) (TopCat.ofHom f) (fun _ hx => hx) (d + 1)
  have hi : MapsTo (Subtype.val : closedBall a r → E)
      {y : closedBall a r | y.val ∈ sphere a r} Zᶜ := by
    intro y hy hz
    change f y.val = 0 at hz
    have hh : dist y.val a < r := hball hz
    have hs : dist y.val a = r := mem_sphere.mp hy
    exact (ne_of_lt hh) hs
  have hm : closedBallPunctureHomologyMap a r A Z hball (d + 1) ≫ m =
      closedBallRelativeHomologyMap A (f.restrict (closedBall a r))
        (fun _ hy hz => (ne_of_lt (hball hz)) (mem_sphere.mp hy)) (d + 1) :=
    (relativeHomologyMap_comp A (X := TopCat.of (closedBall a r)) (Y := TopCat.of E) (Z := TopCat.of E)
      (s := {y : closedBall a r | y.val ∈ sphere a r}) (t := Zᶜ) (v := ({0}ᶜ : Set E))
      (TopCat.ofHom (⟨Subtype.val,continuous_subtype_val⟩ : C(closedBall a r,E))) hi
      (TopCat.ofHom f) (fun _ hx => hx) (d + 1)).symm
  apply (euclideanBallDegree_eq_iff hr (f.restrict (closedBall a r))
    (fun _ hy hz => (ne_of_lt (hball hz)) (mem_sphere.mp hy)) _).mpr
  rw [← congrArg (fun g => g (euclideanClosedBallFundamentalClass a r hr)) hm]
  change m (closedBallPunctureHomologyMap a r A Z hball (d + 1)
    (euclideanClosedBallFundamentalClass a r hr)) = _
  rw [closedBallPunctureHomologyMap_fundamentalClass_eq_finsum a r hr Z hball hfinite]
  let := hfinite.fintype
  rw [finsum_eq_sum_of_fintype,map_sum,finsum_eq_sum_of_fintype]
  change _ = (zmultiplesHom (relativeHomology (TopCat.of E) ({0}ᶜ : Set E) A (d + 1))
    (euclideanLocalGenerator d)) (∑ p : Z, euclideanLocalDegree f p.val
      (isolatedZero_of_continuous_finite_zeroSet f.continuous hfinite p.property))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro p _
  obtain ⟨R,hR⟩ := isolatedZero_of_continuous_finite_zeroSet f.continuous hfinite p.property
  exact hR.finitePunctureHomologyInclusion_generator_degree hfinite f.continuous
end GlobalAux

variable {d : ℕ} {a : EuclideanSpace ℝ (Fin (d + 1))} {r : ℝ}
  (hr : 0 < r) {f : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1))}
  (hf : ContinuousOn f (closedBall a r)) (hfinite : {x ∈ closedBall a r | f x = 0}.Finite)
  (hb : ∀ x ∈ sphere a r, f x ≠ 0)


theorem euclideanBallDegree_eq_finsum_localDegrees :
    euclideanBallDegree hr (⟨fun y => f y.val,hf.domRestrict⟩ : C(closedBall a r, EuclideanSpace ℝ (Fin (d + 1))))
      (fun y hy => hb y.val hy) =
    ∑ᶠ p : {x ∈ closedBall a r | f x = 0}, euclideanLocalDegree f p.val
      (isolatedZero_of_finite_closedBall_zeroSet hf hfinite hb p.property.1 p.property.2) := by
  classical
  let E := EuclideanSpace ℝ (Fin (d + 1))
  let Z : Set E := {x ∈ closedBall a r | f x = 0}
  let F : C(closedBall a r,E) := ⟨fun y => f y.val,hf.domRestrict⟩
  let G : C(E,E) := Poincare.Topology.ClosedBall.extension a hr.le F
  have hFb : ∀ y : closedBall a r, y.val ∈ sphere a r → F y ≠ 0 := fun y hy => hb y.val hy
  have hset : {x | G x = 0} = Z := by
    ext x
    change Poincare.Topology.ClosedBall.extension a hr.le F x = 0 ↔ x ∈ closedBall a r ∧ f x = 0
    rw [Poincare.Topology.ClosedBall.extension_eq_iff a hr.le F hFb x]
    exact ⟨fun ⟨hx,hz⟩ => ⟨hx,hz⟩,fun ⟨hx,hz⟩ => ⟨hx,hz⟩⟩
  have hGfinite : {x | G x = 0}.Finite := hset.symm ▸ hfinite
  have hGball : {x | G x = 0} ⊆ ball a r := by
    intro x hx
    have hxZ : x ∈ Z := hset ▸ hx
    exact closedBall_zeroSet_subset_ball hb hxZ
  have heq : G.restrict (closedBall a r) = F :=
    Poincare.Topology.ClosedBall.extension_restrict a hr.le F
  have hsum := euclideanBallDegree_eq_finsum_of_finite_zeroSet hr G hGfinite hGball
  have hdegree : euclideanBallDegree hr F hFb =
      euclideanBallDegree hr (G.restrict (closedBall a r))
        (fun _ hy hz => (ne_of_lt (hGball hz)) (mem_sphere.mp hy)) := by
    congr 1
    exact heq.symm
  refine hdegree.trans (hsum.trans ?_)
  let e : {x | G x = 0} ≃ Z := Equiv.setCongr hset
  have hlocal (p : {x | G x = 0}) :
      euclideanLocalDegree G p.val (isolatedZero_of_continuous_finite_zeroSet G.continuous hGfinite p.property) =
      euclideanLocalDegree f (e p).val
        (isolatedZero_of_finite_closedBall_zeroSet hf hfinite hb (e p).property.1 (e p).property.2) := by
    apply euclideanLocalDegree_congr
    exact Poincare.Topology.ClosedBall.extension_eventuallyEq_of_eventuallyEq a hr.le F
      (hGball p.property) (Filter.EventuallyEq.rfl)
  calc
    _ = ∑ᶠ p : {x | G x = 0}, euclideanLocalDegree f (e p).val
        (isolatedZero_of_finite_closedBall_zeroSet hf hfinite hb (e p).property.1 (e p).property.2) :=
      finsum_congr hlocal
    _ = _ := finsum_comp_equiv e (f := fun p : Z => euclideanLocalDegree f p.val
      (isolatedZero_of_finite_closedBall_zeroSet hf hfinite hb p.property.1 p.property.2))
end Poincare.LocalDegree
