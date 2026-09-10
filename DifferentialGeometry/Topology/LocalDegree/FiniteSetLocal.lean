import DifferentialGeometry.Topology.LocalDegree.Relative
import DifferentialGeometry.Topology.Homology.Local.NeighborhoodGenerator
import DifferentialGeometry.Topology.Homology.Local.FiniteSetDecomposition

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits Set Metric
namespace Poincare.LocalDegree
open Poincare.Homology
universe u
section Maps
variable {E F : Type u} [PseudoMetricSpace E] [TopologicalSpace F] [Zero F]
  {f : E → F} {p : E} {r : ℝ} (hr : IsolatingRadius f p r)
  {k : Type u} [Ring k] (A : ModuleCat.{u} k)

def IsolatingRadius.finitePunctureHomologyMap (n : ℕ) :
    relativeHomology (TopCat.of (ball p r))
      ({(⟨p,mem_ball_self hr.pos⟩ : ball p r)}ᶜ : Set (ball p r)) A n ⟶
    relativeHomology (TopCat.of E) ({x | f x = 0}ᶜ : Set E) A n :=
  Poincare.Homology.relativeHomologyMap A (X := TopCat.of (ball p r)) (Y := TopCat.of E)
    (s := ({(⟨p,mem_ball_self hr.pos⟩ : ball p r)}ᶜ : Set (ball p r)))
    (t := ({x | f x = 0}ᶜ : Set E))
    (TopCat.ofHom (⟨Subtype.val,continuous_subtype_val⟩ : C(ball p r,E)))
    (fun y hy => hr.nonzero y (ball_subset_closedBall y.property)
      (fun he => hy (Subtype.ext he))) n

@[reassoc]
theorem IsolatingRadius.finitePunctureHomologyMap_projection_self [T1Space E] (n : ℕ) :
    hr.finitePunctureHomologyMap A n ≫
      finitePunctureProjection (TopCat.of E) {x | f x = 0} A ⟨p,hr.zero⟩ n =
    (puncturedNeighborhoodHomologyIso (TopCat.of E) (ball p r) p (mem_ball_self hr.pos)
      A isOpen_ball n).hom := by
  erw [IsolatingRadius.finitePunctureHomologyMap,finitePunctureProjection,
    puncturedNeighborhoodHomologyIso_hom,← relativeHomologyMap_comp]
  rfl

@[reassoc]
theorem IsolatingRadius.finitePunctureHomologyMap_projection_ne
    (q : {x | f x = 0}) (hpq : p ≠ q.val) (n : ℕ) :
    hr.finitePunctureHomologyMap A n ≫
      finitePunctureProjection (TopCat.of E) {x | f x = 0} A q n = 0 := by
  erw [IsolatingRadius.finitePunctureHomologyMap,finitePunctureProjection,
    ← relativeHomologyMap_comp]
  apply relativeHomologyMap_eq_zero_of_range_subset
  rintro y ⟨z,rfl⟩ he
  change z.val = q.val at he
  have hz : f z.val = 0 := he ▸ q.property
  exact hpq ((hr.zero_iff z (ball_subset_closedBall z.property)).mp hz |>.symm.trans he)

theorem IsolatingRadius.finitePunctureHomologyMap_eq_inclusion [T2Space E]
    (hZ : {x | f x = 0}.Finite) (n : ℕ) :
    hr.finitePunctureHomologyMap A n =
      (puncturedNeighborhoodHomologyIso (TopCat.of E) (ball p r) p (mem_ball_self hr.pos)
        A isOpen_ball n).hom ≫
      finitePunctureHomologyInclusion (TopCat.of E) {x | f x = 0} A hZ n ⟨p,hr.zero⟩ := by
  apply (cancel_mono (finitePunctureHomologyIso (TopCat.of E) {x | f x = 0} A hZ n).hom).mp
  apply Pi.hom_ext
  intro q
  simp only [Category.assoc]
  erw [finitePunctureHomologyIso_hom_π]
  by_cases hpq : p = q.val
  · have hq : q = (⟨p,hr.zero⟩ : {x | f x = 0}) := Subtype.ext hpq.symm
    subst q
    rw [IsolatingRadius.finitePunctureHomologyMap_projection_self,
      finitePunctureHomologyInclusion_projection_self,Category.comp_id]
  · rw [IsolatingRadius.finitePunctureHomologyMap_projection_ne hr A q hpq,
      finitePunctureHomologyInclusion_projection_ne _ _ _ _ _ _ q
        (fun h => hpq (congrArg Subtype.val h)),comp_zero]

@[reassoc]
theorem IsolatingRadius.finitePunctureHomologyMap_comp (hf : Continuous f) (n : ℕ) :
    hr.finitePunctureHomologyMap A n ≫
      Poincare.Homology.relativeHomologyMap A (X := TopCat.of E) (Y := TopCat.of F)
        (s := ({x | f x = 0}ᶜ : Set E)) (t := ({0}ᶜ : Set F))
        (TopCat.ofHom (⟨f,hf⟩ : C(E,F))) (fun _ hy => hy) n =
      hr.relativeHomologyMap A n := by
  erw [IsolatingRadius.finitePunctureHomologyMap,← relativeHomologyMap_comp,
    IsolatingRadius.relativeHomologyMap_eq]
  rfl
end Maps

section Euclidean
variable {d : ℕ}
  {f : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1))}
  {p : EuclideanSpace ℝ (Fin (d + 1))} {r : ℝ} (hr : IsolatingRadius f p r)

theorem IsolatingRadius.finitePunctureHomologyMap_generator_self :
    finitePunctureProjection (TopCat.of (EuclideanSpace ℝ (Fin (d + 1)))) {x | f x = 0}
      (ModuleCat.of ℤ ℤ) ⟨p,hr.zero⟩ (d + 1)
      (hr.finitePunctureHomologyMap (ModuleCat.of ℤ ℤ) (d + 1)
        (euclideanBallLocalGenerator p r hr.pos)) = euclideanLocalGeneratorAt p := by
  have he := congrArg (fun g => g (euclideanBallLocalGenerator p r hr.pos))
    (hr.finitePunctureHomologyMap_projection_self (ModuleCat.of ℤ ℤ) (d + 1))
  exact he.trans (euclideanBallLocalGenerator_inclusion p r hr.pos)


theorem IsolatingRadius.finitePunctureHomologyMap_generator_ne
    (q : {x | f x = 0}) (hpq : p ≠ q.val) :
    finitePunctureProjection (TopCat.of (EuclideanSpace ℝ (Fin (d + 1)))) {x | f x = 0}
      (ModuleCat.of ℤ ℤ) q (d + 1)
      (hr.finitePunctureHomologyMap (ModuleCat.of ℤ ℤ) (d + 1)
        (euclideanBallLocalGenerator p r hr.pos)) = 0 := by
  exact (congrArg (fun g => g (euclideanBallLocalGenerator p r hr.pos))
    (hr.finitePunctureHomologyMap_projection_ne (ModuleCat.of ℤ ℤ) q hpq (d + 1))).trans rfl

theorem IsolatingRadius.finitePunctureHomologyMap_generator_inclusion
    (hZ : {x | f x = 0}.Finite) :
    hr.finitePunctureHomologyMap (ModuleCat.of ℤ ℤ) (d + 1)
      (euclideanBallLocalGenerator p r hr.pos) =
    finitePunctureHomologyInclusion (TopCat.of (EuclideanSpace ℝ (Fin (d + 1))))
      {x | f x = 0} (ModuleCat.of ℤ ℤ) hZ (d + 1) ⟨p,hr.zero⟩ (euclideanLocalGeneratorAt p) := by
  have he := congrArg (fun g => g (euclideanBallLocalGenerator p r hr.pos))
    (hr.finitePunctureHomologyMap_eq_inclusion (ModuleCat.of ℤ ℤ) hZ (d + 1))
  exact he.trans (congrArg
    (finitePunctureHomologyInclusion (TopCat.of (EuclideanSpace ℝ (Fin (d + 1))))
      {x | f x = 0} (ModuleCat.of ℤ ℤ) hZ (d + 1) ⟨p,hr.zero⟩)
    (euclideanBallLocalGenerator_inclusion p r hr.pos))

theorem IsolatingRadius.finitePunctureHomologyMap_generator_degree (hf : Continuous f) :
    Poincare.Homology.relativeHomologyMap (ModuleCat.of ℤ ℤ)
      (X := TopCat.of (EuclideanSpace ℝ (Fin (d + 1))))
      (Y := TopCat.of (EuclideanSpace ℝ (Fin (d + 1))))
      (s := ({x | f x = 0}ᶜ : Set (EuclideanSpace ℝ (Fin (d + 1)))))
      (t := ({0}ᶜ : Set (EuclideanSpace ℝ (Fin (d + 1)))))
      (TopCat.ofHom (⟨f,hf⟩ : C(EuclideanSpace ℝ (Fin (d + 1)),EuclideanSpace ℝ (Fin (d + 1)))))
      (fun _ hy => hy) (d + 1)
      (hr.finitePunctureHomologyMap (ModuleCat.of ℤ ℤ) (d + 1)
        (euclideanBallLocalGenerator p r hr.pos)) =
      euclideanLocalDegree f p ⟨r,hr⟩ • euclideanLocalGenerator d := by
  have he := congrArg (fun g => g (euclideanBallLocalGenerator p r hr.pos))
    (hr.finitePunctureHomologyMap_comp (ModuleCat.of ℤ ℤ) hf (d + 1))
  exact he.trans (euclideanLocalDegree_relativeHomology hr)

theorem IsolatingRadius.finitePunctureHomologyInclusion_generator_degree
    (hZ : {x | f x = 0}.Finite) (hf : Continuous f) :
    Poincare.Homology.relativeHomologyMap (ModuleCat.of ℤ ℤ)
      (X := TopCat.of (EuclideanSpace ℝ (Fin (d + 1))))
      (Y := TopCat.of (EuclideanSpace ℝ (Fin (d + 1))))
      (s := ({x | f x = 0}ᶜ : Set (EuclideanSpace ℝ (Fin (d + 1)))))
      (t := ({0}ᶜ : Set (EuclideanSpace ℝ (Fin (d + 1)))))
      (TopCat.ofHom (⟨f,hf⟩ : C(EuclideanSpace ℝ (Fin (d + 1)),EuclideanSpace ℝ (Fin (d + 1)))))
      (fun _ hy => hy) (d + 1)
      (finitePunctureHomologyInclusion (TopCat.of (EuclideanSpace ℝ (Fin (d + 1))))
        {x | f x = 0} (ModuleCat.of ℤ ℤ) hZ (d + 1) ⟨p,hr.zero⟩ (euclideanLocalGeneratorAt p)) =
      euclideanLocalDegree f p ⟨r,hr⟩ • euclideanLocalGenerator d := by
  rw [← hr.finitePunctureHomologyMap_generator_inclusion hZ]
  exact hr.finitePunctureHomologyMap_generator_degree hf

end Euclidean
end Poincare.LocalDegree
