import DifferentialGeometry.Topology.Homology.Local.Generator

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits Set Metric
namespace DifferentialGeometry.Homology
universe u


def localTranslationHomologyIso (G : Type u) [AddGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] (p : G) {k : Type u} [Ring k] (R : ModuleCat.{u} k) (n : ℕ) :
    relativeHomology (TopCat.of G) ({p}ᶜ : Set G) R n ≅
      relativeHomology (TopCat.of G) ({0}ᶜ : Set G) R n :=
  relativeHomologyIso (X := TopCat.of G) (Y := TopCat.of G) R (Homeomorph.subRight p)
    (s := ({p}ᶜ : Set G)) (t := ({0}ᶜ : Set G))
    (fun y => by change y ≠ p ↔ y - p ≠ 0; exact sub_ne_zero.symm) n


@[simp]
theorem localTranslationHomologyIso_hom (G : Type u) [AddGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] (p : G) {k : Type u} [Ring k] (R : ModuleCat.{u} k) (n : ℕ) :
    (localTranslationHomologyIso G p R n).hom =
      relativeHomologyMap R (X := TopCat.of G) (Y := TopCat.of G)
        (s := ({p}ᶜ : Set G)) (t := ({0}ᶜ : Set G))
        (TopCat.ofHom (⟨fun y => y-p,continuous_id.sub continuous_const⟩ : C(G,G)))
        (fun _ hy => sub_ne_zero.mpr hy) n := rfl


@[simp]
theorem localTranslationHomologyIso_zero (G : Type u) [AddGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] {k : Type u} [Ring k] (R : ModuleCat.{u} k) (n : ℕ) :
    localTranslationHomologyIso G 0 R n = Iso.refl _ := by
  apply Iso.ext
  rw [localTranslationHomologyIso_hom]
  have he : TopCat.ofHom (⟨fun y : G => y-0,continuous_id.sub continuous_const⟩ : C(G,G)) =
      𝟙 (TopCat.of G) := by ext y; simp
  have hc := relativeChainMap_congr R (s := ({0}ᶜ : Set G)) (t := ({0}ᶜ : Set G))
    (fun _ hy => sub_ne_zero.mpr hy) (fun _ hy => hy) he
  exact (congrArg (_root_.HomologicalComplex.homologyFunctor (ModuleCat.{u} k)
    (ComplexShape.down ℕ) n).map hc).trans (relativeHomologyMap_id R n)

variable {d : ℕ}

def euclideanLocalGeneratorAt (p : EuclideanSpace ℝ (Fin (d + 1))) :
    relativeHomology (TopCat.of (EuclideanSpace ℝ (Fin (d + 1))))
      ({p}ᶜ : Set (EuclideanSpace ℝ (Fin (d + 1)))) (ModuleCat.of ℤ ℤ) (d + 1) :=
  (localTranslationHomologyIso _ p (ModuleCat.of ℤ ℤ) (d + 1)).inv (euclideanLocalGenerator d)


theorem euclideanLocalGeneratorAt_translate (p : EuclideanSpace ℝ (Fin (d + 1))) :
    (localTranslationHomologyIso _ p (ModuleCat.of ℤ ℤ) (d + 1)).hom (euclideanLocalGeneratorAt p) =
      euclideanLocalGenerator d :=
  congrArg (fun g => g (euclideanLocalGenerator d))
    (localTranslationHomologyIso _ p (ModuleCat.of ℤ ℤ) (d + 1)).inv_hom_id


theorem euclideanLocalGeneratorAt_ne_zero (p : EuclideanSpace ℝ (Fin (d + 1))) :
    euclideanLocalGeneratorAt p ≠ 0 := by
  intro h
  have hh := congrArg (localTranslationHomologyIso _ p (ModuleCat.of ℤ ℤ) (d + 1)).hom h
  rw [euclideanLocalGeneratorAt_translate,map_zero] at hh
  exact euclideanLocalGenerator_ne_zero d hh

@[simp]
theorem euclideanLocalGeneratorAt_zero (d : ℕ) :
    euclideanLocalGeneratorAt (0 : EuclideanSpace ℝ (Fin (d + 1))) = euclideanLocalGenerator d := by
  simp [euclideanLocalGeneratorAt]
end DifferentialGeometry.Homology
