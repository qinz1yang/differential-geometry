/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Homology.Local.NeighborhoodGenerator

open CategoryTheory CategoryTheory.Limits Set Metric

noncomputable section

namespace DifferentialGeometry.Homology

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin (d + 1))
local notation "Z" => ModuleCat.of ℤ ℤ

def euclideanOpenLocalGenerator {U : Set E} (hU : IsOpen U) (x : E) (hx : x ∈ U) :
    relativeHomology (TopCat.of U) ({(⟨x, hx⟩ : U)}ᶜ : Set U) Z (d + 1) :=
  (puncturedNeighborhoodHomologyIso (TopCat.of E) U x hx Z hU (d + 1)).inv
    (euclideanLocalGeneratorAt x)

theorem euclideanOpenLocalGenerator_inclusion {U : Set E}
    (hU : IsOpen U) (x : E) (hx : x ∈ U) :
    (puncturedNeighborhoodHomologyIso (TopCat.of E) U x hx Z hU (d + 1)).hom
      (euclideanOpenLocalGenerator hU x hx) = euclideanLocalGeneratorAt x := by
  exact congrArg (fun g => g (euclideanLocalGeneratorAt x))
    (puncturedNeighborhoodHomologyIso (TopCat.of E) U x hx Z hU (d + 1)).inv_hom_id

theorem euclideanOpenLocalGenerator_ball (x : E) (r : ℝ) (hr : 0 < r) :
    euclideanOpenLocalGenerator isOpen_ball x (mem_ball_self hr) =
      euclideanBallLocalGenerator x r hr := by
  apply (ModuleCat.mono_iff_injective
    (puncturedNeighborhoodHomologyIso (TopCat.of E) (ball x r) x
      (mem_ball_self hr) Z isOpen_ball (d + 1)).hom).mp inferInstance
  rw [euclideanOpenLocalGenerator_inclusion, euclideanBallLocalGenerator_inclusion]

theorem euclideanOpenLocalGenerator_smul_injective {U : Set E}
    (hU : IsOpen U) (x : E) (hx : x ∈ U) :
    Function.Injective (fun m : ℤ => m • euclideanOpenLocalGenerator hU x hx) := by
  intro m n hmn
  let q := puncturedNeighborhoodHomologyIso (TopCat.of E) U x hx Z hU (d + 1)
  let t := localTranslationHomologyIso E x Z (d + 1)
  let s := localEuclideanSphereHomologyIso Z (d + 1) d
  let a := q.toLinearEquiv.toAddEquiv.trans
    (t.toLinearEquiv.toAddEquiv.trans
      (s.toLinearEquiv.toAddEquiv.trans
        (DifferentialGeometry.LocalDegree.euclideanSphereTopReducedHomologyEquiv d)))
  have ha : a (euclideanOpenLocalGenerator hU x hx) = 1 := by
    change DifferentialGeometry.LocalDegree.euclideanSphereTopReducedHomologyEquiv d
      (s.hom (t.hom (q.hom (euclideanOpenLocalGenerator hU x hx)))) = 1
    rw [euclideanOpenLocalGenerator_inclusion, euclideanLocalGeneratorAt_translate]
    simp [s, euclideanLocalGenerator,
      DifferentialGeometry.LocalDegree.euclideanSphereTopReducedHomologyEquiv_generator]
  have h := congrArg a hmn
  simpa only [map_zsmul, ha, smul_eq_mul, mul_one] using h

theorem euclideanOpenLocalGenerator_map_inclusion {U V : Set E}
    (hU : IsOpen U) (hV : IsOpen V) (hUV : U ⊆ V) (x : E) (hx : x ∈ U)
    (j : TopCat.of U ⟶ TopCat.of V)
    (hj : ∀ z : U, (j z : E) = (z : E))
    (hjpunct : MapsTo j ({(⟨x, hx⟩ : U)}ᶜ : Set U)
      ({(⟨x, hUV hx⟩ : V)}ᶜ : Set V)) :
    relativeHomologyMap Z j hjpunct (d + 1) (euclideanOpenLocalGenerator hU x hx) =
      euclideanOpenLocalGenerator hV x (hUV hx) := by
  let iU := puncturedNeighborhoodHomologyIso (TopCat.of E) U x hx Z hU (d + 1)
  let iV := puncturedNeighborhoodHomologyIso (TopCat.of E) V x (hUV hx) Z hV (d + 1)
  have heq : relativeHomologyMap Z j hjpunct (d + 1) ≫ iV.hom = iU.hom := by
    dsimp only [iU, iV]
    rw [puncturedNeighborhoodHomologyIso_hom, puncturedNeighborhoodHomologyIso_hom,
      ← relativeHomologyMap_comp]
    congr 1
    exact TopCat.ext hj
  apply (ModuleCat.mono_iff_injective iV.hom).mp inferInstance
  change (relativeHomologyMap Z j hjpunct (d + 1) ≫ iV.hom)
    (euclideanOpenLocalGenerator hU x hx) = _
  rw [heq]
  exact (euclideanOpenLocalGenerator_inclusion hU x hx).trans
    (euclideanOpenLocalGenerator_inclusion hV x (hUV hx)).symm

end DifferentialGeometry.Homology
