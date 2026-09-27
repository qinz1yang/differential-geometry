/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Homology.Local.OpenGenerator
import DifferentialGeometry.Topology.LocalDegree.InjectiveUnit

open CategoryTheory CategoryTheory.Limits Set Metric Filter
open scoped Topology

namespace DifferentialGeometry.LocalDegree

open DifferentialGeometry.Homology

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin (d + 1))
local notation "Z" => ModuleCat.of ℤ ℤ

theorem euclideanLocalDegree_open_relativeHomology
    {U V : Set E} (hU : IsOpen U) (hV : IsOpen V)
    {f : E → E} (hf : ContinuousOn f U) (hinj : InjOn f U)
    (hm : MapsTo f U V) {x : E} (hx : x ∈ U)
    (F : TopCat.of U ⟶ TopCat.of V) (hF : ∀ z : U, (F z : E) = f z)
    (hFp : MapsTo F ({(⟨x, hx⟩ : U)}ᶜ : Set U)
      ({(⟨f x, hm hx⟩ : V)}ᶜ : Set V)) :
    relativeHomologyMap Z F hFp (d + 1) (euclideanOpenLocalGenerator hU x hx) =
      euclideanLocalDegree (fun z => f z - f x) x
          (isolatedZero_sub_of_injOn hU hf hinj hx) •
        euclideanOpenLocalGenerator hV (f x) (hm hx) := by
  obtain ⟨r, hr, hrU⟩ := nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hx)
  have hrU' : ball x r ⊆ U := ball_subset_closedBall.trans hrU
  have hR := isolatingRadius_sub_of_injOn hf hinj hr hrU
  let j : TopCat.of (ball x r) ⟶ TopCat.of U :=
    TopCat.ofHom ⟨fun z => ⟨z, hrU' z.2⟩, continuous_subtype_val.subtype_mk _⟩
  have hj : MapsTo j ({(⟨x, mem_ball_self hr⟩ : ball x r)}ᶜ : Set (ball x r))
      ({(⟨x, hx⟩ : U)}ᶜ : Set U) := by
    intro z hz heq
    apply hz
    apply Subtype.ext
    change j z = (⟨x, hx⟩ : U) at heq
    exact congrArg (fun a : U => (a : E)) heq
  let iV := puncturedNeighborhoodHomologyIso (TopCat.of E) V (f x) (hm hx) Z hV (d + 1)
  let t := localTranslationHomologyIso E (f x) Z (d + 1)
  let v : TopCat.of V ⟶ TopCat.of E :=
    TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  have hvp : MapsTo v ({(⟨f x, hm hx⟩ : V)}ᶜ : Set V) ({f x}ᶜ : Set E) :=
    puncturedNeighborhood_mapsTo (TopCat.of E) V (f x) (hm hx)
  let tmap : TopCat.of E ⟶ TopCat.of E :=
    TopCat.ofHom ⟨fun z => z - f x, continuous_id.sub continuous_const⟩
  have htp : MapsTo tmap ({f x}ᶜ : Set E) ({0}ᶜ : Set E) :=
    fun z hz => sub_ne_zero.mpr hz
  have hvmap : iV.hom ≫ t.hom =
      relativeHomologyMap Z (v ≫ tmap) (htp.comp hvp) (d + 1) := by
    exact (relativeHomologyMap_comp Z v hvp tmap htp (d + 1)).symm
  have hFmap := relativeHomologyMap_comp Z F hFp (v ≫ tmap) (htp.comp hvp) (d + 1)
  have hjmap := relativeHomologyMap_comp Z j hj (F ≫ v ≫ tmap)
    ((htp.comp hvp).comp hFp) (d + 1)
  have hcomp : relativeHomologyMap Z j hj (d + 1) ≫
      relativeHomologyMap Z F hFp (d + 1) ≫ iV.hom ≫ t.hom =
        hR.relativeHomologyMap Z (d + 1) := by
    rw [hvmap, ← hFmap, ← hjmap, hR.relativeHomologyMap_eq]
    congr 1
    apply TopCat.ext
    intro z
    change (F (j z) : E) - f x = f z - f x
    rw [hF]
    rfl
  have hjgen : relativeHomologyMap Z j hj (d + 1)
      (euclideanBallLocalGenerator x r hr) = euclideanOpenLocalGenerator hU x hx := by
    rw [← euclideanOpenLocalGenerator_ball]
    exact euclideanOpenLocalGenerator_map_inclusion isOpen_ball hU hrU' x
      (mem_ball_self hr) j (fun _ => rfl) hj
  have hvgen : (iV.hom ≫ t.hom) (euclideanOpenLocalGenerator hV (f x) (hm hx)) =
      euclideanLocalGenerator d := by
    change t.hom (iV.hom (euclideanOpenLocalGenerator hV (f x) (hm hx))) = _
    rw [euclideanOpenLocalGenerator_inclusion, euclideanLocalGeneratorAt_translate]
  apply (ModuleCat.mono_iff_injective (iV.hom ≫ t.hom)).mp inferInstance
  rw [map_zsmul, hvgen]
  have heq := congrArg (fun q => q (euclideanBallLocalGenerator x r hr)) hcomp
  change (iV.hom ≫ t.hom)
    (relativeHomologyMap Z F hFp (d + 1)
      (relativeHomologyMap Z j hj (d + 1) (euclideanBallLocalGenerator x r hr))) = _ at heq
  rw [hjgen, euclideanLocalDegree_relativeHomology] at heq
  exact heq

end DifferentialGeometry.LocalDegree
