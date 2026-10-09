/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.LocalDegree.OpenDomain

open CategoryTheory Set

namespace DifferentialGeometry.LocalDegree

open DifferentialGeometry.Homology

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin (d + 1))
local notation "Z" => ModuleCat.of ℤ ℤ

theorem euclideanLocalDegree_sub_comp_of_injOn
    {U V : Set E} (hU : IsOpen U) (hV : IsOpen V)
    {f g : E → E} (hf : ContinuousOn f U) (hfi : InjOn f U)
    (hg : ContinuousOn g V) (hgi : InjOn g V) (hm : MapsTo f U V)
    {x : E} (hx : x ∈ U) :
    euclideanLocalDegree (fun z => g (f z) - g (f x)) x
        (isolatedZero_sub_of_injOn hU (hg.comp hf hm) (hgi.comp hfi hm) hx) =
      euclideanLocalDegree (fun z => f z - f x) x
          (isolatedZero_sub_of_injOn hU hf hfi hx) *
        euclideanLocalDegree (fun z => g z - g (f x)) (f x)
          (isolatedZero_sub_of_injOn hV hg hgi (hm hx)) := by
  let F : TopCat.of U ⟶ TopCat.of V :=
    TopCat.ofHom ⟨fun z => ⟨f z, hm z.2⟩, hf.domRestrict.subtype_mk _⟩
  let G : TopCat.of V ⟶ TopCat.of (univ : Set E) :=
    TopCat.ofHom ⟨fun z => ⟨g z, mem_univ _⟩, hg.domRestrict.subtype_mk _⟩
  have hFp : MapsTo F ({(⟨x, hx⟩ : U)}ᶜ : Set U)
      ({(⟨f x, hm hx⟩ : V)}ᶜ : Set V) := by
    intro z hz heq
    apply hz
    apply Subtype.ext
    exact hfi z.2 hx (congrArg (fun a : V => (a : E)) heq)
  have hGp : MapsTo G ({(⟨f x, hm hx⟩ : V)}ᶜ : Set V)
      ({(⟨g (f x), mem_univ _⟩ : (univ : Set E))}ᶜ : Set (univ : Set E)) := by
    intro z hz heq
    apply hz
    apply Subtype.ext
    exact hgi z.2 (hm hx) (congrArg (fun a : (univ : Set E) => (a : E)) heq)
  have hFdeg := euclideanLocalDegree_open_relativeHomology hU hV hf hfi hm hx
    F (fun _ => rfl) hFp
  have hGdeg := euclideanLocalDegree_open_relativeHomology hV isOpen_univ hg hgi
    (mapsTo_univ g V) (hm hx) G (fun _ => rfl) hGp
  have hGFdeg := euclideanLocalDegree_open_relativeHomology hU isOpen_univ
    (hg.comp hf hm) (hgi.comp hfi hm) (mapsTo_univ (g ∘ f) U) hx
    (F ≫ G) (fun _ => rfl) (hGp.comp hFp)
  have hcomp := relativeHomologyMap_comp Z F hFp G hGp (d + 1)
  have h := congrArg (fun q => q (euclideanOpenLocalGenerator hU x hx)) hcomp
  change relativeHomologyMap Z (F ≫ G) (hGp.comp hFp) (d + 1)
    (euclideanOpenLocalGenerator hU x hx) =
      relativeHomologyMap Z G hGp (d + 1)
        (relativeHomologyMap Z F hFp (d + 1) (euclideanOpenLocalGenerator hU x hx)) at h
  rw [hGFdeg, hFdeg, map_zsmul, hGdeg, smul_smul] at h
  exact euclideanOpenLocalGenerator_smul_injective isOpen_univ
    (g (f x)) (mem_univ _) h

end DifferentialGeometry.LocalDegree
