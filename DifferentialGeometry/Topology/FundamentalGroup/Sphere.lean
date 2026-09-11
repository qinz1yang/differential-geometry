/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Geometry.Manifold.Instances.Sphere
import DifferentialGeometry.Topology.FundamentalGroup.Circle
import DifferentialGeometry.Topology.VanKampen.SimplyConnectedUnion

set_option autoImplicit false

open Metric Module Set
open scoped RealInnerProductSpace

universe u

namespace DifferentialGeometry.Topology

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def sphereComplPointHomeomorph (v : E) (hv : ‖v‖ = 1) :
    ({⟨v, by simp [hv]⟩}ᶜ : Set (sphere (0 : E) 1)) ≃ₜ (ℝ ∙ v)ᗮ := by
  rw [← stereographic_source hv]
  exact (stereographic hv).toHomeomorphSourceTarget.trans (Homeomorph.Set.univ _)

theorem simplyConnectedSpace_sphere_compl_point (v : E) (hv : ‖v‖ = 1) :
    SimplyConnectedSpace ({⟨v, by simp [hv]⟩}ᶜ : Set (sphere (0 : E) 1)) := by
  exact (sphereComplPointHomeomorph v hv).toHomotopyEquiv.simplyConnectedSpace

noncomputable def sphereComplAntipodesHomeomorph (v : E) (hv : ‖v‖ = 1) :
    (({⟨v, by simp [hv]⟩}ᶜ ∩ {⟨-v, by simp [hv]⟩}ᶜ) :
      Set (sphere (0 : E) 1)) ≃ₜ ({0}ᶜ : Set ((ℝ ∙ v)ᗮ)) :=
  (stereographic hv).homeomorphOfImageSubsetSource (fun _ hx ↦ hx.1) <| by
    ext w
    constructor
    · rintro ⟨x, hx, rfl⟩ hzero
      have hzero' : stereographic hv x = 0 := by simpa using hzero
      have hneg : (⟨-v, by simp [hv]⟩ : sphere (0 : E) 1) = -⟨v, by simp [hv]⟩ := by
        apply Subtype.ext
        rfl
      have hstereoSouth :
          stereographic hv (⟨-v, by simp [hv]⟩ : sphere (0 : E) 1) = 0 := by
        rw [hneg]
        exact stereographic_apply_neg ⟨v, by simp [hv]⟩
      have hsouth : (⟨-v, by simp [hv]⟩ : sphere (0 : E) 1) ∈
          (stereographic hv).source := by
        rw [stereographic_source]
        simp only [mem_compl_iff, mem_singleton_iff]
        intro h
        have hval : -v = v := congrArg Subtype.val h
        have htwo : (2 : ℝ) • v = 0 := by
          rw [two_smul]
          exact neg_eq_iff_add_eq_zero.mp hval
        have hvzero : v = 0 := (smul_eq_zero.mp htwo).resolve_left (by norm_num)
        simp [hvzero] at hv
      have hxeq : x = ⟨-v, by simp [hv]⟩ := by
        exact (stereographic hv).injOn hx.1 hsouth (by
          rw [hzero']
          exact hstereoSouth.symm)
      exact hx.2 hxeq
    · intro hw
      let w' : (stereographic hv).target := ⟨w, by simp⟩
      let x : sphere (0 : E) 1 := (stereographic hv).symm w'
      have hxsource : x ∈ (stereographic hv).source :=
        (stereographic hv).map_target w'.property
      have hmap : stereographic hv x = w := by
        change stereographic hv ((stereographic hv).symm w') = w
        exact (stereographic hv).right_inv w'.property
      refine ⟨x, ⟨hxsource, ?_⟩, hmap⟩
      intro hxsouth
      have : w = 0 := by
        rw [← hmap, hxsouth]
        have hneg : (⟨-v, by simp [hv]⟩ : sphere (0 : E) 1) = -⟨v, by simp [hv]⟩ := by
          apply Subtype.ext
          rfl
        rw [hneg]
        exact stereographic_apply_neg ⟨v, by simp [hv]⟩
      exact hw this

theorem simplyConnectedSpace_sphere_of_orthogonal_rank_gt_one
    (v : E) (hv : ‖v‖ = 1) (horth : 1 < Module.rank ℝ ((ℝ ∙ v)ᗮ)) :
    SimplyConnectedSpace (sphere (0 : E) 1) := by
  let north : sphere (0 : E) 1 := ⟨v, by simp [hv]⟩
  let south : sphere (0 : E) 1 := ⟨-v, by simp [hv]⟩
  let U : Set (sphere (0 : E) 1) := {north}ᶜ
  let V : Set (sphere (0 : E) 1) := {south}ᶜ
  have hnorth_ne_south : north ≠ south := by
    intro h
    have hval : v = -v := congrArg Subtype.val h
    have htwo : (2 : ℝ) • v = 0 := by
      rw [two_smul]
      exact eq_neg_iff_add_eq_zero.mp hval
    have hvzero : v = 0 := (smul_eq_zero.mp htwo).resolve_left (by norm_num)
    simp [hvzero] at hv
  have hU : IsOpen U := isOpen_compl_singleton
  have hV : IsOpen V := isOpen_compl_singleton
  have hcover : U ∪ V = univ := by
    ext x
    simp only [U, V, mem_union, mem_compl_iff, mem_singleton_iff, mem_univ, iff_true]
    by_contra h
    rw [not_or] at h
    exact hnorth_ne_south ((not_ne_iff.mp h.1).symm.trans (not_ne_iff.mp h.2))
  let _ : SimplyConnectedSpace U := by
    simpa only [U, north] using simplyConnectedSpace_sphere_compl_point v hv
  have hvneg : ‖-v‖ = 1 := by simpa using hv
  let _ : SimplyConnectedSpace V := by
    simpa only [V, south, north] using simplyConnectedSpace_sphere_compl_point (-v) hvneg
  let e : ↑(U ∩ V) ≃ₜ ({0}ᶜ : Set ((ℝ ∙ v)ᗮ)) := by
    simpa only [U, V, north, south] using sphereComplAntipodesHomeomorph v hv
  have htarget : IsPathConnected ({0}ᶜ : Set ((ℝ ∙ v)ᗮ)) :=
    isPathConnected_compl_singleton_of_one_lt_rank horth 0
  let _ : PathConnectedSpace ({0}ᶜ : Set ((ℝ ∙ v)ᗮ)) :=
    isPathConnected_iff_pathConnectedSpace.mp htarget
  let _ : PathConnectedSpace (↑(U ∩ V)) :=
    e.symm.surjective.pathConnectedSpace e.symm.continuous
  let w₀ : ({0}ᶜ : Set ((ℝ ∙ v)ᗮ)) := Classical.choice inferInstance
  let x₀ : sphere (0 : E) 1 := (e.symm w₀).1
  have hx₀ : x₀ ∈ U ∩ V := (e.symm w₀).2
  exact DifferentialGeometry.Topology.VanKampen.simplyConnectedSpace_of_open_cover
    U V hU hV hcover x₀ hx₀

abbrev SphereTwo := sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

noncomputable abbrev sphereTwoNorthVector : EuclideanSpace ℝ (Fin 3) :=
  EuclideanSpace.single 0 1

theorem norm_sphereTwoNorthVector : ‖sphereTwoNorthVector‖ = 1 := by
  simp [sphereTwoNorthVector]

theorem one_lt_rank_sphereTwoNorthOrthogonal :
    1 < Module.rank ℝ ((ℝ ∙ sphereTwoNorthVector)ᗮ) := by
  let _ : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  have hnonzero : sphereTwoNorthVector ≠ 0 := by
    simp [sphereTwoNorthVector]
  have hfin : Module.finrank ℝ ((ℝ ∙ sphereTwoNorthVector)ᗮ) = 2 :=
    Submodule.finrank_orthogonal_span_singleton (n := 2) hnonzero
  rw [← Module.finrank_eq_rank']
  simp [hfin]

instance sphereTwoSimplyConnectedSpace : SimplyConnectedSpace SphereTwo :=
  simplyConnectedSpace_sphere_of_orthogonal_rank_gt_one sphereTwoNorthVector
    norm_sphereTwoNorthVector one_lt_rank_sphereTwoNorthOrthogonal

noncomputable def sphereTwoNorth : SphereTwo :=
  ⟨sphereTwoNorthVector, by simp⟩

noncomputable def fundamentalGroupSphereTwoProdCircleEquivInt :
    FundamentalGroup (SphereTwo × Circle) (sphereTwoNorth, 1) ≃* Multiplicative ℤ :=
  fundamentalGroupProdCircleEquivIntOfSimplyConnected sphereTwoNorth

abbrev SphereThree := sphere (0 : EuclideanSpace ℝ (Fin 4)) 1

noncomputable abbrev sphereThreeNorthVector : EuclideanSpace ℝ (Fin 4) :=
  EuclideanSpace.single 0 1

theorem norm_sphereThreeNorthVector : ‖sphereThreeNorthVector‖ = 1 := by
  simp [sphereThreeNorthVector]

theorem one_lt_rank_sphereThreeNorthOrthogonal :
    1 < Module.rank ℝ ((ℝ ∙ sphereThreeNorthVector)ᗮ) := by
  let _ : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) := ⟨by simp⟩
  have hnonzero : sphereThreeNorthVector ≠ 0 := by
    simp [sphereThreeNorthVector]
  have hfin : Module.finrank ℝ ((ℝ ∙ sphereThreeNorthVector)ᗮ) = 3 :=
    Submodule.finrank_orthogonal_span_singleton (n := 3) hnonzero
  rw [← Module.finrank_eq_rank']
  simp [hfin]

instance sphereThreeSimplyConnectedSpace : SimplyConnectedSpace SphereThree :=
  simplyConnectedSpace_sphere_of_orthogonal_rank_gt_one sphereThreeNorthVector
    norm_sphereThreeNorthVector one_lt_rank_sphereThreeNorthOrthogonal

noncomputable def sphereThreeNorth : SphereThree :=
  ⟨sphereThreeNorthVector, by simp⟩

end DifferentialGeometry.Topology
