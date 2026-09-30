/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CylindricalProduct
import DifferentialGeometry.Topology.PiecewiseLinear.CenteredDiskSimplexMap
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "Δ" => Convexity.StdSimplex.coordinateSet ℝ (Fin 3)
local notation "Disk" => Metric.closedBall (0 : E2) 1
local notation "Circle" => Metric.sphere (0 : E2) 1

theorem IsCylindricalDiagram.exists_homeomorph_closedBall_prod_sphere_of_eq_ends
    {S : Set F} {f : (Fin 3 → ℝ) × ℝ → F}
    (hf : IsCylindricalDiagram f Δ S)
    (hends : ∀ x ∈ Δ, f (x, 0) = f (x, 1)) :
    ∃ e : (Disk × Circle) ≃ₜ S,
      Subtype.val '' (e '' {z | (z.1 : E2) = 0}) =
        f '' ({stdCenter 1} ×ˢ Icc (0 : ℝ) 1) := by
  obtain ⟨q, hq⟩ := hf.exists_homeomorph_prod_circle_of_eq_ends
    (isPLBall_stdSimplex 2).isPolyhedron.isCompact hends
  obtain ⟨g, hgc, hgi, hgD, -, hg0⟩ :=
    exists_continuous_injective_image_closedBall_eq_stdSimplex
  let d : Disk → Δ := fun x => ⟨g x, hgD ▸ mem_image_of_mem g x.property⟩
  have hdc : Continuous d :=
    (hgc.comp continuous_subtype_val).subtype_mk _
  have hdb : Function.Bijective d := by
    constructor
    · intro x y hxy
      exact Subtype.ext (hgi (congrArg Subtype.val hxy))
    · intro y
      have hy : y.val ∈ g '' Disk := by rw [hgD]; exact y.property
      obtain ⟨x, hx, hxy⟩ := hy
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  let D : Disk ≃ₜ Δ :=
    Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective d hdb) hdc
  let c := Complex.orthonormalBasisOneI.repr
  have hc : Metric.sphere (0 : ℂ) 1 = c.toHomeomorph ⁻¹' Circle := by
    change _ = c ⁻¹' _
    rw [c.preimage_sphere, map_zero]
  let circle : loopCircle ≃ₜ Circle :=
    (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).trans
      (c.toHomeomorph.sets hc)
  let e : (Disk × Circle) ≃ₜ S :=
    (Homeomorph.prodCongr D circle.symm).trans q.symm
  refine ⟨e, ?_⟩
  ext y
  constructor
  · rintro ⟨z, ⟨w, hw, rfl⟩, rfl⟩
    obtain ⟨t, ht, htw⟩ := exists_lift_mem_Ico (circle.symm w.2)
    have hdw : (D w.1).val = stdCenter 1 := by
      change g (w.1 : E2) = stdCenter 1
      rw [hw, hg0]
    refine ⟨(stdCenter 1, t), ⟨rfl, ht.1, ht.2.le⟩, ?_⟩
    change f (stdCenter 1, t) = (q.symm (D w.1, circle.symm w.2) : F)
    rw [← htw, hq (D w.1) ⟨t, ht.1, ht.2.le⟩]
    exact congrArg (fun x : Fin 3 → ℝ => f (x, t)) hdw.symm
  · rintro ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
    change x = stdCenter 1 at hx
    subst x
    let z : Disk := ⟨0, by simp⟩
    have hDz : (D z).val = stdCenter 1 := hg0
    refine ⟨e (z, circle (t : loopCircle)), ?_, ?_⟩
    · exact ⟨(z, circle (t : loopCircle)), rfl, rfl⟩
    · change (q.symm (D z, circle.symm (circle (t : loopCircle))) : F) =
        f (stdCenter 1, t)
      rw [Homeomorph.symm_apply_apply, hq (D z) ⟨t, ht⟩]
      exact congrArg (fun x : Fin 3 → ℝ => f (x, t)) hDz

end DifferentialGeometry.Topology.PiecewiseLinear
