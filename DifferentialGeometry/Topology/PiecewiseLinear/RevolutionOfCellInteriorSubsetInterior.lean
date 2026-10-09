/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.ClosedBall.Retraction
import DifferentialGeometry.Topology.OpenEmbeddingFrontier
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalConfiguration

open Set Topology Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

noncomputable section

private def planarProjection (p : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 2) :=
  EuclideanSpace.single 0 (p 0) + EuclideanSpace.single 1 (p 1)

private theorem planarProjection_apply_zero (p : EuclideanSpace ℝ (Fin 3)) :
    planarProjection p 0 = p 0 := by
  simp [planarProjection, PiLp.add_apply]

private theorem planarProjection_apply_one (p : EuclideanSpace ℝ (Fin 3)) :
    planarProjection p 1 = p 1 := by
  simp [planarProjection, PiLp.add_apply]

private theorem continuous_planarProjection : Continuous planarProjection := by
  have h : planarProjection = fun p : EuclideanSpace ℝ (Fin 3) =>
      WithLp.toLp 2 (fun i : Fin 2 => p i.castSucc) := by
    funext p
    apply PiLp.ext
    intro i
    fin_cases i <;> simp [planarProjection, PiLp.add_apply]
  rw [h]
  exact (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 2 => ℝ)).comp
    (continuous_pi fun i => continuous_euclideanApply i.castSucc)

private theorem planarProjection_injOn_plane :
    Set.InjOn planarProjection {p : EuclideanSpace ℝ (Fin 3) | p 2 = 0} := by
  intro p hp q hq hpq
  change p 2 = 0 at hp
  change q 2 = 0 at hq
  apply PiLp.ext
  intro i
  fin_cases i
  · change p 0 = q 0
    simpa only [planarProjection_apply_zero] using
      congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 0) hpq
  · change p 1 = q 1
    simpa only [planarProjection_apply_one] using
      congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 1) hpq
  · change p 2 = q 2
    exact hp.trans hq.symm

private def radialCoordinates (p : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 2) :=
  EuclideanSpace.single 0 (Real.sqrt (p 0 ^ 2 + p 2 ^ 2)) +
    EuclideanSpace.single 1 (p 1)

private theorem radialCoordinates_apply_zero (p : EuclideanSpace ℝ (Fin 3)) :
    radialCoordinates p 0 = Real.sqrt (p 0 ^ 2 + p 2 ^ 2) := by
  simp [radialCoordinates, PiLp.add_apply]

private theorem radialCoordinates_apply_one (p : EuclideanSpace ℝ (Fin 3)) :
    radialCoordinates p 1 = p 1 := by
  simp [radialCoordinates, PiLp.add_apply]

private theorem continuous_radialCoordinates : Continuous radialCoordinates := by
  have h : radialCoordinates = fun p : EuclideanSpace ℝ (Fin 3) =>
      WithLp.toLp 2 (fun i : Fin 2 =>
        if i = 0 then Real.sqrt (p 0 ^ 2 + p 2 ^ 2) else p i.castSucc) := by
    funext p
    apply PiLp.ext
    intro i
    fin_cases i <;> simp [radialCoordinates, PiLp.add_apply]
  rw [h]
  apply (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 2 => ℝ)).comp
  apply continuous_pi
  intro i
  fin_cases i
  · exact Real.continuous_sqrt.comp
      (((continuous_euclideanApply 0).pow 2).add ((continuous_euclideanApply 2).pow 2))
  · exact continuous_euclideanApply 1

theorem revolutionOf_cellInterior_subset_interior {D Dint : Set (EuclideanSpace ℝ (Fin 3))}
    (hD : IsTopologicalCellWithInterior 2 D Dint) (hhalf : ∀ q ∈ D, q 2 = 0 ∧ 0 < q 0) :
    revolutionOf Dint ⊆ interior (revolutionOf D) := by
  obtain ⟨φ, hDint⟩ := hD
  let r := DifferentialGeometry.Topology.ClosedBall.retraction
    (0 : EuclideanSpace ℝ (Fin 2)) (show (0 : ℝ) ≤ 1 by norm_num)
  let f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
    fun x => planarProjection (φ (r x))
  have hf : Continuous f := by
    dsimp [f]
    exact continuous_planarProjection.comp
      (continuous_subtype_val.comp (φ.continuous.comp r.continuous))
  have hinj : Set.InjOn f (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1) := by
    intro x hx y hy hxy
    have hxy' : planarProjection (φ (r x) : EuclideanSpace ℝ (Fin 3)) =
        planarProjection (φ (r y) : EuclideanSpace ℝ (Fin 3)) := hxy
    have hxr : (φ (r x) : EuclideanSpace ℝ (Fin 3)) 2 = 0 :=
      (hhalf (φ (r x)) (φ (r x)).property).1
    have hyr : (φ (r y) : EuclideanSpace ℝ (Fin 3)) 2 = 0 :=
      (hhalf (φ (r y)) (φ (r y)).property).1
    have hφ : φ (r x) = φ (r y) :=
      Subtype.ext (planarProjection_injOn_plane hxr hyr hxy')
    have hr : r x = r y := φ.injective hφ
    calc
      x = (r x : EuclideanSpace ℝ (Fin 2)) := by
        symm
        exact DifferentialGeometry.Topology.ClosedBall.retraction_apply_of_mem
          (0 : EuclideanSpace ℝ (Fin 2)) (by norm_num) (ball_subset_closedBall hx)
      _ = (r y : EuclideanSpace ℝ (Fin 2)) := congrArg Subtype.val hr
      _ = y := DifferentialGeometry.Topology.ClosedBall.retraction_apply_of_mem
        (0 : EuclideanSpace ℝ (Fin 2)) (by norm_num) (ball_subset_closedBall hy)
  let U := f '' Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1
  have hU : IsOpen U := by
    exact DifferentialGeometry.Topology.invariance_of_domain_open_map f
      (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1) isOpen_ball hf.continuousOn hinj
  let W := radialCoordinates ⁻¹' U
  have hW : IsOpen W := hU.preimage continuous_radialCoordinates
  intro p hp
  rcases hp with ⟨q, hqDint, hqplane, hqnonneg, hqone, hqsq⟩
  rw [hDint] at hqDint
  rcases hqDint with ⟨v, ⟨u, hu, huv⟩, hvq⟩
  have hφq : (φ u : EuclideanSpace ℝ (Fin 3)) = q := by
    calc
      (φ u : EuclideanSpace ℝ (Fin 3)) = v := congrArg Subtype.val huv
      _ = q := hvq
  change ‖(u : EuclideanSpace ℝ (Fin 2))‖ < 1 at hu
  have hu' : (u : EuclideanSpace ℝ (Fin 2)) ∈ Metric.ball 0 1 := by
    simpa only [mem_ball, dist_zero_right] using hu
  have hqhalf := hhalf (φ u) (φ u).property
  have hfu : f (u : EuclideanSpace ℝ (Fin 2)) = planarProjection (φ u) := by
    dsimp [f, r]
    rw [DifferentialGeometry.Topology.ClosedBall.retraction_coe]
  have hsqrt : Real.sqrt ((φ u : EuclideanSpace ℝ (Fin 3)) 0 ^ 2) =
      (φ u : EuclideanSpace ℝ (Fin 3)) 0 := by
    rw [Real.sqrt_sq_eq_abs, abs_of_pos hqhalf.2]
  have hradial : radialCoordinates p = f (u : EuclideanSpace ℝ (Fin 2)) := by
    apply PiLp.ext
    intro i
    fin_cases i
    · change radialCoordinates p 0 = f (u : EuclideanSpace ℝ (Fin 2)) 0
      rw [hfu, radialCoordinates_apply_zero, planarProjection_apply_zero, ← hqsq, ← hφq,
        hsqrt]
    · change radialCoordinates p 1 = f (u : EuclideanSpace ℝ (Fin 2)) 1
      rw [hfu, radialCoordinates_apply_one, planarProjection_apply_one, ← hqone, ← hφq]
  refine mem_interior.mpr ⟨W, ?_, hW, ?_⟩
  · intro z hz
    rcases hz with ⟨x, hx, hzx⟩
    refine ⟨(φ (r x) : EuclideanSpace ℝ (Fin 3)), (φ (r x)).property, ?_⟩
    have hplane := hhalf (φ (r x)) (φ (r x)).property
    constructor
    · exact hplane.1
    constructor
    · exact hplane.2.le
    constructor
    · have hcoord := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 1) hzx
      change f x 1 = radialCoordinates z 1 at hcoord
      simpa only [f, radialCoordinates_apply_one, planarProjection_apply_one] using hcoord
    · have hcoord := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 0) hzx
      change f x 0 = radialCoordinates z 0 at hcoord
      have hcoord' : (φ (r x) : EuclideanSpace ℝ (Fin 3)) 0 =
          Real.sqrt (z 0 ^ 2 + z 2 ^ 2) := by
        simpa only [f, radialCoordinates_apply_zero, planarProjection_apply_zero] using hcoord
      rw [hcoord', Real.sq_sqrt]
      positivity
  · change radialCoordinates p ∈ U
    exact ⟨u, hu', hradial.symm⟩

end

end DifferentialGeometry.Topology.PiecewiseLinear
