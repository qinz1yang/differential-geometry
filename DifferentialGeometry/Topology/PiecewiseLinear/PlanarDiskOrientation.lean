/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.DiskLocalDegreeOrientation
import DifferentialGeometry.Topology.PiecewiseLinear.DiskCrosscut
import DifferentialGeometry.Topology.PiecewiseLinear.JordanDiskPasting
import DifferentialGeometry.Topology.LocalDegree.HomeomorphConjugation

open Set Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

open DifferentialGeometry.LocalDegree

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "D1" => closedBall (0 : Plane) 1
local notation "B1" => ball (0 : Plane) 1
local notation "S1" => sphere (0 : Plane) 1

theorem isPLCirclePositive_frontier_iff_orientationParity_eq_zero
    {P : Set Plane} (hP : IsPLBall 2 P) {f : Plane → Plane}
    (hf : ContinuousOn f P) (hfi : InjOn f P)
    (hB : MapsTo f (interior P) (interior P)) (hS : BijOn f (frontier P) (frontier P))
    {x : Plane} (hx : x ∈ interior P) :
    IsPLCirclePositive (frontier P) f ↔
      embeddingOrientationParity isOpen_interior (hf.mono interior_subset)
        (hfi.mono interior_subset) ⟨x, hx⟩ = 0 := by
  obtain ⟨e, heS, heP, heB⟩ := exists_homeomorph_image_closure_inside_eq_closedBall
    (isJordanCurve_of_isPLSphere_one hP.isPLSphere_frontier)
  rw [← hP.interior_eq_inside_frontier, hP.closure_interior] at heP
  rw [← hP.interior_eq_inside_frontier] at heB
  have hback (T T' : Set Plane) (hTT' : e '' T = T') : MapsTo e.symm T' T := by
    rintro y hy
    obtain ⟨z, hz, rfl⟩ := hTT'.symm.subset hy
    rwa [e.symm_apply_apply]
  have hPS : BijOn e (frontier P) S1 := by
    rw [← heS]
    exact e.injective.injOn.bijOn_image
  have hSP : BijOn e.symm S1 (frontier P) :=
    ⟨hback _ _ heS, e.symm.injective.injOn,
      fun z hz => ⟨e z, hPS.mapsTo hz, e.symm_apply_apply z⟩⟩
  let g : Plane → Plane := e ∘ f ∘ e.symm
  have hg : ContinuousOn g D1 := e.continuous.comp_continuousOn
    (hf.comp e.symm.continuous.continuousOn (hback _ _ heP))
  have hgi : InjOn g D1 := fun y hy z hz hyz =>
    e.symm.injective (hfi (hback _ _ heP hy) (hback _ _ heP hz) (e.injective hyz))
  have hgB : MapsTo g B1 B1 := by
    intro y hy
    rw [← heB]
    exact ⟨f (e.symm y), hB (hback _ _ heB hy), rfl⟩
  have hgS : BijOn g S1 S1 := hPS.comp (hS.comp hSP)
  have hyB : e x ∈ B1 := heB ▸ mem_image_of_mem e hx
  have hpos : IsPLCirclePositive (frontier P) f ↔ IsPLCirclePositive S1 g := by
    constructor
    · intro hp
      have hp' := hp.conj hS.mapsTo e.continuous.continuousOn hPS
      apply hp'.of_eqOn
      intro y hy
      have hi : Function.invFunOn e (frontier P) y = e.symm y :=
        e.injective ((hPS.invOn_invFunOn.2 hy).trans (e.apply_symm_apply y).symm)
      exact congrArg (fun z => e (f z)) hi.symm
    · intro hp
      have hp' := hp.conj hgS.mapsTo e.symm.continuous.continuousOn hSP
      apply hp'.of_eqOn
      intro y hy
      have hi : Function.invFunOn e.symm S1 y = e y :=
        e.symm.injective ((hSP.invOn_invFunOn.2 hy).trans (e.symm_apply_apply y).symm)
      simp only [Function.comp_apply, hi, g, e.symm_apply_apply]
  have hgV : ContinuousOn g (e.symm ⁻¹' interior P) :=
    e.continuous.comp_continuousOn
      ((hf.mono interior_subset).comp e.symm.continuous.continuousOn (fun _ hz => hz))
  have hgiV : InjOn g (e.symm ⁻¹' interior P) := fun y hy z hz hyz =>
    e.symm.injective (hfi (interior_subset hy) (interior_subset hz) (e.injective hyz))
  have hyV : e x ∈ e.symm ⁻¹' interior P := by
    simpa only [mem_preimage, e.symm_apply_apply] using hx
  have hconj : embeddingOrientationParity (isOpen_interior.preimage e.symm.continuous)
      hgV hgiV ⟨e x, hyV⟩ =
      embeddingOrientationParity isOpen_interior (hf.mono interior_subset)
        (hfi.mono interior_subset) ⟨x, hx⟩ :=
    embeddingOrientationParity_conj_homeomorph e isOpen_interior
      (hf.mono interior_subset) (hfi.mono interior_subset) ⟨x, hx⟩
  have hrestrict := embeddingOrientationParity_congr isOpen_ball
    (isOpen_interior.preimage e.symm.continuous)
    (hg.mono ball_subset_closedBall) (hgi.mono ball_subset_closedBall)
    hgV hgiV hyB hyV Filter.EventuallyEq.rfl
  have hround := (isPLCirclePositive_iff_localDegree_sub_eq_one hg hgi hgB hgS hyB).trans
    (embeddingOrientationParity_eq_zero_iff isOpen_ball
      (hg.mono ball_subset_closedBall) (hgi.mono ball_subset_closedBall) ⟨e x, hyB⟩).symm
  rw [hpos, hround, hrestrict, hconj]

end DifferentialGeometry.Topology.PiecewiseLinear
