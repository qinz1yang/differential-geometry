/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Manifold.SurfaceSegmentSmoothing
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Locus
import DifferentialGeometry.Topology.PlanarJordan.PlaneRectTube

open Set Metric
open scoped ContDiff Manifold

namespace Homeomorph

open Schoenflies (Plane)
open DifferentialGeometry.Topology.PlanarJordan

variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [T2Space M] [T2Space N] [ChartedSpace Plane M] [ChartedSpace Plane N]

theorem exists_smooth_segment_within (h : M ≃ₜ N)
    (a : PartialDiffeomorph 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) Plane M ∞)
    (b : PartialDiffeomorph 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) N Plane ∞)
    (has : ∀ t ∈ Icc (0 : ℝ) 1, Plane.mk t 0 ∈ a.source)
    (hbs : ∀ t ∈ Icc (0 : ℝ) 1, h (a (Plane.mk t 0)) ∈ b.source)
    (h0 : IsLocalDiffeomorphAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞ h (a (Plane.mk 0 0)))
    (h1 : IsLocalDiffeomorphAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞ h (a (Plane.mk 1 0)))
    {U : Set M} (hU : IsOpen U)
    (hsegment : ∀ t ∈ Ioo (0 : ℝ) 1, a (Plane.mk t 0) ∈ U) :
    ∃ K : Set M, IsCompact K ∧ K ⊆ U ∧ ∃ g : M ≃ₜ N,
      EqOn g h Kᶜ ∧ g '' K = h '' K ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        IsLocalDiffeomorphAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞ g (a (Plane.mk t 0))) ∧
      ∀ x ∉ K, IsLocalDiffeomorphAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞ h x →
        IsLocalDiffeomorphAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞ g x := by
  let L := a.source ∩ a ⁻¹' {x | IsLocalDiffeomorphAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞ h x}
  have hL : IsOpen L := a.toOpenPartialHomeomorph.isOpen_inter_preimage
    (isOpen_setOf_isLocalDiffeomorphAt _ _ _ h)
  let σ : ℝ → Plane := fun t => Plane.mk t 0
  let e : Plane ≃L[ℝ] ℝ × ℝ :=
    (EuclideanSpace.equiv (Fin 2) ℝ).trans (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)
  have hσ : Continuous σ := e.symm.continuous.comp (continuous_id.prodMk continuous_const)
  have h0L : σ 0 ∈ L := ⟨has 0 ⟨le_rfl, zero_le_one⟩, h0⟩
  have h1L : σ 1 ∈ L := ⟨has 1 ⟨zero_le_one, le_rfl⟩, h1⟩
  obtain ⟨r0, hr0, hball0⟩ := Metric.mem_nhds_iff.mp ((hL.preimage hσ).mem_nhds h0L)
  obtain ⟨r1, hr1, hball1⟩ := Metric.mem_nhds_iff.mp ((hL.preimage hσ).mem_nhds h1L)
  let η := min (1 / 8 : ℝ) (min r0 r1 / 4)
  have hη : 0 < η := lt_min (by norm_num) (div_pos (lt_min hr0 hr1) (by norm_num))
  have hη8 : η ≤ 1 / 8 := min_le_left _ _
  have hηr : η ≤ min r0 r1 / 4 := min_le_right _ _
  have hηr0 : η < r0 := by linarith [min_le_left r0 r1]
  have hηr1 : η < r1 := by linarith [min_le_right r0 r1]
  have hleft : ∀ t ∈ Icc (0 : ℝ) η, σ t ∈ L := by
    intro t ht
    apply hball0
    rw [mem_ball, Real.dist_eq, sub_zero, abs_lt]
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hright : ∀ t ∈ Icc (1 - η) (1 : ℝ), σ t ∈ L := by
    intro t ht
    apply hball1
    rw [mem_ball, Real.dist_eq, abs_lt]
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  obtain ⟨ra, hra, hballa⟩ := Metric.mem_nhds_iff.mp
    (hL.mem_nhds (hleft η ⟨hη.le, le_rfl⟩))
  obtain ⟨rb, hrb, hballb⟩ := Metric.mem_nhds_iff.mp
    (hL.mem_nhds (hright (1 - η) ⟨le_rfl, by linarith⟩))
  let O := a.source ∩ a ⁻¹' (U ∩ h ⁻¹' b.source)
  have hO : IsOpen O := a.toOpenPartialHomeomorph.isOpen_inter_preimage
    (hU.inter (b.open_source.preimage h.continuous))
  have haxis : ∀ t ∈ Icc (η / 2) (1 - η / 2), Plane.mk t 0 ∈ O := by
    intro t ht
    have ht01 : t ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    exact ⟨has t ht01, hsegment t ⟨by linarith [ht.1], by linarith [ht.2]⟩, hbs t ht01⟩
  obtain ⟨W, hW, hrect⟩ := exists_planeRect_subset_of_axis_subset hO haxis
  let ρ := min W (min ra (min rb (η / 8)))
  have hρ : 0 < ρ := lt_min hW (lt_min hra (lt_min hrb (div_pos hη (by norm_num))))
  have hρW : ρ ≤ W := min_le_left _ _
  have hρa : ρ ≤ ra := (min_le_right _ _).trans (min_le_left _ _)
  have hρb : ρ ≤ rb := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))
  have hρη : ρ ≤ η / 8 := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _))
  have hab : η + 2 * ρ < (1 - η) - 2 * ρ := by linarith
  let R := planeRect (η - 3 * ρ) ((1 - η) + 3 * ρ) (-W) W
  have hRO : R ⊆ O := by
    intro v hv
    apply hrect
    exact ⟨by linarith [hv.1], by linarith [hv.2.1], hv.2.2⟩
  have hends : IsLocalDiffeomorphOn 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞ h
      (a '' (ball (Plane.mk η 0) ρ ∪ ball (Plane.mk (1 - η) 0) ρ)) := by
    rintro ⟨x, v, hv, rfl⟩
    rcases hv with hv | hv
    · exact (hballa (ball_subset_ball hρa hv)).2
    · exact (hballb (ball_subset_ball hρb hv)).2
  have htail : ∀ t ∈ Icc (0 : ℝ) 1, t ≤ η ∨ 1 - η ≤ t →
      IsLocalDiffeomorphAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞ h (a (Plane.mk t 0)) := by
    intro t ht hend
    exact hend.elim (fun hl => (hleft t ⟨ht.1, hl⟩).2)
      (fun hr => (hright t ⟨hr, ht.2⟩).2)
  obtain ⟨g, hgout, hgimage, hgsmooth, hgpreserve⟩ := h.exists_smooth_segment_in_charts a b
    hρ hρW hab (fun _ hv => (hRO hv).1) (fun _ hv => (hRO hv).2.2) hends has htail
  refine ⟨a '' R, ?_, ?_, g, hgout, hgimage, hgsmooth, hgpreserve⟩
  · exact (isCompact_planeRect (by linarith) (by linarith)).image_of_continuousOn
      (a.toOpenPartialHomeomorph.continuousOn.mono (fun _ hv => (hRO hv).1))
  · rintro _ ⟨v, hv, rfl⟩
    exact (hRO hv).2.1

end Homeomorph
