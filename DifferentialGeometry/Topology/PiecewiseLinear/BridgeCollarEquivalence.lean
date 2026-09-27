/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BridgeCollarSweep
import DifferentialGeometry.Topology.PiecewiseLinear.BridgeDiskTransport
import DifferentialGeometry.Topology.PiecewiseLinear.CollarShellExtension

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem exists_isPLHomeomorphOn_eqOn_boundary_map_bridge_arc_of_collars
    {C A B W D A' B' Z : Set E3} {a b a' b' : E3}
    (hC : IsPLBall 3 C) (hD : IsPLBall 3 D)
    (hbridge : IsBridgeDisk C A B a b) (hbridge' : IsBridgeDisk D A' B' a' b')
    {c d : E3 × ℝ → E3}
    (hc : IsPLHomeomorphOn c (frontier C ×ˢ Icc (0 : ℝ) 2) W)
    (hd : IsPLHomeomorphOn d (frontier D ×ˢ Icc (0 : ℝ) 2) Z)
    (hWC : W ⊆ C) (hZD : Z ⊆ D)
    (hc0 : ∀ x ∈ frontier C, c (x, 0) = x)
    (hd0 : ∀ y ∈ frontier D, d (y, 0) = y)
    (hcB : B ∩ W = c '' ((B ∩ frontier C) ×ˢ Icc (0 : ℝ) 2))
    (hdB : B' ∩ Z = d '' ((B' ∩ frontier D) ×ˢ Icc (0 : ℝ) 2))
    {f : E3 → E3} (hf : IsPLHomeomorphOn f (frontier C) (frontier D))
    (hfβ : f '' (B ∩ frontier C) = B' ∩ frontier D) :
    ∃ G : E3 → E3, IsPLHomeomorphOn G C D ∧ EqOn G f (frontier C) ∧ G '' A = A' := by
  obtain ⟨e, he, -, hefront, heC, hebridge⟩ :=
    hbridge.exists_isPLHomeomorphOn_to_collar_ribbon hC.isPolyhedron hc hc0 hcB
  obtain ⟨e', he', -, hefront', heD, hebridge'⟩ :=
    hbridge'.exists_isPLHomeomorphOn_to_collar_ribbon hD.isPolyhedron hd hd0 hdB
  obtain ⟨F, hF, hFf, hFcd⟩ :=
    exists_isPLHomeomorphOn_eq_on_collars hC hD hc hd hWC hZD hc0 hd0 hf
  have hFribbon : F '' (c '' ((B ∩ frontier C) ×ˢ Icc (0 : ℝ) 1)) =
      d '' ((B' ∩ frontier D) ×ˢ Icc (0 : ℝ) 1) := by
    apply Subset.antisymm
    · rintro _ ⟨_, ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩, rfl⟩
      exact ⟨(f x, t), ⟨hfβ.subset ⟨x, hx, rfl⟩, ht⟩, (hFcd x hx.2 t ht).symm⟩
    · rintro _ ⟨⟨y, t⟩, ⟨hy, ht⟩, rfl⟩
      obtain ⟨x, hx, rfl⟩ := hfβ.symm.subset hy
      exact ⟨c (x, t), ⟨(x, t), ⟨hx, ht⟩, rfl⟩, hFcd x hx.2 t ht⟩
  have hFarc : F '' (e '' A) = e' '' A' := by
    have hnew := hebridge.image hF rfl hC.isPolyhedron.isClosed hD.isPolyhedron.isClosed
    rw [hFribbon] at hnew
    exact hnew.arc_eq hebridge'
  have heCpl : IsPLHomeomorphOn e C C := by
    have h := he.restrict hC.isPolyhedron (subset_univ C)
    rwa [heC] at h
  have heDpl : IsPLHomeomorphOn e' D D := by
    have h := he'.restrict hD.isPolyhedron (subset_univ D)
    rwa [heD] at h
  let v := Function.invFunOn e' D
  have hleft : ∀ y ∈ D, v (e' y) = y := fun _ hy => heDpl.bijOn.invOn_invFunOn.1 hy
  have hvA : v '' (e' '' A') = A' := by
    rw [image_image]
    exact (show EqOn (v ∘ e') id A' from
      fun y hy => hleft y (hbridge'.subset hy)).image_eq.trans (image_id _)
  refine ⟨v ∘ F ∘ e, (heCpl.trans hF).trans heDpl.symm, ?_, ?_⟩
  · intro x hx
    change v (F (e x)) = f x
    rw [hefront hx, id_eq, hFf hx]
    have hy := hf.bijOn.mapsTo hx
    simpa only [hefront' hy, id_eq] using
      hleft (f x) (hD.isPolyhedron.isClosed.frontier_subset hy)
  · rw [image_comp, image_comp, hFarc, hvA]

end DifferentialGeometry.Topology.PiecewiseLinear
