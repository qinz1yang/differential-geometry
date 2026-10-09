/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.ClosedBallImage
import DifferentialGeometry.Topology.PiecewiseLinear.BicollarEmbedding
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactFaceEnvelopes
import DifferentialGeometry.Topology.Simplex.NormedBall

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem IsPLBall.isConnected_compl_image {P U : Set E3} (hP : IsPLBall 3 P)
    (hU : IsOpen U) {f : E3 → E3} (hf : ContinuousOn f U) (hinj : InjOn f U)
    (hPU : P ⊆ U) : IsConnected (f '' P)ᶜ := by
  obtain ⟨g, hg⟩ := id hP
  have hcell : IsTopologicalCell 3 P :=
    ⟨hg.homeomorph.symm.trans
      (DifferentialGeometry.Simplex.stdSimplexNormedBallHomeomorph
        (EuclideanSpace.equiv (Fin 3) ℝ).symm)⟩
  obtain ⟨φ⟩ := hcell.image_of_continuousOn_injOn (hf.mono hPU) (hinj.mono hPU)
  exact isConnected_compl_of_homeomorphClosedBall_of_isBicollared
    (by rw [← Module.finrank_eq_rank']; norm_num) φ
    (hP.isBicollared_frontier_image hU hf hinj hPU)

theorem IsPLBall.not_isBounded_connectedComponentIn_compl_of_subset_image
    {P U O : Set E3} (hP : IsPLBall 3 P) (hU : IsOpen U) {f : E3 → E3}
    (hf : ContinuousOn f U) (hinj : InjOn f U) (hPU : P ⊆ U) (hOP : O ⊆ f '' P)
    {y : E3} (hy : y ∉ f '' P) :
    ¬ Bornology.IsBounded (connectedComponentIn Oᶜ y) := by
  have hconn := hP.isConnected_compl_image hU hf hinj hPU
  have hsub : (f '' P)ᶜ ⊆ connectedComponentIn Oᶜ y :=
    hconn.isPreconnected.subset_connectedComponentIn hy (compl_subset_compl.mpr hOP)
  have hcpt : IsCompact (f '' P) :=
    hP.isPolyhedron.isCompact.image_of_continuousOn (hf.mono hPU)
  intro hb
  have huniv : Bornology.IsBounded (univ : Set E3) := by
    simpa only [union_compl_self] using hcpt.isBounded.union (hb.subset hsub)
  have hcptU : IsCompact (univ : Set E3) :=
    Metric.isCompact_iff_isClosed_bounded.mpr ⟨isClosed_univ, huniv⟩
  exact (not_compactSpace_iff.mpr (inferInstance : NoncompactSpace E3))
    (isCompact_univ_iff.mp hcptU)

end DifferentialGeometry.Topology.PiecewiseLinear
