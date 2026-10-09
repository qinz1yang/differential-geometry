/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BallFrontier
import DifferentialGeometry.Topology.PiecewiseLinear.CrossingTraceCircles
import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedralTubeNeighborhoodExists

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem IsPseudoCell.exists_small_transverse_ball
    {Ec Eint Ebd : Set E3} {P : E3}
    (hE : IsPseudoCell Ec Eint Ebd P) {δ : ℝ} (hδ : 0 < δ) :
    ∃ Bl : Set E3, IsPLBall 3 Bl ∧ Bl ⊆ Metric.ball P δ ∧
      P ∈ interior Bl ∧ CrossesPseudoCell (frontier Bl) Ec Eint P := by
  classical
  have hbdc : IsClosed Ebd := by
    obtain ⟨φ⟩ := hE.isSphere
    exact (isCompact_iff_compactSpace.mpr φ.symm.compactSpace).isClosed
  have hPbd : P ∉ Ebd := Set.disjoint_left.mp hE.disjointRim hE.centerMem
  let V := Metric.ball P δ \ Ebd
  have hV : IsOpen V := Metric.isOpen_ball.sdiff hbdc
  have hPV : P ∈ V := ⟨Metric.mem_ball_self hδ, hPbd⟩
  obtain ⟨T, hT, hTcard, -, hTV, hTP⟩ :=
    exists_openSimplex_nhds 3 finrank_euclideanSpace_fin P (hV.mem_nhds hPV)
  let B₀ := convexHull ℝ (T : Set E3)
  have hB₀ : IsPLBall 3 B₀ := isPLBall_convexHull_of_affineIndependent T hT hTcard
  have hPB₀ : P ∈ interior B₀ := mem_interior_iff_mem_nhds.mpr hTP
  have hB₀c := hB₀.isPolyhedron.isCompact
  have hFrc : IsCompact (frontier B₀) :=
    hB₀c.of_isClosed_subset isClosed_frontier hB₀c.isClosed.frontier_subset
  let U := V \ {P}
  have hU : IsOpen U := hV.sdiff isClosed_singleton
  have hFrU : frontier B₀ ⊆ U := fun x hx =>
    ⟨hTV (hB₀c.isClosed.frontier_subset hx), fun hxP =>
      hx.2 ((mem_singleton_iff.mp hxP).symm ▸ hPB₀)⟩
  obtain ⟨ε, hε, hεU⟩ := hFrc.exists_cthickening_subset_open hU hFrU
  let Q := Ec ∩ Metric.cthickening ε (frontier B₀)
  have hQ : IsCompact Q := hFrc.cthickening.inter_left hE.isClosed
  have hQE : Q ⊆ Eint \ {P} := by
    rintro x ⟨hxE, hxε⟩
    have hxU := hεU hxε
    refine ⟨?_, hxU.2⟩
    rw [hE.carrierEq] at hxE
    exact hxE.resolve_right hxU.1.2
  obtain ⟨L, hLfin, hL, hLagree⟩ :=
    exists_isCombinatorialManifoldWithBoundary_two_eventually_mem_iff
      ({()} : Finset Unit) (M := fun _ => Eint) (P := fun _ => P) (Cc := fun _ => Q)
      (fun _ _ => hE.isOpenCell) (fun _ _ => hE.regular)
      (fun i _ j _ hij => (hij (Subsingleton.elim i j)).elim)
      (fun _ _ => hQ) (fun _ _ => hQE)
  have : Finite L.faces := hLfin.to_subtype
  obtain ⟨K, hKfin, hKspace⟩ := hB₀.isPLSphere_frontier.isPolyhedron.exists_simplicialComplex
  have : Finite K.faces := hKfin.to_subtype
  have hK : IsCombinatorialManifold 2 K :=
    IsPLSphere.isCombinatorialManifold (n := 1) (hKspace.symm ▸ hB₀.isPLSphere_frontier)
  obtain ⟨f, -, hf, hfε, hfix, -, -, -, hcross⟩ :=
    exists_small_homeomorph_generalPosition K L hK.isCombinatorialManifoldWithBoundary hL
      finrank_euclideanSpace_fin hU (hKspace.symm ▸ hFrU) hε
  have hfB := hf.restrict hB₀.isPolyhedron (subset_univ _)
  have hBl : IsPLBall 3 (f '' B₀) := hB₀.of_isPLHomeomorphOn hfB
  have hfr : f '' frontier B₀ = frontier (f '' B₀) :=
    hfB.image_frontier rfl hB₀c.isClosed hBl.isPolyhedron.isClosed
  have hBlV : f '' B₀ ⊆ V := by
    rintro _ ⟨y, hy, rfl⟩
    by_cases hyU : y ∈ U
    · by_contra hfy
      have hfyU : f y ∉ U := fun h => hfy h.1
      have hff : f (f y) = f y := hfix hfyU
      have hyy : f y = y := hf.bijOn.injOn (mem_univ _) (mem_univ _) hff
      exact hfyU (hyy.symm ▸ hyU)
    · rw [show f y = y from hfix hyU]
      exact hTV hy
  have hPBl : P ∈ interior (f '' B₀) := by
    rw [← hfB.image_interior rfl]
    exact ⟨P, hPB₀, hfix fun h => h.2 (mem_singleton P)⟩
  have htrace : frontier (f '' B₀) ∩ Ec ⊆ Eint \ {P} := by
    rintro x ⟨hxF, hxE⟩
    have hxV := hBlV (hBl.isPolyhedron.isClosed.frontier_subset hxF)
    refine ⟨?_, fun hxP => hxF.2 ((mem_singleton_iff.mp hxP).symm ▸ hPBl)⟩
    rw [hE.carrierEq] at hxE
    exact hxE.resolve_right hxV.2
  have hcrossI : ∀ x ∈ Eint ∩ frontier (f '' B₀),
      HasPLCrossingAt Eint (frontier (f '' B₀)) x := by
    rintro x ⟨hxI, hxF⟩
    have hxE : x ∈ Ec := hE.carrierEq.symm ▸ Or.inl hxI
    rw [← hfr] at hxF
    obtain ⟨y, hyF, rfl⟩ := hxF
    have hxQ : f y ∈ Q :=
      ⟨hxE, Metric.mem_cthickening_of_dist_le (f y) y ε _ hyF (hfε y).le⟩
    have hagree := hLagree () (by simp) (f y) hxQ
    have hxL : f y ∈ L.space := hagree.self_of_nhds.mpr hxI
    have hyK : y ∈ K.space := hKspace.symm ▸ hyF
    refine ((hcross (f y) ⟨⟨y, hyK, rfl⟩, hxL⟩).congr ?_ hagree).symm
    exact Filter.Eventually.of_forall fun z => by rw [hKspace, hfr]
  have hTeq : Eint ∩ frontier (f '' B₀) = Ec ∩ frontier (f '' B₀) := by
    ext x
    exact ⟨fun h => ⟨hE.carrierEq.symm ▸ Or.inl h.1, h.2⟩,
      fun h => ⟨(htrace ⟨h.2, h.1⟩).1, h.2⟩⟩
  have hTpoly : IsPolyhedron (Eint ∩ frontier (f '' B₀)) := by
    have hTc : IsCompact (Eint ∩ frontier (f '' B₀)) := by
      rw [hTeq]
      exact hBl.isPLSphere_frontier.isPolyhedron.isCompact.inter_left hE.isClosed
    apply IsLocallyPolyhedral.isPolyhedron_of_isCompact _ hTc
    have heq : Eint ∩ frontier (f '' B₀) =
        (Eint \ {P}) ∩ frontier (f '' B₀) := by
      ext x
      exact ⟨fun h => ⟨htrace ⟨h.2, hE.carrierEq.symm ▸ Or.inl h.1⟩, h.2⟩,
        fun h => ⟨h.1.1, h.2⟩⟩
    rw [heq]
    exact hE.regular.inter hBl.isPLSphere_frontier.isPolyhedron.isLocallyPolyhedral
  obtain ⟨ι, hιfin, G, hG, hGdisj, hGeq⟩ :=
    exists_iUnion_isPLSphere_one_of_forall_lineChart hTpoly hcrossI fun x hx =>
      (hcrossI x hx).exists_lineChart hx.1 (by
        obtain ⟨ψ⟩ := hE.isOpenCell
        exact ⟨univ, isOpen_univ, mem_univ _, Metric.ball 0 1, Metric.isOpen_ball,
          ⟨(Homeomorph.setCongr (univ_inter Eint)).trans ψ⟩⟩)
        hBl.isPolyhedron.isClosed
        (hBl.closure_interior.symm ▸ hBl.isPolyhedron.isClosed.frontier_subset hx.2)
  let : Finite ι := hιfin
  let : Fintype ι := Fintype.ofFinite ι
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have hGun : (⋃ i, G (e i)) = ⋃ j, G j := by
    ext x
    simp only [mem_iUnion]
    exact ⟨fun ⟨i, hi⟩ => ⟨e i, hi⟩, fun ⟨j, hj⟩ => ⟨e.symm j, by simpa using hj⟩⟩
  have hGtrace : frontier (f '' B₀) ∩ Ec = ⋃ i, G (e i) := by
    rw [hGun, ← hGeq, hTeq, inter_comm]
  refine ⟨f '' B₀, hBl, fun x hx => (hBlV hx).1, hPBl, Fintype.card ι,
    fun i => G (e i), fun i => hG (e i), fun i j hij => hGdisj (e.injective.ne hij),
    hGtrace, hGtrace ▸ htrace, ?_⟩
  intro x hx
  refine (hcrossI x ⟨(htrace hx).1, hx.1⟩).symm.congr
    (Filter.Eventually.of_forall fun _ => Iff.rfl) ?_
  filter_upwards [hbdc.isOpen_compl.mem_nhds (Set.disjoint_left.mp hE.disjointRim
    (htrace hx).1)] with y hy
  rw [hE.carrierEq]
  exact ⟨Or.inl, fun h => h.resolve_right hy⟩

end DifferentialGeometry.Topology.PiecewiseLinear
