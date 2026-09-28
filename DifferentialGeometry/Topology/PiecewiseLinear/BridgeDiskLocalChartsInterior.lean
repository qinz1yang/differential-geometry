/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BridgeDiskLocalCharts

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem IsBridgeDisk.exists_conical_frontier_model
    {C A B : Set E} {a b x : E} (h : IsBridgeDisk C A B a b)
    (hdim : Module.finrank ℝ E = 3) (hC : IsPLBall 3 C)
    (hxβ : x ∈ B ∩ frontier C) (hxends : x ∉ ({a, b} : Set E)) :
    ∃ (S : Geometry.SimplicialComplex ℝ E) (D J : Set E)
      (r : (Fin 3 → ℝ) → E) (η : ℝ → E),
      S.faces.Finite ∧ IsConeBase x S ∧ IsPLSphere 2 S.space ∧ coneSet x S.space ∈ 𝓝 x ∧
      D ⊆ S.space ∧ IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D ∧
      IsPLHomeomorphOn η (Icc 0 1) J ∧ J ⊆ D ∧
      J ∩ (r '' stdSimplexBoundary 2) = {η 0, η 1} ∧
      (∀ᶠ z in 𝓝 x, z ∈ coneSet x D ↔ z ∈ C) ∧
      (∀ᶠ z in 𝓝 x, z ∈ coneSet x (r '' stdSimplexBoundary 2) ↔ z ∈ frontier C) ∧
      (∀ᶠ z in 𝓝 x, z ∈ coneSet x J ↔ z ∈ B) ∧
      (∀ᶠ z in 𝓝 x, z ∈ segment ℝ x (η 0) ∪ segment ℝ x (η 1) ↔
        z ∈ B ∩ frontier C) ∧ Aᶜ ∈ 𝓝 x := by
  obtain ⟨T, hTfin, hCT, hTC, hTB, hTA, hTβ, _, _, hxT⟩ :=
    h.exists_compatible_triangulation hC.isPolyhedron hxβ
  let _ : Finite T.faces := hTfin.to_subtype
  let K := restrict T C
  let L := restrict T B
  let M := restrict T A
  let R := restrict T (B ∩ frontier C)
  let _ : Finite K.faces := (restrict_faces_finite T C).to_subtype
  let _ : Finite L.faces := (restrict_faces_finite T B).to_subtype
  let _ : Finite M.faces := (restrict_faces_finite T A).to_subtype
  let _ : Finite R.faces := (restrict_faces_finite T (B ∩ frontier C)).to_subtype
  obtain ⟨hS, hD, hJ, hJD, htrace, _, _, _, hinner⟩ := h.geometricLink_traces hdim hC
    T K L M R (restrict_faces_subset T C) (restrict_faces_subset T B)
    (restrict_faces_subset T A) (restrict_faces_subset T (B ∩ frontier C))
    hTC hTB hTA hTβ hCT hxT hxβ
  obtain ⟨_, hRbd⟩ := hinner hxends
  obtain ⟨η, hη⟩ := exists_isPLHomeomorphOn_Icc_of_isPLBall_one hJ
  have hηbd := boundaryComplex_space_of_parametrized_Icc
    (SimplicialComplex.geometricLink L {x}) zero_lt_one hη
  obtain ⟨r, hr⟩ := hD
  have hrbd := hr.image_stdSimplexBoundary_eq_boundaryComplex
    (SimplicialComplex.geometricLink K {x}) rfl
  have hcopy := h
  obtain ⟨q, hq, hBC, _, _, _, _⟩ := hcopy
  have hxK : {x} ∈ K.faces := ⟨hxT, by simpa using hBC hxβ.1⟩
  have hxL : {x} ∈ L.faces := ⟨hxT, by simpa using hxβ.1⟩
  have hxR : {x} ∈ R.faces := ⟨hxT, by simpa using hxβ⟩
  have hK : IsPLBall 3 K.space := hTC.symm ▸ hC
  have hfront : (boundaryComplex 3 K).space = frontier C := by
    rw [← frontier_space_eq_boundaryComplex_space_of_finrank hdim K
      hK.isCombinatorialManifoldWithBoundary, hTC]
  have hxfrontK : {x} ∈ (boundaryComplex 3 K).faces := by
    by_contra hnot
    exact notMem_space_of_notMem_faces (boundaryComplex_faces_subset 3 K) hxK hnot
      (mem_openSimplex_singleton x) (hfront.symm ▸ hxβ.2)
  have hsegR : coneSet x (SimplicialComplex.geometricLink R {x}).space =
      segment ℝ x (η 0) ∪ segment ℝ x (η 1) := by
    rw [hRbd, hηbd, coneSet_eq_iUnion_segment (show ({η 0, η 1} : Set E).Nonempty from
      ⟨η 0, Or.inl rfl⟩), biUnion_pair]
  refine ⟨SimplicialComplex.geometricLink T {x},
    (SimplicialComplex.geometricLink K {x}).space,
    (SimplicialComplex.geometricLink L {x}).space, r, η,
    (hTfin.subset (geometricLink_faces_subset T {x})), isConeBase_geometricLink T,
    hS, ?_, space_mono_of_faces_subset (fun _ hs => ⟨hs.1, hs.2.1, hs.2.2.1⟩),
    hr, hη, hJD, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← coneComplex_space_eq_coneSet (isConeBase_geometricLink T),
      ← closedStar_eq_coneComplex_space T hxT]
    exact closedStar_mem_nhds T (mem_interior_iff_mem_nhds.mp (hCT (hBC hxβ.1)))
  · rw [hrbd, htrace, hRbd, hηbd]
  · simpa only [K, hTC] using eventually_mem_cone_geometricLink_iff K hxK
  · rw [hrbd, ← geometricLink_boundaryComplex (n := 2)]
    simpa only [hfront] using eventually_mem_cone_geometricLink_iff (boundaryComplex 3 K) hxfrontK
  · simpa only [L, hTB] using eventually_mem_cone_geometricLink_iff L hxL
  · rw [← hsegR]
    simpa only [R, hTβ] using eventually_mem_cone_geometricLink_iff R hxR
  · obtain ⟨γ, hγ, _, _⟩ := h.exists_parametrization
    exact ((isPLBall_Icc zero_lt_one).of_isPLHomeomorphOn hγ).isPolyhedron.isClosed.isOpen_compl
      |>.mem_nhds
      (fun hx => hxends (h.inter_frontier.subset ⟨hx, hxβ.2⟩))

end DifferentialGeometry.Topology.PiecewiseLinear
