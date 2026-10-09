/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PseudoCellFlatChart

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem IsPseudoCell.exists_isPLBall_neighborhood_pair {Ec Eint Ebd : Set E3} {P : E3}
    (hpc : IsPseudoCell Ec Eint Ebd P) {x : E3} (hx : x ∈ Eint \ {P}) {O : Set E3}
    (hO : O ∈ 𝓝 x) :
    ∃ Q₁ Q₂ DQ : Set E3, IsPLBall 3 Q₁ ∧ IsPLBall 3 Q₂ ∧ Q₁ ∩ Q₂ = DQ ∧
      IsPLBall 2 DQ ∧ DQ ⊆ Eint \ {P} ∧ Q₁ ∪ Q₂ ∈ 𝓝 x ∧ Q₁ ∪ Q₂ ⊆ O ∧
      (Q₁ ∪ Q₂) ∩ Ec = DQ := by
  let _ : DecidableEq E3 := fun a b => Classical.propDecidable (a = b)
  obtain ⟨L, hLfin, hL, hag⟩ := exists_isCombinatorialManifoldWithBoundary_two_eventually_mem_iff
    (ι := Unit) {()} (M := fun _ => Eint) (Cc := fun _ => {x}) (P := fun _ => P)
    (fun _ _ => hpc.isOpenCell) (fun _ _ => hpc.regular)
    (fun i _ j _ hij => (hij (Subsingleton.elim i j)).elim)
    (fun _ _ => isCompact_singleton) (fun _ _ => singleton_subset_iff.mpr hx)
  have : Finite L.faces := hLfin.to_subtype
  have hagx : ∀ᶠ y in 𝓝 x, y ∈ L.space ↔ y ∈ Eint :=
    hag () (Finset.mem_singleton_self _) x (mem_singleton x)
  have hxL : x ∈ L.space := hagx.self_of_nhds.mpr hx.1
  have hxB : x ∉ (boundaryComplex 2 L).space := by
    intro hxB
    obtain ⟨R, hRL, hRfin, hxR⟩ := exists_isSubdivision_singleton_mem L hxL
    have : Finite R.faces := hRfin.to_subtype
    obtain ⟨ψ⟩ := hpc.isOpenCell
    have hsph := isPLSphere_one_geometricLink_of_homeomorph R Metric.isOpen_ball ψ hxR
      (by rw [hRL.space_eq]; exact hagx)
    have hball := (isPLBall_geometricLink_iff_mem_boundaryComplex_of_isSubdivision (n := 1)
      L R hL hRL hxR).mpr hxB
    exact hball.not_isPLSphere hsph
  obtain ⟨W₀, hW₀p, hW₀, hxW₀⟩ := eventually_nhds_iff.mp hagx
  have hbdc : IsClosed Ebd := by
    obtain ⟨φ⟩ := hpc.isSphere
    exact (isCompact_iff_compactSpace.mpr φ.symm.compactSpace).isClosed
  have hxbd : x ∉ Ebd := fun h => Set.disjoint_left.mp hpc.disjointRim hx.1 h
  have hdim : Module.finrank ℝ E3 = 3 := by simp
  obtain ⟨T, hT, hTcard, hLT⟩ := exists_affineIndependent_openSimplex_superset 3 hdim
    (isPolyhedron_space L).isCompact.isBounded
  let K := simplexComplex T hT
  let _ : Finite K.faces := (simplexComplex_faces_finite T hT).to_subtype
  have hKspace : K.space = convexHull ℝ (T : Set E3) :=
    simplexComplex_space T hT (Finset.card_pos.mp (by omega))
  have hKball : IsPLBall 3 K.space := hKspace.symm ▸
    isPLBall_convexHull_of_affineIndependent T hT hTcard
  have hK := hKball.isCombinatorialManifoldWithBoundary
  have hint : interior K.space = openSimplex T := by
    rw [hKspace, interior_convexHull_eq_openSimplex hT (by omega)]
  have hLint : L.space ⊆ interior K.space := hLT.trans hint.symm.subset
  have hxKB : x ∉ (boundaryComplex 3 K).space := by
    rw [← frontier_space_eq_boundaryComplex_space_of_finrank hdim K hK]
    exact fun h => h.2 (hLint hxL)
  have hU : O ∩ W₀ ∩ Ebdᶜ ∩ ({P} : Set E3)ᶜ ∈ 𝓝[K.space] x :=
    mem_nhdsWithin_of_mem_nhds (Filter.inter_mem
      (Filter.inter_mem (Filter.inter_mem hO (hW₀.mem_nhds hxW₀))
        (hbdc.isOpen_compl.mem_nhds hxbd))
      (isClosed_singleton.isOpen_compl.mem_nhds hx.2))
  obtain ⟨C, -, hCsub, hCnhds, hDQ, a, -, b, -, -, -, hQa, hQb, hQab, hQint⟩ :=
    exists_isPLBall_neighborhood_pair_sdiff_of_isCombinatorialManifoldWithBoundary hK hL
      (hLint.trans interior_subset) ⟨hxL, hxB⟩ hxKB hU
  rw [nhdsWithin_eq_nhds.mpr (mem_interior_iff_mem_nhds.mp (hLint hxL))] at hCnhds
  refine ⟨closure (connectedComponentIn (C \ L.space) a),
    closure (connectedComponentIn (C \ L.space) b), C ∩ L.space,
    hQa, hQb, hQint, hDQ, ?_, hQab.symm ▸ hCnhds, ?_, ?_⟩
  · intro y hy
    exact ⟨(hW₀p y (hCsub hy.1).2.1.1.2).mp hy.2, (hCsub hy.1).2.2⟩
  · rw [hQab]
    exact fun y hy => (hCsub hy).2.1.1.1
  · rw [hQab]
    ext y
    constructor
    · intro hy
      refine ⟨hy.1, (hW₀p y (hCsub hy.1).2.1.1.2).mpr ?_⟩
      rw [hpc.carrierEq] at hy
      exact hy.2.resolve_right (hCsub hy.1).2.1.2
    · intro hy
      exact ⟨hy.1, hpc.carrierEq.symm ▸
        Or.inl ((hW₀p y (hCsub hy.1).2.1.1.2).mp hy.2)⟩

end DifferentialGeometry.Topology.PiecewiseLinear
