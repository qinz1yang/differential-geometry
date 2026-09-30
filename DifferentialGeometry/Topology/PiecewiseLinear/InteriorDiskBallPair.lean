/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceSplitPrismChart
import DifferentialGeometry.Topology.PiecewiseLinear.GeneralPosition

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsPLBall.exists_neighborhood_pair_of_nested_disks {D M U : Set E}
    (hD : IsPLBall 2 D) (hdim : Module.finrank ℝ E = 3) {r : (Fin 3 → ℝ) → E}
    (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) M)
    (hDM : D ⊆ r '' openSimplex (stdVertices 1)) (hU : IsOpen U) (hDU : D ⊆ U) :
    ∃ N Q₁ Q₂ DQ : Set E, IsPLBall 3 N ∧ IsPLBall 3 Q₁ ∧ IsPLBall 3 Q₂ ∧
      Q₁ ∪ Q₂ = N ∧ Q₁ ∩ Q₂ = DQ ∧ IsPLBall 2 DQ ∧ N ∩ M = DQ ∧
      N ⊆ U ∧ D ⊆ DQ ∧ (∀ x ∈ D, N ∈ 𝓝 x) ∧
      DQ ⊆ frontier Q₁ ∧ DQ ⊆ frontier Q₂ := by
  let _ : DecidableEq E := fun a b => Classical.propDecidable (a = b)
  have hM : IsPLBall 2 M := ⟨r, hr⟩
  have hDsub : D ⊆ M := hDM.trans ((image_mono
    (openSimplex_stdVertices_subset_stdSimplex (n := 1))).trans hr.image_eq.subset)
  obtain ⟨T, hT, hTcard, hMT⟩ := exists_affineIndependent_openSimplex_superset 3 hdim
    hM.isPolyhedron.isCompact.isBounded
  let K := simplexComplex T hT
  let _ : Finite K.faces := (simplexComplex_faces_finite T hT).to_subtype
  have hKspace : K.space = convexHull ℝ (T : Set E) :=
    simplexComplex_space T hT (Finset.card_pos.mp (by omega))
  have hKball : IsPLBall 3 K.space := hKspace.symm ▸
    isPLBall_convexHull_of_affineIndependent T hT hTcard
  have hK := hKball.isCombinatorialManifoldWithBoundary
  have hint : interior K.space = openSimplex T := by
    rw [hKspace, interior_convexHull_eq_openSimplex hT (by omega)]
  have hMint : M ⊆ interior K.space := hMT.trans hint.symm.subset
  have hDint : D ⊆ interior K.space := hDsub.trans hMint
  have hUnhds : U ∩ interior K.space ∈ 𝓝ˢ[K.space] D :=
    mem_nhdsSetWithin.mpr ⟨U ∩ interior K.space, hU.inter isOpen_interior,
      subset_inter hDU hDint, inter_subset_left⟩
  have hUdis : Disjoint (U ∩ interior K.space) (boundaryComplex 3 K).space := by
    rw [← frontier_space_eq_boundaryComplex_space_of_finrank hdim K hK]
    exact disjoint_interior_frontier.mono_left inter_subset_right
  obtain ⟨R, A, A₁, A₂, K₀, K₁, L, φ, ψ, g, ρ, -, hRfin, -, hAfin, -,
      -, -, -, -, -, -, -, -, -, -, -, -, hN, hDN, -, hNU, hNnhds,
      hDQ, -, -, -, hK₀fin, hK₁fin, hK₀, hK₁, hcover, hinter, hD₀, hD₁, -, -, -, -⟩ :=
    hK.exists_isSubdivision_disk_pair_with_centered_prism hD hD hr hDM subset_rfl hDsub
      (inter_eq_left.mpr hDsub) (hDint.trans interior_subset)
      (hMint.trans interior_subset) hUnhds hUdis
  let _ : Finite R.faces := hRfin.to_subtype
  let _ : Finite A.faces := hAfin.to_subtype
  let _ : Finite K₀.faces := hK₀fin.to_subtype
  let _ : Finite K₁.faces := hK₁fin.to_subtype
  refine ⟨(derivedNeighborhood R A).space, K₀.space, K₁.space,
    M ∩ (derivedNeighborhood R A).space,
    hN, hK₀, hK₁, hcover, hinter, hDQ, inter_comm _ _,
    hNU.trans inter_subset_left, subset_inter hDsub hDN, ?_, ?_, ?_⟩
  · intro x hx
    have h := hNnhds x hx
    rwa [nhdsWithin_eq_nhds.mpr (mem_interior_iff_mem_nhds.mp (hDint hx))] at h
  · rwa [frontier_space_eq_boundaryComplex_space_of_finrank hdim K₀
      hK₀.isCombinatorialManifoldWithBoundary]
  · rwa [frontier_space_eq_boundaryComplex_space_of_finrank hdim K₁
      hK₁.isCombinatorialManifoldWithBoundary]

end DifferentialGeometry.Topology.PiecewiseLinear
