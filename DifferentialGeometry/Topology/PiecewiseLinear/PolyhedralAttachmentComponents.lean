/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ComponentPartitionEquivalence
import DifferentialGeometry.Topology.PiecewiseLinear.PLHomeomorphGluing

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

open Classical in
theorem IsPLHomeomorphOn.exists_component_equiv_of_connected_attachment
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (Q : Geometry.SimplicialComplex ℝ F) {D : Set E} {f : E → F}
    (hD : IsPolyhedron D) (hDc : IsConnected D) (hmeet : IsConnected (K.space ∩ D))
    (hf : IsPLHomeomorphOn f (K.space ∪ D) Q.space) :
    ∃ (c₀ : ConnectedComponents K.space) (e : ConnectedComponents K.space ≃
        ConnectedComponents Q.space),
      K.space ∩ D ⊆ (connectedComponentComplex K c₀).space ∧
      ∀ c, IsPLHomeomorphOn f
        ((connectedComponentComplex K c).space ∪ if c = c₀ then D else ∅)
        (connectedComponentComplex Q (e c)).space := by
  classical
  let _ : Finite (ConnectedComponents K.space) := finite_connectedComponents_space K
  let _ (c : ConnectedComponents K.space) : Finite (connectedComponentComplex K c).faces :=
    (connectedComponentComplex_faces_finite K c).to_subtype
  obtain ⟨x, hx⟩ := hmeet.nonempty
  let c₀ := ConnectedComponents.mk (⟨x, hx.1⟩ : K.space)
  let B := fun c => (connectedComponentComplex K c).space
  have hBsub (c : ConnectedComponents K.space) : B c ⊆ K.space :=
    (subset_iUnion B c).trans (iUnion_connectedComponentComplex_space K).subset
  have hG : K.space ∩ D ⊆ B c₀ := by
    dsimp only [B, c₀]
    rw [connectedComponentComplex_mk, restrict_connectedComponentIn_space]
    exact hmeet.isPreconnected.subset_connectedComponentIn hx inter_subset_left
  have hBdis : Pairwise fun c d => Disjoint (B c) (B d) :=
    pairwise_disjoint_connectedComponentComplex_space K
  have hDdis (c : ConnectedComponents K.space) (hc : c ≠ c₀) : Disjoint D (B c) := by
    apply disjoint_left.mpr
    intro y hyD hyB
    exact disjoint_left.mp (hBdis (Ne.symm hc)) (hG ⟨hBsub c hyB, hyD⟩) hyB
  let P := fun c => B c ∪ if c = c₀ then D else ∅
  have hPsub (c : ConnectedComponents K.space) : P c ⊆ K.space ∪ D := by
    by_cases hc : c = c₀
    · simpa only [P, ite_eq_left hc] using union_subset_union (hBsub c) (Subset.rfl : D ⊆ D)
    · simpa only [P, ite_eq_right hc, union_empty] using (hBsub c).trans subset_union_left
  have hPpoly (c : ConnectedComponents K.space) : IsPolyhedron (P c) := by
    by_cases hc : c = c₀
    · simpa only [P, ite_eq_left hc] using (isPolyhedron_space (connectedComponentComplex K c)).union hD
    · simpa only [P, ite_eq_right hc, union_empty] using
        isPolyhedron_space (connectedComponentComplex K c)
  have hPc (c : ConnectedComponents K.space) : IsConnected (P c) := by
    by_cases hc : c = c₀
    · subst c
      simpa [P] using IsConnected.union ⟨x, hG hx, hx.2⟩
        (isConnected_connectedComponentComplex_space K c₀) hDc
    · simpa only [P, ite_eq_right hc, union_empty] using isConnected_connectedComponentComplex_space K c
  have hPdis : Pairwise fun c d => Disjoint (P c) (P d) := by
    intro c d hcd
    by_cases hc : c = c₀
    · subst c
      have hd : d ≠ c₀ := Ne.symm hcd
      simpa [P, hd] using (hBdis hcd).union_left (hDdis d hd)
    · by_cases hd : d = c₀
      · subst d
        simpa [P, hc] using (hBdis hcd).union_right (hDdis c hc).symm
      · simpa only [P, ite_eq_right hc, ite_eq_right hd, union_empty] using hBdis hcd
  have hPcover : (⋃ c, P c) = K.space ∪ D := by
    apply Subset.antisymm (iUnion_subset hPsub)
    rintro y (hyK | hyD)
    · obtain ⟨c, hc⟩ := mem_iUnion.mp ((iUnion_connectedComponentComplex_space K).symm.subset hyK)
      exact mem_iUnion.mpr ⟨c, Or.inl hc⟩
    · exact mem_iUnion.mpr ⟨c₀, Or.inr (by simpa using hyD)⟩
  have hfP (c : ConnectedComponents K.space) : IsPLHomeomorphOn f (P c) (f '' P c) :=
    hf.restrict (hPpoly c) (hPsub c)
  have hCc (c : ConnectedComponents K.space) : IsConnected (f '' P c) :=
    (hPc c).image f (hfP c).isPiecewiseAffineOn.continuousOn
  have hCcl (c : ConnectedComponents K.space) : IsClosed (f '' P c) :=
    ((hPpoly c).image_of_isPiecewiseAffineOn (hfP c).isPiecewiseAffineOn
      (hfP c).bijOn.injOn).isClosed
  have hCdis : Pairwise fun c d => Disjoint (f '' P c) (f '' P d) := by
    intro c d hcd
    apply disjoint_left.mpr
    rintro y ⟨z, hz, hzy⟩ ⟨w, hw, hwy⟩
    have hzw := hf.bijOn.injOn (hPsub c hz) (hPsub d hw) (hzy.trans hwy.symm)
    exact disjoint_left.mp (hPdis hcd) hz (hzw.symm ▸ hw)
  have hCcover : Q.space = ⋃ c, f '' P c := by
    rw [← hf.image_eq, ← hPcover, image_iUnion]
  obtain ⟨e, he⟩ := exists_equiv_connectedComponents_of_finite_partition Q
    (fun c => f '' P c) hCc hCcl hCdis hCcover
  refine ⟨c₀, e, hG, ?_⟩
  intro c
  rw [he c]
  exact hfP c

end DifferentialGeometry.Topology.PiecewiseLinear
