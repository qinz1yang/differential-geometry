/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ComponentComplement
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryInvariance
import DifferentialGeometry.Topology.PiecewiseLinear.MobiusEmbedding

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsCombinatorialManifoldWithBoundary.exists_component_complement [d : DecidableEq E]
    {n : ℕ} (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K) (hKo : IsOrientable (n + 1) K)
    (c₀ : ConnectedComponents K.space) :
    ∃ (R : Geometry.SimplicialComplex ℝ E) (hRfin : R.faces.Finite),
      letI := hRfin.to_subtype
      IsCombinatorialManifoldWithBoundary (n + 1) R ∧ IsOrientable (n + 1) R ∧
      R.space = K.space \ (PiecewiseLinear.connectedComponentComplex K c₀).space ∧
      (boundaryComplex (n + 1) R).space =
        (boundaryComplex (n + 1) K).space \ (PiecewiseLinear.connectedComponentComplex K c₀).space ∧
      (∃ e : {c : ConnectedComponents K.space // c ≠ c₀} ≃ ConnectedComponents R.space,
        ∀ c, (PiecewiseLinear.connectedComponentComplex R (e c)).space =
          (PiecewiseLinear.connectedComponentComplex K c).space) ∧
      Nat.card (ConnectedComponents R.space) + 1 = Nat.card (ConnectedComponents K.space) := by
  have hd : d = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  subst d
  let _ : DecidableEq E := fun a b => Classical.propDecidable (a = b)
  obtain ⟨R, hRfin, hRspace, ⟨e, he⟩, hcard⟩ := exists_polyhedral_component_complement K c₀
  let _ : Finite R.faces := hRfin.to_subtype
  let _ (c : ConnectedComponents K.space) :
      Finite (PiecewiseLinear.connectedComponentComplex K c).faces :=
    (connectedComponentComplex_faces_finite K c).to_subtype
  let _ (c : ConnectedComponents R.space) :
      Finite (PiecewiseLinear.connectedComponentComplex R c).faces :=
    (connectedComponentComplex_faces_finite R c).to_subtype
  have hf (c : {c : ConnectedComponents K.space // c ≠ c₀}) :
      IsPLHomeomorphOn (id : E → E) (PiecewiseLinear.connectedComponentComplex K c).space
        (PiecewiseLinear.connectedComponentComplex R (e c)).space := by
    rw [he c]
    exact (isPolyhedron_space (PiecewiseLinear.connectedComponentComplex K c)).isPLHomeomorphOn_id
  have hcc (c : {c : ConnectedComponents K.space // c ≠ c₀}) :
      IsCombinatorialManifoldWithBoundary (n + 1)
        (PiecewiseLinear.connectedComponentComplex R (e c)) :=
    (hK.connectedComponentComplex c).of_isPLHomeomorphOn (hf c)
  have hR : IsCombinatorialManifoldWithBoundary (n + 1) R := by
    intro v hv
    have hvR : v ∈ R.space := R.subset_space hv (Finset.mem_singleton_self v)
    let p : R.space := ⟨v, hvR⟩
    have hc : IsCombinatorialManifoldWithBoundary (n + 1)
        (PiecewiseLinear.connectedComponentComplex R (ConnectedComponents.mk p)) := by
      simpa only [e.apply_symm_apply] using hcc (e.symm (ConnectedComponents.mk p))
    rw [connectedComponentComplex_mk] at hc
    have hvc : v ∈ connectedComponentIn R.space v := mem_connectedComponentIn hvR
    have hvC : {v} ∈ (restrict R (connectedComponentIn R.space v)).faces := by
      refine ⟨hv, ?_⟩
      simpa only [Finset.coe_singleton, convexHull_singleton, singleton_subset_iff] using hvc
    have hlink := hc v hvC
    rwa [geometricLink_restrict_connectedComponentIn R hvc] at hlink
  have hboundary (x : E) (hxR : x ∈ R.space) :
      x ∈ (boundaryComplex (n + 1) R).space ↔ x ∈ (boundaryComplex (n + 1) K).space := by
    let p : R.space := ⟨x, hxR⟩
    let c := e.symm (ConnectedComponents.mk p)
    have hxC : x ∈ (PiecewiseLinear.connectedComponentComplex R (e c)).space := by
      dsimp only [c]
      rw [e.apply_symm_apply, connectedComponentComplex_mk, restrict_connectedComponentIn_space]
      exact mem_connectedComponentIn hxR
    have hxKc : x ∈ (PiecewiseLinear.connectedComponentComplex K c).space := (he c).subset hxC
    have hB : (boundaryComplex (n + 1) (PiecewiseLinear.connectedComponentComplex R (e c))).space =
        (boundaryComplex (n + 1) (PiecewiseLinear.connectedComponentComplex K c)).space := by
      simpa only [image_id] using boundaryComplex_space_of_isPLHomeomorphOn
        (PiecewiseLinear.connectedComponentComplex K c)
        (PiecewiseLinear.connectedComponentComplex R (e c))
        (hK.connectedComponentComplex c) (hf c)
    rw [boundaryComplex_space_connectedComponentComplex,
      boundaryComplex_space_connectedComponentComplex] at hB
    exact ⟨fun hx => (hB.subset ⟨hx, hxC⟩).1, fun hx => (hB.symm.subset ⟨hx, hxKc⟩).1⟩
  refine ⟨R, hRfin, hR, hKo.of_space_subset K R (hRspace.subset.trans sdiff_subset) hK hR,
    hRspace, ?_, ⟨e, he⟩, hcard⟩
  ext x
  constructor
  · intro hx
    have hxR := boundaryComplex_space_subset (n + 1) R hx
    exact ⟨(hboundary x hxR).mp hx, (hRspace.subset hxR).2⟩
  · rintro ⟨hx, hxc⟩
    have hxR := hRspace.symm.subset ⟨boundaryComplex_space_subset (n + 1) K hx, hxc⟩
    exact (hboundary x hxR).mpr hx

theorem IsCombinatorialManifoldWithBoundary.exists_closed_component_complement [DecidableEq E]
    {n : ℕ} (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K) (hKo : IsOrientable (n + 1) K)
    (c₀ : ConnectedComponents K.space)
    (hclosed :
      (boundaryComplex (n + 1) (PiecewiseLinear.connectedComponentComplex K c₀)).space = ∅) :
    ∃ (R : Geometry.SimplicialComplex ℝ E) (hRfin : R.faces.Finite),
      letI := hRfin.to_subtype
      IsCombinatorialManifoldWithBoundary (n + 1) R ∧ IsOrientable (n + 1) R ∧
      R.space = K.space \ (PiecewiseLinear.connectedComponentComplex K c₀).space ∧
      (boundaryComplex (n + 1) R).space = (boundaryComplex (n + 1) K).space ∧
      (∃ e : {c : ConnectedComponents K.space // c ≠ c₀} ≃ ConnectedComponents R.space,
        ∀ c, (PiecewiseLinear.connectedComponentComplex R (e c)).space =
          (PiecewiseLinear.connectedComponentComplex K c).space) ∧
      Nat.card (ConnectedComponents R.space) + 1 = Nat.card (ConnectedComponents K.space) := by
  obtain ⟨R, hRfin, hR, hRo, hRspace, hRb, he, hcard⟩ :=
    hK.exists_component_complement K hKo c₀
  let _ : Finite R.faces := hRfin.to_subtype
  have hdis : Disjoint (boundaryComplex (n + 1) K).space
      (PiecewiseLinear.connectedComponentComplex K c₀).space :=
    disjoint_iff_inter_eq_empty.mpr
      ((boundaryComplex_space_connectedComponentComplex (n + 1) K c₀).symm.trans hclosed)
  exact ⟨R, hRfin, hR, hRo, hRspace, hRb.trans (sdiff_eq_left.mpr hdis), he, hcard⟩

end DifferentialGeometry.Topology.PiecewiseLinear
