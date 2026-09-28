/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceDiskSeparation
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldInteriorConnected

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsCombinatorialManifoldWithBoundary.inter_disk_eq_of_not_subset [d : DecidableEq E]
    {n : ℕ} (K R : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite R.faces]
    (hK : IsCombinatorialManifold (n + 1) K)
    (hR : IsCombinatorialManifoldWithBoundary (n + 1) R)
    (hconn : IsPreconnected R.space) (hRK : R.space ⊆ K.space)
    {D : Set E} {r : (Fin (n + 2) → ℝ) → E}
    (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin (n + 2))) D) (hDK : D ⊆ K.space)
    (hboundary : r '' stdSimplexBoundary (n + 1) ⊆ (boundaryComplex (n + 1) R).space)
    (hnot : ¬ R.space ⊆ D) : R.space ∩ D = r '' stdSimplexBoundary (n + 1) := by
  have hd : d = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  subst d
  let _ : DecidableEq E := fun a b => Classical.propDecidable (a = b)
  let A := R.space \ (boundaryComplex (n + 1) R).space
  have hDclosed := (IsPLBall.isPolyhedron (⟨r, hr⟩ : IsPLBall (n + 1) D)).isClosed
  have hmeet := hK.inter_closure_sdiff_eq_image_stdSimplexBoundary K hr hDK
  have hcover : A ⊆ D ∪ closure (K.space \ D) := by
    intro x hx
    by_cases hxD : x ∈ D
    · exact Or.inl hxD
    · exact Or.inr (subset_closure ⟨hRK hx.1, hxD⟩)
  have hdis : A ∩ (D ∩ closure (K.space \ D)) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact hx.1.2 (hboundary (hmeet.subset hx.2))
  have hdense : R.space ⊆ closure A := hR.space_subset_closure_sdiff_boundaryComplex_space
  rcases isPreconnected_iff_subset_of_disjoint_closed.mp
      (hR.isPreconnected_sdiff_boundaryComplex_space hconn) D (closure (K.space \ D))
      hDclosed isClosed_closure hcover hdis with hin | hout
  · exact (hnot (hdense.trans (closure_minimal hin hDclosed))).elim
  · have hRout : R.space ⊆ closure (K.space \ D) :=
      hdense.trans (closure_minimal hout isClosed_closure)
    refine Subset.antisymm (fun x hx => hmeet.subset ⟨hx.2, hRout hx.1⟩) ?_
    intro x hx
    refine ⟨boundaryComplex_space_subset (n + 1) R (hboundary hx), ?_⟩
    obtain ⟨p, hp, rfl⟩ := hx
    exact hr.bijOn.mapsTo hp.1

theorem IsCombinatorialManifoldWithBoundary.inter_disk_eq_of_essential_circle [DecidableEq E]
    (K R : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite R.faces]
    (hK : IsCombinatorialManifold 2 K) (hR : IsCombinatorialManifoldWithBoundary 2 R)
    (hconn : IsPreconnected R.space) (hRK : R.space ⊆ K.space)
    {D H : Set E} {r : (Fin 3 → ℝ) → E}
    (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D) (hDK : D ⊆ K.space)
    (hboundary : r '' stdSimplexBoundary 2 ⊆ (boundaryComplex 2 R).space)
    (hH : IsPLSphere 1 H) (hHR : H ⊆ R.space)
    (hHJ : Disjoint H (r '' stdSimplexBoundary 2))
    (hess : ¬ ∃ (D' : Set E) (q : (Fin 3 → ℝ) → E),
      IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D' ∧ D' ⊆ K.space ∧
        H = q '' stdSimplexBoundary 2) : R.space ∩ D = r '' stdSimplexBoundary 2 := by
  have hdis := hK.disjoint_disk_of_essential_circle K hr hDK hH (hHR.trans hRK) hHJ hess
  apply hR.inter_disk_eq_of_not_subset K R hK hconn hRK hr hDK hboundary
  intro hRD
  obtain ⟨x, hx⟩ := hH.isConnected.nonempty
  exact disjoint_left.mp hdis (hRD (hHR hx)) hx

end DifferentialGeometry.Topology.PiecewiseLinear
