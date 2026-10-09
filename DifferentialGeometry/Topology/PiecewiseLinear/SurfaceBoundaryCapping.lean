/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldCapping
import DifferentialGeometry.Topology.PiecewiseLinear.EulerUnion
import DifferentialGeometry.Topology.PiecewiseLinear.BallReplacement

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_closed_of_disk
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) (hconn : IsConnected K.space)
    {D : Set E} {r : (Fin 3 → ℝ) → E}
    (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D)
    (hmeet : K.space ∩ D = r '' stdSimplexBoundary 2)
    (hboundary : (boundaryComplex 2 K).space = r '' stdSimplexBoundary 2) :
    ∃ (R : Geometry.SimplicialComplex ℝ E) (hRfin : R.faces.Finite),
      letI := hRfin.to_subtype
      IsCombinatorialManifold 2 R ∧ IsConnected R.space ∧
      eulerChar R = eulerChar K + 1 ∧ R.space = K.space ∪ D := by
  have hD : IsPLBall 2 D := ⟨r, hr⟩
  have hJ : IsPLSphere 1 (r '' stdSimplexBoundary 2) := hr.isPLSphere_image_stdSimplexBoundary
  obtain ⟨R, hRfin, hR, hRspace⟩ :=
    hK.exists_isCombinatorialManifold_union_ball K hr hmeet hboundary
  let _ : Finite R.faces := hRfin.to_subtype
  have hRc : IsConnected R.space := by
    rw [hRspace]
    exact IsConnected.union (hmeet.symm ▸ hJ.nonempty) hconn hD.isConnected
  obtain ⟨A, hAfin, hAspace⟩ := hD.isPolyhedron.exists_simplicialComplex
  let _ : Finite A.faces := hAfin.to_subtype
  have hAχ := eulerChar_of_isPLBall A (hAspace.symm ▸ hD)
  have hRχ := eulerChar_eq_add_of_space_union_of_isPLSphere_one R K A
    (by rw [hRspace, hAspace]) (by rw [hAspace, hmeet]; exact hJ)
  exact ⟨R, hRfin, hR, hRc, by omega, hRspace⟩

open Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_closed_of_disk_pair
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) (hconn : IsConnected K.space)
    {D₀ D₁ : Set E} {r₀ r₁ : (Fin 3 → ℝ) → E}
    (hr₀ : IsPLHomeomorphOn r₀ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₀)
    (hr₁ : IsPLHomeomorphOn r₁ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₁) (hdis : Disjoint D₀ D₁)
    (hmeet₀ : K.space ∩ D₀ = r₀ '' stdSimplexBoundary 2)
    (hmeet₁ : K.space ∩ D₁ = r₁ '' stdSimplexBoundary 2)
    (hboundary : (boundaryComplex 2 K).space =
      r₀ '' stdSimplexBoundary 2 ∪ r₁ '' stdSimplexBoundary 2) :
    ∃ (R : Geometry.SimplicialComplex ℝ E) (hRfin : R.faces.Finite),
      letI := hRfin.to_subtype
      IsCombinatorialManifold 2 R ∧ IsConnected R.space ∧
      eulerChar R = eulerChar K + 2 ∧ R.space = K.space ∪ D₀ ∪ D₁ := by
  have hD₀ : IsPLBall 2 D₀ := ⟨r₀, hr₀⟩
  have hD₁ : IsPLBall 2 D₁ := ⟨r₁, hr₁⟩
  have hJ₀ : IsPLSphere 1 (r₀ '' stdSimplexBoundary 2) := hr₀.isPLSphere_image_stdSimplexBoundary
  have hJ₁ : IsPLSphere 1 (r₁ '' stdSimplexBoundary 2) := hr₁.isPLSphere_image_stdSimplexBoundary
  obtain ⟨R, hRfin, hR, hRspace⟩ :=
    hK.exists_isCombinatorialManifold_union_ball_pair K hr₀ hr₁ hdis hmeet₀ hmeet₁ hboundary
  let _ : Finite R.faces := hRfin.to_subtype
  have hinter : (K.space ∪ D₀) ∩ D₁ = r₁ '' stdSimplexBoundary 2 := by
    rw [union_inter_distrib_right, hmeet₁, hdis.inter_eq, union_empty]
  have hRc : IsConnected R.space := by
    rw [hRspace]
    exact IsConnected.union (hinter.symm ▸ hJ₁.nonempty)
      (IsConnected.union (hmeet₀.symm ▸ hJ₀.nonempty) hconn hD₀.isConnected) hD₁.isConnected
  obtain ⟨A, hAfin, hAspace⟩ := hD₀.isPolyhedron.exists_simplicialComplex
  obtain ⟨B, hBfin, hBspace⟩ := hD₁.isPolyhedron.exists_simplicialComplex
  obtain ⟨P, hPfin, hPspace⟩ :=
    ((isPolyhedron_space K).union hD₀.isPolyhedron).exists_simplicialComplex
  let _ : Finite A.faces := hAfin.to_subtype
  let _ : Finite B.faces := hBfin.to_subtype
  let _ : Finite P.faces := hPfin.to_subtype
  have hAχ := eulerChar_of_isPLBall A (hAspace.symm ▸ hD₀)
  have hBχ := eulerChar_of_isPLBall B (hBspace.symm ▸ hD₁)
  have hPχ := eulerChar_eq_add_of_space_union_of_isPLSphere_one P K A
    (by rw [hPspace, hAspace]) (by rw [hAspace, hmeet₀]; exact hJ₀)
  have hRχ := eulerChar_eq_add_of_space_union_of_isPLSphere_one R P B
    (by rw [hRspace, hPspace, hBspace]) (by rw [hPspace, hBspace, hinter]; exact hJ₁)
  exact ⟨R, hRfin, hR, hRc, by omega, hRspace⟩

open Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_closed_pair_of_disks
    (A B : Geometry.SimplicialComplex ℝ E) [Finite A.faces] [Finite B.faces]
    (hA : IsCombinatorialManifoldWithBoundary 2 A)
    (hB : IsCombinatorialManifoldWithBoundary 2 B)
    (hAc : IsConnected A.space) (hBc : IsConnected B.space) (hAB : Disjoint A.space B.space)
    {D₀ D₁ : Set E} {r₀ r₁ : (Fin 3 → ℝ) → E}
    (hr₀ : IsPLHomeomorphOn r₀ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₀)
    (hr₁ : IsPLHomeomorphOn r₁ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₁) (hdis : Disjoint D₀ D₁)
    (hmeet₀ : (A.space ∪ B.space) ∩ D₀ = r₀ '' stdSimplexBoundary 2)
    (hmeet₁ : (A.space ∪ B.space) ∩ D₁ = r₁ '' stdSimplexBoundary 2)
    (hboundary₀ : (boundaryComplex 2 A).space = r₀ '' stdSimplexBoundary 2)
    (hboundary₁ : (boundaryComplex 2 B).space = r₁ '' stdSimplexBoundary 2) :
    ∃ (P Q : Geometry.SimplicialComplex ℝ E) (hPfin : P.faces.Finite) (hQfin : Q.faces.Finite),
      letI := hPfin.to_subtype
      letI := hQfin.to_subtype
      IsCombinatorialManifold 2 P ∧ IsCombinatorialManifold 2 Q ∧
      IsConnected P.space ∧ IsConnected Q.space ∧ Disjoint P.space Q.space ∧
      eulerChar P + eulerChar Q = eulerChar A + eulerChar B + 2 ∧
      P.space = A.space ∪ D₀ ∧ Q.space = B.space ∪ D₁ := by
  have hJ₀A : r₀ '' stdSimplexBoundary 2 ⊆ A.space :=
    hboundary₀.symm.subset.trans (boundaryComplex_space_subset 2 A)
  have hJ₁B : r₁ '' stdSimplexBoundary 2 ⊆ B.space :=
    hboundary₁.symm.subset.trans (boundaryComplex_space_subset 2 B)
  have hAD : A.space ∩ D₀ = r₀ '' stdSimplexBoundary 2 :=
    Subset.antisymm (fun _ hx => hmeet₀.subset ⟨Or.inl hx.1, hx.2⟩)
      (fun _ hx => ⟨hJ₀A hx, (hmeet₀.symm.subset hx).2⟩)
  have hBD : B.space ∩ D₁ = r₁ '' stdSimplexBoundary 2 :=
    Subset.antisymm (fun _ hx => hmeet₁.subset ⟨Or.inr hx.1, hx.2⟩)
      (fun _ hx => ⟨hJ₁B hx, (hmeet₁.symm.subset hx).2⟩)
  obtain ⟨P, hPfin, hP, hPc, hPχ, hPspace⟩ :=
    hA.exists_closed_of_disk A hAc hr₀ hAD hboundary₀
  obtain ⟨Q, hQfin, hQ, hQc, hQχ, hQspace⟩ :=
    hB.exists_closed_of_disk B hBc hr₁ hBD hboundary₁
  let _ : Finite P.faces := hPfin.to_subtype
  let _ : Finite Q.faces := hQfin.to_subtype
  refine ⟨P, Q, hPfin, hQfin, hP, hQ, hPc, hQc, ?_, by omega, hPspace, hQspace⟩
  rw [hPspace, hQspace]
  apply disjoint_left.mpr
  rintro x (hxA | hxD₀) (hxB | hxD₁)
  · exact disjoint_left.mp hAB hxA hxB
  · exact disjoint_left.mp hAB hxA (hJ₁B (hmeet₁.subset ⟨Or.inl hxA, hxD₁⟩))
  · exact disjoint_left.mp hAB (hJ₀A (hmeet₀.subset ⟨Or.inr hxB, hxD₀⟩)) hxB
  · exact disjoint_left.mp hdis hxD₀ hxD₁

end DifferentialGeometry.Topology.PiecewiseLinear
