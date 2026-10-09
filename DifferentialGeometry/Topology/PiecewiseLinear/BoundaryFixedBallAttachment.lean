/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PLHomeomorphBallAttachment
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryInvariance

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsPLHomeomorphOn.exists_manifold_union_ball_fixed_boundary [d : DecidableEq E]
    {n : ℕ} (R Q : Geometry.SimplicialComplex ℝ E) [Finite R.faces] [Finite Q.faces]
    (hQ : IsCombinatorialManifoldWithBoundary (n + 1) Q) (hQconn : IsConnected Q.space)
    {L D Δ : Set E} {f g : E → E} (hf : IsPLHomeomorphOn f R.space L)
    (hfix : EqOn f id (boundaryComplex (n + 1) R).space)
    {r s : (Fin (n + 2) → ℝ) → E}
    (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin (n + 2))) D)
    (hs : IsPLHomeomorphOn s (Convexity.StdSimplex.coordinateSet ℝ (Fin (n + 2))) Δ)
    (hrim : s '' stdSimplexBoundary (n + 1) = r '' stdSimplexBoundary (n + 1))
    (hRD : R.space ∩ D = r '' stdSimplexBoundary (n + 1))
    (hLΔ : L ∩ Δ = r '' stdSimplexBoundary (n + 1))
    (hbd : r '' stdSimplexBoundary (n + 1) ⊆ (boundaryComplex (n + 1) R).space)
    (hg : IsPLHomeomorphOn g (L ∪ Δ) Q.space)
    (hgfix : EqOn g id ((boundaryComplex (n + 1) R).space \ r '' stdSimplexBoundary (n + 1)))
    (hQbd : (boundaryComplex (n + 1) Q).space =
      (boundaryComplex (n + 1) R).space \ r '' stdSimplexBoundary (n + 1)) :
    ∃ A : Geometry.SimplicialComplex ℝ E, A.faces.Finite ∧
      IsCombinatorialManifoldWithBoundary (n + 1) A ∧ IsConnected A.space ∧
      A.space = R.space ∪ D ∧ (boundaryComplex (n + 1) A).space =
        (boundaryComplex (n + 1) Q).space ∧
      ∃ k : E → E, IsPLHomeomorphOn k A.space Q.space ∧
        EqOn k id (boundaryComplex (n + 1) A).space := by
  have hd : d = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  subst d
  let _ : DecidableEq E := fun a b => Classical.propDecidable (a = b)
  have hmark : f '' (r '' stdSimplexBoundary (n + 1)) =
      s '' stdSimplexBoundary (n + 1) := by
    simpa only [image_id, hrim] using (hfix.mono hbd).image_eq
  obtain ⟨k, hk, hkf⟩ := hf.exists_extension_union_ball (isPolyhedron_space R)
    hr hs hRD (hLΔ.trans hrim.symm) hmark
  obtain ⟨A, hAfin, hAspace⟩ :=
    ((isPolyhedron_space R).union (IsPLBall.isPolyhedron
      (⟨r, hr⟩ : IsPLBall (n + 1) D))).exists_simplicialComplex
  let _ : Finite A.faces := hAfin.to_subtype
  have hkg : IsPLHomeomorphOn (g ∘ k) A.space Q.space := by
    rw [hAspace]
    exact hk.trans hg
  have hA := hQ.of_isPLHomeomorphOn hkg.symm
  have hAconn : IsConnected A.space := by
    rw [← hkg.symm.image_eq]
    exact hQconn.image _ hkg.symm.isPiecewiseAffineOn.continuousOn
  have hnewfix : EqOn (g ∘ k) id (boundaryComplex (n + 1) Q).space := by
    intro x hx
    have hxR := hQbd.subset hx
    have hxspace := boundaryComplex_space_subset (n + 1) R hxR.1
    dsimp only [Function.comp_apply, id_eq]
    rw [hkf hxspace, hfix hxR.1]
    exact hgfix hxR
  have hinvfix : EqOn (Function.invFunOn (g ∘ k) A.space) id
      (boundaryComplex (n + 1) Q).space := by
    intro x hx
    have hxA : x ∈ A.space := hAspace.symm.subset
      (Or.inl (boundaryComplex_space_subset (n + 1) R (hQbd.subset hx).1))
    simpa only [hnewfix hx, id_eq] using hkg.bijOn.invOn_invFunOn.1 hxA
  have hAbd : (boundaryComplex (n + 1) A).space =
      (boundaryComplex (n + 1) Q).space := by
    rw [boundaryComplex_space_of_isPLHomeomorphOn Q A hQ hkg.symm]
    simpa only [image_id] using hinvfix.image_eq
  exact ⟨A, hAfin, hA, hAconn, hAspace, hAbd, g ∘ k, hkg, hnewfix.mono hAbd.subset⟩

end DifferentialGeometry.Topology.PiecewiseLinear
