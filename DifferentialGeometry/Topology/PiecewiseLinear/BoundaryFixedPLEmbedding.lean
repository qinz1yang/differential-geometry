/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryInvariance

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def HasBoundaryFixedPLEmbedding [DecidableEq E] (n : ℕ)
    (K : Geometry.SimplicialComplex ℝ E) (T : Set E) : Prop :=
  ∃ f : E → E, IsPLHomeomorphOn f K.space (f '' K.space) ∧ f '' K.space ⊆ T ∧
    EqOn f id (boundaryComplex n K).space

theorem HasBoundaryFixedPLEmbedding.of_subsurface [DecidableEq E] {n : ℕ}
    (K R : Geometry.SimplicialComplex ℝ E) {T : Set E} (hRT : R.space ⊆ T)
    {f : E → E} (hf : IsPLHomeomorphOn f R.space K.space)
    (hboundary : (boundaryComplex n R).space = (boundaryComplex n K).space)
    (hfix : EqOn f id (boundaryComplex n R).space) : HasBoundaryFixedPLEmbedding n K T := by
  refine ⟨Function.invFunOn f R.space, ?_, ?_, ?_⟩
  · rw [hf.symm.image_eq]
    exact hf.symm
  · rw [hf.symm.image_eq]
    exact hRT
  · intro x hx
    have hxR := boundaryComplex_space_subset n R (hboundary.symm.subset hx)
    simpa only [hfix (hboundary.symm.subset hx), id_eq] using hf.bijOn.invOn_invFunOn.1 hxR

variable [FiniteDimensional ℝ E]

theorem HasBoundaryFixedPLEmbedding.of_subset [DecidableEq E] (n : ℕ)
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] {T : Set E} (hKT : K.space ⊆ T) :
    HasBoundaryFixedPLEmbedding n K T := by
  refine ⟨id, ?_, ?_, fun _ _ => rfl⟩
  · simpa only [image_id] using (isPolyhedron_space K).isPLHomeomorphOn_id
  · simpa only [image_id] using hKT

theorem HasBoundaryFixedPLEmbedding.of_isPLHomeomorphOn [DecidableEq E] {n : ℕ}
    {K Q : Geometry.SimplicialComplex ℝ E} {T : Set E}
    (h : HasBoundaryFixedPLEmbedding n K T) {g : E → E}
    (hg : IsPLHomeomorphOn g K.space Q.space)
    (hboundary : (boundaryComplex n Q).space = (boundaryComplex n K).space)
    (hgfix : EqOn g id (boundaryComplex n K).space) : HasBoundaryFixedPLEmbedding n Q T := by
  obtain ⟨f, hf, hfT, hfix⟩ := h
  have hcomp := hg.symm.trans hf
  refine ⟨f ∘ Function.invFunOn g K.space, ?_, ?_, ?_⟩
  · rw [hcomp.image_eq]
    exact hcomp
  · rw [hcomp.image_eq]
    exact hfT
  · intro x hx
    have hxK := hboundary.subset hx
    have hinv : Function.invFunOn g K.space x = x := by
      simpa only [hgfix hxK, id_eq] using
        hg.bijOn.invOn_invFunOn.1 (boundaryComplex_space_subset n K hxK)
    simpa only [Function.comp_apply, hinv] using hfix hxK

theorem HasBoundaryFixedPLEmbedding.exists_subsurface [d : DecidableEq E] {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K) (hconn : IsConnected K.space)
    {T : Set E} (h : HasBoundaryFixedPLEmbedding (n + 1) K T) :
    ∃ R : Geometry.SimplicialComplex ℝ E, R.faces.Finite ∧
      IsCombinatorialManifoldWithBoundary (n + 1) R ∧ IsConnected R.space ∧ R.space ⊆ T ∧
      (boundaryComplex (n + 1) R).space = (boundaryComplex (n + 1) K).space ∧
      ∃ f : E → E, IsPLHomeomorphOn f R.space K.space ∧
        EqOn f id (boundaryComplex (n + 1) R).space := by
  have hd : d = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  subst d
  let _ : DecidableEq E := fun a b => Classical.propDecidable (a = b)
  obtain ⟨f, hf, hfT, hfix⟩ := h
  obtain ⟨R, hRfin, hRspace⟩ := (isPolyhedron_space K).image_of_isPiecewiseAffineOn
    hf.isPiecewiseAffineOn hf.bijOn.injOn |>.exists_simplicialComplex
  let _ : Finite R.faces := hRfin.to_subtype
  have hfR : IsPLHomeomorphOn f K.space R.space := by rw [hRspace]; exact hf
  have hR := hK.of_isPLHomeomorphOn hfR
  have hRconn : IsConnected R.space := by
    rw [hRspace]
    exact hconn.image _ hf.isPiecewiseAffineOn.continuousOn
  have hRbd : (boundaryComplex (n + 1) R).space = (boundaryComplex (n + 1) K).space := by
    rw [boundaryComplex_space_of_isPLHomeomorphOn K R hK hfR]
    simpa only [image_id] using hfix.image_eq
  refine ⟨R, hRfin, hR, hRconn, hRspace.subset.trans hfT, hRbd,
    Function.invFunOn f K.space, hfR.symm, ?_⟩
  intro x hx
  have hxK := hRbd.subset hx
  simpa only [hfix hxK, id_eq] using
    hfR.bijOn.invOn_invFunOn.1 (boundaryComplex_space_subset (n + 1) K hxK)

end DifferentialGeometry.Topology.PiecewiseLinear
