/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedralAttachmentComponents
import DifferentialGeometry.Topology.PiecewiseLinear.EulerUnion
import DifferentialGeometry.Topology.PiecewiseLinear.BallReplacement

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

open Classical in
theorem IsPLHomeomorphOn.exists_component_eulerChar_of_disk_attachment
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (Q : Geometry.SimplicialComplex ℝ F) [Finite Q.faces]
    {D : Set E} {r : (Fin 3 → ℝ) → E} {f : E → F}
    (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D)
    (hmeet : K.space ∩ D = r '' stdSimplexBoundary 2)
    (hf : IsPLHomeomorphOn f (K.space ∪ D) Q.space) :
    letI (c : ConnectedComponents K.space) : Finite (connectedComponentComplex K c).faces :=
      (connectedComponentComplex_faces_finite K c).to_subtype
    letI (c : ConnectedComponents Q.space) : Finite (connectedComponentComplex Q c).faces :=
      (connectedComponentComplex_faces_finite Q c).to_subtype
    ∃ (c₀ : ConnectedComponents K.space) (e : ConnectedComponents K.space ≃
        ConnectedComponents Q.space),
      K.space ∩ D ⊆ (connectedComponentComplex K c₀).space ∧
      (∀ c, IsPLHomeomorphOn f
        ((connectedComponentComplex K c).space ∪ if c = c₀ then D else ∅)
        (connectedComponentComplex Q (e c)).space) ∧
      eulerChar (connectedComponentComplex Q (e c₀)) =
        eulerChar (connectedComponentComplex K c₀) + 1 ∧
      ∀ c, c ≠ c₀ → eulerChar (connectedComponentComplex Q (e c)) =
        eulerChar (connectedComponentComplex K c) := by
  have hD : IsPLBall 2 D := ⟨r, hr⟩
  have hG : IsPLSphere 1 (r '' stdSimplexBoundary 2) :=
    hr.isPLSphere_image_stdSimplexBoundary
  obtain ⟨c₀, e, hattach, hcomp⟩ :=
    hf.exists_component_equiv_of_connected_attachment K Q hD.isPolyhedron hD.isConnected
      (hmeet.symm ▸ hG.isConnected)
  let _ (c : ConnectedComponents K.space) : Finite (connectedComponentComplex K c).faces :=
    (connectedComponentComplex_faces_finite K c).to_subtype
  let _ (c : ConnectedComponents Q.space) : Finite (connectedComponentComplex Q c).faces :=
    (connectedComponentComplex_faces_finite Q c).to_subtype
  refine ⟨c₀, e, hattach, hcomp, ?_, ?_⟩
  · let A := connectedComponentComplex K c₀
    have hAK : A.space ⊆ K.space :=
      (subset_iUnion (fun c => (connectedComponentComplex K c).space) c₀).trans
        (iUnion_connectedComponentComplex_space K).subset
    have hAD : A.space ∩ D = r '' stdSimplexBoundary 2 := Subset.antisymm
      (fun x hx => hmeet.subset ⟨hAK hx.1, hx.2⟩)
      (fun x hx => ⟨hattach (hmeet.symm.subset hx), (hmeet.symm.subset hx).2⟩)
    obtain ⟨B, hBfin, hBspace⟩ := hD.isPolyhedron.exists_simplicialComplex
    obtain ⟨R, hRfin, hRspace⟩ :=
      ((isPolyhedron_space A).union hD.isPolyhedron).exists_simplicialComplex
    let _ : Finite B.faces := hBfin.to_subtype
    let _ : Finite R.faces := hRfin.to_subtype
    have hχR := eulerChar_eq_add_of_space_union_of_isPLSphere_one R A B
      (by rw [hBspace]; exact hRspace) (by rw [hBspace, hAD]; exact hG)
    have hχB := eulerChar_of_isPLBall B (hBspace.symm ▸ hD)
    have hfR : IsPLHomeomorphOn f R.space (connectedComponentComplex Q (e c₀)).space := by
      rw [hRspace]
      simpa only [A, ↓reduceIte] using hcomp c₀
    have hχQ := eulerChar_eq_of_isPLHomeomorphOn R (connectedComponentComplex Q (e c₀)) hfR
    dsimp only [A] at hχR
    omega
  · intro c hc
    have hfC : IsPLHomeomorphOn f (connectedComponentComplex K c).space
        (connectedComponentComplex Q (e c)).space := by
      simpa only [ite_eq_right hc, union_empty] using hcomp c
    exact (eulerChar_eq_of_isPLHomeomorphOn (connectedComponentComplex K c)
      (connectedComponentComplex Q (e c)) hfC).symm

end DifferentialGeometry.Topology.PiecewiseLinear
