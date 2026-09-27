/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PLAnnulusEnds
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryGluing
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldInteriorConnected
import DifferentialGeometry.Topology.PiecewiseLinear.SurfacePatchReplacement

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem IsPLAnnulusWithEnds.exists_closed_surface_union {C B J₀ J₁ : Set E3}
    (hC : IsPLAnnulusWithEnds C J₀ J₁) (hB : IsPLAnnulusWithEnds B J₀ J₁)
    (hCB : C ∩ B = J₀ ∪ J₁) :
    ∃ Q : Geometry.SimplicialComplex ℝ E3, Q.faces.Finite ∧
      IsCombinatorialManifold 2 Q ∧ IsConnected Q.space ∧ Q.space = C ∪ B := by
  classical
  let _ : DecidableEq E3 := fun a b => Classical.propDecidable (a = b)
  obtain ⟨K, hKfin, hK, hKc, hKC, hKb⟩ := hC.exists_complex
  obtain ⟨L, hLfin, hL, hLc, hLB, hLb⟩ := hB.exists_complex
  let _ : Finite K.faces := hKfin.to_subtype
  let _ : Finite L.faces := hLfin.to_subtype
  have hmeetK : K.space ∩ L.space = (boundaryComplex 2 K).space := by
    rw [hKC, hLB, hCB, hKb]
  have hmeetL : K.space ∩ L.space = (boundaryComplex 2 L).space := by
    rw [hKC, hLB, hCB, hLb]
  obtain ⟨Q, hQfin, hQ, hQspace⟩ :=
    exists_isCombinatorialManifold_space_union K L hK hL hmeetK hmeetL
  have hne : (K.space ∩ L.space).Nonempty := by
    rw [hKC, hLB, hCB]
    obtain ⟨J, ρ, hJ, -, h₀, -⟩ := hC
    rw [h₀]
    exact ((hJ.nonempty.prod (singleton_nonempty (0 : ℝ))).image ρ).mono subset_union_left
  refine ⟨Q, hQfin, hQ, hQspace.symm ▸ hKc.union hne hLc, ?_⟩
  rw [hQspace, hKC, hLB]

theorem IsPLAnnulusWithEnds.separates_after_delete_interior {C B J₀ J₁ U S M : Set E3}
    (hC : IsPLAnnulusWithEnds C J₀ J₁) (hB : IsPLAnnulusWithEnds B J₀ J₁)
    (hCB : C ∩ B = J₀ ∪ J₁) (hU : IsOpen U) (hS : IsTopologicalSolidTorus S)
    (hSU : S ⊆ U) (hCS : C ∪ B ⊆ interior S) (hCM : C ⊆ M) (hBM : B ⊆ M)
    (hR : IsClosed (((↑) : U → E3) ⁻¹' (M \ (C \ (J₀ ∪ J₁)))))
    {a b : E3} (haS : a ∉ S) (hbS : b ∉ S)
    (hsep : Separates (((↑) : U → E3) ⁻¹' M) (((↑) : U → E3) ⁻¹' {a})
      (((↑) : U → E3) ⁻¹' {b})) :
    Separates (((↑) : U → E3) ⁻¹' (M \ (C \ (J₀ ∪ J₁))))
      (((↑) : U → E3) ⁻¹' {a}) (((↑) : U → E3) ⁻¹' {b}) := by
  classical
  let _ : DecidableEq E3 := fun a b => Classical.propDecidable (a = b)
  obtain ⟨Q, hQfin, hQ, hQc, hQspace⟩ := hC.exists_closed_surface_union hB hCB
  let _ : Finite Q.faces := hQfin.to_subtype
  have hQM : Q.space ⊆ M := hQspace.subset.trans (union_subset hCM hBM)
  have hCQ : C ⊆ Q.space := subset_union_left.trans hQspace.symm.subset
  have hout : M \ Q.space = (M \ (C \ (J₀ ∪ J₁))) \ Q.space := by
    ext x
    exact ⟨fun hx => ⟨⟨hx.1, fun hc => hx.2 (hCQ hc.1)⟩, hx.2⟩,
      fun hx => ⟨hx.1.1, hx.2⟩⟩
  have hpatchEq : Q.space \ (M \ (C \ (J₀ ∪ J₁))) = C \ (J₀ ∪ J₁) := by
    ext x
    constructor
    · intro hx
      by_contra hn
      exact hx.2 ⟨hQM hx.1, hn⟩
    · intro hx
      exact ⟨hCQ hx.1, fun hr => hr.2 hx⟩
  have hpatch : IsPreconnected (Q.space \ (M \ (C \ (J₀ ∪ J₁)))) := by
    rw [hpatchEq]
    obtain ⟨K, hKfin, hK, hKc, hKC, hKb⟩ := hC.exists_complex
    let _ : Finite K.faces := hKfin.to_subtype
    simpa only [hKC, hKb] using
      (hK.isConnected_sdiff_boundaryComplex_space hKc).isPreconnected
  exact hQ.separates_of_connected_surface_patch Q hQc hU hS hSU
    (hQspace.subset.trans hCS) hR hout hpatch haS hbS hsep

end DifferentialGeometry.Topology.PiecewiseLinear
