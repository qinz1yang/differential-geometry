/-
Copyright (c) 2026 Antigravity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antigravity
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ControlledInwardPush
import DifferentialGeometry.Topology.PiecewiseLinear.GeneralPosition
import DifferentialGeometry.Topology.PiecewiseLinear.Groupoid
import DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePLPastingManifold
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.SingularCell
import DifferentialGeometry.Topology.PiecewiseLinear.PLHomeomorph
import Mathlib.Geometry.Manifold.LocalInvariantProperties

/-!
Construction of a glued singular two-cell from a vertex map in an adapted chart.
-/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

open Classical in
theorem exists_gluedCell_of_vertexMap_in_adaptedChart {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] (D : SingularTwoCell M)
    {V : Set M} (hVopen : IsOpen V)
    (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (hec : ec ∈ (plGroupoid 3).maximalAtlas M) (hVec : V ⊆ ec.source)
    (Rc Ac : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    {Ω Nb : Set (EuclideanSpace ℝ (Fin 2))}
    (hRfin : Rc.faces.Finite) (hRman : IsCombinatorialManifoldWithBoundary 2 Rc)
    (hAR : Ac.faces ⊆ Rc.faces) (hRdom : Rc.space ⊆ D.domain) (hRV : Rc.space ⊆ ⇑D ⁻¹' V)
    (hΩ : IsOpen Ω) (hΩR : D.domain ∩ Ω ⊆ Rc.space) (hNb : IsOpen Nb)
    (hNbfr : Rc.space \ Ω ⊆ Nb) (hNbA : Rc.space ∩ Nb ⊆ Ac.space)
    (Rs : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    (φ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hsub : IsSubdivision Rs Rc) (hRsfin : Rs.faces.Finite)
    (hfrozen : EqOn (simplicialMap Rs φ) (fun x => ec (D x)) Ac.space)
    (hpl : IsPiecewiseAffineOn (simplicialMap Rs φ) Rc.space)
    (hmaps : MapsTo (simplicialMap Rs φ) Rc.space (⇑ec '' V)) :
    ∃ D' : SingularTwoCell M, D'.domain = D.domain ∧
      EqOn (⇑D') (fun x => ec.symm (simplicialMap Rs φ x)) Rc.space ∧
      EqOn (⇑D') (⇑D) Rc.spaceᶜ := by
  let _ := hVopen
  let _ := hRman
  let _ := hAR
  let _ := hsub
  let _ := hRsfin
  let h := simplicialMap Rs φ
  let g : EuclideanSpace ℝ (Fin 2) → M :=
    fun x => if x ∈ Rc.space then ec.symm (h x) else D x
  have _ : Finite Rc.faces := hRfin.to_subtype
  have hRclosed : IsClosed Rc.space := (isPolyhedron_space Rc).isCompact.isClosed
  have hVtarget : ⇑ec '' V ⊆ ec.target :=
    image_subset_iff.mpr (fun x hx => ec.map_source (hVec hx))
  have hhtarget : MapsTo h Rc.space ec.target := hmaps.mono_right hVtarget
  have hU1_eq : D.domain ∩ Ω = Rc.space ∩ Ω := by
    ext x
    exact ⟨fun hx => ⟨hΩR hx, hx.2⟩, fun hx => ⟨hRdom hx.1, hx.2⟩⟩
  have hU1_eq' : Ω ∩ D.domain = Rc.space ∩ Ω := by
    rw [inter_comm, hU1_eq]
  have hg_eq_D_on_Nb : ∀ x ∈ Rc.space ∩ Nb, g x = D x := by
    intro x hx
    have hxAc : x ∈ Ac.space := hNbA hx
    have hxV : D x ∈ V := hRV hx.1
    have hxsrc : D x ∈ ec.source := hVec hxV
    simp only [g, if_pos hx.1]
    have h_hx : h x = simplicialMap Rs φ x := rfl
    rw [h_hx, hfrozen hxAc, ec.left_inv hxsrc]
  let W₂ := Rc.spaceᶜ ∪ Nb
  have hW₂open : IsOpen W₂ := hRclosed.isOpen_compl.union hNb
  let U₂ := W₂ ∩ D.domain
  have hg_eq_D_on_U₂ : EqOn g D U₂ := by
    rintro x ⟨hxW₂, hxD⟩
    rcases hxW₂ with hxRcompl | hxNb
    · simp only [g, if_neg hxRcompl]
    · by_cases hxR : x ∈ Rc.space
      · exact hg_eq_D_on_Nb x ⟨hxR, hxNb⟩
      · simp only [g, if_neg hxR]
  have hcover : D.domain ⊆ (Ω ∩ D.domain) ∪ U₂ := by
    intro x hx
    by_cases hxR : x ∈ Rc.space
    · by_cases hxΩ : x ∈ Ω
      · exact Or.inl ⟨hxΩ, hx⟩
      · have hxNb : x ∈ Nb := hNbfr ⟨hxR, hxΩ⟩
        exact Or.inr ⟨Or.inr hxNb, hx⟩
    · exact Or.inr ⟨Or.inl hxR, hx⟩
  have hg_pl : IsPLOn 2 3 g D.domain := by
    intro x hx
    rcases hcover hx with ⟨hxΩ, -⟩ | hxU₂
    · have hU1_nhds : (Ω ∩ D.domain) ∈ 𝓝[D.domain] x :=
        mem_nhdsWithin.mpr ⟨Ω, hΩ, hxΩ, subset_rfl⟩
      have hxR : x ∈ Rc.space := hΩR ⟨hx, hxΩ⟩
      have hxhtgt : h x ∈ ec.target := hhtarget hxR
      have hgx_src : g x ∈ ec.source := by
        simp only [g, if_pos hxR]
        exact ec.map_target hxhtgt
      have hProp := piecewiseAffineProperty_localInvariantProp (n := 2) (m := 3)
      have hlift := hProp.liftPropWithinAt_indep_chart_target
        (s := Ω ∩ D.domain) (x := x) hec hgx_src
      have hgh : EqOn (ec ∘ g) h (Ω ∩ D.domain) := by
        intro y hy
        have hyR : y ∈ Rc.space := hΩR ⟨hy.2, hy.1⟩
        have hytgt : h y ∈ ec.target := hhtarget hyR
        simp only [Function.comp_apply, g, if_pos hyR]
        exact ec.right_inv hytgt
      have hxnhds : Ω ∈ 𝓝 x := hΩ.mem_nhds hxΩ
      have hpa_x : IsPiecewiseAffineWithinAt h (Rc.space ∩ Ω) x :=
        (hpl x hxR).inter_of_mem_nhds hxnhds
      have hpa_U1 : IsPiecewiseAffineWithinAt h (Ω ∩ D.domain) x :=
        hU1_eq'.symm ▸ hpa_x
      have hpa_ecg : IsPiecewiseAffineWithinAt (ec ∘ g) (Ω ∩ D.domain) x :=
        hpa_U1.congr hgh
      have hlift_ecg : ChartedSpace.LiftPropWithinAt (piecewiseAffineProperty 2 3)
          (ec ∘ g) (Ω ∩ D.domain) x :=
        StructureGroupoid.liftPropWithinAt_self.mpr ⟨hpa_ecg.continuousWithinAt, hpa_ecg⟩
      have hcont_g : ContinuousWithinAt g (Ω ∩ D.domain) x := by
        have hcont_h : ContinuousWithinAt h (Ω ∩ D.domain) x := hpa_U1.continuousWithinAt
        have hmap_h : MapsTo h (Ω ∩ D.domain) ec.target := fun y hy =>
          hhtarget (hΩR ⟨hy.2, hy.1⟩)
        have hcont_comp : ContinuousWithinAt (ec.symm ∘ h) (Ω ∩ D.domain) x :=
          ec.continuousOn_symm.continuousWithinAt hxhtgt |>.comp hcont_h hmap_h
        refine hcont_comp.congr (fun y hy => ?_)
          (by simp only [Function.comp_apply, g, if_pos hxR])
        simp only [Function.comp_apply, g, if_pos (hΩR ⟨hy.2, hy.1⟩)]
      have hPL_U1 : IsPLWithinAt 2 3 g (Ω ∩ D.domain) x :=
        hlift.mpr ⟨hcont_g, hlift_ecg⟩
      have h_inter := hProp.liftPropWithinAt_inter' (g := g) (s := D.domain) hU1_nhds
      rw [inter_eq_right.mpr inter_subset_right] at h_inter
      exact h_inter.mp hPL_U1
    · have hU2_nhds : U₂ ∈ 𝓝[D.domain] x :=
        mem_nhdsWithin.mpr ⟨W₂, hW₂open, hxU₂.1, subset_rfl⟩
      have hD_x : IsPLWithinAt 2 3 D D.domain x := D.isPLOn x hx
      have hD_U2 : IsPLWithinAt 2 3 D U₂ x :=
        IsPLWithinAt.mono_of_mem_nhdsWithin hD_x inter_subset_right hU2_nhds
      have hProp := piecewiseAffineProperty_localInvariantProp (n := 2) (m := 3)
      have hg_U2 : IsPLWithinAt 2 3 g U₂ x :=
        hProp.liftPropWithinAt_congr_of_mem hD_U2 hg_eq_D_on_U₂ hxU₂
      have h_inter := hProp.liftPropWithinAt_inter' (g := g) (s := D.domain) hU2_nhds
      rw [inter_eq_right.mpr inter_subset_right] at h_inter
      exact h_inter.mp hg_U2
  let D' : SingularTwoCell M :=
    { domain := D.domain
      isPLBall_domain := D.isPLBall_domain
      toFun := g
      isPLOn := hg_pl }
  refine ⟨D', rfl, ?_, ?_⟩
  · intro x hx
    simp only [D', g, if_pos hx]
    rfl
  · intro x hx
    simp only [D', g, if_neg hx]

end DifferentialGeometry.Topology.PiecewiseLinear
