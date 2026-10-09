/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BallGluingTwo
import DifferentialGeometry.Topology.PiecewiseLinear.BallDensity
import DifferentialGeometry.Topology.PiecewiseLinear.IntervalHomeomorph

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem exists_isPLHomeomorphOn_map_arc_eqOn_disjoint_arc_planar
    {S D A B : Set (EuclideanSpace ℝ (Fin 2))}
    (hS : IsPLSphere 1 S) (hD : IsPLBall 1 D) (hDS : D ⊆ S)
    (hA : IsPLBall 1 A) (hAS : A ⊆ S) (hB : IsPLBall 1 B) (hBS : B ⊆ S)
    (hDA : Disjoint D A) (hDB : Disjoint D B) :
    ∃ G : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2),
      IsPLHomeomorphOn G S S ∧ G '' A = B ∧ EqOn G id D := by
  classical
  obtain ⟨p, q, hDpq⟩ := hD.isArc.exists_isArcBetween
  obtain ⟨R, hcut, _, hR⟩ :=
    exists_isCutPair_of_isArcBetween_subset_isPLSphere hS hDpq hDS
  obtain ⟨γ, hγ, hγ0, hγ1⟩ := exists_isPLHomeomorphOn_Icc_of_isArcBetween hR hcut.snd
  let η := Function.invFunOn γ (Icc (0 : ℝ) 1)
  have hsub {C : Set (EuclideanSpace ℝ (Fin 2))} (hCS : C ⊆ S)
      (hDC : Disjoint D C) : C ⊆ R := by
    intro x hx
    rcases hcut.union_eq.symm.subset (hCS hx) with hxD | hxR
    · exact (disjoint_left.mp hDC hxD hx).elim
    · exact hxR
  have hinterior {C : Set (EuclideanSpace ℝ (Fin 2))} (hCS : C ⊆ S)
      (hDC : Disjoint D C) : η '' C ⊆ Ioo 0 1 := by
    rintro _ ⟨x, hx, rfl⟩
    have hxR := hsub hCS hDC hx
    have ht := hγ.symm.bijOn.mapsTo hxR
    have hzero : η x ≠ 0 := by
      intro hz
      change Function.invFunOn γ (Icc 0 1) x = 0 at hz
      have hxD : x ∈ D := by
        rw [← hγ.bijOn.invOn_invFunOn.2 hxR, hz, hγ0]
        exact hcut.fst.left_mem
      exact disjoint_left.mp hDC hxD hx
    have hone : η x ≠ 1 := by
      intro hz
      change Function.invFunOn γ (Icc 0 1) x = 1 at hz
      have hxD : x ∈ D := by
        rw [← hγ.bijOn.invOn_invFunOn.2 hxR, hz, hγ1]
        exact hcut.fst.right_mem
      exact disjoint_left.mp hDC hxD hx
    exact ⟨lt_of_le_of_ne ht.1 hzero.symm, lt_of_le_of_ne ht.2 hone⟩
  have hAη : IsPLBall 1 (η '' A) :=
    hA.of_isPLHomeomorphOn (hγ.symm.restrict hA.isPolyhedron (hsub hAS hDA))
  have hBη : IsPLBall 1 (η '' B) :=
    hB.of_isPLHomeomorphOn (hγ.symm.restrict hB.isPolyhedron (hsub hBS hDB))
  obtain ⟨f, hf, hf0, hf1, hfAB⟩ := exists_isPLHomeomorphOn_Icc_map_compact_subset
    hAη.isPolyhedron.isCompact hAη.isConnected hAη.nontrivial (hinterior hAS hDA)
    hBη.isPolyhedron.isCompact hBη.isConnected hBη.nontrivial (hinterior hBS hDB)
  let g := γ ∘ f ∘ η
  have hg : IsPLHomeomorphOn g R R := hγ.symm.trans (hf.trans hγ)
  have hgγ (t : ℝ) (ht : t ∈ Icc 0 1) : g (γ t) = γ (f t) := by
    change γ (f (Function.invFunOn γ (Icc 0 1) (γ t))) = γ (f t)
    rw [hγ.bijOn.invOn_invFunOn.1 ht]
  have hgp : g p = p := by rw [← hγ0, hgγ 0 (by norm_num), hf0]
  have hgq : g q = q := by rw [← hγ1, hgγ 1 (by norm_num), hf1]
  have hfix : EqOn id g (D ∩ R) := by
    rw [hcut.inter_eq]
    rintro x (rfl | rfl)
    · exact hgp.symm
    · exact hgq.symm
  have hG := hD.isPolyhedron.isPLHomeomorphOn_id.piecewise hg
    hD.isPolyhedron hR.isPolyhedron hfix (image_id _)
  rw [hcut.union_eq] at hG
  refine ⟨D.piecewise id g, hG, ?_, D.piecewise_eqOn id g⟩
  have hGA : EqOn (D.piecewise id g) g A := fun _ hx =>
    D.piecewise_eq_of_notMem id g (fun hxD => disjoint_left.mp hDA hxD hx)
  rw [hGA.image_eq]
  change (γ ∘ (f ∘ η)) '' A = B
  rw [image_comp, image_comp, hfAB, image_image]
  exact (show EqOn (γ ∘ η) id B from fun _ hx =>
    hγ.bijOn.invOn_invFunOn.2 (hsub hBS hDB hx)).image_eq.trans (image_id B)

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem exists_isPLHomeomorphOn_map_arc_eqOn_disjoint_arc
    {S D A B : Set E} (hS : IsPLSphere 1 S) (hD : IsPLBall 1 D) (hDS : D ⊆ S)
    (hA : IsPLBall 1 A) (hAS : A ⊆ S) (hB : IsPLBall 1 B) (hBS : B ⊆ S)
    (hDA : Disjoint D A) (hDB : Disjoint D B) :
    ∃ G : E → E, IsPLHomeomorphOn G S S ∧ G '' A = B ∧ EqOn G id D := by
  obtain ⟨C, f, hC, hf⟩ := exists_planar_isPLHomeomorphOn_of_isPLSphere_one hS
  have hD' := hD.of_isPLHomeomorphOn (hf.restrict hD.isPolyhedron hDS)
  have hA' := hA.of_isPLHomeomorphOn (hf.restrict hA.isPolyhedron hAS)
  have hB' := hB.of_isPLHomeomorphOn (hf.restrict hB.isPolyhedron hBS)
  have hsub {P : Set E} (hPS : P ⊆ S) : f '' P ⊆ C :=
    (image_mono hPS).trans hf.image_eq.subset
  have hdis {P : Set E} (hPS : P ⊆ S) (hDP : Disjoint D P) :
      Disjoint (f '' D) (f '' P) := by
    apply disjoint_left.mpr
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, heq⟩
    exact disjoint_left.mp hDP hx (hf.bijOn.injOn (hPS hy) (hDS hx) heq ▸ hy)
  obtain ⟨k, hk, hkA, hkfix⟩ := exists_isPLHomeomorphOn_map_arc_eqOn_disjoint_arc_planar
    hC hD' (hsub hDS) hA' (hsub hAS) hB' (hsub hBS) (hdis hAS hDA) (hdis hBS hDB)
  let fi := Function.invFunOn f S
  refine ⟨fi ∘ k ∘ f, (hf.trans hk).trans hf.symm, ?_, ?_⟩
  · rw [image_comp, image_comp, hkA, image_image]
    exact (show EqOn (fi ∘ f) id B from fun _ hx =>
      hf.bijOn.invOn_invFunOn.1 (hBS hx)).image_eq.trans (image_id B)
  · intro x hx
    change fi (k (f x)) = x
    rw [hkfix ⟨x, hx, rfl⟩]
    exact hf.bijOn.invOn_invFunOn.1 (hDS hx)

theorem exists_isPLHomeomorphOn_map_arc_pair_eqOn_arc
    {S D₀ D₁ : Set E} {S' D₀' D₁' : Set F}
    (hS : IsPLSphere 1 S) (hS' : IsPLSphere 1 S')
    (hD₀ : IsPLBall 1 D₀) (hD₀S : D₀ ⊆ S)
    (hD₁ : IsPLBall 1 D₁) (hD₁S : D₁ ⊆ S) (hdis : Disjoint D₀ D₁)
    (hD₁' : IsPLBall 1 D₁') (hD₁'S' : D₁' ⊆ S') (hdis' : Disjoint D₀' D₁')
    {g : E → F} (hg : IsPLHomeomorphOn g D₀ D₀') (hD₀'S' : D₀' ⊆ S') :
    ∃ G : E → F, IsPLHomeomorphOn G S S' ∧ EqOn G g D₀ ∧ G '' D₁ = D₁' := by
  obtain ⟨f, hf, hfg⟩ := exists_isPLHomeomorphOn_eqOn_arc_of_isPLSphere_one_of_ambient
    hS hS' hD₀ hD₀S hg hD₀'S'
  have hfD₀ : f '' D₀ = D₀' := hfg.image_eq.trans hg.image_eq
  have hA : IsPLBall 1 (f '' D₁) :=
    hD₁.of_isPLHomeomorphOn (hf.restrict hD₁.isPolyhedron hD₁S)
  have hAS : f '' D₁ ⊆ S' := (image_mono hD₁S).trans hf.image_eq.subset
  have hDA : Disjoint D₀' (f '' D₁) := by
    rw [← hfD₀]
    apply disjoint_left.mpr
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, heq⟩
    exact disjoint_left.mp hdis hx (hf.bijOn.injOn (hD₁S hy) (hD₀S hx) heq ▸ hy)
  obtain ⟨k, hk, hkA, hkfix⟩ := exists_isPLHomeomorphOn_map_arc_eqOn_disjoint_arc
    hS' (hD₀.of_isPLHomeomorphOn hg) hD₀'S' hA hAS hD₁' hD₁'S' hDA hdis'
  refine ⟨k ∘ f, hf.trans hk, ?_, (image_comp k f D₁).trans hkA⟩
  intro x hx
  change k (f x) = g x
  exact (hkfix (hfD₀ ▸ mem_image_of_mem f hx)).trans (hfg hx)

open Classical in
theorem exists_isPLHomeomorphOn_map_arc_pair_of_boundaryComplex
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (L : Geometry.SimplicialComplex ℝ F) [Finite L.faces]
    (hK : IsPLBall 2 K.space) (hL : IsPLBall 2 L.space)
    {D₀ D₁ : Set E} {D₀' D₁' : Set F}
    (hD₀ : IsPLBall 1 D₀) (hD₀K : D₀ ⊆ (boundaryComplex 2 K).space)
    (hD₁ : IsPLBall 1 D₁) (hD₁K : D₁ ⊆ (boundaryComplex 2 K).space)
    (hdis : Disjoint D₀ D₁) (hD₁' : IsPLBall 1 D₁')
    (hD₁'L : D₁' ⊆ (boundaryComplex 2 L).space) (hdis' : Disjoint D₀' D₁')
    {g : E → F} (hg : IsPLHomeomorphOn g D₀ D₀')
    (hD₀'L : D₀' ⊆ (boundaryComplex 2 L).space) :
    ∃ G : E → F, IsPLHomeomorphOn G K.space L.space ∧ EqOn G g D₀ ∧ G '' D₁ = D₁' := by
  let _ : DecidableEq E := Classical.decEq _
  let _ : DecidableEq F := Classical.decEq _
  obtain ⟨f, hf, hfg, hfD₁⟩ := exists_isPLHomeomorphOn_map_arc_pair_eqOn_arc
    (isPLSphere_boundaryComplex_space_of_isPLBall K hK)
    (isPLSphere_boundaryComplex_space_of_isPLBall L hL)
    hD₀ hD₀K hD₁ hD₁K hdis hD₁' hD₁'L hdis' hg hD₀'L
  obtain ⟨G, hG, hGf⟩ := exists_isPLHomeomorphOn_of_boundaryComplex K L hK hL hf
  exact ⟨G, hG, (hGf.mono hD₀K).trans hfg, (hGf.mono hD₁K).image_eq.trans hfD₁⟩

end DifferentialGeometry.Topology.PiecewiseLinear
