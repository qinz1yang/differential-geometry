/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SphericalDiskPair
import DifferentialGeometry.Topology.PiecewiseLinear.SphereDiskMarked
import DifferentialGeometry.Topology.PiecewiseLinear.ConePairExtension
import DifferentialGeometry.Topology.PiecewiseLinear.BallPairModel
import DifferentialGeometry.Topology.PiecewiseLinear.ConvexPolytope
import DifferentialGeometry.Topology.PiecewiseLinear.PrismBoundary

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

omit [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] in
theorem IsConeBase.exists_stdSimplex_homeomorph_apex {n : ℕ} {p : E}
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsConeBase p K) (hS : IsPLSphere n K.space) :
    ∃ q : (Fin (n + 2) → ℝ) → E,
      IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin (n + 2))) (coneSet p K.space) ∧
      q (stdCenter n) = p := by
  classical
  obtain ⟨q₀, hq₀⟩ := hS
  let _ : Finite (simplexBoundary (stdVertices n) (stdVertices_affineIndependent n)).faces :=
    (simplexBoundary_faces_finite _ _).to_subtype
  have hqbase : IsPLHomeomorphOn q₀
      (simplexBoundary (stdVertices n) (stdVertices_affineIndependent n)).space K.space := by
    rwa [simplexBoundary_stdVertices_space]
  obtain ⟨q, hq, -, hqa, -⟩ :=
    exists_isPLHomeomorphOn_coneComplex (isConeBase_std n) hK hqbase
  rw [coneComplex_std_space, coneComplex_space_eq_coneSet] at hq
  exact ⟨q, hq, hqa⟩

theorem exists_isPLHomeomorphOn_map_disk_pair_eqOn_disk_marked
    {S D₀ D₁ : Set E} {S' D₀' D₁' : Set F}
    (hS : IsPLSphere 2 S) (hS' : IsPLSphere 2 S')
    (hD₀ : IsPLBall 2 D₀) (hD₀S : D₀ ⊆ S)
    {q : (Fin 3 → ℝ) → E} {q' : (Fin 3 → ℝ) → F}
    (hq : IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₁)
    (hq' : IsPLHomeomorphOn q' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₁')
    (hD₁S : D₁ ⊆ S) (hD₁'S' : D₁' ⊆ S')
    (hdis : Disjoint D₀ D₁) (hdis' : Disjoint D₀' D₁')
    {g : E → F} (hg : IsPLHomeomorphOn g D₀ D₀') (hD₀'S' : D₀' ⊆ S') :
    ∃ G : E → F, IsPLHomeomorphOn G S S' ∧ EqOn G g D₀ ∧ G '' D₁ = D₁' ∧
      G (q (stdCenter 1)) = q' (stdCenter 1) := by
  classical
  have hD₁ : IsPLBall 2 D₁ := ⟨q, hq⟩
  have hD₁' : IsPLBall 2 D₁' := ⟨q', hq'⟩
  obtain ⟨f, hf, hfg, hfD₁⟩ := exists_isPLHomeomorphOn_map_disk_pair_eqOn_disk
    hS hS' hD₀ hD₀S hD₁ hD₁S hdis hD₁' hD₁'S' hdis' hg hD₀'S'
  have hfD : IsPLHomeomorphOn f D₁ D₁' := by
    have h := hf.restrict hD₁.isPolyhedron hD₁S
    rwa [hfD₁] at h
  have hqf : IsPLHomeomorphOn (f ∘ q) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₁' := hq.trans hfD
  have hbd : (f ∘ q) '' stdSimplexBoundary 2 = q' '' stdSimplexBoundary 2 :=
    hqf.image_stdSimplexBoundary_congr hq'
  have hBpoly : IsPolyhedron (stdSimplexBoundary 2) := by
    rw [← simplexBoundary_stdVertices_space]
    let _ := (simplexBoundary_faces_finite (stdVertices 1)
      (stdVertices_affineIndependent 1)).to_subtype
    exact isPolyhedron_space _
  have hid : IsPLHomeomorphOn (id : F → F)
      ((f ∘ q) '' stdSimplexBoundary 2) (q' '' stdSimplexBoundary 2) := by
    rw [hbd]
    have hqB := hq'.restrict hBpoly (fun _ hx => hx.1)
    exact (hBpoly.image_of_isPiecewiseAffineOn hqB.isPiecewiseAffineOn
      hqB.bijOn.injOn).isPLHomeomorphOn_id
  obtain ⟨k, hk, hkfix, hkcenter⟩ :=
    exists_isPLHomeomorphOn_extension_marked_stdSimplexBoundary hqf hq' hid
  rw [hbd] at hkfix
  let A := closure (S' \ D₁')
  have hA : IsPLBall 2 A := hS'.isPLBall_closure_sdiff hD₁' hD₁'S'
  have hmeet : D₁' ∩ A = q' '' stdSimplexBoundary 2 :=
    hS'.inter_closure_sdiff_eq_image_stdSimplexBoundary hq' hD₁'S'
  have hcover : D₁' ∪ A = S' := by
    refine Subset.antisymm
      (union_subset hD₁'S' (closure_minimal sdiff_subset hS'.isPolyhedron.isClosed)) ?_
    intro x hx
    by_cases hxD : x ∈ D₁'
    · exact Or.inl hxD
    · exact Or.inr (subset_closure ⟨hx, hxD⟩)
  have hcompat : EqOn k id (D₁' ∩ A) := by rwa [hmeet]
  have hκ : IsPLHomeomorphOn (D₁'.piecewise k id) S' S' := by
    have h := hk.piecewise hA.isPolyhedron.isPLHomeomorphOn_id
      hD₁'.isPolyhedron hA.isPolyhedron hcompat
      (hcompat.image_eq.trans (image_id _))
    rwa [hcover] at h
  have hκD : EqOn (D₁'.piecewise k id) k D₁' := D₁'.piecewise_eqOn k id
  refine ⟨(D₁'.piecewise k id) ∘ f, hf.trans hκ, ?_, ?_, ?_⟩
  · intro x hx
    change D₁'.piecewise k id (f x) = g x
    have hxD₀ : f x ∈ D₀' := hfg hx ▸ hg.bijOn.mapsTo hx
    rw [piecewise_eq_of_notMem _ _ _ (fun hxD₁ => disjoint_left.mp hdis' hxD₀ hxD₁)]
    exact hfg hx
  · rw [image_comp, hfD₁, hκD.image_eq, hk.image_eq]
  · have hc : stdCenter 1 ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3) :=
      openSimplex_stdVertices_subset_stdSimplex (stdCenter_mem_openSimplex 1)
    change D₁'.piecewise k id (f (q (stdCenter 1))) = q' (stdCenter 1)
    exact (hκD (hqf.bijOn.mapsTo hc)).trans hkcenter

theorem exists_isPLHomeomorphOn_cone_pair_map_caps_marked
    {p : E} {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    {p' : F} {K' : Geometry.SimplicialComplex ℝ F} [Finite K'.faces]
    (hK : IsConeBase p K) (hK' : IsConeBase p' K')
    (hS : IsPLSphere 2 K.space) (hS' : IsPLSphere 2 K'.space)
    {D₀ D₁ : Set E} {D₀' D₁' : Set F}
    (hD₀ : IsPLBall 2 D₀) (hD₀S : D₀ ⊆ K.space)
    {q : (Fin 3 → ℝ) → E} {q' : (Fin 3 → ℝ) → F}
    (hq : IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₁)
    (hq' : IsPLHomeomorphOn q' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₁')
    (hD₁S : D₁ ⊆ K.space) (hD₁'S' : D₁' ⊆ K'.space)
    (hdis : Disjoint D₀ D₁) (hdis' : Disjoint D₀' D₁')
    {g : E → F} (hg : IsPLHomeomorphOn g D₀ D₀') (hD₀'S' : D₀' ⊆ K'.space)
    {x : E} (hx : x ∈ D₀) :
    ∃ G : E → F, IsPLHomeomorphOn G (coneSet p K.space) (coneSet p' K'.space) ∧
      EqOn G g D₀ ∧ G p = p' ∧ G '' D₁ = D₁' ∧
      G (q (stdCenter 1)) = q' (stdCenter 1) ∧
      G '' coneSet p {x, q (stdCenter 1)} = coneSet p' {g x, q' (stdCenter 1)} := by
  classical
  obtain ⟨f, hf, hfg, hfD, hfc⟩ :=
    exists_isPLHomeomorphOn_map_disk_pair_eqOn_disk_marked hS hS' hD₀ hD₀S
      hq hq' hD₁S hD₁'S' hdis hdis' hg hD₀'S'
  obtain ⟨G, hG, hGf, hGp, -, hGrad⟩ :=
    exists_isPLHomeomorphOn_coneComplex_pair hK hK' hf
  rw [coneComplex_space_eq_coneSet, coneComplex_space_eq_coneSet] at hG
  refine ⟨G, hG, (hGf.mono hD₀S).trans hfg, hGp,
    (hGf.mono hD₁S).image_eq.trans hfD, ?_, ?_⟩
  · have hc : stdCenter 1 ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3) :=
      openSimplex_stdVertices_subset_stdSimplex (stdCenter_mem_openSimplex 1)
    exact (hGf (hD₁S (hq.bijOn.mapsTo hc))).trans hfc
  have hc : stdCenter 1 ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3) :=
    openSimplex_stdVertices_subset_stdSimplex (stdCenter_mem_openSimplex 1)
  have hsub : ({x, q (stdCenter 1)} : Set E) ⊆ K.space := by
    intro z hz
    rcases mem_insert_iff.mp hz with rfl | hz
    · exact hD₀S hx
    · exact mem_singleton_iff.mp hz ▸ hD₁S (hq.bijOn.mapsTo hc)
  rw [hGrad _ hsub, image_pair, hfg hx, hfc]

theorem coneSet_prism_axis {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (p : X) : coneSet (p, (1 / 2 : ℝ)) {(p, 0), (p, 1)} = {p} ×ˢ Icc (0 : ℝ) 1 := by
  rw [coneSet_pair_eq_union_segment, ← Prod.image_mk_segment_right,
    ← Prod.image_mk_segment_right, ← image_union, segment_symm ℝ (1 / 2 : ℝ) 0,
    segment_eq_Icc (by norm_num : (0 : ℝ) ≤ 1 / 2),
    segment_eq_Icc (by norm_num : (1 / 2 : ℝ) ≤ 1),
    Icc_union_Icc_eq_Icc (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1)]
  exact singleton_prod.symm

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
theorem exists_isPLHomeomorphOn_prism_cone_marked
    {P : Set (EuclideanSpace ℝ (Fin 2))} (hP : IsHPolytope P)
    {a : EuclideanSpace ℝ (Fin 2)} (ha : a ∈ interior P)
    {p : F} {K : Geometry.SimplicialComplex ℝ F} [Finite K.faces]
    (hK : IsConeBase p K) (hS : IsPLSphere 2 K.space)
    {D₀ D₁ : Set F} (hD₀S : D₀ ⊆ K.space) (hD₁S : D₁ ⊆ K.space)
    (hdis : Disjoint D₀ D₁) {g : EuclideanSpace ℝ (Fin 2) → F}
    (hg : IsPLHomeomorphOn g P D₀) {q : (Fin 3 → ℝ) → F}
    (hq : IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₁) :
    ∃ G : EuclideanSpace ℝ (Fin 2) × ℝ → F,
      IsPLHomeomorphOn G (P ×ˢ Icc (0 : ℝ) 1) (coneSet p K.space) ∧
      (∀ x ∈ P, G (x, 0) = g x) ∧ G (a, 1 / 2) = p ∧
      G '' (P ×ˢ ({1} : Set ℝ)) = D₁ ∧ G (a, 1) = q (stdCenter 1) ∧
      G '' ({a} ×ˢ Icc (0 : ℝ) 1) = coneSet p {g a, q (stdCenter 1)} := by
  classical
  have hPball : IsPLBall 2 P := by simpa using hP.isPLBall ⟨a, ha⟩
  have hC : IsHPolytope (P ×ˢ Icc (0 : ℝ) 1) := hP.prod isHPolytope_Icc
  have hac : (a, (1 / 2 : ℝ)) ∈ interior (P ×ˢ Icc (0 : ℝ) 1) := by
    rw [interior_prod_eq, interior_Icc]
    exact ⟨ha, by norm_num⟩
  have hCS : IsPLSphere 2 (frontier (P ×ˢ Icc (0 : ℝ) 1)) :=
    hC.isPLSphere_frontier (by simp [Module.finrank_prod]) ⟨_, hac⟩
  obtain ⟨R, hRfin, hRspace⟩ := hCS.isPolyhedron.exists_simplicialComplex
  let _ : Finite R.faces := hRfin.to_subtype
  have hR : IsConeBase (a, (1 / 2 : ℝ)) R :=
    isConeBase_of_space_subset_frontier_convex hC.convex hC.isCompact.isClosed hac R
      hRspace.subset
  have hRcone : coneSet (a, (1 / 2 : ℝ)) R.space = P ×ˢ Icc (0 : ℝ) 1 := by
    rw [← coneComplex_space_eq_coneSet hR]
    exact coneComplex_space_eq_of_convex hC.convex hC.isCompact
      (interior_subset hac) hR hRspace
  have hcap (t : ℝ) (ht : t = 0 ∨ t = 1) : P ×ˢ {t} ⊆ R.space := by
    rw [hRspace, frontier_prod_eq, hP.isCompact.isClosed.closure_eq,
      isClosed_Icc.closure_eq, frontier_Icc zero_le_one]
    intro z hz
    exact Or.inl ⟨hz.1, hz.2.symm ▸ ht⟩
  have hcaps : Disjoint (P ×ˢ ({0} : Set ℝ)) (P ×ˢ ({1} : Set ℝ)) := by
    refine disjoint_left.mpr fun z hz₀ hz₁ => ?_
    exact zero_ne_one (hz₀.2.symm.trans hz₁.2)
  obtain ⟨r, hr, hra⟩ := hPball.exists_isPLHomeomorphOn_stdSimplex_stdCenter_eq ha
  have hr1 : IsPLHomeomorphOn ((fun x => (x, (1 : ℝ))) ∘ r)
      (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (P ×ˢ {1}) :=
    hr.trans (hP.isPolyhedron.isPLHomeomorphOn_prod_const 1)
  have hgf : IsPLHomeomorphOn (g ∘ Prod.fst) (P ×ˢ ({0} : Set ℝ)) D₀ :=
    (hP.isPolyhedron.isPLHomeomorphOn_fst_prod_const 0).trans hg
  obtain ⟨G, hG, hGg, hGp, hGtop, hGend, hGaxis⟩ :=
    exists_isPLHomeomorphOn_cone_pair_map_caps_marked hR hK (hRspace.symm ▸ hCS) hS
      (hPball.of_isPLHomeomorphOn (hP.isPolyhedron.isPLHomeomorphOn_prod_const 0))
      (hcap 0 (Or.inl rfl)) hr1 hq (hcap 1 (Or.inr rfl)) hD₁S hcaps hdis hgf hD₀S
      (x := (a, 0)) ⟨interior_subset ha, rfl⟩
  refine ⟨G, hRcone ▸ hG, fun x hx => hGg ⟨hx, rfl⟩, hGp, hGtop, ?_, ?_⟩
  · simpa only [Function.comp_apply, hra] using hGend
  · simpa only [Function.comp_apply, hra, coneSet_prism_axis] using hGaxis

end DifferentialGeometry.Topology.PiecewiseLinear
