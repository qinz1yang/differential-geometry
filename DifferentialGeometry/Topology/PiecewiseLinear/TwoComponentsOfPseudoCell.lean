/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import Mathlib.Analysis.Normed.Module.Connected
import DifferentialGeometry.Topology.PiecewiseLinear.BallRegularClosed
import DifferentialGeometry.Topology.PiecewiseLinear.FreeFaceArc
import DifferentialGeometry.Topology.PiecewiseLinear.SphericalDiskComplement

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem IsOpenTopologicalCell.isConnected_sdiff_singleton {X : Type*} [TopologicalSpace X]
    {U : Set X} (hU : IsOpenTopologicalCell 2 U) {p : X} (hp : p ∈ U) :
    IsConnected (U \ {p}) ∧ U ⊆ closure (U \ {p}) := by
  obtain ⟨φ⟩ := hU
  let Θ : U ≃ₜ EuclideanSpace ℝ (Fin 2) := φ.trans Homeomorph.unitBall.symm
  have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin 2)) := by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
    exact_mod_cast (by norm_num : (1 : ℕ) < 2)
  have himg : ((↑) : U → X) '' (Θ ⁻¹' {Θ ⟨p, hp⟩}ᶜ) = U \ {p} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, fun hyp => hy ?_⟩
      have hyeq : y = ⟨p, hp⟩ := Subtype.ext hyp
      rw [hyeq]
      exact mem_singleton _
    · rintro ⟨hxU, hxp⟩
      refine ⟨⟨x, hxU⟩, fun hx => hxp ?_, rfl⟩
      exact congrArg Subtype.val (Θ.injective hx)
  refine ⟨?_, ?_⟩
  · rw [← himg, ← Θ.image_symm]
    exact ((isConnected_compl_singleton_of_one_lt_rank hrank _).image _
      Θ.symm.continuous.continuousOn).image _ continuous_subtype_val.continuousOn
  · intro x hxU
    have hcl : (⟨x, hxU⟩ : U) ∈ closure (Θ ⁻¹' {Θ ⟨p, hp⟩}ᶜ) := by
      rw [← Θ.preimage_closure, closure_compl_singleton]
      trivial
    rw [← himg]
    exact image_closure_subset_closure_image continuous_subtype_val ⟨_, hcl, rfl⟩

theorem isConnected_sdiff_of_isPLBall_inter {Q₁ Q₂ DQ : Set E3} (h₁ : IsPLBall 3 Q₁)
    (h₂ : IsPLBall 3 Q₂) (hQ : Q₁ ∩ Q₂ = DQ) (hD : IsPLBall 2 DQ) :
    IsConnected (Q₁ \ DQ) ∧ Q₁ ⊆ closure (Q₁ \ DQ) := by
  have hI : IsPLBall 2 (Q₁ ∩ Q₂) := by
    rw [hQ]
    exact hD
  have hDfr : DQ ⊆ frontier Q₁ := by
    rw [← hQ]
    exact IsPLBall.inter_subset_frontier_of_isPLBall (n := 2) h₂ hI (by norm_num)
  have hint : interior Q₁ ⊆ Q₁ \ DQ := fun x hx => ⟨interior_subset hx, fun hxD => (hDfr hxD).2 hx⟩
  have hcl : closure (interior Q₁) = Q₁ := IsPLBall.closure_interior (n := 2) h₁
  have hconn : IsConnected (interior Q₁) :=
    IsPLBall.isConnected_interior_of_finrank (n := 2) (by simp) h₁
  refine ⟨hconn.subset_closure hint ?_, ?_⟩
  · rw [hcl]
    exact sdiff_subset
  · calc Q₁ = closure (interior Q₁) := hcl.symm
      _ ⊆ closure (Q₁ \ DQ) := closure_mono hint

theorem image_stdSimplex_subset_closure_image_openSimplex {g : (Fin 4 → ℝ) → E3}
    (hgc : ContinuousOn g (Convexity.StdSimplex.coordinateSet ℝ (Fin 4))) :
    g '' Convexity.StdSimplex.coordinateSet ℝ (Fin 4) ⊆ closure (g '' openSimplex (stdVertices 2)) := by
  have hcl : closure (openSimplex (stdVertices 2)) ⊆ Convexity.StdSimplex.coordinateSet ℝ (Fin 4) :=
    closure_minimal openSimplex_stdVertices_subset_stdSimplex (Convexity.StdSimplex.isCompact_coordinateSet ℝ _).isClosed
  exact (image_mono (stdSimplex_subset_closure_openSimplex 2)).trans (hgc.mono hcl).image_closure

theorem exists_preconnected_local_interior {g : (Fin 4 → ℝ) → E3}
    (hgc : ContinuousOn g (Convexity.StdSimplex.coordinateSet ℝ (Fin 4))) (hgi : InjOn g (Convexity.StdSimplex.coordinateSet ℝ (Fin 4)))
    {y : E3} (hy : y ∈ g '' Convexity.StdSimplex.coordinateSet ℝ (Fin 4)) {O : Set E3} (hO : O ∈ 𝓝 y) :
    ∃ L : Set E3, L ⊆ O ∧ L ⊆ g '' openSimplex (stdVertices 2) ∧ IsPreconnected L ∧
      y ∈ closure L ∧ ∃ O' ∈ 𝓝 y, O' ∩ g '' openSimplex (stdVertices 2) ⊆ L := by
  obtain ⟨β, hβ, rfl⟩ := hy
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhdsWithin_iff.mp ((hgc β hβ).preimage_mem_nhdsWithin hO)
  obtain ⟨T, hT, hTeq⟩ := exists_isOpen_inter_image_eq_of_isCompact
    (Convexity.StdSimplex.isCompact_coordinateSet ℝ (Fin 4)) hgc hgi (Metric.isOpen_ball (x := β) (ε := r))
  have hsubΔ : Metric.ball β r ∩ openSimplex (stdVertices 2) ⊆ Convexity.StdSimplex.coordinateSet ℝ (Fin 4) :=
    inter_subset_right.trans openSimplex_stdVertices_subset_stdSimplex
  refine ⟨g '' (Metric.ball β r ∩ openSimplex (stdVertices 2)), ?_, image_mono inter_subset_right,
    ?_, ?_, T, hT.mem_nhds ?_, ?_⟩
  · rintro _ ⟨z, ⟨hzr, hzo⟩, rfl⟩
    exact hball ⟨hzr, openSimplex_stdVertices_subset_stdSimplex hzo⟩
  · exact ((convex_ball β r).inter (convex_openSimplex _)).isPreconnected.image g (hgc.mono hsubΔ)
  · have hβcl : β ∈ closure (Metric.ball β r ∩ openSimplex (stdVertices 2)) :=
      Metric.isOpen_ball.inter_closure
        ⟨Metric.mem_ball_self hr, stdSimplex_subset_closure_openSimplex 2 hβ⟩
    have hsub : closure (Metric.ball β r ∩ openSimplex (stdVertices 2)) ⊆
        Convexity.StdSimplex.coordinateSet ℝ (Fin 4) := closure_minimal hsubΔ (Convexity.StdSimplex.isCompact_coordinateSet ℝ _).isClosed
    exact (hgc.mono hsub).image_closure ⟨β, hβcl, rfl⟩
  · have hmem : g β ∈ g '' (Metric.ball β r ∩ Convexity.StdSimplex.coordinateSet ℝ (Fin 4)) :=
      ⟨β, ⟨Metric.mem_ball_self hr, hβ⟩, rfl⟩
    rw [← hTeq] at hmem
    exact hmem.1
  · rintro _ ⟨hyT, z, hzo, rfl⟩
    have hzΔ : z ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 4) := openSimplex_stdVertices_subset_stdSimplex hzo
    have hmem : g z ∈ T ∩ g '' Convexity.StdSimplex.coordinateSet ℝ (Fin 4) := ⟨hyT, z, hzΔ, rfl⟩
    rw [hTeq] at hmem
    obtain ⟨w, ⟨hwr, hwΔ⟩, hwz⟩ := hmem
    have hwz' : w = z := hgi hwΔ hzΔ hwz
    rw [hwz'] at hwr
    exact ⟨z, ⟨hwr, hzo⟩, rfl⟩

section TubeFrontier

variable {K : Geometry.SimplicialComplex ℝ E3} {N N' : Set E3} {C : E3 → Set E3}
  {D Dbd : Finset E3 → Set E3} {h : E3 → E3}

theorem IsTube.mem_frontier_of_mem_frontier_dualCell (ht : IsTube K N C D Dbd h N') {a : E3}
    (ha : a ∈ K.vertices) {x : E3} (hx : x ∈ frontier (C a))
    (hxD : ∀ f ∈ K.faces, f.card = 2 → a ∈ f → x ∉ D f) : x ∈ frontier N := by
  have hCcl : IsClosed (C a) := (ht.dualBall a ha).isPolyhedron.isClosed
  have hxC : x ∈ C a := hCcl.frontier_subset hx
  refine ⟨subset_closure (ht.dualCell_subset ha hxC), fun hxint => hx.2 ?_⟩
  have hfin : {w | w ∈ K.vertices ∧ w ≠ a}.Finite := ht.finite_vertices.subset fun w hw => hw.1
  have hFcl : IsClosed (⋃ w ∈ {w | w ∈ K.vertices ∧ w ≠ a}, C w) :=
    hfin.isClosed_biUnion fun w hw => (ht.dualBall w hw.1).isPolyhedron.isClosed
  have hxF : x ∉ ⋃ w ∈ {w | w ∈ K.vertices ∧ w ≠ a}, C w := by
    intro hxw
    obtain ⟨w, ⟨hw, hwa⟩, hxw⟩ := mem_iUnion₂.mp hxw
    by_cases hadj : ∃ f ∈ K.faces, a ∈ f ∧ w ∈ f
    · obtain ⟨f, hf, haf, hwf⟩ := hadj
      have hxf : x ∈ D f := by
        rw [← ht.inter_eq_of_mem_faces ha hw (Ne.symm hwa) hf haf hwf]
        exact ⟨hxC, hxw⟩
      exact hxD f hf (ht.card_eq_two_of_mem hf haf hwf (Ne.symm hwa)) haf hxf
    · have hmem : x ∈ C a ∩ C w := ⟨hxC, hxw⟩
      rw [ht.inter_eq_empty_of_forall_notMem_faces ha hw (Ne.symm hwa)
        fun f hf haf hwf => hadj ⟨f, hf, haf, hwf⟩] at hmem
      exact hmem
  refine mem_interior.mpr ⟨interior N \ ⋃ w ∈ {w | w ∈ K.vertices ∧ w ≠ a}, C w, ?_,
    isOpen_interior.sdiff hFcl, hxint, hxF⟩
  rintro y ⟨hyN, hyF⟩
  have hyN' := interior_subset hyN
  rw [ht.unionEq] at hyN'
  obtain ⟨w, hw, hyw⟩ := mem_iUnion₂.mp hyN'
  by_cases hwa : w = a
  · rw [hwa] at hyw
    exact hyw
  · exact absurd (mem_iUnion₂.mpr ⟨w, ⟨hw, hwa⟩, hyw⟩) hyF

theorem IsTube.frontier_inter_frontier_subset_closure_freeFace (ht : IsTube K N C D Dbd h N')
    {a : E3} (ha : a ∈ K.vertices) :
    frontier (C a) ∩ frontier N ⊆ closure ((frontier (C a) ∩ frontier N) \
      ⋃ f ∈ {f : Finset E3 | f ∈ K.faces ∧ f.card = 2 ∧ a ∈ f}, Dbd f) := by
  intro x hx
  by_cases hxb : x ∈ ⋃ f ∈ {f : Finset E3 | f ∈ K.faces ∧ f.card = 2 ∧ a ∈ f}, Dbd f
  · obtain ⟨f, ⟨hf, hfc, haf⟩, hxf⟩ := mem_iUnion₂.mp hxb
    have hS : IsPLSphere 2 (frontier (C a)) :=
      IsPLBall.isPLSphere_frontier (n := 2) (ht.dualBall a ha)
    obtain ⟨r, hr, hrb⟩ := ht.splitCell f hf hfc
    have hDS := ht.splitDisk_subset_frontier ha hf hfc haf
    have hcl := hS.closure_sdiff_eq_sdiff_image_stdSimplexBoundary hr hDS
    have hxcl : x ∈ closure (frontier (C a) \ D f) := by
      rw [hcl]
      refine ⟨hx.1, fun h' => h'.2 ?_⟩
      rw [← hrb]
      exact hxf
    have hfin : {g : Finset E3 | g ∈ K.faces ∧ g.card = 2 ∧ a ∈ g ∧ g ≠ f}.Finite :=
      ht.facesFinite.subset fun g hg => hg.1
    have hGcl : IsClosed
        (⋃ g ∈ {g : Finset E3 | g ∈ K.faces ∧ g.card = 2 ∧ a ∈ g ∧ g ≠ f}, D g) := by
      refine hfin.isClosed_biUnion fun g hg => ?_
      obtain ⟨q, hq, -⟩ := ht.splitCell g hg.1 hg.2.1
      exact (show IsPLBall 2 (D g) from ⟨q, hq⟩).isPolyhedron.isClosed
    have hxDf : x ∈ D f := by
      rw [← ht.splitProper f hf hfc] at hxf
      exact hxf.1
    have hxG : x ∉ ⋃ g ∈ {g : Finset E3 | g ∈ K.faces ∧ g.card = 2 ∧ a ∈ g ∧ g ≠ f}, D g := by
      intro hxg
      obtain ⟨g, ⟨hg, hgc, -, hgf⟩, hxg⟩ := mem_iUnion₂.mp hxg
      exact disjoint_left.mp (ht.splitDisjoint hf hfc hg hgc (Ne.symm hgf)) hxDf hxg
    have hmem := hGcl.isOpen_compl.inter_closure ⟨hxG, hxcl⟩
    refine closure_mono ?_ hmem
    rintro y ⟨hyG, hyS, hyDf⟩
    have hyD : ∀ g ∈ K.faces, g.card = 2 → a ∈ g → y ∉ D g := by
      intro g hg hgc hag hyg
      by_cases hgf : g = f
      · rw [hgf] at hyg
        exact hyDf hyg
      · exact hyG (mem_iUnion₂.mpr ⟨g, ⟨hg, hgc, hag, hgf⟩, hyg⟩)
    refine ⟨⟨hyS, ht.mem_frontier_of_mem_frontier_dualCell ha hyS hyD⟩, fun hyb => ?_⟩
    obtain ⟨g, ⟨hg, hgc, hag⟩, hyg⟩ := mem_iUnion₂.mp hyb
    have hygD : y ∈ D g := by
      rw [← ht.splitProper g hg hgc] at hyg
      exact hyg.1
    exact hyD g hg hgc hag hygD
  · exact subset_closure ⟨hx, hxb⟩

end TubeFrontier

section Leaves

variable {K : Geometry.SimplicialComplex ℝ E3} {N N' : Set E3} {C : E3 → Set E3}
  {D Dbd : Finset E3 → Set E3} {h : E3 → E3} {u v : E3} {W : Set E3} {P' : E3}
  {φ : E3 → E3} {Pt : ℤ → E3} {Dp Dpint J A S T S'' T'' H B Jlo Jhi : ℤ → Set E3}

open Classical in
theorem exists_twoComponents_of_pseudoCell (ht : IsTube K N C D Dbd h N') (hu : u ∈ K.vertices)
    (hv : v ∈ K.vertices) (huv : u ≠ v) (he : ({u, v} : Finset E3) ∈ K.faces)
    (hP' : P' = h (({u, v} : Finset E3).centroid ℝ id))
    (hWsub : W ⊆ h '' C u ∪ h '' C v)
    (hWfr : W ∩ frontier (h '' C u ∪ h '' C v) = h '' Dbd {u, v})
    {Ec Eint Ebd : Set E3} (hE : IsPseudoCell Ec Eint Ebd P') (hEbd : Ebd = h '' Dbd {u, v})
    (hEW : Ec ⊆ W)
    (hsep : Separates (((↑) : interior (h '' C u ∪ h '' C v) → E3) ⁻¹' Eint)
      (((↑) : interior (h '' C u ∪ h '' C v) → E3) ⁻¹' {h u})
      (((↑) : interior (h '' C u ∪ h '' C v) → E3) ⁻¹' {h v}))
    (hcell : ∀ x ∈ Eint \ {P'}, ∃ Q₁ Q₂ DQ : Set E3,
      IsPLBall 3 Q₁ ∧ IsPLBall 3 Q₂ ∧ Q₁ ∩ Q₂ = DQ ∧ IsPLBall 2 DQ ∧ DQ ⊆ Eint \ {P'} ∧
      Q₁ ∪ Q₂ ∈ 𝓝 x ∧ Q₁ ∪ Q₂ ⊆ interior (h '' C u ∪ h '' C v) ∧ (Q₁ ∪ Q₂) ∩ Ec = DQ)
    {Bu Bv : Set E3}
    (hBu : IsCompact Bu ∧ IsConnected Bu ∧ h u ∈ Bu ∧ Bu ⊆ h '' C u ∧ Disjoint Bu Ec ∧
      (Bu ∩ h '' ((frontier (C u) ∩ frontier N) \
        ⋃ f ∈ {f : Finset E3 | f ∈ K.faces ∧ f.card = 2 ∧ u ∈ f}, Dbd f)).Nonempty)
    (hBv : IsCompact Bv ∧ IsConnected Bv ∧ h v ∈ Bv ∧ Bv ⊆ h '' C v ∧ Disjoint Bv Ec ∧
      (Bv ∩ h '' ((frontier (C v) ∩ frontier N) \
        ⋃ f ∈ {f : Finset E3 | f ∈ K.faces ∧ f.card = 2 ∧ v ∈ f}, Dbd f)).Nonempty) :
    ∃ U₁ U₂ : Set E3, h u ∈ U₁ ∧ h v ∈ U₂ ∧ IsConnected U₁ ∧ IsConnected U₂ ∧
      Disjoint U₁ U₂ ∧ U₁ ∪ U₂ = (h '' C u ∪ h '' C v) \ Ec ∧
      (∀ V : Set E3, IsPreconnected V → V ⊆ (h '' C u ∪ h '' C v) \ Ec →
        V ⊆ U₁ ∨ V ⊆ U₂) ∧
      Ec ⊆ frontier U₁ ∧ Ec ⊆ frontier U₂ ∧
      h '' (frontier (C u) ∩ frontier N) ⊆ frontier U₁ ∧
      h '' (frontier (C v) ∩ frontier N) ⊆ frontier U₂ := by
  obtain ⟨-, hBuc, hBuu, hBuC, hBuE, hBuF⟩ := hBu
  obtain ⟨-, hBvc, hBvv, hBvC, hBvE, hBvF⟩ := hBv
  have hue : u ∈ ({u, v} : Finset E3) := Finset.mem_insert_self u {v}
  have hve : v ∈ ({u, v} : Finset E3) := Finset.mem_insert_of_mem (Finset.mem_singleton_self v)
  have hc : ({u, v} : Finset E3).card = 2 := ht.card_eq_two_of_mem he hue hve huv
  have hcont := ht.continuousOn
  have hinj := ht.injOn
  have hCuN := ht.dualCell_subset hu
  have hCvN := ht.dualCell_subset hv
  have hCuc : IsCompact (C u) := (ht.dualBall u hu).isPolyhedron.isCompact
  have hCvc : IsCompact (C v) := (ht.dualBall v hv).isPolyhedron.isCompact
  have hY₀c : IsCompact (C u ∪ C v) := hCuc.union hCvc
  have hY₀N : C u ∪ C v ⊆ N := union_subset hCuN hCvN
  have hYeq : h '' C u ∪ h '' C v = h '' (C u ∪ C v) := (image_union h (C u) (C v)).symm
  have hIeq : interior (h '' C u ∪ h '' C v) = h '' interior (C u ∪ C v) := by
    rw [hYeq]
    exact interior_image_eq_image_interior_of_isCompact hY₀c (hcont.mono hY₀N) (hinj.mono hY₀N)
  have hFeq : frontier (h '' C u ∪ h '' C v) = h '' frontier (C u ∪ C v) := by
    rw [hYeq]
    exact frontier_image_eq_image_frontier_of_isCompact hY₀c (hcont.mono hY₀N) (hinj.mono hY₀N)
  have hCucl : IsClosed (h '' C u) := (hCuc.image_of_continuousOn (hcont.mono hCuN)).isClosed
  have hCvcl : IsClosed (h '' C v) := (hCvc.image_of_continuousOn (hcont.mono hCvN)).isClosed
  have hDuv : C u ∩ C v = D {u, v} := ht.inter_eq_of_mem_faces hu hv huv he hue hve
  have hCuv : h '' C u ∩ h '' C v = h '' D {u, v} := by
    rw [← hinj.image_inter hCuN hCvN, hDuv]
  have hDN : D {u, v} ⊆ N := by
    rw [← hDuv]
    exact inter_subset_left.trans hCuN
  have hintD : h '' (D {u, v} \ Dbd {u, v}) ⊆ interior (h '' C u ∪ h '' C v) := by
    rw [hIeq]
    exact image_mono (ht.splitDisk_sdiff_subset_interior hu hv huv he hue hve)
  have hDfr : h '' D {u, v} ∩ frontier (h '' C u ∪ h '' C v) ⊆ Ebd := by
    rintro _ ⟨⟨x, hxD, rfl⟩, hxF⟩
    rw [hEbd]
    by_contra hxb
    have hxb' : x ∉ Dbd {u, v} := fun h' => hxb ⟨x, h', rfl⟩
    exact hxF.2 (hintD ⟨x, ⟨hxD, hxb'⟩, rfl⟩)
  have hEcl : IsClosed Ec := by
    rw [hE.carrierEq, ← hE.closureEq]
    exact isClosed_closure
  have hEbdF : Ebd ⊆ frontier (h '' C u ∪ h '' C v) := by
    rw [hEbd, ← hWfr]
    exact inter_subset_right
  have hEcF : Ec ∩ frontier (h '' C u ∪ h '' C v) ⊆ Ebd := by
    rintro x ⟨hxE, hxF⟩
    rw [hEbd, ← hWfr]
    exact ⟨hEW hxE, hxF⟩
  have hEintEc : Eint ⊆ Ec := by
    rw [hE.carrierEq]
    exact subset_union_left
  have hEbdEc : Ebd ⊆ Ec := by
    rw [hE.carrierEq]
    exact subset_union_right
  have hEintI : Eint ⊆ interior (h '' C u ∪ h '' C v) := by
    intro x hx
    have hxE : x ∈ Ec := hEintEc hx
    by_contra hxI
    have hxF : x ∈ frontier (h '' C u ∪ h '' C v) :=
      ⟨subset_closure (hWsub (hEW hxE)), hxI⟩
    exact disjoint_left.mp hE.disjointRim hx (hEcF ⟨hxE, hxF⟩)
  have hEcI : Ec ∩ interior (h '' C u ∪ h '' C v) ⊆ Eint := by
    rintro x ⟨hxE, hxI⟩
    rw [hE.carrierEq] at hxE
    rcases hxE with h1 | h1
    · exact h1
    · exact absurd hxI (hEbdF h1).2
  have hNfr : ∀ x ∈ C u ∪ C v, x ∈ frontier N → h x ∉ interior (h '' C u ∪ h '' C v) := by
    intro x hxY hxN hxI
    rw [hIeq] at hxI
    obtain ⟨x', hx', hxx'⟩ := hxI
    have hxx : x' = x := hinj (hY₀N (interior_subset hx')) (hY₀N hxY) hxx'
    rw [hxx] at hx'
    exact hxN.2 (interior_mono hY₀N hx')
  obtain ⟨gu, hguc, hgui, hguim, -, hguint⟩ := ht.exists_dualCell_model hu
  obtain ⟨gv, hgvc, hgvi, hgvim, -, hgvint⟩ := ht.exists_dualCell_model hv
  have huint : h u ∈ interior (h '' C u) := by
    rw [interior_image_eq_image_interior_of_isCompact hCuc (hcont.mono hCuN) (hinj.mono hCuN)]
    exact ⟨u, ht.mem_interior_dualCell hu, rfl⟩
  have hvint : h v ∈ interior (h '' C v) := by
    rw [interior_image_eq_image_interior_of_isCompact hCvc (hcont.mono hCvN) (hinj.mono hCvN)]
    exact ⟨v, ht.mem_interior_dualCell hv, rfl⟩
  have huI : h u ∈ interior (h '' C u ∪ h '' C v) := interior_mono subset_union_left huint
  have hvI : h v ∈ interior (h '' C u ∪ h '' C v) := interior_mono subset_union_right hvint
  have huE : h u ∉ Ec := disjoint_left.mp hBuE hBuu
  have hvE : h v ∉ Ec := disjoint_left.mp hBvE hBvv
  have hmid : ({u, v} : Finset E3).centroid ℝ id ∈ D {u, v} := by
    have hm : ({u, v} : Finset E3).centroid ℝ id ∈ D {u, v} ∩ K.space := by
      rw [ht.splitMidpoint he hc]
      exact mem_singleton _
    exact hm.1
  have hP'D : P' ∈ h '' D {u, v} := ⟨_, hmid, hP'.symm⟩
  have hDfrU : h '' D {u, v} ⊆ frontier (h '' C u) := by
    rw [frontier_image_eq_image_frontier_of_isCompact hCuc (hcont.mono hCuN) (hinj.mono hCuN)]
    exact image_mono (ht.splitDisk_subset_frontier hu he hc hue)
  have hDfrV : h '' D {u, v} ⊆ frontier (h '' C v) := by
    rw [frontier_image_eq_image_frontier_of_isCompact hCvc (hcont.mono hCvN) (hinj.mono hCvN)]
    exact image_mono (ht.splitDisk_subset_frontier hv he hc hve)
  have hPE : P' ∈ Eint := hE.centerMem
  obtain ⟨hSgc, hSgd⟩ := hE.isOpenCell.isConnected_sdiff_singleton hPE
  obtain ⟨z₀, hz₀D, hz₀P⟩ : ∃ z₀ ∈ h '' (D {u, v} \ Dbd {u, v}), z₀ ≠ P' := by
    obtain ⟨r, hr, hrb⟩ := ht.splitCell _ he hc
    have hopen1 : r '' openSimplex (stdVertices 1) = D {u, v} \ Dbd {u, v} := by
      rw [hrb]
      exact IsPLHomeomorphOn.image_openSimplex_stdVertices (n := 1) hr
    obtain ⟨c₂, hc₂def⟩ : ∃ c₂ : Fin 3 → ℝ, c₂ = fun i => if i = 0 then 1 / 2 else 1 / 4 :=
      ⟨_, rfl⟩
    have hpos : ∀ i, 0 < c₂ i := by
      intro i
      rw [hc₂def]
      dsimp only
      split_ifs <;> norm_num
    have hsum : ∑ i : Fin 3, c₂ i = 1 := by
      rw [hc₂def, Fin.sum_univ_three]
      norm_num [show ¬((2 : Fin 3) = 0) by decide]
    have hc₁m : stdCenter 1 ∈ openSimplex (stdVertices 1) := stdCenter_mem_openSimplex 1
    have hc₂m : c₂ ∈ openSimplex (stdVertices 1) :=
      (mem_openSimplex_stdVertices_iff 1).mpr ⟨hpos, hsum⟩
    have hne : stdCenter 1 ≠ c₂ := by
      intro h'
      have h0 := congrFun h' 0
      rw [hc₂def] at h0
      norm_num [stdCenter] at h0
    have hmaps : MapsTo r (openSimplex (stdVertices 1)) (D {u, v}) :=
      hr.bijOn.mapsTo.mono_left openSimplex_stdVertices_subset_stdSimplex
    have hrinj : InjOn (h ∘ r) (openSimplex (stdVertices 1)) :=
      (hinj.mono hDN).comp (hr.bijOn.injOn.mono openSimplex_stdVertices_subset_stdSimplex) hmaps
    have hmem : ∀ c ∈ openSimplex (stdVertices 1), h (r c) ∈ h '' (D {u, v} \ Dbd {u, v}) := by
      intro c hcm
      rw [← hopen1]
      exact ⟨r c, ⟨c, hcm, rfl⟩, rfl⟩
    by_cases h1 : h (r (stdCenter 1)) = P'
    · exact ⟨h (r c₂), hmem c₂ hc₂m, fun h2 => hne (hrinj hc₁m hc₂m (h1.trans h2.symm))⟩
    · exact ⟨h (r (stdCenter 1)), hmem _ hc₁m, h1⟩
  set Y := h '' C u ∪ h '' C v with hYdef
  set I := interior Y with hIdef
  have hTu : IsConnected (interior (h '' C u)) := by
    rw [← hguint]
    exact ((convex_openSimplex _).isConnected ⟨_, stdCenter_mem_openSimplex 2⟩).image gu
      (hguc.mono openSimplex_stdVertices_subset_stdSimplex)
  have hTv : IsConnected (interior (h '' C v)) := by
    rw [← hgvint]
    exact ((convex_openSimplex _).isConnected ⟨_, stdCenter_mem_openSimplex 2⟩).image gv
      (hgvc.mono openSimplex_stdVertices_subset_stdSimplex)
  have hclu : h '' C u ⊆ closure (interior (h '' C u)) := by
    rw [← hguint, ← hguim]
    exact image_stdSimplex_subset_closure_image_openSimplex hguc
  have hclv : h '' C v ⊆ closure (interior (h '' C v)) := by
    rw [← hgvint, ← hgvim]
    exact image_stdSimplex_subset_closure_image_openSimplex hgvc
  have hz₀uv : z₀ ∈ h '' C u ∩ h '' C v := by
    rw [hCuv]
    obtain ⟨x, hx, rfl⟩ := hz₀D
    exact ⟨x, hx.1, rfl⟩
  have hIP : IsConnected (I \ {P'}) := by
    have hA : IsConnected (interior (h '' C u) ∪ {z₀}) :=
      hTu.subset_closure subset_union_left
        (union_subset subset_closure (singleton_subset_iff.mpr (hclu hz₀uv.1)))
    have hB : IsConnected (interior (h '' C v) ∪ {z₀}) :=
      hTv.subset_closure subset_union_left
        (union_subset subset_closure (singleton_subset_iff.mpr (hclv hz₀uv.2)))
    have hAB := hA.union ⟨z₀, Or.inr (mem_singleton _), Or.inr (mem_singleton _)⟩ hB
    refine hAB.subset_closure ?_ ?_
    · rintro y ((hy | hy) | (hy | hy))
      · refine ⟨interior_mono subset_union_left hy, fun hyP => ?_⟩
        rw [mem_singleton_iff] at hyP
        rw [hyP] at hy
        exact (hDfrU hP'D).2 hy
      · rw [mem_singleton_iff] at hy
        rw [hy]
        exact ⟨hintD hz₀D, hz₀P⟩
      · refine ⟨interior_mono subset_union_right hy, fun hyP => ?_⟩
        rw [mem_singleton_iff] at hyP
        rw [hyP] at hy
        exact (hDfrV hP'D).2 hy
      · rw [mem_singleton_iff] at hy
        rw [hy]
        exact ⟨hintD hz₀D, hz₀P⟩
    · rintro y ⟨hyI, -⟩
      rcases interior_subset hyI with hyu | hyv
      · exact closure_mono (subset_union_left.trans subset_union_left) (hclu hyu)
      · exact closure_mono (subset_union_left.trans subset_union_right) (hclv hyv)
  obtain ⟨O, hOdef⟩ : ∃ O : Set E3, O = I \ Ec := ⟨_, rfl⟩
  have hOopen : IsOpen O := by
    rw [hOdef]
    exact isOpen_interior.sdiff hEcl
  have hOmem : ∀ z, z ∈ O ↔ z ∈ I ∧ z ∉ Ec := by
    intro z
    rw [hOdef]
    exact Iff.rfl
  have huO : h u ∈ O := (hOmem _).mpr ⟨huI, huE⟩
  have hvO : h v ∈ O := (hOmem _).mpr ⟨hvI, hvE⟩
  have hOZ : O ⊆ Y \ Ec := fun z hz => ⟨interior_subset ((hOmem z).mp hz).1, ((hOmem z).mp hz).2⟩
  have hΓopen : ∀ z, IsOpen (connectedComponentIn O z) := fun z => hOopen.connectedComponentIn
  have hΓeq : ∀ z z' w, w ∈ connectedComponentIn O z → w ∈ connectedComponentIn O z' →
      connectedComponentIn O z = connectedComponentIn O z' := fun z z' w hwz hwz' =>
    (connectedComponentIn_eq hwz).trans (connectedComponentIn_eq hwz').symm
  have hLsub : ∀ z (L : Set E3), IsPreconnected L → L ⊆ O → ∀ y ∈ L,
      y ∈ connectedComponentIn O z → L ⊆ connectedComponentIn O z := by
    intro z L hL hLO y hyL hyz
    rw [connectedComponentIn_eq hyz]
    exact hL.subset_connectedComponentIn hyL hLO
  have hsepΓ : h v ∉ connectedComponentIn O (h u) := by
    intro hvΓ
    obtain ⟨U', V', hU', hV', hd', heq', hu', hv'⟩ := hsep
    have hΓI : connectedComponentIn O (h u) ⊆ I := fun y hy =>
      ((hOmem y).mp (connectedComponentIn_subset _ _ hy)).1
    have hpre : IsPreconnected (((↑) : I → E3) ⁻¹' connectedComponentIn O (h u)) := by
      refine IsInducing.subtypeVal.isPreconnected_image.mp ?_
      rw [Subtype.image_preimage_coe, inter_eq_right.mpr hΓI]
      exact isPreconnected_connectedComponentIn
    have hsub : ((↑) : I → E3) ⁻¹' connectedComponentIn O (h u) ⊆ U' ∪ V' := by
      rw [heq']
      intro y hy hyE
      exact ((hOmem _).mp (connectedComponentIn_subset _ _ hy)).2 (hEintEc hyE)
    have hsubU := hpre.subset_left_of_subset_union hU' hV' hd' hsub
      ⟨⟨h u, huI⟩, mem_connectedComponentIn huO,
        hu' (show (⟨h u, huI⟩ : I) ∈ ((↑) : I → E3) ⁻¹' {h u} from rfl)⟩
    exact disjoint_left.mp hd'
      (hsubU (show (⟨h v, hvI⟩ : I) ∈ ((↑) : I → E3) ⁻¹' connectedComponentIn O (h u) from hvΓ))
      (hv' (show (⟨h v, hvI⟩ : I) ∈ ((↑) : I → E3) ⁻¹' {h v} from rfl))
  have hΓne : connectedComponentIn O (h u) ≠ connectedComponentIn O (h v) := by
    intro heq
    apply hsepΓ
    rw [heq]
    exact mem_connectedComponentIn hvO
  have hside_cell : ∀ x ∈ Eint \ {P'}, ∃ L₁ L₂ N₀ : Set E3, N₀ ∈ 𝓝 x ∧ IsConnected L₁ ∧
      IsConnected L₂ ∧ L₁ ⊆ O ∧ L₂ ⊆ O ∧ N₀ \ Ec ⊆ L₁ ∪ L₂ ∧ N₀ ∩ Ec ⊆ closure L₁ ∧
      N₀ ∩ Ec ⊆ closure L₂ := by
    intro x hx
    obtain ⟨Q₁, Q₂, DQ, hQ₁, hQ₂, hQ, hDQ, -, hN, hQI, hQE⟩ := hcell x hx
    obtain ⟨hc₁, hcl₁⟩ := isConnected_sdiff_of_isPLBall_inter hQ₁ hQ₂ hQ hDQ
    obtain ⟨hc₂, hcl₂⟩ := isConnected_sdiff_of_isPLBall_inter hQ₂ hQ₁
      (by rw [inter_comm]; exact hQ) hDQ
    have hDQE : DQ ⊆ Ec := by
      rw [← hQE]
      exact inter_subset_right
    have hLO : ∀ Q, Q ⊆ Q₁ ∪ Q₂ → Q \ DQ ⊆ O := by
      intro Q hQsub y ⟨hyQ, hyD⟩
      refine (hOmem y).mpr ⟨hQI (hQsub hyQ), fun hyE => hyD ?_⟩
      rw [← hQE]
      exact ⟨hQsub hyQ, hyE⟩
    refine ⟨Q₁ \ DQ, Q₂ \ DQ, Q₁ ∪ Q₂, hN, hc₁, hc₂, hLO Q₁ subset_union_left,
      hLO Q₂ subset_union_right, ?_, ?_, ?_⟩
    · rintro y ⟨hyQ | hyQ, hyE⟩
      · exact Or.inl ⟨hyQ, fun hyD => hyE (hDQE hyD)⟩
      · exact Or.inr ⟨hyQ, fun hyD => hyE (hDQE hyD)⟩
    · rw [hQE]
      intro y hy
      rw [← hQ] at hy
      exact hcl₁ hy.1
    · rw [hQE]
      intro y hy
      rw [← hQ] at hy
      exact hcl₂ hy.2
  have hcontains : ∀ z ∈ O, ∀ x ∈ Eint \ {P'}, x ∈ closure (connectedComponentIn O z) →
      ∀ L₁ L₂ N₀ : Set E3, N₀ ∈ 𝓝 x → IsConnected L₁ → IsConnected L₂ → L₁ ⊆ O → L₂ ⊆ O →
      N₀ \ Ec ⊆ L₁ ∪ L₂ →
      L₁ ⊆ connectedComponentIn O z ∨ L₂ ⊆ connectedComponentIn O z := by
    intro z _ x _ hxcl L₁ L₂ N₀ hN₀ hL₁ hL₂ hL₁O hL₂O hNL
    obtain ⟨y, hyN, hyΓ⟩ := mem_closure_iff_nhds.mp hxcl N₀ hN₀
    have hyO : y ∈ O := connectedComponentIn_subset _ _ hyΓ
    rcases hNL ⟨hyN, ((hOmem y).mp hyO).2⟩ with hy1 | hy1
    · exact Or.inl (hLsub z L₁ hL₁.isPreconnected hL₁O y hy1 hyΓ)
    · exact Or.inr (hLsub z L₂ hL₂.isPreconnected hL₂O y hy1 hyΓ)
  have hall : ∀ z ∈ O, (∃ x ∈ Eint \ {P'}, x ∈ closure (connectedComponentIn O z)) →
      Eint \ {P'} ⊆ closure (connectedComponentIn O z) := by
    intro z hzO ⟨x₁, hx₁Sg, hx₁cl⟩
    have hSgU : ∀ x ∈ Eint \ {P'}, x ∈ closure (connectedComponentIn O z) →
        x ∈ interior (closure (connectedComponentIn O z) ∪ (Eint \ {P'})ᶜ) := by
      intro x hxSg hxcl
      obtain ⟨L₁, L₂, N₀, hN₀, hL₁, hL₂, hL₁O, hL₂O, hNL, hNcl₁, hNcl₂⟩ := hside_cell x hxSg
      have key : ∀ L : Set E3, L ⊆ connectedComponentIn O z → N₀ ∩ Ec ⊆ closure L →
          x ∈ interior (closure (connectedComponentIn O z) ∪ (Eint \ {P'})ᶜ) := by
        intro L hLΓ hNcl
        refine mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset hN₀ fun y hyN => ?_)
        by_cases hySg : y ∈ Eint \ {P'}
        · exact Or.inl (closure_mono hLΓ (hNcl ⟨hyN, hEintEc hySg.1⟩))
        · exact Or.inr hySg
      rcases hcontains z hzO x hxSg hxcl L₁ L₂ N₀ hN₀ hL₁ hL₂ hL₁O hL₂O hNL with h1 | h1
      · exact key L₁ h1 hNcl₁
      · exact key L₂ h1 hNcl₂
    have hcov : Eint \ {P'} ⊆ interior (closure (connectedComponentIn O z) ∪ (Eint \ {P'})ᶜ) ∪
        (closure (connectedComponentIn O z))ᶜ := by
      intro x hxSg
      by_cases hxcl : x ∈ closure (connectedComponentIn O z)
      · exact Or.inl (hSgU x hxSg hxcl)
      · exact Or.inr hxcl
    have hdis : (Eint \ {P'}) ∩ (interior (closure (connectedComponentIn O z) ∪ (Eint \ {P'})ᶜ) ∩
        (closure (connectedComponentIn O z))ᶜ) = ∅ := by
      refine eq_empty_iff_forall_notMem.mpr fun x ⟨hxSg, hxU, hxV⟩ => ?_
      rcases interior_subset hxU with h1 | h1
      · exact hxV h1
      · exact h1 hxSg
    rcases (isPreconnected_iff_subset_of_disjoint.mp hSgc.isPreconnected) _ _ isOpen_interior
      isClosed_closure.isOpen_compl hcov hdis with h1 | h1
    · intro x hx
      rcases interior_subset (h1 hx) with h2 | h2
      · exact h2
      · exact absurd hx h2
    · exact absurd hx₁cl (h1 hx₁Sg)
  have hmeet : ∀ z ∈ O, ∃ x ∈ Eint \ {P'}, x ∈ closure (connectedComponentIn O z) := by
    intro z hzO
    by_contra hno
    push Not at hno
    obtain ⟨x₀, hx₀⟩ := hSgc.nonempty
    have hcov : I \ {P'} ⊆ connectedComponentIn O z ∪ (closure (connectedComponentIn O z))ᶜ := by
      rintro y ⟨hyI, hyP⟩
      by_cases hycl : y ∈ closure (connectedComponentIn O z)
      · left
        by_cases hyE : y ∈ Ec
        · exact absurd hycl (hno y ⟨hEcI ⟨hyE, hyI⟩, hyP⟩)
        · have hyO : y ∈ O := (hOmem y).mpr ⟨hyI, hyE⟩
          obtain ⟨w, hwy, hwz⟩ := mem_closure_iff_nhds.mp hycl _
            ((hΓopen y).mem_nhds (mem_connectedComponentIn hyO))
          rw [← hΓeq y z w hwy hwz]
          exact mem_connectedComponentIn hyO
      · exact Or.inr hycl
    have hzP : z ≠ P' := by
      intro hzP
      rw [hzP] at hzO
      exact ((hOmem P').mp hzO).2 (hEintEc hPE)
    obtain ⟨y, -, hy1, hy2⟩ := hIP.isPreconnected _ _ (hΓopen z) isClosed_closure.isOpen_compl
      hcov ⟨z, ⟨((hOmem z).mp hzO).1, hzP⟩, mem_connectedComponentIn hzO⟩
      ⟨x₀, ⟨hEintI hx₀.1, hx₀.2⟩, hno x₀ hx₀⟩
    exact hy2 (subset_closure hy1)
  obtain ⟨x₀, hx₀⟩ := hSgc.nonempty
  obtain ⟨L₁, L₂, N₀, hN₀, hL₁, hL₂, hL₁O, hL₂O, hNL, -, -⟩ := hside_cell x₀ hx₀
  have hcont2 : ∀ z ∈ O, L₁ ⊆ connectedComponentIn O z ∨ L₂ ⊆ connectedComponentIn O z :=
    fun z hzO => hcontains z hzO x₀ hx₀ (hall z hzO (hmeet z hzO) hx₀) L₁ L₂ N₀ hN₀ hL₁ hL₂
      hL₁O hL₂O hNL
  have hcomp2 : ∀ z ∈ O, connectedComponentIn O z = connectedComponentIn O (h u) ∨
      connectedComponentIn O z = connectedComponentIn O (h v) := by
    intro z hzO
    obtain ⟨y₁, hy₁⟩ := hL₁.nonempty
    obtain ⟨y₂, hy₂⟩ := hL₂.nonempty
    rcases hcont2 z hzO with hz1 | hz1 <;> rcases hcont2 (h u) huO with hu1 | hu1
    · exact Or.inl (hΓeq _ _ y₁ (hz1 hy₁) (hu1 hy₁))
    · rcases hcont2 (h v) hvO with hv1 | hv1
      · exact Or.inr (hΓeq _ _ y₁ (hz1 hy₁) (hv1 hy₁))
      · exact absurd (hΓeq _ _ y₂ (hu1 hy₂) (hv1 hy₂)) hΓne
    · rcases hcont2 (h v) hvO with hv1 | hv1
      · exact absurd (hΓeq _ _ y₁ (hu1 hy₁) (hv1 hy₁)) hΓne
      · exact Or.inr (hΓeq _ _ y₂ (hz1 hy₂) (hv1 hy₂))
    · exact Or.inl (hΓeq _ _ y₂ (hz1 hy₂) (hu1 hy₂))
  have hbdry : ∀ z ∈ Y \ Ec, z ∉ I → ∃ L : Set E3, L ⊆ O ∧ IsPreconnected L ∧ L.Nonempty ∧
      z ∈ closure L ∧ ∃ O' ∈ 𝓝 z, O' ∩ I ⊆ L := by
    rintro z ⟨hzY, hzE⟩ hzI
    have hzF : z ∈ frontier Y := ⟨subset_closure hzY, hzI⟩
    have hzD : z ∉ h '' D {u, v} := fun hzD => hzE (hEbdEc (hDfr ⟨hzD, hzF⟩))
    have key : ∀ (a b : E3) (g : (Fin 4 → ℝ) → E3), ContinuousOn g (Convexity.StdSimplex.coordinateSet ℝ (Fin 4)) →
        InjOn g (Convexity.StdSimplex.coordinateSet ℝ (Fin 4)) → g '' Convexity.StdSimplex.coordinateSet ℝ (Fin 4) = h '' C a →
        g '' openSimplex (stdVertices 2) = interior (h '' C a) → IsClosed (h '' C b) →
        (Y ⊆ h '' C a ∪ h '' C b) → interior (h '' C a) ⊆ I → z ∈ h '' C a → z ∉ h '' C b →
        ∃ L : Set E3, L ⊆ O ∧ IsPreconnected L ∧ L.Nonempty ∧ z ∈ closure L ∧
          ∃ O' ∈ 𝓝 z, O' ∩ I ⊆ L := by
      intro a b g hgc hgi hgim hgint hbcl hYab haI hza hzb
      have hzg : z ∈ g '' Convexity.StdSimplex.coordinateSet ℝ (Fin 4) := by
        rw [hgim]
        exact hza
      obtain ⟨L, hLO, hLint, hLpc, hzL, O', hO', hO'L⟩ := exists_preconnected_local_interior hgc
        hgi hzg (Filter.inter_mem (hEcl.isOpen_compl.mem_nhds hzE)
          (hbcl.isOpen_compl.mem_nhds hzb))
      rw [hgint] at hLint hO'L
      refine ⟨L, fun y hy => (hOmem y).mpr ⟨haI (hLint hy), (hLO hy).1⟩, hLpc,
        closure_nonempty_iff.mp ⟨z, hzL⟩, hzL, O' ∩ (h '' C b)ᶜ,
        Filter.inter_mem hO' (hbcl.isOpen_compl.mem_nhds hzb), ?_⟩
      rintro y ⟨⟨hyO', hyb⟩, hyI⟩
      refine hO'L ⟨hyO', ?_⟩
      have hopen : IsOpen (I ∩ (h '' C b)ᶜ) := isOpen_interior.inter hbcl.isOpen_compl
      have hsub : I ∩ (h '' C b)ᶜ ⊆ h '' C a := by
        rintro w ⟨hwI, hwb⟩
        rcases hYab (interior_subset hwI) with h1 | h1
        · exact h1
        · exact absurd h1 hwb
      exact interior_maximal hsub hopen ⟨hyI, hyb⟩
    rcases hzY with hzu | hzv
    · have hzv : z ∉ h '' C v := by
        intro hzv
        apply hzD
        rw [← hCuv]
        exact ⟨hzu, hzv⟩
      exact key u v gu hguc hgui hguim hguint hCvcl subset_rfl (interior_mono subset_union_left)
        hzu hzv
    · have hzu : z ∉ h '' C u := by
        intro hzu
        apply hzD
        rw [← hCuv]
        exact ⟨hzu, hzv⟩
      exact key v u gv hgvc hgvi hgvim hgvint hCucl (union_comm _ _).subset
        (interior_mono subset_union_right) hzv hzu
  have hΓsub : ∀ z ∈ O, connectedComponentIn O z ⊆ Y \ Ec := fun z _ =>
    (connectedComponentIn_subset _ _).trans hOZ
  have hdisj : Disjoint ((Y \ Ec) ∩ closure (connectedComponentIn O (h u)))
      ((Y \ Ec) ∩ closure (connectedComponentIn O (h v))) := by
    rw [disjoint_left]
    rintro z ⟨hzZ, hzu⟩ ⟨-, hzv⟩
    by_cases hzI : z ∈ I
    · have hzO : z ∈ O := (hOmem z).mpr ⟨hzI, hzZ.2⟩
      obtain ⟨w₁, hw₁z, hw₁u⟩ := mem_closure_iff_nhds.mp hzu _
        ((hΓopen z).mem_nhds (mem_connectedComponentIn hzO))
      obtain ⟨w₂, hw₂z, hw₂v⟩ := mem_closure_iff_nhds.mp hzv _
        ((hΓopen z).mem_nhds (mem_connectedComponentIn hzO))
      exact hΓne ((hΓeq _ _ w₁ hw₁z hw₁u).symm.trans (hΓeq _ _ w₂ hw₂z hw₂v))
    · obtain ⟨L, hLO, hLpc, ⟨y, hyL⟩, -, O', hO', hO'L⟩ := hbdry z hzZ hzI
      have hLΓ : ∀ w, w ∈ O → z ∈ closure (connectedComponentIn O w) →
          L ⊆ connectedComponentIn O w := by
        intro w _ hzw
        obtain ⟨y', hy'O', hy'Γ⟩ := mem_closure_iff_nhds.mp hzw O' hO'
        have hy'I : y' ∈ I := ((hOmem y').mp (connectedComponentIn_subset _ _ hy'Γ)).1
        exact hLsub w L hLpc hLO y' (hO'L ⟨hy'O', hy'I⟩) hy'Γ
      exact hΓne (hΓeq _ _ y (hLΓ (h u) huO hzu hyL) (hLΓ (h v) hvO hzv hyL))
  have hcover : (Y \ Ec) ∩ closure (connectedComponentIn O (h u)) ∪
      (Y \ Ec) ∩ closure (connectedComponentIn O (h v)) = Y \ Ec := by
    apply Subset.antisymm (union_subset inter_subset_left inter_subset_left)
    intro z hzZ
    have key : ∀ y ∈ O, z ∈ closure (connectedComponentIn O y) →
        z ∈ (Y \ Ec) ∩ closure (connectedComponentIn O (h u)) ∪
          (Y \ Ec) ∩ closure (connectedComponentIn O (h v)) := by
      intro y hyO hzy
      rcases hcomp2 y hyO with h1 | h1
      · rw [h1] at hzy
        exact Or.inl ⟨hzZ, hzy⟩
      · rw [h1] at hzy
        exact Or.inr ⟨hzZ, hzy⟩
    by_cases hzI : z ∈ I
    · have hzO : z ∈ O := (hOmem z).mpr ⟨hzI, hzZ.2⟩
      exact key z hzO (subset_closure (mem_connectedComponentIn hzO))
    · obtain ⟨L, hLO, hLpc, ⟨y, hyL⟩, hzL, -⟩ := hbdry z hzZ hzI
      exact key y (hLO hyL) (closure_mono (hLpc.subset_connectedComponentIn hyL hLO) hzL)
  have hpre : ∀ V : Set E3, IsPreconnected V → V ⊆ Y \ Ec →
      V ⊆ (Y \ Ec) ∩ closure (connectedComponentIn O (h u)) ∨
        V ⊆ (Y \ Ec) ∩ closure (connectedComponentIn O (h v)) := by
    intro V hV hVZ
    have hVcov : V ⊆ closure (connectedComponentIn O (h u)) ∪
        closure (connectedComponentIn O (h v)) := by
      intro y hy
      have hy' : y ∈ (Y \ Ec) ∩ closure (connectedComponentIn O (h u)) ∪
          (Y \ Ec) ∩ closure (connectedComponentIn O (h v)) := by
        rw [hcover]
        exact hVZ hy
      rcases hy' with h1 | h1
      · exact Or.inl h1.2
      · exact Or.inr h1.2
    have hVdis : V ∩ (closure (connectedComponentIn O (h u)) ∩
        closure (connectedComponentIn O (h v))) = ∅ := by
      refine eq_empty_iff_forall_notMem.mpr fun y ⟨hyV, hyu, hyv⟩ => ?_
      exact disjoint_left.mp hdisj ⟨hVZ hyV, hyu⟩ ⟨hVZ hyV, hyv⟩
    rcases (isPreconnected_iff_subset_of_disjoint_closed.mp hV) _ _ isClosed_closure
      isClosed_closure hVcov hVdis with h1 | h1
    · exact Or.inl (subset_inter hVZ h1)
    · exact Or.inr (subset_inter hVZ h1)
  have hESg : Ec ⊆ closure (Eint \ {P'}) := by
    rw [hE.carrierEq, ← hE.closureEq]
    exact closure_minimal hSgd isClosed_closure
  have hEfr : ∀ w ∈ O, Ec ⊆ frontier ((Y \ Ec) ∩ closure (connectedComponentIn O w)) := by
    intro w hwO x hx
    refine ⟨?_, fun hxint => (interior_subset hxint).1.2 hx⟩
    have hsub : connectedComponentIn O w ⊆ (Y \ Ec) ∩ closure (connectedComponentIn O w) :=
      subset_inter (hΓsub w hwO) subset_closure
    exact closure_mono hsub (closure_minimal (hall w hwO (hmeet w hwO)) isClosed_closure (hESg hx))
  have hfree : ∀ a ∈ K.vertices, a ∈ ({u, v} : Finset E3) → ∀ U Ba : Set E3,
      U ⊆ Y \ Ec → (∀ V : Set E3, IsPreconnected V → V ⊆ Y \ Ec → (V ∩ U).Nonempty → V ⊆ U) →
      IsConnected Ba → Ba ⊆ h '' C a → Disjoint Ba Ec → (Ba ∩ U).Nonempty →
      (Ba ∩ h '' ((frontier (C a) ∩ frontier N) \
        ⋃ f ∈ {f : Finset E3 | f ∈ K.faces ∧ f.card = 2 ∧ a ∈ f}, Dbd f)).Nonempty →
      h '' (frontier (C a) ∩ frontier N) ⊆ frontier U := by
    intro a ha hae U Ba hUZ habs hBac hBaC hBaE hBaU hBaF
    have hCaN := ht.dualCell_subset ha
    have hCacl : IsClosed (C a) := (ht.dualBall a ha).isPolyhedron.isClosed
    have hCaY : h '' C a ⊆ Y := by
      rcases eq_or_eq_of_mem_of_card_eq_two hc hue hve huv hae with h1 | h1
      · rw [h1]
        exact subset_union_left
      · rw [h1]
        exact subset_union_right
    have hBaZ : Ba ⊆ Y \ Ec := fun y hy => ⟨hCaY (hBaC hy), disjoint_left.mp hBaE hy⟩
    have hBaU' : Ba ⊆ U := habs Ba hBac.isPreconnected hBaZ hBaU
    have hFsub : (frontier (C a) ∩ frontier N) \
        ⋃ f ∈ {f : Finset E3 | f ∈ K.faces ∧ f.card = 2 ∧ a ∈ f}, Dbd f ⊆ C a :=
      fun x hx => hCacl.frontier_subset hx.1.1
    have hFZ : h '' ((frontier (C a) ∩ frontier N) \
        ⋃ f ∈ {f : Finset E3 | f ∈ K.faces ∧ f.card = 2 ∧ a ∈ f}, Dbd f) ⊆ Y \ Ec := by
      rintro _ ⟨x, hx, rfl⟩
      refine ⟨hCaY ⟨x, hFsub hx, rfl⟩, fun hxE => ?_⟩
      have hxY₀ : x ∈ C u ∪ C v := by
        rcases eq_or_eq_of_mem_of_card_eq_two hc hue hve huv hae with h1 | h1
        · rw [← h1]
          exact Or.inl (hFsub hx)
        · rw [← h1]
          exact Or.inr (hFsub hx)
      have hxF : h x ∈ frontier Y := by
        rw [hFeq]
        refine ⟨x, ⟨subset_closure hxY₀, fun hxint => hx.1.2.2 (interior_mono hY₀N hxint)⟩, rfl⟩
      have hxb := hEcF ⟨hxE, hxF⟩
      rw [hEbd] at hxb
      obtain ⟨x', hx', hxx'⟩ := hxb
      have hx'D : x' ∈ D {u, v} := by
        rw [← ht.splitProper _ he hc] at hx'
        exact hx'.1
      have hxx : x' = x := hinj (hDN hx'D) (hCaN (hFsub hx)) hxx'
      rw [hxx] at hx'
      exact hx.2 (mem_iUnion₂.mpr ⟨_, ⟨he, hc, hae⟩, hx'⟩)
    have hFU : h '' ((frontier (C a) ∩ frontier N) \
        ⋃ f ∈ {f : Finset E3 | f ∈ K.faces ∧ f.card = 2 ∧ a ∈ f}, Dbd f) ⊆ U := by
      obtain ⟨p, hpBa, hpF⟩ := hBaF
      refine habs _ (((ht.freeFaceConnected a ha).image h
        (hcont.mono (hFsub.trans hCaN))).isPreconnected) hFZ ⟨p, hpF, hBaU' hpBa⟩
    have hclF := ht.frontier_inter_frontier_subset_closure_freeFace ha
    have hclsub : closure ((frontier (C a) ∩ frontier N) \
        ⋃ f ∈ {f : Finset E3 | f ∈ K.faces ∧ f.card = 2 ∧ a ∈ f}, Dbd f) ⊆ C a :=
      closure_minimal hFsub hCacl
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨?_, fun hxint => ?_⟩
    · exact closure_mono hFU ((hcont.mono (hclsub.trans hCaN)).image_closure ⟨x, hclF hx, rfl⟩)
    · have hxY₀ : x ∈ C u ∪ C v := by
        rcases eq_or_eq_of_mem_of_card_eq_two hc hue hve huv hae with h1 | h1
        · rw [← h1]
          exact Or.inl (hCacl.frontier_subset hx.1)
        · rw [← h1]
          exact Or.inr (hCacl.frontier_subset hx.1)
      exact hNfr x hxY₀ hx.2 (interior_mono (hUZ.trans sdiff_subset) hxint)
  have habsorb : ∀ w ∈ O, ∀ V : Set E3, IsPreconnected V → V ⊆ Y \ Ec →
      (V ∩ ((Y \ Ec) ∩ closure (connectedComponentIn O w))).Nonempty →
      V ⊆ (Y \ Ec) ∩ closure (connectedComponentIn O w) := by
    intro w hwO V hV hVZ ⟨y, hyV, hyU⟩
    rcases hcomp2 w hwO with h1 | h1
    · rw [h1] at hyU ⊢
      rcases hpre V hV hVZ with h2 | h2
      · exact h2
      · exact absurd (h2 hyV) (disjoint_left.mp hdisj hyU)
    · rw [h1] at hyU ⊢
      rcases hpre V hV hVZ with h2 | h2
      · exact absurd hyU (disjoint_left.mp hdisj (h2 hyV))
      · exact h2
  have huU : h u ∈ (Y \ Ec) ∩ closure (connectedComponentIn O (h u)) :=
    ⟨hOZ huO, subset_closure (mem_connectedComponentIn huO)⟩
  have hvU : h v ∈ (Y \ Ec) ∩ closure (connectedComponentIn O (h v)) :=
    ⟨hOZ hvO, subset_closure (mem_connectedComponentIn hvO)⟩
  refine ⟨(Y \ Ec) ∩ closure (connectedComponentIn O (h u)),
    (Y \ Ec) ∩ closure (connectedComponentIn O (h v)), huU, hvU,
    (isConnected_connectedComponentIn_iff.mpr huO).subset_closure
      (subset_inter (hΓsub _ huO) subset_closure) inter_subset_right,
    (isConnected_connectedComponentIn_iff.mpr hvO).subset_closure
      (subset_inter (hΓsub _ hvO) subset_closure) inter_subset_right,
    hdisj, hcover, hpre, hEfr _ huO, hEfr _ hvO, ?_, ?_⟩
  · exact hfree u hu hue _ Bu inter_subset_left (habsorb _ huO) hBuc hBuC hBuE
      ⟨h u, hBuu, huU⟩ hBuF
  · exact hfree v hv hve _ Bv inter_subset_left (habsorb _ hvO) hBvc hBvC hBvE
      ⟨h v, hBvv, hvU⟩ hBvF

end Leaves

end DifferentialGeometry.Topology.PiecewiseLinear
