/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.HandlePieceChart
import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedralTubeConnected

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem geometricLink_restrict_eq_of_forall_convexHull_subset {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E] (T : Geometry.SimplicialComplex ℝ E)
    (A : Set E) {w : E} (hw : ∀ s ∈ T.faces, w ∈ s → convexHull ℝ (s : Set E) ⊆ A) :
    SimplicialComplex.geometricLink (restrict T A) {w} = SimplicialComplex.geometricLink T {w} := by
  ext t
  rw [SimplicialComplex.mem_geometricLink_singleton, SimplicialComplex.mem_geometricLink_singleton]
  constructor
  · rintro ⟨hne, hwt, hins⟩
    exact ⟨hne, hwt, hins.1⟩
  · rintro ⟨hne, hwt, hins⟩
    exact ⟨hne, hwt, hins, hw _ hins (Finset.mem_insert_self w t)⟩

section HandlePieceSurface

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {K : Geometry.SimplicialComplex ℝ E3} {N N' : Set E3} {C : E3 → Set E3}
  {D Dbd Ec Eint Ebd : Finset E3 → Set E3} {h : E3 → E3} {Cpp : E3 → Set E3}
  {XK : Geometry.SimplicialComplex ℝ E3}

theorem IsPolyhedralTubeNeighborhood.exists_handlePieceSurface
    (hd : IsHandleDecompositionOfTube K N C D Dbd h N' Ec Eint Ebd Cpp)
    (h2 : IsPolyhedralTubeNeighborhood K h N' Ec Eint Ebd XK)
    (h34 : HasSinglePolygonTraces K h Ec XK.space) (hSconn : IsConnected (frontier XK.space))
    (hconn : IsConnected K.space) {v : E3} (hv : v ∈ K.vertices) :
    ∃ A : Geometry.SimplicialComplex ℝ E3, A.faces.Finite ∧
      A.space = Cpp v ∩ frontier XK.space ∧ IsCombinatorialManifoldWithBoundary 2 A ∧
        IsConnected A.space ∧
          (@boundaryComplex _ _ _ (fun a b => Classical.propDecidable (a = b)) 2 A).space =
            ⋃ e ∈ edgesAt K v, Ec e ∩ frontier XK.space := by
  let _ : DecidableEq E3 := fun a b => Classical.propDecidable (a = b)
  have : Finite XK.faces := h2.facesFinite.to_subtype
  have ht := hd.tube
  have hXc : IsClosed XK.space := (isPolyhedron_space XK).isClosed
  have hSX : frontier XK.space ⊆ XK.space := hXc.frontier_subset
  have hSN : frontier XK.space ⊆ interior N' := hSX.trans h2.subsetInterior
  have hfin : {e : Finset E3 | e ∈ K.faces ∧ e.card = 2}.Finite :=
    ht.facesFinite.subset fun e he => he.1
  have hCc : IsClosed (Cpp v) := by
    rw [hd.componentClosure v hv]
    exact isClosed_closure
  let eF := hfin.toFinset
  have heF : ∀ e, e ∈ eF ↔ e ∈ K.faces ∧ e.card = 2 := fun e => hfin.mem_toFinset
  let Jall : Set E3 := ⋃ e ∈ eF, Ec e ∩ frontier XK.space
  have hJpoly : IsPolyhedron Jall := by
    have heq : Jall = ⋃ e ∈ eF, (if e ∈ eF then Ec e ∩ frontier XK.space else ∅) :=
      iUnion₂_congr fun e he => (ite_eq_left he).symm
    rw [heq]
    refine IsPolyhedron.finsetBiUnion eF fun e => ?_
    split_ifs with he
    · exact (h34 e ((heF e).mp he).1 ((heF e).mp he).2).1.isPolyhedron
    · exact IsPolyhedron.empty
  have hJS : Jall ⊆ frontier XK.space := iUnion₂_subset fun e _ => inter_subset_right
  obtain ⟨Dc, hDfin, hDm, hDsp⟩ :=
    h2.isManifold.exists_isCombinatorialManifold_space_eq_frontier (n := 2) (by simp)
  have : Finite Dc.faces := hDfin.to_subtype
  obtain ⟨T, hT, hTfin, hTJ⟩ :=
    exists_isSubdivision_restrict_space Dc hJpoly (by rw [hDsp]; exact hJS)
  have : Finite T.faces := hTfin.to_subtype
  have hTm : IsCombinatorialManifold 2 T := hDm.of_isSubdivision hT
  have hTsp : T.space = frontier XK.space := hT.space_eq.trans hDsp
  have hSJ : ∀ y ∈ frontier XK.space, y ∉ Jall →
      y ∈ interior N' \ ⋃ e ∈ {e : Finset E3 | e ∈ K.faces ∧ e.card = 2}, Ec e := by
    intro y hy hyJ
    refine ⟨hSN hy, fun hyU => hyJ ?_⟩
    obtain ⟨e, he, hye⟩ := mem_iUnion₂.mp hyU
    exact mem_iUnion₂.mpr ⟨e, (heF e).mpr he, hye, hy⟩
  have hint : ∀ y ∈ frontier XK.space, y ∈ Cpp v → y ∉ Jall → y ∈ interior (Cpp v) :=
    fun y hy hyC hyJ => hd.subset_interior_handlePiece hv ⟨hSJ y hy hyJ, hyC⟩
  have hK2 : ∀ T' : Geometry.SimplicialComplex ℝ E3, T'.space = frontier XK.space →
      (restrict T' Jall).space = Jall → ∀ s ∈ T'.faces, ∀ y ∈ convexHull ℝ (s : Set E3),
        y ∈ Cpp v → y ∉ Jall → convexHull ℝ (s : Set E3) ⊆ Cpp v := by
    intro T' hT'sp hT'J s hs y hys hyC hyJ
    have hopen : openSimplex s ⊆
        interior N' \ ⋃ e ∈ {e : Finset E3 | e ∈ K.faces ∧ e.card = 2}, Ec e := by
      intro z hz
      have hzS : z ∈ frontier XK.space := by
        rw [← hT'sp]
        exact T'.convexHull_subset_space hs (openSimplex_subset_convexHull s hz)
      refine hSJ z hzS fun hzJ => hyJ ?_
      have hsJ : s ∈ (restrict T' Jall).faces :=
        mem_faces_of_mem_openSimplex_of_mem_space (restrict_faces_subset T' Jall) hs hz
          (by rw [hT'J]; exact hzJ)
      exact hsJ.2 hys
    have hyS : y ∈ frontier XK.space := by
      rw [← hT'sp]
      exact T'.convexHull_subset_space hs hys
    have hyint := hint y hyS hyC hyJ
    have hcl := convexHull_subset_closure_openSimplex (T'.nonempty_of_mem_faces hs)
    obtain ⟨z, hzint, hzs⟩ := mem_closure_iff_nhds.mp (hcl hys) _ (isOpen_interior.mem_nhds hyint)
    have hsub := hd.subset_handlePiece_of_isPreconnected hv (convex_openSimplex s).isPreconnected
      hopen ⟨z, hzs, interior_subset hzint⟩
    exact hcl.trans (closure_minimal hsub hCc)
  have hJv : ∀ y ∈ Jall, y ∈ Cpp v → ∃ f, (f ∈ K.faces ∧ f.card = 2) ∧ v ∈ f ∧
      y ∈ Ec f ∩ frontier XK.space := by
    intro y hy hyC
    obtain ⟨f, hf, hyf⟩ := mem_iUnion₂.mp hy
    obtain ⟨hfK, hfc⟩ := (heF f).mp hf
    refine ⟨f, ⟨hfK, hfc⟩, ?_, hyf⟩
    by_contra hvf
    have hmem : y ∈ Cpp v ∩ Ec f := ⟨hyC, hyf.1⟩
    rw [hd.handlePiece_inter_pseudoCell_eq_empty hv hfK hfc hvf] at hmem
    exact hmem
  have hJcomp : ∀ f, f ∈ K.faces ∧ f.card = 2 → ∀ P : Set E3, IsPreconnected P → P ⊆ Jall →
      (P ∩ (Ec f ∩ frontier XK.space)).Nonempty → P ⊆ Ec f ∩ frontier XK.space := by
    intro f hf P hP hPJ hne
    have hfF : f ∈ eF := (heF f).mpr hf
    have hc1 : IsClosed (Ec f ∩ frontier XK.space) :=
      (hd.pseudoCell f hf.1 hf.2).isClosed.inter isClosed_frontier
    have hc2 : IsClosed (⋃ g ∈ eF.erase f, Ec g ∩ frontier XK.space) :=
      isClosed_biUnion_finset fun g hg =>
        (hd.pseudoCell g ((heF g).mp (Finset.mem_of_mem_erase hg)).1
          ((heF g).mp (Finset.mem_of_mem_erase hg)).2).isClosed.inter isClosed_frontier
    rcases isPreconnected_iff_subset_of_disjoint_closed.mp hP _ _ hc1 hc2
        (fun y hy => by
          obtain ⟨g, hg, hyg⟩ := mem_iUnion₂.mp (hPJ hy)
          by_cases hgf : g = f
          · rw [hgf] at hyg
            exact Or.inl hyg
          · exact Or.inr (mem_iUnion₂.mpr ⟨g, Finset.mem_erase.mpr ⟨hgf, hg⟩, hyg⟩))
        (by
          rw [Set.eq_empty_iff_forall_notMem]
          rintro y ⟨-, hy1, hy2⟩
          obtain ⟨g, hg, hyg⟩ := mem_iUnion₂.mp hy2
          have hgK := (heF g).mp (Finset.mem_of_mem_erase hg)
          exact Set.disjoint_left.mp (hd.pseudoCellDisjoint f hf.1 hf.2 g hgK.1 hgK.2
            (Ne.symm (Finset.ne_of_mem_erase hg))) hy1.1 hyg.1) with h1 | h1
    · exact h1
    · obtain ⟨y, hyP, hyf⟩ := hne
      obtain ⟨g, hg, hyg⟩ := mem_iUnion₂.mp (h1 hyP)
      have hgK := (heF g).mp (Finset.mem_of_mem_erase hg)
      exact (Set.disjoint_left.mp (hd.pseudoCellDisjoint f hf.1 hf.2 g hgK.1 hgK.2
        (Ne.symm (Finset.ne_of_mem_erase hg))) hyf.1 hyg.1).elim
  let A := restrict T (Cpp v ∩ frontier XK.space)
  have : Finite A.faces := (restrict_faces_finite T _).to_subtype
  have hAsp : A.space = Cpp v ∩ frontier XK.space := by
    refine Subset.antisymm (restrict_space_subset T _) fun y hy => ?_
    obtain ⟨s, hs, hys⟩ := exists_face_mem_openSimplex T (by rw [hTsp]; exact hy.2)
    have hyconv := openSimplex_subset_convexHull s hys
    by_cases hyJ : y ∈ Jall
    · obtain ⟨f, hf, hvf, hyf⟩ := hJv y hyJ hy.1
      have hsJ : s ∈ (restrict T Jall).faces :=
        mem_faces_of_mem_openSimplex_of_mem_space (restrict_faces_subset T Jall) hs hys
          (by rw [hTJ]; exact hyJ)
      have hsf := hJcomp f hf _ (convex_convexHull ℝ _).isPreconnected hsJ.2 ⟨y, hyconv, hyf⟩
      exact A.convexHull_subset_space ⟨hs, fun z hz =>
        ⟨hd.pseudoCell_subset_handlePiece hf.1 hf.2 hvf (hsf hz).1, (hsf hz).2⟩⟩ hyconv
    · refine A.convexHull_subset_space ⟨hs, fun z hz => ⟨hK2 T hTsp hTJ s hs y hyconv hy.1 hyJ hz,
        ?_⟩⟩ hyconv
      rw [← hTsp]
      exact T.convexHull_subset_space hs hz
  have hwA : ∀ w, {w} ∈ A.faces → w ∈ Cpp v ∩ frontier XK.space := fun w hw =>
    restrict_space_subset T _ (A.convexHull_subset_space hw (subset_convexHull ℝ _ (by simp)))
  have hAm : IsCombinatorialManifoldWithBoundary 2 A := by
    intro w hw
    by_cases hwJ : w ∈ Jall
    · right
      obtain ⟨f, hf, hvf, hwf⟩ := hJv w hwJ (hwA w hw).1
      exact h2.isPLBall_geometricLink_handlePiece hd hv hf.1 hf.2 hvf A hAsp hw hwf
    · left
      rw [geometricLink_restrict_eq_of_forall_convexHull_subset T (Cpp v ∩ frontier XK.space)
        fun s hs hws z hz => ⟨hK2 T hTsp hTJ s hs w
          (subset_convexHull ℝ _ (Finset.mem_coe.mpr hws)) (hwA w hw).1 hwJ hz,
          by rw [← hTsp]; exact T.convexHull_subset_space hs hz⟩]
      exact hTm w hw.1
  refine ⟨A, restrict_faces_finite T _, hAsp, hAm, ?_, ?_⟩
  · rw [hAsp]
    have hKN : K.space ⊆ N :=
      (subset_interior_iff_mem_nhdsSet.mpr ht.isNeighborhood).trans interior_subset
    have hvN : ∀ a ∈ K.vertices, a ∈ N := fun a ha => hKN (K.vertices_subset_space ha)
    have hKint : h '' K.space ⊆ interior XK.space :=
      subset_interior_iff_mem_nhdsSet.mpr h2.isNeighborhood
    have hvEc : ∀ g, (g ∈ K.faces ∧ g.card = 2) → v ∈ g → h v ∉ Ec g := by
      intro g hg hvg hvE
      obtain ⟨w', hw'g, hw'v⟩ := Finset.exists_mem_ne (by omega : 1 < g.card) v
      have hw' : w' ∈ K.vertices :=
        K.down_closed hg.1 (Finset.singleton_subset_iff.mpr hw'g) (Finset.singleton_nonempty w')
      have hmem : h v ∈ Cpp w' ∩ h '' K.vertices :=
        ⟨hd.pseudoCell_subset_handlePiece hg.1 hg.2 hw'g hvE, v, hv, rfl⟩
      rw [hd.oneVertex w' hw'] at hmem
      exact hw'v (ht.injOn (hvN v hv) (hvN w' hw') hmem).symm
    obtain ⟨f₀, hf₀, hvf₀⟩ : ∃ f, (f ∈ K.faces ∧ f.card = 2) ∧ v ∈ f := by
      obtain ⟨e₀, he₀, hc₀⟩ := ht.hasEdge
      obtain ⟨w₀, hw₀e, hw₀v⟩ := Finset.exists_mem_ne (by omega : 1 < e₀.card) v
      have hw₀ : w₀ ∈ K.vertices :=
        K.down_closed he₀ (Finset.singleton_subset_iff.mpr hw₀e) (Finset.singleton_nonempty w₀)
      have : Finite K.faces := ht.facesFinite.to_subtype
      obtain ⟨p⟩ := (edgeGraph_connected_of_isConnected_space K hconn).preconnected
        (⟨v, hv⟩ : K.vertices) ⟨w₀, hw₀⟩
      cases p with
      | nil => exact (hw₀v rfl).elim
      | cons hadj _ =>
        obtain ⟨hne, hmem⟩ := hadj
        rw [classical_insert_singleton_eq_pair] at hmem
        refine ⟨_, ⟨hmem, Finset.card_pair fun h => hne (Subtype.ext h)⟩, ?_⟩
        exact Finset.mem_insert_self _ _
    have hJA : ∀ f, (f ∈ K.faces ∧ f.card = 2) → v ∈ f →
        Ec f ∩ frontier XK.space ⊆ Cpp v ∩ frontier XK.space := fun f hf hvf y hy =>
      ⟨hd.pseudoCell_subset_handlePiece hf.1 hf.2 hvf hy.1, hy.2⟩
    refine ⟨(h34 f₀ hf₀.1 hf₀.2).1.nonempty.mono (hJA f₀ hf₀ hvf₀), ?_⟩
    rw [isPreconnected_iff_subset_of_disjoint_closed]
    intro u w hu hw hAuw hAdis
    have hdis : ∀ y ∈ Cpp v ∩ frontier XK.space, y ∈ u → y ∈ w → False :=
      fun y hy hyu hyw => (Set.eq_empty_iff_forall_notMem.mp hAdis) y ⟨hy, hyu, hyw⟩
    have hJuw : ∀ f, (f ∈ K.faces ∧ f.card = 2) → v ∈ f →
        Ec f ∩ frontier XK.space ⊆ u ∨ Ec f ∩ frontier XK.space ⊆ w := by
      intro f hf hvf
      refine isPreconnected_iff_subset_of_disjoint_closed.mp
        (h34 f hf.1 hf.2).1.isConnected_one.isPreconnected u w hu hw
        ((hJA f hf hvf).trans hAuw) ?_
      rw [Set.eq_empty_iff_forall_notMem]
      rintro y ⟨hy, hyu, hyw⟩
      exact hdis y (hJA f hf hvf hy) hyu hyw
    have hnoJ : ∀ u w : Set E3, IsClosed u → IsClosed w →
        Cpp v ∩ frontier XK.space ⊆ u ∪ w →
        (∀ y ∈ Cpp v ∩ frontier XK.space, y ∈ u → y ∈ w → False) →
        (∀ f, (f ∈ K.faces ∧ f.card = 2) → v ∈ f → Ec f ∩ frontier XK.space ⊆ u) →
        Cpp v ∩ frontier XK.space ⊆ u := by
      intro u w hu hw hAuw hdis hall
      by_contra hnot
      obtain ⟨y, hyA, hyu⟩ := not_subset.mp hnot
      have hyw : y ∈ w := (hAuw hyA).resolve_left hyu
      have hAwc : IsClosed (Cpp v ∩ frontier XK.space ∩ w) :=
        (hCc.inter isClosed_frontier).inter hw
      rcases isPreconnected_iff_subset_of_disjoint.mp hSconn.isPreconnected
          (interior (Cpp v) ∩ uᶜ) (Cpp v ∩ frontier XK.space ∩ w)ᶜ
          (isOpen_interior.inter hu.isOpen_compl) hAwc.isOpen_compl
          (fun z hz => by
            by_cases hzAw : z ∈ Cpp v ∩ frontier XK.space ∩ w
            · refine Or.inl ⟨?_, fun hzu => hdis z hzAw.1 hzu hzAw.2⟩
              refine hint z hz hzAw.1.1 fun hzJ => ?_
              obtain ⟨f, hf, hvf, hzf⟩ := hJv z hzJ hzAw.1.1
              exact hdis z hzAw.1 (hall f hf hvf hzf) hzAw.2
            · exact Or.inr hzAw)
          (by
            rw [Set.eq_empty_iff_forall_notMem]
            rintro z ⟨hzS, ⟨hzi, hzu⟩, hzAw⟩
            have hzA : z ∈ Cpp v ∩ frontier XK.space := ⟨interior_subset hzi, hzS⟩
            exact hzAw ⟨hzA, (hAuw hzA).resolve_left hzu⟩) with h1 | h1
      · obtain ⟨z, hz⟩ := (h34 f₀ hf₀.1 hf₀.2).1.nonempty
        exact (h1 hz.2).2 (hall f₀ hf₀ hvf₀ hz)
      · exact h1 hyA.2 ⟨hyA, hyw⟩
    by_cases hallu : ∀ f, (f ∈ K.faces ∧ f.card = 2) → v ∈ f →
        Ec f ∩ frontier XK.space ⊆ u
    · exact Or.inl (hnoJ u w hu hw hAuw hdis hallu)
    by_cases hallw : ∀ f, (f ∈ K.faces ∧ f.card = 2) → v ∈ f →
        Ec f ∩ frontier XK.space ⊆ w
    · exact Or.inr (hnoJ w u hw hu (fun y hy => (hAuw hy).symm)
        (fun y hy h1 h2 => hdis y hy h2 h1) hallw)
    exfalso
    push Not at hallu hallw
    obtain ⟨f₂, hf₂, hvf₂, hf₂u⟩ := hallu
    obtain ⟨f₁, hf₁, hvf₁, hf₁w⟩ := hallw
    have hH := hd.isConnected_compl_interior hconn
    have hXH : ∀ z ∈ (interior N')ᶜ, z ∉ XK.space := fun z hz hzX =>
      hz (h2.subsetInterior hzX)
    let Fset : Set E3 → Set E3 := fun u' => Cpp v ∩ frontier XK.space ∩ u' ∪
      ⋃ f ∈ {f : Finset E3 | (f ∈ K.faces ∧ f.card = 2) ∧ v ∈ f ∧
        Ec f ∩ frontier XK.space ⊆ u'}, Ec f ∩ XK.space
    have hmemF : ∀ u', ∀ z ∈ Fset u', z ∈ Cpp v ∩ frontier XK.space ∩ u' ∨
        ∃ f, ((f ∈ K.faces ∧ f.card = 2) ∧ v ∈ f ∧ Ec f ∩ frontier XK.space ⊆ u') ∧
          z ∈ Ec f ∩ XK.space := by
      rintro u' z (hz | hz)
      · exact Or.inl hz
      · obtain ⟨f, hf, hzf⟩ := mem_iUnion₂.mp hz
        exact Or.inr ⟨f, hf, hzf⟩
    have hFX : ∀ u', Fset u' ⊆ XK.space := by
      intro u' z hz
      rcases hmemF u' z hz with hz | ⟨f, -, hzf⟩
      · exact hSX hz.1.2
      · exact hzf.2
    have hFc : ∀ u', IsClosed u' → IsClosed (Fset u') := fun u' hu' =>
      ((hCc.inter isClosed_frontier).inter hu').union
        ((hfin.subset fun f hf => hf.1).isClosed_biUnion fun f hf =>
          (hd.pseudoCell f hf.1.1 hf.1.2).isClosed.inter hXc)
    have hdisF : ∀ u' w' : Set E3,
        (∀ y ∈ Cpp v ∩ frontier XK.space, y ∈ u' → y ∈ w' → False) →
        Disjoint (Fset u') (Fset w') := by
      intro u' w' hdis'
      refine Set.disjoint_left.mpr fun z hz1 hz2 => ?_
      rcases hmemF u' z hz1 with hz1 | ⟨f, ⟨hf, hvf, hfu⟩, hzf⟩ <;>
        rcases hmemF w' z hz2 with hz2 | ⟨g, ⟨hg, hvg, hgw⟩, hzg⟩
      · exact hdis' z hz1.1 hz1.2 hz2.2
      · exact hdis' z hz1.1 hz1.2 (hgw ⟨hzg.1, hz1.1.2⟩)
      · exact hdis' z hz2.1 (hfu ⟨hzf.1, hz2.1.2⟩) hz2.2
      · by_cases hfg : f = g
        · rw [← hfg] at hgw
          obtain ⟨y, hy⟩ := (h34 f hf.1 hf.2).1.nonempty
          exact hdis' y (hJA f hf hvf hy) (hfu hy) (hgw hy)
        · exact Set.disjoint_left.mp (hd.pseudoCellDisjoint f hf.1 hf.2 g hg.1 hg.2 hfg)
            hzf.1 hzg.1
    have hY : ∀ z ∈ XK.space ∩ Cpp v, z ∉ Fset u ∪ Fset w →
        z ∈ interior (XK.space ∩ Cpp v) := by
      rintro z ⟨hzX, hzC⟩ hzF
      have hzS : z ∉ frontier XK.space := by
        intro hzS
        rcases hAuw ⟨hzC, hzS⟩ with hzu | hzw
        · exact hzF (Or.inl (Or.inl ⟨⟨hzC, hzS⟩, hzu⟩))
        · exact hzF (Or.inr (Or.inl ⟨⟨hzC, hzS⟩, hzw⟩))
      have hzi : z ∈ interior XK.space := (mem_interior_iff_notMem_frontier hzX).mpr hzS
      have hzO : z ∈ interior N' \
          ⋃ e ∈ {e : Finset E3 | e ∈ K.faces ∧ e.card = 2}, Ec e := by
        refine ⟨h2.subsetInterior hzX, fun hzU => ?_⟩
        obtain ⟨g, hg, hzg⟩ := mem_iUnion₂.mp hzU
        by_cases hvg : v ∈ g
        · rcases hJuw g hg hvg with hgu | hgw
          · exact hzF (Or.inl (Or.inr (mem_iUnion₂.mpr ⟨g, ⟨hg, hvg, hgu⟩, hzg, hzX⟩)))
          · exact hzF (Or.inr (Or.inr (mem_iUnion₂.mpr ⟨g, ⟨hg, hvg, hgw⟩, hzg, hzX⟩)))
        · have hmem : z ∈ Cpp v ∩ Ec g := ⟨hzC, hzg⟩
          rw [hd.handlePiece_inter_pseudoCell_eq_empty hv hg.1 hg.2 hvg] at hmem
          exact hmem
      rw [interior_inter]
      exact ⟨hzi, hd.subset_interior_handlePiece hv ⟨hzO, hzC⟩⟩
    have hvK : h v ∈ h '' K.space := ⟨v, K.vertices_subset_space hv, rfl⟩
    have hvCpp : h v ∈ Cpp v := by
      have hmem : h v ∈ Cpp v ∩ h '' K.vertices := by
        rw [hd.oneVertex v hv]
        exact rfl
      exact hmem.1
    have hvF : h v ∉ Fset u ∪ Fset w := by
      have hvS : h v ∉ frontier XK.space := fun hS => hS.2 (hKint hvK)
      rintro (hz | hz) <;> rcases hmemF _ _ hz with hz | ⟨g, ⟨hg, hvg, -⟩, hzg⟩
      · exact hvS hz.1.2
      · exact hvEc g hg hvg hzg.1
      · exact hvS hz.1.2
      · exact hvEc g hg hvg hzg.1
    have hsep : Separates (⋃ b : Bool, cond b (Fset u) (Fset w)) {h v} (interior N')ᶜ := by
      rw [← union_eq_iUnion]
      refine ⟨interior (XK.space ∩ Cpp v) \ (Fset u ∪ Fset w),
        (XK.space ∩ Cpp v)ᶜ \ (Fset u ∪ Fset w),
        isOpen_interior.sdiff ((hFc u hu).union (hFc w hw)),
        (hXc.inter hCc).isOpen_compl.sdiff ((hFc u hu).union (hFc w hw)),
        Set.disjoint_left.mpr fun z hz1 hz2 => hz2.1 (interior_subset hz1.1), ?_, ?_, ?_⟩
      · ext z
        constructor
        · rintro (hz | hz)
          · exact hz.2
          · exact hz.2
        · intro hz
          by_cases hzXC : z ∈ XK.space ∩ Cpp v
          · exact Or.inl ⟨hY z hzXC hz, hz⟩
          · exact Or.inr ⟨hzXC, hz⟩
      · rintro _ rfl
        exact ⟨hY (h v) ⟨interior_subset (hKint hvK), hvCpp⟩ hvF, hvF⟩
      · intro z hz
        refine ⟨fun hzXC => hXH z hz hzXC.1, fun hzF => hXH z hz ?_⟩
        rcases hzF with hzF | hzF
        · exact hFX u hzF
        · exact hFX w hzF
    obtain ⟨b, hb⟩ := exists_separates_of_finite_iUnion
      (fun O hO hconn => hO.isConnected_iff_isPathConnected.mp hconn)
      (fun b : Bool => cond b (Fset u) (Fset w))
      (fun b => by cases b; exacts [hFc w hw, hFc u hu])
      (by
        rintro (_ | _) (_ | _) hne
        · exact (hne rfl).elim
        · exact (hdisF u w hdis).symm
        · exact hdisF u w hdis
        · exact (hne rfl).elim)
      isConnected_singleton hH hsep
    have hcontra : ∀ (u' w' : Set E3) (f : Finset E3), (f ∈ K.faces ∧ f.card = 2) → v ∈ f →
        Ec f ∩ frontier XK.space ⊆ w' → ¬ Ec f ∩ frontier XK.space ⊆ u' →
        (∀ y ∈ Cpp v ∩ frontier XK.space, y ∈ u' → y ∈ w' → False) →
        Separates (Fset u') {h v} (interior N')ᶜ → False := by
      intro u' w' f hf hvf hfw hfu hdis' hsep'
      have hsegf : segment ℝ v (f.centroid ℝ id) ⊆ convexHull ℝ (f : Set E3) :=
        (convex_convexHull ℝ _).segment_subset
          (subset_convexHull ℝ _ (Finset.mem_coe.mpr hvf))
          (f.centroid_mem_convexHull (K.nonempty_of_mem_faces hf.1))
      have hsegK : segment ℝ v (f.centroid ℝ id) ⊆ K.space :=
        hsegf.trans (K.convexHull_subset_space hf.1)
      have harm : IsPreconnected (h '' segment ℝ v (f.centroid ℝ id)) :=
        (convex_segment _ _).isPreconnected.image h (ht.continuousOn.mono (hsegK.trans hKN))
      have hpcf := hd.pseudoCell f hf.1 hf.2
      have hEconn : IsPreconnected (Ec f) := by
        obtain ⟨ψ⟩ := hpcf.isOpenCell
        have : PreconnectedSpace (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
          isPreconnected_iff_preconnectedSpace.mp (convex_ball 0 1).isPreconnected
        have hr := isPreconnected_range (continuous_subtype_val.comp ψ.symm.continuous)
        rw [range_comp, ψ.symm.surjective.range_eq, image_univ, Subtype.range_coe] at hr
        rw [hpcf.carrierEq, ← hpcf.closureEq]
        exact hr.closure
      have hPf : h (f.centroid ℝ id) ∈ Ec f := by
        rw [hpcf.carrierEq]
        exact Or.inl hpcf.centerMem
      have hrim : (Ebd f ∩ (interior N')ᶜ).Nonempty := by
        obtain ⟨ψ⟩ := hpcf.isSphere
        have hs : ((EuclideanSpace.single 0 1 : EuclideanSpace ℝ (Fin 2))) ∈
            Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
          simp
        refine ⟨ψ.symm ⟨_, hs⟩, (ψ.symm ⟨_, hs⟩).2, ?_⟩
        have hy : ((ψ.symm ⟨_, hs⟩ : Ebd f) : E3) ∈ Ec f ∩ frontier N' := by
          rw [hd.rimFrontier f hf.1 hf.2]
          exact (ψ.symm ⟨_, hs⟩).2
        exact hy.2.2
      have hΓ : IsPreconnected
          (h '' segment ℝ v (f.centroid ℝ id) ∪ Ec f ∪ (interior N')ᶜ) := by
        have h1 := IsPreconnected.union (h (f.centroid ℝ id))
          (mem_image_of_mem h (right_mem_segment ℝ _ _)) hPf harm hEconn
        obtain ⟨z, hzB, hzH⟩ := hrim
        have hzE : z ∈ Ec f := by
          rw [hpcf.carrierEq]
          exact Or.inr hzB
        exact IsPreconnected.union z (Or.inr hzE) hzH h1 hH.isPreconnected
      obtain ⟨z, hzF, hzΓ⟩ := hsep'.inter_nonempty_of_isPreconnected hΓ
        ⟨h v, rfl, Or.inl (Or.inl ⟨v, left_mem_segment ℝ _ _, rfl⟩)⟩
        (hH.nonempty.mono fun z hz => ⟨hz, Or.inr hz⟩)
      rcases hzΓ with (⟨t, ht', rfl⟩ | hzE) | hzH
      · rcases hmemF u' _ hzF with hz | ⟨g, ⟨hg, hvg, hgu⟩, hzg⟩
        · exact hz.1.2.2 (hKint ⟨t, hsegK ht', rfl⟩)
        · have hgf : g ≠ f := fun hgf => hfu (hgf ▸ hgu)
          have hmeet : h t ∈ Ec g ∩ h '' K.space := ⟨hzg.1, t, hsegK ht', rfl⟩
          rw [hd.meetsGraph g hg.1 hg.2] at hmeet
          have htc : t = g.centroid ℝ id := ht.injOn (hKN (hsegK ht'))
            (hKN (K.convexHull_subset_space hg.1
              (g.centroid_mem_convexHull (K.nonempty_of_mem_faces hg.1)))) hmeet
          have hcg : g.centroid ℝ id ∈ convexHull ℝ ((g : Set E3) ∩ (f : Set E3)) :=
            K.inter_subset_convexHull hg.1 hf.1
              ⟨g.centroid_mem_convexHull (K.nonempty_of_mem_faces hg.1), htc ▸ hsegf ht'⟩
          have hgfv : (g : Set E3) ∩ (f : Set E3) ⊆ {v} := by
            rintro y ⟨hyg, hyf⟩
            by_contra hyv
            have hy' : y ≠ v := hyv
            have hpg : ({v, y} : Finset E3) = g := Finset.eq_of_subset_of_card_le
              (Finset.insert_subset hvg (Finset.singleton_subset_iff.mpr hyg))
              (by rw [hg.2, Finset.card_pair hy'.symm])
            have hpf : ({v, y} : Finset E3) = f := Finset.eq_of_subset_of_card_le
              (Finset.insert_subset hvf (Finset.singleton_subset_iff.mpr hyf))
              (by rw [hf.2, Finset.card_pair hy'.symm])
            exact hgf (hpg.symm.trans hpf)
          have hcv : g.centroid ℝ id = v := by
            have hmem := convexHull_mono hgfv hcg
            rwa [convexHull_singleton, mem_singleton_iff] at hmem
          exact hvEc g hg hvg (by rw [← hcv, ← htc]; exact hzg.1)
      · rcases hmemF u' z hzF with hz | ⟨g, ⟨hg, hvg, hgu⟩, hzg⟩
        · exact hdis' z hz.1 hz.2 (hfw ⟨hzE, hz.1.2⟩)
        · have hgf : g ≠ f := fun hgf => hfu (hgf ▸ hgu)
          exact Set.disjoint_left.mp (hd.pseudoCellDisjoint g hg.1 hg.2 f hf.1 hf.2 hgf)
            hzg.1 hzE
      · exact hXH z hzH (hFX u' hzF)
    cases b
    · exact hcontra w u f₁ hf₁ hvf₁ ((hJuw f₁ hf₁ hvf₁).resolve_right hf₁w) hf₁w
        (fun y hy h1 h2 => hdis y hy h2 h1) hb
    · exact hcontra u w f₂ hf₂ hvf₂ ((hJuw f₂ hf₂ hvf₂).resolve_left hf₂u) hf₂u hdis hb
  · ext x
    constructor
    · intro hx
      have hxA : x ∈ A.space := boundaryComplex_space_subset 2 A hx
      rw [hAsp] at hxA
      by_contra hxU
      have hxJ : x ∉ Jall := fun hxJ => by
        obtain ⟨f, hf, hvf, hxf⟩ := hJv x hxJ hxA.1
        exact hxU (mem_iUnion₂.mpr ⟨f, ⟨hf.1, hf.2, hvf⟩, hxf⟩)
      obtain ⟨T', hT', hT'fin, hxT'⟩ :=
        exists_isSubdivision_singleton_mem T (by rw [hTsp]; exact hxA.2)
      have : Finite T'.faces := hT'fin.to_subtype
      have hT'sp : T'.space = frontier XK.space := hT'.space_eq.trans hTsp
      have hT'J : (restrict T' Jall).space = Jall := by
        have h1 := (hT'.restrict (restrict T Jall) (restrict_faces_subset T Jall)).space_eq
        rwa [hTJ] at h1
      have hRA : IsSubdivision (restrict T' A.space) A :=
        hT'.restrict A (restrict_faces_subset T _)
      have : Finite (restrict T' A.space).faces := (restrict_faces_finite T' _).to_subtype
      have hxR : {x} ∈ (restrict T' A.space).faces := by
        refine ⟨hxT', ?_⟩
        rw [Finset.coe_singleton, convexHull_singleton, singleton_subset_iff, hAsp]
        exact hxA
      have hlink : SimplicialComplex.geometricLink (restrict T' A.space) {x} =
          SimplicialComplex.geometricLink T' {x} := by
        refine geometricLink_restrict_eq_of_forall_convexHull_subset T' A.space
          fun s hs hxs z hz => ?_
        rw [hAsp]
        refine ⟨hK2 T' hT'sp hT'J s hs x (subset_convexHull ℝ _ (Finset.mem_coe.mpr hxs))
          hxA.1 hxJ hz, ?_⟩
        rw [← hT'sp]
        exact T'.convexHull_subset_space hs hz
      have hsph : IsPLSphere 1 (SimplicialComplex.geometricLink T' {x}).space :=
        (hTm.of_isSubdivision hT') x hxT'
      have hball := (isPLBall_geometricLink_iff_mem_boundaryComplex_of_isSubdivision (n := 1)
        A _ hAm hRA hxR).mpr hx
      rw [hlink] at hball
      exact hball.not_isPLSphere hsph
    · intro hx
      obtain ⟨f, hf, hxf⟩ := mem_iUnion₂.mp hx
      have hxA : x ∈ A.space := by
        rw [hAsp]
        exact ⟨hd.pseudoCell_subset_handlePiece hf.1 hf.2.1 hf.2.2 hxf.1, hxf.2⟩
      obtain ⟨R, hRA, hRfin, hxR⟩ := exists_isSubdivision_singleton_mem A hxA
      have : Finite R.faces := hRfin.to_subtype
      have hball := h2.isPLBall_geometricLink_handlePiece hd hv hf.1 hf.2.1 hf.2.2 R
        (hRA.space_eq.trans hAsp) hxR hxf
      exact (isPLBall_geometricLink_iff_mem_boundaryComplex_of_isSubdivision (n := 1)
        A R hAm hRA hxR).mp hball

end HandlePieceSurface

section Leaves

variable {K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))}
  {N N' : Set (EuclideanSpace ℝ (Fin 3))}
  {C Cpp : EuclideanSpace ℝ (Fin 3) → Set (EuclideanSpace ℝ (Fin 3))}
  {D Dbd Ec Eint Ebd : Finset (EuclideanSpace ℝ (Fin 3)) → Set (EuclideanSpace ℝ (Fin 3))}
  {h : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
  {XK : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))}
  {AK : EuclideanSpace ℝ (Fin 3) → Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))}

theorem exists_hasConnectedHandlePieces
    (hd : IsHandleDecompositionOfTube K N C D Dbd h N' Ec Eint Ebd Cpp)
    (hconn : IsConnected K.space)
    (h2 : IsPolyhedralTubeNeighborhood K h N' Ec Eint Ebd XK)
    (h34 : HasSinglePolygonTraces K h Ec XK.space) :
    ∃ (XK' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
      (AK : EuclideanSpace ℝ (Fin 3) → Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))),
      IsPolyhedralTubeNeighborhood K h N' Ec Eint Ebd XK' ∧
      HasSinglePolygonTraces K h Ec XK'.space ∧
      HasConnectedHandlePieces K Ec Cpp XK'.space AK := by
  classical
  obtain ⟨X', hX', hspt', hXc', hFc'⟩ := h2.exists_isConnected hd hconn h34
  have hex := fun v (hv : v ∈ K.vertices) =>
    hX'.exists_handlePieceSurface hd hspt' hFc' hconn hv
  let AK' : EuclideanSpace ℝ (Fin 3) → Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)) :=
    fun v => if hv : v ∈ K.vertices then (hex v hv).choose else X'
  refine ⟨X', AK', hX', hspt', hXc', hFc', fun v hv => ?_⟩
  obtain ⟨hA1, hA2, hA3, hA4, hA5⟩ := (hex v hv).choose_spec
  have hAK : AK' v = (hex v hv).choose := dite_eq_left hv
  rw [hAK]
  refine ⟨hA1, hA2, hA3, hA4, ?_⟩
  convert hA5 using 3

end Leaves

end DifferentialGeometry.Topology.PiecewiseLinear
