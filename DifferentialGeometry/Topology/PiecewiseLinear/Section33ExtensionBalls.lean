/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Connected.Frontier
import DifferentialGeometry.Topology.PiecewiseLinear.HandlePieceChart
import DifferentialGeometry.Topology.PiecewiseLinear.Section33ExtensionSides

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {K : Geometry.SimplicialComplex ℝ E3} {N N' : Set E3} {C Cpp : E3 → Set E3}
  {D Dbd Ec Eint Ebd : Finset E3 → Set E3} {h : E3 → E3}
  {XK : Geometry.SimplicialComplex ℝ E3} {F : Finset E3 → Set E3} {B : E3 → Set E3}

theorem Finset.eq_of_card_eq_two_of_mem_of_mem {e e' : Finset E3} (he : e.card = 2)
    (he' : e'.card = 2) {u v : E3} (huv : u ≠ v) (hue : u ∈ e) (hve : v ∈ e) (hue' : u ∈ e')
    (hve' : v ∈ e') : e = e' := by
  classical
  have h1 : ({u, v} : Finset E3) = e := Finset.eq_of_subset_of_card_le
    (Finset.insert_subset hue (Finset.singleton_subset_iff.mpr hve))
    (by rw [he, Finset.card_pair huv])
  have h2 : ({u, v} : Finset E3) = e' := Finset.eq_of_subset_of_card_le
    (Finset.insert_subset hue' (Finset.singleton_subset_iff.mpr hve'))
    (by rw [he', Finset.card_pair huv])
  rw [← h1, ← h2]

theorem IsHandleDecompositionOfTube.ball_subset_and_disjoint_interior
    (hd : IsHandleDecompositionOfTube K N C D Dbd h N' Ec Eint Ebd Cpp)
    (h34 : HasSinglePolygonTraces K h Ec XK.space) (hXfin : XK.faces.Finite)
    (hXc : IsConnected XK.spaceᶜ) (hFX : ∀ e ∈ K.faces, e.card = 2 → F e ⊆ XK.space)
    (hFbd : ∀ e ∈ K.faces, e.card = 2 → F e ∩ frontier XK.space = Ec e ∩ frontier XK.space)
    (hFc : ∀ e ∈ K.faces, e.card = 2 → IsPreconnected (F e))
    (hFdisj : ∀ e ∈ K.faces, e.card = 2 → ∀ e' ∈ K.faces, e'.card = 2 → e ≠ e' →
      Disjoint (F e) (F e'))
    {v : E3} (hv : v ∈ K.vertices) (hB : IsPLBall 3 (B v))
    (hBfr : frontier (B v) = (Cpp v ∩ frontier XK.space) ∪ ⋃ e ∈ edgesAt K v, F e) :
    B v ⊆ XK.space ∧ Disjoint (interior (B v)) (frontier XK.space) ∧
      ∀ e ∈ K.faces, e.card = 2 → Disjoint (interior (B v)) (F e) := by
  let _ : Finite XK.faces := hXfin.to_subtype
  have hXcl : IsClosed XK.space := (isPolyhedron_space XK).isClosed
  have hBc : IsClosed (B v) := hB.isPolyhedron.isClosed
  have hfrX : frontier (B v) ⊆ XK.space := by
    rw [hBfr]
    refine union_subset (inter_subset_right.trans hXcl.frontier_subset) ?_
    exact iUnion₂_subset fun e he => hFX e he.1 he.2.1
  have hBX : B v ⊆ XK.space := subset_closure.trans
    (closure_subset_of_frontier_subset_of_isConnected_compl
      (isPolyhedron_space XK).isCompact.isBounded hXc hB.isPolyhedron.isCompact.isBounded hfrX)
  have hint : Disjoint (interior (B v)) (frontier XK.space) := by
    rw [disjoint_left]
    intro y hyB hyF
    exact hyF.2 (interior_mono hBX hyB)
  refine ⟨hBX, hint, fun e he hc => ?_⟩
  by_cases hve : v ∈ e
  · have hsub : F e ⊆ frontier (B v) := by
      rw [hBfr]
      exact (subset_biUnion_of_mem (u := F) (show e ∈ edgesAt K v from ⟨he, hc, hve⟩)).trans
        subset_union_right
    exact disjoint_interior_frontier.mono_right hsub
  · have hdis : Disjoint (F e) (frontier (B v)) := by
      rw [hBfr, disjoint_union_right]
      refine ⟨?_, disjoint_iUnion₂_right.mpr fun e' he' =>
        hFdisj e he hc e' he'.1 he'.2.1 fun h => hve (h ▸ he'.2.2)⟩
      rw [disjoint_left]
      rintro y hyF ⟨hyC, hyX⟩
      have hyE : y ∈ F e ∩ frontier XK.space := ⟨hyF, hyX⟩
      rw [hFbd e he hc] at hyE
      have : y ∈ Cpp v ∩ Ec e := ⟨hyC, hyE.1⟩
      rw [hd.handlePiece_inter_pseudoCell_eq_empty hv he hc hve] at this
      exact this
    obtain ⟨y, hy⟩ := (h34 e he hc).1.isConnected.nonempty
    have hyF : y ∈ F e := by
      rw [← hFbd e he hc] at hy
      exact hy.1
    have hcomp := compl_frontier_eq_interior_union_compl hBc
    rcases (hFc e he hc).subset_or_subset isOpen_interior hBc.isOpen_compl
      (disjoint_compl_right.mono_left interior_subset)
      (by rw [← hcomp]; exact fun z hz hzf => disjoint_left.mp hdis hz hzf) with h' | h'
    · exact absurd hy.2 (disjoint_left.mp hint (h' hyF))
    · exact disjoint_left.mpr fun z hz hzF => h' hzF (interior_subset hz)

theorem IsHandleDecompositionOfTube.disjoint_interior_balls
    (hd : IsHandleDecompositionOfTube K N C D Dbd h N' Ec Eint Ebd Cpp)
    (h34 : HasSinglePolygonTraces K h Ec XK.space) (hXfin : XK.faces.Finite)
    (hXc : IsConnected XK.spaceᶜ) (hFX : ∀ e ∈ K.faces, e.card = 2 → F e ⊆ XK.space)
    (hFbd : ∀ e ∈ K.faces, e.card = 2 → F e ∩ frontier XK.space = Ec e ∩ frontier XK.space)
    (hFc : ∀ e ∈ K.faces, e.card = 2 → IsPreconnected (F e))
    (hFdisj : ∀ e ∈ K.faces, e.card = 2 → ∀ e' ∈ K.faces, e'.card = 2 → e ≠ e' →
      Disjoint (F e) (F e'))
    (hB : ∀ v ∈ K.vertices, IsPLBall 3 (B v))
    (hBfr : ∀ v ∈ K.vertices,
      frontier (B v) = (Cpp v ∩ frontier XK.space) ∪ ⋃ e ∈ edgesAt K v, F e)
    (hpt : ∀ v ∈ K.vertices,
      ∃ y ∈ Cpp v ∩ frontier XK.space, ∀ e ∈ K.faces, e.card = 2 → y ∉ Ec e)
    {u v : E3} (hu : u ∈ K.vertices) (hv : v ∈ K.vertices) (huv : u ≠ v) :
    Disjoint (interior (B u)) (interior (B v)) := by
  have hA := fun w (hw : w ∈ K.vertices) =>
    hd.ball_subset_and_disjoint_interior h34 hXfin hXc hFX hFbd hFc hFdisj hw (hB w hw)
      (hBfr w hw)
  have hmiss : ∀ a ∈ K.vertices, ∀ b ∈ K.vertices,
      Disjoint (interior (B a)) (frontier (B b)) := by
    intro a ha b hb
    rw [hBfr b hb, disjoint_union_right]
    exact ⟨(hA a ha).2.1.mono_right inter_subset_right,
      disjoint_iUnion₂_right.mpr fun e he => (hA a ha).2.2 e he.1 he.2.1⟩
  have hsub : ∀ a ∈ K.vertices, ∀ b ∈ K.vertices,
      (interior (B a) ∩ interior (B b)).Nonempty → interior (B a) ⊆ interior (B b) :=
    fun a ha b hb hne => subset_interior_of_isPreconnected_of_disjoint_frontier
      (IsPLBall.isConnected_interior_of_finrank finrank_euclideanSpace_fin (hB a ha)).isPreconnected
      (hmiss a ha b hb) hne
  rw [disjoint_iff_inter_eq_empty]
  by_contra hne
  rw [← ne_eq, ← nonempty_iff_ne_empty] at hne
  have h1 := hsub u hu v hv hne
  have h2 := hsub v hv u hu (by rwa [inter_comm])
  have heq : B u = B v := by
    rw [← (hB u hu).closure_interior, ← (hB v hv).closure_interior, Subset.antisymm h1 h2]
  have hfr := congrArg frontier heq
  rw [hBfr u hu, hBfr v hv] at hfr
  obtain ⟨y, hy, hyE⟩ := hpt u hu
  have hyv : y ∈ (Cpp v ∩ frontier XK.space) ∪ ⋃ e ∈ edgesAt K v, F e := by
    rw [← hfr]
    exact Or.inl hy
  rcases hyv with hyv | hyF
  · obtain ⟨e, he, hce, -, -, hye⟩ := hd.exists_trace_of_mem_inter hu hv huv hy hyv
    exact hyE e he hce hye.1
  · obtain ⟨e, he, hyFe⟩ := mem_iUnion₂.mp hyF
    have hyE' : y ∈ F e ∩ frontier XK.space := ⟨hyFe, hy.2⟩
    rw [hFbd e he.1 he.2.1] at hyE'
    exact hyE e he.1 he.2.1 hyE'.1

theorem IsHandleDecompositionOfTube.exists_edge_of_mem_ball_inter_ball
    (hd : IsHandleDecompositionOfTube K N C D Dbd h N' Ec Eint Ebd Cpp)
    (h34 : HasSinglePolygonTraces K h Ec XK.space) (hXfin : XK.faces.Finite)
    (hXc : IsConnected XK.spaceᶜ) (hFX : ∀ e ∈ K.faces, e.card = 2 → F e ⊆ XK.space)
    (hFbd : ∀ e ∈ K.faces, e.card = 2 → F e ∩ frontier XK.space = Ec e ∩ frontier XK.space)
    (hFc : ∀ e ∈ K.faces, e.card = 2 → IsPreconnected (F e))
    (hFdisj : ∀ e ∈ K.faces, e.card = 2 → ∀ e' ∈ K.faces, e'.card = 2 → e ≠ e' →
      Disjoint (F e) (F e'))
    (hB : ∀ v ∈ K.vertices, IsPLBall 3 (B v))
    (hBfr : ∀ v ∈ K.vertices,
      frontier (B v) = (Cpp v ∩ frontier XK.space) ∪ ⋃ e ∈ edgesAt K v, F e)
    (hpt : ∀ v ∈ K.vertices,
      ∃ y ∈ Cpp v ∩ frontier XK.space, ∀ e ∈ K.faces, e.card = 2 → y ∉ Ec e)
    {u v : E3} (hu : u ∈ K.vertices) (hv : v ∈ K.vertices) (huv : u ≠ v) {y : E3}
    (hy : y ∈ B u ∩ B v) : ∃ e ∈ K.faces, e.card = 2 ∧ u ∈ e ∧ v ∈ e ∧ y ∈ F e := by
  have hA := fun w (hw : w ∈ K.vertices) =>
    hd.ball_subset_and_disjoint_interior h34 hXfin hXc hFX hFbd hFc hFdisj hw (hB w hw)
      (hBfr w hw)
  have hmiss : ∀ a ∈ K.vertices, ∀ b ∈ K.vertices,
      Disjoint (interior (B a)) (frontier (B b)) := by
    intro a ha b hb
    rw [hBfr b hb, disjoint_union_right]
    exact ⟨(hA a ha).2.1.mono_right inter_subset_right,
      disjoint_iUnion₂_right.mpr fun e he => (hA a ha).2.2 e he.1 he.2.1⟩
  have hdisj : ∀ a ∈ K.vertices, ∀ b ∈ K.vertices, a ≠ b →
      Disjoint (interior (B a)) (interior (B b)) := fun a ha b hb hab =>
    hd.disjoint_interior_balls h34 hXfin hXc hFX hFbd hFc hFdisj hB hBfr hpt ha hb hab
  have hfr : ∀ a ∈ K.vertices, ∀ b ∈ K.vertices, a ≠ b → y ∈ B a → y ∈ B b →
      y ∈ frontier (B a) := by
    intro a ha b hb hab hya hyb
    refine ⟨subset_closure hya, fun hyi => ?_⟩
    by_cases hybi : y ∈ interior (B b)
    · exact disjoint_left.mp (hdisj a ha b hb hab) hyi hybi
    · exact disjoint_left.mp (hmiss a ha b hb) hyi ⟨subset_closure hyb, hybi⟩
  have hyu := hfr u hu v hv huv hy.1 hy.2
  have hyv := hfr v hv u hu huv.symm hy.2 hy.1
  rw [hBfr u hu] at hyu
  rw [hBfr v hv] at hyv
  have hcase : ∀ a ∈ K.vertices, ∀ b ∈ K.vertices, ∀ e ∈ edgesAt K a,
      y ∈ F e → y ∈ (Cpp b ∩ frontier XK.space) ∪ ⋃ e ∈ edgesAt K b, F e → b ∈ e := by
    intro a ha b hb e he hyFe hyb
    rcases hyb with hyb | hyb
    · by_contra hbe
      have hyE : y ∈ F e ∩ frontier XK.space := ⟨hyFe, hyb.2⟩
      rw [hFbd e he.1 he.2.1] at hyE
      have : y ∈ Cpp b ∩ Ec e := ⟨hyb.1, hyE.1⟩
      rw [hd.handlePiece_inter_pseudoCell_eq_empty hb he.1 he.2.1 hbe] at this
      exact this
    · obtain ⟨e', he', hyFe'⟩ := mem_iUnion₂.mp hyb
      by_contra hbe
      have hne : e ≠ e' := fun h => hbe (h ▸ he'.2.2)
      exact disjoint_left.mp (hFdisj e he.1 he.2.1 e' he'.1 he'.2.1 hne) hyFe hyFe'
  rcases hyu with hyu | hyu
  · rcases hyv with hyv | hyv
    · obtain ⟨e, he, hce, hue, hve, hye⟩ := hd.exists_trace_of_mem_inter hu hv huv hyu hyv
      have hyF : y ∈ Ec e ∩ frontier XK.space := hye
      rw [← hFbd e he hce] at hyF
      exact ⟨e, he, hce, hue, hve, hyF.1⟩
    · obtain ⟨e, he, hyFe⟩ := mem_iUnion₂.mp hyv
      exact ⟨e, he.1, he.2.1, hcase v hv u hu e he hyFe (Or.inl hyu), he.2.2, hyFe⟩
  · obtain ⟨e, he, hyFe⟩ := mem_iUnion₂.mp hyu
    exact ⟨e, he.1, he.2.1, he.2.2, hcase u hu v hv e he hyFe hyv, hyFe⟩

theorem IsHandleDecompositionOfTube.mem_interior_iUnion_balls_of_mem_disk
    (hd : IsHandleDecompositionOfTube K N C D Dbd h N' Ec Eint Ebd Cpp)
    (h34 : HasSinglePolygonTraces K h Ec XK.space) (hXfin : XK.faces.Finite)
    (hXc : IsConnected XK.spaceᶜ) (hFX : ∀ e ∈ K.faces, e.card = 2 → F e ⊆ XK.space)
    (hFbd : ∀ e ∈ K.faces, e.card = 2 → F e ∩ frontier XK.space = Ec e ∩ frontier XK.space)
    (hFc : ∀ e ∈ K.faces, e.card = 2 → IsPreconnected (F e))
    (hFcl : ∀ e ∈ K.faces, e.card = 2 → IsClosed (F e))
    (hFdisj : ∀ e ∈ K.faces, e.card = 2 → ∀ e' ∈ K.faces, e'.card = 2 → e ≠ e' →
      Disjoint (F e) (F e'))
    (hB : ∀ v ∈ K.vertices, IsPLBall 3 (B v))
    (hBfr : ∀ v ∈ K.vertices,
      frontier (B v) = (Cpp v ∩ frontier XK.space) ∪ ⋃ e ∈ edgesAt K v, F e)
    (hpt : ∀ v ∈ K.vertices,
      ∃ y ∈ Cpp v ∩ frontier XK.space, ∀ e ∈ K.faces, e.card = 2 → y ∉ Ec e)
    {e : Finset E3} (he : e ∈ K.faces) (hc : e.card = 2) {z : E3} (hzF : z ∈ F e)
    (hzX : z ∉ frontier XK.space) : z ∈ interior (⋃ v ∈ K.vertices, B v) := by
  obtain ⟨a, hae, b, hbe, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < e.card)
  have ha : a ∈ K.vertices :=
    K.down_closed he (Finset.singleton_subset_iff.mpr hae) (Finset.singleton_nonempty a)
  have hb : b ∈ K.vertices :=
    K.down_closed he (Finset.singleton_subset_iff.mpr hbe) (Finset.singleton_nonempty b)
  have hEfin : {e' : Finset E3 | e' ∈ K.faces ∧ e'.card = 2 ∧ e' ≠ e}.Finite :=
    hd.tube.facesFinite.subset fun e' h => h.1
  have hTc : IsClosed (frontier XK.space ∪
      ⋃ e' ∈ {e' : Finset E3 | e' ∈ K.faces ∧ e'.card = 2 ∧ e' ≠ e}, F e') :=
    isClosed_frontier.union (hEfin.isClosed_biUnion fun e' h => hFcl e' h.1 h.2.1)
  have hzT : z ∉ frontier XK.space ∪
      ⋃ e' ∈ {e' : Finset E3 | e' ∈ K.faces ∧ e'.card = 2 ∧ e' ≠ e}, F e' := by
    rintro (h' | h')
    · exact hzX h'
    · obtain ⟨e', he', hze'⟩ := mem_iUnion₂.mp h'
      exact disjoint_left.mp (hFdisj e he hc e' he'.1 he'.2.1 (Ne.symm he'.2.2)) hzF hze'
  have hST : ∀ w ∈ K.vertices, frontier (B w) ⊆ (frontier XK.space ∪
      ⋃ e' ∈ {e' : Finset E3 | e' ∈ K.faces ∧ e'.card = 2 ∧ e' ≠ e}, F e') ∪ F e := by
    intro w hw
    rw [hBfr w hw]
    refine union_subset (fun y hy => Or.inl (Or.inl hy.2)) (iUnion₂_subset fun e' he' => ?_)
    by_cases h' : e' = e
    · rw [h']
      exact subset_union_right
    · exact fun y hy => Or.inl (Or.inr (mem_iUnion₂.mpr ⟨e', ⟨he'.1, he'.2.1, h'⟩, hy⟩))
  have hFS : ∀ w ∈ K.vertices, w ∈ e → F e ⊆ frontier (B w) := by
    intro w hw hwe
    rw [hBfr w hw]
    exact (subset_biUnion_of_mem (u := F) (show e ∈ edgesAt K w from ⟨he, hc, hwe⟩)).trans
      subset_union_right
  obtain ⟨Cn, hCn, hCT, A₀, B₀, hA₀, hB₀, hAB, -, -⟩ :=
    (hB a ha).isPLSphere_frontier.exists_connected_neighborhood_pair_sdiff_of_two
      (hFS a ha hae hzF) (hTc.isOpen_compl.mem_nhds hzT)
  have hiff : ∀ w ∈ K.vertices, w ∈ e → ∀ y ∈ Cn, (y ∈ frontier (B w) ↔ y ∈ F e) := by
    intro w hw hwe y hyC
    refine ⟨fun hy => ?_, fun hy => hFS w hw hwe hy⟩
    rcases hST w hw hy with hyT | hyF
    · exact absurd hyT (hCT hyC)
    · exact hyF
  have hsd : ∀ w ∈ K.vertices, w ∈ e → Cn \ frontier (B w) = A₀ ∪ B₀ := by
    intro w hw hwe
    rw [hAB]
    ext y
    constructor
    · rintro ⟨hyC, hyn⟩
      exact ⟨hyC, fun h' => hyn ((hiff w hw hwe y hyC).mpr ((hiff a ha hae y hyC).mp h'))⟩
    · rintro ⟨hyC, hyn⟩
      exact ⟨hyC, fun h' => hyn ((hiff a ha hae y hyC).mpr ((hiff w hw hwe y hyC).mp h'))⟩
  have hZsub : ∀ w ∈ K.vertices, w ∈ e → ∀ Z : Set E3, IsPreconnected Z → Z ⊆ A₀ ∪ B₀ →
      (Z ∩ interior (B w)).Nonempty → Z ⊆ interior (B w) := by
    intro w hw hwe Z hZ hZs hne
    rw [← hsd w hw hwe] at hZs
    exact subset_interior_of_isPreconnected_of_disjoint_frontier hZ
      (disjoint_left.mpr fun y hy hyf => (hZs hy).2 hyf) hne
  have hmeet : ∀ w ∈ K.vertices, w ∈ e →
      (A₀ ∩ interior (B w)).Nonempty ∨ (B₀ ∩ interior (B w)).Nonempty := by
    intro w hw hwe
    have hzB : z ∈ closure (interior (B w)) := by
      rw [(hB w hw).closure_interior]
      exact (hB w hw).isPolyhedron.isClosed.frontier_subset (hFS w hw hwe hzF)
    obtain ⟨y, hyC, hyI⟩ := mem_closure_iff_nhds.mp hzB Cn hCn
    have hy' : y ∈ Cn \ frontier (B w) :=
      ⟨hyC, fun hf => disjoint_left.mp disjoint_interior_frontier hyI hf⟩
    rw [hsd w hw hwe] at hy'
    rcases hy' with hyA | hyB
    · exact Or.inl ⟨y, hyA, hyI⟩
    · exact Or.inr ⟨y, hyB, hyI⟩
  have hdisj :=
    hd.disjoint_interior_balls h34 hXfin hXc hFX hFbd hFc hFdisj hB hBfr hpt ha hb hab
  have hcov : A₀ ∪ B₀ ⊆ interior (B a) ∪ interior (B b) := by
    rcases hmeet a ha hae with hAa | hBa
    · have hAa' := hZsub a ha hae A₀ hA₀.isPreconnected subset_union_left hAa
      rcases hmeet b hb hbe with hAb | hBb
      · exfalso
        have hAb' := hZsub b hb hbe A₀ hA₀.isPreconnected subset_union_left hAb
        obtain ⟨y, hy⟩ := hA₀.nonempty
        exact disjoint_left.mp hdisj (hAa' hy) (hAb' hy)
      · have hBb' := hZsub b hb hbe B₀ hB₀.isPreconnected subset_union_right hBb
        exact union_subset (hAa'.trans subset_union_left) (hBb'.trans subset_union_right)
    · have hBa' := hZsub a ha hae B₀ hB₀.isPreconnected subset_union_right hBa
      rcases hmeet b hb hbe with hAb | hBb
      · have hAb' := hZsub b hb hbe A₀ hA₀.isPreconnected subset_union_left hAb
        exact union_subset (hAb'.trans subset_union_right) (hBa'.trans subset_union_left)
      · exfalso
        have hBb' := hZsub b hb hbe B₀ hB₀.isPreconnected subset_union_right hBb
        obtain ⟨y, hy⟩ := hB₀.nonempty
        exact disjoint_left.mp hdisj (hBa' hy) (hBb' hy)
  have hCsub : Cn ⊆ ⋃ v ∈ K.vertices, B v := by
    intro y hyC
    by_cases hyF : y ∈ F e
    · exact mem_iUnion₂.mpr
        ⟨a, ha, (hB a ha).isPolyhedron.isClosed.frontier_subset (hFS a ha hae hyF)⟩
    · have hy : y ∈ A₀ ∪ B₀ := by
        rw [← hsd a ha hae]
        exact ⟨hyC, fun hf => hyF ((hiff a ha hae y hyC).mp hf)⟩
      rcases hcov hy with h' | h'
      · exact mem_iUnion₂.mpr ⟨a, ha, interior_subset h'⟩
      · exact mem_iUnion₂.mpr ⟨b, hb, interior_subset h'⟩
  exact mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset hCn hCsub)

theorem IsHandleDecompositionOfTube.iUnion_balls_eq
    (hd : IsHandleDecompositionOfTube K N C D Dbd h N' Ec Eint Ebd Cpp)
    (h2 : IsPolyhedralTubeNeighborhood K h N' Ec Eint Ebd XK)
    (h34 : HasSinglePolygonTraces K h Ec XK.space) (hXc : IsConnected XK.spaceᶜ)
    (hXint : IsConnected (interior XK.space))
    (hFX : ∀ e ∈ K.faces, e.card = 2 → F e ⊆ XK.space)
    (hFbd : ∀ e ∈ K.faces, e.card = 2 → F e ∩ frontier XK.space = Ec e ∩ frontier XK.space)
    (hFc : ∀ e ∈ K.faces, e.card = 2 → IsPreconnected (F e))
    (hFcl : ∀ e ∈ K.faces, e.card = 2 → IsClosed (F e))
    (hFdisj : ∀ e ∈ K.faces, e.card = 2 → ∀ e' ∈ K.faces, e'.card = 2 → e ≠ e' →
      Disjoint (F e) (F e'))
    (hB : ∀ v ∈ K.vertices, IsPLBall 3 (B v))
    (hBfr : ∀ v ∈ K.vertices,
      frontier (B v) = (Cpp v ∩ frontier XK.space) ∪ ⋃ e ∈ edgesAt K v, F e)
    (hpt : ∀ v ∈ K.vertices,
      ∃ y ∈ Cpp v ∩ frontier XK.space, ∀ e ∈ K.faces, e.card = 2 → y ∉ Ec e) :
    ⋃ v ∈ K.vertices, B v = XK.space := by
  have hXfin := h2.facesFinite
  have hA := fun w (hw : w ∈ K.vertices) =>
    hd.ball_subset_and_disjoint_interior h34 hXfin hXc hFX hFbd hFc hFdisj hw (hB w hw)
      (hBfr w hw)
  refine Subset.antisymm (iUnion₂_subset fun v hv => (hA v hv).1) ?_
  have hYc : IsClosed (⋃ v ∈ K.vertices, B v) :=
    hd.tube.finite_vertices.isClosed_biUnion fun v hv => (hB v hv).isPolyhedron.isClosed
  obtain ⟨e₁, he₁, he₁c⟩ := hd.tube.hasEdge
  obtain ⟨v₀, hv₀e⟩ := Finset.card_pos.mp (by omega : 0 < e₁.card)
  have hv₀ : v₀ ∈ K.vertices :=
    K.down_closed he₁ (Finset.singleton_subset_iff.mpr hv₀e) (Finset.singleton_nonempty v₀)
  have hint : interior XK.space ⊆ interior (⋃ v ∈ K.vertices, B v) := by
    apply hXint.isPreconnected.subset_of_closure_inter_subset isOpen_interior
    · obtain ⟨z, hz⟩ := (hB v₀ hv₀).interior_nonempty
      exact ⟨z, interior_mono (hA v₀ hv₀).1 hz,
        interior_mono (subset_biUnion_of_mem (u := B) hv₀) hz⟩
    · rintro z ⟨hzc, hzX⟩
      have hzY : z ∈ ⋃ v ∈ K.vertices, B v :=
        hYc.closure_subset (closure_mono interior_subset hzc)
      obtain ⟨w, hw, hzw⟩ := mem_iUnion₂.mp hzY
      by_cases hzi : z ∈ interior (B w)
      · exact interior_mono (subset_biUnion_of_mem (u := B) hw) hzi
      · have hzfr : z ∈ frontier (B w) := ⟨subset_closure hzw, hzi⟩
        rw [hBfr w hw] at hzfr
        have hzX' : z ∉ frontier XK.space := fun h' => h'.2 hzX
        rcases hzfr with h' | h'
        · exact absurd h'.2 hzX'
        · obtain ⟨e, he, hzF⟩ := mem_iUnion₂.mp h'
          exact hd.mem_interior_iUnion_balls_of_mem_disk h34 hXfin hXc hFX hFbd hFc hFcl hFdisj
            hB hBfr hpt he.1 he.2.1 hzF hzX'
  intro z hzX
  by_cases hzi : z ∈ interior XK.space
  · exact interior_subset (hint hzi)
  · have hzfr : z ∈ frontier XK.space := ⟨subset_closure hzX, hzi⟩
    have hzN : z ∈ N' := interior_subset (h2.subsetInterior hzX)
    rw [hd.coversTube] at hzN
    obtain ⟨v, hv, hzv⟩ := mem_iUnion₂.mp hzN
    have hzv' : z ∈ frontier (B v) := by
      rw [hBfr v hv]
      exact Or.inl ⟨hzv, hzfr⟩
    exact mem_iUnion₂.mpr ⟨v, hv, (hB v hv).isPolyhedron.isClosed.frontier_subset hzv'⟩

end DifferentialGeometry.Topology.PiecewiseLinear
