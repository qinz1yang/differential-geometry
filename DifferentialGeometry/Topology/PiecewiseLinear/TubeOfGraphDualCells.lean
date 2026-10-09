/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BallReplacement
import DifferentialGeometry.Topology.PiecewiseLinear.HandleDecompositionOfEdgeCollars
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BranchDeletion
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexBall
import DifferentialGeometry.Topology.PiecewiseLinear.SphericalDiskComplement
import DifferentialGeometry.Topology.PiecewiseLinear.SplittingDiskRim

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

section SphereDisks

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsPLSphere.isConnected_sdiff_iUnion_of_isPLBall_two {ι : Type*} [Finite ι] {S : Set E}
    {D : ι → Set E} (hS : IsPLSphere 2 S) (hD : ∀ i, IsPLBall 2 (D i)) (hDS : ∀ i, D i ⊆ S)
    (hdisj : Pairwise fun i j => Disjoint (D i) (D j)) : IsConnected (S \ ⋃ i, D i) := by
  have hDc : ∀ i, IsClosed (D i) := fun i => (hD i).isPolyhedron.isClosed
  refine ⟨?_, ?_⟩
  · by_contra hne
    rw [not_nonempty_iff_eq_empty, Set.sdiff_eq_empty] at hne
    obtain ⟨j, hj⟩ := subset_of_isPreconnected_of_iUnion_isClosed hDc hdisj
      hS.isConnected.isPreconnected hS.nonempty hne
    exact (hS.isConnected_sdiff_of_isPLBall_two (hD j) (hDS j)).nonempty.ne_empty
      (Set.sdiff_eq_empty.mpr hj)
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨i₀⟩⟩
  · rw [iUnion_of_empty, Set.sdiff_empty]
    exact hS.isConnected.isPreconnected
  have hB : IsPLBall 2 (closure (S \ D i₀)) := hS.isPLBall_closure_sdiff (hD i₀) (hDS i₀)
  have hBS : closure (S \ D i₀) ⊆ S := closure_minimal Set.sdiff_subset hS.isPolyhedron.isClosed
  have hSB : S ⊆ closure (S \ D i₀) ∪ D i₀ := fun x hx => by
    by_cases hxD : x ∈ D i₀
    · exact Or.inr hxD
    · exact Or.inl (subset_closure ⟨hx, hxD⟩)
  have hrim : IsPreconnected (closure (S \ D i₀) ∩ D i₀) := by
    obtain ⟨q, hq⟩ := hB
    rw [← hS.image_stdSimplexBoundary_complement (hD i₀) (hDS i₀) hq]
    exact (isConnected_stdSimplexBoundary 0).isPreconnected.image q
      (hq.isPiecewiseAffineOn.continuousOn.mono fun _ hx => hx.1)
  let _ : SimplyConnectedSpace (closure (S \ D i₀)) := hB.simplyConnectedSpace
  let _ : LocallyPathConnectedSpace (closure (S \ D i₀)) := hB.locallyPathConnectedSpace
  have himg : ∀ T : Set E, ((↑) : closure (S \ D i₀) → E) ''
      (((↑) : closure (S \ D i₀) → E) ⁻¹' T)ᶜ = closure (S \ D i₀) \ T := by
    intro T
    rw [← preimage_compl, Subtype.image_preimage_coe, ← Set.sdiff_eq]
  have hc : ∀ i, IsPreconnected (((↑) : closure (S \ D i₀) → E) ⁻¹' D i)ᶜ := by
    intro i
    rw [← IsInducing.subtypeVal.isPreconnected_image, himg]
    by_cases hi : i = i₀
    · subst hi
      have heq : closure (S \ D i) \ D i = S \ D i := by
        ext x
        exact ⟨fun hx => ⟨hBS hx.1, hx.2⟩, fun hx => ⟨subset_closure hx, hx.2⟩⟩
      rw [heq]
      exact (hS.isConnected_sdiff_of_isPLBall_two (hD i) (hDS i)).isPreconnected
    · have hY : IsPreconnected (S \ D i) :=
        (hS.isConnected_sdiff_of_isPLBall_two (hD i) (hDS i)).isPreconnected
      let _ : PreconnectedSpace ↥(S \ D i) := Subtype.preconnectedSpace hY
      have huniv : ((↑) : (S \ D i : Set E) → E) ⁻¹' closure (S \ D i₀) ∪
          ((↑) : (S \ D i : Set E) → E) ⁻¹' D i₀ = univ :=
        eq_univ_of_forall fun y => hSB y.2.1
      have hinter : IsPreconnected (((↑) : (S \ D i : Set E) → E) ⁻¹' closure (S \ D i₀) ∩
          ((↑) : (S \ D i : Set E) → E) ⁻¹' D i₀) := by
        have hsub : closure (S \ D i₀) ∩ D i₀ ⊆ S \ D i := fun x hx =>
          ⟨hBS hx.1, fun hxi => disjoint_left.mp (hdisj hi) hxi hx.2⟩
        rw [← preimage_inter, ← IsInducing.subtypeVal.isPreconnected_image,
          Subtype.image_preimage_coe, inter_eq_right.mpr hsub]
        exact hrim
      have hA : IsPreconnected (((↑) : (S \ D i : Set E) → E) ⁻¹' closure (S \ D i₀)) :=
        isPreconnected_left_of_isClosed_union (isClosed_closure.preimage continuous_subtype_val)
          ((hDc i₀).preimage continuous_subtype_val) (by rw [huniv]; exact isPreconnected_univ)
          hinter
      rw [← IsInducing.subtypeVal.isPreconnected_image, Subtype.image_preimage_coe] at hA
      convert hA using 1
      ext x
      exact ⟨fun hx => ⟨⟨hBS hx.1, hx.2⟩, hx.1⟩, fun hx => ⟨hx.2, hx.1.2⟩⟩
  have hmain := isPreconnected_compl_iUnion_of_isPreconnected_compl
    (fun i => (hDc i).preimage continuous_subtype_val) (fun i j hij => (hdisj hij).preimage _) hc
  rw [← preimage_iUnion, ← IsInducing.subtypeVal.isPreconnected_image, himg] at hmain
  convert hmain using 1
  ext x
  constructor
  · rintro ⟨hxS, hxU⟩
    exact ⟨subset_closure ⟨hxS, fun h => hxU (mem_iUnion.mpr ⟨i₀, h⟩)⟩, hxU⟩
  · rintro ⟨hxB, hxU⟩
    exact ⟨hBS hxB, hxU⟩

end SphereDisks

local notation "E3" => EuclideanSpace ℝ (Fin 3)

section Tube

open Classical in
theorem isTube_graphDualCell {A K : Geometry.SimplicialComplex ℝ E3} (hAfin : A.faces.Finite)
    (hA : IsCombinatorialManifoldWithBoundary 3 A) (hKA : K.faces ⊆ A.faces)
    (hcard : ∀ s ∈ K.faces, s.card ≤ 2) (hedge : ∃ e ∈ K.faces, e.card = 2)
    (hint : ∀ v ∈ K.vertices, v ∈ interior A.space) :
    IsTube K (⋃ v ∈ K.vertices, (graphDualCell A K v).space)
      (fun v => (graphDualCell A K v).space)
      (fun e => if he : e ∈ A.faces then (splittingDisk A e he).space else ∅)
      (fun e => (if he : e ∈ A.faces then (splittingDisk A e he).space else ∅) ∩
        frontier (⋃ v ∈ K.vertices, (graphDualCell A K v).space))
      id (⋃ v ∈ K.vertices, (graphDualCell A K v).space) := by
  let _ : Finite A.faces := hAfin.to_subtype
  have hn : Module.finrank ℝ E3 = 2 + 1 := finrank_euclideanSpace_fin
  have hDe : ∀ e (he : e ∈ A.faces),
      (if he : e ∈ A.faces then (splittingDisk A e he).space else ∅) =
        (splittingDisk A e he).space := fun e he => dite_eq_left he
  have hball : ∀ v ∈ K.vertices, IsPLBall 3 (graphDualCell A K v).space :=
    fun v hv => hA.isPLBall_graphDualCell A K hKA hcard hv
  have hclosed : ∀ v ∈ K.vertices, IsClosed (graphDualCell A K v).space :=
    fun v hv => (hball v hv).isPolyhedron.isClosed
  have hfinV : K.vertices.Finite :=
    Set.Finite.preimage Finset.singleton_injective.injOn (hAfin.subset hKA)
  have hCN : ∀ v ∈ K.vertices,
      (graphDualCell A K v).space ⊆ ⋃ w ∈ K.vertices, (graphDualCell A K w).space :=
    fun v hv => subset_biUnion_of_mem (u := fun w => (graphDualCell A K w).space) hv
  have hinter : ∀ e ∈ K.faces, ∀ u ∈ e, ∀ w ∈ e, u ≠ w →
      (graphDualCell A K u).space ∩ (graphDualCell A K w).space =
        if he : e ∈ A.faces then (splittingDisk A e he).space else ∅ := by
    intro e he u hu w hw huw
    rw [hDe e (hKA he)]
    exact graphDualCell_space_inter_of_mem A K hKA hcard he hu hw huw
  have hdisk : ∀ e ∈ K.faces, e.card = 2 → ∃ r : (Fin 3 → ℝ) → E3,
      IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3))
        (if he : e ∈ A.faces then (splittingDisk A e he).space else ∅) ∧
      (if he : e ∈ A.faces then (splittingDisk A e he).space else ∅) ∩
          frontier (⋃ v ∈ K.vertices, (graphDualCell A K v).space) =
        r '' stdSimplexBoundary 2 := by
    intro e he hc
    rw [hDe e (hKA he)]
    exact hA.exists_isPLHomeomorphOn_splittingDisk_inter_frontier (k := 1) hn hKA hint he hc
      (by norm_num) fun s hs => (hcard s hs).trans hc.ge
  refine ⟨hAfin.subset hKA, hcard, hedge,
    subset_interior_iff_mem_nhdsSet.mp (hA.space_subset_interior_iUnion_graphDualCell hn hKA hint),
    ⟨A, hAfin, hA, hKA, fun v _ => rfl, fun e _ _ he => hDe e he⟩, hball, hdisk, rfl,
    fun e _ _ => rfl, ?_, ?_, IsEmbedding.subtypeVal, (image_id _).symm⟩
  · intro u hu v hv huv he
    have huv' := hinter _ he u (Finset.mem_insert_self u {v}) v
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self v)) huv
    have huCv : u ∉ (graphDualCell A K v).space := fun h =>
      huv ((mem_graphDualCell_space_iff_of_singleton_mem A K hKA hv hu).mp h)
    have hvCu : v ∉ (graphDualCell A K u).space := fun h =>
      huv ((mem_graphDualCell_space_iff_of_singleton_mem A K hKA hu hv).mp h).symm
    refine ⟨{p | (p : E3) ∉ (graphDualCell A K v).space},
      {p | (p : E3) ∉ (graphDualCell A K u).space},
      (hclosed v hv).isOpen_compl.preimage continuous_subtype_val,
      (hclosed u hu).isOpen_compl.preimage continuous_subtype_val, ?_, ?_, ?_, ?_⟩
    · rw [Set.disjoint_left]
      intro p hp1 hp2
      rcases interior_subset p.2 with h | h
      · exact hp2 h
      · exact hp1 h
    · ext p
      have hpN : (p : E3) ∉ frontier (⋃ w ∈ K.vertices, (graphDualCell A K w).space) :=
        fun hfr => hfr.2 (interior_mono (union_subset (hCN u hu) (hCN v hv)) p.2)
      constructor
      · intro hUV hpX
        obtain ⟨hpD, -⟩ := hpX
        have hp : (p : E3) ∈ (graphDualCell A K u).space ∩ (graphDualCell A K v).space := by
          rw [huv']
          exact hpD
        rcases hUV with h | h
        · exact h hp.2
        · exact h hp.1
      · intro hp
        by_contra hcon
        apply hp
        have hpu : (p : E3) ∈ (graphDualCell A K u).space := by
          by_contra h
          exact hcon (Or.inr h)
        have hpv : (p : E3) ∈ (graphDualCell A K v).space := by
          by_contra h
          exact hcon (Or.inl h)
        have hpD : (p : E3) ∈ if he : ({u, v} : Finset E3) ∈ A.faces then
            (splittingDisk A {u, v} he).space else ∅ := by
          rw [← huv']
          exact ⟨hpu, hpv⟩
        exact ⟨hpD, fun h => hpN h.2⟩
    · intro p hp
      have hpu : (p : E3) = u := hp
      change (p : E3) ∉ (graphDualCell A K v).space
      rw [hpu]
      exact huCv
    · intro p hp
      have hpv : (p : E3) = v := hp
      change (p : E3) ∉ (graphDualCell A K u).space
      rw [hpv]
      exact hvCu
  · intro v hv
    have hS : IsPLSphere 2 (frontier (graphDualCell A K v).space) := by
      obtain ⟨f, hf⟩ := hball v hv
      rw [← IsPLHomeomorphOn.image_stdSimplexBoundary_eq_frontier (n := 2) hf]
      exact hf.isPLSphere_image_stdSimplexBoundary
    have hsub : ∀ e ∈ K.faces, e.card = 2 → v ∈ e →
        (if he : e ∈ A.faces then (splittingDisk A e he).space else ∅) ⊆
          frontier (graphDualCell A K v).space := by
      intro e he hc hve
      obtain ⟨w, hwe, hwv⟩ := Finset.exists_mem_ne (by omega : 1 < e.card) v
      have hw : w ∈ K.vertices :=
        K.down_closed he (Finset.singleton_subset_iff.mpr hwe) (Finset.singleton_nonempty w)
      obtain ⟨r, hr, -⟩ := hdisk e he hc
      rw [← hinter e he v hve w hwe (Ne.symm hwv)] at hr ⊢
      exact IsPLBall.inter_subset_frontier_of_isPLBall (n := 2) (hball w hw) ⟨r, hr⟩
        (by norm_num)
    have hEfin : {e : Finset E3 | e ∈ K.faces ∧ e.card = 2 ∧ v ∈ e}.Finite :=
      (hAfin.subset hKA).subset fun e he => he.1
    let _ : Finite {e : Finset E3 | e ∈ K.faces ∧ e.card = 2 ∧ v ∈ e} := hEfin.to_subtype
    have hset : (frontier (graphDualCell A K v).space ∩
          frontier (⋃ w ∈ K.vertices, (graphDualCell A K w).space)) \
        ⋃ e ∈ {e : Finset E3 | e ∈ K.faces ∧ e.card = 2 ∧ v ∈ e},
          ((if he : e ∈ A.faces then (splittingDisk A e he).space else ∅) ∩
            frontier (⋃ w ∈ K.vertices, (graphDualCell A K w).space)) =
        frontier (graphDualCell A K v).space \
          ⋃ e : {e : Finset E3 | e ∈ K.faces ∧ e.card = 2 ∧ v ∈ e},
            if he : e.1 ∈ A.faces then (splittingDisk A e.1 he).space else ∅ := by
      ext x
      constructor
      · rintro ⟨⟨hxC, hxN⟩, hxU⟩
        refine ⟨hxC, fun hx => hxU ?_⟩
        obtain ⟨e, hxe⟩ := mem_iUnion.mp hx
        exact mem_iUnion₂.mpr ⟨e.1, e.2, hxe, hxN⟩
      · rintro ⟨hxC, hxU⟩
        refine ⟨⟨hxC, ?_⟩, fun hx => ?_⟩
        · have hxCv : x ∈ (graphDualCell A K v).space := (hclosed v hv).frontier_subset hxC
          refine ⟨subset_closure (hCN v hv hxCv), fun hxint => ?_⟩
          have hFc : IsClosed (⋃ w ∈ K.vertices \ {v}, (graphDualCell A K w).space) :=
            (hfinV.subset Set.sdiff_subset).isClosed_biUnion fun w hw => hclosed w hw.1
          by_cases hxF : x ∈ ⋃ w ∈ K.vertices \ {v}, (graphDualCell A K w).space
          · obtain ⟨w, ⟨hw, hwv⟩, hxw⟩ := mem_iUnion₂.mp hxF
            have hwv' : w ≠ v := hwv
            by_cases hadj : ∃ e ∈ K.faces, v ∈ e ∧ w ∈ e
            · obtain ⟨e, he, hve, hwe⟩ := hadj
              have hc : e.card = 2 := le_antisymm (hcard e he)
                (Finset.one_lt_card.mpr ⟨v, hve, w, hwe, hwv'.symm⟩)
              apply hxU
              refine mem_iUnion.mpr ⟨⟨e, he, hc, hve⟩, ?_⟩
              rw [← hinter e he v hve w hwe hwv'.symm]
              exact ⟨hxCv, hxw⟩
            · have hempty := graphDualCell_space_inter_eq_empty A K hKA hcard hv hw hwv'.symm
                fun h => hadj ⟨{v, w}, classical_insert_singleton_eq_pair v w ▸ h,
                  Finset.mem_insert_self v {w},
                  Finset.mem_insert_of_mem (Finset.mem_singleton_self w)⟩
              have hmem : x ∈ (graphDualCell A K v).space ∩ (graphDualCell A K w).space :=
                ⟨hxCv, hxw⟩
              rw [hempty] at hmem
              exact hmem
          · apply hxC.2
            refine mem_interior.mpr ⟨interior (⋃ w ∈ K.vertices, (graphDualCell A K w).space) ∩
              (⋃ w ∈ K.vertices \ {v}, (graphDualCell A K w).space)ᶜ, ?_,
              isOpen_interior.inter hFc.isOpen_compl, hxint, hxF⟩
            rintro y ⟨hyN, hyF⟩
            obtain ⟨w, hw, hyw⟩ := mem_iUnion₂.mp (interior_subset hyN)
            by_cases hwv : w = v
            · exact hwv ▸ hyw
            · exact absurd (mem_iUnion₂.mpr ⟨w, ⟨hw, hwv⟩, hyw⟩) hyF
        · obtain ⟨e, he, hxe, -⟩ := mem_iUnion₂.mp hx
          exact hxU (mem_iUnion.mpr ⟨⟨e, he⟩, hxe⟩)
    have hconn := hS.isConnected_sdiff_iUnion_of_isPLBall_two
      (D := fun e : {e : Finset E3 | e ∈ K.faces ∧ e.card = 2 ∧ v ∈ e} =>
        if he : e.1 ∈ A.faces then (splittingDisk A e.1 he).space else ∅)
      (fun i => by
        obtain ⟨r, hr, -⟩ := hdisk i.1 i.2.1 i.2.2.1
        exact ⟨r, hr⟩)
      (fun i => hsub i.1 i.2.1 i.2.2.1 i.2.2.2)
      (fun i j hij => by
        dsimp only
        rw [hDe _ (hKA i.2.1), hDe _ (hKA j.2.1)]
        exact disjoint_splittingDisk_space A (hKA i.2.1) (hKA j.2.1)
          (fun h => hij (Subtype.ext h)) (by rw [i.2.2.1, j.2.2.1]))
    rw [← hset] at hconn
    exact hconn

theorem IsTube.of_isEmbedding {K : Geometry.SimplicialComplex ℝ E3} {N N₀ : Set E3}
    {C : E3 → Set E3} {D Dbd : Finset E3 → Set E3} {h₀ h : E3 → E3}
    (ht : IsTube K N C D Dbd h₀ N₀) (hh : IsEmbedding (N.domRestrict h)) :
    IsTube K N C D Dbd h (h '' N) :=
  { ht with isEmbedding := hh, imageEq := rfl }

theorem exists_isTube : ∃ (K : Geometry.SimplicialComplex ℝ E3) (N : Set E3)
    (C : E3 → Set E3) (D Dbd : Finset E3 → Set E3) (h : E3 → E3) (N' : Set E3),
    IsTube K N C D Dbd h N' := by
  obtain ⟨T, hT, hTcard, -, -, -⟩ := exists_affineIndependent_openSimplex_subset (n := 2)
    finrank_euclideanSpace_fin (0 : E3) Filter.univ_mem
  let _ : Finite (simplexComplex T hT).faces := (simplexComplex_faces_finite T hT).to_subtype
  obtain ⟨a, ha⟩ : T.Nonempty := Finset.card_pos.mp (by omega)
  have hAfin :
      (barycentricSubdivision (barycentricSubdivision (simplexComplex T hT))).faces.Finite :=
    Set.toFinite _
  set A := barycentricSubdivision (barycentricSubdivision (simplexComplex T hT)) with hAdef
  let _ : Finite A.faces := hAfin.to_subtype
  have hAsp : A.space = convexHull ℝ (T : Set E3) := by
    rw [hAdef, (barycentricSubdivision_isSubdivision _).space_eq,
      (barycentricSubdivision_isSubdivision _).space_eq, simplexComplex_space T hT ⟨a, ha⟩]
  have hA : IsCombinatorialManifoldWithBoundary 3 A := by
    apply IsPLBall.isCombinatorialManifoldWithBoundary (n := 2)
    rw [hAsp]
    exact isPLBall_convexHull_of_affineIndependent T hT (by omega)
  set t := T.erase a with htdef
  have htT : t ⊆ T := Finset.erase_subset a T
  have htcard : t.card = 3 := by
    rw [htdef, Finset.card_erase_of_mem ha, hTcard]
  have htne : t.Nonempty := Finset.card_pos.mp (by omega)
  have htneT : t ≠ T := fun h => by
    have hc := congrArg Finset.card h
    omega
  have hTf : T ∈ (simplexComplex T hT).faces := ⟨⟨a, ha⟩, Finset.Subset.refl T⟩
  have htf : t ∈ (simplexComplex T hT).faces := ⟨htne, htT⟩
  have hflag₁ : IsFlag (simplexComplex T hT) {T} := by
    refine ⟨fun s hs => ?_, fun s hs r hr => ?_⟩
    · rw [Finset.mem_singleton.mp hs]
      exact hTf
    · rw [Finset.mem_singleton.mp hs, Finset.mem_singleton.mp hr]
      exact Or.inl subset_rfl
  have hflag₂ : IsFlag (simplexComplex T hT) {t, T} := by
    refine ⟨fun s hs => ?_, fun s hs r hr => ?_⟩
    · rcases Finset.mem_insert.mp hs with rfl | hs
      · exact htf
      · rw [Finset.mem_singleton.mp hs]
        exact hTf
    · have hsT : s ⊆ T := by
        rcases Finset.mem_insert.mp hs with rfl | hs
        · exact htT
        · rw [Finset.mem_singleton.mp hs]
      rcases Finset.mem_insert.mp hr with rfl | hr
      · rcases Finset.mem_insert.mp hs with rfl | hs
        · exact Or.inl subset_rfl
        · rw [Finset.mem_singleton.mp hs]
          exact Or.inr htT
      · rw [Finset.mem_singleton.mp hr]
        exact Or.inl hsT
  set σ₁ : Finset E3 := ({T} : Finset (Finset E3)).image fun s => s.centroid ℝ id with hσ₁def
  set σ₂ : Finset E3 := ({t, T} : Finset (Finset E3)).image fun s => s.centroid ℝ id
    with hσ₂def
  have hσ₁ : σ₁ ∈ (barycentricSubdivision (simplexComplex T hT)).faces :=
    ⟨{T}, hflag₁, Finset.singleton_nonempty _, rfl⟩
  have hσ₂ : σ₂ ∈ (barycentricSubdivision (simplexComplex T hT)).faces :=
    ⟨{t, T}, hflag₂, Finset.insert_nonempty _ _, rfl⟩
  have hσ₁₂ : σ₁ ⊆ σ₂ := Finset.image_subset_image
    (Finset.singleton_subset_iff.mpr (Finset.mem_insert_of_mem (Finset.mem_singleton_self T)))
  have hσne : σ₁ ≠ σ₂ := by
    intro h
    have hmem : t.centroid ℝ id ∈ σ₁ := by
      rw [h, hσ₂def]
      exact Finset.mem_image_of_mem _ (Finset.mem_insert_self t {T})
    rw [hσ₁def, Finset.image_singleton, Finset.mem_singleton] at hmem
    exact htneT (injOn_faces_of_mem_openSimplex _
      (centroid_mem_openSimplex_of_mem_faces (simplexComplex T hT)) htf hTf hmem)
  have hflag : IsFlag (barycentricSubdivision (simplexComplex T hT)) {σ₁, σ₂} := by
    refine ⟨fun s hs => ?_, fun s hs r hr => ?_⟩
    · rcases Finset.mem_insert.mp hs with rfl | hs
      · exact hσ₁
      · rw [Finset.mem_singleton.mp hs]
        exact hσ₂
    · have hsσ : s ⊆ σ₂ := by
        rcases Finset.mem_insert.mp hs with rfl | hs
        · exact hσ₁₂
        · rw [Finset.mem_singleton.mp hs]
      rcases Finset.mem_insert.mp hr with rfl | hr
      · rcases Finset.mem_insert.mp hs with rfl | hs
        · exact Or.inl subset_rfl
        · rw [Finset.mem_singleton.mp hs]
          exact Or.inr hσ₁₂
      · rw [Finset.mem_singleton.mp hr]
        exact Or.inl hsσ
  set u : Finset E3 := ({σ₁, σ₂} : Finset (Finset E3)).image fun s => s.centroid ℝ id
    with hudef
  have huA : u ∈ A.faces := ⟨{σ₁, σ₂}, hflag, Finset.insert_nonempty _ _, rfl⟩
  have hucard : u.card = 2 := by
    rw [hudef, Finset.card_image_of_injOn (hflag.injOn _
      (centroid_mem_openSimplex_of_mem_faces _)), Finset.card_pair hσne]
  have hKu : ∀ s ∈ (subcomplexGeneratedBy A {u}).faces, s ⊆ u := by
    rintro s ⟨r, ⟨-, hr⟩, hsr, -⟩
    rw [mem_singleton_iff.mp hr] at hsr
    exact hsr
  have huK : u ∈ (subcomplexGeneratedBy A {u}).faces :=
    ⟨u, ⟨huA, rfl⟩, subset_rfl, Finset.card_pos.mp (by omega)⟩
  have hopen : ∀ d : Finset (Finset E3), IsFlag (simplexComplex T hT) d → T ∈ d →
      (d.image fun s => s.centroid ℝ id).centroid ℝ id ∈ openSimplex T := fun d hd hTd =>
    mem_openSimplex_top (simplexComplex T hT)
      (centroid_mem_openSimplex_of_mem_faces (simplexComplex T hT)) hd hTd
      (fun s hs => (hd.mem_faces hs).2)
      (centroid_mem_openSimplex ⟨_, Finset.mem_image_of_mem _ hTd⟩)
  have hint : ∀ v ∈ (subcomplexGeneratedBy A {u}).vertices, v ∈ interior A.space := by
    intro v hv
    have hvu : v ∈ u := Finset.singleton_subset_iff.mp (hKu _ hv)
    rw [hAsp, interior_convexHull_eq_openSimplex hT
      (by rw [finrank_euclideanSpace_fin, hTcard])]
    rw [hudef] at hvu
    obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp hvu
    rcases Finset.mem_insert.mp hσ with rfl | hσ
    · exact hopen {T} hflag₁ (Finset.mem_singleton_self T)
    · rw [Finset.mem_singleton.mp hσ]
      exact hopen {t, T} hflag₂ (Finset.mem_insert_of_mem (Finset.mem_singleton_self T))
  exact ⟨_, _, _, _, _, _, _, isTube_graphDualCell hAfin hA
    (subcomplexGeneratedBy_faces_subset A {u})
    (fun s hs => (Finset.card_le_card (hKu s hs)).trans hucard.le) ⟨u, huK, hucard⟩ hint⟩

end Tube

end DifferentialGeometry.Topology.PiecewiseLinear
