/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34GraphMarkedPoints
import DifferentialGeometry.Topology.PiecewiseLinear.CircleClosedCover
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldRelativeTopology
import DifferentialGeometry.Topology.PiecewiseLinear.GraphDualCellRestrictionE

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem exists_isPLHomeomorphOn_graphDualCell_inter_boundary_residual
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsPLBall 2 K.space)
    {v : E} (hv : {v} ∈ (boundaryComplex 2 K).faces) :
    ∃ γ : ℝ → E, IsPLHomeomorphOn γ (Icc 0 1)
      ((graphDualCell K (boundaryComplex 2 K) v).space ∩
        closure (K.space \ (derivedNeighborhood K (boundaryComplex 2 K)).space)) ∧
      {γ 0, γ 1} = ⋃ e : {e : Finset E //
          e ∈ (boundaryComplex 2 K).faces ∧ e.card = 2 ∧ v ∈ e},
        (splittingDisk K e.1 (boundaryComplex_faces_subset 2 K e.2.1)).space ∩
          closure (K.space \ (derivedNeighborhood K (boundaryComplex 2 K)).space) := by
  classical
  let B := boundaryComplex 2 K
  let N := derivedNeighborhood K B
  let R := subcomplexGeneratedBy (secondDerived K) N.facesᶜ
  let _ : Finite B.faces := (boundaryComplex_faces_finite 2 K).to_subtype
  let _ : Finite N.faces := (derivedNeighborhood_faces_finite K B).to_subtype
  let _ : Finite R.faces := (subcomplexGeneratedBy_faces_finite _ _).to_subtype
  have hBsub : B.faces ⊆ K.faces := boundaryComplex_faces_subset 2 K
  have hB := isCombinatorialManifold_boundaryComplex K hK.isCombinatorialManifoldWithBoundary
  have hBcard : ∀ s ∈ B.faces, s.card ≤ 2 := fun s hs => hB.card_le B hs
  have hN := hK.isCombinatorialManifoldWithBoundary.derivedNeighborhood B
  have hNK : N.space ⊆ K.space := derivedNeighborhood_space_subset K B
  have hRspace : R.space = closure (K.space \ N.space) := by
    rw [← closure_space_sdiff_space_eq_subcomplexGeneratedBy (secondDerived K)
      (secondDerived K) N (subset_refl _) (derivedNeighborhood_faces_subset K B),
      (secondDerived_isSubdivision K).space_eq]
  have hR : IsPLBall 2 R.space := hRspace.symm ▸
    isPLBall_closure_sdiff_derivedNeighborhood_boundaryComplex K hK
  have hRK : R.space ⊆ K.space := hRspace.symm ▸
    closure_minimal sdiff_subset hK.isPolyhedron.isClosed
  have hdis : Disjoint R.space B.space := by
    rw [disjoint_left]
    intro x hxR hxB
    obtain ⟨O, hO, hxO, hON⟩ := mem_nhdsWithin.mp
      (derivedNeighborhood_mem_nhdsWithin hBsub hxB)
    obtain ⟨y, hyO, hyK, hyN⟩ := mem_closure_iff.mp (hRspace ▸ hxR) O hO hxO
    exact hyN (hON ⟨hyO, hyK⟩)
  have hdouble : closure (K.space \ R.space) = N.space := by
    rw [hRspace]
    exact hK.isCombinatorialManifoldWithBoundary.closure_sdiff_closure_sdiff_eq K N hN hNK
  let J := (boundaryComplex 2 R).space
  have hJ : IsPLSphere 1 J := isPLSphere_boundaryComplex_space_of_isPLBall R hR
  have hJN : R.space ∩ N.space = J := by
    rw [← hdouble]
    exact inter_closure_sdiff_eq_boundaryComplex_of_disjoint_boundary K R
      hK.isCombinatorialManifoldWithBoundary hR.isCombinatorialManifoldWithBoundary hRK hdis
  let V := B.vertices
  let Ed := {e : Finset E // e ∈ B.faces ∧ e.card = 2}
  let _ : Finite V := (SimplicialComplex.finite_vertices B).to_subtype
  let C : V → Set E := fun w => (graphDualCell K B w.1).space
  let X : V → Set E := fun w => C w ∩ R.space
  have hclosed : ∀ w, IsClosed (X w) := by
    intro w
    let _ : Finite (graphDualCell K B w.1).faces :=
      (graphDualCell_faces_finite K B w.1).to_subtype
    exact (isPolyhedron_space _).isClosed.inter hR.isPolyhedron.isClosed
  have hXJ : ∀ w, X w ⊆ J := fun w x hx => hJN ▸
    ⟨hx.2, graphDualCell_space_subset K B w.1 hx.1⟩
  have hcover : J ⊆ ⋃ w, X w := by
    intro x hx
    have hx' : x ∈ R.space ∩ N.space := hJN.symm ▸ hx
    have hxN : x ∈ ⋃ w ∈ B.vertices, (graphDualCell K B w).space := by
      have hxN := (iUnion_graphDualCell_space K B hBsub).symm ▸ hx'.2
      obtain ⟨w, hw, hxw⟩ := mem_iUnion₂.mp hxN
      exact mem_iUnion₂.mpr ⟨w, hw, hxw⟩
    obtain ⟨w, hw, hxw⟩ := mem_iUnion₂.mp hxN
    exact mem_iUnion.mpr ⟨⟨w, hw⟩, hxw, hx'.1⟩
  have hpoint : ∀ e : Ed, ∃ p : E,
      (splittingDisk K e.1 (hBsub e.2.1)).space ∩ R.space = {p} := by
    intro e
    rw [hRspace]
    exact exists_singleton_splittingDisk_inter_boundary_residual K
      hK.isCombinatorialManifoldWithBoundary e.2.1 e.2.2
  choose p hp using hpoint
  have hpin (e : Ed) : p e ∈ (splittingDisk K e.1 (hBsub e.2.1)).space ∩ R.space :=
    (hp e).symm ▸ mem_singleton (p e)
  have hpinj : Function.Injective p := by
    intro e f hef
    by_contra hne
    exact Set.disjoint_left.mp (disjoint_splittingDisk_space K (hBsub e.2.1)
      (hBsub f.2.1) (fun heq => hne (Subtype.ext heq)) (e.2.2.trans f.2.2.symm))
      (hpin e).1 (hef.symm ▸ (hpin f).1)
  let inc : V → Ed → Prop := fun w e => w.1 ∈ e.1
  have hsplit (w : V) (e : Ed) (hwe : inc w e) :
      (splittingDisk K e.1 (hBsub e.2.1)).space ⊆ C w := by
    obtain ⟨a, b, hab, heq⟩ := Finset.card_eq_two.mp e.2.2
    have heB : {a, b} ∈ B.faces := heq ▸ e.2.1
    have hinter := graphDualCell_space_inter K B hBsub hBcard hab heB
    change w.1 ∈ e.1 at hwe
    rw [heq] at hwe
    simp only [Finset.mem_insert, Finset.mem_singleton] at hwe
    rcases hwe with hwa | hwb
    · change _ ⊆ (graphDualCell K B w.1).space
      simpa only [heq, hwa] using hinter.symm.subset.trans inter_subset_left
    · change _ ⊆ (graphDualCell K B w.1).space
      simpa only [heq, hwb] using hinter.symm.subset.trans inter_subset_right
  have hpX : ∀ w e, p e ∈ X w ↔ inc w e := by
    intro w e
    constructor
    · intro hx
      exact vertex_mem_of_graphDualCell_inter_splittingDisk_nonempty K B hBsub hBcard
        w.2 (hBsub e.2.1) e.2.2 ⟨p e, hx.1, (hpin e).1⟩
    · intro hwe
      exact ⟨hsplit w e hwe (hpin e).1, (hpin e).2⟩
  have hends : ∀ e : Ed, ∃ w z : V, w ≠ z ∧ inc w e ∧ inc z e := by
    intro e
    obtain ⟨a, b, hab, heq⟩ := Finset.card_eq_two.mp e.2.2
    have haB : {a} ∈ B.faces := B.down_closed e.2.1 (by simp [heq]) (by simp)
    have hbB : {b} ∈ B.faces := B.down_closed e.2.1 (by simp [heq]) (by simp)
    exact ⟨⟨a, haB⟩, ⟨b, hbB⟩, fun h => hab (congrArg Subtype.val h),
      by simp [inc, heq], by simp [inc, heq]⟩
  have hend3 : ∀ e : Ed, ∀ a b c : V, inc a e → inc b e → inc c e →
      a = b ∨ a = c ∨ b = c := by
    intro e a b c ha hb hc
    obtain ⟨u, z, _, he⟩ := Finset.card_eq_two.mp e.2.2
    have hcase : ∀ w : V, inc w e → w.1 = u ∨ w.1 = z := by
      intro w hw
      simpa only [inc, he, Finset.mem_insert, Finset.mem_singleton] using hw
    rcases hcase a ha with ha | ha <;> rcases hcase b hb with hb | hb <;>
      rcases hcase c hc with hc | hc
    all_goals first
      | exact Or.inl (Subtype.ext (ha.trans hb.symm))
      | exact Or.inr (Or.inl (Subtype.ext (ha.trans hc.symm)))
      | exact Or.inr (Or.inr (Subtype.ext (hb.trans hc.symm)))
  have hedgeeq : ∀ (a b : V) (e f : Ed), a ≠ b → inc a e → inc b e →
      inc a f → inc b f → e = f := by
    intro a b e f hab hae hbe haf hbf
    have hab' : a.1 ≠ b.1 := fun h => hab (Subtype.ext h)
    have he : ({a.1, b.1} : Finset E) = e.1 := Finset.eq_of_subset_of_card_le
      (Finset.insert_subset_iff.mpr ⟨hae, Finset.singleton_subset_iff.mpr hbe⟩)
      (by simp [hab', e.2.2])
    have hf : ({a.1, b.1} : Finset E) = f.1 := Finset.eq_of_subset_of_card_le
      (Finset.insert_subset_iff.mpr ⟨haf, Finset.singleton_subset_iff.mpr hbf⟩)
      (by simp [hab', f.2.2])
    exact Subtype.ext (he.symm.trans hf)
  have hdegree : ∀ w : V, ∃ e f : Ed, e ≠ f ∧ inc w e ∧ inc w f ∧
      ∀ g : Ed, inc w g → g = e ∨ g = f := by
    intro w
    obtain ⟨a, b, hab, hco⟩ := hB.codimension_one_cofaces B w.2 (Finset.card_singleton w.1)
    have ha : a ∉ ({w.1} : Finset E) ∧ insert a {w.1} ∈ B.faces := by
      change a ∈ {z | z ∉ ({w.1} : Finset E) ∧ insert z {w.1} ∈ B.faces}
      rw [hco]
      exact mem_insert _ _
    have hb : b ∉ ({w.1} : Finset E) ∧ insert b {w.1} ∈ B.faces := by
      change b ∈ {z | z ∉ ({w.1} : Finset E) ∧ insert z {w.1} ∈ B.faces}
      rw [hco]
      exact mem_insert_of_mem _ (mem_singleton _)
    let e : Ed := ⟨insert a {w.1}, ha.2, by simp [ha.1]⟩
    let f : Ed := ⟨insert b {w.1}, hb.2, by simp [hb.1]⟩
    have hef : e ≠ f := by
      intro h
      have ha' : a ∈ f.1 := congrArg Subtype.val h ▸ Finset.mem_insert_self _ _
      simp only [f, Finset.mem_insert, Finset.mem_singleton] at ha'
      exact ha'.elim hab (fun h => ha.1 (Finset.mem_singleton.mpr h))
    refine ⟨e, f, hef, by simp [inc, e], by simp [inc, f], ?_⟩
    intro g hwg
    obtain ⟨u, z, huz, hg⟩ := Finset.card_eq_two.mp g.2.2
    have hwu : w.1 = u ∨ w.1 = z := by
      simpa only [inc, hg, Finset.mem_insert, Finset.mem_singleton] using hwg
    have hother : ∃ c, c ∉ ({w.1} : Finset E) ∧ g.1 = insert c {w.1} := by
      rcases hwu with hwu | hwz
      · exact ⟨z, by simp [hwu, huz.symm], by rw [hg, hwu, Finset.pair_comm]⟩
      · exact ⟨u, by simp [hwz, huz], by rw [hg, hwz]⟩
    obtain ⟨c, hcw, hgc⟩ := hother
    have hc : c ∈ {a, b} := hco ▸ (show c ∈
      {z | z ∉ ({w.1} : Finset E) ∧ insert z {w.1} ∈ B.faces} from
        ⟨hcw, hgc ▸ g.2.1⟩)
    rcases hc with rfl | rfl
    · exact Or.inl (Subtype.ext hgc)
    · exact Or.inr (Subtype.ext hgc)
  have hdeg3 : ∀ w e f g, inc w e → inc w f → inc w g → e = f ∨ e = g ∨ f = g := by
    intro w e f g he hf hg
    obtain ⟨a, b, _, _, _, hex⟩ := hdegree w
    rcases hex e he with rfl | rfl <;> rcases hex f hf with rfl | rfl <;>
      rcases hex g hg with rfl | rfl <;> simp
  have hXne : ∀ w, X w ≠ J := by
    intro w hw
    obtain ⟨e, _, _, hwe, _, _⟩ := hdegree w
    obtain ⟨a, b, hab, hae, hbe⟩ := hends e
    obtain ⟨z, hzw, hze⟩ : ∃ z : V, z ≠ w ∧ inc z e := by
      by_cases haw : a = w
      · exact ⟨b, fun h => hab (haw.trans h.symm), hbe⟩
      · exact ⟨a, haw, hae⟩
    obtain ⟨f, g, hfg, hzf, hzg, _⟩ := hdegree z
    obtain ⟨d, hde, hzd⟩ : ∃ d : Ed, d ≠ e ∧ inc z d := by
      by_cases hfe : f = e
      · exact ⟨g, fun h => hfg (hfe.trans h.symm), hzg⟩
      · exact ⟨f, hfe, hzf⟩
    have hpJ : p d ∈ J := hXJ z ((hpX z d).mpr hzd)
    have hwd := (hpX w d).mp (hw.symm ▸ hpJ)
    exact hde (hedgeeq z w d e hzw hzd hwd hze hwe)
  have hmeet : ∀ w z, w ≠ z → ∀ x ∈ X w ∩ X z,
      ∃ e : Ed, inc w e ∧ inc z e ∧ x = p e := by
    intro w z hwz x hx
    have hwz' : w.1 ≠ z.1 := fun h => hwz (Subtype.ext h)
    have heB : {w.1, z.1} ∈ B.faces := by
      by_contra he
      exact Set.notMem_empty x ((graphDualCell_space_inter_eq_empty K B hBsub hBcard
        w.2 z.2 hwz' he) ▸ (show x ∈ C w ∩ C z from ⟨hx.1.1, hx.2.1⟩))
    let e : Ed := ⟨{w.1, z.1}, heB, Finset.card_pair hwz'⟩
    refine ⟨e, by simp [inc, e], by simp [inc, e], ?_⟩
    apply Set.mem_singleton_iff.mp
    rw [← hp e]
    refine ⟨?_, hx.1.2⟩
    rw [← graphDualCell_space_inter K B hBsub hBcard hwz' heB]
    exact ⟨hx.1.1, hx.2.1⟩
  let w : V := ⟨v, hv⟩
  obtain ⟨e, f, hef, hwe, hwf, hex⟩ := hdegree w
  obtain ⟨γ, hγ, hγ0, hγ1⟩ := hJ.exists_isPLHomeomorphOn_Icc_of_cycle hclosed hXJ hcover hXne
    hpinj hpX hmeet (fun u => by
      obtain ⟨a, b, hab, ha, hb, _⟩ := hdegree u
      exact ⟨a, b, hab, ha, hb⟩) hdeg3 hends hend3 hef hwe hwf
  refine ⟨γ, by simpa only [X, C, w, hRspace, N, B] using hγ, ?_⟩
  rw [hγ0, hγ1]
  apply Subset.antisymm
  · rintro x (rfl | rfl)
    · refine mem_iUnion.mpr ⟨⟨e.1, e.2.1, e.2.2, hwe⟩, ?_⟩
      simpa only [hRspace, N, B] using hpin e
    · refine mem_iUnion.mpr ⟨⟨f.1, f.2.1, f.2.2, hwf⟩, ?_⟩
      simpa only [hRspace, N, B] using hpin f
  · intro x hx
    obtain ⟨g, hxg⟩ := mem_iUnion.mp hx
    let d : Ed := ⟨g.1, g.2.1, g.2.2.1⟩
    have hxd : x = p d := by
      apply mem_singleton_iff.mp
      rw [← hp d]
      simpa only [d, hRspace, N, B] using hxg
    rcases hex d g.2.2.2 with he | hf
    · rw [hxd, he]
      exact mem_insert _ _
    · rw [hxd, hf]
      exact mem_insert_of_mem _ (mem_singleton _)

open Classical in
theorem isPLBall_graphDualCell_inter_boundary_residual
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsPLBall 2 K.space)
    {v : E} (hv : {v} ∈ (boundaryComplex 2 K).faces) :
    IsPLBall 1 ((graphDualCell K (boundaryComplex 2 K) v).space ∩
      closure (K.space \ (derivedNeighborhood K (boundaryComplex 2 K)).space)) := by
  obtain ⟨γ, hγ, -⟩ := exists_isPLHomeomorphOn_graphDualCell_inter_boundary_residual K hK hv
  exact (isPLBall_Icc (by norm_num : (0 : ℝ) < 1)).of_isPLHomeomorphOn hγ

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [T2Space M] {U : Set M} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M U}

open Classical in
theorem exists_isPLCellOn_section34GraphVertexCell_inter_residualTriangle
    (hsub : IsSubdivision 𝒦'.complex 𝒦.complex) (hmap : 𝒦'.map = 𝒦.map)
    (s : Section34SimplexIndex 𝒦 3) (w : Section34VertexIndex 𝒦 𝒦')
    (hws : Section34Incident w.1 s.1) :
    ∃ B, IsPLCellOn 1 (section34GraphVertexCell 𝒦 𝒦' w ∩
      section34GraphResidualCell 𝒦 𝒦' s.1) B := by
  classical
  let S₀ := simplexComplex s.1 (𝒦.complex.indep s.2.1)
  let B₀ := simplexBoundary s.1 (𝒦.complex.indep s.2.1)
  let S := restrict 𝒦'.complex (convexHull ℝ (s.1 : Set Ea))
  let L := restrict 𝒦'.complex (𝒦'.map ⁻¹' graphSkeletonSpace 𝒦)
  let L₀ := restrict 𝒦.complex (𝒦.map ⁻¹' graphSkeletonSpace 𝒦)
  have hS₀space : S₀.space = convexHull ℝ (s.1 : Set Ea) :=
    simplexComplex_space _ _ (𝒦.complex.nonempty_of_mem_faces s.2.1)
  have hS₀K : S₀.faces ⊆ 𝒦.complex.faces :=
    fun _ ht => 𝒦.complex.down_closed s.2.1 ht.2 ht.1
  have hSsub : IsSubdivision S S₀ := by
    simpa only [hS₀space] using hsub.restrict S₀ hS₀K
  have hSspace : S.space = convexHull ℝ (s.1 : Set Ea) := hSsub.space_eq.trans hS₀space
  have hS₀ : IsPLBall 2 S₀.space := hS₀space.symm ▸
    isPLBall_convexHull_of_affineIndependent s.1 (𝒦.complex.indep s.2.1) s.2.2
  have hS : IsPLBall 2 S.space := hSsub.space_eq.symm ▸ hS₀
  let _ : Finite S₀.faces := (simplexComplex_faces_finite _ _).to_subtype
  let _ : Finite S.faces := (𝒦'.restrict_faces_finite_of_isCompact
    (s.1.finite_toSet.isCompact_convexHull ℝ)
      ((𝒦.complex.convexHull_subset_space s.2.1).trans hsub.space_eq.symm.subset)).to_subtype
  have hSbd : (boundaryComplex 2 S).space = B₀.space := by
    rw [boundaryComplex_space_of_isSubdivision S₀ S hS₀.isCombinatorialManifoldWithBoundary
      hSsub, show boundaryComplex 2 S₀ = B₀ from
        boundaryComplex_simplexComplex (𝒦.complex.indep s.2.1) s.2.2]
  have hLspace : L.space = L₀.space :=
    (isSubdivision_restrict_preimage_graphSkeletonSpace hsub hmap).space_eq
  have hcore : L.space ∩ S.space = (boundaryComplex 2 S).space := by
    rw [hSbd, hLspace, hSspace, ← hS₀space,
      ← restrict_space_eq_inter_of_faces_subset 𝒦.complex L₀ S₀
        (restrict_faces_subset _ _) hS₀K, hS₀space,
      restrict_graph_core_triangle_eq_simplexBoundary 𝒦 s]
  have hLS : restrict L S.space = boundaryComplex 2 S :=
    eq_of_faces_subset_of_space_eq _ _ S
      (fun _ hu => ((mem_restrict_faces_iff_of_faces_subset 𝒦'.complex L S
        (restrict_faces_subset _ _) (restrict_faces_subset _ _)).mp hu).2)
      (boundaryComplex_faces_subset 2 S)
      ((restrict_space_eq_inter_of_faces_subset 𝒦'.complex L S
        (restrict_faces_subset _ _) (restrict_faces_subset _ _)).trans hcore)
  let v := w.1.centroid ℝ id
  have hvS : {v} ∈ S.faces := by
    rw [show ({v} : Finset Ea) = w.1 from (section34VertexIndex_eq_singleton_centroid w).symm]
    exact ⟨w.2.1, convexHull_min hws (convex_convexHull ℝ (s.1 : Set Ea))⟩
  have hvL : {v} ∈ L.faces := singleton_centroid_mem_section34GraphCore w
  have hvB : {v} ∈ (boundaryComplex 2 S).faces := by
    rw [← hLS]
    exact ⟨hvL, hSspace.symm ▸ hvS.2⟩
  have hres : closure (convexHull ℝ (s.1 : Set Ea) \
      (derivedNeighborhood 𝒦'.complex L).space) =
      closure (S.space \
        (derivedNeighborhood S (boundaryComplex 2 S)).space) := by
    congr 1
    rw [← hLS, derivedNeighborhood_restrict_core_eq 𝒦'.complex S L
      (restrict_faces_subset _ _) (restrict_faces_subset _ _),
      ← derivedNeighborhood_space_inter_subcomplex 𝒦'.complex S L (restrict_faces_subset _ _),
      hSspace]
    ext x
    simp only [mem_sdiff, mem_inter_iff]
    tauto
  let C := closure (convexHull ℝ (s.1 : Set Ea) \
    (derivedNeighborhood 𝒦'.complex L).space)
  have hCS : C ⊆ S.space := hSspace.symm ▸
    closure_minimal sdiff_subset (s.1.finite_toSet.isCompact_convexHull ℝ).isClosed
  have hCK : C ⊆ 𝒦'.complex.space :=
    hCS.trans (space_mono_of_faces_subset (restrict_faces_subset _ _))
  have htrace : (graphDualCell 𝒦'.complex L v).space ∩ C =
      (graphDualCell S (boundaryComplex 2 S) v).space ∩
        closure (S.space \ (derivedNeighborhood S (boundaryComplex 2 S)).space) := by
    rw [← inter_eq_right.mpr hCS, ← inter_assoc,
      graphDualCell_space_inter_subcomplex 𝒦'.complex S L (restrict_faces_subset _ _) hvS,
      ← graphDualCell_restrict_core_eq 𝒦'.complex S L
        (restrict_faces_subset _ _) (restrict_faces_subset _ _), hLS]
    exact congrArg (fun A => (graphDualCell S (boundaryComplex 2 S) v).space ∩ A) hres
  have hball : IsPLBall 1 ((graphDualCell 𝒦'.complex L v).space ∩ C) :=
    htrace.symm ▸ isPLBall_graphDualCell_inter_boundary_residual S hS hvB
  have hGsub : (graphDualCell 𝒦'.complex L v).space ⊆ 𝒦'.complex.space :=
    (graphDualCell_space_subset _ _ _).trans (derivedNeighborhood_space_subset _ _)
  obtain ⟨Bd, hBd⟩ := 𝒦'.exists_isPLCellOn_image
    (inter_subset_left.trans hGsub) (by omega) hball
  rw [𝒦'.bijOn.injOn.image_inter hGsub hCK,
    image_closure_sdiff_derivedNeighborhood_eq_section34GraphResidualCell hsub hmap s.2.1] at hBd
  exact ⟨Bd, hBd⟩

end DifferentialGeometry.Topology.PiecewiseLinear
