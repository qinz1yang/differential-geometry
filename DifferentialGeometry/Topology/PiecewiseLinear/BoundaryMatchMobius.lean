/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.TubeFreeFaceStrips
import DifferentialGeometry.Topology.PiecewiseLinear.IntervalMonodromy
import DifferentialGeometry.Topology.PiecewiseLinear.CircleFourPoints
import DifferentialGeometry.Topology.PiecewiseLinear.EuclideanSurfaceOrientation
import DifferentialGeometry.Topology.PiecewiseLinear.TubeFrontierConnected
import DifferentialGeometry.Topology.PiecewiseLinear.PLPiece

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {K : Geometry.SimplicialComplex ℝ E3} {N N' : Set E3} {C Cpp : E3 → Set E3}
  {D Dbd Ec Eint Ebd : Finset E3 → Set E3} {h : E3 → E3}

theorem mem_or_mem_of_card_eq_two {g : Finset E3} {a b : E3} (hg : g.card = 2) (ha : a ∈ g)
    (hb : b ∈ g) (hab : a ≠ b) {u : E3} (hu : u ∈ g) : u = a ∨ u = b := by
  have hpair : ({a, b} : Finset E3) = g := by
    classical
    refine Finset.eq_of_subset_of_card_le
      (Finset.insert_subset ha (Finset.singleton_subset_iff.mpr hb)) ?_
    rw [Finset.card_pair hab, hg]
  classical
  rw [← hpair] at hu
  simpa using hu

theorem IsHandleDecompositionOfTube.exists_trace_of_mem_inter
    (hd : IsHandleDecompositionOfTube K N C D Dbd h N' Ec Eint Ebd Cpp) {u v : E3}
    (hu : u ∈ K.vertices) (hv : v ∈ K.vertices) (huv : u ≠ v) {X : Set E3} {y : E3}
    (hyu : y ∈ Cpp u ∩ X) (hyv : y ∈ Cpp v ∩ X) :
    ∃ g ∈ K.faces, g.card = 2 ∧ u ∈ g ∧ v ∈ g ∧ y ∈ Ec g ∩ X := by
  classical
  by_cases hadj : ({u, v} : Finset E3) ∈ K.faces
  · have hE := hd.handleEdge u hu v hv huv hadj
    exact ⟨{u, v}, hadj, Finset.card_pair huv, Finset.mem_insert_self _ _,
      Finset.mem_insert_of_mem (Finset.mem_singleton_self _), hE ▸ ⟨hyu.1, hyv.1⟩, hyu.2⟩
  · have h0 := hd.handleNonEdge u hu v hv huv hadj
    exact absurd (h0 ▸ (⟨hyu.1, hyv.1⟩ : y ∈ Cpp u ∩ Cpp v)) (notMem_empty y)

theorem IsHandleDecompositionOfTube.pseudoCell_subset_piece
    (hd : IsHandleDecompositionOfTube K N C D Dbd h N' Ec Eint Ebd Cpp) {g : Finset E3}
    (hg : g ∈ K.faces) (hgc : g.card = 2) {u : E3} (hug : u ∈ g) : Ec g ⊆ Cpp u := by
  classical
  obtain ⟨a, hag, b, hbg, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < g.card)
  have hpair : ({a, b} : Finset E3) = g := by
    refine Finset.eq_of_subset_of_card_le
      (Finset.insert_subset hag (Finset.singleton_subset_iff.mpr hbg)) ?_
    rw [Finset.card_pair hab, hgc]
  have ha : a ∈ K.vertices :=
    K.down_closed hg (Finset.singleton_subset_iff.mpr hag) (Finset.singleton_nonempty a)
  have hb : b ∈ K.vertices :=
    K.down_closed hg (Finset.singleton_subset_iff.mpr hbg) (Finset.singleton_nonempty b)
  have hE := hd.handleEdge a ha b hb hab (hpair ▸ hg)
  rw [hpair] at hE
  rcases mem_or_mem_of_card_eq_two hgc hag hbg hab hug with rfl | rfl
  · rw [← hE]
    exact inter_subset_left
  · rw [← hE]
    exact inter_subset_right

theorem IsHandleDecompositionOfTube.isPLHomeomorphOn_iUnion_freeFace
    (hd : IsHandleDecompositionOfTube K N C D Dbd h N' Ec Eint Ebd Cpp) {X : Set E3}
    (hXpoly : ∀ v ∈ K.vertices, IsPolyhedron (Cpp v ∩ X)) {f : E3 → E3}
    (W : Finset K.vertices)
    (hf : ∀ v ∈ W, IsPLHomeomorphOn f (frontier (C v) ∩ frontier N) (Cpp v ∩ X))
    (hrim : ∀ v ∈ W, ∀ e ∈ edgesAt K v, f '' Dbd e = Ec e ∩ X) :
    IsPLHomeomorphOn f (⋃ v ∈ W, frontier (C v) ∩ frontier N) (⋃ v ∈ W, Cpp v ∩ X) := by
  classical
  have ht := hd.tube
  have hApoly : ∀ v ∈ W, IsPolyhedron (frontier (C (v : E3)) ∩ frontier N) := by
    intro v hv
    have h := (hXpoly v v.2).image_of_isPiecewiseAffineOn (hf v hv).symm.isPiecewiseAffineOn
      (hf v hv).symm.bijOn.injOn
    rwa [(hf v hv).symm.image_eq] at h
  induction W using Finset.induction_on with
  | empty =>
    simp only [Finset.notMem_empty, iUnion_of_empty, iUnion_empty]
    exact ⟨bijOn_empty f, fun x hx => absurd hx (notMem_empty x),
      fun x hx => absurd hx (notMem_empty x)⟩
  | insert a W ha ih =>
    have hfW : ∀ v ∈ W, IsPLHomeomorphOn f (frontier (C v) ∩ frontier N) (Cpp v ∩ X) :=
      fun v hv => hf v (Finset.mem_insert_of_mem hv)
    have hrimW : ∀ v ∈ W, ∀ e ∈ edgesAt K v, f '' Dbd e = Ec e ∩ X :=
      fun v hv => hrim v (Finset.mem_insert_of_mem hv)
    have hApolyW : ∀ v ∈ W, IsPolyhedron (frontier (C (v : E3)) ∩ frontier N) :=
      fun v hv => hApoly v (Finset.mem_insert_of_mem hv)
    have hIH := ih hfW hrimW hApolyW
    simp only [Finset.set_biUnion_insert]
    have hfa := hf a (Finset.mem_insert_self a W)
    have hPipoly : IsPolyhedron (⋃ v ∈ W, frontier (C (v : E3)) ∩ frontier N) := by
      have h := (IsPolyhedron.finsetBiUnion W fun v => hXpoly v v.2).image_of_isPiecewiseAffineOn
        hIH.symm.isPiecewiseAffineOn hIH.symm.bijOn.injOn
      rwa [hIH.symm.image_eq] at h
    refine hfa.union hIH (hApoly a (Finset.mem_insert_self a W)) hPipoly ?_
    · apply Subset.antisymm
      · rintro _ ⟨y, ⟨hya, hyW⟩, rfl⟩
        obtain ⟨v, hv, hyv⟩ := mem_iUnion₂.mp hyW
        exact ⟨hfa.bijOn.mapsTo hya,
          mem_iUnion₂.mpr ⟨v, hv, (hfW v hv).bijOn.mapsTo hyv⟩⟩
      · rintro z ⟨hza, hzW⟩
        obtain ⟨v, hv, hzv⟩ := mem_iUnion₂.mp hzW
        have hav : (a : E3) ≠ v := fun h => ha (Subtype.ext h ▸ hv)
        obtain ⟨g, hg, hgc, hag, hvg, hzg⟩ := hd.exists_trace_of_mem_inter a.2 v.2 hav hza hzv
        rw [← hrim a (Finset.mem_insert_self a W) g ⟨hg, hgc, hag⟩] at hzg
        obtain ⟨y, hy, rfl⟩ := hzg
        exact ⟨y, ⟨ht.rim_subset_freeFace hg hgc a.2 hag hy,
          mem_iUnion₂.mpr ⟨v, hv, ht.rim_subset_freeFace hg hgc v.2 hvg hy⟩⟩, rfl⟩

theorem IsTube.exists_isOrientable_frontier (ht : IsTube K N C D Dbd h N')
    (hconn : IsConnected K.space) :
    ∃ (T : Geometry.SimplicialComplex ℝ E3) (_ : Finite T.faces),
      IsCombinatorialManifoldWithBoundary 2 T ∧ IsOrientable 2 T ∧ T.space = frontier N := by
  classical
  let _ : DecidableEq E3 := fun a b => Classical.propDecidable (a = b)
  obtain ⟨A, hAfin, hA, hKA, hC, -⟩ := ht.derivedModel
  let _ : Finite A.faces := hAfin.to_subtype
  have hN : N = (derivedNeighborhood A K).space := by
    rw [ht.unionEq, ← iUnion_graphDualCell_space A K hKA]
    exact iUnion₂_congr hC
  let Nc := derivedNeighborhood A K
  let _ : Finite Nc.faces := (derivedNeighborhood_faces_finite A K).to_subtype
  have hNc : IsCombinatorialManifoldWithBoundary 3 Nc := hA.derivedNeighborhood K
  let BN := @boundaryComplex _ _ _ (Classical.decEq _) (2 + 1) Nc
  have hFr : frontier Nc.space = BN.space := frontier_space_eq_boundaryComplex_space hNc
  let _ : Finite BN.faces := ((Set.toFinite Nc.faces).subset fun _ hs => hs.1).to_subtype
  have hBman : IsCombinatorialManifold 2 BN := isCombinatorialManifold_boundaryComplex Nc hNc
  have hconnB : IsConnected BN.space := by
    rw [← hFr]
    change IsConnected (frontier (derivedNeighborhood A K).space)
    rw [← hN]
    exact ht.isConnected_frontier hconn
  refine ⟨BN, inferInstance, hBman.isCombinatorialManifoldWithBoundary,
    hBman.isOrientable_euclidean_three BN hconnB, ?_⟩
  rw [← hFr]
  change frontier (derivedNeighborhood A K).space = frontier N
  rw [← hN]

theorem exists_isOrientable_frontier_of_isCombinatorialManifoldWithBoundary
    {XK : Geometry.SimplicialComplex ℝ E3} (hfin : XK.faces.Finite)
    (hX : IsCombinatorialManifoldWithBoundary 3 XK) (hc : IsConnected (frontier XK.space)) :
    ∃ (T : Geometry.SimplicialComplex ℝ E3) (_ : Finite T.faces),
      IsCombinatorialManifoldWithBoundary 2 T ∧ IsOrientable 2 T ∧
        T.space = frontier XK.space := by
  classical
  let _ : Finite XK.faces := hfin.to_subtype
  let BX := @boundaryComplex _ _ _ (Classical.decEq _) (2 + 1) XK
  have hFr : frontier XK.space = BX.space := frontier_space_eq_boundaryComplex_space hX
  let _ : Finite BX.faces := ((Set.toFinite XK.faces).subset fun _ hs => hs.1).to_subtype
  have hBman : IsCombinatorialManifold 2 BX := isCombinatorialManifold_boundaryComplex XK hX
  have hconnB : IsConnected BX.space := hFr ▸ hc
  exact ⟨BX, inferInstance, hBman.isCombinatorialManifoldWithBoundary,
    hBman.isOrientable_euclidean_three BX hconnB, hFr.symm⟩

theorem image_prod_singleton_eq {F : ℝ × ℝ → E3} (c : ℝ) :
    F '' (Icc (0 : ℝ) 1 ×ˢ {c}) = (fun t => F (t, c)) '' Icc 0 1 := by
  ext z
  constructor
  · rintro ⟨⟨t, s⟩, ⟨ht, hs⟩, rfl⟩
    have hs' : s = c := hs
    subst hs'
    exact ⟨t, ht, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨(t, c), ⟨ht, mem_singleton c⟩, rfl⟩

theorem image_one_sub_eq {a : ℝ → E3} :
    (fun t => a (1 - t)) '' Icc (0 : ℝ) 1 = a '' Icc 0 1 := by
  have hrev : (fun t : ℝ => 1 - t) '' Icc 0 1 = Icc 0 1 := by
    rw [image_const_sub_Icc]
    norm_num
  rw [show (fun t : ℝ => a (1 - t)) = a ∘ fun t => 1 - t from rfl, image_comp, hrev]

theorem IsHandleDecompositionOfTube.false_of_reversed_rim
    (hd : IsHandleDecompositionOfTube K N C D Dbd h N' Ec Eint Ebd Cpp)
    (hconn : IsConnected K.space) {XK : Geometry.SimplicialComplex ℝ E3}
    (hXfin : XK.faces.Finite) (hXman : IsCombinatorialManifoldWithBoundary 3 XK)
    (hXc : IsConnected (frontier XK.space)) {R : Finset E3 → (Fin 3 → ℝ) → E3}
    (hR : ∀ e ∈ K.faces, e.card = 2 → IsPLHomeomorphOn (R e) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (D e) ∧
      Dbd e = R e '' stdSimplexBoundary 2)
    {W : Finset K.vertices} {f fw : E3 → E3}
    (hf : IsPLHomeomorphOn f (⋃ v ∈ W, frontier (C v) ∩ frontier N)
      (⋃ v ∈ W, Cpp v ∩ frontier XK.space))
    (hfv : ∀ v ∈ W, MapsTo f (frontier (C v) ∩ frontier N) (Cpp v ∩ frontier XK.space))
    {w x x₀ : K.vertices} (hw : w ∉ W) (hx : x ∈ W) (hx₀ : x₀ ∈ W)
    {e e₀ : Finset E3} (he : e ∈ edgesAt K w) (hxe : (x : E3) ∈ e) (he₀ : e₀ ∈ edgesAt K w)
    (hx₀e₀ : (x₀ : E3) ∈ e₀) (hee₀ : e ≠ e₀)
    (p : (SimplicialComplex.edgeGraph K).Walk x x₀) (hp : p.IsPath)
    (hpW : ∀ v ∈ p.support, v ∈ W)
    (hfw : IsPLHomeomorphOn fw (frontier (C w) ∩ frontier N) (Cpp w ∩ frontier XK.space))
    (hfwrim : ∀ g ∈ edgesAt K w, fw '' Dbd g = Ec g ∩ frontier XK.space)
    (hfw₀ : EqOn fw f (Dbd e₀)) {r : E3 → E3} {a : ℝ → E3}
    (hr : IsPLHomeomorphOn r (Dbd e) (Dbd e)) (hnr : ¬ IsPLCirclePositive (Dbd e) r)
    (ha : IsPLHomeomorphOn a (Icc 0 1) (a '' Icc 0 1)) (hac : a '' Icc 0 1 ⊆ Dbd e)
    (hra : ∀ t ∈ Icc (0 : ℝ) 1, r (a t) = a (1 - t))
    (hfwe : ∀ y ∈ Dbd e, fw y = f (r y)) : False := by
  classical
  have ht := hd.tube
  have hwx : (w : E3) ≠ x := fun h => hw (Subtype.ext h ▸ hx)
  have hwx₀ : (w : E3) ≠ x₀ := fun h => hw (Subtype.ext h ▸ hx₀)
  have hein : e ∈ edgesAt K x := ⟨he.1, he.2.1, hxe⟩
  have heout : e₀ ∈ edgesAt K x₀ := ⟨he₀.1, he₀.2.1, hx₀e₀⟩
  have hinp : ∀ v ∈ p.support, (v : E3) ∈ e → v = x := by
    intro v hv hve
    rcases mem_or_mem_of_card_eq_two he.2.1 he.2.2 hxe hwx hve with h | h
    · exact absurd (Subtype.ext h ▸ hpW v hv) hw
    · exact Subtype.ext h
  have houtp : ∀ v ∈ p.support, (v : E3) ∈ e₀ → v = x₀ := by
    intro v hv hve
    rcases mem_or_mem_of_card_eq_two he₀.2.1 he₀.2.2 hx₀e₀ hwx₀ hve with h | h
    · exact absurd (Subtype.ext h ▸ hpW v hv) hw
    · exact Subtype.ext h
  obtain ⟨S₁, γ, hS₁, hS₁0, hS₁1, hγ, hγc, hS₁sub, hS₁in, hS₁out, -⟩ :=
    ht.exists_freeFace_chain hR p hp hein heout hee₀ hinp houtp ha hac
  obtain ⟨σ, hσ, hσ0, hσ1, hσsub, hσin, hσout, hσdis⟩ :=
    ht.exists_freeFace_strip hR w.2 he₀ he hee₀.symm hγ hγc ha hac hr hnr hra
  have hsqpoly : IsPolyhedron (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :=
    (isHPolytope_Icc.prod isHPolytope_Icc).isPolyhedron
  have hS₁poly : IsPolyhedron (S₁ '' (Icc 0 1 ×ˢ Icc 0 1)) :=
    hsqpoly.image_of_isPiecewiseAffineOn hS₁.isPiecewiseAffineOn hS₁.bijOn.injOn
  have hσpoly : IsPolyhedron (σ '' (Icc 0 1 ×ˢ Icc 0 1)) :=
    hsqpoly.image_of_isPiecewiseAffineOn hσ.isPiecewiseAffineOn hσ.bijOn.injOn
  have hS₁W : S₁ '' (Icc 0 1 ×ˢ Icc 0 1) ⊆ ⋃ v ∈ W, frontier (C v) ∩ frontier N :=
    hS₁sub.trans (iUnion₂_subset fun v hv => subset_iUnion₂
      (s := fun v (_ : v ∈ W) => frontier (C (v : E3)) ∩ frontier N) v (hpW v hv))
  have haS₁ : a '' Icc 0 1 ⊆ S₁ '' (Icc 0 1 ×ˢ Icc 0 1) := by
    rw [← hS₁in]
    exact inter_subset_left
  have hγS₁ : γ '' Icc 0 1 ⊆ S₁ '' (Icc 0 1 ×ˢ Icc 0 1) := by
    rw [← hS₁out]
    exact inter_subset_left
  have haσ : a '' Icc 0 1 ⊆ σ '' (Icc 0 1 ×ˢ Icc 0 1) := by
    rw [← hσout]
    exact inter_subset_left
  have hγσ : γ '' Icc 0 1 ⊆ σ '' (Icc 0 1 ×ˢ Icc 0 1) := by
    rw [← hσin]
    exact inter_subset_left
  have hwv : ∀ v ∈ p.support, (w : E3) ≠ v := fun v hv h => hw (Subtype.ext h ▸ hpW v hv)
  have hσrim : ∀ y ∈ σ '' (Icc 0 1 ×ˢ Icc 0 1), ∀ g ∈ K.faces, g.card = 2 → y ∈ Dbd g →
      y ∈ a '' Icc 0 1 ∪ γ '' Icc 0 1 := by
    intro y hy g hg hgc hyg
    by_cases hge : g = e
    · subst hge
      exact Or.inl (hσout.subset ⟨hy, hyg⟩)
    · by_cases hge₀ : g = e₀
      · subst hge₀
        exact Or.inr (hσin.subset ⟨hy, hyg⟩)
      · exact absurd hyg (disjoint_left.mp (hσdis g hg hgc hge₀ hge) hy)
  have hSσ : S₁ '' (Icc 0 1 ×ˢ Icc 0 1) ∩ σ '' (Icc 0 1 ×ˢ Icc 0 1) =
      a '' Icc 0 1 ∪ γ '' Icc 0 1 := by
    apply Subset.antisymm
    · rintro y ⟨hyS, hyσ⟩
      obtain ⟨v, hv, hyv⟩ := mem_iUnion₂.mp (hS₁sub hyS)
      obtain ⟨g, hg, hgc, -, -, hyg⟩ := ht.exists_rim_of_mem_freeFace_inter w.2 v.2
        (hwv v hv) (hσsub hyσ) hyv
      exact hσrim y hyσ g hg hgc hyg
    · exact union_subset (subset_inter haS₁ haσ) (subset_inter hγS₁ hγσ)
  have hlow : ∀ t ∈ Icc (0 : ℝ) 1, (t, (0 : ℝ)) ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) (1 / 2) :=
    fun t ht' => ⟨ht', by norm_num, by norm_num⟩
  have hnotlow : ∀ t : ℝ, (t, (1 : ℝ)) ∉ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) (1 / 2) :=
    fun t h => by linarith [h.2.2]
  have hf₁ : IsPLHomeomorphOn (S₁ ∘ fun q : ℝ × ℝ => (q.1, 2 * q.2))
      (Icc 0 1 ×ˢ Icc 0 (1 / 2)) (S₁ '' (Icc 0 1 ×ˢ Icc 0 1)) :=
    isPLHomeomorphOn_squareLowerHalf.trans hS₁
  have hg₁ : IsPLHomeomorphOn (σ ∘ fun q : ℝ × ℝ => (q.1, 2 * q.2 - 1))
      (Icc 0 1 ×ˢ Icc (1 / 2) 1) (σ '' (Icc 0 1 ×ˢ Icc 0 1)) :=
    isPLHomeomorphOn_squareUpperHalf.trans hσ
  have hf₁0 : (S₁ ∘ fun q : ℝ × ℝ => (q.1, 2 * q.2)) '' (Icc 0 1 ×ˢ {0}) = a '' Icc 0 1 := by
    rw [image_prod_singleton_eq]
    refine image_congr fun t ht' => ?_
    change S₁ (t, 2 * 0) = a t
    rw [mul_zero]
    exact hS₁0 t ht'
  have hσtop : (fun t => σ (t, 1)) '' Icc (0 : ℝ) 1 = a '' Icc 0 1 := by
    rcases hσ1 with h1 | h1
    · exact image_congr fun t ht' => h1 t ht'
    · rw [image_congr fun t ht' => h1 t ht']
      exact image_one_sub_eq
  have hg₁1 : (σ ∘ fun q : ℝ × ℝ => (q.1, 2 * q.2 - 1)) '' (Icc 0 1 ×ˢ {1}) =
      a '' Icc 0 1 := by
    rw [image_prod_singleton_eq, ← hσtop]
    refine image_congr fun t _ => ?_
    change σ (t, 2 * 1 - 1) = σ (t, 1)
    norm_num
  have hf₁m : (S₁ ∘ fun q : ℝ × ℝ => (q.1, 2 * q.2)) '' (Icc 0 1 ×ˢ {1 / 2}) =
      γ '' Icc 0 1 := by
    rw [image_prod_singleton_eq]
    refine image_congr fun t ht' => ?_
    change S₁ (t, 2 * (1 / 2)) = γ t
    norm_num
    exact hS₁1 t ht'
  have hfg₁ : EqOn (S₁ ∘ fun q : ℝ × ℝ => (q.1, 2 * q.2))
      (σ ∘ fun q : ℝ × ℝ => (q.1, 2 * q.2 - 1)) (Icc 0 1 ×ˢ {1 / 2}) := by
    rintro ⟨t, s⟩ ⟨ht', hs⟩
    have hs' : s = 1 / 2 := hs
    subst hs'
    change S₁ (t, 2 * (1 / 2)) = σ (t, 2 * (1 / 2) - 1)
    norm_num
    rw [hS₁1 t ht', hσ0 t ht']
  obtain ⟨M, hcyl, hMlow, hMup⟩ : ∃ M : ℝ × ℝ → E3,
      IsCylindricalDiagram M (Icc 0 1)
        (S₁ '' (Icc 0 1 ×ˢ Icc 0 1) ∪ σ '' (Icc 0 1 ×ˢ Icc 0 1)) ∧
      (∀ q ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) (1 / 2), M q = S₁ (q.1, 2 * q.2)) ∧
      (∀ q ∉ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) (1 / 2), M q = σ (q.1, 2 * q.2 - 1)) :=
    ⟨_, isCylindricalDiagram_piecewise isHPolytope_Icc.isPolyhedron hf₁ hg₁ hf₁0 hg₁1 hf₁m hfg₁
      hSσ, fun q hq => ite_eq_left hq, fun q hq => ite_eq_right hq⟩
  obtain ⟨TN, _, hTN, hTNor, hTNsp⟩ := ht.exists_isOrientable_frontier hconn
  have hsubN : S₁ '' (Icc 0 1 ×ˢ Icc 0 1) ∪ σ '' (Icc 0 1 ×ˢ Icc 0 1) ⊆ TN.space := by
    rw [hTNsp]
    refine union_subset (hS₁sub.trans (iUnion₂_subset fun v _ => inter_subset_right))
      (hσsub.trans inter_subset_right)
  have hσ1' : ∀ t ∈ Icc (0 : ℝ) 1, σ (t, 1) = a t := by
    rcases hσ1 with h1 | h1
    · exact h1
    · exfalso
      have hfu : ∀ t ∈ Icc (0 : ℝ) 1, M (t, 0) = M ((fun s : ℝ => 1 - s) t, 1) := by
        intro t ht'
        have ht'' : 1 - t ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht'.2], by linarith [ht'.1]⟩
        rw [hMlow _ (hlow t ht'), hMup _ (hnotlow _)]
        change S₁ (t, 2 * 0) = σ (1 - t, 2 * 1 - 1)
        norm_num
        rw [hS₁0 t ht', h1 (1 - t) ht'', sub_sub_cancel]
      have hend := (hcyl.endMap_endpoints_of_isOrientable TN hTN hTNor hsubN
        isPLHomeomorphOn_one_sub_Icc hfu).1
      norm_num at hend
  have hfwa : ∀ t ∈ Icc (0 : ℝ) 1, fw (a t) = f (a (1 - t)) := fun t ht' => by
    rw [hfwe (a t) (hac ⟨t, ht', rfl⟩), hra t ht']
  have hfwaim : fw '' (a '' Icc 0 1) = f '' (a '' Icc 0 1) :=
    calc fw '' (a '' Icc 0 1) = (fun t => fw (a t)) '' Icc 0 1 := image_image _ _ _
      _ = (fun t => f (a (1 - t))) '' Icc 0 1 := image_congr fun t ht' => hfwa t ht'
      _ = f '' ((fun t => a (1 - t)) '' Icc 0 1) := (image_image _ _ _).symm
      _ = f '' (a '' Icc 0 1) := by rw [image_one_sub_eq]
  have hfwγ : fw '' (γ '' Icc 0 1) = f '' (γ '' Icc 0 1) :=
    image_congr fun y hy => hfw₀ (hγc hy)
  have hf₂ := hf₁.trans (hf.restrict hS₁poly hS₁W)
  have hg₂ := hg₁.trans (hfw.restrict hσpoly hσsub)
  have hf₂0 : (f ∘ (S₁ ∘ fun q : ℝ × ℝ => (q.1, 2 * q.2))) '' (Icc 0 1 ×ˢ {0}) =
      f '' (a '' Icc 0 1) := by
    rw [image_comp, hf₁0]
  have hg₂1 : (fw ∘ (σ ∘ fun q : ℝ × ℝ => (q.1, 2 * q.2 - 1))) '' (Icc 0 1 ×ˢ {1}) =
      f '' (a '' Icc 0 1) := by
    rw [image_comp, hg₁1, hfwaim]
  have hf₂m : (f ∘ (S₁ ∘ fun q : ℝ × ℝ => (q.1, 2 * q.2))) '' (Icc 0 1 ×ˢ {1 / 2}) =
      f '' (γ '' Icc 0 1) := by
    rw [image_comp, hf₁m]
  have hfg₂ : EqOn (f ∘ (S₁ ∘ fun q : ℝ × ℝ => (q.1, 2 * q.2)))
      (fw ∘ (σ ∘ fun q : ℝ × ℝ => (q.1, 2 * q.2 - 1))) (Icc 0 1 ×ˢ {1 / 2}) := by
    intro q hq
    have hq' := hfg₁ hq
    change f ((S₁ ∘ fun q : ℝ × ℝ => (q.1, 2 * q.2)) q) =
      fw ((σ ∘ fun q : ℝ × ℝ => (q.1, 2 * q.2 - 1)) q)
    rw [hq']
    obtain ⟨t, s⟩ := q
    obtain ⟨ht', hs⟩ := hq
    have hs' : s = 1 / 2 := hs
    subst hs'
    change f (σ (t, 2 * (1 / 2) - 1)) = fw (σ (t, 2 * (1 / 2) - 1))
    norm_num
    rw [hσ0 t ht']
    exact (hfw₀ (hγc ⟨t, ht', rfl⟩)).symm
  have hinter₂ : f '' (S₁ '' (Icc 0 1 ×ˢ Icc 0 1)) ∩ fw '' (σ '' (Icc 0 1 ×ˢ Icc 0 1)) =
      f '' (a '' Icc 0 1) ∪ f '' (γ '' Icc 0 1) := by
    apply Subset.antisymm
    · rintro z ⟨⟨y, hyS, rfl⟩, ⟨y', hyσ, hfy⟩⟩
      obtain ⟨v, hv, hyv⟩ := mem_iUnion₂.mp (hS₁sub hyS)
      have hy'A : y' ∈ frontier (C w) ∩ frontier N := hσsub hyσ
      obtain ⟨g, hg, hgc, hwg, -, hzg⟩ := hd.exists_trace_of_mem_inter w.2 v.2 (hwv v hv)
        (hfw.bijOn.mapsTo hy'A) (by rw [hfy]; exact hfv v (hpW v hv) hyv)
      rw [← hfwrim g ⟨hg, hgc, hwg⟩] at hzg
      obtain ⟨y'', hy'', hfy''⟩ := hzg
      have hyy : y'' = y' := hfw.bijOn.injOn (ht.rim_subset_freeFace hg hgc w.2 hwg hy'') hy'A
        hfy''
      rw [hyy] at hy''
      rw [← hfy]
      rcases hσrim y' hyσ g hg hgc hy'' with hya | hyγ
      · exact Or.inl (by rw [← hfwaim]; exact mem_image_of_mem fw hya)
      · exact Or.inr (by rw [← hfwγ]; exact mem_image_of_mem fw hyγ)
    · refine union_subset (subset_inter (image_mono haS₁) ?_)
        (subset_inter (image_mono hγS₁) ?_)
      · rw [← hfwaim]
        exact image_mono haσ
      · rw [← hfwγ]
        exact image_mono hγσ
  obtain ⟨M₂, hcyl₂, hM₂low, hM₂up⟩ : ∃ M₂ : ℝ × ℝ → E3,
      IsCylindricalDiagram M₂ (Icc 0 1)
        (f '' (S₁ '' (Icc 0 1 ×ˢ Icc 0 1)) ∪ fw '' (σ '' (Icc 0 1 ×ˢ Icc 0 1))) ∧
      (∀ q ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) (1 / 2), M₂ q = f (S₁ (q.1, 2 * q.2))) ∧
      (∀ q ∉ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) (1 / 2), M₂ q = fw (σ (q.1, 2 * q.2 - 1))) :=
    ⟨_, isCylindricalDiagram_piecewise isHPolytope_Icc.isPolyhedron hf₂ hg₂ hf₂0 hg₂1 hf₂m hfg₂
      hinter₂, fun q hq => ite_eq_left hq, fun q hq => ite_eq_right hq⟩
  obtain ⟨TX, _, hTX, hTXor, hTXsp⟩ :=
    exists_isOrientable_frontier_of_isCombinatorialManifoldWithBoundary hXfin hXman hXc
  have hsubX : f '' (S₁ '' (Icc 0 1 ×ˢ Icc 0 1)) ∪ fw '' (σ '' (Icc 0 1 ×ˢ Icc 0 1)) ⊆
      TX.space := by
    rw [hTXsp]
    refine union_subset ((image_mono hS₁W).trans ?_) ((image_mono hσsub).trans ?_)
    · rw [hf.image_eq]
      exact iUnion₂_subset fun v _ => inter_subset_right
    · rw [hfw.image_eq]
      exact inter_subset_right
  have hfu₂ : ∀ t ∈ Icc (0 : ℝ) 1, M₂ (t, 0) = M₂ ((fun s : ℝ => 1 - s) t, 1) := by
    intro t ht'
    have ht'' : 1 - t ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht'.2], by linarith [ht'.1]⟩
    rw [hM₂low _ (hlow t ht'), hM₂up _ (hnotlow _)]
    change f (S₁ (t, 2 * 0)) = fw (σ (1 - t, 2 * 1 - 1))
    norm_num
    rw [hS₁0 t ht', hσ1' (1 - t) ht'', hfwa (1 - t) ht'', sub_sub_cancel]
  have hend := (hcyl₂.endMap_endpoints_of_isOrientable TX hTX hTXor hsubX
    isPLHomeomorphOn_one_sub_Icc hfu₂).1
  norm_num at hend

end DifferentialGeometry.Topology.PiecewiseLinear
