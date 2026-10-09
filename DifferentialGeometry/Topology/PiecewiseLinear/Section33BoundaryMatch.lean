/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryMatchMobius
import DifferentialGeometry.Topology.PiecewiseLinear.HoledSphereExtension
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceCapSphere

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem isPLHomeomorphOn_fst_inl {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {P : Set E} (hP : IsPolyhedron P) :
    IsPLHomeomorphOn Prod.fst (LinearMap.inl ℝ E F '' P) P := by
  have hκ := hP.isPLHomeomorphOn_linearMap_image (LinearMap.inl ℝ E F) LinearMap.inl_injective
  refine hκ.symm.congr ?_
  rintro _ ⟨y, hy, rfl⟩
  rw [hκ.bijOn.invOn_invFunOn.1 hy]
  rfl

section PieceMap

variable {K : Geometry.SimplicialComplex ℝ E3} {N N' : Set E3} {C Cpp : E3 → Set E3}
  {D Dbd Ec Eint Ebd : Finset E3 → Set E3} {h : E3 → E3}
  {XK : Geometry.SimplicialComplex ℝ E3} {AK : E3 → Geometry.SimplicialComplex ℝ E3}

theorem IsHandleDecompositionOfTube.exists_piece_map
    (hd : IsHandleDecompositionOfTube K N C D Dbd h N' Ec Eint Ebd Cpp)
    (h34 : HasSinglePolygonTraces K h Ec XK.space)
    (h56 : HasConnectedHandlePieces K Ec Cpp XK.space AK)
    (hχ : ∀ v ∈ K.vertices, ∀ [Finite (AK v).faces],
      SimplicialComplex.faceEulerChar (AK v).toPreAbstractSimplicialComplex =
        2 - ((edgesAt K v).ncard : ℤ))
    {R : Finset E3 → (Fin 3 → ℝ) → E3}
    (hR : ∀ e ∈ K.faces, e.card = 2 → IsPLHomeomorphOn (R e) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (D e) ∧
      Dbd e = R e '' stdSimplexBoundary 2)
    {w : E3} (hw : w ∈ K.vertices) {e₀ : Finset E3} (he₀ : e₀ ∈ edgesAt K w) {φ : E3 → E3}
    (hφ : IsPLHomeomorphOn φ (Dbd e₀) (Ec e₀ ∩ frontier XK.space)) :
    ∃ G₀ : E3 → E3,
      IsPLHomeomorphOn G₀ (frontier (C w) ∩ frontier N) (Cpp w ∩ frontier XK.space) ∧
      EqOn G₀ φ (Dbd e₀) ∧
      (∀ e ∈ edgesAt K w, G₀ '' Dbd e = Ec e ∩ frontier XK.space) ∧
      ∀ ψ : Finset E3 → E3 → E3,
        (∀ e ∈ edgesAt K w, e ≠ e₀ →
          IsPLHomeomorphOn (ψ e) (Dbd e) (Ec e ∩ frontier XK.space)) →
        (∀ e ∈ edgesAt K w, e ≠ e₀ → IsPLCirclePositive (Ec e ∩ frontier XK.space)
          (ψ e ∘ Function.invFunOn G₀ (Dbd e))) →
        ∃ G : E3 → E3,
          IsPLHomeomorphOn G (frontier (C w) ∩ frontier N) (Cpp w ∩ frontier XK.space) ∧
          EqOn G φ (Dbd e₀) ∧ ∀ e ∈ edgesAt K w, e ≠ e₀ → EqOn G (ψ e) (Dbd e) := by
  classical
  have ht := hd.tube
  let ι := {e // e ∈ edgesAt K w}
  have hfin : (edgesAt K w).Finite := ht.facesFinite.subset fun e he => he.1
  have _ : Finite ι := hfin.to_subtype
  let _ : Fintype ι := Fintype.ofFinite ι
  have hS : IsPLSphere 2 (frontier (C w)) := (ht.dualBall w hw).isPLSphere_frontier (n := 2)
  have hq : ∀ e : ι, IsPLHomeomorphOn (R e.1) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (D e.1) := fun e =>
    (hR e.1 e.2.1 e.2.2.1).1
  have hc : ∀ e : ι, R e.1 '' stdSimplexBoundary 2 = Dbd e.1 := fun e =>
    (hR e.1 e.2.1 e.2.2.1).2.symm
  have hDS : ∀ e : ι, D e.1 ⊆ frontier (C w) := fun e =>
    ht.splitDisk_subset_frontier hw e.2.1 e.2.2.1 e.2.2.2
  have hdis : Pairwise fun e f : ι => Disjoint (D e.1) (D f.1) :=
    fun e f hef => ht.splitDisjoint e.2.1 e.2.2.1 f.2.1 f.2.2.1 fun h => hef (Subtype.ext h)
  have hholed : frontier (C w) \ ⋃ e : ι, (D e.1 \ R e.1 '' stdSimplexBoundary 2) =
      frontier (C w) ∩ frontier N := by
    rw [ht.freeFace_eq_sdiff hw]
    congr 1
    exact iUnion_congr fun e => by rw [hc e]
  obtain ⟨hAKfin, hAKsp, hAKman, hAKconn, hAKbd⟩ := h56.2.2 w hw
  let _ : Finite (AK w).faces := hAKfin.to_subtype
  let J : ι → Set E3 := fun e => Ec e.1 ∩ frontier XK.space
  have hJ : ∀ e : ι, IsPLSphere 1 (J e) := fun e => (h34 e.1 e.2.1 e.2.2.1).1
  have hJdis : Pairwise fun e f : ι => Disjoint (J e) (J f) := fun e f hef =>
    (hd.pseudoCellDisjoint e.1 e.2.1 e.2.2.1 f.1 f.2.1 f.2.2.1 fun h => hef (Subtype.ext h)).mono
      inter_subset_left inter_subset_left
  have hbd : (boundaryComplex 2 (AK w)).space = ⋃ e : ι, J e := by
    rw [hAKbd]
    ext y
    simp only [mem_iUnion, exists_prop, J]
    constructor
    · rintro ⟨e, he, hy⟩
      exact ⟨⟨e, he⟩, hy⟩
    · rintro ⟨e, hy⟩
      exact ⟨e.1, e.2, hy⟩
  have hχw : SimplicialComplex.faceEulerChar (AK w).toPreAbstractSimplicialComplex =
      2 - Nat.card ι := by
    rw [hχ w hw, Nat.card_coe_set_eq]
  obtain ⟨S', D', q', hS', hS'eq, hq', hq'bd, hD'M, hD'dis⟩ :=
    hAKman.exists_isPLSphere_cap (AK w) hAKconn J hJ hJdis (by convert hbd using 3) hχw
  let κ : E3 →ₗ[ℝ] E3 × (ι → ℝ) := LinearMap.inl ℝ E3 (ι → ℝ)
  have hD'S' : ∀ e : ι, D' e ⊆ S' := fun e => by
    rw [hS'eq]
    exact subset_union_of_subset_right (subset_iUnion D' e) _
  have hA'poly : IsPolyhedron (Cpp w ∩ frontier XK.space) := by
    rw [← hAKsp]
    exact isPolyhedron_space (AK w)
  have hholed' : S' \ ⋃ e : ι, (D' e \ q' e '' stdSimplexBoundary 2) =
      κ '' (Cpp w ∩ frontier XK.space) := by
    rw [← hAKsp]
    apply Subset.antisymm
    · rintro y ⟨hyS, hy⟩
      rw [hS'eq] at hyS
      rcases hyS with hyA | hyD
      · exact hyA
      · obtain ⟨e, hye⟩ := mem_iUnion.mp hyD
        have hyc : y ∈ q' e '' stdSimplexBoundary 2 := by
          by_contra hyc
          exact hy (mem_iUnion.mpr ⟨e, hye, hyc⟩)
        rw [hq'bd e] at hyc
        obtain ⟨z, hz, rfl⟩ := hyc
        exact ⟨z, (boundaryComplex_space_subset 2 (AK w)) (hbd ▸ mem_iUnion.mpr ⟨e, hz⟩), rfl⟩
    · intro y hy
      refine ⟨by rw [hS'eq]; exact Or.inl hy, ?_⟩
      simp only [mem_iUnion, not_exists]
      intro e hye
      exact hye.2 (by rw [hq'bd e, ← hD'M e]; exact ⟨hye.1, hy⟩)
  have hc' : ∀ e : ι, q' e '' stdSimplexBoundary 2 = κ '' J e := hq'bd
  have hJpoly : ∀ e : ι, IsPolyhedron (J e) := fun e => (hJ e).isPolyhedron
  have hκJ : ∀ e : ι, IsPLHomeomorphOn κ (J e) (κ '' J e) := fun e =>
    (hJpoly e).isPLHomeomorphOn_linearMap_image κ LinearMap.inl_injective
  let i₀ : ι := ⟨e₀, he₀⟩
  have hφF : IsPLHomeomorphOn (κ ∘ φ) (R i₀.1 '' stdSimplexBoundary 2)
      (q' i₀ '' stdSimplexBoundary 2) := by
    rw [hc i₀, hc' i₀]
    exact hφ.trans (hκJ i₀)
  obtain ⟨G₀F, hG₀F, hG₀Fφ, hG₀Fc, hextF⟩ := hS.exists_isPLHomeomorphOn_holed hS'
    (D := fun e => D e.1) (q := fun e => R e.1) hq hq' hDS hD'S' hdis hD'dis i₀ hφF
  rw [hholed, hholed'] at hG₀F
  have hfst := isPLHomeomorphOn_fst_inl (F := ι → ℝ) hA'poly
  have hG₀Fc' : ∀ e : ι, G₀F '' Dbd e.1 = κ '' J e := fun e => by
    have h1 := hG₀Fc e
    rwa [hc e, hc' e] at h1
  have hrimA : ∀ e : ι, Dbd e.1 ⊆ frontier (C w) ∩ frontier N := fun e =>
    ht.rim_subset_freeFace e.2.1 e.2.2.1 hw e.2.2.2
  have hG₀img : ∀ e : ι, (Prod.fst ∘ G₀F) '' Dbd e.1 = J e := fun e => by
    rw [image_comp, hG₀Fc' e, image_image]
    exact image_id' _
  have hG₀Fκ : ∀ e : ι, ∀ x ∈ Dbd e.1, G₀F x = κ (G₀F x).1 := by
    intro e x hx
    obtain ⟨y, -, hy⟩ := (hG₀Fc' e).subset (mem_image_of_mem G₀F hx)
    rw [← hy]
    rfl
  refine ⟨Prod.fst ∘ G₀F, hG₀F.trans hfst, ?_, fun e he => hG₀img ⟨e, he⟩, ?_⟩
  · intro y hy
    have hy' : y ∈ R i₀.1 '' stdSimplexBoundary 2 := by rw [hc i₀]; exact hy
    change (G₀F y).1 = φ y
    rw [hG₀Fφ hy']
    rfl
  · intro ψ hψ hpos
    let ψF : ι → E3 → E3 × (ι → ℝ) := fun e => κ ∘ ψ e.1
    have hψF : ∀ e : ι, e ≠ i₀ → IsPLHomeomorphOn (ψF e) (R e.1 '' stdSimplexBoundary 2)
        (q' e '' stdSimplexBoundary 2) := by
      intro e he
      rw [hc e, hc' e]
      exact (hψ e.1 e.2 fun h => he (Subtype.ext h)).trans (hκJ e)
    have hposF : ∀ e : ι, e ≠ i₀ → IsPLCirclePositive (q' e '' stdSimplexBoundary 2)
        (ψF e ∘ Function.invFunOn G₀F (R e.1 '' stdSimplexBoundary 2)) := by
      intro e he
      have hne : e.1 ≠ e₀ := fun h => he (Subtype.ext h)
      have hψe := hψ e.1 e.2 hne
      have hsurj : SurjOn (Prod.fst ∘ G₀F) (Dbd e.1) (J e) := (hG₀img e) ▸ surjOn_image _ _
      have hmu : MapsTo (ψ e.1 ∘ Function.invFunOn (Prod.fst ∘ G₀F) (Dbd e.1)) (J e) (J e) :=
        fun y hy => hψe.bijOn.mapsTo (hsurj.mapsTo_invFunOn hy)
      have h1 := (hpos e.1 e.2 hne).conj hmu (hκJ e).isPiecewiseAffineOn.continuousOn
        (hκJ e).bijOn
      rw [hc e, hc' e]
      refine h1.of_eqOn ?_
      rintro _ ⟨y, hy, rfl⟩
      have hx := hsurj.mapsTo_invFunOn hy
      have hGx : (Prod.fst ∘ G₀F) (Function.invFunOn (Prod.fst ∘ G₀F) (Dbd e.1) y) = y :=
        hsurj.rightInvOn_invFunOn hy
      have hGFx : G₀F (Function.invFunOn (Prod.fst ∘ G₀F) (Dbd e.1) y) = κ y := by
        rw [hG₀Fκ e _ hx]
        exact congrArg κ hGx
      have hinj : InjOn G₀F (Dbd e.1) := hG₀F.bijOn.injOn.mono (hrimA e)
      have hinv : Function.invFunOn G₀F (Dbd e.1) (κ y) =
          Function.invFunOn (Prod.fst ∘ G₀F) (Dbd e.1) y := by
        rw [← hGFx]
        exact hinj.leftInvOn_invFunOn hx
      change κ (ψ e.1 (Function.invFunOn G₀F (Dbd e.1) (κ y))) =
        κ (ψ e.1 (Function.invFunOn (Prod.fst ∘ G₀F) (Dbd e.1)
          (Function.invFunOn κ (J e) (κ y))))
      rw [hinv, (hκJ e).bijOn.invOn_invFunOn.1 hy]
    obtain ⟨GF, hGF, hGFφ, hGFψ⟩ := hextF ψF hψF hposF
    rw [hholed, hholed'] at hGF
    refine ⟨Prod.fst ∘ GF, hGF.trans hfst, ?_, ?_⟩
    · intro y hy
      have hy' : y ∈ R i₀.1 '' stdSimplexBoundary 2 := by rw [hc i₀]; exact hy
      change (GF y).1 = φ y
      rw [hGFφ hy']
      rfl
    · intro e he hne y hy
      have hy' : y ∈ R e '' stdSimplexBoundary 2 := by rw [hc ⟨e, he⟩]; exact hy
      change (GF y).1 = ψ e y
      rw [hGFψ ⟨e, he⟩ (fun h => hne (congrArg Subtype.val h)) hy']
      rfl

theorem IsHandleDecompositionOfTube.exists_boundaryMatch_step
    (hd : IsHandleDecompositionOfTube K N C D Dbd h N' Ec Eint Ebd Cpp)
    (hconn : IsConnected K.space) (h2 : IsPolyhedralTubeNeighborhood K h N' Ec Eint Ebd XK)
    (h34 : HasSinglePolygonTraces K h Ec XK.space)
    (h56 : HasConnectedHandlePieces K Ec Cpp XK.space AK)
    (hχ : ∀ v ∈ K.vertices, ∀ [Finite (AK v).faces],
      SimplicialComplex.faceEulerChar (AK v).toPreAbstractSimplicialComplex =
        2 - ((edgesAt K v).ncard : ℤ))
    {R : Finset E3 → (Fin 3 → ℝ) → E3}
    (hR : ∀ e ∈ K.faces, e.card = 2 → IsPLHomeomorphOn (R e) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (D e) ∧
      Dbd e = R e '' stdSimplexBoundary 2)
    {W : Finset K.vertices} {f : E3 → E3}
    (hf : ∀ v ∈ W,
      IsPLHomeomorphOn f (frontier (C v) ∩ frontier N) (Cpp v ∩ frontier XK.space))
    (hfrim : ∀ v ∈ W, ∀ e ∈ edgesAt K v, f '' Dbd e = Ec e ∩ frontier XK.space)
    (hW : ∀ u ∈ W, ∀ v ∈ W, ∃ p : (SimplicialComplex.edgeGraph K).Walk u v,
      p.IsPath ∧ ∀ z ∈ p.support, z ∈ W)
    {w x₀ : K.vertices} (hw : w ∉ W) (hx₀ : x₀ ∈ W)
    (hadj : (SimplicialComplex.edgeGraph K).Adj x₀ w) :
    ∃ f' : E3 → E3,
      (∀ v ∈ insert w W,
        IsPLHomeomorphOn f' (frontier (C v) ∩ frontier N) (Cpp v ∩ frontier XK.space)) ∧
      ∀ v ∈ insert w W, ∀ e ∈ edgesAt K v, f' '' Dbd e = Ec e ∩ frontier XK.space := by
  classical
  have ht := hd.tube
  have hx₀w : (x₀ : E3) ≠ w := fun h => hadj.1 (Subtype.ext h)
  have he₀F : ({(x₀ : E3), (w : E3)} : Finset E3) ∈ K.faces := by
    have h := hadj.2
    rwa [classical_insert_singleton_eq_pair] at h
  have he₀w : ({(x₀ : E3), (w : E3)} : Finset E3) ∈ edgesAt K w :=
    ⟨he₀F, Finset.card_pair hx₀w, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩
  have hx₀e₀ : (x₀ : E3) ∈ ({(x₀ : E3), (w : E3)} : Finset E3) := Finset.mem_insert_self _ _
  have hrimpoly : ∀ e ∈ edgesAt K w, IsPolyhedron (Dbd e) := fun e he => by
    rw [(hR e he.1 he.2.1).2]
    exact ((hR e he.1 he.2.1).1.isPLSphere_image_stdSimplexBoundary (n := 1)).isPolyhedron
  have hfrimPL : ∀ e ∈ edgesAt K w, (∃ v ∈ W, (v : E3) ∈ e) →
      IsPLHomeomorphOn f (Dbd e) (Ec e ∩ frontier XK.space) := by
    rintro e he ⟨v, hv, hve⟩
    have h1 := (hf v hv).restrict (hrimpoly e he)
      (ht.rim_subset_freeFace he.1 he.2.1 v.2 hve)
    rwa [hfrim v hv e ⟨he.1, he.2.1, hve⟩] at h1
  obtain ⟨G₀, hG₀, hG₀φ, hG₀rim, hext⟩ := hd.exists_piece_map h34 h56 hχ hR w.2 he₀w
    (hfrimPL _ he₀w ⟨x₀, hx₀, hx₀e₀⟩)
  have hG₀g : ∀ g ∈ edgesAt K w, IsPLHomeomorphOn G₀ (Dbd g) (Ec g ∩ frontier XK.space) := by
    intro g hg
    have h1 := hG₀.restrict (hrimpoly g hg) (ht.rim_subset_freeFace hg.1 hg.2.1 w.2 hg.2.2)
    rwa [hG₀rim g hg] at h1
  have hJsph : ∀ g ∈ edgesAt K w, IsPLSphere 1 (Ec g ∩ frontier XK.space) := fun g hg =>
    (h34 g hg.1 hg.2.1).1
  have hG₀pos : ∀ g ∈ edgesAt K w, IsPLCirclePositive (Ec g ∩ frontier XK.space)
      (G₀ ∘ Function.invFunOn G₀ (Dbd g)) := fun g hg =>
    (isPLCirclePositive_id (hJsph g hg)).of_eqOn fun z hz =>
      (hG₀g g hg).bijOn.surjOn.rightInvOn_invFunOn hz
  have hXpoly : ∀ v ∈ K.vertices, IsPolyhedron (Cpp v ∩ frontier XK.space) := fun v hv => by
    obtain ⟨hfin, hsp, -⟩ := h56.2.2 v hv
    let _ : Finite (AK v).faces := hfin.to_subtype
    rw [← hsp]
    exact isPolyhedron_space (AK v)
  have hgood : ∀ e ∈ edgesAt K w, e ≠ {(x₀ : E3), (w : E3)} → (∃ v ∈ W, (v : E3) ∈ e) →
      IsPLCirclePositive (Ec e ∩ frontier XK.space) (f ∘ Function.invFunOn G₀ (Dbd e)) := by
    by_contra hbad
    push Not at hbad
    obtain ⟨e, he, hne, ⟨x, hx, hxe⟩, hnpos⟩ := hbad
    have hrefl : ∀ g ∈ edgesAt K w, ∃ (r : E3 → E3) (a : ℝ → E3),
        IsPLHomeomorphOn r (Dbd g) (Dbd g) ∧ ¬ IsPLCirclePositive (Dbd g) r ∧
        IsPLHomeomorphOn a (Icc 0 1) (a '' Icc 0 1) ∧ a '' Icc 0 1 ⊆ Dbd g ∧
        ∀ t ∈ Icc (0 : ℝ) 1, r (a t) = a (1 - t) := by
      intro g hg
      have hsph : IsPLSphere 1 (Dbd g) := by
        rw [(hR g hg.1 hg.2.1).2]
        exact (hR g hg.1 hg.2.1).1.isPLSphere_image_stdSimplexBoundary (n := 1)
      obtain ⟨r, A, a, hr, hnr, -, ha, hAS, hra⟩ := exists_isPLHomeomorphOn_reflection_arc hsph
      rw [← ha.image_eq] at hAS
      exact ⟨r, a, hr, hnr, by rw [ha.image_eq]; exact ha, hAS, hra⟩
    choose! r a hr hnr ha hac hra using hrefl
    let pos : Finset E3 → Prop := fun g =>
      IsPLCirclePositive (Ec g ∩ frontier XK.space) (f ∘ Function.invFunOn G₀ (Dbd g))
    let ψ : Finset E3 → E3 → E3 := fun g =>
      if (∃ v ∈ W, (v : E3) ∈ g) then (if pos g then f else f ∘ r g) else G₀
    have hflip : ∀ g ∈ edgesAt K w, (∃ v ∈ W, (v : E3) ∈ g) → ¬ pos g →
        IsPLCirclePositive (Ec g ∩ frontier XK.space)
          ((f ∘ r g) ∘ Function.invFunOn G₀ (Dbd g)) := by
      intro g hg hpre hng
      have hu : IsPLHomeomorphOn (f ∘ Function.invFunOn G₀ (Dbd g))
          (Ec g ∩ frontier XK.space) (Ec g ∩ frontier XK.space) :=
        (hG₀g g hg).symm.trans (hfrimPL g hg hpre)
      have hv : IsPLHomeomorphOn (G₀ ∘ r g ∘ Function.invFunOn G₀ (Dbd g))
          (Ec g ∩ frontier XK.space) (Ec g ∩ frontier XK.space) :=
        (hG₀g g hg).symm.trans ((hr g hg).trans (hG₀g g hg))
      have hnv : ¬ IsPLCirclePositive (Ec g ∩ frontier XK.space)
          (G₀ ∘ r g ∘ Function.invFunOn G₀ (Dbd g)) := by
        intro hpv
        apply hnr g hg
        have hc := hpv.conj hv.bijOn.mapsTo (hG₀g g hg).symm.isPiecewiseAffineOn.continuousOn
          (hG₀g g hg).symm.bijOn
        refine hc.of_eqOn fun y hy => ?_
        have hGy : G₀ y ∈ Ec g ∩ frontier XK.space := (hG₀g g hg).bijOn.mapsTo hy
        have h1 : Function.invFunOn (Function.invFunOn G₀ (Dbd g))
            (Ec g ∩ frontier XK.space) y = G₀ y := by
          have h := (hG₀g g hg).symm.bijOn.injOn.leftInvOn_invFunOn hGy
          rwa [(hG₀g g hg).bijOn.invOn_invFunOn.1 hy] at h
        change r g y = Function.invFunOn G₀ (Dbd g) (G₀ (r g (Function.invFunOn G₀ (Dbd g)
          (Function.invFunOn (Function.invFunOn G₀ (Dbd g)) (Ec g ∩ frontier XK.space) y))))
        rw [h1, (hG₀g g hg).bijOn.invOn_invFunOn.1 hy,
          (hG₀g g hg).bijOn.invOn_invFunOn.1 ((hr g hg).bijOn.mapsTo hy)]
      have hcomp := isPLCirclePositive_comp_of_not_isPLCirclePositive (u := f ∘
        Function.invFunOn G₀ (Dbd g)) (v := G₀ ∘ r g ∘ Function.invFunOn G₀ (Dbd g))
        (hJsph g hg) hu hv hng hnv
      refine hcomp.of_eqOn fun z hz => ?_
      have hz' : Function.invFunOn G₀ (Dbd g) z ∈ Dbd g :=
        (hG₀g g hg).bijOn.surjOn.mapsTo_invFunOn hz
      change f (r g (Function.invFunOn G₀ (Dbd g) z)) = f (Function.invFunOn G₀ (Dbd g)
        (G₀ (r g (Function.invFunOn G₀ (Dbd g) z))))
      rw [(hG₀g g hg).bijOn.invOn_invFunOn.1 ((hr g hg).bijOn.mapsTo hz')]
    have hψ1 : ∀ g, (∃ v ∈ W, (v : E3) ∈ g) → pos g → ψ g = f := fun g h1 h2 => by
      simp only [ψ, ite_eq_left h1, ite_eq_left h2]
    have hψ2 : ∀ g, (∃ v ∈ W, (v : E3) ∈ g) → ¬ pos g → ψ g = f ∘ r g := fun g h1 h2 => by
      simp only [ψ, ite_eq_left h1, ite_eq_right h2]
    have hψ3 : ∀ g, ¬ (∃ v ∈ W, (v : E3) ∈ g) → ψ g = G₀ := fun g h1 => by
      simp only [ψ, ite_eq_right h1]
    have hψ : ∀ g ∈ edgesAt K w, g ≠ {(x₀ : E3), (w : E3)} →
        IsPLHomeomorphOn (ψ g) (Dbd g) (Ec g ∩ frontier XK.space) := by
      intro g hg _
      by_cases hpre : ∃ v ∈ W, (v : E3) ∈ g
      · by_cases hp : pos g
        · rw [hψ1 g hpre hp]
          exact hfrimPL g hg hpre
        · rw [hψ2 g hpre hp]
          exact (hr g hg).trans (hfrimPL g hg hpre)
      · rw [hψ3 g hpre]
        exact hG₀g g hg
    have hψpos : ∀ g ∈ edgesAt K w, g ≠ {(x₀ : E3), (w : E3)} →
        IsPLCirclePositive (Ec g ∩ frontier XK.space) (ψ g ∘ Function.invFunOn G₀ (Dbd g)) := by
      intro g hg _
      by_cases hpre : ∃ v ∈ W, (v : E3) ∈ g
      · by_cases hp : pos g
        · rw [hψ1 g hpre hp]
          exact hp
        · rw [hψ2 g hpre hp]
          exact hflip g hg hpre hp
      · rw [hψ3 g hpre]
        exact hG₀pos g hg
    obtain ⟨G, hG, hGφ, hGψ⟩ := hext ψ hψ hψpos
    have hGrim : ∀ g ∈ edgesAt K w, G '' Dbd g = Ec g ∩ frontier XK.space := by
      intro g hg
      by_cases hge : g = {(x₀ : E3), (w : E3)}
      · subst hge
        rw [image_congr hGφ]
        exact (hfrimPL _ he₀w ⟨x₀, hx₀, hx₀e₀⟩).image_eq
      · rw [image_congr (hGψ g hg hge)]
        exact (hψ g hg hge).image_eq
    have hfPi := hd.isPLHomeomorphOn_iUnion_freeFace hXpoly W hf hfrim
    obtain ⟨p, hp, hpW⟩ := hW x hx x₀ hx₀
    have hGe : ∀ y ∈ Dbd e, G y = f (r e y) := by
      intro y hy
      rw [hGψ e he hne hy, hψ2 e ⟨x, hx, hxe⟩ hnpos]
      rfl
    exact hd.false_of_reversed_rim hconn h2.facesFinite h2.isManifold h56.2.1 hR hfPi
      (fun v hv => (hf v hv).bijOn.mapsTo) hw hx hx₀ he hxe he₀w hx₀e₀ hne p hp hpW hG hGrim
      hGφ (hr e he) (hnr e he) (ha e he) (hac e he) (hra e he) hGe
  let ψ : Finset E3 → E3 → E3 := fun g => if (∃ v ∈ W, (v : E3) ∈ g) then f else G₀
  have hψ1 : ∀ g, (∃ v ∈ W, (v : E3) ∈ g) → ψ g = f := fun g h1 => by
    simp only [ψ, ite_eq_left h1]
  have hψ3 : ∀ g, ¬ (∃ v ∈ W, (v : E3) ∈ g) → ψ g = G₀ := fun g h1 => by
    simp only [ψ, ite_eq_right h1]
  have hψ : ∀ g ∈ edgesAt K w, g ≠ {(x₀ : E3), (w : E3)} →
      IsPLHomeomorphOn (ψ g) (Dbd g) (Ec g ∩ frontier XK.space) := by
    intro g hg _
    by_cases hpre : ∃ v ∈ W, (v : E3) ∈ g
    · rw [hψ1 g hpre]
      exact hfrimPL g hg hpre
    · rw [hψ3 g hpre]
      exact hG₀g g hg
  have hψpos : ∀ g ∈ edgesAt K w, g ≠ {(x₀ : E3), (w : E3)} →
      IsPLCirclePositive (Ec g ∩ frontier XK.space) (ψ g ∘ Function.invFunOn G₀ (Dbd g)) := by
    intro g hg hne
    by_cases hpre : ∃ v ∈ W, (v : E3) ∈ g
    · rw [hψ1 g hpre]
      exact hgood g hg hne hpre
    · rw [hψ3 g hpre]
      exact hG₀pos g hg
  obtain ⟨G, hG, hGφ, hGψ⟩ := hext ψ hψ hψpos
  have hGrim : ∀ g ∈ edgesAt K w, G '' Dbd g = Ec g ∩ frontier XK.space := by
    intro g hg
    by_cases hge : g = {(x₀ : E3), (w : E3)}
    · subst hge
      rw [image_congr hGφ]
      exact (hfrimPL _ he₀w ⟨x₀, hx₀, hx₀e₀⟩).image_eq
    · rw [image_congr (hGψ g hg hge)]
      exact (hψ g hg hge).image_eq
  have hGf : ∀ v ∈ W, EqOn G f ((frontier (C w) ∩ frontier N) ∩ (frontier (C v) ∩ frontier N)) := by
    intro v hv y hy
    have hwv : (w : E3) ≠ v := fun h => hw (Subtype.ext h ▸ hv)
    obtain ⟨g, hg, hgc, hwg, hvg, hyg⟩ := ht.exists_rim_of_mem_freeFace_inter w.2 v.2 hwv hy.1 hy.2
    by_cases hge : g = {(x₀ : E3), (w : E3)}
    · subst hge
      exact hGφ hyg
    · rw [hGψ g ⟨hg, hgc, hwg⟩ hge hyg, hψ1 g ⟨v, hv, hvg⟩]
  refine ⟨(frontier (C w) ∩ frontier N).piecewise G f, ?_, ?_⟩
  · intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact hG.congr fun y hy => piecewise_eq_of_mem _ _ _ hy
    · refine (hf v hv).congr fun y hy => ?_
      by_cases hyw : y ∈ frontier (C w) ∩ frontier N
      · rw [piecewise_eq_of_mem _ _ _ hyw]
        exact hGf v hv ⟨hyw, hy⟩
      · exact piecewise_eq_of_notMem _ _ _ hyw
  · intro v hv g hg
    rcases Finset.mem_insert.mp hv with rfl | hv
    · refine (image_congr fun y hy => ?_).trans (hGrim g hg)
      exact piecewise_eq_of_mem _ _ _
        (ht.rim_subset_freeFace hg.1 hg.2.1 (Subtype.coe_prop _) hg.2.2 hy)
    · rw [← hfrim v hv g hg]
      refine image_congr fun y hy => ?_
      have hyv := ht.rim_subset_freeFace hg.1 hg.2.1 v.2 hg.2.2 hy
      by_cases hyw : y ∈ frontier (C w) ∩ frontier N
      · rw [piecewise_eq_of_mem _ _ _ hyw]
        exact hGf v hv ⟨hyw, hyv⟩
      · exact piecewise_eq_of_notMem _ _ _ hyw

end PieceMap

section Leaves

variable {K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))}
  {N N' : Set (EuclideanSpace ℝ (Fin 3))}
  {C Cpp : EuclideanSpace ℝ (Fin 3) → Set (EuclideanSpace ℝ (Fin 3))}
  {D Dbd Ec Eint Ebd : Finset (EuclideanSpace ℝ (Fin 3)) → Set (EuclideanSpace ℝ (Fin 3))}
  {h : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
  {XK : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))}
  {AK : EuclideanSpace ℝ (Fin 3) → Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))}

theorem exists_section33BoundaryMatch
    (hd : IsHandleDecompositionOfTube K N C D Dbd h N' Ec Eint Ebd Cpp)
    (hconn : IsConnected K.space)
    (h2 : IsPolyhedralTubeNeighborhood K h N' Ec Eint Ebd XK)
    (h34 : HasSinglePolygonTraces K h Ec XK.space)
    (h56 : HasConnectedHandlePieces K Ec Cpp XK.space AK)
    (hχ : ∀ v ∈ K.vertices, ∀ [Finite (AK v).faces],
      SimplicialComplex.faceEulerChar (AK v).toPreAbstractSimplicialComplex =
        2 - ((edgesAt K v).ncard : ℤ)) :
    ∃ g : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3),
      IsPLHomeomorphOn g (frontier N) (frontier XK.space) ∧
      (∀ v ∈ K.vertices, g '' (frontier (C v) ∩ frontier N) = Cpp v ∩ frontier XK.space) ∧
      ∀ e ∈ K.faces, e.card = 2 → g '' Dbd e = Ec e ∩ frontier XK.space := by
  classical
  have ht := hd.tube
  have hRex : ∀ e : Finset E3, ∃ R : (Fin 3 → ℝ) → E3, e ∈ K.faces → e.card = 2 →
      IsPLHomeomorphOn R (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (D e) ∧ Dbd e = R '' stdSimplexBoundary 2 := by
    intro e
    by_cases he : e ∈ K.faces ∧ e.card = 2
    · obtain ⟨r, hr, hrb⟩ := ht.splitCell e he.1 he.2
      exact ⟨r, fun _ _ => ⟨hr, hrb⟩⟩
    · exact ⟨fun _ => 0, fun h1 h2 => absurd ⟨h1, h2⟩ he⟩
  choose R hR using hRex
  let _ : Finite K.faces := ht.facesFinite.to_subtype
  let _ : Fintype K.vertices := ht.finite_vertices.fintype
  have hgraph := edgeGraph_connected_of_isConnected_space K hconn
  have hXpoly : ∀ v ∈ K.vertices, IsPolyhedron (Cpp v ∩ frontier XK.space) := fun v hv => by
    obtain ⟨hfin, hsp, -⟩ := h56.2.2 v hv
    let _ : Finite (AK v).faces := hfin.to_subtype
    rw [← hsp]
    exact isPolyhedron_space (AK v)
  obtain ⟨e₁, he₁, he₁c⟩ := ht.hasEdge
  obtain ⟨a, hae, b, hbe, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < e₁.card)
  have ha : a ∈ K.vertices :=
    K.down_closed he₁ (Finset.singleton_subset_iff.mpr hae) (Finset.singleton_nonempty a)
  obtain ⟨f₀, hf₀, hf₀rim⟩ : ∃ f₀ : E3 → E3,
      IsPLHomeomorphOn f₀ (frontier (C a) ∩ frontier N) (Cpp a ∩ frontier XK.space) ∧
      ∀ e ∈ edgesAt K a, f₀ '' Dbd e = Ec e ∩ frontier XK.space := by
    have hDsph : IsPLSphere 1 (Dbd e₁) := by
      rw [(hR e₁ he₁ he₁c).2]
      exact (hR e₁ he₁ he₁c).1.isPLSphere_image_stdSimplexBoundary (n := 1)
    obtain ⟨u, hu⟩ := hDsph
    obtain ⟨u', hu'⟩ := (h34 e₁ he₁ he₁c).1
    obtain ⟨G₀, hG₀, -, hG₀rim, -⟩ := hd.exists_piece_map h34 h56 hχ hR ha ⟨he₁, he₁c, hae⟩
      (hu.symm.trans hu')
    exact ⟨G₀, hG₀, hG₀rim⟩
  have hind : ∀ n : ℕ, ∃ (W : Finset K.vertices) (f : E3 → E3),
      (n ≤ W.card ∨ W = Finset.univ) ∧ W.Nonempty ∧
      (∀ v ∈ W,
        IsPLHomeomorphOn f (frontier (C v) ∩ frontier N) (Cpp v ∩ frontier XK.space)) ∧
      (∀ v ∈ W, ∀ e ∈ edgesAt K v, f '' Dbd e = Ec e ∩ frontier XK.space) ∧
      ∀ u ∈ W, ∀ v ∈ W, ∃ p : (SimplicialComplex.edgeGraph K).Walk u v,
        p.IsPath ∧ ∀ z ∈ p.support, z ∈ W := by
    intro n
    induction n with
    | zero =>
      refine ⟨{⟨a, ha⟩}, f₀, Or.inl (Nat.zero_le _), Finset.singleton_nonempty _, ?_, ?_, ?_⟩
      · intro v hv
        rw [Finset.mem_singleton.mp hv]
        exact hf₀
      · intro v hv
        rw [Finset.mem_singleton.mp hv]
        exact hf₀rim
      · intro u hu v hv
        rw [Finset.mem_singleton.mp hu, Finset.mem_singleton.mp hv]
        exact ⟨SimpleGraph.Walk.nil, SimpleGraph.Walk.IsPath.nil, by simp⟩
    | succ n ih =>
      obtain ⟨W, f, hn, hne, hf, hfrim, hW⟩ := ih
      by_cases hWu : W = Finset.univ
      · exact ⟨W, f, Or.inr hWu, hne, hf, hfrim, hW⟩
      · obtain ⟨v, hv⟩ : ∃ v, v ∉ W := by
          by_contra hall
          push Not at hall
          exact hWu (Finset.eq_univ_iff_forall.mpr hall)
        obtain ⟨u, hu⟩ := hne
        obtain ⟨p⟩ := hgraph.preconnected u v
        obtain ⟨d, -, hd1, hd2⟩ := p.exists_boundary_dart (↑W) (Finset.mem_coe.mpr hu)
          (fun h => hv (Finset.mem_coe.mp h))
        have hd1' : d.fst ∈ W := Finset.mem_coe.mp hd1
        have hd2' : d.snd ∉ W := fun h => hd2 (Finset.mem_coe.mpr h)
        obtain ⟨f', hf', hf'rim⟩ := hd.exists_boundaryMatch_step hconn h2 h34 h56 hχ hR hf
          hfrim hW hd2' hd1' d.adj
        refine ⟨insert d.snd W, f', Or.inl ?_, ⟨d.snd, Finset.mem_insert_self _ _⟩, hf', hf'rim,
          ?_⟩
        · rw [Finset.card_insert_of_notMem hd2']
          rcases hn with hn | hn
          · omega
          · exact absurd hn hWu
        · have hto : ∀ z ∈ W, ∃ p : (SimplicialComplex.edgeGraph K).Walk d.snd z,
              p.IsPath ∧ ∀ y ∈ p.support, y ∈ insert d.snd W := by
            intro z hz
            obtain ⟨q, hq, hqW⟩ := hW d.fst hd1' z hz
            refine ⟨SimpleGraph.Walk.cons d.adj.symm q, ?_, ?_⟩
            · exact hq.cons fun h => hd2' (hqW _ h)
            · intro y hy
              rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hy
              rcases hy with rfl | hy
              · exact Finset.mem_insert_self _ _
              · exact Finset.mem_insert_of_mem (hqW y hy)
          intro u hu v hv
          rcases Finset.mem_insert.mp hu with rfl | hu
          · rcases Finset.mem_insert.mp hv with rfl | hv
            · exact ⟨SimpleGraph.Walk.nil, SimpleGraph.Walk.IsPath.nil, by simp⟩
            · exact hto v hv
          · rcases Finset.mem_insert.mp hv with rfl | hv
            · obtain ⟨q, hq, hqW⟩ := hto u hu
              refine ⟨q.reverse, hq.reverse, fun y hy => ?_⟩
              rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hy
              exact hqW y hy
            · obtain ⟨q, hq, hqW⟩ := hW u hu v hv
              exact ⟨q, hq, fun y hy => Finset.mem_insert_of_mem (hqW y hy)⟩
  obtain ⟨W, f, hn, -, hf, hfrim, -⟩ := hind (Fintype.card K.vertices)
  have hWu : W = Finset.univ := by
    rcases hn with hn | hn
    · exact Finset.eq_univ_of_card W (le_antisymm (Finset.card_le_univ W) hn)
    · exact hn
  subst hWu
  have hglue := hd.isPLHomeomorphOn_iUnion_freeFace hXpoly Finset.univ hf hfrim
  have hsrc : ⋃ v ∈ (Finset.univ : Finset K.vertices), frontier (C v) ∩ frontier N =
      frontier N := by
    refine Eq.trans ?_ ht.frontier_eq_iUnion_freeFace.symm
    apply Subset.antisymm
    · exact iUnion₂_subset fun v _ => subset_iUnion₂
        (s := fun v (_ : v ∈ K.vertices) => frontier (C v) ∩ frontier N) v.1 v.2
    · exact iUnion₂_subset fun v hv => subset_iUnion₂
        (s := fun (v : K.vertices) (_ : v ∈ (Finset.univ : Finset K.vertices)) =>
          frontier (C (v : E3)) ∩ frontier N) ⟨v, hv⟩ (Finset.mem_univ _)
  have htgt : ⋃ v ∈ (Finset.univ : Finset K.vertices), Cpp v ∩ frontier XK.space =
      frontier XK.space := by
    apply Subset.antisymm
    · exact iUnion₂_subset fun v _ => inter_subset_right
    · intro y hy
      let _ : Finite XK.faces := h2.facesFinite.to_subtype
      have hyX : y ∈ XK.space :=
        (isPolyhedron_space XK).isClosed.frontier_subset hy
      have hyN' : y ∈ N' := interior_subset (h2.subsetInterior hyX)
      rw [hd.coversTube] at hyN'
      obtain ⟨v, hv, hyv⟩ := mem_iUnion₂.mp hyN'
      exact mem_iUnion₂.mpr ⟨⟨v, hv⟩, Finset.mem_univ _, hyv, hy⟩
  rw [hsrc, htgt] at hglue
  refine ⟨f, hglue, fun v hv => (hf ⟨v, hv⟩ (Finset.mem_univ _)).image_eq, ?_⟩
  intro e he hc
  obtain ⟨u, hue, -, -, -⟩ := Finset.one_lt_card.mp (by omega : 1 < e.card)
  have hu : u ∈ K.vertices :=
    K.down_closed he (Finset.singleton_subset_iff.mpr hue) (Finset.singleton_nonempty u)
  exact hfrim ⟨u, hu⟩ (Finset.mem_univ _) e ⟨he, hc, hue⟩

end Leaves

end DifferentialGeometry.Topology.PiecewiseLinear
