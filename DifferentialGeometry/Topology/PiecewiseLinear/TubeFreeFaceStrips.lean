/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.HoledSphereStrip
import DifferentialGeometry.Topology.PiecewiseLinear.SquareConcat
import DifferentialGeometry.Topology.PiecewiseLinear.TwoComponentsOfPseudoCell
import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedralTubeNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.CircleReflection
import DifferentialGeometry.Topology.SimplicialComplex.EdgeGraph
import Mathlib.Combinatorics.SimpleGraph.Paths

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {K : Geometry.SimplicialComplex ℝ E3} {N N' : Set E3} {C : E3 → Set E3}
  {D Dbd : Finset E3 → Set E3} {h : E3 → E3}

theorem IsTube.rim_subset_splitDisk (ht : IsTube K N C D Dbd h N') {e : Finset E3}
    (he : e ∈ K.faces) (hc : e.card = 2) : Dbd e ⊆ D e := by
  rw [← ht.splitProper e he hc]
  exact inter_subset_left

theorem IsTube.disjoint_rim_rim (ht : IsTube K N C D Dbd h N') {e f : Finset E3}
    (he : e ∈ K.faces) (hec : e.card = 2) (hf : f ∈ K.faces) (hfc : f.card = 2) (hef : e ≠ f) :
    Disjoint (Dbd e) (Dbd f) :=
  (ht.splitDisjoint he hec hf hfc hef).mono (ht.rim_subset_splitDisk he hec)
    (ht.rim_subset_splitDisk hf hfc)

theorem IsTube.freeFace_eq_sdiff (ht : IsTube K N C D Dbd h N') {v : E3} (hv : v ∈ K.vertices) :
    frontier (C v) ∩ frontier N =
      frontier (C v) \ ⋃ e : {e // e ∈ edgesAt K v}, (D e.1 \ Dbd e.1) := by
  ext x
  constructor
  · rintro ⟨hxC, hxN⟩
    refine ⟨hxC, ?_⟩
    intro hmem
    rw [mem_iUnion] at hmem
    obtain ⟨e, hxe⟩ := hmem
    obtain ⟨he1, hec, -⟩ := e.2
    have hxb : x ∈ Dbd e.1 := by
      rw [← ht.splitProper e.1 he1 hec]
      exact ⟨hxe.1, hxN⟩
    exact hxe.2 hxb
  · rintro ⟨hxC, hx⟩
    refine ⟨hxC, ?_⟩
    by_cases hD : ∃ f ∈ K.faces, f.card = 2 ∧ v ∈ f ∧ x ∈ D f
    · obtain ⟨f, hf, hfc, hvf, hxf⟩ := hD
      have hxb : x ∈ Dbd f := by
        by_contra hxb
        exact hx (mem_iUnion.mpr ⟨⟨f, hf, hfc, hvf⟩, hxf, hxb⟩)
      rw [← ht.splitProper f hf hfc] at hxb
      exact hxb.2
    · push Not at hD
      exact ht.mem_frontier_of_mem_frontier_dualCell hv hxC fun f hf hfc hvf => hD f hf hfc hvf

theorem IsTube.frontier_eq_iUnion_freeFace (ht : IsTube K N C D Dbd h N') :
    frontier N = ⋃ v ∈ K.vertices, frontier (C v) ∩ frontier N := by
  apply Subset.antisymm
  · intro x hx
    have hxN := ht.isClosed.frontier_subset hx
    rw [ht.unionEq] at hxN
    obtain ⟨v, hv, hxv⟩ := mem_iUnion₂.mp hxN
    exact mem_iUnion₂.mpr ⟨v, hv, ⟨subset_closure hxv, fun hxi =>
      hx.2 (interior_mono (ht.dualCell_subset hv) hxi)⟩, hx⟩
  · exact iUnion₂_subset fun v _ => inter_subset_right

theorem IsTube.exists_rim_of_mem_freeFace_inter (ht : IsTube K N C D Dbd h N') {u v : E3}
    (hu : u ∈ K.vertices) (hv : v ∈ K.vertices) (huv : u ≠ v) {x : E3}
    (hxu : x ∈ frontier (C u) ∩ frontier N) (hxv : x ∈ frontier (C v) ∩ frontier N) :
    ∃ f ∈ K.faces, f.card = 2 ∧ u ∈ f ∧ v ∈ f ∧ x ∈ Dbd f := by
  have hxCu : x ∈ C u := (ht.dualBall u hu).isPolyhedron.isClosed.frontier_subset hxu.1
  have hxCv : x ∈ C v := (ht.dualBall v hv).isPolyhedron.isClosed.frontier_subset hxv.1
  by_cases hadj : ∃ f ∈ K.faces, u ∈ f ∧ v ∈ f
  · obtain ⟨f, hf, huf, hvf⟩ := hadj
    have hfc := ht.card_eq_two_of_mem hf huf hvf huv
    have hxD : x ∈ D f := ht.inter_eq_of_mem_faces hu hv huv hf huf hvf ▸ ⟨hxCu, hxCv⟩
    exact ⟨f, hf, hfc, huf, hvf, ht.splitProper f hf hfc ▸ ⟨hxD, hxu.2⟩⟩
  · push Not at hadj
    have h0 := ht.inter_eq_empty_of_forall_notMem_faces hu hv huv hadj
    exact absurd (h0 ▸ (⟨hxCu, hxCv⟩ : x ∈ C u ∩ C v)) (notMem_empty x)

theorem IsTube.rim_subset_freeFace (ht : IsTube K N C D Dbd h N') {e : Finset E3}
    (he : e ∈ K.faces) (hc : e.card = 2) {v : E3} (hv : v ∈ K.vertices) (hve : v ∈ e) :
    Dbd e ⊆ frontier (C v) ∩ frontier N := by
  intro x hx
  rw [← ht.splitProper e he hc] at hx
  exact ⟨ht.splitDisk_subset_frontier hv he hc hve hx.1, hx.2⟩

theorem IsTube.disjoint_rim_freeFace (ht : IsTube K N C D Dbd h N') {e : Finset E3}
    (he : e ∈ K.faces) (hc : e.card = 2) {v : E3} (hv : v ∈ K.vertices) (hve : v ∉ e) :
    Disjoint (Dbd e) (frontier (C v) ∩ frontier N) := by
  rw [disjoint_left]
  intro x hxe hxv
  obtain ⟨a, hae, b, hbe, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < e.card)
  have ha : a ∈ K.vertices :=
    K.down_closed he (Finset.singleton_subset_iff.mpr hae) (Finset.singleton_nonempty a)
  have hva : v ≠ a := fun h => hve (h ▸ hae)
  obtain ⟨f, hf, hfc, hvf, haf, hxf⟩ := ht.exists_rim_of_mem_freeFace_inter hv ha hva hxv
    (ht.rim_subset_freeFace he hc ha hae hxe)
  have hfe : f ≠ e := fun h => hve (h ▸ hvf)
  exact disjoint_left.mp (ht.disjoint_rim_rim hf hfc he hc hfe) hxf hxe

theorem IsTube.exists_freeFace_strip (ht : IsTube K N C D Dbd h N')
    {R : Finset E3 → (Fin 3 → ℝ) → E3}
    (hR : ∀ e ∈ K.faces, e.card = 2 → IsPLHomeomorphOn (R e) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (D e) ∧
      Dbd e = R e '' stdSimplexBoundary 2)
    {v : E3} (hv : v ∈ K.vertices) {ein eout : Finset E3} (hein : ein ∈ edgesAt K v)
    (heout : eout ∈ edgesAt K v) (hne : ein ≠ eout) {α β : ℝ → E3}
    (hα : IsPLHomeomorphOn α (Icc 0 1) (α '' Icc 0 1)) (hαc : α '' Icc 0 1 ⊆ Dbd ein)
    (hβ : IsPLHomeomorphOn β (Icc 0 1) (β '' Icc 0 1)) (hβc : β '' Icc 0 1 ⊆ Dbd eout)
    {r : E3 → E3} (hr : IsPLHomeomorphOn r (Dbd eout) (Dbd eout))
    (hnr : ¬ IsPLCirclePositive (Dbd eout) r) (hrβ : ∀ t ∈ Icc (0 : ℝ) 1, r (β t) = β (1 - t)) :
    ∃ σ : ℝ × ℝ → E3,
      IsPLHomeomorphOn σ (Icc 0 1 ×ˢ Icc 0 1) (σ '' (Icc 0 1 ×ˢ Icc 0 1)) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, σ (t, 0) = α t) ∧
      ((∀ t ∈ Icc (0 : ℝ) 1, σ (t, 1) = β t) ∨ ∀ t ∈ Icc (0 : ℝ) 1, σ (t, 1) = β (1 - t)) ∧
      σ '' (Icc 0 1 ×ˢ Icc 0 1) ⊆ frontier (C v) ∩ frontier N ∧
      σ '' (Icc 0 1 ×ˢ Icc 0 1) ∩ Dbd ein = α '' Icc 0 1 ∧
      σ '' (Icc 0 1 ×ˢ Icc 0 1) ∩ Dbd eout = β '' Icc 0 1 ∧
      ∀ f ∈ K.faces, f.card = 2 → f ≠ ein → f ≠ eout →
        Disjoint (σ '' (Icc 0 1 ×ˢ Icc 0 1)) (Dbd f) := by
  classical
  have hS : IsPLSphere 2 (frontier (C v)) := (ht.dualBall v hv).isPLSphere_frontier (n := 2)
  have hfin : (edgesAt K v).Finite := ht.facesFinite.subset fun e he => he.1
  have _ : Finite {e // e ∈ edgesAt K v} := hfin.to_subtype
  have hq : ∀ e : {e // e ∈ edgesAt K v},
      IsPLHomeomorphOn (R e.1) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (D e.1) := fun e =>
    (hR e.1 e.2.1 e.2.2.1).1
  have hc : ∀ e : {e // e ∈ edgesAt K v}, R e.1 '' stdSimplexBoundary 2 = Dbd e.1 := fun e =>
    (hR e.1 e.2.1 e.2.2.1).2.symm
  have hDS : ∀ e : {e // e ∈ edgesAt K v}, D e.1 ⊆ frontier (C v) := fun e =>
    ht.splitDisk_subset_frontier hv e.2.1 e.2.2.1 e.2.2.2
  have hdis : Pairwise fun e f : {e // e ∈ edgesAt K v} => Disjoint (D e.1) (D f.1) :=
    fun e f hef => ht.splitDisjoint e.2.1 e.2.2.1 f.2.1 f.2.2.1 fun h => hef (Subtype.ext h)
  have hj : (⟨eout, heout⟩ : {e // e ∈ edgesAt K v}) ≠ ⟨ein, hein⟩ := fun h =>
    hne (congrArg Subtype.val h).symm
  have hcin : R ein '' stdSimplexBoundary 2 = Dbd ein := hc ⟨ein, hein⟩
  have hcout : R eout '' stdSimplexBoundary 2 = Dbd eout := hc ⟨eout, heout⟩
  have hαc' : α '' Icc 0 1 ⊆ R ein '' stdSimplexBoundary 2 := by
    rw [hcin]
    exact hαc
  have hβc' : β '' Icc 0 1 ⊆ R eout '' stdSimplexBoundary 2 := by
    rw [hcout]
    exact hβc
  have hr' : IsPLHomeomorphOn r (R eout '' stdSimplexBoundary 2)
      (R eout '' stdSimplexBoundary 2) := by
    rw [hcout]
    exact hr
  have hnr' : ¬ IsPLCirclePositive (R eout '' stdSimplexBoundary 2) r := by
    rw [hcout]
    exact hnr
  obtain ⟨σ, hσ, hsub, hint, h0, h1⟩ := hS.exists_holed_strip (D := fun e => D e.1)
    (q := fun e => R e.1) hq hDS hdis hj hα hαc' hβ hβc' hr' hnr' hrβ
  have hholed : frontier (C v) \ ⋃ e : {e // e ∈ edgesAt K v},
      (D e.1 \ R e.1 '' stdSimplexBoundary 2) = frontier (C v) ∩ frontier N := by
    rw [ht.freeFace_eq_sdiff hv]
    congr 1
    exact iUnion_congr fun e => by rw [hc e]
  have hcirc : ⋃ e : {e // e ∈ edgesAt K v}, R e.1 '' stdSimplexBoundary 2 =
      ⋃ e : {e // e ∈ edgesAt K v}, Dbd e.1 := iUnion_congr hc
  rw [hholed] at hsub
  rw [hcirc] at hint
  have hin : Dbd ein ⊆ ⋃ e : {e // e ∈ edgesAt K v}, Dbd e.1 :=
    subset_iUnion (fun e : {e // e ∈ edgesAt K v} => Dbd e.1) ⟨ein, hein⟩
  have hout : Dbd eout ⊆ ⋃ e : {e // e ∈ edgesAt K v}, Dbd e.1 :=
    subset_iUnion (fun e : {e // e ∈ edgesAt K v} => Dbd e.1) ⟨eout, heout⟩
  have hdisio := ht.disjoint_rim_rim hein.1 hein.2.1 heout.1 heout.2.1 hne
  have hbot : α '' Icc 0 1 ⊆ σ '' (Icc 0 1 ×ˢ Icc 0 1) := by
    rintro _ ⟨t, ht', rfl⟩
    exact ⟨(t, 0), ⟨ht', by norm_num⟩, h0 t ht'⟩
  have htop : β '' Icc 0 1 ⊆ σ '' (Icc 0 1 ×ˢ Icc 0 1) := by
    rintro _ ⟨t, ht', rfl⟩
    rcases h1 with h1 | h1
    · exact ⟨(t, 1), ⟨ht', by norm_num⟩, h1 t ht'⟩
    · have ht'' : 1 - t ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht'.2], by linarith [ht'.1]⟩
      refine ⟨(1 - t, 1), ⟨ht'', by norm_num⟩, ?_⟩
      rw [h1 (1 - t) ht'']
      congr 1
      ring
  refine ⟨σ, hσ, h0, h1, hsub, ?_, ?_, ?_⟩
  · apply Subset.antisymm
    · rintro y ⟨hyσ, hyb⟩
      rcases (hint.subset ⟨hyσ, hin hyb⟩ : y ∈ α '' Icc 0 1 ∪ β '' Icc 0 1) with hy | hy
      · exact hy
      · exact absurd (hβc hy) (disjoint_left.mp hdisio hyb)
    · exact subset_inter hbot hαc
  · apply Subset.antisymm
    · rintro y ⟨hyσ, hyb⟩
      rcases (hint.subset ⟨hyσ, hout hyb⟩ : y ∈ α '' Icc 0 1 ∪ β '' Icc 0 1) with hy | hy
      · exact absurd (hαc hy) (disjoint_right.mp hdisio hyb)
      · exact hy
    · exact subset_inter htop hβc
  · intro f hf hfc hfin hfout
    by_cases hvf : v ∈ f
    · rw [disjoint_left]
      intro y hyσ hyf
      have hyf' : y ∈ ⋃ e : {e // e ∈ edgesAt K v}, Dbd e.1 :=
        subset_iUnion (fun e : {e // e ∈ edgesAt K v} => Dbd e.1) ⟨f, hf, hfc, hvf⟩ hyf
      rcases (hint.subset ⟨hyσ, hyf'⟩ : y ∈ α '' Icc 0 1 ∪ β '' Icc 0 1) with hy | hy
      · exact disjoint_left.mp (ht.disjoint_rim_rim hein.1 hein.2.1 hf hfc
          fun h => hfin h.symm) (hαc hy) hyf
      · exact disjoint_left.mp (ht.disjoint_rim_rim heout.1 heout.2.1 hf hfc
          fun h => hfout h.symm) (hβc hy) hyf
    · exact ((ht.disjoint_rim_freeFace hf hfc hv hvf).mono_right hsub).symm

theorem IsTube.exists_freeFace_chain (ht : IsTube K N C D Dbd h N')
    {R : Finset E3 → (Fin 3 → ℝ) → E3}
    (hR : ∀ e ∈ K.faces, e.card = 2 → IsPLHomeomorphOn (R e) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (D e) ∧
      Dbd e = R e '' stdSimplexBoundary 2)
    {x y : K.vertices} (p : (SimplicialComplex.edgeGraph K).Walk x y) :
    p.IsPath → ∀ {ein eout : Finset E3}, ein ∈ edgesAt K x → eout ∈ edgesAt K y → ein ≠ eout →
      (∀ v ∈ p.support, (v : E3) ∈ ein → v = x) → (∀ v ∈ p.support, (v : E3) ∈ eout → v = y) →
      ∀ {α : ℝ → E3}, IsPLHomeomorphOn α (Icc 0 1) (α '' Icc 0 1) → α '' Icc 0 1 ⊆ Dbd ein →
      ∃ (S : ℝ × ℝ → E3) (γ : ℝ → E3),
        IsPLHomeomorphOn S (Icc 0 1 ×ˢ Icc 0 1) (S '' (Icc 0 1 ×ˢ Icc 0 1)) ∧
        (∀ t ∈ Icc (0 : ℝ) 1, S (t, 0) = α t) ∧ (∀ t ∈ Icc (0 : ℝ) 1, S (t, 1) = γ t) ∧
        IsPLHomeomorphOn γ (Icc 0 1) (γ '' Icc 0 1) ∧ γ '' Icc 0 1 ⊆ Dbd eout ∧
        S '' (Icc 0 1 ×ˢ Icc 0 1) ⊆ ⋃ v ∈ p.support, frontier (C v) ∩ frontier N ∧
        S '' (Icc 0 1 ×ˢ Icc 0 1) ∩ Dbd ein = α '' Icc 0 1 ∧
        S '' (Icc 0 1 ×ˢ Icc 0 1) ∩ Dbd eout = γ '' Icc 0 1 ∧
        ∀ f ∈ K.faces, f.card = 2 → f ≠ ein → f ≠ eout →
          (∃ u ∈ f, ∀ v ∈ p.support, (v : E3) ≠ u) →
          Disjoint (S '' (Icc 0 1 ×ˢ Icc 0 1)) (Dbd f) := by
  classical
  have hsqpoly : IsPolyhedron (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :=
    (isHPolytope_Icc.prod isHPolytope_Icc).isPolyhedron
  have htopedge : ∀ {σ : ℝ × ℝ → E3},
      IsPLHomeomorphOn σ (Icc 0 1 ×ˢ Icc 0 1) (σ '' (Icc 0 1 ×ˢ Icc 0 1)) →
      IsPLHomeomorphOn (fun t => σ (t, 1)) (Icc 0 1) ((fun t => σ (t, 1)) '' Icc 0 1) := by
    intro σ hσ
    let emb : ℝ →ᵃ[ℝ] ℝ × ℝ :=
      { toFun := fun t => (t, 1)
        linear := LinearMap.inl ℝ ℝ ℝ
        map_vadd' := fun t w => by simp [vadd_eq_add] }
    have hemb : IsPLHomeomorphOn emb (Icc 0 1) (emb '' Icc 0 1) :=
      isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn isHPolytope_Icc.isPolyhedron
        ((isPiecewiseAffineOn_of_affine emb isOpen_univ).mono_of_isPolyhedron
          isHPolytope_Icc.isPolyhedron (subset_univ _))
        (InjOn.bijOn_image fun s _ t _ hst => congrArg Prod.fst hst)
    have hembsub : emb '' Icc 0 1 ⊆ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 := by
      rintro _ ⟨t, ht', rfl⟩
      exact ⟨ht', by change (1 : ℝ) ∈ Icc (0 : ℝ) 1; norm_num⟩
    have hembpoly : IsPolyhedron (emb '' Icc 0 1) :=
      isHPolytope_Icc.isPolyhedron.image_of_isPiecewiseAffineOn hemb.isPiecewiseAffineOn
        hemb.bijOn.injOn
    have h := hemb.trans (hσ.restrict hembpoly hembsub)
    rwa [← image_comp] at h
  induction p with
  | nil =>
    intro _ ein eout hein heout hne _ _ α hα hαc
    have hsph : IsPLSphere 1 (Dbd eout) := by
      rw [(hR eout heout.1 heout.2.1).2]
      exact (hR eout heout.1 heout.2.1).1.isPLSphere_image_stdSimplexBoundary (n := 1)
    obtain ⟨r, A, β, hr, hnr, -, hβ, hAS, hrβ⟩ := exists_isPLHomeomorphOn_reflection_arc hsph
    have hβim : β '' Icc 0 1 = A := hβ.image_eq
    rw [← hβim] at hAS hβ
    obtain ⟨σ, hσ, h0, h1, hsub, hin, hout, hdis⟩ := ht.exists_freeFace_strip hR
      (Subtype.coe_prop _) hein heout hne hα hαc hβ hAS hr hnr hrβ
    have hγim : (fun t => σ (t, 1)) '' Icc 0 1 = β '' Icc 0 1 := by
      rcases h1 with h1 | h1
      · exact image_congr fun t ht' => h1 t ht'
      · rw [image_congr fun t ht' => h1 t ht']
        have hrev : (fun t : ℝ => 1 - t) '' Icc 0 1 = Icc 0 1 := by
          rw [image_const_sub_Icc]
          norm_num
        rw [show (fun t : ℝ => β (1 - t)) = β ∘ fun t => 1 - t from rfl, image_comp, hrev]
    refine ⟨σ, fun t => σ (t, 1), hσ, h0, fun t _ => rfl, htopedge hσ, by rw [hγim]; exact hAS,
      ?_, hin, by rw [hγim]; exact hout, fun f hf hfc hfin hfout _ => hdis f hf hfc hfin hfout⟩
    simp only [SimpleGraph.Walk.support_nil, List.mem_singleton, iUnion_iUnion_eq_left]
    exact hsub
  | @cons x z y hadj p' ih =>
    intro hp ein eout hein heout hne hinp houtp α hα hαc
    rw [SimpleGraph.Walk.cons_isPath_iff] at hp
    obtain ⟨hp', hxp'⟩ := hp
    have hxz : (x : E3) ≠ z := fun h => hadj.1 (Subtype.ext h)
    have hexz : ({(x : E3), (z : E3)} : Finset E3) ∈ K.faces := by
      have h := hadj.2
      rwa [classical_insert_singleton_eq_pair] at h
    have hexzc : ({(x : E3), (z : E3)} : Finset E3).card = 2 := Finset.card_pair hxz
    have hxexz : ({(x : E3), (z : E3)} : Finset E3) ∈ edgesAt K x :=
      ⟨hexz, hexzc, Finset.mem_insert_self _ _⟩
    have hzexz : ({(x : E3), (z : E3)} : Finset E3) ∈ edgesAt K z :=
      ⟨hexz, hexzc, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩
    have hzsupp : z ∈ (SimpleGraph.Walk.cons hadj p').support := by
      simp
    have hzein : (z : E3) ∉ ein := fun h => hadj.1 (hinp z hzsupp h).symm
    have hne1 : ein ≠ {(x : E3), (z : E3)} := fun h =>
      hzein (h ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    have hxeout : (x : E3) ∉ eout := by
      intro h
      have hxy := houtp x (by simp) h
      subst hxy
      exact hxp' p'.end_mem_support
    have hne2 : ({(x : E3), (z : E3)} : Finset E3) ≠ eout := fun h =>
      hxeout (h ▸ Finset.mem_insert_self _ _)
    have hsph : IsPLSphere 1 (Dbd {(x : E3), (z : E3)}) := by
      rw [(hR _ hexz hexzc).2]
      exact (hR _ hexz hexzc).1.isPLSphere_image_stdSimplexBoundary (n := 1)
    obtain ⟨r, A, β, hr, hnr, -, hβ, hAS, hrβ⟩ := exists_isPLHomeomorphOn_reflection_arc hsph
    have hβim : β '' Icc 0 1 = A := hβ.image_eq
    rw [← hβim] at hAS hβ
    obtain ⟨σ, hσ, h0, h1, hsub, hin, hout, hdis⟩ := ht.exists_freeFace_strip hR
      (Subtype.coe_prop x) hein hxexz hne1 hα hαc hβ hAS hr hnr hrβ
    have hγim : (fun t => σ (t, 1)) '' Icc 0 1 = β '' Icc 0 1 := by
      rcases h1 with h1 | h1
      · exact image_congr fun t ht' => h1 t ht'
      · rw [image_congr fun t ht' => h1 t ht']
        have hrev : (fun t : ℝ => 1 - t) '' Icc 0 1 = Icc 0 1 := by
          rw [image_const_sub_Icc]
          norm_num
        rw [show (fun t : ℝ => β (1 - t)) = β ∘ fun t => 1 - t from rfl, image_comp, hrev]
    have hinp' : ∀ v ∈ p'.support, (v : E3) ∈ ({(x : E3), (z : E3)} : Finset E3) → v = z := by
      intro v hv hvexz
      rcases Finset.mem_insert.mp hvexz with h | h
      · exact absurd (Subtype.ext h ▸ hv) hxp'
      · exact Subtype.ext (Finset.mem_singleton.mp h)
    have houtp' : ∀ v ∈ p'.support, (v : E3) ∈ eout → v = y := fun v hv hve =>
      houtp v (by simp [hv]) hve
    obtain ⟨S', γ, hS', hS'0, hS'1, hγ, hγc, hS'sub, hS'in, hS'out, hS'dis⟩ :=
      ih hp' hzexz heout hne2 hinp' houtp' (htopedge hσ) (by rw [hγim]; exact hAS)
    have hmeet : σ '' (Icc 0 1 ×ˢ Icc 0 1) ∩ S' '' (Icc 0 1 ×ˢ Icc 0 1) ⊆
        σ '' (Icc 0 1 ×ˢ {1}) := by
      rintro w ⟨hwσ, hwS'⟩
      obtain ⟨v, hv, hwv⟩ := mem_iUnion₂.mp (hS'sub hwS')
      have hvx : (x : E3) ≠ v := fun h => hxp' (Subtype.ext h ▸ hv)
      obtain ⟨f, hf, hfc, hxf, hvf, hwf⟩ := ht.exists_rim_of_mem_freeFace_inter
        (Subtype.coe_prop x) (Subtype.coe_prop v) hvx (hsub hwσ) hwv
      by_cases hfe : f = ({(x : E3), (z : E3)} : Finset E3)
      · subst hfe
        have hw' : w ∈ β '' Icc 0 1 := hout.subset ⟨hwσ, hwf⟩
        rw [← hγim] at hw'
        obtain ⟨t, ht', rfl⟩ := hw'
        exact ⟨(t, 1), ⟨ht', mem_singleton 1⟩, rfl⟩
      · by_cases hfin : f = ein
        · subst hfin
          exact absurd (hinp v (by simp [hv]) hvf) (fun h => hvx (congrArg Subtype.val h).symm)
        · exact absurd hwf (disjoint_left.mp (hdis f hf hfc hfin hfe) hwσ)
    have hjoin : ∀ t ∈ Icc (0 : ℝ) 1, σ (t, 1) = S' (t, 0) := fun t ht' => (hS'0 t ht').symm
    obtain ⟨S, hS, hS0, hS1, -, -⟩ := exists_isPLHomeomorphOn_square_concat hσ hS' hjoin hmeet
    have hSim : S '' (Icc 0 1 ×ˢ Icc 0 1) =
        σ '' (Icc 0 1 ×ˢ Icc 0 1) ∪ S' '' (Icc 0 1 ×ˢ Icc 0 1) := hS.image_eq
    refine ⟨S, γ, by rw [hSim]; exact hS, fun t ht' => (hS0 t ht').trans (h0 t ht'),
      fun t ht' => (hS1 t ht').trans (hS'1 t ht'), hγ, hγc, ?_, ?_, ?_, ?_⟩
    · rw [hSim]
      refine union_subset (hsub.trans ?_) (hS'sub.trans ?_)
      · exact subset_iUnion₂ (s := fun v (_ : v ∈ (SimpleGraph.Walk.cons hadj p').support) =>
          frontier (C v) ∩ frontier N) x (by simp)
      · exact iUnion₂_subset fun v hv => subset_iUnion₂
          (s := fun v (_ : v ∈ (SimpleGraph.Walk.cons hadj p').support) =>
            frontier (C v) ∩ frontier N) v (by simp [hv])
    · rw [hSim, union_inter_distrib_right, hin]
      have hempty : S' '' (Icc 0 1 ×ˢ Icc 0 1) ∩ Dbd ein = ∅ :=
        disjoint_iff_inter_eq_empty.mp (hS'dis ein hein.1 hein.2.1 hne1 hne
          ⟨x, hein.2.2, fun v hv h => hxp' (Subtype.ext h ▸ hv)⟩)
      rw [hempty, union_empty]
    · rw [hSim, union_inter_distrib_right, hS'out]
      have hempty : σ '' (Icc 0 1 ×ˢ Icc 0 1) ∩ Dbd eout = ∅ :=
        disjoint_iff_inter_eq_empty.mp ((ht.disjoint_rim_freeFace heout.1 heout.2.1
          (Subtype.coe_prop x) hxeout).mono_right hsub).symm
      rw [hempty, empty_union]
    · intro f hf hfc hfin hfout ⟨u, huf, hu⟩
      rw [hSim]
      have hfexz : f ≠ ({(x : E3), (z : E3)} : Finset E3) := by
        rintro rfl
        rcases Finset.mem_insert.mp huf with h | h
        · exact hu x (by simp) h.symm
        · exact hu z hzsupp (Finset.mem_singleton.mp h).symm
      refine Disjoint.union_left (hdis f hf hfc hfin hfexz) (hS'dis f hf hfc hfexz hfout
        ⟨u, huf, fun v hv => hu v (by simp [hv])⟩)

end DifferentialGeometry.Topology.PiecewiseLinear
