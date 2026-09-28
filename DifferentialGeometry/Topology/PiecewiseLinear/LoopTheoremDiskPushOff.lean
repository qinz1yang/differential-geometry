/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.HandlePiecePushOff

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem IsLoopTheoremDisk.image_of_isPLHomeomorphOn {Kimg N' X Δ : Set E3}
    (hΔ : IsLoopTheoremDisk Kimg N' (frontier X) Δ) {Φ : E3 → E3}
    (hΦ : IsPLHomeomorphOn Φ univ univ) (hΦX : ∀ y, Φ y ∈ X ↔ y ∈ X)
    (hint : ∀ y ∈ Δ, Φ y ∈ interior N' \ Kimg) :
    IsLoopTheoremDisk Kimg N' (frontier X) (Φ '' Δ) := by
  obtain ⟨r, hr, -, hΔB, hb, hnull⟩ := hΔ
  have hΔpoly : IsPolyhedron Δ := by
    rw [← hr.image_eq]
    exact (isHPolytope_stdSimplex (Fin 3)).isPolyhedron.image_of_isPiecewiseAffineOn
      hr.isPiecewiseAffineOn hr.bijOn.injOn
  let H := (Homeomorph.Set.univ E3).symm.trans (hΦ.homeomorph.trans (Homeomorph.Set.univ E3))
  have hpre : H ⁻¹' X = X := by
    ext y
    exact hΦX y
  have hfr0 := H.preimage_frontier X
  rw [hpre] at hfr0
  have hfr : ∀ y, Φ y ∈ frontier X ↔ y ∈ frontier X := fun y => Set.ext_iff.mp hfr0 y
  have himg : (Φ ∘ r) '' stdSimplexBoundary 2 = Φ '' Δ ∩ frontier X := by
    rw [image_comp, ← hΔB]
    ext z
    constructor
    · rintro ⟨y, ⟨hyΔ, hyB⟩, rfl⟩
      exact ⟨mem_image_of_mem Φ hyΔ, (hfr y).mpr hyB⟩
    · rintro ⟨⟨y, hyΔ, rfl⟩, hyB⟩
      exact ⟨y, ⟨hyΔ, (hfr y).mp hyB⟩, rfl⟩
  have hb' : (Φ ∘ r) '' stdSimplexBoundary 2 ⊆ frontier X := by
    rw [himg]
    exact inter_subset_right
  have hr' : IsPLHomeomorphOn (Φ ∘ r) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (Φ '' Δ) :=
    IsPLHomeomorphOn.trans hr (IsPLHomeomorphOn.restrict hΦ hΔpoly (subset_univ Δ))
  refine ⟨Φ ∘ r, hr', ?_, himg.symm, hb', fun hnull' => hnull ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact hint y hy
  · have hgmem : ∀ z : frontier X, H.symm z ∈ frontier X := fun z =>
      (hfr _).mp (by
        change H (H.symm z) ∈ frontier X
        rw [H.apply_symm_apply]
        exact z.2)
    have hkmem : ∀ y : r '' stdSimplexBoundary 2, H y ∈ (Φ ∘ r) '' stdSimplexBoundary 2 :=
      fun y => by
        rw [image_comp]
        exact mem_image_of_mem Φ y.2
    let g : C(frontier X, frontier X) :=
      ⟨fun z => ⟨H.symm z, hgmem z⟩, (H.symm.continuous.comp continuous_subtype_val).subtype_mk
        hgmem⟩
    let k : C(r '' stdSimplexBoundary 2, (Φ ∘ r) '' stdSimplexBoundary 2) :=
      ⟨fun y => ⟨H y, hkmem y⟩, (H.continuous.comp continuous_subtype_val).subtype_mk hkmem⟩
    have hcomp := (hnull'.comp_right g).comp_left k
    convert hcomp using 1
    refine ContinuousMap.ext fun y => Subtype.ext ?_
    exact (H.symm_apply_apply (y : E3)).symm

section PushOff

variable {K : Geometry.SimplicialComplex ℝ E3} {N N' : Set E3} {C : E3 → Set E3}
  {D Dbd Ec Eint Ebd : Finset E3 → Set E3} {h : E3 → E3} {Cpp : E3 → Set E3}
  {XK : Geometry.SimplicialComplex ℝ E3}

theorem IsPolyhedralTubeNeighborhood.exists_isLoopTheoremDisk_pushOff
    (hd : IsHandleDecompositionOfTube K N C D Dbd h N' Ec Eint Ebd Cpp)
    (h2 : IsPolyhedralTubeNeighborhood K h N' Ec Eint Ebd XK) {v : E3} (hv : v ∈ K.vertices)
    {Δ : Set E3} (hΔ : IsLoopTheoremDisk (h '' K.space) N' (frontier XK.space) Δ)
    {O : Set E3} (hO : IsOpen O) (hON : O ⊆ interior N') (hOK : Disjoint O (h '' K.space))
    {Z : Set E3} (hZ : IsCompact Z) (hZO : Z ⊆ O) (hZC : Z ⊆ Cpp v) (hΔC : Δ ∩ O ⊆ Cpp v)
    (hΔZ : Δ ∩ O ∩ (⋃ e ∈ {e : Finset E3 | e ∈ K.faces ∧ e.card = 2}, Ec e) ⊆ Z) :
    ∃ Δ' : Set E3, IsLoopTheoremDisk (h '' K.space) N' (frontier XK.space) Δ' ∧
      Δ' ∩ (⋃ e ∈ {e : Finset E3 | e ∈ K.faces ∧ e.card = 2}, Ec e) =
        (Δ \ O) ∩ (⋃ e ∈ {e : Finset E3 | e ∈ K.faces ∧ e.card = 2}, Ec e) := by
  set A := ⋃ e ∈ {e : Finset E3 | e ∈ K.faces ∧ e.card = 2}, Ec e with hAdef
  have hfin : {f : Finset E3 | f ∈ K.faces ∧ f.card = 2}.Finite :=
    hd.tube.facesFinite.subset fun f hf => hf.1
  have hAc : IsClosed A := hfin.isClosed_biUnion fun f hf => (hd.pseudoCell f hf.1 hf.2).isClosed
  obtain ⟨Φ, hΦ, hΦO, hΦX, hΦC⟩ := exists_isPLHomeomorphOn_push_of_forall (A := A)
    (C := Cpp v) (X := XK.space) (O := O) (hZ.inter_right hAc)
    fun x hx => h2.exists_localPush hd hv hO hON hOK (hZO hx.1) (hZC hx.1) hx.2
  have hinj : ∀ y y', Φ y = Φ y' → y = y' := fun y y' hyy =>
    hΦ.bijOn.injOn (mem_univ y) (mem_univ y') hyy
  have hmapO : ∀ y ∈ O, Φ y ∈ O := by
    intro y hy
    by_contra hn
    have hyy := hinj _ _ (hΦO _ hn)
    rw [hyy] at hn
    exact hn hy
  have hΔsub : Δ ⊆ interior N' \ h '' K.space := by
    obtain ⟨r, -, hsub, -⟩ := hΔ
    exact hsub
  refine ⟨Φ '' Δ, hΔ.image_of_isPLHomeomorphOn hΦ hΦX fun y hy => ?_, ?_⟩
  · by_cases hyO : y ∈ O
    · exact ⟨hON (hmapO y hyO), Set.disjoint_left.mp hOK (hmapO y hyO)⟩
    · rw [hΦO y hyO]
      exact hΔsub hy
  · ext y
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hxA⟩
      by_cases hxO : x ∈ O
      · obtain ⟨hxZ, hfix⟩ := (hΦC x (hΔC ⟨hx, hxO⟩)).2 hxA
        rw [hfix] at hxA
        exact absurd ⟨hΔZ ⟨⟨hx, hxO⟩, hxA⟩, hxA⟩ hxZ
      · rw [hΦO x hxO] at hxA ⊢
        exact ⟨⟨hx, hxO⟩, hxA⟩
    · rintro ⟨⟨hy, hyO⟩, hyA⟩
      exact ⟨⟨y, hy, hΦO y hyO⟩, hyA⟩

end PushOff

end DifferentialGeometry.Topology.PiecewiseLinear
