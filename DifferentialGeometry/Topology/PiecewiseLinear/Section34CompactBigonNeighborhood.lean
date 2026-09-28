/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactBigonTrace
import DifferentialGeometry.Topology.PiecewiseLinear.PlanarBigonNeighborhood

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Plane" => EuclideanSpace ℝ (Fin 2)

variable {C V : Set E3} {h f₁ : E3 → E3} {ε : ℝ}
  {K K' : Geometry.SimplicialComplex ℝ E3}
  {src srcBd : Section34CompactLabelOf K K' → Set E3} {H : Finset E3 → Set E3}

theorem exists_compactBigonCrosscutNeighborhood
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hgraph : Section34CompactGraphFrame V h ε K K' src H f₁)
    {fbl fblBd : Section34CompactSimplexIndex K 3 → Set E3}
    (hinv : Section34CompactFaceBallInvariants K K' h H
      (section34CompactVertexBallImage src f₁) (section34CompactSplitDiskImage srcBd f₁)
      fbl fblBd)
    (s : Section34CompactSimplexIndex K 3) {e : Section34CompactEdgeIndex K K'}
    {B B' Bb Dj Jd : Set E3} (hB : IsPLCellOn 1 B Bb) (hB' : IsPLCellOn 1 B' Bb)
    (hD : IsPLCellOn 2 Dj Jd) (hDB : Dj ∩ fblBd s = B)
    (hDB' : Dj ∩ section34CompactSplitDiskImage srcBd f₁ e = B') (hBB' : B ∩ B' = Bb)
    (hDS : Dj ⊆ frontier (⋃ w, section34CompactVertexBallImage src f₁ w))
    (k : OpenPartialHomeomorph E3 (Plane × ℝ))
    (hk : IsPiecewiseAffineOn k k.source) (hki : IsPiecewiseAffineOn k.symm k.target)
    (hDk : Dj ⊆ k.source)
    (hS : ∀ x ∈ k.source,
      x ∈ frontier (⋃ w, section34CompactVertexBallImage src f₁ w) ↔ (k x).2 = 0)
    (hEs : ∀ x ∈ section34CompactSplitDiskImage srcBd f₁ e ∩ k.source,
      x ∈ frontier (⋃ w, section34CompactVertexBallImage src f₁ w))
    {N : Set Plane} (hN : IsOpen N) (hDN : (fun x => (k x).1) '' Dj ⊆ N) :
    ∃ (Q A C : Set Plane) (α β : ℝ → Plane) (p q : Plane),
      IsPLBall 2 Q ∧ (fun x => (k x).1) '' Dj ⊆ interior Q ∧ Q ⊆ N ∧
      IsPLHomeomorphOn α (Icc 0 1) (A ∩ Q) ∧
      IsPLHomeomorphOn β (Icc 0 1) (C ∩ Q) ∧
      Schoenflies.IsCrosscut (frontier Q) (A ∩ Q) (α 0) (α 1) ∧
      Schoenflies.IsCrosscut (frontier Q) (C ∩ Q) (β 0) (β 1) ∧
      p ≠ q ∧ (A ∩ Q) ∩ (C ∩ Q) = {p, q} ∧
      p ∈ interior Q ∧ q ∈ interior Q ∧
      HasPLCurveCrossingOnAt univ (A ∩ Q) (C ∩ Q) p ∧
      HasPLCurveCrossingOnAt univ (A ∩ Q) (C ∩ Q) q ∧
      (fun x => (k x).1) '' Bb = {p, q} ∧
      ∀ z ∈ Q, (z, (0 : ℝ)) ∈ k.target ∧
        (k.symm (z, 0) ∈ fblBd s ∩
          frontier (⋃ w, section34CompactVertexBallImage src f₁ w) ↔ z ∈ A) ∧
        (k.symm (z, 0) ∈ section34CompactSplitDiskImage srcBd f₁ e ↔ z ∈ C) := by
  classical
  obtain ⟨-, -, -, -, -, hcross, -, hfinite, -⟩ := id hinv
  let S := frontier (⋃ w, section34CompactVertexBallImage src f₁ w)
  let T := fblBd s ∩ S
  let E := section34CompactSplitDiskImage srcBd f₁ e
  let f : E3 → Plane := fun x => (k x).1
  have hBD : B ⊆ Dj := fun x hx => (hDB.symm ▸ hx).1
  have hB'D : B' ⊆ Dj := fun x hx => (hDB'.symm ▸ hx).1
  have hBbD : Bb ⊆ Dj := hB.boundary_subset.trans hBD
  obtain ⟨d, hd, -⟩ := hD.exists_isPLHomeomorphOn_stdSimplex
  have hDball : IsPLBall 2 Dj := ⟨d, hd⟩
  obtain ⟨b, hb, hbb⟩ := hB.exists_isPLHomeomorphOn_stdSimplex
  obtain ⟨b', hb', -⟩ := hB'.exists_isPLHomeomorphOn_stdSimplex
  have hbb' : b '' stdSimplexBoundary 1 = B ∩ Bb := by
    rw [inter_eq_right.mpr hB.boundary_subset]
    exact hbb.symm
  obtain ⟨γ, hγ, hγb⟩ := exists_isPLHomeomorphOn_Icc_of_stdSimplex_one hb hbb'
  rw [inter_eq_right.mpr hB.boundary_subset] at hγb
  have hγne : γ 0 ≠ γ 1 := fun h => zero_ne_one
    (hγ.bijOn.injOn ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ h)
  obtain ⟨A₀, r, O₁, hr, hA₀, hDA₀, hrends, hO₁, hDO₁, hO₁k, hO₁T⟩ :=
    exists_compactBigonTraceArc hcut hgraph hinv s hB hDB hDS k.open_source hDk
  obtain ⟨C₀, t, O₂, ht, hC₀, hDC₀, htends, hO₂, hDO₂, hO₂k, hO₂E⟩ :=
    exists_compactBigonSplittingArc hcut hgraph hB' hDB' k.open_source hDk
  have hDz : ∀ x ∈ Dj, (k x).2 = 0 := fun x hx => (hS x (hDk hx)).mp (hDS hx)
  have hAz : ∀ x ∈ A₀, (k x).2 = 0 :=
    fun x hx => (hS x (hA₀ hx).2).mp (hA₀ hx).1.2
  have hCz : ∀ x ∈ C₀, (k x).2 = 0 :=
    fun x hx => (hS x (hC₀ hx).2).mp (hEs x (hC₀ hx))
  let Z := {x : E3 | x ∈ k.source ∧ (k x).2 = 0}
  have hinj : InjOn f Z := fun x hx y hy hxy =>
    k.injOn hx.1 hy.1 (Prod.ext hxy (hx.2.trans hy.2.symm))
  have hDZ : Dj ⊆ Z := fun x hx => ⟨hDk hx, hDz x hx⟩
  have hAZ : A₀ ⊆ Z := fun x hx => ⟨(hA₀ hx).2, hAz x hx⟩
  have hCZ : C₀ ⊆ Z := fun x hx => ⟨(hC₀ hx).2, hCz x hx⟩
  have hfD := isPLHomeomorphOn_fst_openPartialHomeomorph k hk hDball.isPolyhedron hDk hDz
  have hAball : IsPLBall 1 A₀ := ⟨r, hr⟩
  have hCball : IsPLBall 1 C₀ := ⟨t, ht⟩
  have hfA := isPLHomeomorphOn_fst_openPartialHomeomorph k hk hAball.isPolyhedron
    (fun _ hx => (hA₀ hx).2) hAz
  have hfC := isPLHomeomorphOn_fst_openPartialHomeomorph k hk hCball.isPolyhedron
    (fun _ hx => (hC₀ hx).2) hCz
  have hDA : IsPLBall 1 ((f '' Dj) ∩ (f '' A₀)) := by
    rw [← hinj.image_inter hDZ hAZ, hDA₀]
    have hBball : IsPLBall 1 B := ⟨b, hb⟩
    exact hBball.of_isPLHomeomorphOn
      (isPLHomeomorphOn_fst_openPartialHomeomorph k hk hBball.isPolyhedron
        (hBD.trans hDk) (fun x hx => hDz x (hBD hx)))
  have hDC : IsPLBall 1 ((f '' Dj) ∩ (f '' C₀)) := by
    rw [← hinj.image_inter hDZ hCZ, hDC₀]
    have hBball : IsPLBall 1 B' := ⟨b', hb'⟩
    exact hBball.of_isPLHomeomorphOn
      (isPLHomeomorphOn_fst_openPartialHomeomorph k hk hBball.isPolyhedron
        (hB'D.trans hDk) (fun x hx => hDz x (hB'D hx)))
  have hends (R : Set E3) (u : (Fin 2 → ℝ) → E3)
      (hu : IsPLHomeomorphOn u (Convexity.StdSimplex.coordinateSet ℝ (Fin 2)) R) (hRZ : R ⊆ Z)
      (he : Disjoint Dj (u '' stdSimplexBoundary 1)) :
      Disjoint (f '' Dj) ((f ∘ u) '' stdSimplexBoundary 1) := by
    refine disjoint_left.mpr ?_
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hyx⟩
    have hxy : u y = x := hinj (hRZ (hu.bijOn.mapsTo hy.1)) (hDZ hx) hyx
    exact disjoint_left.mp he hx ⟨y, hy, hxy⟩
  have hpair₀ : Dj ∩ (A₀ ∩ C₀) = Bb := by
    rw [← hBB', ← hDA₀, ← hDC₀]
    ext x
    simp only [mem_inter_iff]
    tauto
  have hpair : (f '' Dj) ∩ ((f '' A₀) ∩ (f '' C₀)) = {f (γ 0), f (γ 1)} := by
    rw [← hinj.image_inter hAZ hCZ, ← hinj.image_inter hDZ
      (inter_subset_left.trans hAZ), hpair₀, ← hγb, image_pair]
  have hfinite₀ : (A₀ ∩ C₀).Finite := (hfinite s).subset fun x hx =>
    ⟨(hA₀ hx.1).1.1, mem_iUnion.mpr ⟨e, (hC₀ hx.2).1⟩⟩
  have hfinite' : ((f '' A₀) ∩ (f '' C₀)).Finite := by
    rw [← hinj.image_inter hAZ hCZ]
    exact hfinite₀.image f
  have hcross' (x : E3) (hx : x ∈ Bb) :
      HasPLCurveCrossingOnAt univ (f '' A₀) (f '' C₀) (f x) := by
    have hxD := hBbD hx
    have hxB := hB.boundary_subset hx
    have hxB' := hB'.boundary_subset hx
    have hcr : HasPLCurveCrossingOnAt S T E x :=
      hcross s e x ⟨(hDB.symm ▸ hxB).2, (hDB'.symm ▸ hxB').2⟩
    have hcr' : HasPLCurveCrossingOnAt S A₀ C₀ x := by
      refine hcr.congr (Filter.Eventually.of_forall fun _ => Iff.rfl) ?_ ?_
      · filter_upwards [hO₁.mem_nhds (hDO₁ hxD)] with z hz
        exact ⟨fun h => (hO₁T ▸ ⟨hz, h⟩ : z ∈ O₁ ∩ A₀).2,
          fun h => (hO₁T.symm ▸ ⟨hz, h⟩ : z ∈ O₁ ∩ T).2⟩
      · filter_upwards [hO₂.mem_nhds (hDO₂ hxD)] with z hz
        exact ⟨fun h => (hO₂E ▸ ⟨hz, h⟩ : z ∈ O₂ ∩ C₀).2,
          fun h => (hO₂E.symm ▸ ⟨hz, h⟩ : z ∈ O₂ ∩ E).2⟩
    exact hcr'.fst_openPartialHomeomorph (by simp) k hki (hDk hxD) (hDz x hxD)
      hS (fun _ hz => (hA₀ hz).2) (fun _ hz => (hC₀ hz).2) hAz hCz
  have hγ0 : γ 0 ∈ Bb := hγb.subset (Or.inl rfl)
  have hγ1 : γ 1 ∈ Bb := hγb.subset (Or.inr rfl)
  have hpq : f (γ 0) ≠ f (γ 1) := fun hpq => hγne
    (hinj (hDZ (hBbD hγ0)) (hDZ (hBbD hγ1)) hpq)
  let W := N ∩ (fun z : Plane => (z, (0 : ℝ))) ⁻¹' (k '' (O₁ ∩ O₂))
  have hW : IsOpen W := hN.inter
    ((k.isOpen_image_of_subset_source (hO₁.inter hO₂)
      (inter_subset_left.trans hO₁k)).preimage (continuous_id.prodMk continuous_const))
  have hDW : f '' Dj ⊆ W := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨hDN ⟨x, hx, rfl⟩, x, ⟨hDO₁ hx, hDO₂ hx⟩, Prod.ext rfl (hDz x hx)⟩
  obtain ⟨Q, α, β, hQ, hDQ, hQW, hα, hβ, hαc, hβc, hAC, hp, hq, hcp, hcq⟩ :=
    (hDball.of_isPLHomeomorphOn hfD).exists_isPLBall_neighborhood_with_two_crossings
      hW hDW (hr.trans hfA) (ht.trans hfC) hDA hDC
      (hends A₀ r hr hAZ hrends) (hends C₀ t ht hCZ htends)
      hfinite' hpair (hcross' _ hγ0) (hcross' _ hγ1)
  refine ⟨Q, f '' A₀, f '' C₀, α, β, f (γ 0), f (γ 1), hQ, hDQ,
    hQW.trans inter_subset_left, hα, hβ, hαc, hβc, hpq, hAC, hp, hq, hcp, hcq, ?_, ?_⟩
  · rw [← hγb, image_pair]
  · intro z hz
    obtain ⟨x, hxO, hxz⟩ := (hQW hz).2
    change k x = (z, (0 : ℝ)) at hxz
    have hxk := hO₁k hxO.1
    have hzt : (z, (0 : ℝ)) ∈ k.target := hxz ▸ k.map_source hxk
    have hzix : k.symm (z, 0) = x := by rw [← hxz, k.left_inv hxk]
    have hmem (R : Set E3) (hRZ : R ⊆ Z) : x ∈ R ↔ z ∈ f '' R := by
      constructor
      · intro hxR
        exact ⟨x, hxR, congrArg Prod.fst hxz⟩
      · rintro ⟨y, hy, hyz⟩
        have hyx : y = x := k.injOn (hRZ hy).1 hxk
          ((Prod.ext hyz (hRZ hy).2).trans hxz.symm)
        exact hyx ▸ hy
    refine ⟨hzt, ?_, ?_⟩
    · rw [hzix, ← hmem A₀ hAZ]
      exact ⟨fun hx => (hO₁T ▸ ⟨hxO.1, hx⟩ : x ∈ O₁ ∩ A₀).2,
        fun hx => (hO₁T.symm ▸ ⟨hxO.1, hx⟩ : x ∈ O₁ ∩ T).2⟩
    · rw [hzix, ← hmem C₀ hCZ]
      exact ⟨fun hx => (hO₂E ▸ ⟨hxO.2, hx⟩ : x ∈ O₂ ∩ C₀).2,
        fun hx => (hO₂E.symm ▸ ⟨hxO.2, hx⟩ : x ∈ O₂ ∩ E).2⟩

end DifferentialGeometry.Topology.PiecewiseLinear
