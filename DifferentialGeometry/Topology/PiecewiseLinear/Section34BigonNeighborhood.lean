/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34BigonTrace
import DifferentialGeometry.Topology.PiecewiseLinear.PlanarBigonNeighborhood

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
  {U : Set M₁} {h : M₁ → M₂} {η : M₁ → ℝ} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁} {H : Finset Ea → Set M₂}
  {cr : Section34VertexIndex 𝒦 𝒦' → Finset Ea} {f₁ : M₁ → M₂}

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Plane" => EuclideanSpace ℝ (Fin 2)

theorem exists_section34BigonCrosscutNeighborhood (hh : IsEmbedding (U.domRestrict h))
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hctrl : Section34CarrierControl U 𝒦 h η H)
    (hgraph : Section34GraphFrame U U h η H 𝒦 𝒦' src cr f₁)
    {fbl fblBd : Section34SimplexIndex 𝒦 3 → Set M₂}
    (hinv : Section34FaceBallInvariants 𝒦 𝒦' h H (section34VertexBallImage src f₁)
      (section34SplitDiskImage srcBd f₁) fbl fblBd)
    (s : Section34SimplexIndex 𝒦 3) {e : Section34EdgeIndex 𝒦 𝒦'}
    {B B' Bb Dj Jd : Set M₂} (hB : IsPLCellOn 1 B Bb) (hB' : IsPLCellOn 1 B' Bb)
    (hD : IsPLCellOn 2 Dj Jd) (hDB : Dj ∩ fblBd s = B)
    (hDB' : Dj ∩ section34SplitDiskImage srcBd f₁ e = B') (hBB' : B ∩ B' = Bb)
    (hDS : Dj ⊆ frontier (⋃ w, section34VertexBallImage src f₁ w))
    {c : OpenPartialHomeomorph M₂ E3} (hc : c ∈ (plGroupoid 3).maximalAtlas M₂)
    (hfc : fbl s ⊆ c.source)
    (hTc : section34FaceTorus (section34VertexBallImage src f₁) s ⊆ c.source)
    (hEc : section34SplitDiskImage src f₁ e ⊆ c.source) (hDc : Dj ⊆ c.source)
    (k : OpenPartialHomeomorph E3 (Plane × ℝ))
    (hk : IsPiecewiseAffineOn k k.source) (hki : IsPiecewiseAffineOn k.symm k.target)
    (hDk : c '' Dj ⊆ k.source)
    (hS : ∀ x ∈ k.source,
      x ∈ c '' (frontier (⋃ w, section34VertexBallImage src f₁ w) ∩ c.source) ↔
        (k x).2 = 0)
    (hEs : ∀ x ∈ (c '' section34SplitDiskImage srcBd f₁ e) ∩ k.source,
      x ∈ c '' (frontier (⋃ w, section34VertexBallImage src f₁ w) ∩ c.source))
    {V : Set Plane} (hV : IsOpen V) (hDV : (fun x => (k x).1) '' (c '' Dj) ⊆ V) :
    ∃ (Q A C : Set Plane) (α β : ℝ → Plane) (p q : Plane),
      IsPLBall 2 Q ∧ (fun x => (k x).1) '' (c '' Dj) ⊆ interior Q ∧ Q ⊆ V ∧
      IsPLHomeomorphOn α (Icc 0 1) (A ∩ Q) ∧
      IsPLHomeomorphOn β (Icc 0 1) (C ∩ Q) ∧
      Schoenflies.IsCrosscut (frontier Q) (A ∩ Q) (α 0) (α 1) ∧
      Schoenflies.IsCrosscut (frontier Q) (C ∩ Q) (β 0) (β 1) ∧
      p ≠ q ∧ (A ∩ Q) ∩ (C ∩ Q) = {p, q} ∧
      p ∈ interior Q ∧ q ∈ interior Q ∧
      HasPLCurveCrossingOnAt univ (A ∩ Q) (C ∩ Q) p ∧
      HasPLCurveCrossingOnAt univ (A ∩ Q) (C ∩ Q) q ∧
      (fun x => (k x).1) '' (c '' Bb) = {p, q} ∧
      ∀ z ∈ Q, (z, (0 : ℝ)) ∈ k.target ∧
        (k.symm (z, 0) ∈ c ''
          (fblBd s ∩ frontier (⋃ w, section34VertexBallImage src f₁ w)) ↔ z ∈ A) ∧
        (k.symm (z, 0) ∈ c '' section34SplitDiskImage srcBd f₁ e ↔ z ∈ C) := by
  classical
  obtain ⟨hfcell, -, -, -, -, hcross, -, hfinite, -, -⟩ := id hinv
  obtain ⟨-, -, hf₁, -, -, -, -, -, -, -, -, -, -, -⟩ := id hgraph
  let S := c '' (frontier (⋃ w, section34VertexBallImage src f₁ w) ∩ c.source)
  let T := c '' (fblBd s ∩ frontier (⋃ w, section34VertexBallImage src f₁ w))
  let E := c '' section34SplitDiskImage srcBd f₁ e
  let D := c '' Dj
  let f : E3 → Plane := fun x => (k x).1
  have hfbc := (hfcell s).boundary_subset.trans hfc
  have hEbc := (hcut.isPLCellOn_splitDiskImage hf₁ e).boundary_subset.trans hEc
  have hBD : B ⊆ Dj := fun x hx => (hDB.symm ▸ hx).1
  have hB'D : B' ⊆ Dj := fun x hx => (hDB'.symm ▸ hx).1
  have hBbD : Bb ⊆ Dj := hB.boundary_subset.trans hBD
  have hBbB : c '' Bb ⊆ c '' B := image_mono hB.boundary_subset
  obtain ⟨d, hd, -⟩ := hD.exists_isPLHomeomorphOn_image_chart hc hDc
  have hDball : IsPLBall 2 D := ⟨d, hd⟩
  obtain ⟨b, hb, hbb⟩ := hB.exists_isPLHomeomorphOn_image_chart hc (hBD.trans hDc)
  obtain ⟨b', hb', -⟩ := hB'.exists_isPLHomeomorphOn_image_chart hc (hB'D.trans hDc)
  have hbb' : b '' stdSimplexBoundary 1 = (c '' B) ∩ (c '' Bb) := by
    rw [inter_eq_right.mpr hBbB]
    exact hbb.symm
  obtain ⟨γ, hγ, hγb⟩ := exists_isPLHomeomorphOn_Icc_of_stdSimplex_one hb hbb'
  rw [inter_eq_right.mpr hBbB] at hγb
  have hγne : γ 0 ≠ γ 1 := fun h => zero_ne_one
    (hγ.bijOn.injOn ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ h)
  obtain ⟨A₀, r, O₁, hr, hA₀, hDA₀, hrends, hO₁, hDO₁, hO₁k, hO₁T⟩ :=
    exists_section34BigonTraceArc hh hcut hctrl hgraph hinv s hB hDB hDS hc hfc hTc hDc
      k.open_source hDk
  obtain ⟨C₀, t, O₂, ht, hC₀, hDC₀, htends, hO₂, hDO₂, hO₂k, hO₂E⟩ :=
    exists_section34BigonSplittingArc hcut hgraph hB' hDB' hc hEc hDc k.open_source hDk
  have hDz : ∀ x ∈ D, (k x).2 = 0 := by
    rintro _ ⟨y, hy, rfl⟩
    exact (hS _ (hDk ⟨y, hy, rfl⟩)).mp ⟨y, ⟨hDS hy, hDc hy⟩, rfl⟩
  have hAz : ∀ x ∈ A₀, (k x).2 = 0 := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := (hA₀ hx).1
    exact (hS x (hA₀ hx).2).mp ⟨y, ⟨hy.2, hfbc hy.1⟩, hyx⟩
  have hCz : ∀ x ∈ C₀, (k x).2 = 0 :=
    fun x hx => (hS x (hC₀ hx).2).mp (hEs x (hC₀ hx))
  let Z := {x : E3 | x ∈ k.source ∧ (k x).2 = 0}
  have hinj : InjOn f Z := fun x hx y hy hxy =>
    k.injOn hx.1 hy.1 (Prod.ext hxy (hx.2.trans hy.2.symm))
  have hDZ : D ⊆ Z := fun x hx => ⟨hDk hx, hDz x hx⟩
  have hAZ : A₀ ⊆ Z := fun x hx => ⟨(hA₀ hx).2, hAz x hx⟩
  have hCZ : C₀ ⊆ Z := fun x hx => ⟨(hC₀ hx).2, hCz x hx⟩
  have hfD := isPLHomeomorphOn_fst_openPartialHomeomorph k hk hDball.isPolyhedron hDk hDz
  have hAball : IsPLBall 1 A₀ := ⟨r, hr⟩
  have hCball : IsPLBall 1 C₀ := ⟨t, ht⟩
  have hfA := isPLHomeomorphOn_fst_openPartialHomeomorph k hk hAball.isPolyhedron
    (fun _ hx => (hA₀ hx).2) hAz
  have hfC := isPLHomeomorphOn_fst_openPartialHomeomorph k hk hCball.isPolyhedron
    (fun _ hx => (hC₀ hx).2) hCz
  have hDA : IsPLBall 1 ((f '' D) ∩ (f '' A₀)) := by
    rw [← hinj.image_inter hDZ hAZ, hDA₀]
    exact (show IsPLBall 1 (c '' B) from ⟨b, hb⟩).of_isPLHomeomorphOn
      (isPLHomeomorphOn_fst_openPartialHomeomorph k hk
        (show IsPLBall 1 (c '' B) from ⟨b, hb⟩).isPolyhedron
        ((image_mono hBD).trans hDk) (fun x hx => hDz x (image_mono hBD hx)))
  have hDC : IsPLBall 1 ((f '' D) ∩ (f '' C₀)) := by
    rw [← hinj.image_inter hDZ hCZ, hDC₀]
    exact (show IsPLBall 1 (c '' B') from ⟨b', hb'⟩).of_isPLHomeomorphOn
      (isPLHomeomorphOn_fst_openPartialHomeomorph k hk
        (show IsPLBall 1 (c '' B') from ⟨b', hb'⟩).isPolyhedron
        ((image_mono hB'D).trans hDk) (fun x hx => hDz x (image_mono hB'D hx)))
  have hends (R : Set E3) (u : (Fin 2 → ℝ) → E3)
      (hu : IsPLHomeomorphOn u (Convexity.StdSimplex.coordinateSet ℝ (Fin 2)) R) (hRZ : R ⊆ Z)
      (he : Disjoint D (u '' stdSimplexBoundary 1)) :
      Disjoint (f '' D) ((f ∘ u) '' stdSimplexBoundary 1) := by
    refine disjoint_left.mpr ?_
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hyx⟩
    have hxy : u y = x := hinj (hRZ (hu.bijOn.mapsTo hy.1)) (hDZ hx) hyx
    exact disjoint_left.mp he hx ⟨y, hy, hxy⟩
  have hpair₀ : D ∩ (A₀ ∩ C₀) = c '' Bb := by
    rw [← hBB', c.injOn.image_inter (hBD.trans hDc) (hB'D.trans hDc),
      ← hDA₀, ← hDC₀]
    ext x
    simp only [D, mem_inter_iff]
    tauto
  have hpair : (f '' D) ∩ ((f '' A₀) ∩ (f '' C₀)) = {f (γ 0), f (γ 1)} := by
    rw [← hinj.image_inter hAZ hCZ, ← hinj.image_inter hDZ
      (inter_subset_left.trans hAZ), hpair₀, ← hγb, image_pair]
  have hfinite₀ : (A₀ ∩ C₀).Finite := by
    apply ((hfinite s).image c).subset
    rintro x ⟨hxA, hxC⟩
    obtain ⟨y, hy, hyx⟩ := (hA₀ hxA).1
    obtain ⟨z, hz, hzx⟩ := (hC₀ hxC).1
    have hzy : z = y := c.injOn (hEbc hz) (hfbc hy.1) (hzx.trans hyx.symm)
    exact ⟨y, ⟨hy.1, mem_iUnion.mpr ⟨e, hzy ▸ hz⟩⟩, hyx⟩
  have hfinite' : ((f '' A₀) ∩ (f '' C₀)).Finite := by
    rw [← hinj.image_inter hAZ hCZ]
    exact hfinite₀.image f
  have hcross' (x : E3) (hx : x ∈ c '' Bb) :
      HasPLCurveCrossingOnAt univ (f '' A₀) (f '' C₀) (f x) := by
    have hxD : x ∈ D := image_mono hBbD hx
    obtain ⟨y, hy, hyx⟩ := hx
    have hyB := hB.boundary_subset hy
    have hyB' := hB'.boundary_subset hy
    have hyF := (hDB.symm ▸ hyB).2
    have hyE := (hDB'.symm ▸ hyB').2
    obtain ⟨c', hc', hyc', hcr⟩ := hcross s e y ⟨hyF, hyE⟩
    have hcr' := hcr.image_chart_of_mem_maximalAtlas hc hc' (hDc (hBbD hy)) hyc'
    have hTc' : fblBd s ∩ frontier (⋃ w, section34VertexBallImage src f₁ w) ⊆
        c.source := inter_subset_left.trans hfbc
    rw [inter_eq_left.mpr hTc', inter_eq_left.mpr hEbc, hyx] at hcr'
    have hcr'' : HasPLCurveCrossingOnAt S A₀ C₀ x := by
      refine hcr'.congr (Filter.Eventually.of_forall fun _ => Iff.rfl) ?_ ?_
      · filter_upwards [hO₁.mem_nhds (hDO₁ hxD)] with z hz
        exact ⟨fun h => (hO₁T ▸ ⟨hz, h⟩ : z ∈ O₁ ∩ A₀).2,
          fun h => (hO₁T.symm ▸ ⟨hz, h⟩ : z ∈ O₁ ∩ T).2⟩
      · filter_upwards [hO₂.mem_nhds (hDO₂ hxD)] with z hz
        exact ⟨fun h => (hO₂E ▸ ⟨hz, h⟩ : z ∈ O₂ ∩ C₀).2,
          fun h => (hO₂E.symm ▸ ⟨hz, h⟩ : z ∈ O₂ ∩ E).2⟩
    exact hcr''.fst_openPartialHomeomorph (by simp) k hki (hDk hxD) (hDz x hxD)
      hS (fun _ hz => (hA₀ hz).2) (fun _ hz => (hC₀ hz).2) hAz hCz
  have hγ0 : γ 0 ∈ c '' Bb := hγb.subset (Or.inl rfl)
  have hγ1 : γ 1 ∈ c '' Bb := hγb.subset (Or.inr rfl)
  have hpq : f (γ 0) ≠ f (γ 1) := fun hpq => hγne
    (hinj (hDZ (image_mono hBbD hγ0)) (hDZ (image_mono hBbD hγ1)) hpq)
  let W := V ∩ (fun z : Plane => (z, (0 : ℝ))) ⁻¹' (k '' (O₁ ∩ O₂))
  have hW : IsOpen W := hV.inter
    ((k.isOpen_image_of_subset_source (hO₁.inter hO₂)
      (inter_subset_left.trans hO₁k)).preimage (continuous_id.prodMk continuous_const))
  have hDW : f '' D ⊆ W := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨hDV ⟨x, hx, rfl⟩, x, ⟨hDO₁ hx, hDO₂ hx⟩, Prod.ext rfl (hDz x hx)⟩
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
