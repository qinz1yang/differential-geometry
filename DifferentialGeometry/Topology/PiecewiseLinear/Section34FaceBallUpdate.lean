/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CrossingNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.Section34FaceBallVocabulary

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

section Components

variable {X : Type*} [TopologicalSpace X]

theorem image_connectedComponentIn_subset_diff {Z Z' O C : Set X} (hO : IsOpen O)
    (hC : IsClosed C) (hZO : Z' = Z ∩ O) (hZC : Z' = Z ∩ C) {y : X} (hyZ : y ∈ Z)
    (hyZ' : y ∉ Z') :
    (fun x => connectedComponentIn Z' x) '' Z' ⊆
      ((fun x => connectedComponentIn Z x) '' Z) \ {connectedComponentIn Z y} := by
  rintro _ ⟨x, hx, rfl⟩
  have hxZ : x ∈ Z := by
    rw [hZO] at hx
    exact hx.1
  have hxC : x ∈ C := by
    rw [hZC] at hx
    exact hx.2
  have hZ'Z : Z' ⊆ Z := by
    rw [hZO]
    exact inter_subset_left
  have hcomp : connectedComponentIn Z' x = connectedComponentIn Z x := by
    refine Subset.antisymm (connectedComponentIn_mono x hZ'Z) ?_
    have hpc : IsPreconnected (connectedComponentIn Z x) := isPreconnected_connectedComponentIn
    have hsub : connectedComponentIn Z x ⊆ O := by
      have hcover : connectedComponentIn Z x ⊆ O ∪ Cᶜ := by
        intro z hz
        have hzZ := connectedComponentIn_subset Z x hz
        by_cases hzC : z ∈ C
        · have hz' : z ∈ Z' := by
            rw [hZC]
            exact ⟨hzZ, hzC⟩
          rw [hZO] at hz'
          exact Or.inl hz'.2
        · exact Or.inr hzC
      have hdisj : connectedComponentIn Z x ∩ (O ∩ Cᶜ) = ∅ := by
        refine eq_empty_iff_forall_notMem.mpr fun z ⟨hz, hzO, hzC⟩ => hzC ?_
        have hz' : z ∈ Z' := by
          rw [hZO]
          exact ⟨connectedComponentIn_subset Z x hz, hzO⟩
        rw [hZC] at hz'
        exact hz'.2
      rcases isPreconnected_iff_subset_of_disjoint.mp hpc O Cᶜ hO hC.isOpen_compl hcover hdisj
        with h | h
      · exact h
      · exact absurd hxC (h (mem_connectedComponentIn hxZ))
    refine hpc.subset_connectedComponentIn (mem_connectedComponentIn hxZ) fun z hz => ?_
    rw [hZO]
    exact ⟨connectedComponentIn_subset Z x hz, hsub hz⟩
  refine ⟨⟨x, hxZ, hcomp.symm⟩, fun heq => ?_⟩
  have heq' : connectedComponentIn Z' x = connectedComponentIn Z y := mem_singleton_iff.mp heq
  have hy : y ∈ connectedComponentIn Z' x := by
    rw [heq']
    exact mem_connectedComponentIn hyZ
  exact hyZ' (connectedComponentIn_subset Z' x hy)

theorem ncard_image_connectedComponentIn_add_one_le {Z Z' O C : Set X} (hO : IsOpen O)
    (hC : IsClosed C) (hZO : Z' = Z ∩ O) (hZC : Z' = Z ∩ C) {y : X} (hyZ : y ∈ Z)
    (hyZ' : y ∉ Z') (hfin : ((fun x => connectedComponentIn Z x) '' Z).Finite) :
    ((fun x => connectedComponentIn Z' x) '' Z').ncard + 1 ≤
      ((fun x => connectedComponentIn Z x) '' Z).ncard := by
  have hsub := image_connectedComponentIn_subset_diff hO hC hZO hZC hyZ hyZ'
  have hmem : connectedComponentIn Z y ∈ (fun x => connectedComponentIn Z x) '' Z :=
    ⟨y, hyZ, rfl⟩
  have hle := Set.ncard_le_ncard hsub (hfin.subset sdiff_subset)
  have hadd := Set.ncard_sdiff_singleton_add_one hmem hfin
  omega

end Components

section Charts

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

theorem HasPLCrossingAt.image_chart_of_mem_maximalAtlas
    {c c' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    (hc : c ∈ (plGroupoid 3).maximalAtlas M) (hc' : c' ∈ (plGroupoid 3).maximalAtlas M)
    {A B : Set M} {y : M} (hy : y ∈ c.source) (hy' : y ∈ c'.source)
    (hcross : HasPLCrossingAt (c' '' (A ∩ c'.source)) (c' '' (B ∩ c'.source)) (c' y)) :
    HasPLCrossingAt (c '' (A ∩ c.source)) (c '' (B ∩ c.source)) (c y) := by
  set e := c.symm.trans c'
  have he : e ∈ plGroupoid 3 := StructureGroupoid.compatible_of_mem_maximalAtlas hc hc'
  have hepa : IsPiecewiseAffineOn e e.source := (mem_plGroupoid_iff.mp he).1
  have hsrc : ∀ z, z ∈ e.source ↔ z ∈ c.target ∧ c.symm z ∈ c'.source := fun z => by
    simp [e]
  have happ : ∀ z, e z = c' (c.symm z) := fun _ => rfl
  have hx : c y ∈ e.source := (hsrc _).mpr ⟨c.map_source hy, by rw [c.left_inv hy]; exact hy'⟩
  have hex : e (c y) = c' y := by rw [happ, c.left_inv hy]
  have hmem : ∀ (X : Set M) {z}, z ∈ e.source →
      (z ∈ c '' (X ∩ c.source) ↔ e z ∈ c' '' (X ∩ c'.source)) := by
    intro X z hz
    obtain ⟨hzt, hz'⟩ := (hsrc z).mp hz
    rw [happ]
    constructor
    · rintro ⟨a, ⟨haX, has⟩, rfl⟩
      rw [c.left_inv has] at hz' ⊢
      exact ⟨a, ⟨haX, hz'⟩, rfl⟩
    · rintro ⟨a, ⟨haX, has'⟩, hae⟩
      have hae' : a = c.symm z := c'.injOn has' hz' hae
      refine ⟨a, ⟨haX, ?_⟩, ?_⟩
      · rw [hae']
        exact c.map_target hzt
      · rw [hae']
        exact c.right_inv hzt
  refine HasPLCrossingAt.of_openPartialHomeomorph e hepa hx (hex ▸ hcross) ?_ ?_
  · filter_upwards [e.open_source.mem_nhds hx] with z hz using hmem A hz
  · filter_upwards [e.open_source.mem_nhds hx] with z hz using hmem B hz

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem eventually_mem_image_inter_source_iff {E : Type*} [TopologicalSpace E]
    {c : OpenPartialHomeomorph M E} {X X' O : Set M} (hO : IsOpen O) (hXO : X ∩ O = X' ∩ O)
    {y : M} (hyO : y ∈ O) (hy : y ∈ c.source) :
    ∀ᶠ z in 𝓝 (c y), z ∈ c '' (X ∩ c.source) ↔ z ∈ c '' (X' ∩ c.source) := by
  have hkey : ∀ {Y Y' : Set M}, Y ∩ O = Y' ∩ O → ∀ a ∈ c.source ∩ O,
      c a ∈ c '' (Y ∩ c.source) → c a ∈ c '' (Y' ∩ c.source) := by
    intro Y Y' hYO a ⟨has, haO⟩ ⟨b, ⟨hbY, hbs⟩, hba⟩
    have hb : b = a := c.injOn hbs has hba
    subst hb
    exact ⟨b, ⟨((Set.ext_iff.mp hYO b).mp ⟨hbY, haO⟩).1, hbs⟩, rfl⟩
  filter_upwards [(c.isOpen_image_source_inter hO).mem_nhds ⟨y, ⟨hy, hyO⟩, rfl⟩] with z hz
  obtain ⟨a, ha, rfl⟩ := hz
  exact ⟨hkey hXO a ha, hkey hXO.symm a ha⟩

end Charts

section Update

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
  {U W : Set M₁} {h : M₁ → M₂} {η ψ : M₁ → ℝ} {H : Finset Ea → Set M₂}
  {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U} {src : Section34CutLabelOf 𝒦 𝒦' → Set M₁}
  {cr : Section34VertexIndex 𝒦 𝒦' → Finset Ea} {f₁ : M₁ → M₂}

omit [FiniteDimensional ℝ Ea] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂] in
theorem Section34Exterior.mono {tgtV : Section34VertexIndex 𝒦 𝒦' → Set M₂}
    {fbl fbl' : Section34SimplexIndex 𝒦 3 → Set M₂} (hext : Section34Exterior 𝒦 𝒦' h H tgtV fbl)
    (hsub : ∀ s, fbl' s ⊆ fbl s) : Section34Exterior 𝒦 𝒦' h H tgtV fbl' := by
  have hobs : ∀ t, section34TetraObstacle tgtV fbl' t ⊆ section34TetraObstacle tgtV fbl t :=
    fun t => union_subset_union Subset.rfl (iUnion₂_mono fun s _ => hsub s)
  obtain ⟨h1, h2, h3⟩ := hext
  refine ⟨fun t => (hobs t).trans (h1 t), h2, fun t w hw y hy hyH => ?_⟩
  obtain ⟨hyo, hne⟩ := h3 t w hw y hy hyH
  exact ⟨fun hyo' => hyo (hobs t hyo'), hne.mono (inter_subset_inter_left _
    (connectedComponentIn_mono y (sdiff_subset_sdiff_right (hobs t))))⟩

omit [FiniteDimensional ℝ Ea] in
open Classical in
theorem section34FaceBallInvariants_update_of_subset
    {tgtV : Section34VertexIndex 𝒦 𝒦' → Set M₂} {tgtEBd : Section34EdgeIndex 𝒦 𝒦' → Set M₂}
    {fbl fblBd : Section34SimplexIndex 𝒦 3 → Set M₂}
    (hinv : Section34FaceBallInvariants 𝒦 𝒦' h H tgtV tgtEBd fbl fblBd)
    {s : Section34SimplexIndex 𝒦 3} {F Fb : Set M₂} (hF : IsPLCellOn 3 F Fb)
    (hrim : h '' simplexRim 𝒦 s.1 ⊆ interior F) (hFs : F ⊆ fbl s)
    (h5 : ∀ y ∈ Fb ∩ frontier (⋃ w, tgtV w), ∃ c ∈ (plGroupoid 3).maximalAtlas M₂,
      y ∈ c.source ∧ HasPLCrossingAt (c '' (Fb ∩ c.source))
        (c '' (frontier (⋃ w, tgtV w) ∩ c.source)) (c y))
    (h6 : ∀ e : Section34EdgeIndex 𝒦 𝒦', ∀ y ∈ Fb ∩ tgtEBd e,
      ∃ c ∈ (plGroupoid 3).maximalAtlas M₂, y ∈ c.source ∧
        HasPLCurveCrossingOnAt (c '' (frontier (⋃ w, tgtV w) ∩ c.source))
          (c '' (Fb ∩ frontier (⋃ w, tgtV w) ∩ c.source)) (c '' (tgtEBd e ∩ c.source)) (c y))
    (h7 : CarriesFirstHomologyOnto (Fb ∩ frontier (section34FaceTorus tgtV s))
      (section34FaceTorus tgtV s))
    (h8 : (Fb ∩ ⋃ e : Section34EdgeIndex 𝒦 𝒦', tgtEBd e).Finite)
    (h9 : ((fun y => connectedComponentIn (Fb ∩ frontier (⋃ w, tgtV w)) y) ''
      (Fb ∩ frontier (⋃ w, tgtV w))).Finite) :
    Section34FaceBallInvariants 𝒦 𝒦' h H tgtV tgtEBd (Function.update fbl s F)
      (Function.update fblBd s Fb) := by
  obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10⟩ := hinv
  have hsub : ∀ s', Function.update fbl s F s' ⊆ fbl s' := by
    intro s'
    rcases eq_or_ne s' s with rfl | hs
    · rw [Function.update_self]
      exact hFs
    · rw [Function.update_of_ne hs]
  refine ⟨fun s' => ?_, fun s' => ?_, fun s' w hw => ?_, fun s₁ s₂ hne => ?_, fun s' => ?_,
    fun s' e => ?_, fun s' => ?_, fun s' => ?_, fun s' => ?_, hc10.mono hsub⟩
  · rcases eq_or_ne s' s with rfl | hs
    · simpa only [Function.update_self] using hF
    · simpa only [Function.update_of_ne hs] using hc1 s'
  · rcases eq_or_ne s' s with rfl | hs
    · simpa only [Function.update_self] using hrim
    · simpa only [Function.update_of_ne hs] using hc2 s'
  · exact subset_eq_empty (inter_subset_inter_left _ (hsub s')) (hc3 s' w hw)
  · exact (inter_subset_inter (hsub s₁) (hsub s₂)).trans (hc4 s₁ s₂ hne)
  · rcases eq_or_ne s' s with rfl | hs
    · simpa only [Function.update_self] using h5
    · simpa only [Function.update_of_ne hs] using hc5 s'
  · rcases eq_or_ne s' s with rfl | hs
    · simpa only [Function.update_self] using h6 e
    · simpa only [Function.update_of_ne hs] using hc6 s' e
  · rcases eq_or_ne s' s with rfl | hs
    · simpa only [Function.update_self] using h7
    · simpa only [Function.update_of_ne hs] using hc7 s'
  · rcases eq_or_ne s' s with rfl | hs
    · simpa only [Function.update_self] using h8
    · simpa only [Function.update_of_ne hs] using hc8 s'
  · rcases eq_or_ne s' s with rfl | hs
    · simpa only [section34TraceComponents, Function.update_self] using h9
    · simpa only [section34TraceComponents, Function.update_of_ne hs] using hc9 s'

omit [FiniteDimensional ℝ Ea] in
theorem finite_setOf_vertexBallImage_inter_nonempty (hctrl : Section34CarrierControl U 𝒦 h η H)
    (hgraph : Section34GraphFrame U W h ψ H 𝒦 𝒦' src cr f₁) {t : Finset Ea}
    (ht : t ∈ 𝒦.complex.faces) :
    {w : Section34VertexIndex 𝒦 𝒦' |
      (section34VertexBallImage src f₁ w ∩ H t).Nonempty}.Finite := by
  obtain ⟨-, hHU, hlf, -, hcell, -⟩ := hctrl
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hcrf, -, hcrfin, hcrH⟩ := hgraph
  have hK : IsCompact (H t) := (hcell t ht).isCompact
  have hloc : ∀ y ∈ H t, ∃ O : Set M₂, IsOpen O ∧ y ∈ O ∧
      {t' | t' ∈ 𝒦.complex.faces ∧ (H t' ∩ O).Nonempty}.Finite := by
    intro y hy
    obtain ⟨V, hV, hfin⟩ := hlf y (hHU t ht hy)
    obtain ⟨O, hO, hyO, hOV⟩ := mem_nhdsWithin.mp hV
    refine ⟨O, hO, hyO, hfin.subset ?_⟩
    rintro t' ⟨ht', z, hzH, hzO⟩
    exact ⟨ht', z, hzH, hOV ⟨hzO, hHU t' ht' hzH⟩⟩
  choose! O hO hyO hOfin using hloc
  obtain ⟨b, hbsub, hbfin, hbcover⟩ := hK.elim_finite_subcover_image (c := O) hO
    fun y hy => mem_iUnion₂.mpr ⟨y, hy, hyO y hy⟩
  have hcar : {t' | t' ∈ 𝒦.complex.faces ∧ (H t' ∩ H t).Nonempty}.Finite := by
    refine (hbfin.biUnion fun y hy => hOfin y (hbsub hy)).subset ?_
    rintro t' ⟨ht', z, hzt', hzt⟩
    obtain ⟨y, hyb, hzy⟩ := mem_iUnion₂.mp (hbcover hzt)
    exact mem_iUnion₂.mpr ⟨y, hyb, ht', z, hzt', hzy⟩
  refine (hcar.biUnion fun σ _ => hcrfin σ).subset ?_
  rintro w ⟨z, hzw, hzt⟩
  exact mem_iUnion₂.mpr ⟨cr w, ⟨hcrf w, z, hcrH w (Or.inr hzw), hzt⟩, rfl⟩

end Update

end DifferentialGeometry.Topology.PiecewiseLinear
