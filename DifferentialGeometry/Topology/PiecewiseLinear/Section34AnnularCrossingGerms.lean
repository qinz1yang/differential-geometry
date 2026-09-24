import DifferentialGeometry.Topology.PiecewiseLinear.Section34CrossingOutsideDensity

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem side_chart_subset {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {A X U N : Set E} {x : E} {φ : E → ℝ × ℝ × ℝ} {ρ : ℝ}
    (hU : IsOpen U) (hxU : x ∈ U) (hφ : IsPLHomeomorphOn φ U (Metric.ball 0 ρ))
    (hφx : φ x = 0)
    (hloc : ∀ y ∈ U, (y ∈ A ↔ (φ y).2.2 = 0) ∧
      (y ∈ frontier X ↔ (φ y).2.1 = 0) ∧ (y ∈ X ↔ 0 ≤ (φ y).2.1))
    (hN : N ∈ 𝓝 x) :
    ∃ (V : Set E) (r : ℝ), IsOpen V ∧ x ∈ V ∧ V ⊆ N ∧ 0 < r ∧
      IsPLHomeomorphOn φ V (Metric.ball 0 r) ∧
      ∀ y ∈ V, (y ∈ A ↔ (φ y).2.2 = 0) ∧
        (y ∈ frontier X ↔ (φ y).2.1 = 0) ∧ (y ∈ X ↔ 0 ≤ (φ y).2.1) := by
  obtain ⟨S, hSN, hS, hxS⟩ := mem_nhds_iff.mp hN
  have hopen : IsOpen (φ '' (S ∩ U)) :=
    hφ.isOpen_image_of_isOpen Metric.isOpen_ball (hS.inter hU) inter_subset_right
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen 0 ⟨x, ⟨hxS, hxU⟩, hφx⟩
  let V := S ∩ (U ∩ φ ⁻¹' Metric.ball 0 r)
  have hVo : IsOpen V := hS.inter
    (hφ.isPiecewiseAffineOn.continuousOn.isOpen_inter_preimage hU Metric.isOpen_ball)
  have hVU : V ⊆ U := fun _ hy => hy.2.1
  have himage : φ '' V = Metric.ball 0 r := by
    apply Subset.antisymm
    · rintro _ ⟨y, hy, rfl⟩
      exact hy.2.2
    · intro z hz
      obtain ⟨y, hy, rfl⟩ := hball hz
      exact ⟨y, ⟨hy.1, hy.2, hz⟩, rfl⟩
  refine ⟨V, r, hVo, ⟨hxS, hxU, ?_⟩, fun _ hy => hSN hy.1, hr, ?_, ?_⟩
  · simpa [hφx] using (Metric.mem_ball_self hr : (0 : ℝ × ℝ × ℝ) ∈ Metric.ball 0 r)
  · have hh := hφ.restrict_isOpen hVo hVU (himage ▸ Metric.isOpen_ball)
    rwa [himage] at hh
  · exact fun y hy => hloc y (hVU hy)

theorem HasPLCrossingAt.exists_connected_ambient_sides {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {A X N : Set E} {x : E}
    (hcross : HasPLCrossingAt A (frontier X) x)
    (hA : ∀ W ∈ 𝓝 x, ∃ (c : EuclideanSpace ℝ (Fin 2)) (r : ℝ)
      (g : EuclideanSpace ℝ (Fin 2) → E), 0 < r ∧ ContinuousOn g (Metric.ball c r) ∧
        InjOn g (Metric.ball c r) ∧ MapsTo g (Metric.ball c r) (A ∩ W) ∧ g c = x)
    (hXc : IsClosed X) (hX : x ∈ closure (interior X)) (hN : N ∈ 𝓝 x) :
    ∃ V : Set E, IsOpen V ∧ x ∈ V ∧ V ⊆ N ∧
      IsPreconnected (V ∩ interior X) ∧ IsPreconnected (V ∩ Xᶜ) := by
  obtain ⟨U, φ, ρ, hU, hxU, -, hφ, hφx, hloc⟩ := hcross.exists_sideChart hA hXc hX
  obtain ⟨V, r, hV, hxV, hVN, -, hφV, hlocV⟩ :=
    side_chart_subset hU hxU hφ hφx hloc hN
  let ψ := Function.invFunOn φ V
  have hψφ : ∀ y ∈ V, ψ (φ y) = y := fun y hy => hφV.bijOn.invOn_invFunOn.1 hy
  have hφψ : ∀ z ∈ Metric.ball (0 : ℝ × ℝ × ℝ) r, φ (ψ z) = z :=
    fun z hz => hφV.bijOn.invOn_invFunOn.2 hz
  have hψV : ∀ z ∈ Metric.ball (0 : ℝ × ℝ × ℝ) r, ψ z ∈ V :=
    fun z hz => hφV.symm.bijOn.mapsTo hz
  have hψc : ContinuousOn ψ (Metric.ball (0 : ℝ × ℝ × ℝ) r) :=
    hφV.isPiecewiseAffineOn_invFunOn.continuousOn
  have hinside : ∀ y ∈ V, y ∈ interior X ↔ 0 < (φ y).2.1 := by
    intro y hy
    constructor
    · intro hyX
      have hnn := (hlocV y hy).2.2.mp (interior_subset hyX)
      refine lt_of_le_of_ne hnn ?_
      intro heq
      exact disjoint_left.mp disjoint_interior_frontier hyX
        ((hlocV y hy).2.1.mpr heq.symm)
    · intro hpos
      have hyX := (hlocV y hy).2.2.mpr hpos.le
      exact (mem_interior_iff_notMem_frontier hyX).mpr fun hyfr =>
        hpos.ne' ((hlocV y hy).2.1.mp hyfr)
  have houtside : ∀ y ∈ V, y ∈ Xᶜ ↔ (φ y).2.1 < 0 := by
    intro y hy
    exact ((hlocV y hy).2.2.not).trans not_le
  have hlin : IsLinearMap ℝ (fun z : ℝ × ℝ × ℝ => z.2.1) :=
    ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  have hplus : ψ '' (Metric.ball 0 r ∩ {z : ℝ × ℝ × ℝ | 0 < z.2.1}) =
      V ∩ interior X := by
    apply Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      refine ⟨hψV z hz.1, (hinside _ (hψV z hz.1)).mpr ?_⟩
      rw [hφψ z hz.1]
      exact hz.2
    · rintro y ⟨hyV, hyX⟩
      exact ⟨φ y, ⟨hφV.bijOn.mapsTo hyV, (hinside y hyV).mp hyX⟩, hψφ y hyV⟩
  have hminus : ψ '' (Metric.ball 0 r ∩ {z : ℝ × ℝ × ℝ | z.2.1 < 0}) = V ∩ Xᶜ := by
    apply Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      refine ⟨hψV z hz.1, (houtside _ (hψV z hz.1)).mpr ?_⟩
      rw [hφψ z hz.1]
      exact hz.2
    · rintro y ⟨hyV, hyX⟩
      exact ⟨φ y, ⟨hφV.bijOn.mapsTo hyV, (houtside y hyV).mp hyX⟩, hψφ y hyV⟩
  refine ⟨V, hV, hxV, hVN, ?_, ?_⟩
  · rw [← hplus]
    exact ((convex_ball (0 : ℝ × ℝ × ℝ) r).inter (convex_halfSpace_gt hlin 0)).isPreconnected
      |>.image ψ (hψc.mono inter_subset_left)
  · rw [← hminus]
    exact ((convex_ball (0 : ℝ × ℝ × ℝ) r).inter (convex_halfSpace_lt hlin 0)).isPreconnected
      |>.image ψ (hψc.mono inter_subset_left)

theorem exists_connected_ambient_sides_of_chart_crossing {M : Type*} [TopologicalSpace M]
    {A X N : Set M} {x : M} (hXc : IsClosed X) (hX : x ∈ closure (interior X))
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))) (hx : x ∈ c.source)
    (hcross : HasPLCrossingAt (c '' (A ∩ c.source))
      (c '' (frontier X ∩ c.source)) (c x))
    (hA : ∀ W ∈ 𝓝 x, ∃ (a : EuclideanSpace ℝ (Fin 2)) (r : ℝ)
      (g : EuclideanSpace ℝ (Fin 2) → M), 0 < r ∧ ContinuousOn g (Metric.ball a r) ∧
        InjOn g (Metric.ball a r) ∧ MapsTo g (Metric.ball a r) (A ∩ W) ∧ g a = x)
    (hN : N ∈ 𝓝 x) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ U ⊆ N ∧
      IsPreconnected (U ∩ interior X) ∧ IsPreconnected (U ∩ Xᶜ) := by
  have himage (Z : Set M) : c.IsImage Z (c '' (Z ∩ c.source)) := by
    intro y hy
    constructor
    · rintro ⟨z, ⟨hz, hzs⟩, hzy⟩
      exact c.injOn hzs hy hzy ▸ hz
    · exact fun hyZ => ⟨y, ⟨hyZ, hy⟩, rfl⟩
  let Y := closure (c '' (X ∩ c.source))
  have hY : c.IsImage X Y := by
    have hh := (himage X).closure
    rwa [hXc.closure_eq] at hh
  have hfront : ∀ᶠ z in 𝓝 (c x),
      z ∈ c '' (frontier X ∩ c.source) ↔ z ∈ frontier Y := by
    filter_upwards [c.open_target.mem_nhds (c.map_source hx)] with z hz
    exact ((himage (frontier X)).symm hz).symm.trans (hY.frontier.symm hz)
  have hcross' : HasPLCrossingAt (c '' (A ∩ c.source)) (frontier Y) (c x) :=
    hcross.congr (Filter.Eventually.of_forall fun _ => Iff.rfl) hfront
  have hAc : ∀ W ∈ 𝓝 (c x), ∃ (a : EuclideanSpace ℝ (Fin 2)) (r : ℝ)
      (g : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)),
      0 < r ∧ ContinuousOn g (Metric.ball a r) ∧ InjOn g (Metric.ball a r) ∧
        MapsTo g (Metric.ball a r) ((c '' (A ∩ c.source)) ∩ W) ∧ g a = c x := by
    intro W hW
    have hpre : c.source ∩ c ⁻¹' W ∈ 𝓝 x := Filter.inter_mem
      (c.open_source.mem_nhds hx) ((c.continuousAt hx).preimage_mem_nhds hW)
    obtain ⟨a, r, g, hr, hgc, hgi, hgmap, hga⟩ := hA _ hpre
    have hgs : MapsTo g (Metric.ball a r) c.source := fun y hy => (hgmap hy).2.1
    refine ⟨a, r, c ∘ g, hr, c.continuousOn.comp hgc hgs, ?_, ?_, ?_⟩
    · intro y hy z hz hyz
      exact hgi hy hz (c.injOn (hgs hy) (hgs hz) hyz)
    · intro y hy
      exact ⟨⟨g y, ⟨(hgmap hy).1, (hgmap hy).2.1⟩, rfl⟩, (hgmap hy).2.2⟩
    · change c (g a) = c x
      rw [hga]
  obtain ⟨S, hSN, hS, hxS⟩ := mem_nhds_iff.mp hN
  have hNs : c '' (c.source ∩ S) ∈ 𝓝 (c x) :=
    (c.isOpen_image_source_inter hS).mem_nhds ⟨x, ⟨hx, hxS⟩, rfl⟩
  obtain ⟨V, hV, hxV, hVN, hconn, hconn'⟩ := hcross'.exists_connected_ambient_sides hAc
    isClosed_closure ((hY.interior.closure hx).mpr hX) hNs
  have hVT : V ⊆ c.target := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := hVN hz
    exact c.map_source hy.1
  let U := c.source ∩ c ⁻¹' V
  have heq (Z : Set M) (W : Set (EuclideanSpace ℝ (Fin 3))) (h : c.IsImage Z W) :
      c.symm '' (V ∩ W) = U ∩ Z := by
    apply Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      refine ⟨⟨c.map_target (hVT hz.1), ?_⟩, (h.symm (hVT hz.1)).mpr hz.2⟩
      change c (c.symm z) ∈ V
      rw [c.right_inv (hVT hz.1)]
      exact hz.1
    · rintro y ⟨⟨hys, hyV⟩, hyZ⟩
      exact ⟨c y, ⟨hyV, (h hys).mpr hyZ⟩, c.left_inv hys⟩
  refine ⟨U, c.isOpen_inter_preimage hV, ⟨hx, hxV⟩, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨z, hz, hzy⟩ := hVN hy.2
    exact hSN (c.injOn hz.1 hy.1 hzy ▸ hz.2)
  · rw [← heq _ _ hY.interior]
    exact hconn.image c.symm (c.symm.continuousOn.mono (inter_subset_left.trans hVT))
  · rw [← heq _ _ hY.compl]
    exact hconn'.image c.symm (c.symm.continuousOn.mono (inter_subset_left.trans hVT))

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂] {U : Set M₁} {h : M₁ → M₂}
  {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src : Section34CutLabelOf 𝒦 𝒦' → Set M₁}
  {Q : Section34VertexIndex 𝒦 𝒦' → Set M₂}
  {Cp CpBd Cc CcBd Kcore : Section34VertexIndex 𝒦 𝒦' → Set M₁}
  {ε : Section34VertexIndex 𝒦 𝒦' → ℝ}
  {ends : Section34EdgeIndex 𝒦 𝒦' →
    Section34VertexIndex 𝒦 𝒦' × Section34VertexIndex 𝒦 𝒦'}
  {Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ : Section34EdgeIndex 𝒦 𝒦' → Set M₁}
  {Sp Tp : Section34EdgeIndex 𝒦 𝒦' → Set M₂} {cnt : Section34EdgeIndex 𝒦 𝒦' → ℕ}
  {Pg : Section34EdgeIndex 𝒦 𝒦' → ℕ → Set M₂}
  {G : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂}


theorem section34_crossing_connected_ambient_sides
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦') {x : M₂}
    (hx : x ∈ G (ends e).1 '' CpBd (ends e).1 ∩ G (ends e).2 '' Bb e)
    {N : Set M₂} (hN : N ∈ 𝓝 x) :
    ∃ V : Set M₂, IsOpen V ∧ x ∈ V ∧ V ⊆ N ∧
      IsPreconnected (V ∩ interior (G (ends e).1 '' Cp (ends e).1)) ∧
      IsPreconnected (V ∩ (G (ends e).1 '' Cp (ends e).1)ᶜ) := by
  have hAeq := section34_first_annulus_eq_boundary_inter_tube hprep hpack e
  have hann := (section34_piercing_annuli hprep hpack e).2
  obtain ⟨-, -, hsub, -, hCp, -, -, -, -, -, -, -, -, -, -, hBb, -⟩ := id hprep
  obtain ⟨hG, -, -, -, -, -, hmeet, -, hBdis, -, hGp, -, -, -, -, -, -, -, -, hcross, -⟩ :=
    id hpack
  have hcellA := (hCp (ends e).1).image (hGp (ends e).1)
  have hcellB := (hCp (ends e).2).image (hGp (ends e).2)
  have hxmeet := hmeet e ⟨hx.1, image_mono (hBb e).1 hx.2⟩
  have hxtrace : x ∈ G (ends e).1 '' Aa e ∩ G (ends e).2 '' Bb e :=
    ⟨image_mono sdiff_subset hxmeet.1.1, hx.2⟩
  obtain ⟨c, -, hxc, hcross⟩ := hcross e x hxtrace
  have hcongr : ∀ᶠ z in 𝓝 (c x),
      z ∈ c '' (G (ends e).1 '' Aa e ∩ c.source) ↔
        z ∈ c '' (frontier (G (ends e).1 '' Cp (ends e).1) ∩ c.source) := by
    filter_upwards [(c.isOpen_image_source_inter isOpen_interior).mem_nhds
      ⟨x, ⟨hxc, hxmeet.2⟩, rfl⟩] with z hz
    obtain ⟨y, ⟨hys, hyT⟩, rfl⟩ := hz
    have hmem (S : Set M₂) : c y ∈ c '' (S ∩ c.source) ↔ y ∈ S := by
      constructor
      · rintro ⟨w, ⟨hw, hws⟩, hwy⟩
        exact c.injOn hws hys hwy ▸ hw
      · exact fun hy => ⟨y, ⟨hy, hys⟩, rfl⟩
    rw [hmem, hmem, hAeq, ← hcellA.boundary_eq_frontier]
    exact and_iff_left (interior_subset hyT)
  have hcross' := hcross.symm.congr (Filter.Eventually.of_forall fun _ => Iff.rfl) hcongr
  refine exists_connected_ambient_sides_of_chart_crossing hcellA.isCompact.isClosed
    (X := G (ends e).1 '' Cp (ends e).1) ?_ c hxc hcross' ?_ hN
  · have hcl : closure (interior (G (ends e).1 '' Cp (ends e).1)) =
        G (ends e).1 '' Cp (ends e).1 := by
      rw [← hcellA.sdiff_boundary_eq_interior]
      exact hcellA.closure_sdiff_boundary
    rw [hcl]
    exact hcellA.boundary_subset hx.1
  · intro N hN
    apply hcellB.exists_ball_chart_in_annulus hann (image_mono (hBb e).1) hx.2 ?_ hN
    intro hxends
    rw [← image_union] at hxends
    exact disjoint_left.mp (hBdis e).2 hxends (interior_subset hxmeet.2)

end DifferentialGeometry.Topology.PiecewiseLinear
