import DifferentialGeometry.Topology.PiecewiseLinear.Approximation.Normalization.CollaredFilling
import DifferentialGeometry.Topology.PiecewiseLinear.Surface.BandFilling.SynchronizedCollar
import DifferentialGeometry.Topology.PiecewiseLinear.Surface.BandFilling.TraceCancellation
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CurrentCarrierBandFilling
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CurrentBandForbiddenBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.Section34SynchronizedBaseArcs
import DifferentialGeometry.Topology.PiecewiseLinear.Section34ExpandedSquareCrossingChartsSwap

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem exists_crosscuts_with_axis_charts
    {A B : Set (ℝ × ℝ)} {δ ε : ℝ → ℝ × ℝ}
    (hδ : IsPLHomeomorphOn δ (Icc 0 1) A) (hε : IsPLHomeomorphOn ε (Icc 0 1) B)
    (hεzero : ε 0 = δ 0) (hεone : ε 1 = δ 1)
    (hA : A ⊆ frontier (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1))
    (hB : B ⊆ frontier (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1))
    (hAB : A ∩ B = {δ 0, δ 1}) {γ : Fin 2 → ℝ → ℝ × ℝ} {c d : ℝ}
    (hc : 0 < c) (hcd : c ≤ 2 * d)
    (hγ : ∀ k, IsPLHomeomorphOn (γ k) (Icc (-d) d) (γ k '' Icc (-d) d))
    (hγbd : ∀ k, γ k '' Icc (-d) d ⊆ frontier (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1))
    (hγzero : γ 0 0 = δ 0) (hγone : γ 1 0 = δ 1)
    (hdis : Disjoint (γ 0 '' Icc (-d) d) (γ 1 '' Icc (-d) d))
    (hpos : ∀ k, γ k '' Icc 0 d ⊆ A) (hneg : ∀ k, γ k '' Icc (-d) 0 ⊆ B) :
    let ηX := fun (k : Fin 2) (r : ℝ) => section34SquareShellFlatten c (γ k (-r / 2), r)
    let ηY := fun (k : Fin 2) (r : ℝ) => section34SquareShellFlatten c (γ k (r / 2), r)
    let X := A ∪ (ηX 0 '' Icc 0 c ∪ ηX 1 '' Icc 0 c)
    let Y := B ∪ (ηY 0 '' Icc 0 c ∪ ηY 1 '' Icc 0 c)
    let Q := Icc (-c) (1 + c) ×ˢ Icc (-c) (1 + c)
    ∃ α β : ℝ → ℝ × ℝ, IsPLHomeomorphOn α (Icc 0 1) X ∧
      IsPLHomeomorphOn β (Icc 0 1) Y ∧
      α 0 = ηX 0 c ∧ α 1 = ηX 1 c ∧ β 0 = ηY 0 c ∧ β 1 = ηY 1 c ∧
      X ⊆ Q ∧ Y ⊆ Q ∧
      X ∩ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) = A ∧
      Y ∩ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) = B ∧
      X ∩ frontier Q = {α 0, α 1} ∧ Y ∩ frontier Q = {β 0, β 1} ∧
      X ∩ Y = {δ 0, δ 1} ∧
    ∀ k, ∃ (e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ)) (ε : ℝ),
      0 < ε ∧ IsPLHomeomorphOn e e.source e.target ∧ e (0, 0) = γ k 0 ∧
      Ioo (-ε) ε ×ˢ Ioo (-ε) ε ⊆ e.source ∧
      (∀ p ∈ Ioo (-ε) ε ×ˢ Ioo (-ε) ε, e p ∈ X ↔ p.2 = 0) ∧
      ∀ s ∈ Ioo (-ε) ε, e (0, s) ∈ Y := by
  obtain ⟨α, β, hα, hβ, hαzero, hαone, hβzero, hβone,
      hXN, hYN, hXQ, hYQ, hXends, hYends, hXY⟩ :=
    exists_expanded_square_crosscuts hδ hε hεzero hεone hA hB hAB hc hcd hγ hγbd
      hγzero hγone hdis
  have hcharts := exists_swapped_axis_charts_of_expanded_square_paths hc hcd hγ hγbd hdis
    hA (by simpa only [hγzero, hγone] using hAB) hpos hneg
  exact ⟨α, β, hα, hβ, hαzero, hαone, hβzero, hβone,
    hXN, hYN, hXQ, hYQ, hXends, hYends, hXY, hcharts⟩

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

theorem exists_trace_cancellation_of_carrier_band
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦') (I : Set (Fin (cnt e)))
    (hlt : 1 < Nat.card I) (Ψ : M₂ ≃ₜ M₂) {K : Set M₂}
    (hK : IsCompact K) (hKS : K ⊆ interior (Sp e)) (hfix : EqOn Ψ id Kᶜ)
    (hΨ : IsPLOn 3 3 Ψ (interior (G (ends e).1 '' Cc (ends e).1)))
    (hrim : Disjoint K (G (ends e).2 '' (Bb₀ e ∪ Bb₁ e)))
    (hout : Disjoint K
      (closure (G (ends e).2 '' CpBd (ends e).2 \ G (ends e).2 '' Bb e)))
    (hkeep : ∀ i : I, Disjoint K (Pg e i.1.val))
    (hcarry : ∀ i : I, CarriesFundamentalGroupOnto (Pg e i.1.val) (Sp e))
    (htrace : G (ends e).1 '' CpBd (ends e).1 ∩ Ψ '' (G (ends e).2 '' CpBd (ends e).2) =
      ⋃ i : I, Pg e i.1.val) :
    ∃ (J : Set I) (Φ : M₂ ≃ₜ M₂) (K₁ : Set M₂), Nat.card J < Nat.card I ∧
      IsCompact K₁ ∧ K₁ ⊆ interior (Sp e) ∧ EqOn Φ id K₁ᶜ ∧
      IsPLOn 3 3 Φ (interior (G (ends e).1 '' Cc (ends e).1)) ∧
      Disjoint K₁ (G (ends e).1 '' (Ab₀ e ∪ Ab₁ e)) ∧
      Disjoint K₁ (G (ends e).2 '' (Bb₀ e ∪ Bb₁ e)) ∧
      Disjoint K₁ (closure (G (ends e).2 '' CpBd (ends e).2 \ G (ends e).2 '' Bb e)) ∧
      (∀ j : J, Disjoint K₁ (Pg e j.1.1.val)) ∧
      (∀ j : J, ∀ x ∈ Pg e j.1.1.val, Φ =ᶠ[𝓝 x] id) ∧
      G (ends e).1 '' CpBd (ends e).1 ∩ Φ '' (Ψ '' (G (ends e).2 '' CpBd (ends e).2)) =
        ⋃ j : J, Pg e j.1.1.val := by
  obtain ⟨i, j, hij, D, F, hFA, hDB, hfill⟩ :=
    exists_section34_current_carrier_band_filling hprep hpack e I hlt Ψ hK hKS hfix hΨ
      hrim hkeep hcarry htrace
  obtain ⟨-, -, hCpCc, -, hCp, -, -, -, -, -, -, -, hSnCc, -⟩ := id hprep
  obtain ⟨-, -, -, htube, -, -, -, -, -, -, hGp, -, -, -, -, -, -, hPg, hdis, -⟩ := id hpack
  have hSpCc : Sp e ⊆ G (ends e).1 '' Cc (ends e).1 := by
    rw [(htube e).1]
    exact image_mono (hSnCc e _ (Or.inl rfl))
  have hcellB := ((hCp (ends e).2).image (hGp (ends e).2)).image_of_supported_isPLOn
    Ψ hΨ isOpen_interior hK.isClosed (hKS.trans (interior_mono hSpCc)) hfix
  have hseams : Disjoint K (Pg e i.1.val ∪ Pg e j.1.val) :=
    disjoint_union_right.mpr ⟨hkeep i, hkeep j⟩
  have hnear : ∀ x ∈ Pg e i.1.val ∪ Pg e j.1.val, Ψ =ᶠ[𝓝 x] id := by
    intro x hx
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds
      (disjoint_right.mp hseams hx)] with y hy
    exact hfix hy
  have hij' : i.1.val ≠ j.1.val := fun heq => hij (Subtype.ext (Fin.ext heq))
  obtain ⟨P, u, R, g₀, a, A₀, A₁, δ₀, δ₁, hP, hu, hcell, hRfin, hR, hRP, hsolid,
    hg₀, hends₀, hside₀, hfront₀, hT, hfirst, hsecond, hcontact, hposition, ha, hinj,
    hzero₀, hone₀, hδ₀, hδ₁, hδ₀₀, hδ₀₁, hδ₁₀, hδ₁₁, hcover, hinter, hface₀₀, hface₁₀⟩ := id hfill
  have hext := exists_collared_annular_filling_of_transported_sheet hprep hpack e
    i.1.isLt j.1.isLt hij' Ψ hnear hcellB
    P u R g₀ a A₀ A₁ δ₀ δ₁ hP hu hcell hRfin hR hRP hsolid.1 hg₀ hends₀
    hT hfirst hsecond hzero₀ hone₀ hδ₀ hδ₁ hδ₀₀ hδ₀₁ hδ₁₀ hδ₁₁ hcover hinter hface₀₀ hface₁₀
  obtain ⟨C, f, α, β, hCdis, htarget, hfamily, c₀, L, W₀, ρ, H₀,
    hbase₀, hH₀, hH₀ends, hH₀eq, hshell₀, hsupport₀, hc₀, hc₀1, hLfin, hL,
    hLB, hJL, hLnhds, haxisModel, hW₀, hWP₀, hWSp₀, hρ₀, hρzero, hWR₀,
    hpositive₀, hread, hfull, hlevels, Hc, θ, b, ν, hHc,
    hg, hends, hface₀, hface₁, hPgfib, hframe⟩ := hext
  obtain ⟨hZ, hZsheet, hZfaces⟩ := section34_current_band_forbidden_boundary hprep hpack e
    i.1.isLt j.1.isLt Ψ (fun _ hx => hfix (disjoint_right.mp hseams hx))
    hcellB hfill hFA hDB
  have hBrim : Ψ '' (G (ends e).2 '' (Bb₀ e ∪ Bb₁ e)) =
      G (ends e).2 '' (Bb₀ e ∪ Bb₁ e) :=
    (image_congr fun _ hx => hfix (disjoint_right.mp hrim hx)).trans (image_id' _)
  have houtside : Ψ '' (G (ends e).2 '' CpBd (ends e).2) \
      Ψ '' (G (ends e).2 '' Bb e) =
      G (ends e).2 '' CpBd (ends e).2 \ G (ends e).2 '' Bb e := by
    rw [← image_sdiff Ψ.injective]
    exact (image_congr fun _ hx => hfix
      (disjoint_right.mp hout (subset_closure hx))).trans (image_id' _)
  rw [hBrim, houtside] at hZ hZsheet hZfaces
  have hAs : G (ends e).1 '' CpBd (ends e).1 ⊆ G (ends e).1 '' Cc (ends e).1 :=
    image_mono ((hCp _).boundary_subset.trans (hCpCc _).2.1)
  have hpair : Pairwise fun k l : I => Disjoint (Pg e k.1.val) (Pg e l.1.val) :=
    fun k l hkl => hdis e k.1.val k.1.isLt l.1.val l.1.isLt
      (fun heq => hkl (Subtype.ext (Fin.ext heq)))
  let g := Hc ∘ g₀
  let Q := Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1
  let γ := fun (k : Fin 2) (t : ℝ) => θ k (t / 2 + 1 / 2, 0)
  have hγ (k : Fin 2) : MapsTo (γ k) (Icc (-b k) (b k)) (frontier Q) := by
    have hθbd : θ k '' frontier Q = frontier Q := by
      obtain ⟨v, hv⟩ := isPLBall_unit_square
      conv_lhs => rw [← hv.image_stdSimplexBoundary_eq_frontier_real_prod, ← image_comp]
      exact (hv.trans (hframe k).1).image_stdSimplexBoundary_eq_frontier_real_prod
    intro t ht
    apply hθbd.subset
    refine ⟨(t / 2 + 1 / 2, 0), ?_, rfl⟩
    rw [frontier_prod_eq, isClosed_Icc.closure_eq, frontier_Icc (zero_le_one' ℝ)]
    refine Or.inl ⟨?_, by simp⟩
    constructor <;> linarith [ht.1, ht.2, (hframe k).2.2.2.1]
  have hγzero (k : Fin 2) : γ k 0 = a k := by
    simpa only [γ, zero_div, zero_add] using (hframe k).2.1
  have hγcore (k : Fin 2) : γ k 0 ∈ A₀ ∩ A₁ := by
    rw [hγzero]
    fin_cases k
    · exact ⟨hδ₀₀ ▸ hδ₀.bijOn.mapsTo (by norm_num : (0 : ℝ) ∈ Icc 0 1),
        hδ₁₀ ▸ hδ₁.bijOn.mapsTo (by norm_num : (0 : ℝ) ∈ Icc 0 1)⟩
    · exact ⟨hδ₀₁ ▸ hδ₀.bijOn.mapsTo (by norm_num : (1 : ℝ) ∈ Icc 0 1),
        hδ₁₁ ▸ hδ₁.bijOn.mapsTo (by norm_num : (1 : ℝ) ∈ Icc 0 1)⟩
  have hLn (k : Fin 2) : L.space ∈ 𝓝ˢ[frontier R.space] (f k '' section34MarkedAxis) := by
    rw [nhdsSetWithin, Filter.mem_inf_principal, mem_nhdsSet_iff_forall]
    intro x hx
    apply Filter.mem_inf_principal.mp
    apply hLnhds x
    fin_cases k
    · exact Or.inl hx
    · exact Or.inr hx
  have hRZ : Disjoint (u '' R.space) ((G (ends e).1 '' (Ab₀ e ∪ Ab₁ e) ∪ G (ends e).2 '' (Bb₀ e ∪ Bb₁ e)) ∪
      closure (G (ends e).2 '' CpBd (ends e).2 \ G (ends e).2 '' Bb e)) := by
    apply disjoint_left.mpr
    intro x hx hxZ
    apply disjoint_left.mp hZfaces hxZ
    rcases hZsheet hxZ with hA | hB
    · exact Or.inr (hfirst ▸ ⟨hA, hx⟩)
    · exact Or.inl (hsecond ▸ ⟨hB, hx⟩)
  obtain ⟨c, H, hc, hcc, hc1, hce, hWW, hρ, hWR, hVP, hsupport,
    hH, hHends, hHeq, hshell, hγsides, hfeet, hshellread, htraceA, htraceB, havoid⟩ :=
    exists_synchronized_collared_filling_avoiding hu.injOn hu.continuousOn hg hends hRP
      hcover (hfirst.trans hface₀.symm) (hsecond.trans hface₁.symm)
      (fun k => (hfamily k).2.2.1) (fun k => (hfamily k).2.2.2.2.2.1)
      (fun k => (hfamily k).2.2.2.2.2.2.1)
      (fun k => (hfamily k).2.2.2.2.2.2.2.2.2.2) hc₀ hρ₀ hρzero hWR₀ hWP₀ hsupport₀
      hLn (fun k p hp s hs hx t ht => (hread k p hp s hs hx t ht).1) hlevels
      (fun k => (hframe k).2.2.1)
      (fun k => (hframe k).2.2.2.1.trans (by norm_num : (1 / 2 : ℝ) ≤ 1))
      hγ hγcore (fun k => (hframe k).2.2.2.2.1.bijOn.mapsTo)
      (fun k => (hframe k).2.2.2.2.1.bijOn.surjOn)
      (fun k => (hframe k).2.2.2.2.2.1) (fun k => (hframe k).2.2.2.2.2.2) hZ hRZ
  let W := ρ '' (frontier R.space ×ˢ Icc (0 : ℝ) c)
  let N := Icc (-c) (1 + c) ×ˢ Icc (-c) (1 + c)
  let d := min (b 0) (b 1)
  let η₀ := fun (k : Fin 2) (t : ℝ) => section34SquareShellFlatten c (γ k (-t / 2), t)
  let η₁ := fun (k : Fin 2) (t : ℝ) => section34SquareShellFlatten c (γ k (t / 2), t)
  let X := A₀ ∪ (η₀ 0 '' Icc 0 c ∪ η₀ 1 '' Icc 0 c)
  let Y := A₁ ∪ (η₁ 0 '' Icc 0 c ∪ η₁ 1 '' Icc 0 c)
  obtain ⟨_, hdb, hγPL, hγbd, _, hdisγ⟩ := synchronized_base_arcs
    (fun k => (hframe k).1) (fun k => (hframe k).2.1)
    (fun k => (hframe k).2.2.1) (fun k => (hframe k).2.2.2.1)
    (fun k => (hframe k).2.2.2.2.1.bijOn.mapsTo)
    (fun k => (hfamily k).2.2.1) hCdis
    (fun k => (hframe k).2.2.2.2.2.1) (fun k => (hframe k).2.2.2.2.2.2)
  have hcd : c ≤ 2 * d := by
    have h : c / 2 ≤ d := le_min (hce 0) (hce 1)
    linarith
  have hAbd : A₀ ⊆ frontier Q := subset_union_left.trans hcover.subset
  have hBbd : A₁ ⊆ frontier Q := subset_union_right.trans hcover.subset
  have hpos (k : Fin 2) : γ k '' Icc (0 : ℝ) d ⊆ A₀ :=
    (image_mono (Icc_subset_Icc le_rfl (hdb k))).trans (hγsides k).1
  have hneg (k : Fin 2) : γ k '' Icc (-d) 0 ⊆ A₁ :=
    (image_mono (Icc_subset_Icc (neg_le_neg (hdb k)) le_rfl)).trans (hγsides k).2
  obtain ⟨δ, ε, hδ, hε, _, _, _, _, hXN, hYN, _, _, hXends, hYends, hXY, hex⟩ :=
    exists_crosscuts_with_axis_charts hδ₀ hδ₁ (hδ₁₀.trans hδ₀₀.symm)
      (hδ₁₁.trans hδ₀₁.symm) hAbd hBbd (hinter.trans (by rw [hδ₀₀, hδ₀₁]))
      hc hcd hγPL hγbd ((hγzero 0).trans hδ₀₀.symm)
      ((hγzero 1).trans hδ₀₁.symm) hdisγ hpos hneg
  choose κ r hr hκ hcenter hsource hcurve haxis using hex
  have hN : IsPLBall 2 N :=
    isPLBall_two_prod (isPLBall_Icc (by linarith)) (isPLBall_Icc (by linarith))
  have hQint : Q ⊆ interior N := by
    rw [interior_prod_eq, interior_Icc]
    rintro p hp
    exact ⟨by constructor <;> linarith [hp.1.1, hp.1.2],
      by constructor <;> linarith [hp.2.1, hp.2.2]⟩
  have haQ (k : Fin 2) : a k ∈ Q := by
    rw [← hγzero k]
    exact (isClosed_Icc.prod isClosed_Icc).frontier_subset
      (hγbd k (mem_image_of_mem _ (by constructor <;> linarith [hc, hcd])))
  have hane : a 0 ≠ a 1 := by
    intro heq
    have hh := hδ₀.bijOn.injOn (by norm_num : (0 : ℝ) ∈ Icc 0 1)
      (by norm_num : (1 : ℝ) ∈ Icc 0 1) (hδ₀₀.trans (heq.trans hδ₀₁.symm))
    norm_num at hh
  have hunion (T : Fin 2 → Set (ℝ × ℝ)) : (⋃ k, T k) = T 0 ∪ T 1 := by
    ext x
    simp only [mem_iUnion, mem_union]
    constructor
    · rintro ⟨k, hk⟩
      fin_cases k
      · exact Or.inl hk
      · exact Or.inr hk
    · rintro (hx | hx)
      · exact ⟨0, hx⟩
      · exact ⟨1, hx⟩
  have hXY' : X ∩ Y = {a 0, a 1} := by simpa only [hδ₀₀, hδ₀₁] using hXY
  have hPg' (k : Fin 2) : (u ∘ H) '' ({a k} ×ˢ Icc (0 : ℝ) 1) = ![Pg e i.1.val, Pg e j.1.val] k := by
    rw [image_comp, (hHeq.mono (prod_mono_left (singleton_subset_iff.mpr (haQ k)))).image_eq,
      ← image_comp]
    exact hPgfib k
  have hfirst' : u '' (R.space ∪ W) ∩ (G (ends e).1 '' CpBd (ends e).1) = (u ∘ H) '' (X ×ˢ Icc (0 : ℝ) 1) := by
    simpa only [hunion] using htraceA
  have hsecond' : u '' (R.space ∪ W) ∩ (Ψ '' (G (ends e).2 '' CpBd (ends e).2)) = (u ∘ H) '' (Y ×ˢ Icc (0 : ℝ) 1) := by
    simpa only [hunion] using htraceB
  obtain ⟨J, Φ, hlt', hK₁, hK₁S, hfix₁, hΦ, _, hkeep₁, hgerms, htrace₁, havoid, _⟩ :=
    exists_relative_annular_trace_cancellation_avoiding hP.isPolyhedron hu hVP hsupport
      (hAs.trans hcell.symm.subset) hN hH hHends hδ hε hXN hYN hXends hYends a hXY'
      hane (fun k => hQint (haQ k)) hPg' hfirst' hsecond' κ r hr hsource
      (fun k => (hcenter k).trans (hγzero k)) hcurve haxis
      (fun k : I => (hPg e k.1.val k.1.isLt).1) hpair htrace havoid
  let K₁ := u '' (R.space ∪ W)
  obtain ⟨havoidRims, havoidOut⟩ := disjoint_union_right.mp havoid
  obtain ⟨havoidA, havoidB⟩ := disjoint_union_right.mp havoidRims
  exact ⟨J, Φ, K₁, hlt', hK₁, hK₁S, hfix₁, hcell ▸ hΦ, havoidA, havoidB, havoidOut,
    hkeep₁, hgerms, htrace₁⟩

end DifferentialGeometry.Topology.PiecewiseLinear
