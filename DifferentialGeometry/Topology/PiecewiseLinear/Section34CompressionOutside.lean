/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompressionShell
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompressionChartBall
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompressionReroute
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompressionTraceCarry
import DifferentialGeometry.Topology.PiecewiseLinear.Section34FaceTorusCycle

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)

section Chart

theorem disjoint_torus_of_disjoint_interior {P X Θ Lx Bx Rest Tc : Set E3}
    (hP : IsPLBall 3 P) (hX : IsPLBall 3 X) (hPX : Disjoint (interior P) X)
    (hXf : frontier X = Lx ∪ Bx) (hPf : frontier P = Bx ∪ Rest) (hLc : IsClosed Lx)
    (hRc : IsClosed Rest) (hBR : Bx ∩ Rest ⊆ Lx) (hLΘ : Disjoint Lx Θ)
    (hΘX : Disjoint Θ (interior X)) (hΘ : Θ = frontier Tc) (hTc : IsClosed Tc)
    (hcross : ∀ y ∈ frontier P ∩ Θ, HasPLCrossingAt (frontier P) Θ y)
    (hreg : ∀ y ∈ Θ, y ∈ closure (interior Tc)) : Disjoint Bx Θ := by
  have hdim : Module.finrank ℝ E3 = 2 + 1 := by simp
  have hPc : IsClosed P := hP.isPolyhedron.isClosed
  refine Set.disjoint_left.mpr fun y hyB hyΘ => ?_
  have hyL : y ∉ Lx := fun h => Set.disjoint_left.mp hLΘ h hyΘ
  have hyR : y ∉ Rest := fun h => hyL (hBR ⟨hyB, h⟩)
  have hO : IsOpen (Lx ∪ Rest)ᶜ := (hLc.union hRc).isOpen_compl
  have hyO : y ∈ (Lx ∪ Rest)ᶜ := fun h => h.elim hyL hyR
  have hyP : y ∈ frontier P := hPf ▸ Or.inl hyB
  have hfr : (Lx ∪ Rest)ᶜ ∩ frontier P = (Lx ∪ Rest)ᶜ ∩ frontier X := by
    rw [hPf, hXf]
    ext z
    simp only [mem_inter_iff, mem_compl_iff, mem_union]
    tauto
  have hyint := mem_interior_union_of_inter_frontier_eq hP hX hO hfr
    (hPX.mono_right interior_subset) hyO hyP
  obtain ⟨B, hBsub, hBo, hyBo⟩ := mem_interior.mp hyint
  have hcr := hcross y ⟨hyP, hyΘ⟩
  rw [hΘ] at hcr
  obtain ⟨U, φ, ρ, hU, hyU, hρ, hφ, hφy, hloc⟩ := hcr.exists_lineChart hyP
    (hP.isPLSphere_frontier.exists_isOpen_inter_homeomorph_of_two hyP) hTc (hreg y hyΘ)
  have hside := side_of_frontier_plane_snd_snd hU hyU hφ hφy (fun z hz => (hloc z hz).1) hPc
    (by rw [hP.closure_interior_of_finrank hdim]; exact hPc.frontier_subset hyP)
  have hopen : IsOpen (φ '' (U ∩ B)) :=
    hφ.isOpen_image_of_isOpen Metric.isOpen_ball (hU.inter hBo) inter_subset_left
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen 0 ⟨y, ⟨hyU, hyBo⟩, hφy⟩
  set a : ℝ := min r ρ / 2 with hadef
  have ha : 0 < a := by positivity
  have hpt : ∀ σ : ℝ, (σ = 1 ∨ σ = -1) → ∃ z ∈ U ∩ B, (φ z).2.1 = 0 ∧ (φ z).2.2 = σ * a := by
    intro σ hσ
    have hmem : ((0 : ℝ), (0 : ℝ), σ * a) ∈ Metric.ball (0 : ℝ × ℝ × ℝ) r := by
      rw [mem_ball_zero_iff, Prod.norm_def, Prod.norm_def]
      simp only [norm_zero, Real.norm_eq_abs]
      have : |σ * a| < r := by
        rcases hσ with rfl | rfl <;> simp [abs_of_pos ha] <;>
          linarith [min_le_left r ρ]
      exact max_lt hr (max_lt hr this)
    obtain ⟨z, hz, hzφ⟩ := hball hmem
    exact ⟨z, hz, by rw [hzφ], by rw [hzφ]⟩
  have hkey : ∀ z ∈ U ∩ B, (φ z).2.1 = 0 → z ∉ P → False := by
    intro z hz hv hzP
    have hzΘ : z ∈ frontier Tc := ((hloc z hz.1).2).mpr hv
    have hzX : z ∈ X := (hBsub hz.2).resolve_left hzP
    have hzint : z ∈ interior X := by
      refine interior_maximal (fun u hu => ?_) (hBo.inter hPc.isOpen_compl) ⟨hz.2, hzP⟩
      exact (hBsub hu.1).resolve_left hu.2
    exact Set.disjoint_left.mp hΘX (hΘ ▸ hzΘ) hzint
  rcases hside with h | h
  · obtain ⟨z, hz, hv, hw⟩ := hpt (-1) (Or.inr rfl)
    refine hkey z hz hv fun hzP => ?_
    have := (h z hz.1).mp hzP
    rw [hw] at this
    linarith
  · obtain ⟨z, hz, hv, hw⟩ := hpt 1 (Or.inl rfl)
    refine hkey z hz hv fun hzP => ?_
    have := (h z hz.1).mp hzP
    rw [hw] at this
    linarith

end Chart

section Outside

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
  {U W : Set M₁} {h : M₁ → M₂} {η ψ : M₁ → ℝ} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁} {H : Finset Ea → Set M₂}
  {cr : Section34VertexIndex 𝒦 𝒦' → Finset Ea} {f₁ : M₁ → M₂}

omit [FiniteDimensional ℝ Ea] in
theorem finite_setOf_carrier_inter_nonempty (hctrl : Section34CarrierControl U 𝒦 h η H)
    {t : Finset Ea} (ht : t ∈ 𝒦.complex.faces) :
    {t' | t' ∈ 𝒦.complex.faces ∧ (H t' ∩ H t).Nonempty}.Finite := by
  obtain ⟨-, hHU, hlf, -, hcell, -⟩ := hctrl
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
  refine (hbfin.biUnion fun y hy => hOfin y (hbsub hy)).subset ?_
  rintro t' ⟨ht', z, hzt', hzt⟩
  obtain ⟨y, hyb, hzy⟩ := mem_iUnion₂.mp (hbcover hzt)
  exact mem_iUnion₂.mpr ⟨y, hyb, ht', z, hzt', hzy⟩

omit [FiniteDimensional ℝ Ea] in
theorem finite_setOf_faceBall_inter_nonempty (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hctrl : Section34CarrierControl U 𝒦 h η H) {tgtV : Section34VertexIndex 𝒦 𝒦' → Set M₂}
    {fbl : Section34SimplexIndex 𝒦 3 → Set M₂} (hext : Section34Exterior 𝒦 𝒦' h H tgtV fbl)
    {t : Finset Ea} (ht : t ∈ 𝒦.complex.faces) :
    {s' : Section34SimplexIndex 𝒦 3 | (fbl s' ∩ H t).Nonempty}.Finite := by
  classical
  obtain ⟨hext1, -, -⟩ := hext
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hcof⟩ := hcut
  have hfin := finite_setOf_carrier_inter_nonempty hctrl ht
  have hsub : ∀ s' : Section34SimplexIndex 𝒦 3, (fbl s' ∩ H t).Nonempty →
      ∃ t' ∈ {t' | t' ∈ 𝒦.complex.faces ∧ (H t' ∩ H t).Nonempty}, s'.1 ⊆ t' := by
    intro s' hs'
    obtain ⟨t', hst'⟩ := hcof s'
    have hfb : fbl s' ⊆ interior (H t'.1) := by
      refine Subset.trans ?_ (hext1 t')
      unfold section34TetraObstacle
      exact subset_union_of_subset_right
        (subset_iUnion₂ (s := fun s'' (_ : Section34Incident s''.1 t'.1) => fbl s'') s' hst') _
    obtain ⟨z, hz, hzt⟩ := hs'
    refine ⟨t'.1, ⟨t'.2.1, z, interior_subset (hfb hz), hzt⟩, fun v hv => ?_⟩
    have hvs : ({v} : Finset Ea) ∈ 𝒦.complex.faces :=
      𝒦.complex.down_closed s'.2.1 (Finset.singleton_subset_iff.mpr hv)
        (Finset.singleton_nonempty v)
    exact mem_of_mem_convexHull_of_singleton_mem 𝒦.complex hvs t'.2.1
      (hst' (Finset.mem_coe.mpr hv))
  have hfin2 : (⋃ t' ∈ {t' | t' ∈ 𝒦.complex.faces ∧ (H t' ∩ H t).Nonempty},
      {s' : Section34SimplexIndex 𝒦 3 | s'.1 ⊆ t'}).Finite :=
    hfin.biUnion fun t' _ => Set.Finite.of_finite_image
      ((t'.powerset.finite_toSet).subset fun x ⟨y, hy, hxy⟩ => hxy ▸ Finset.mem_coe.mpr
        (Finset.mem_powerset.mpr hy)) Subtype.val_injective.injOn
  refine hfin2.subset fun s' hs' => ?_
  obtain ⟨t', ht', hst'⟩ := hsub s' hs'
  exact mem_iUnion₂.mpr ⟨t', ht', hst'⟩

omit [FiniteDimensional ℝ Ea] in
theorem subset_interior_carrier_of_section34Pocket (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hctrl : Section34CarrierControl U 𝒦 h η H)
    (hgraph : Section34GraphFrame U W h ψ H 𝒦 𝒦' src cr f₁)
    {fbl : Section34SimplexIndex 𝒦 3 → Set M₂}
    (hext : Section34Exterior 𝒦 𝒦' h H (section34VertexBallImage src f₁) fbl)
    {s : Section34SimplexIndex 𝒦 3} {t₀ : Section34SimplexIndex 𝒦 4}
    (hst₀ : Section34Incident s.1 t₀.1) {Pk : Set M₂} (hPkc : IsPreconnected Pk)
    (hPk₀ : Pk ⊆ interior (H t₀.1))
    (hPkfr : ∀ t : Section34SimplexIndex 𝒦 4, Section34Incident s.1 t.1 →
      frontier Pk ⊆ section34TetraObstacle (section34VertexBallImage src f₁) fbl t)
    (hPkV : ∀ u : Section34VertexIndex 𝒦 𝒦', ¬ Section34Incident u.1 s.1 →
      Disjoint Pk (section34VertexBallImage src f₁ u))
    (hPkne : ∀ t : Section34SimplexIndex 𝒦 4, Section34Incident s.1 t.1 →
      (Pk ∩ H t.1).Nonempty) :
    ∀ t : Section34SimplexIndex 𝒦 4, Section34Incident s.1 t.1 → Pk ⊆ interior (H t.1) := by
  classical
  obtain ⟨hext1, -, hext3⟩ := hext
  obtain ⟨-, hsubdiv, hmap, -⟩ := hcut
  obtain ⟨-, -, -, -, -, hmark, -⟩ := hgraph
  obtain ⟨hsupp, -, -, -, hHcell, -⟩ := hctrl
  intro t hst
  by_cases ht : t = t₀
  · rw [ht]
    exact hPk₀
  by_cases hmeet : (frontier (H t.1) ∩ Pk).Nonempty
  · exfalso
    have hfrH : IsConnected (frontier (H t.1)) := by
      obtain ⟨P0, r0, u0, hr0, hu0, -, hB0⟩ := hHcell t.1 t.2.1
      rw [hB0]
      exact ((isConnected_stdSimplexBoundary 1).image r0
        (hr0.isPiecewiseAffineOn.continuousOn.mono fun x hx => hx.1)).image u0
        (hu0.continuousOn.mono (by
          rintro _ ⟨x, hx, rfl⟩
          exact hr0.bijOn.mapsTo hx.1))
    have hdisj : Disjoint (frontier (H t.1)) (frontier Pk) :=
      Set.disjoint_left.mpr fun y hy hyP => hy.2 (hext1 t (hPkfr t hst hyP))
    have hsubfr : frontier (H t.1) ⊆ Pk :=
      IsPreconnected.subset_of_disjoint_frontier hfrH.isPreconnected hmeet hdisj
    have hsub : ∀ t' : Section34SimplexIndex 𝒦 4, Section34Incident s.1 t'.1 → s.1 ⊆ t'.1 :=
      fun t' hst' v hv => by
        have hvs : ({v} : Finset Ea) ∈ 𝒦.complex.faces :=
          𝒦.complex.down_closed s.2.1 (Finset.singleton_subset_iff.mpr hv)
            (Finset.singleton_nonempty v)
        exact mem_of_mem_convexHull_of_singleton_mem 𝒦.complex hvs t'.2.1
          (hst' (Finset.mem_coe.mpr hv))
    obtain ⟨d, hdt₀, hds⟩ : ∃ d ∈ t₀.1, d ∉ s.1 := by
      by_contra hcon
      push Not at hcon
      have hle := Finset.card_le_card (show t₀.1 ⊆ s.1 from hcon)
      rw [t₀.2.2, s.2.2] at hle
      omega
    have hins : ∀ t' : Section34SimplexIndex 𝒦 4, s.1 ⊆ t'.1 → d ∈ t'.1 →
        t'.1 = insert d s.1 := by
      intro t' hst' hdt'
      refine (Finset.eq_of_subset_of_card_le (Finset.insert_subset hdt' hst') ?_).symm
      rw [Finset.card_insert_of_notMem hds, t'.2.2, s.2.2]
    have hdt : d ∉ t.1 := fun hdt => ht (Subtype.ext ((hins t (hsub t hst) hdt).trans
      (hins t₀ (hsub t₀ hst₀) hdt₀).symm))
    have hdK : ({d} : Finset Ea) ∈ 𝒦.complex.faces :=
      𝒦.complex.down_closed t₀.2.1 (Finset.singleton_subset_iff.mpr hdt₀)
        (Finset.singleton_nonempty d)
    have hbody : simplexBody 𝒦' {d} ⊆ graphSkeletonSpace 𝒦 := by
      refine Subset.trans ?_ (subset_iUnion₂ (s := fun t'' (_ : t'' ∈ {t'' : Finset Ea |
        t'' ∈ 𝒦.complex.faces ∧ t''.card ≤ 2}) => simplexBody 𝒦 t'') {d}
        ⟨hdK, by simp⟩)
      simp only [simplexBody, hmap]
      exact Subset.rfl
    let ud : Section34VertexIndex 𝒦 𝒦' :=
      ⟨{d}, hsubdiv.singleton_mem hdK, Finset.card_singleton d, hbody⟩
    have hnotinc : ∀ t' : Finset Ea, t' ∈ 𝒦.complex.faces → d ∉ t' →
        ¬ Section34Incident ud.1 t' := by
      intro t' ht' hdt' hinc
      exact hdt' (mem_of_mem_convexHull_of_singleton_mem 𝒦.complex hdK ht'
        (hinc (by simp [ud])))
    have hyd : h (𝒦.map d) ∈ h '' simplexBody 𝒦' ud.1 :=
      ⟨𝒦.map d, ⟨d, subset_convexHull ℝ _ (by simp [ud]), by rw [hmap]⟩, rfl⟩
    obtain ⟨a, has⟩ : s.1.Nonempty := Finset.card_pos.mp (by rw [s.2.2]; norm_num)
    have hydH : h (𝒦.map d) ∈ interior (H t.1) := by
      refine hsupp t.1 t.2.1 ⟨𝒦.map d, mem_iUnion₂.mpr ⟨a, Finset.mem_coe.mpr (hsub t hst has),
        mem_iUnion₂.mpr ⟨t₀.1, ⟨t₀.2.1, hsub t₀ hst₀ has⟩, d, subset_convexHull ℝ _
          (Finset.mem_coe.mpr hdt₀), rfl⟩⟩, rfl⟩
    obtain ⟨hyo, z, hzC, hzfr⟩ := hext3 t ud (hnotinc t.1 t.2.1 hdt) _ hyd (interior_subset hydH)
    have hCPk : connectedComponentIn
        (H t.1 \ section34TetraObstacle (section34VertexBallImage src f₁) fbl t)
        (h (𝒦.map d)) ⊆ Pk :=
      IsPreconnected.subset_of_disjoint_frontier isPreconnected_connectedComponentIn
        ⟨z, hzC, hsubfr hzfr⟩ (Set.disjoint_left.mpr fun y hy hyP =>
          (connectedComponentIn_subset _ _ hy).2 (hPkfr t hst hyP))
    have hydPk := hCPk (mem_connectedComponentIn ⟨interior_subset hydH, hyo⟩)
    exact Set.disjoint_left.mp (hPkV ud (hnotinc s.1 s.2.1 hds)) hydPk
      (interior_subset (hmark ud hyd))
  · have hdisj : Disjoint Pk (frontier (H t.1)) :=
      Set.disjoint_left.mpr fun y hyP hyF => hmeet ⟨y, hyF, hyP⟩
    have hsubP := IsPreconnected.subset_of_disjoint_frontier hPkc (hPkne t hst) hdisj
    intro y hy
    exact (mem_interior_iff_notMem_frontier (hsubP hy)).mpr fun hyF => hmeet ⟨y, hyF, hy⟩

theorem exists_section34Compression_of_disjoint_of_cleanPocket
    (hh : Topology.IsEmbedding (U.domRestrict h))
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hctrl : Section34CarrierControl U 𝒦 h η H)
    (hgraph : Section34GraphFrame U W h ψ H 𝒦 𝒦' src cr f₁)
    {fbl fblBd : Section34SimplexIndex 𝒦 3 → Set M₂}
    (hinv : Section34FaceBallInvariants 𝒦 𝒦' h H (section34VertexBallImage src f₁)
      (section34SplitDiskImage srcBd f₁) fbl fblBd)
    (s : Section34SimplexIndex 𝒦 3) {w : Section34VertexIndex 𝒦 𝒦'} {Dj Jd : Set M₂}
    (hDcell : IsPLCellOn 2 Dj Jd) (hDw : Dj ⊆ section34VertexBallImage srcBd f₁ w)
    (hDJ : Dj ∩ fblBd s = Jd)
    (hDE : ∀ e : Section34EdgeIndex 𝒦 𝒦', Disjoint Dj (section34SplitDiskImage src f₁ e))
    (hDo : ∀ s' : Section34SimplexIndex 𝒦 3, s' ≠ s → Disjoint (Dj \ Jd) (fbl s'))
    (hout : Disjoint (Dj \ Jd) (fbl s)) (t₀ : Section34SimplexIndex 𝒦 4)
    (hst₀ : Section34Incident s.1 t₀.1) {c : OpenPartialHomeomorph M₂ E3}
    (hc : c ∈ (plGroupoid 3).maximalAtlas M₂) (hHc : H t₀.1 ⊆ c.source)
    (hfsc : fbl s ⊆ c.source)
    (hTc : section34FaceTorus (section34VertexBallImage src f₁) s ⊆ c.source)
    (hTcomp : IsCompact (section34FaceTorus (section34VertexBallImage src f₁) s)) {O₀ : Set M₂}
    (hO₀def : O₀ = interior (H t₀.1) \ ⋃ w' ∈ {w' : Section34VertexIndex 𝒦 𝒦' |
      (section34VertexBallImage src f₁ w' ∩ H t₀.1).Nonempty ∧ ¬ Section34Incident w'.1 s.1},
      section34VertexBallImage src f₁ w') (hO₀ : IsOpen O₀) (hfO₀ : fbl s ⊆ O₀)
    (hSgO₀ : frontier (⋃ w, section34VertexBallImage src f₁ w) ∩ O₀ =
      frontier (section34FaceTorus (section34VertexBallImage src f₁) s) ∩ O₀)
    (hclean : ∀ Y : Set M₂, IsPLCellOn 3 Y (frontier Y) → frontier Y ⊆ Dj ∪ fblBd s →
      Disjoint (interior (fbl s)) Y → Y ⊆ interior (H t₀.1) →
      Disjoint (interior Y) (frontier (section34FaceTorus (section34VertexBallImage src f₁) s)) ∧
      ∀ u : Section34VertexIndex 𝒦 𝒦', ¬ Section34Incident u.1 s.1 →
        Disjoint Y (section34VertexBallImage src f₁ u)) :
    ∃ fbl' fblBd' : Section34SimplexIndex 𝒦 3 → Set M₂,
      Section34FaceBallInvariants 𝒦 𝒦' h H (section34VertexBallImage src f₁)
        (section34SplitDiskImage srcBd f₁) fbl' fblBd' ∧
      (∀ s', s' ≠ s → fbl' s' = fbl s' ∧ fblBd' s' = fblBd s') ∧
      section34TraceCount (section34VertexBallImage src f₁) fblBd' s + 1 ≤
        section34TraceCount (section34VertexBallImage src f₁) fblBd s ∧
      section34CrossingCount (section34SplitDiskImage srcBd f₁) fblBd' s ≤
        section34CrossingCount (section34SplitDiskImage srcBd f₁) fblBd s := by
  classical
  obtain ⟨hfcell, hfrim, hfV, hf4, hf5, -, hf7, -, -, hext⟩ := id hinv
  obtain ⟨-, hsubdiv, hmap, hcell, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    hends, -, -⟩ := id hcut
  obtain ⟨-, -, hf₁, -, -, hmark, -, -, hrimT, -, -, -, -, -⟩ := id hgraph
  obtain ⟨hsupp, -, -, -, hHcell, -⟩ := id hctrl
  obtain ⟨hext1, -, hext3⟩ := id hext
  set T := section34FaceTorus (section34VertexBallImage src f₁) s with hTdef
  set Sg := frontier (⋃ w', section34VertexBallImage src f₁ w') with hSgdef
  have hNV : ∀ v : Section34VertexIndex 𝒦 𝒦',
      src (.vertexBall v) ⊆ section34CutNeighborhood src :=
    fun v => subset_iUnion (fun v => src (Section34Label.vertexBall v)) v
  have hVT : ∀ w' : Section34VertexIndex 𝒦 𝒦', Section34Incident w'.1 s.1 →
      section34VertexBallImage src f₁ w' ⊆ T := fun w' hw z hz =>
    mem_iUnion₂.mpr ⟨⟨(s, w'), hw⟩, rfl, hz⟩
  have hTinc : ∀ z ∈ T, ∃ w' : Section34VertexIndex 𝒦 𝒦', Section34Incident w'.1 s.1 ∧
      z ∈ section34VertexBallImage src f₁ w' := by
    intro z hz
    obtain ⟨a, ha, hza⟩ := mem_iUnion₂.mp hz
    refine ⟨a.1.2, ?_, hza⟩
    rw [← ha]
    exact a.2
  have hVc : ∀ w' : Section34VertexIndex 𝒦 𝒦', Section34Incident w'.1 s.1 →
      section34VertexBallImage src f₁ w' ⊆ c.source := fun w' hw => (hVT w' hw).trans hTc
  have hfbs : fblBd s ⊆ fbl s := (hfcell s).boundary_subset
  have hVcell : ∀ w' : Section34VertexIndex 𝒦 𝒦',
      IsPLCellOn 3 (section34VertexBallImage src f₁ w') (section34VertexBallImage srcBd f₁ w') :=
    fun w' => (hcell (.vertexBall w')).image
      (hf₁.mono_of_isPLCellOn (hcell (.vertexBall w')) (hNV w'))
  have hDN : ∀ e : Section34EdgeIndex 𝒦 𝒦',
      src (.splitDisk e) ⊆ section34CutNeighborhood src := by
    intro e
    obtain ⟨w', _, -, -, he⟩ := hends e
    rw [he]
    exact inter_subset_left.trans (hNV w')
  have hJdb : Jd ⊆ fblBd s := by
    rw [← hDJ]
    exact inter_subset_right
  have hJdD : Jd ⊆ Dj := by
    rw [← hDJ]
    exact inter_subset_left
  obtain ⟨yJ, hyJ⟩ : Jd.Nonempty := by
    obtain ⟨P0, r0, u0, -, -, -, hB⟩ := id hDcell
    rw [hB]
    exact ⟨u0 (r0 (Pi.single 0 1)), r0 (Pi.single 0 1),
      ⟨Pi.single 0 1, ⟨Convexity.StdSimplex.single_mem_coordinateSet ℝ 0, 1,
        Pi.single_eq_of_ne (show (1 : Fin 3) ≠ 0 by decide) (1 : ℝ)⟩, rfl⟩, rfl⟩
  have hDwV : Dj ⊆ section34VertexBallImage src f₁ w := fun z hz =>
    image_mono (hcell (.vertexBall w)).boundary_subset (hDw hz)
  have hwinc : Section34Incident w.1 s.1 := by
    by_contra hn
    have hmem : yJ ∈ fbl s ∩ section34VertexBallImage src f₁ w :=
      ⟨hfbs (hJdb hyJ), hDwV (hJdD hyJ)⟩
    rw [hfV s w hn] at hmem
    exact hmem
  have hDjV : ∀ w' : Section34VertexIndex 𝒦 𝒦', w' ≠ w →
      Disjoint Dj (section34VertexBallImage src f₁ w') := by
    intro w' hw'
    refine Set.disjoint_left.mpr fun z hz hz' => ?_
    obtain ⟨a, ha, haz⟩ := image_mono (hcell (.vertexBall w)).boundary_subset (hDw hz)
    obtain ⟨b, hb, hbz⟩ := hz'
    have hEq : b = a := hf₁.injOn (hNV w' hb) (hNV w ha) (hbz.trans haz.symm)
    rw [hEq] at hb
    obtain ⟨e, he⟩ := exists_splitDisk_src_eq_inter_vertexBall hcut hw'.symm ⟨a, ha, hb⟩
    refine Set.disjoint_left.mp (hDE e) hz ⟨a, ?_, haz⟩
    rw [he]
    exact ⟨ha, hb⟩
  have hIfin := finite_setOf_section34Incident_graphIndex hsubdiv (graphSkeletonSpace 𝒦) 1 s.2.1
  have hEfin := finite_setOf_section34Incident_graphIndex hsubdiv (graphSkeletonSpace 𝒦) 2 s.2.1
  have hcT : IsCompact (c '' T) := hTcomp.image_of_continuousOn (c.continuousOn.mono hTc)
  have hTcl : IsClosed (c '' T) := hcT.isClosed
  set Θ := frontier (c '' T) with hΘdef
  have hΘeq : c '' frontier T = Θ := c.image_frontier_of_isCompact hTcomp hTc
  have hfrTc : frontier T ⊆ c.source := hTcomp.isClosed.frontier_subset.trans hTc
  have hΘt : Θ ⊆ c.target := by
    rw [← hΘeq]
    rintro _ ⟨y, hy, rfl⟩
    exact c.map_source (hfrTc hy)
  have hΘtor : IsPLTorus Θ := by
    rw [← hΘeq]
    exact isPLTorus_image_frontier_section34FaceTorus hcut (hgraph.2.2.1) s hc hTc
  have hmemT : ∀ y ∈ c.source, (y ∈ frontier T ↔ c y ∈ Θ) := by
    intro y hy
    rw [← hΘeq]
    constructor
    · exact fun h1 => mem_image_of_mem c h1
    · rintro ⟨y', hy', hyy⟩
      rwa [← c.injOn (hfrTc hy') hy hyy]
  obtain ⟨hPb, hPfr⟩ := (hfcell s).isPLBall_image_chart hc hfsc
  have hmemP : ∀ y ∈ c.source, (y ∈ fblBd s ↔ c y ∈ frontier (c '' fbl s)) := by
    intro y hy
    rw [← hPfr]
    constructor
    · exact fun h1 => mem_image_of_mem c h1
    · rintro ⟨y', hy', hyy⟩
      rwa [← c.injOn (hfsc (hfbs hy')) hy hyy]
  have hmemSg : ∀ y ∈ fbl s, (y ∈ Sg ↔ c y ∈ Θ) := by
    intro y hy
    have hyO := hfO₀ hy
    rw [← hmemT y (hfsc hy)]
    constructor
    · intro h1
      have h2 : y ∈ Sg ∩ O₀ := ⟨h1, hyO⟩
      rw [hSgO₀] at h2
      exact h2.1
    · intro h1
      have h2 : y ∈ frontier T ∩ O₀ := ⟨h1, hyO⟩
      rw [← hSgO₀] at h2
      exact h2.1
  have hcrossΘ : ∀ y ∈ fblBd s ∩ frontier T,
      HasPLCrossingAt (frontier (c '' fbl s)) Θ (c y) := by
    rintro y ⟨hyb, hyT⟩
    have hyO₀ : y ∈ O₀ := hfO₀ (hfbs hyb)
    have hy : y ∈ c.source := hfsc (hfbs hyb)
    have hySg : y ∈ Sg := (hmemSg y (hfbs hyb)).mpr ((hmemT y hy).mp hyT)
    obtain ⟨c', hc', hyc', hcr⟩ := hf5 s y ⟨hyb, hySg⟩
    have hcr' := hcr.image_chart_of_mem_maximalAtlas hc hc' hy hyc'
    refine hcr'.congr ?_ ?_
    · rw [inter_eq_left.mpr (hfbs.trans hfsc), hPfr]
      exact Filter.Eventually.of_forall fun _ => Iff.rfl
    · filter_upwards [eventually_mem_image_inter_source_iff hO₀ hSgO₀ hyO₀ hy] with z hz
      rw [hz, inter_eq_left.mpr hfrTc, hΘeq]
  have hDjc : Dj ⊆ c.source := hDwV.trans (hVc w hwinc)
  obtain ⟨q, hq, hqJ⟩ := hDcell.exists_isPLHomeomorphOn_image_chart hc hDjc
  have hDjfbl : Dj ∩ fbl s = Jd := by
    apply Subset.antisymm
    · rintro z ⟨hzD, hzf⟩
      by_contra hzJ
      exact Set.disjoint_left.mp hout ⟨hzD, hzJ⟩ hzf
    · exact fun z hz => ⟨hJdD hz, hfbs (hJdb hz)⟩
  have hDP : c '' Dj ∩ c '' fbl s = q '' stdSimplexBoundary 2 := by
    rw [← c.injOn.image_inter hDjc hfsc, hDjfbl, hqJ]
  obtain ⟨hVwb, hVwfr⟩ := (hVcell w).isPLBall_image_chart hc (hVc w hwinc)
  have hDV : c '' Dj ⊆ frontier (c '' section34VertexBallImage src f₁ w) := by
    rw [← hVwfr]
    exact image_mono hDw
  obtain ⟨Oo, hOo, hDO, hΘO⟩ : ∃ Oo : Set (EuclideanSpace ℝ (Fin 3)), IsOpen Oo ∧
      c '' Dj ⊆ Oo ∧ Oo ∩ Θ = Oo ∩ frontier (c '' section34VertexBallImage src f₁ w) := by
    have hcl : IsClosed (⋃ w' ∈ {w' : Section34VertexIndex 𝒦 𝒦' |
        Section34Incident w'.1 s.1 ∧ w' ≠ w}, c '' section34VertexBallImage src f₁ w') :=
      (hIfin.subset fun w' hw' => hw'.1).isClosed_biUnion fun w' hw' =>
        ((hVcell w').isCompact.image_of_continuousOn
          (c.continuousOn.mono (hVc w' hw'.1))).isClosed
    have hcTO : c '' T ∩ (⋃ w' ∈ {w' : Section34VertexIndex 𝒦 𝒦' |
        Section34Incident w'.1 s.1 ∧ w' ≠ w}, c '' section34VertexBallImage src f₁ w')ᶜ =
        c '' section34VertexBallImage src f₁ w ∩ (⋃ w' ∈ {w' : Section34VertexIndex 𝒦 𝒦' |
          Section34Incident w'.1 s.1 ∧ w' ≠ w}, c '' section34VertexBallImage src f₁ w')ᶜ := by
      apply Subset.antisymm
      · rintro _ ⟨⟨z, hz, rfl⟩, hzO⟩
        obtain ⟨w', hw', hzw'⟩ := hTinc z hz
        by_cases hww : w' = w
        · subst hww
          exact ⟨⟨z, hzw', rfl⟩, hzO⟩
        · exact (hzO (mem_iUnion₂.mpr ⟨w', ⟨hw', hww⟩, ⟨z, hzw', rfl⟩⟩)).elim
      · exact inter_subset_inter_left _ (image_mono (hVT w hwinc))
    refine ⟨_, hcl.isOpen_compl, ?_, ?_⟩
    · rintro _ ⟨z, hz, rfl⟩ hzU
      obtain ⟨w', ⟨hw', hww⟩, ⟨z', hz', hzz⟩⟩ := mem_iUnion₂.mp hzU
      have hzz' := c.injOn (hVc w' hw' hz') (hDjc hz) hzz
      rw [hzz'] at hz'
      exact Set.disjoint_left.mp (hDjV w' hww) hz hz'
    · have h1 := frontier_inter_open_inter (s := c '' T) hcl.isOpen_compl
      have h2 := frontier_inter_open_inter (s := c '' section34VertexBallImage src f₁ w)
        hcl.isOpen_compl
      rw [hcTO] at h1
      change _ ∩ frontier (c '' T) = _
      rw [inter_comm _ (frontier (c '' T)), inter_comm _ (frontier _), ← h1, h2]
  have hDjT : Dj ⊆ frontier T := by
    intro z hz
    have hzc : c z ∈ Oo ∩ frontier (c '' section34VertexBallImage src f₁ w) :=
      ⟨hDO ⟨z, hz, rfl⟩, hDV ⟨z, hz, rfl⟩⟩
    rw [← hΘO] at hzc
    exact (hmemT z (hDjc hz)).mpr hzc.2
  have hJdSg : Jd ⊆ Sg := fun z hz =>
    (hmemSg z (hfbs (hJdb hz))).mpr ((hmemT z (hDjc (hJdD hz))).mp (hDjT (hJdD hz)))
  have hcrossΘJ : ∀ x ∈ q '' stdSimplexBoundary 2,
      HasPLCrossingAt (frontier (c '' fbl s)) Θ x := by
    intro x hx
    rw [← hqJ] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact hcrossΘ y ⟨hJdb hy, hDjT (hJdD hy)⟩
  have hcrossVP : ∀ x ∈ q '' stdSimplexBoundary 2,
      HasPLCrossingAt (frontier (c '' section34VertexBallImage src f₁ w))
        (frontier (c '' fbl s)) x := by
    intro x hx
    refine (hcrossΘJ x hx).symm.congr ?_ (Filter.Eventually.of_forall fun _ => Iff.rfl)
    have hxO : x ∈ Oo := by
      rw [← hqJ] at hx
      exact hDO (image_mono hJdD hx)
    filter_upwards [hOo.mem_nhds hxO] with z hz
    constructor
    · intro h1
      have h2 : z ∈ Oo ∩ Θ := ⟨hz, h1⟩
      rw [hΘO] at h2
      exact h2.2
    · intro h1
      have h2 : z ∈ Oo ∩ frontier (c '' section34VertexBallImage src f₁ w) := ⟨hz, h1⟩
      rw [← hΘO] at h2
      exact h2.2
  have hEsc : ∀ e : Section34EdgeIndex 𝒦 𝒦', Section34Incident e.1 s.1 →
      section34SplitDiskImage src f₁ e ⊆ c.source := by
    intro e he
    obtain ⟨u, u', -, hew, hDu⟩ := hends e
    have hue : ((u.1 : Finset Ea) : Set Ea) ⊆ (e.1 : Set Ea) := by
      rw [hew]
      exact subset_union_left
    change f₁ '' src (.splitDisk e) ⊆ c.source
    rw [hDu]
    exact (image_mono inter_subset_left).trans (hVc u (hue.trans he))
  have hEcc : IsClosed (⋃ e ∈ {e : Section34EdgeIndex 𝒦 𝒦' | Section34Incident e.1 s.1},
      c '' section34SplitDiskImage src f₁ e) := hEfin.isClosed_biUnion fun e he =>
    (((hcell (.splitDisk e)).image (hf₁.mono_of_isPLCellOn (hcell (.splitDisk e))
      (hDN e))).isCompact.image_of_continuousOn (c.continuousOn.mono (hEsc e he))).isClosed
  have hDEc : Disjoint (⋃ e ∈ {e : Section34EdgeIndex 𝒦 𝒦' |
      Section34Incident e.1 s.1}, c '' section34SplitDiskImage src f₁ e) (c '' Dj) := by
    refine Set.disjoint_right.mpr fun x hx hxE => ?_
    obtain ⟨e, he, z, hz, hzx⟩ := mem_iUnion₂.mp hxE
    obtain ⟨y, hy, rfl⟩ := hx
    have hzy := c.injOn (hEsc e he hz) (hDjc hy) hzx
    rw [hzy] at hz
    exact Set.disjoint_left.mp (hDE e) hy hz
  have hsTs : ∀ t : Section34SimplexIndex 𝒦 4, Section34Incident s.1 t.1 →
      fbl s ⊆ interior (H t.1) := by
    intro t hst
    refine Subset.trans ?_ (hext1 t)
    unfold section34TetraObstacle
    exact subset_union_of_subset_right
      (subset_iUnion₂ (s := fun s' (_ : Section34Incident s'.1 t.1) => fbl s') s hst) _
  have hTsfin : {t : Section34SimplexIndex 𝒦 4 | Section34Incident s.1 t.1}.Finite := by
    obtain ⟨z, hz⟩ := (hfcell s).nonempty
    have himg : (Subtype.val '' {t : Section34SimplexIndex 𝒦 4 |
        Section34Incident s.1 t.1}).Finite := by
      refine (finite_setOf_carrier_inter_nonempty hctrl t₀.2.1).subset ?_
      rintro _ ⟨t, ht, rfl⟩
      exact ⟨t.2.1, z, interior_subset (hsTs t ht hz), interior_subset (hsTs t₀ hst₀ hz)⟩
    exact himg.of_finite_image Subtype.val_injective.injOn
  have hwt : ∀ t : Section34SimplexIndex 𝒦 4, Section34Incident s.1 t.1 →
      Section34Incident w.1 t.1 :=
    fun t hst => hwinc.trans (convexHull_min hst (convex_convexHull ℝ _))
  have hVwt : ∀ t : Section34SimplexIndex 𝒦 4, Section34Incident s.1 t.1 →
      section34VertexBallImage src f₁ w ⊆ interior (H t.1) := fun t hst =>
    image_vertexBall_subset_interior_of_incident hh hcut hctrl hgraph w t.2.1 (hwt t hst)
  set Qv := ⋃ u ∈ {u : Section34VertexIndex 𝒦 𝒦' | u ≠ w ∧
    (section34VertexBallImage src f₁ u ∩ H t₀.1).Nonempty}, section34VertexBallImage src f₁ u
    with hQvdef
  set Qf := ⋃ s' ∈ {s' : Section34SimplexIndex 𝒦 3 | s' ≠ s ∧ (fbl s' ∩ H t₀.1).Nonempty},
    fbl s' with hQfdef
  have hQvc : IsClosed Qv :=
    ((finite_setOf_vertexBallImage_inter_nonempty hctrl hgraph t₀.2.1).subset
      fun u hu => hu.2).isClosed_biUnion fun u _ => (hVcell u).isCompact.isClosed
  have hQfc : IsClosed Qf :=
    ((finite_setOf_faceBall_inter_nonempty hcut hctrl hext t₀.2.1).subset
      fun s' hs' => hs'.2).isClosed_biUnion fun s' _ => (hfcell s').isCompact.isClosed
  set OM := (⋂ t ∈ {t : Section34SimplexIndex 𝒦 4 | Section34Incident s.1 t.1},
    interior (H t.1)) ∩ O₀ ∩ (Qv ∪ Qf)ᶜ with hOMdef
  have hOMo : IsOpen OM :=
    ((hTsfin.isOpen_biInter fun t _ => isOpen_interior).inter hO₀).inter
      (hQvc.union hQfc).isOpen_compl
  have hDjOM : Dj ⊆ OM := by
    intro z hz
    refine ⟨⟨mem_iInter₂.mpr fun t ht => hVwt t ht (hDwV hz), ?_⟩, ?_⟩
    · rw [hO₀def]
      refine ⟨hVwt t₀ hst₀ (hDwV hz), fun hzQ => ?_⟩
      obtain ⟨u, ⟨-, hu⟩, hzu⟩ := mem_iUnion₂.mp hzQ
      have huw : u ≠ w := fun h => hu (h ▸ hwinc)
      exact Set.disjoint_left.mp (hDjV u huw) hz hzu
    · rintro (hzQ | hzQ)
      · obtain ⟨u, ⟨huw, -⟩, hzu⟩ := mem_iUnion₂.mp hzQ
        exact Set.disjoint_left.mp (hDjV u huw) hz hzu
      · obtain ⟨s', ⟨hs', -⟩, hzs'⟩ := mem_iUnion₂.mp hzQ
        by_cases hzJ : z ∈ Jd
        · have hzN := hf4 s s' (Ne.symm hs') ⟨hfbs (hJdb hzJ), hzs'⟩
          exact (hJdSg hzJ).2 hzN
        · exact Set.disjoint_left.mp (hDo s' hs') ⟨hz, hzJ⟩ hzs'
  set O := c '' (OM ∩ c.source) ∩ Oo with hOdef
  have hOo' : IsOpen O :=
    (c.isOpen_image_of_subset_source (hOMo.inter c.open_source) inter_subset_right).inter hOo
  have hDO' : c '' Dj ⊆ O := fun x hx => by
    obtain ⟨z, hz, rfl⟩ := hx
    exact ⟨⟨z, ⟨hDjOM hz, hDjc hz⟩, rfl⟩, hDO ⟨z, hz, rfl⟩⟩
  have hOsymm : ∀ x ∈ O, x ∈ c.target ∧ c.symm x ∈ OM := by
    rintro _ ⟨⟨z, hz, rfl⟩, -⟩
    exact ⟨c.map_source hz.2, by rw [c.left_inv hz.2]; exact hz.1⟩
  obtain ⟨Wc, Xc, Ein, Eout, Bin, Bout, Ain, Aout, Lin, Lout, Tin, Tout, hW, hX, hXW, hPX, hWeq,
    hWf, hXf, hEu, hEi, hEinB, hEoutB, hBAin, hBAout, hBinJ, hBoutJ, hEinc, hEoutc, hAinc,
    hAoutc, hLinc, hLoutc, hBinc, hBoutc, hsubO, hAVF, hLVF, hLinP, hLoutP, hYs, hYsf, R, Lr, g,
    hRo, hRO,
    hLrO, hToutR, hclR, hgc, hgLr, hgR, hgT, hRP, hRVF, hRV, hRY, hclRY, R', Lr', g', hR'o,
    hR'O, hLr'O, hTinR', hclR', hg'c, hg'Lr, hg'R, hg'T, hR'P, hR'VF, hR'V, hR'Y, hToutY, -, -,
    -, -⟩ :=
    exists_compressionShell hPb hVwb hq hDV hDP hcrossVP hEcc hDEc hOo' hDO'
  have hAinO : Ain ⊆ O := fun x hx => hsubO (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hx)))))
  have hAoutO : Aout ⊆ O := fun x hx => hsubO (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hx)))))
  have hLinO : Lin ⊆ O := fun x hx => hsubO (Or.inl (Or.inl (Or.inl (Or.inr hx))))
  have hLoutO : Lout ⊆ O := fun x hx => hsubO (Or.inl (Or.inl (Or.inr hx)))
  have hTinO : Tin ⊆ O := fun x hx => hsubO (Or.inl (Or.inr hx))
  have hToutO : Tout ⊆ O := fun x hx => hsubO (Or.inr hx)
  have hOt : O ⊆ c.target := fun x hx => (hOsymm x hx).1
  have hOΘ : ∀ x ∈ O, (x ∈ Θ ↔ x ∈ frontier (c '' section34VertexBallImage src f₁ w)) := by
    intro x hx
    constructor
    · intro h1
      have h2 : x ∈ Oo ∩ Θ := ⟨hx.2, h1⟩
      rw [hΘO] at h2
      exact h2.2
    · intro h1
      have h2 : x ∈ Oo ∩ frontier (c '' section34VertexBallImage src f₁ w) := ⟨hx.2, h1⟩
      rw [← hΘO] at h2
      exact h2.2
  have hLΘ : ∀ x ∈ Lin ∪ Lout, x ∉ Θ := by
    intro x hx hxΘ
    have hxO : x ∈ O := hx.elim (fun h => hLinO h) (fun h => hLoutO h)
    exact Set.disjoint_left.mp hLVF hx (Or.inl ((hOΘ x hxO).mp hxΘ))
  have hAΘ : ∀ x ∈ Ain ∪ Aout, x ∈ Θ → x ∈ q '' stdSimplexBoundary 2 := by
    intro x hx hxΘ
    have hxO : x ∈ O := hx.elim (fun h => hAinO h) (fun h => hAoutO h)
    exact hAVF ⟨hx, Or.inl ((hOΘ x hxO).mp hxΘ)⟩
  have hPfrE : frontier (c '' fbl s) = Bin ∪ Ain ∪ (Bout ∪ Aout) := by
    rw [← hEu, hEinB, hEoutB]
  have hOMH : ∀ y ∈ OM, ∀ t : Section34SimplexIndex 𝒦 4, Section34Incident s.1 t.1 →
      y ∈ interior (H t.1) := fun y hy t ht => mem_iInter₂.mp hy.1.1 t ht
  have hOMV : ∀ y ∈ OM, ∀ u : Section34VertexIndex 𝒦 𝒦', u ≠ w →
      y ∉ section34VertexBallImage src f₁ u := by
    intro y hy u hu hyu
    have hyH := hOMH y hy t₀ hst₀
    exact hy.2 (Or.inl (mem_iUnion₂.mpr ⟨u, ⟨hu, y, hyu, interior_subset hyH⟩, hyu⟩))
  have hOMf : ∀ y ∈ OM, ∀ s' : Section34SimplexIndex 𝒦 3, s' ≠ s → y ∉ fbl s' := by
    intro y hy s' hs' hys'
    have hyH := hOMH y hy t₀ hst₀
    exact hy.2 (Or.inr (mem_iUnion₂.mpr ⟨s', ⟨hs', y, hys', interior_subset hyH⟩, hys'⟩))
  have hsplitV : ∀ e : Section34EdgeIndex 𝒦 𝒦', ∀ y ∈ section34SplitDiskImage srcBd f₁ e,
      ∃ u : Section34VertexIndex 𝒦 𝒦', u ≠ w ∧ y ∈ section34VertexBallImage src f₁ u := by
    intro e y hy
    obtain ⟨u, u', huu', -, hDu⟩ := hends e
    obtain ⟨a, ha, rfl⟩ := image_mono (hcell (.splitDisk e)).boundary_subset hy
    rw [hDu] at ha
    by_cases huw : u = w
    · exact ⟨u', fun h => huu' (huw.trans h.symm), a, ha.2, rfl⟩
    · exact ⟨u, huw, a, ha.1, rfl⟩
  have hOsplit : ∀ x ∈ O, ∀ e : Section34EdgeIndex 𝒦 𝒦',
      x ∉ c '' (section34SplitDiskImage srcBd f₁ e ∩ c.source) := by
    rintro x hxO e ⟨y, ⟨hye, hyc⟩, rfl⟩
    obtain ⟨u, hu, hyu⟩ := hsplitV e y hye
    have hyOM := (hOsymm _ hxO).2
    rw [c.left_inv hyc] at hyOM
    exact hOMV y hyOM u hu hyu
  have hJTr : q '' stdSimplexBoundary 2 ⊆ frontier (c '' fbl s) ∩ Θ := by
    intro x hx
    rw [← hqJ] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨(hmemP y (hDjc (hJdD hy))).mp (hJdb hy),
      (hmemT y (hDjc (hJdD hy))).mp (hDjT (hJdD hy))⟩
  have hcy₀ : c yJ ∈ q '' stdSimplexBoundary 2 := by
    rw [← hqJ]
    exact ⟨yJ, hyJ, rfl⟩
  have hZc : frontier (c '' fbl s) ∩ Θ = c '' (fblBd s ∩ frontier T) := by
    rw [c.injOn.image_inter (hfbs.trans hfsc) hfrTc, hPfr, hΘeq]
  have hcTreg : ∀ x ∈ Θ, x ∈ closure (interior (c '' T)) := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ : x ∈ c '' T := hTcl.frontier_subset hx
    obtain ⟨w', hw', hzw'⟩ := hTinc z hz
    obtain ⟨hb', -⟩ := (hVcell w').isPLBall_image_chart hc (hVc w' hw')
    have hcl := hb'.closure_interior_of_finrank (by simp)
    have hzin : c z ∈ closure (interior (c '' section34VertexBallImage src f₁ w')) := by
      rw [hcl]
      exact ⟨z, hzw', rfl⟩
    exact closure_mono (interior_mono (image_mono (hVT w' hw'))) hzin
  have hcrossPΘ : ∀ x ∈ frontier (c '' fbl s) ∩ Θ,
      HasPLCrossingAt (frontier (c '' fbl s)) Θ x := by
    intro x hx
    rw [hZc] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact hcrossΘ y hy
  obtain ⟨ι, hιfin, C, hC, hCd, hCeq⟩ := exists_iUnion_isPLSphere_one_of_forall_lineChart
    (hPb.isPolyhedron.frontier.inter hΘtor.1) hcrossPΘ fun x hx =>
      (hcrossPΘ x hx).exists_lineChart hx.1
        (hPb.isPLSphere_frontier.exists_isOpen_inter_homeomorph_of_two hx.1) hTcl (hcTreg x hx.2)
  have hZS : CarriesFirstHomologyOnto (c.symm '' (frontier (c '' fbl s) ∩ Θ)) T := by
    rw [hZc]
    convert hf7 s using 1
    exact c.symm_image_image_of_subset_source (inter_subset_right.trans hfrTc)
  have hΘS : c.symm '' Θ ⊆ T := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← hΘeq] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    rw [c.left_inv (hfrTc hz)]
    exact hTcomp.isClosed.frontier_subset hz
  have hJsph : IsPLSphere 1 (q '' stdSimplexBoundary 2) :=
    hq.isPLSphere_image_stdSimplexBoundary (n := 1)
  have hDΘ : c '' Dj ⊆ Θ := by
    rw [← hΘeq]
    exact image_mono hDjT
  have hJD : q '' stdSimplexBoundary 2 ⊆ c '' Dj :=
    (image_mono fun _ hx => hx.1).trans hq.image_eq.subset
  have hDcl : IsClosed (c '' Dj) := (IsPLBall.isPolyhedron ⟨q, hq⟩).isClosed
  have hDJne : (c '' Dj \ q '' stdSimplexBoundary 2).Nonempty :=
    closure_nonempty_iff.mp ⟨c yJ, mem_closure_sdiff_image_stdSimplexBoundary hq hcy₀⟩
  have hDo' : ∀ z ∈ c '' Dj \ q '' stdSimplexBoundary 2, ∃ O' : Set E3, IsOpen O' ∧ z ∈ O' ∧
      O' ∩ Θ ⊆ c '' Dj := by
    intro z hz
    have hS := hVwb.isPLSphere_frontier
    have hint := hS.inter_closure_sdiff_eq_image_stdSimplexBoundary hq hDV
    refine ⟨Oo ∩ (closure (frontier (c '' section34VertexBallImage src f₁ w) \ c '' Dj))ᶜ,
      hOo.inter isClosed_closure.isOpen_compl, ⟨hDO hz.1, fun hzc => hz.2 ?_⟩, ?_⟩
    · rw [← hint]
      exact ⟨hz.1, hzc⟩
    · rintro y ⟨⟨hyO, hycl⟩, hyΘ⟩
      have h2 : y ∈ Oo ∩ Θ := ⟨hyO, hyΘ⟩
      rw [hΘO] at h2
      by_contra hyD
      exact hycl (subset_closure ⟨h2.2, hyD⟩)
  have hΘD : (Θ \ c '' Dj).Nonempty := by
    obtain ⟨p, hp⟩ := hJsph.nonempty
    obtain ⟨U₁, φ, r, hU₁, hpU₁, hr, hφ, hφp, hloc⟩ :=
      exists_quadrantChart hPb hVwb hq hDV hDP hp (hcrossVP p hp)
    have hpOo : p ∈ Oo := hDO (hJD hp)
    have hopen : IsOpen (φ '' (U₁ ∩ Oo)) :=
      hφ.isOpen_image_of_isOpen Metric.isOpen_ball (hU₁.inter hOo) inter_subset_left
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen 0 ⟨p, ⟨hpU₁, hpOo⟩, hφp⟩
    have hmem : ((0 : ℝ), ε / 2, (0 : ℝ)) ∈ Metric.ball (0 : ℝ × ℝ × ℝ) ε := by
      rw [mem_ball_zero_iff, Prod.norm_def, Prod.norm_def]
      simp only [norm_zero, Real.norm_eq_abs]
      have h1 : |ε / 2| < ε := by rw [abs_of_pos (by linarith)]; linarith
      exact max_lt hε (max_lt h1 hε)
    obtain ⟨z, ⟨hzU, hzO⟩, hzφ⟩ := hball hmem
    obtain ⟨h1, -, -, -, h5⟩ := hloc z hzU
    refine ⟨z, ?_, fun hzD => ?_⟩
    · have hzV : z ∈ frontier (c '' section34VertexBallImage src f₁ w) :=
        h1.mpr (by rw [hzφ])
      have h3 : z ∈ Oo ∩ frontier (c '' section34VertexBallImage src f₁ w) := ⟨hzO, hzV⟩
      rw [← hΘO] at h3
      exact h3.2
    · have h6 := (h5.mp hzD).2
      rw [hzφ] at h6
      change ε / 2 ≤ 0 at h6
      linarith
  have hJo : ∃ O' : Set E3, IsOpen O' ∧ q '' stdSimplexBoundary 2 ⊆ O' ∧
      frontier (c '' fbl s) ∩ Θ ∩ O' ⊆ q '' stdSimplexBoundary 2 := by
    refine ⟨(Bin ∪ Bout)ᶜ, (hBinc.union hBoutc).isOpen_compl, fun x hx hxB => ?_, ?_⟩
    · rcases hxB with h | h
      · exact Set.disjoint_left.mp hBinJ h hx
      · exact Set.disjoint_left.mp hBoutJ h hx
    · rintro x ⟨⟨hxP, hxΘ⟩, hxO⟩
      rw [hPfrE] at hxP
      rcases hxP with (hxB | hxA) | (hxB | hxA)
      · exact absurd (Or.inl hxB) hxO
      · exact hAΘ x (Or.inl hxA) hxΘ
      · exact absurd (Or.inr hxB) hxO
      · exact hAΘ x (Or.inr hxA) hxΘ
  have hcarry : CarriesFirstHomologyOnto
      (c.symm '' ((frontier (c '' fbl s) ∩ Θ) \ q '' stdSimplexBoundary 2)) T :=
    hΘtor.carriesFirstHomologyOnto_image_sdiff_of_disk (Tr := frontier (c '' fbl s) ∩ Θ)
      hC hCd hCeq.symm inter_subset_right hJsph.isConnected hJsph.isPolyhedron.isClosed hJTr hJo hDΘ
      hJD hDcl hDJne hDo' hΘD (c.continuousOn_symm.mono hΘt) (c.symm.injOn.mono hΘt) hΘS hZS
  have hy₀ : yJ ∈ fblBd s ∩ Sg := ⟨hJdb hyJ, hJdSg hyJ⟩
  have hPcl : IsClosed (c '' fbl s) := hPb.isPolyhedron.isClosed
  have hPt : c '' fbl s ⊆ c.target := by
    rintro _ ⟨z, hz, rfl⟩
    exact c.map_source (hfsc hz)
  have hsymmP : c.symm '' (c '' fbl s) = fbl s := c.symm_image_image_of_subset_source hfsc
  have hrimP : c '' (h '' simplexRim 𝒦 s.1) ⊆ interior (c '' fbl s) := by
    rw [← c.image_interior_of_subset_source hfsc]
    exact image_mono (hfrim s)
  have hfrH : ∀ t : Section34SimplexIndex 𝒦 4, IsConnected (frontier (H t.1)) := by
    intro t
    obtain ⟨P0, r0, u0, hr0, hu0, hS0, hB0⟩ := hHcell t.1 t.2.1
    rw [hB0]
    exact ((isConnected_stdSimplexBoundary 1).image r0
      (hr0.isPiecewiseAffineOn.continuousOn.mono fun x hx => hx.1)).image u0
      (hu0.continuousOn.mono (by
        rintro _ ⟨x, hx, rfl⟩
        exact hr0.bijOn.mapsTo hx.1))
  have hVobs : ∀ t : Section34SimplexIndex 𝒦 4, Section34Incident s.1 t.1 →
      section34VertexBallImage src f₁ w ⊆
        section34TetraObstacle (section34VertexBallImage src f₁) fbl t := fun t hst z hz =>
    Or.inl (mem_iUnion₂.mpr ⟨⟨(t, w), hwt t hst⟩, rfl, hz⟩)
  have hfobs : ∀ t : Section34SimplexIndex 𝒦 4, Section34Incident s.1 t.1 →
      fbl s ⊆ section34TetraObstacle (section34VertexBallImage src f₁) fbl t := fun t hst z hz =>
    Or.inr (mem_iUnion₂.mpr ⟨s, hst, hz⟩)
  have hPfrf : ∀ x ∈ frontier (c '' fbl s), c.symm x ∈ fbl s := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := hPcl.frontier_subset hx
    rw [c.left_inv (hfsc hz)]
    exact hz
  have hDsymm : c.symm '' (c '' Dj) = Dj := c.symm_image_image_of_subset_source hDjc
  obtain ⟨hHb, -⟩ := (hHcell t₀.1 t₀.2.1).isPLBall_image_chart hc hHc
  have hint₀ : c '' interior (H t₀.1) = interior (c '' H t₀.1) :=
    c.image_interior_of_subset_source hHc
  have hfrY : frontier (Xc ∪ Tin) ⊆ interior (c '' H t₀.1) := by
    rw [hYsf, ← hint₀]
    rintro x (⟨z, hz, rfl⟩ | hx)
    · exact ⟨z, hVwt t₀ hst₀ (hDwV hz), rfl⟩
    · obtain ⟨z, hz, rfl⟩ := hPcl.frontier_subset (hEu.subset (Or.inl hx))
      exact ⟨z, hsTs t₀ hst₀ hz, rfl⟩
  have hYH : Xc ∪ Tin ⊆ interior (c '' H t₀.1) := by
    have hsub := hHb.subset_of_isCompact_frontier_subset hYs.isPolyhedron.isCompact
      (hfrY.trans interior_subset)
    intro x hx
    by_cases hxi : x ∈ interior (Xc ∪ Tin)
    · exact interior_mono hsub hxi
    · exact hfrY ⟨subset_closure hx, hxi⟩
  have hYt : Xc ∪ Tin ⊆ c.target := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := interior_subset (hYH hx)
    exact c.map_source (hHc hz)
  have hYM : c.symm '' (Xc ∪ Tin) ⊆ interior (H t₀.1) := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' := hYH hx
    rw [← hint₀] at hx'
    obtain ⟨z, hz, rfl⟩ := hx'
    rw [c.left_inv (hHc (interior_subset hz))]
    exact hz
  have hTinP : Disjoint Tin (interior (c '' fbl s)) := by
    refine Set.disjoint_left.mpr fun x hxT hxi => ?_
    rcases hTinR' hxT with hxR | hxD | hxA
    · exact Set.disjoint_left.mp hR'P hxR (interior_subset hxi)
    · exact (hJTr (hDP.subset ⟨hxD, interior_subset hxi⟩)).1.2 hxi
    · exact (hEu.subset (Or.inl (hEinB.symm.subset (Or.inr hxA)))).2 hxi
  have hYP : Disjoint (interior (c '' fbl s)) (Xc ∪ Tin) := by
    refine Set.disjoint_left.mpr fun x hxi hx => ?_
    rcases hx with hxX | hxT
    · exact Set.disjoint_left.mp hPX hxi hxX
    · exact Set.disjoint_left.mp hTinP hxT hxi
  have hYcell : IsPLCellOn 3 (c.symm '' (Xc ∪ Tin)) (frontier (c.symm '' (Xc ∪ Tin))) := by
    obtain ⟨r, hr'⟩ := id hYs
    have hfr : r '' stdSimplexBoundary 3 = frontier (Xc ∪ Tin) :=
      IsPLHomeomorphOn.image_stdSimplexBoundary (n := 2) hr'
    refine ⟨Xc ∪ Tin, r, c.symm, hr',
      isPLHomeomorphInto_symm_of_mem_maximalAtlas hc hYs.isPolyhedron hYt, rfl, ?_⟩
    rw [hfr, c.symm.image_frontier_of_isCompact hYs.isPolyhedron.isCompact hYt]
  have hYfrM : frontier (c.symm '' (Xc ∪ Tin)) ⊆ Dj ∪ fblBd s := by
    rw [← c.symm.image_frontier_of_isCompact hYs.isPolyhedron.isCompact hYt, hYsf, image_union,
      hDsymm]
    rintro y (hy | ⟨x, hx, rfl⟩)
    · exact Or.inl hy
    · have hx' : x ∈ c '' fblBd s := by
        rw [hPfr]
        exact hEu.subset (Or.inl hx)
      obtain ⟨z, hz, rfl⟩ := hx'
      rw [c.left_inv (hfsc (hfbs hz))]
      exact Or.inr hz
  have hYintP : Disjoint (interior (fbl s)) (c.symm '' (Xc ∪ Tin)) := by
    refine Set.disjoint_left.mpr ?_
    rintro y hyi ⟨x, hx, rfl⟩
    have hcy : x ∈ interior (c '' fbl s) := by
      rw [← c.image_interior_of_subset_source hfsc]
      exact ⟨c.symm x, hyi, c.right_inv (hYt hx)⟩
    exact Set.disjoint_left.mp hYP hcy hx
  obtain ⟨hcleanΘ, hcleanV⟩ := hclean _ hYcell hYfrM hYintP hYM
  have hfillΘ : Disjoint Θ (interior Xc) := by
    refine Set.disjoint_left.mpr fun x hxΘ hxi => ?_
    have hT' : c.symm x ∈ frontier T := by
      rw [← hΘeq] at hxΘ
      obtain ⟨z, hz, rfl⟩ := hxΘ
      rw [c.left_inv (hfrTc hz)]
      exact hz
    have hi : c.symm x ∈ interior (c.symm '' (Xc ∪ Tin)) := by
      rw [← c.symm.image_interior_of_subset_source hYt]
      exact ⟨x, interior_mono subset_union_left hxi, rfl⟩
    exact Set.disjoint_left.mp hcleanΘ hi hT'
  have hfillV : ∀ u : Section34VertexIndex 𝒦 𝒦', ¬ Section34Incident u.1 s.1 →
      Disjoint (c.symm '' Xc) (section34VertexBallImage src f₁ u) := fun u hu =>
    (hcleanV u hu).mono_left (image_mono subset_union_left)
  have hXt : Xc ⊆ c.target := fun x hx => hYt (Or.inl hx)
  have hWt : Wc ⊆ c.target := by
    rw [hWeq]
    rintro x (((hx | hx) | hx) | hx)
    · exact hPt hx
    · exact hXt hx
    · exact hYt (Or.inr hx)
    · exact hOt (hToutO hx)
  have hLinΘ : Disjoint Lin Θ := Set.disjoint_left.mpr fun x hx => hLΘ x (Or.inl hx)
  have hBinΘ : Disjoint Bin Θ := by
    refine disjoint_torus_of_disjoint_interior hPb hX hPX hXf
      (by rw [← hEu, hEinB, union_assoc]) hLinc (hAinc.union hEoutc) ?_ hLinΘ hfillΘ rfl
      hTcl hcrossPΘ hcTreg
    rintro x ⟨hxB, hxA | hxE⟩
    · exact hBAin ⟨hxB, hxA⟩
    · have hxJ : x ∈ q '' stdSimplexBoundary 2 :=
        hEi.subset ⟨hEinB.symm.subset (Or.inl hxB), hxE⟩
      exact absurd hxJ (Set.disjoint_left.mp hBinJ hxB)
  have hWΘ : frontier Wc ∩ Θ = (frontier (c '' fbl s) ∩ Θ) \ q '' stdSimplexBoundary 2 := by
    rw [hWf]
    ext x
    constructor
    · rintro ⟨hxL | hxB, hxΘ⟩
      · exact absurd hxΘ (hLΘ x (Or.inr hxL))
      · exact ⟨⟨hEu.subset (Or.inr (hEoutB.symm.subset (Or.inl hxB))), hxΘ⟩,
          fun hxJ => Set.disjoint_left.mp hBoutJ hxB hxJ⟩
    · rintro ⟨⟨hxP, hxΘ⟩, hxJ⟩
      rw [hPfrE] at hxP
      rcases hxP with (hxB | hxA) | (hxB | hxA)
      · exact absurd hxΘ (Set.disjoint_left.mp hBinΘ hxB)
      · exact absurd (hAΘ x (Or.inl hxA) hxΘ) hxJ
      · exact ⟨Or.inr hxB, hxΘ⟩
      · exact absurd (hAΘ x (Or.inr hxA) hxΘ) hxJ
  have hXΘ : Disjoint Xc Θ := by
    refine Set.disjoint_left.mpr fun x hx hxΘ => ?_
    by_cases hxi : x ∈ interior Xc
    · exact Set.disjoint_left.mp hfillΘ hxΘ hxi
    · have hxf : x ∈ frontier Xc := ⟨subset_closure hx, hxi⟩
      rw [hXf] at hxf
      rcases hxf with hxL | hxB
      · exact hLΘ x (Or.inl hxL) hxΘ
      · exact Set.disjoint_left.mp hBinΘ hxB hxΘ
  have hXM : ∀ x ∈ Xc, c.symm x ∈ c.source ∧ c (c.symm x) = x := fun x hx =>
    ⟨c.map_target (hXt hx), c.right_inv (hXt hx)⟩
  have hTinM : ∀ x ∈ Tin, c.symm x ∈ OM := fun x hx => (hOsymm x (hTinO hx)).2
  have hToutM : ∀ x ∈ Tout, c.symm x ∈ OM := fun x hx => (hOsymm x (hToutO hx)).2
  have hwne : ∀ u : Section34VertexIndex 𝒦 𝒦', ¬ Section34Incident u.1 s.1 → u ≠ w :=
    fun u hu h => hu (by rw [h]; exact hwinc)
  have hZV : ∀ u : Section34VertexIndex 𝒦 𝒦', ¬ Section34Incident u.1 s.1 →
      Disjoint (c.symm '' (Xc ∪ Tin ∪ Tout)) (section34VertexBallImage src f₁ u) := by
    intro u hu
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨x, (hx | hx) | hx, rfl⟩ hxu
    · exact Set.disjoint_left.mp (hfillV u hu) ⟨x, hx, rfl⟩ hxu
    · exact hOMV _ (hTinM x hx) u (hwne u hu) hxu
    · exact hOMV _ (hToutM x hx) u (hwne u hu) hxu
  have hXN : ∀ s' : Section34SimplexIndex 𝒦 3, s' ≠ s →
      c.symm '' Xc ∩ fbl s' ⊆ interior (⋃ w', section34VertexBallImage src f₁ w') := by
    intro s' hs'
    have hTN : interior T ⊆ interior (⋃ w', section34VertexBallImage src f₁ w') := by
      refine interior_mono fun z hz => ?_
      obtain ⟨a, -, hza⟩ := mem_iUnion₂.mp hz
      exact mem_iUnion.mpr ⟨a.1.2, hza⟩
    rcases subset_interior_or_subset_compl_of_disjoint_frontier hTcl
      hX.isConnected.isPreconnected hXΘ with hXT | hXT
    · rintro _ ⟨⟨x, hx, rfl⟩, -⟩
      refine hTN ?_
      have hx' := hXT hx
      rw [← c.image_interior_of_subset_source hTc] at hx'
      obtain ⟨z, hz, hzx⟩ := hx'
      rw [← hzx, c.left_inv (hTc (interior_subset hz))]
      exact hz
    · have hXNd : ∀ x ∈ Xc, ∀ u : Section34VertexIndex 𝒦 𝒦',
          c.symm x ∉ section34VertexBallImage src f₁ u := by
        intro x hx u hxu
        by_cases hu : Section34Incident u.1 s.1
        · refine hXT hx ?_
          rw [← (hXM x hx).2]
          exact ⟨c.symm x, hVT u hu hxu, rfl⟩
        · exact Set.disjoint_left.mp (hfillV u hu) ⟨x, hx, rfl⟩ hxu
      have hfrXM : frontier (c.symm '' Xc) = c.symm '' frontier Xc :=
        (c.symm.image_frontier_of_isCompact hX.isPolyhedron.isCompact hXt).symm
      have hdisj : Disjoint (fbl s') (frontier (c.symm '' Xc)) := by
        rw [hfrXM, hXf]
        refine Set.disjoint_left.mpr ?_
        rintro y hy ⟨x, hx | hx, rfl⟩
        · exact hOMf _ (hOsymm x (hLinO hx)).2 s' hs' hy
        · have hxP := hPfrf x (hEu.subset (Or.inl (hEinB.symm.subset (Or.inl hx))))
          have hN := hf4 s s' (Ne.symm hs') ⟨hxP, hy⟩
          obtain ⟨u, hu⟩ := mem_iUnion.mp (interior_subset hN)
          have hxX : x ∈ Xc :=
            hX.isPolyhedron.isClosed.frontier_subset (hXf.symm.subset (Or.inr hx))
          exact hXNd x hxX u hu
      have hrimne : (h '' simplexRim 𝒦 s'.1).Nonempty := by
        obtain ⟨v, hv⟩ : s'.1.Nonempty := Finset.card_pos.mp (by rw [s'.2.2]; norm_num)
        have hne : ({v} : Finset Ea) ⊂ s'.1 := by
          refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.singleton_subset_iff.mpr hv, ?_⟩
          intro hEq
          have := congrArg Finset.card hEq
          rw [Finset.card_singleton, s'.2.2] at this
          norm_num at this
        exact ⟨h (𝒦.map v), 𝒦.map v, mem_iUnion₂.mpr ⟨{v}, hne, v,
          subset_convexHull ℝ _ (by simp), rfl⟩, rfl⟩
      rintro y ⟨hyX, hys'⟩
      exfalso
      have hsub : fbl s' ⊆ c.symm '' Xc :=
        IsPreconnected.subset_of_disjoint_frontier (hfcell s').isConnected.isPreconnected
          ⟨y, hys', hyX⟩ hdisj
      obtain ⟨z, hz⟩ := hrimne
      have hzT := interior_subset (hrimT s' hz)
      obtain ⟨a, -, hza⟩ := mem_iUnion₂.mp hzT
      obtain ⟨x, hx, hxz⟩ := hsub (interior_subset (hfrim s' hz))
      rw [← hxz] at hza
      exact hXNd x hx a.1.2 hza
  have hZs : ∀ s', s' ≠ s → c.symm '' (Xc ∪ Tin ∪ Tout) ∩ fbl s' ⊆
      interior (⋃ w', section34VertexBallImage src f₁ w') := by
    rintro s' hs' _ ⟨⟨x, (hx | hx) | hx, rfl⟩, hy⟩
    · exact hXN s' hs' ⟨⟨x, hx, rfl⟩, hy⟩
    · exact absurd hy (hOMf _ (hTinM x hx) s' hs')
    · exact absurd hy (hOMf _ (hToutM x hx) s' hs')
  have hPkV : ∀ u : Section34VertexIndex 𝒦 𝒦', ¬ Section34Incident u.1 s.1 →
      Disjoint (c.symm '' (Xc ∪ Tin)) (section34VertexBallImage src f₁ u) := by
    intro u hu
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨x, hx | hx, rfl⟩ hxu
    · exact Set.disjoint_left.mp (hfillV u hu) ⟨x, hx, rfl⟩ hxu
    · exact hOMV _ (hTinM x hx) u (hwne u hu) hxu
  have hPkfr : ∀ t : Section34SimplexIndex 𝒦 4, Section34Incident s.1 t.1 →
      c.symm '' frontier (Xc ∪ Tin) ⊆
        section34TetraObstacle (section34VertexBallImage src f₁) fbl t := by
    intro t hst
    rw [hYsf, image_union, hDsymm]
    rintro y (hy | ⟨x, hx, rfl⟩)
    · exact hVobs t hst (hDwV hy)
    · exact hfobs t hst (hPfrf x (hEu.subset (Or.inl hx)))
  have hcyY : c yJ ∈ Xc ∪ Tin := by
    have hyT : c yJ ∈ frontier (Xc ∪ Tin) := by
      rw [hYsf]
      exact Or.inl ⟨yJ, hJdD hyJ, rfl⟩
    exact hYs.isPolyhedron.isClosed.frontier_subset hyT
  have hpocketH : ∀ t : Section34SimplexIndex 𝒦 4, Section34Incident s.1 t.1 →
      c.symm '' (Xc ∪ Tin) ⊆ interior (H t.1) := by
    refine subset_interior_carrier_of_section34Pocket hcut hctrl hgraph hext hst₀
      (hYs.isConnected.isPreconnected.image _ (c.continuousOn_symm.mono hYt)) hYM
      (fun t hst => ?_) hPkV (fun t hst => ⟨yJ, ⟨c yJ, hcyY, c.left_inv (hDjc (hJdD hyJ))⟩,
        interior_subset (hVwt t hst (hDwV (hJdD hyJ)))⟩)
    rw [← c.symm.image_frontier_of_isCompact hYs.isPolyhedron.isCompact hYt]
    exact hPkfr t hst
  have hZH : ∀ t : Section34SimplexIndex 𝒦 4, Section34Incident s.1 t.1 →
      c.symm '' (Xc ∪ Tin ∪ Tout) ⊆ interior (H t.1) := by
    intro t hst
    rintro _ ⟨x, hx | hx, rfl⟩
    · exact hpocketH t hst ⟨x, hx, rfl⟩
    · exact hOMH _ (hToutM x hx) t hst
  have hPsymm : ∀ x ∈ c '' fbl s, c.symm x ∈ fbl s := by
    rintro _ ⟨z, hz, rfl⟩
    rw [c.left_inv (hfsc hz)]
    exact hz
  have hWO₀ : c.symm '' Wc ⊆ O₀ := by
    rw [hWeq]
    rintro _ ⟨x, ((hx | hx) | hx) | hx, rfl⟩
    · exact hfO₀ (hPsymm x hx)
    · rw [hO₀def]
      refine ⟨hYM ⟨x, Or.inl hx, rfl⟩, fun hxQ => ?_⟩
      obtain ⟨u, ⟨-, hu⟩, hxu⟩ := mem_iUnion₂.mp hxQ
      exact Set.disjoint_left.mp (hfillV u hu) ⟨x, hx, rfl⟩ hxu
    · exact (hTinM x hx).1.2
    · exact (hToutM x hx).1.2
  have hGZ : c.symm '' Wc ⊆ fbl s ∪ c.symm '' (Xc ∪ Tin ∪ Tout) := by
    rw [hWeq]
    rintro _ ⟨x, ((hx | hx) | hx) | hx, rfl⟩
    · exact Or.inl (hPsymm x hx)
    · exact Or.inr ⟨x, Or.inl (Or.inl hx), rfl⟩
    · exact Or.inr ⟨x, Or.inl (Or.inr hx), rfl⟩
    · exact Or.inr ⟨x, Or.inr hx, rfl⟩
  have hPW : c '' fbl s ⊆ Wc := fun x hx => by
    rw [hWeq]
    exact Or.inl (Or.inl (Or.inl hx))
  have hrimW : c '' (h '' simplexRim 𝒦 s.1) ⊆ interior Wc := hrimP.trans (interior_mono hPW)
  have hr : ∀ t : Section34SimplexIndex 𝒦 4, Section34Incident s.1 t.1 → ∃ r : M₂ → M₂,
      ContinuousOn r (H t.1 \ section34TetraObstacle (section34VertexBallImage src f₁) fbl t) ∧
      MapsTo r (H t.1 \ section34TetraObstacle (section34VertexBallImage src f₁) fbl t)
        (H t.1 \ (section34TetraObstacle (section34VertexBallImage src f₁) fbl t ∪
          c.symm '' (Xc ∪ Tin ∪ Tout))) ∧
      (∀ z ∈ frontier (H t.1), r z = z) ∧
      ∀ u : Section34VertexIndex 𝒦 𝒦', ¬ Section34Incident u.1 t.1 →
        ∀ y ∈ h '' simplexBody 𝒦' u.1, r y = y := by
    intro t hst
    set Obs := section34TetraObstacle (section34VertexBallImage src f₁) fbl t with hObsdef
    set Mk := ⋃ (u : Section34VertexIndex 𝒦 𝒦') (_ : ¬ Section34Incident u.1 t.1),
      h '' simplexBody 𝒦' u.1 with hMkdef
    have hMkV : ∀ y ∈ Mk, ∃ u : Section34VertexIndex 𝒦 𝒦', ¬ Section34Incident u.1 s.1 ∧
        u ≠ w ∧ y ∈ section34VertexBallImage src f₁ u := by
      intro y hy
      obtain ⟨u, hu, hyu⟩ := mem_iUnion₂.mp hy
      have hus : ¬ Section34Incident u.1 s.1 := fun h' =>
        hu (h'.trans (convexHull_min hst (convex_convexHull ℝ _)))
      exact ⟨u, hus, hwne u hus, interior_subset (hmark u hyu)⟩
    have hMkY : Disjoint Mk (c.symm '' (Xc ∪ Tin)) := by
      refine Set.disjoint_left.mpr fun y hy hyY => ?_
      obtain ⟨u, hus, -, hyu⟩ := hMkV y hy
      exact Set.disjoint_left.mp (hPkV u hus) hyY hyu
    have hbdd : closure R ⊆ c '' H t₀.1 := by
      refine closure_minimal (fun x hx => ?_) hHb.isPolyhedron.isClosed
      obtain ⟨⟨z, hz, rfl⟩, -⟩ := hRO hx
      exact ⟨z, interior_subset (hOMH z hz.1 t₀ hst₀), rfl⟩
    have hBh : c.symm '' (c '' Dj ∪ Aout) ⊆ Obs := by
      rw [image_union, hDsymm]
      rintro y (hy | ⟨x, hx, rfl⟩)
      · exact hVobs t hst (hDwV hy)
      · exact hfobs t hst (hPfrf x (hEu.subset (Or.inr (hEoutB.symm.subset (Or.inr hx)))))
    have hRM : ∀ y ∈ c.symm '' R, y ∈ OM := by
      rintro _ ⟨x, hx, rfl⟩
      exact (hOsymm x (hRO hx)).2
    have hRobs : c.symm '' R ⊆ Obs ∨ Disjoint (c.symm '' R) Obs := by
      rcases hRV with hRV | hRV
      · left
        rintro _ ⟨x, hx, rfl⟩
        obtain ⟨z, hz, rfl⟩ := hRV hx
        rw [c.left_inv (hVc w hwinc hz)]
        exact hVobs t hst hz
      · right
        refine Set.disjoint_left.mpr ?_
        rintro _ ⟨x, hx, rfl⟩ hxo
        have hxM := (hOsymm x (hRO hx)).2
        rcases hxo with hxo | hxo
        · obtain ⟨pp, -, hpp⟩ := mem_iUnion₂.mp hxo
          by_cases hpw : pp.1.2 = w
          · rw [hpw] at hpp
            refine Set.disjoint_left.mp hRV hx ?_
            rw [← c.right_inv (hOt (hRO hx))]
            exact ⟨c.symm x, hpp, rfl⟩
          · exact hOMV _ hxM pp.1.2 hpw hpp
        · obtain ⟨s'', -, hs''⟩ := mem_iUnion₂.mp hxo
          by_cases hss : s'' = s
          · rw [hss] at hs''
            refine Set.disjoint_left.mp hRP hx ?_
            rw [← c.right_inv (hOt (hRO hx))]
            exact ⟨c.symm x, hs'', rfl⟩
          · exact hOMf _ hxM s'' hss hs''
    obtain ⟨r, hrc, hrm, hrfr, hrk⟩ := exists_reroute_pocket_push (c := c) (Hs := H t.1)
      (Obs := Obs) (Mk := Mk) hYs.isPolyhedron.isCompact hYt
      (hPkfr t hst)
      (Set.disjoint_left.mpr fun y hy hyf => hyf.2 (hpocketH t hst hy)) hMkY (hfrH t).nonempty
      (hHcell t.1 t.2.1).isCompact.isClosed
      (Set.disjoint_left.mpr fun y hy hyf => hyf.2 (hext1 t hy)) hRo hclR
      (hHb.isPolyhedron.isCompact.of_isClosed_subset isClosed_closure hbdd)
      (fun x hx => by
        obtain ⟨z, hz, rfl⟩ := hbdd hx
        exact c.map_source (hHc hz))
      (fun x hx => hOt (hLrO hx)) (fun x hx => hOt (hToutO hx)) hBh hgc hgLr hgR hgT hToutR
      (fun y hy => interior_subset (hOMH y (hRM y hy) t hst)) hRobs
      (Set.disjoint_left.mpr fun y hy hyf => hyf.2 (hOMH y (hRM y hy) t hst))
      (Set.disjoint_left.mpr fun y hy hyR => by
        obtain ⟨u, -, huw, hyu⟩ := hMkV y hy
        exact hOMV y (hRM y hyR) u huw hyu) hRY
    exact ⟨r, hrc, hrm, hrfr, fun u hu y hy => hrk y (mem_iUnion₂.mpr ⟨u, hu, hy⟩)⟩
  have hOc : IsOpen (Lout ∪ Ein ∪ Aout)ᶜ := ((hLoutc.union hEinc).union hAoutc).isOpen_compl
  have hfrO : frontier Wc ∩ (Lout ∪ Ein ∪ Aout)ᶜ =
      frontier (c '' fbl s) ∩ (Lout ∪ Ein ∪ Aout)ᶜ := by
    rw [hWf, ← hEu, hEoutB]
    ext x
    constructor
    · rintro ⟨hxL | hxB, hxO⟩
      · exact absurd (Or.inl (Or.inl hxL)) hxO
      · exact ⟨Or.inr (Or.inl hxB), hxO⟩
    · rintro ⟨hxE | hxB | hxA, hxO⟩
      · exact absurd (Or.inl (Or.inr hxE)) hxO
      · exact ⟨Or.inr hxB, hxO⟩
      · exact absurd (Or.inr hxA) hxO
  have hk2 : frontier Wc ∩ Θ ⊆ (Lout ∪ Ein ∪ Aout)ᶜ := by
    rw [hWΘ]
    rintro x ⟨⟨hxP, hxΘ⟩, hxJ⟩ ((hxL | hxE) | hxA)
    · exact hLΘ x (Or.inr hxL) hxΘ
    · rw [hEinB] at hxE
      rcases hxE with hxB | hxA
      · exact Set.disjoint_left.mp hBinΘ hxB hxΘ
      · exact hxJ (hAΘ x (Or.inl hxA) hxΘ)
    · exact hxJ (hAΘ x (Or.inr hxA) hxΘ)
  have hk4 : ∀ e : Section34EdgeIndex 𝒦 𝒦',
      frontier Wc ∩ c '' (section34SplitDiskImage srcBd f₁ e ∩ c.source) ⊆
        (Lout ∪ Ein ∪ Aout)ᶜ := by
    rintro e x ⟨hxW, hxE⟩ ((hxL | hxI) | hxA)
    · exact hOsplit x (hLoutO hxL) e hxE
    · rw [hWf] at hxW
      rcases hxW with hxL | hxB
      · exact hOsplit x (hLoutO hxL) e hxE
      · have hxJ : x ∈ q '' stdSimplexBoundary 2 :=
          hEi.subset ⟨hxI, hEoutB.symm.subset (Or.inl hxB)⟩
        obtain ⟨y, ⟨hye, hyc⟩, rfl⟩ := hxE
        obtain ⟨y', hy', hyy'⟩ := hJD hxJ
        have hyy := c.injOn (hDjc hy') hyc hyy'
        rw [hyy] at hy'
        obtain ⟨a, ha, hay⟩ := image_mono (hcell (.splitDisk e)).boundary_subset hye
        exact Set.disjoint_left.mp (hDE e) hy' ⟨a, ha, hay⟩
    · exact hOsplit x (hAoutO hxA) e hxE
  have hk3 : frontier Wc ∩ Θ = frontier (c '' fbl s) ∩ Θ ∩ Bout := by
    rw [hWΘ]
    ext x
    constructor
    · rintro ⟨⟨hxP, hxΘ⟩, hxJ⟩
      refine ⟨⟨hxP, hxΘ⟩, ?_⟩
      rw [hPfrE] at hxP
      rcases hxP with (hxB | hxA) | (hxB | hxA)
      · exact absurd hxΘ (Set.disjoint_left.mp hBinΘ hxB)
      · exact absurd (hAΘ x (Or.inl hxA) hxΘ) hxJ
      · exact hxB
      · exact absurd (hAΘ x (Or.inr hxA) hxΘ) hxJ
    · rintro ⟨hxPΘ, hxB⟩
      exact ⟨hxPΘ, fun hxJ => Set.disjoint_left.mp hBoutJ hxB hxJ⟩
  have hBoutP : Bout ⊆ frontier (c '' fbl s) := fun x hx =>
    hEu.subset (Or.inr (hEoutB.symm.subset (Or.inl hx)))
  have hSel : IsCompact Bout :=
    (hPb.isPolyhedron.isCompact.of_isClosed_subset isClosed_frontier
      hPcl.frontier_subset).of_isClosed_subset hBoutc hBoutP
  have hSelt : Bout ⊆ c.target := fun x hx => hPt (hPcl.frontier_subset (hBoutP hx))
  have hy₀S : c yJ ∉ Bout := fun h' => Set.disjoint_left.mp hBoutJ h' hcy₀
  have h7 : CarriesFirstHomologyOnto (c.symm '' (frontier Wc ∩ Θ)) T := by
    rw [hWΘ]
    exact hcarry
  exact exists_section34Compression_of_chartBall hinv s hc hfsc hTc hTcomp hfO₀ hSgO₀ hW hWt
    hWO₀ hrimW hGZ hZV hZs hZH hr hOc hfrO hk2 hk4 hk3 hSel hSelt hy₀ hy₀S h7
end Outside

end DifferentialGeometry.Topology.PiecewiseLinear
