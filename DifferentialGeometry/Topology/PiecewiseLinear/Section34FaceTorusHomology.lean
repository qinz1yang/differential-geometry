/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CellTraceFirstHomology
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodOpenRetraction
import DifferentialGeometry.Topology.PiecewiseLinear.DiskBallNeighborhoodImage
import DifferentialGeometry.Topology.PiecewiseLinear.Section34VertexBallStar
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.SphericalDiskComplement

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

theorem CarriesFirstHomologyOnto.inter_frontier_of_chart {M : Type u} [TopologicalSpace M]
    {S T : Set M} (h : CarriesFirstHomologyOnto (S ∩ interior T) T) (hS : IsClosed S)
    (hT : IsClosed T) (hS1 : Subsingleton (integralSingularHomology 1 S))
    {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))} (hSc : S ⊆ c.source)
    (A B : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) [Finite A.faces]
    (hBA : B.faces ⊆ A.faces) (hA : A.space = c '' (S ∩ T))
    (hB : B.space = c '' (S ∩ frontier T)) :
    CarriesFirstHomologyOnto (S ∩ frontier T) T := by
  obtain ⟨N₀, hN₀, hBN₀, g₀, hg₀⟩ := exists_isOpen_homotopic_retraction_of_faces_subset hBA
  have hN : IsOpen (c.source ∩ c ⁻¹' N₀) := c.isOpen_inter_preimage hN₀
  have hSN : S ∩ frontier T ⊆ c.source ∩ c ⁻¹' N₀ := fun x hx =>
    ⟨hSc hx.1, hBN₀ (by rw [hB]; exact ⟨x, hx, rfl⟩)⟩
  have hin : ∀ x : ↥(S ∩ interior T ∩ (c.source ∩ c ⁻¹' N₀)), c x ∈ A.space ∩ N₀ := fun x =>
    ⟨by rw [hA]; exact ⟨x, ⟨x.2.1.1, interior_subset x.2.1.2⟩, rfl⟩, x.2.2.2⟩
  let φ : C(↥(S ∩ interior T ∩ (c.source ∩ c ⁻¹' N₀)), ↥(A.space ∩ N₀)) :=
    ⟨fun x => ⟨c x, hin x⟩, (c.continuousOn.comp_continuous continuous_subtype_val
      fun x => x.2.2.1).subtype_mk _⟩
  have hAc : A.space ⊆ c.target := by
    rw [hA]
    rintro _ ⟨x, hx, rfl⟩
    exact c.map_source (hSc hx.1)
  have hAT : ∀ y : ↥A.space, c.symm y ∈ T := by
    intro y
    have hy : (y : EuclideanSpace ℝ (Fin 3)) ∈ c '' (S ∩ T) := hA ▸ y.2
    obtain ⟨x, hx, hxy⟩ := hy
    rw [← hxy, c.left_inv (hSc hx.1)]
    exact hx.2
  let ψ : C(↥A.space, ↥T) :=
    ⟨fun y => ⟨c.symm y, hAT y⟩, (c.continuousOn_symm.comp_continuous continuous_subtype_val
      fun y => hAc y.2).subtype_mk _⟩
  have hBc : B.space ⊆ c.target := by
    rw [hB]
    rintro _ ⟨x, hx, rfl⟩
    exact c.map_source (hSc hx.1)
  have hBfr : ∀ y : ↥B.space, c.symm y ∈ S ∩ frontier T := by
    intro y
    have hy : (y : EuclideanSpace ℝ (Fin 3)) ∈ c '' (S ∩ frontier T) := hB ▸ y.2
    obtain ⟨x, hx, hxy⟩ := hy
    rw [← hxy, c.left_inv (hSc hx.1)]
    exact hx
  let g : C(↥(S ∩ interior T ∩ (c.source ∩ c ⁻¹' N₀)), ↥(S ∩ frontier T)) :=
    ⟨fun x => ⟨c.symm (g₀ (φ x)), hBfr (g₀ (φ x))⟩,
      (c.continuousOn_symm.comp_continuous
        (continuous_subtype_val.comp (g₀.continuous.comp φ.continuous))
        fun x => hBc (g₀ (φ x)).2).subtype_mk _⟩
  refine h.inter_frontier_of_homotopic hS hT hS1 hN hSN g ?_
  have hcomp := (ContinuousMap.Homotopic.refl ψ).comp (hg₀.comp (ContinuousMap.Homotopic.refl φ))
  convert hcomp using 1
  · refine ContinuousMap.ext fun x => Subtype.ext ?_
    exact (c.left_inv x.2.2.1).symm
  · refine ContinuousMap.ext fun x => Subtype.ext ?_
    rfl

theorem IsPLCellOn.isPathConnected {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {d : ℕ} {S B : Set M} (hS : IsPLCellOn d S B) :
    IsPathConnected S := by
  obtain ⟨P, r, v, hr, hv, rfl, -⟩ := hS
  have h1 : IsPathConnected (Convexity.StdSimplex.coordinateSet ℝ (Fin (d + 1))) :=
    (Convexity.StdSimplex.convex_coordinateSet ℝ _).isPathConnected ⟨_, Convexity.StdSimplex.single_mem_coordinateSet ℝ (0 : Fin (d + 1))⟩
  have h2 := h1.image' hr.isPiecewiseAffineOn.continuousOn
  rw [hr.bijOn.image_eq] at h2
  exact h2.image' hv.continuousOn

section Frames

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
  {U W : Set M₁} {h : M₁ → M₂} {η ψ : M₁ → ℝ} {H : Finset Ea → Set M₂}
  {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U} {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁}
  {cr : Section34VertexIndex 𝒦 𝒦' → Finset Ea} {f₁ : M₁ → M₂}

omit [FiniteDimensional ℝ Ea] in
theorem isPathConnected_section34FaceTorus (hh : IsEmbedding (U.domRestrict h))
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hgraph : Section34GraphFrame U W h ψ H 𝒦 𝒦' src cr f₁) (s : Section34SimplexIndex 𝒦 3) :
    IsPathConnected (section34FaceTorus (section34VertexBallImage src f₁) s) := by
  classical
  obtain ⟨-, -, hmap, hcell, -⟩ := id hcut
  obtain ⟨-, -, hf₁, -, -, hcore, -, -, hrim, -⟩ := id hgraph
  have hhU : ContinuousOn h U := continuousOn_iff_continuous_domRestrict.mpr hh.continuous
  have hΦ : ContinuousOn (fun z => h (𝒦.map z)) 𝒦.complex.space :=
    hhU.comp 𝒦.continuousOn fun z hz => 𝒦.bijOn.mapsTo hz
  have hNV : ∀ v : Section34VertexIndex 𝒦 𝒦',
      src (.vertexBall v) ⊆ section34CutNeighborhood src :=
    fun v => subset_iUnion (fun v => src (Section34Label.vertexBall v)) v
  obtain ⟨a, ha⟩ := 𝒦.complex.nonempty_of_mem_faces s.2.1
  have hpiece : ∀ τ : Finset Ea, τ ⊆ s.1 → τ.Nonempty →
      IsPathConnected ((fun z => h (𝒦.map z)) '' convexHull ℝ (τ : Set Ea)) := by
    intro τ hτ hne
    have hτK : τ ∈ 𝒦.complex.faces := 𝒦.complex.down_closed s.2.1 hτ hne
    exact ((convex_convexHull ℝ _).isPathConnected
      ⟨_, subset_convexHull ℝ _ (Finset.mem_coe.mpr hne.choose_spec)⟩).image'
        (hΦ.mono (𝒦.complex.convexHull_subset_space hτK))
  have hrimΦ : ∀ τ : Finset Ea, τ ⊂ s.1 →
      (fun z => h (𝒦.map z)) '' convexHull ℝ (τ : Set Ea) ⊆ h '' simplexRim 𝒦 s.1 := by
    rintro τ hτ _ ⟨z, hz, rfl⟩
    exact ⟨𝒦.map z, mem_iUnion₂.mpr ⟨τ, hτ, z, hz, rfl⟩, rfl⟩
  have hcard : s.1.card = 3 := s.2.2
  have hpair : ∀ v ∈ s.1, v ≠ a → ({v, a} : Finset Ea) ⊂ s.1 := by
    intro v hv hva
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.insert_subset hv
      (Finset.singleton_subset_iff.mpr ha), fun heq => ?_⟩
    have := Finset.card_pair hva
    rw [heq, hcard] at this
    omega
  have hjoinA : ∀ v ∈ s.1, JoinedIn (h '' simplexRim 𝒦 s.1) (h (𝒦.map v)) (h (𝒦.map a)) := by
    intro v hv
    by_cases hva : v = a
    · rw [hva]
      exact JoinedIn.refl ((hrimΦ {a} (Finset.ssubset_iff_subset_ne.mpr
        ⟨Finset.singleton_subset_iff.mpr ha, fun heq => by
          have := congrArg Finset.card heq
          rw [Finset.card_singleton, hcard] at this
          omega⟩)) ⟨a, subset_convexHull ℝ _ (by simp), rfl⟩)
    · have hP := hpiece {v, a} (hpair v hv hva).1 (Finset.insert_nonempty v {a})
      exact (hP.joinedIn _ ⟨v, subset_convexHull ℝ _ (by simp), rfl⟩ _
        ⟨a, subset_convexHull ℝ _ (by simp), rfl⟩).mono (hrimΦ _ (hpair v hv hva))
  have hrimPC : ∀ y ∈ h '' simplexRim 𝒦 s.1, JoinedIn (h '' simplexRim 𝒦 s.1) y (h (𝒦.map a)) := by
    rintro _ ⟨_, hm, rfl⟩
    obtain ⟨τ, hτ, z, hz, rfl⟩ := mem_iUnion₂.mp hm
    have hτne : τ.Nonempty := by
      by_contra hemp
      rw [Finset.not_nonempty_iff_eq_empty] at hemp
      rw [hemp, Finset.coe_empty, convexHull_empty] at hz
      exact hz
    obtain ⟨v, hv⟩ := hτne
    have hP := hpiece τ hτ.1 ⟨v, hv⟩
    refine ((hP.joinedIn _ ⟨z, hz, rfl⟩ _ ⟨v, subset_convexHull ℝ _ (Finset.mem_coe.mpr hv),
      rfl⟩).mono (hrimΦ τ hτ)).trans (hjoinA v (hτ.1 hv))
  have hrimT : h '' simplexRim 𝒦 s.1 ⊆ section34FaceTorus (section34VertexBallImage src f₁) s :=
    (hrim s).trans interior_subset
  have haRim : h (𝒦.map a) ∈ h '' simplexRim 𝒦 s.1 := by
    refine hrimΦ {a} (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.singleton_subset_iff.mpr ha,
      fun heq => ?_⟩) ⟨a, subset_convexHull ℝ _ (by simp), rfl⟩
    have := congrArg Finset.card heq
    rw [Finset.card_singleton, hcard] at this
    omega
  refine ⟨h (𝒦.map a), hrimT haRim, fun {y} hy => ?_⟩
  obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.mp hy
  set w := x.1.2 with hw
  obtain ⟨p, hp⟩ := Finset.card_eq_one.mp w.2.2.1
  have hpw : p ∈ (w.1 : Set Ea) := by
    rw [hp]
    exact Finset.mem_coe.mpr (Finset.mem_singleton_self p)
  have hinc : Section34Incident w.1 s.1 := by
    rw [← hx]
    exact x.2
  have hps : p ∈ convexHull ℝ (s.1 : Set Ea) := hinc hpw
  have hpK : p ∈ 𝒦.complex.space := 𝒦.complex.convexHull_subset_space s.2.1 hps
  have hzw : h (𝒦.map p) ∈ section34VertexBallImage src f₁ w := by
    apply interior_subset
    apply hcore w
    exact ⟨𝒦'.map p, ⟨p, subset_convexHull ℝ _ hpw, rfl⟩, by rw [hmap]⟩
  have hzRim : h (𝒦.map p) ∈ h '' simplexRim 𝒦 s.1 := by
    have hpΓ : 𝒦.map p ∈ graphSkeletonSpace 𝒦 := by
      apply w.2.2.2
      exact ⟨p, subset_convexHull ℝ _ hpw, by rw [hmap]⟩
    obtain ⟨e, ⟨he, he2⟩, p', hp', hpp'⟩ := mem_iUnion₂.mp hpΓ
    have hpp : p' = p := 𝒦.bijOn.injOn (𝒦.complex.convexHull_subset_space he hp') hpK hpp'
    rw [hpp] at hp'
    obtain ⟨σ, hσ, hpσ⟩ := exists_face_mem_openSimplex 𝒦.complex hpK
    have hσe := face_subset_of_mem_openSimplex_of_mem_convexHull _ hσ he hpσ hp'
    have hσs := face_subset_of_mem_openSimplex_of_mem_convexHull _ hσ s.2.1 hpσ hps
    have hσss : σ ⊂ s.1 := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨hσs, fun heq => ?_⟩
      have h1 := Finset.card_le_card hσe
      rw [heq, hcard] at h1
      omega
    exact ⟨𝒦.map p, mem_iUnion₂.mpr ⟨σ, hσss, p, openSimplex_subset_convexHull σ hpσ, rfl⟩, rfl⟩
  have hwPC : IsPathConnected (section34VertexBallImage src f₁ w) :=
    (hcell (.vertexBall w)).isPathConnected.image' (hf₁.continuousOn.mono (hNV w))
  have hwT : section34VertexBallImage src f₁ w ⊆
      section34FaceTorus (section34VertexBallImage src f₁) s :=
    fun z hz => mem_iUnion₂.mpr ⟨x, hx, hz⟩
  exact ((hrimPC _ hzRim).mono hrimT).symm.trans
    ((hwPC.joinedIn _ hzw _ hyx).mono hwT)

omit [FiniteDimensional ℝ Ea] in
theorem carriesFirstHomologyOnto_image_simplexRim (hh : IsEmbedding (U.domRestrict h))
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hgraph : Section34GraphFrame U W h ψ H 𝒦 𝒦' src cr f₁) (s : Section34SimplexIndex 𝒦 3) :
    CarriesFirstHomologyOnto (h '' simplexRim 𝒦 s.1)
      (section34FaceTorus (section34VertexBallImage src f₁) s) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hgen, -⟩ := id hgraph
  obtain ⟨a, ha⟩ := 𝒦.complex.nonempty_of_mem_faces s.2.1
  have hne : (h '' simplexRim 𝒦 s.1).Nonempty := by
    refine ⟨h (𝒦.map a), 𝒦.map a, mem_iUnion₂.mpr ⟨{a}, Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.singleton_subset_iff.mpr ha, fun heq => ?_⟩, a, by simp, rfl⟩, rfl⟩
    have := congrArg Finset.card heq
    rw [Finset.card_singleton, s.2.2] at this
    omega
  exact (hgen s).carriesFirstHomologyOnto hne (isPathConnected_section34FaceTorus hh hcut hgraph s)

open Classical in
theorem exists_section34FaceTorusAuxiliary (hh : IsEmbedding (U.domRestrict h))
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hgraph : Section34GraphFrame U W h ψ H 𝒦 𝒦' src cr f₁) (s : Section34SimplexIndex 𝒦 3) :
    ∃ C' : Set M₂, IsCompact C' ∧ Subsingleton (integralSingularHomology 1 C') ∧
      h '' simplexRim 𝒦 s.1 ⊆ C' ∧
      Disjoint (h '' simplexBody 𝒦 s.1)
        (C' \ interior (section34FaceTorus (section34VertexBallImage src f₁) s)) := by
  obtain ⟨hK, -⟩ := id hcut
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hcof⟩ := id hcut
  obtain ⟨-, -, -, -, -, -, -, -, hrim, -⟩ := id hgraph
  have hhU : ContinuousOn h U := continuousOn_iff_continuous_domRestrict.mpr hh.continuous
  have hhinj : InjOn h U := fun a ha b hb hab =>
    congrArg Subtype.val (@hh.injective ⟨a, ha⟩ ⟨b, hb⟩ hab)
  have hΦ : ContinuousOn (fun z => h (𝒦.map z)) 𝒦.complex.space :=
    hhU.comp 𝒦.continuousOn fun z hz => 𝒦.bijOn.mapsTo hz
  have hΦinj : InjOn (fun z => h (𝒦.map z)) 𝒦.complex.space := fun z hz z' hz' hzz =>
    𝒦.bijOn.injOn hz hz' (hhinj (𝒦.bijOn.mapsTo hz) (𝒦.bijOn.mapsTo hz') hzz)
  obtain ⟨t, hst⟩ := hcof s
  have hsub : s.1 ⊆ t.1 := fun v hv => mem_of_mem_convexHull_of_singleton_mem _
    (𝒦.complex.down_closed s.2.1 (Finset.singleton_subset_iff.mpr hv)
      (Finset.singleton_nonempty v)) t.2.1 (hst (Finset.mem_coe.mpr hv))
  obtain ⟨d, hdt, hds⟩ : ∃ d ∈ t.1, d ∉ s.1 := by
    by_contra hcon
    have hts : t.1 ⊆ s.1 := fun v hv => by
      by_contra hvs
      exact hcon ⟨v, hv, hvs⟩
    have := Finset.card_le_card hts
    rw [t.2.2, s.2.2] at this
    omega
  have hteq : t.1.erase d = s.1 := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro v hv
      exact Finset.mem_erase.mpr ⟨fun hvd => hds (hvd ▸ hv), hsub hv⟩
    · rw [Finset.card_erase_of_mem hdt, t.2.2, s.2.2]
  have hfacet : ∀ v ∈ t.1, t.1.erase v ∈ 𝒦.complex.faces := fun v hv =>
    𝒦.complex.down_closed t.2.1 (Finset.erase_subset v t.1)
      (Finset.card_pos.mp (by rw [Finset.card_erase_of_mem hv, t.2.2]; omega))
  let D : Set Ea := ⋃ v ∈ s.1, convexHull ℝ ((t.1.erase v : Finset Ea) : Set Ea)
  have hSph : IsPLSphere 2 (⋃ v ∈ t.1, convexHull ℝ ((t.1.erase v : Finset Ea) : Set Ea)) :=
    isPLSphere_biUnion_erase t.1 (𝒦.complex.indep t.2.1) (by rw [t.2.2])
  have hsDisk : IsPLBall 2 (convexHull ℝ (s.1 : Set Ea)) :=
    isPLBall_convexHull_of_affineIndependent s.1 (𝒦.complex.indep s.2.1) (by rw [s.2.2])
  have hsSph : convexHull ℝ (s.1 : Set Ea) ⊆
      ⋃ v ∈ t.1, convexHull ℝ ((t.1.erase v : Finset Ea) : Set Ea) := by
    rw [← hteq]
    exact subset_biUnion_of_mem (u := fun v => convexHull ℝ ((t.1.erase v : Finset Ea) : Set Ea))
      (Finset.mem_coe.mpr hdt)
  have hDeq : closure ((⋃ v ∈ t.1, convexHull ℝ ((t.1.erase v : Finset Ea) : Set Ea)) \
      convexHull ℝ (s.1 : Set Ea)) = D := by
    apply Subset.antisymm
    · refine closure_minimal ?_ ?_
      · rintro z ⟨hz, hzs⟩
        obtain ⟨v, hv, hzv⟩ := mem_iUnion₂.mp hz
        have hvs : v ∈ s.1 := by
          by_contra hvs
          have hvd : v = d := by
            by_contra hvd
            exact hvs (hteq ▸ Finset.mem_erase.mpr ⟨hvd, hv⟩)
          rw [hvd, hteq] at hzv
          exact hzs hzv
        exact mem_iUnion₂.mpr ⟨v, hvs, hzv⟩
      · exact s.1.finite_toSet.isClosed_biUnion fun v _ =>
          ((t.1.erase v).finite_toSet.isCompact_convexHull (𝕜 := ℝ)).isClosed
    · refine iUnion₂_subset fun v hv => ?_
      have hvt := hsub hv
      have hne : (t.1.erase v).Nonempty :=
        Finset.card_pos.mp (by rw [Finset.card_erase_of_mem hvt, t.2.2]; omega)
      refine (convexHull_subset_closure_openSimplex hne).trans (closure_mono ?_)
      intro z hz
      refine ⟨mem_iUnion₂.mpr ⟨v, hvt, openSimplex_subset_convexHull _ hz⟩, fun hzs => ?_⟩
      rw [← hteq] at hzs
      have hsubset := face_subset_of_mem_openSimplex_of_mem_convexHull _ (hfacet v hvt)
        (hfacet d hdt) hz hzs
      have hdv : d ≠ v := fun hdv => hds (hdv ▸ hv)
      exact Finset.notMem_erase d t.1 (hsubset (Finset.mem_erase.mpr ⟨hdv, hdt⟩))
  have hD : IsPLBall 2 D := by
    rw [← hDeq]
    exact hSph.isPLBall_closure_sdiff hsDisk hsSph
  have hD𝒦 : D ⊆ 𝒦.complex.space :=
    iUnion₂_subset fun v hv => 𝒦.complex.convexHull_subset_space (hfacet v (hsub hv))
  have hrimD : ∀ τ : Finset Ea, τ ⊂ s.1 → convexHull ℝ (τ : Set Ea) ⊆ D := by
    intro τ hτ
    obtain ⟨v, hvs, hvτ⟩ := Finset.exists_of_ssubset hτ
    refine (convexHull_mono (Finset.coe_subset.mpr fun u hu => ?_)).trans
      (subset_biUnion_of_mem (u := fun v => convexHull ℝ ((t.1.erase v : Finset Ea) : Set Ea))
        (Finset.mem_coe.mpr hvs))
    exact Finset.mem_erase.mpr ⟨fun huv => hvτ (huv ▸ hu), hsub (hτ.1 hu)⟩
  have hDs : ∀ z ∈ D, z ∈ convexHull ℝ (s.1 : Set Ea) →
      h (𝒦.map z) ∈ h '' simplexRim 𝒦 s.1 := by
    intro z hz hzs
    obtain ⟨v, hv, hzv⟩ := mem_iUnion₂.mp hz
    have hint := 𝒦.complex.inter_subset_convexHull (hfacet v (hsub hv)) s.2.1 ⟨hzv, hzs⟩
    rw [← Finset.coe_inter] at hint
    have hproper : t.1.erase v ∩ s.1 ⊂ s.1 := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.inter_subset_right, fun heq => ?_⟩
      have hv' : v ∈ t.1.erase v ∩ s.1 := by
        rw [heq]
        exact hv
      exact Finset.notMem_erase v t.1 (Finset.mem_inter.mp hv').1
    exact ⟨𝒦.map z, mem_iUnion₂.mpr ⟨_, hproper, z, hint, rfl⟩, rfl⟩
  have hsK : convexHull ℝ (s.1 : Set Ea) ⊆ 𝒦.complex.space :=
    𝒦.complex.convexHull_subset_space s.2.1
  have hbad : IsClosed (convexHull ℝ (s.1 : Set Ea) ∩ (fun z => h (𝒦.map z)) ⁻¹'
      (interior (section34FaceTorus (section34VertexBallImage src f₁) s))ᶜ) :=
    (hΦ.mono hsK).preimage_isClosed_of_isClosed
      (s.1.finite_toSet.isCompact_convexHull (𝕜 := ℝ)).isClosed isOpen_interior.isClosed_compl
  have hDO : D ⊆ (convexHull ℝ (s.1 : Set Ea) ∩ (fun z => h (𝒦.map z)) ⁻¹'
      (interior (section34FaceTorus (section34VertexBallImage src f₁) s))ᶜ)ᶜ := by
    rintro z hz ⟨hzs, hzT⟩
    exact hzT (hrim s (hDs z hz hzs))
  obtain ⟨B', hB', hDB', hB'O, -⟩ :=
    𝒦.exists_isPLBall_nhdsWithin_space_of_isPLBall_two hK hD hD𝒦 hbad.isOpen_compl hDO
  have hB'K : B' ⊆ 𝒦.complex.space := fun z hz => (hB'O hz).1
  refine ⟨(fun z => h (𝒦.map z)) '' B', hB'.isPolyhedron.isCompact.image_of_continuousOn
    (hΦ.mono hB'K), ?_, ?_, ?_⟩
  · obtain ⟨r, hr⟩ := hB'
    have hmaps : ∀ x : Convexity.StdSimplex.coordinateSet ℝ (Fin (3 + 1)),
        h (𝒦.map (r x)) ∈ (fun z => h (𝒦.map z)) '' B' :=
      fun x => ⟨r x, hr.bijOn.mapsTo x.2, rfl⟩
    let f : Convexity.StdSimplex.coordinateSet ℝ (Fin (3 + 1)) → (fun z => h (𝒦.map z)) '' B' :=
      fun x => ⟨h (𝒦.map (r x)), hmaps x⟩
    have hcont : Continuous f :=
      ((hΦ.mono hB'K).comp hr.isPiecewiseAffineOn.continuousOn hr.bijOn.mapsTo).comp_continuous
        continuous_subtype_val (fun x => x.2) |>.subtype_mk _
    have hinj : Function.Injective f := by
      intro x y hxy
      have h1 : h (𝒦.map (r x)) = h (𝒦.map (r y)) := congrArg Subtype.val hxy
      have h2 := hΦinj (hB'K (hr.bijOn.mapsTo x.2)) (hB'K (hr.bijOn.mapsTo y.2)) h1
      exact Subtype.ext (hr.bijOn.injOn x.2 y.2 h2)
    have hsurj : Function.Surjective f := by
      rintro ⟨_, z, hz, rfl⟩
      obtain ⟨x, hx, rfl⟩ := hr.bijOn.surjOn hz
      exact ⟨⟨x, hx⟩, rfl⟩
    have : CompactSpace (Convexity.StdSimplex.coordinateSet ℝ (Fin (3 + 1))) :=
      isCompact_iff_compactSpace.mp (Convexity.StdSimplex.isCompact_coordinateSet ℝ (Fin (3 + 1)))
    let Φ := Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f ⟨hinj, hsurj⟩) hcont
    have : ContractibleSpace (Convexity.StdSimplex.coordinateSet ℝ (Fin (3 + 1))) :=
      (Convexity.StdSimplex.convex_coordinateSet ℝ (Fin (3 + 1))).contractibleSpace
        ⟨_, Convexity.StdSimplex.single_mem_coordinateSet ℝ (0 : Fin (3 + 1))⟩
    have : ContractibleSpace ((fun z => h (𝒦.map z)) '' B') := Φ.symm.contractibleSpace
    exact integralSingularHomology_subsingleton_of_contractible 1 one_ne_zero _
  · rintro _ ⟨_, hm, rfl⟩
    obtain ⟨τ, hτ, z, hz, rfl⟩ := mem_iUnion₂.mp hm
    exact ⟨z, hDB' (hrimD τ hτ hz), rfl⟩
  · rw [Set.disjoint_left]
    rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩ ⟨⟨z', hz', hzz'⟩, hnT⟩
    have hzeq : z' = z := hΦinj (hB'K hz') (hsK hz) hzz'
    rw [hzeq] at hz'
    exact (hB'O hz').2 ⟨hz, hnT⟩

end Frames

end DifferentialGeometry.Topology.PiecewiseLinear
