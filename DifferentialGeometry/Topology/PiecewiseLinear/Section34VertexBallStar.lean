/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LinkDimension
import DifferentialGeometry.Topology.PiecewiseLinear.LocallyFiniteSplittingDisks
import DifferentialGeometry.Topology.PiecewiseLinear.OpenStar
import DifferentialGeometry.Topology.PiecewiseLinear.Section34FaceBallVocabulary

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

section OpenStar

variable {Ea : Type*} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {X : Type*} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] {U : Set X}

theorem LocallyFinitePLPieceIn.isClosed_preimage_avoidingUnion
    (𝒦 : LocallyFinitePLPieceIn Ea 3 X U) (a : Ea) :
    IsClosed ((Subtype.val : 𝒦.complex.space → Ea) ⁻¹' avoidingUnion 𝒦.complex a) := by
  let F : 𝒦.complex.faces → Set 𝒦.complex.space := fun s =>
    {z | a ∉ (s : Finset Ea) ∧ (z : Ea) ∈ convexHull ℝ ((s : Finset Ea) : Set Ea)}
  have hF : LocallyFinite F := 𝒦.locallyFinite.subset fun s z hz => hz.2
  have hFc : ∀ s, IsClosed (F s) := by
    intro s
    by_cases has : a ∈ (s : Finset Ea)
    · have hempty : F s = ∅ := eq_empty_of_forall_notMem fun z hz => hz.1 has
      rw [hempty]
      exact isClosed_empty
    · have heq : F s = (Subtype.val : 𝒦.complex.space → Ea) ⁻¹'
          convexHull ℝ ((s : Finset Ea) : Set Ea) := by
        ext z
        exact ⟨fun hz => hz.2, fun hz => ⟨has, hz⟩⟩
      rw [heq]
      exact ((s : Finset Ea).finite_toSet.isCompact_convexHull ℝ).isClosed.preimage
        continuous_subtype_val
  have heq : (Subtype.val : 𝒦.complex.space → Ea) ⁻¹' avoidingUnion 𝒦.complex a = ⋃ s, F s := by
    ext z
    simp only [avoidingUnion, mem_preimage, mem_iUnion]
    constructor
    · rintro ⟨t, ⟨ht, hat⟩, hzt⟩
      exact ⟨⟨t, ht⟩, hat, hzt⟩
    · rintro ⟨⟨t, ht⟩, hat, hzt⟩
      exact ⟨t, ⟨ht, hat⟩, hzt⟩
  rw [heq]
  exact hF.isClosed_iUnion hFc

theorem LocallyFinitePLPieceIn.subset_openStar_of_isPreconnected [FiniteDimensional ℝ Ea]
    (𝒦 : LocallyFinitePLPieceIn Ea 3 X U) (hK : IsCombinatorialManifold 3 𝒦.complex) {a : Ea}
    (ha : ({a} : Finset Ea) ∈ 𝒦.complex.faces) {Y : Set Ea} (hY : IsPreconnected Y)
    (hY𝒦 : Y ⊆ 𝒦.complex.space) (hYa : (Y ∩ openStar 𝒦.complex a).Nonempty)
    (hYs : ∀ s ∈ 𝒦.complex.faces, s.card = 3 → a ∉ s →
      Disjoint Y (convexHull ℝ (s : Set Ea))) :
    Y ⊆ openStar 𝒦.complex a := by
  classical
  let Y' : Set 𝒦.complex.space := Subtype.val ⁻¹' Y
  have hY' : IsPreconnected Y' := by
    rw [← IsInducing.subtypeVal.isPreconnected_image, Subtype.image_preimage_coe,
      inter_eq_right.mpr hY𝒦]
    exact hY
  let u : Set 𝒦.complex.space := (Subtype.val ⁻¹' avoidingUnion 𝒦.complex a)ᶜ
  have hu : IsOpen u := (𝒦.isClosed_preimage_avoidingUnion a).isOpen_compl
  let C : Set 𝒦.complex.space :=
    {z | ∃ t ∈ 𝒦.complex.faces, a ∈ t ∧ (z : Ea) ∈ convexHull ℝ (t : Set Ea)}
  have hC : IsClosed C := by
    let G : 𝒦.complex.faces → Set 𝒦.complex.space := fun s =>
      {z | a ∈ (s : Finset Ea) ∧ (z : Ea) ∈ convexHull ℝ ((s : Finset Ea) : Set Ea)}
    have hG : LocallyFinite G := 𝒦.locallyFinite.subset fun s z hz => hz.2
    have hGc : ∀ s, IsClosed (G s) := by
      intro s
      by_cases has : a ∈ (s : Finset Ea)
      · have heq : G s = (Subtype.val : 𝒦.complex.space → Ea) ⁻¹'
            convexHull ℝ ((s : Finset Ea) : Set Ea) := by
          ext z
          exact ⟨fun hz => hz.2, fun hz => ⟨has, hz⟩⟩
        rw [heq]
        exact ((s : Finset Ea).finite_toSet.isCompact_convexHull ℝ).isClosed.preimage
          continuous_subtype_val
      · have hempty : G s = ∅ := eq_empty_of_forall_notMem fun z hz => has hz.1
        rw [hempty]
        exact isClosed_empty
    have heq : C = ⋃ s, G s := by
      ext z
      simp only [C, G, mem_ofPred_eq, mem_iUnion]
      constructor
      · rintro ⟨t, ht, hat, hzt⟩
        exact ⟨⟨t, ht⟩, hat, hzt⟩
      · rintro ⟨⟨t, ht⟩, hat, hzt⟩
        exact ⟨t, ht, hat, hzt⟩
    rw [heq]
    exact hG.isClosed_iUnion hGc
  have huC : u ⊆ C := by
    intro z hz
    obtain ⟨t, ht, hzt⟩ := exists_face_mem_openSimplex 𝒦.complex z.2
    by_cases hat : a ∈ t
    · exact ⟨t, ht, hat, openSimplex_subset_convexHull t hzt⟩
    · exact absurd (mem_iUnion₂.mpr ⟨t, ⟨ht, hat⟩, openSimplex_subset_convexHull t hzt⟩) hz
  have hclosure : closure u ∩ Y' ⊆ u := by
    rintro z ⟨hzu, hzY⟩
    by_contra hzn
    have hzA : (z : Ea) ∈ avoidingUnion 𝒦.complex a := not_not.mp hzn
    obtain ⟨t, ht, hat, hzt⟩ := closure_minimal huC hC hzu
    obtain ⟨σ, ⟨hσ, haσ⟩, hzσ⟩ := mem_iUnion₂.mp hzA
    obtain ⟨ρ, hρ, hzρ⟩ := exists_face_mem_openSimplex 𝒦.complex z.2
    have hρt : ρ ⊆ t := face_subset_of_mem_openSimplex_of_mem_convexHull _ hρ ht hzρ hzt
    have hρσ : ρ ⊆ σ := face_subset_of_mem_openSimplex_of_mem_convexHull _ hρ hσ hzρ hzσ
    have haρ : a ∉ ρ := fun h => haσ (hρσ h)
    have hins : insert a ρ ∈ 𝒦.complex.faces :=
      𝒦.complex.down_closed ht (Finset.insert_subset hat hρt) (Finset.insert_nonempty a ρ)
    have hρL : ρ ∈ (SimplicialComplex.geometricLink 𝒦.complex {a}).faces :=
      (SimplicialComplex.mem_geometricLink_singleton 𝒦.complex a ρ).mpr
        ⟨𝒦.complex.nonempty_of_mem_faces hρ, haρ, hins⟩
    have : Finite (SimplicialComplex.geometricLink 𝒦.complex {a}).faces :=
      (𝒦.geometricLink_faces_finite ha).to_subtype
    obtain ⟨s, hsL, hρs, hs3⟩ :=
      exists_face_superset_card_eq_of_isPLSphere (n := 2) _ (hK a ha) hρL
    obtain ⟨-, has, hins'⟩ := (SimplicialComplex.mem_geometricLink_singleton 𝒦.complex a s).mp hsL
    have hsK : s ∈ 𝒦.complex.faces :=
      𝒦.complex.down_closed hins' (Finset.subset_insert a s) (Finset.card_pos.mp (by omega))
    exact disjoint_left.mp (hYs s hsK (by omega) has) hzY
      (convexHull_mono (Finset.coe_subset.mpr hρs) (openSimplex_subset_convexHull ρ hzρ))
  obtain ⟨y₀, hy₀Y, hy₀K, hy₀A⟩ := hYa
  have hsub := hY'.subset_of_closure_inter_subset hu ⟨⟨y₀, hy₀K⟩, hy₀Y, hy₀A⟩ hclosure
  intro y hy
  exact ⟨hY𝒦 hy, hsub (show (⟨y, hY𝒦 hy⟩ : 𝒦.complex.space) ∈ Y' from hy)⟩

end OpenStar

theorem IsPLCellOn.isConnected {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {d : ℕ} {S B : Set M} (hS : IsPLCellOn d S B) :
    IsConnected S := by
  obtain ⟨P, r, v, hr, hv, rfl, -⟩ := hS
  have hP : IsConnected P := by
    have h1 : IsConnected (Convexity.StdSimplex.coordinateSet ℝ (Fin (d + 1))) :=
      (Convexity.StdSimplex.convex_coordinateSet ℝ _).isConnected ⟨_, Convexity.StdSimplex.single_mem_coordinateSet ℝ (0 : Fin (d + 1))⟩
    have h2 := h1.image r hr.isPiecewiseAffineOn.continuousOn
    rwa [hr.bijOn.image_eq] at h2
  exact hP.image v hv.continuousOn

section Frames

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
  {U W : Set M₁} {h : M₁ → M₂} {η ψ : M₁ → ℝ} {H : Finset Ea → Set M₂}
  {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U} {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁}
  {cr : Section34VertexIndex 𝒦 𝒦' → Finset Ea} {f₁ : M₁ → M₂}

omit [FiniteDimensional ℝ Ea] in
theorem image_openStar_subset_section34CarrierSupport {a : Ea} {t : Finset Ea} (hat : a ∈ t) :
    𝒦.map '' openStar 𝒦.complex a ⊆ Section34CarrierSupport 𝒦 t := by
  rintro _ ⟨z, ⟨hzK, hzA⟩, rfl⟩
  obtain ⟨τ, hτ, hzτ⟩ := exists_face_mem_openSimplex 𝒦.complex hzK
  have haτ : a ∈ τ := by
    by_contra haτ
    exact hzA (mem_iUnion₂.mpr ⟨τ, ⟨hτ, haτ⟩, openSimplex_subset_convexHull τ hzτ⟩)
  simp only [Section34CarrierSupport, mem_iUnion₂]
  exact ⟨a, hat, τ, ⟨hτ, haτ⟩, z, openSimplex_subset_convexHull τ hzτ, rfl⟩

theorem image_vertexBall_subset_image_openStar (hh : IsEmbedding (U.domRestrict h))
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd) (hctrl : Section34CarrierControl U 𝒦 h η H)
    (hgraph : Section34GraphFrame U W h ψ H 𝒦 𝒦' src cr f₁) (w : Section34VertexIndex 𝒦 𝒦')
    {a : Ea} (ha : ({a} : Finset Ea) ∈ 𝒦.complex.faces)
    (hwa : (w.1 : Set Ea) ⊆ openStar 𝒦.complex a) :
    f₁ '' src (.vertexBall w) ⊆ h '' (𝒦.map '' openStar 𝒦.complex a) := by
  obtain ⟨hK, -, hmap, hcell, -⟩ := hcut
  obtain ⟨-, hHU, -⟩ := hctrl
  obtain ⟨-, -, hf₁, -, -, hcore, -, hvb, -, -, hcr, -, -, hsub⟩ := hgraph
  obtain ⟨p, hp⟩ := Finset.card_eq_one.mp w.2.2.1
  have hpw : p ∈ (w.1 : Set Ea) := by
    rw [hp]
    exact Finset.mem_coe.mpr (Finset.mem_singleton_self p)
  have hpa : p ∈ openStar 𝒦.complex a := hwa hpw
  have hNV : src (.vertexBall w) ⊆ section34CutNeighborhood src :=
    subset_iUnion (fun w => src (Section34Label.vertexBall w)) w
  have hVc : IsConnected (f₁ '' src (.vertexBall w)) :=
    (hcell (.vertexBall w)).isConnected.image f₁ (hf₁.continuousOn.mono hNV)
  have hVU : f₁ '' src (.vertexBall w) ⊆ h '' U := fun y hy =>
    hHU (cr w) (hcr w) (hsub w (Or.inr hy))
  let k : 𝒦.complex.space → U := fun z => ⟨𝒦.map z, 𝒦.bijOn.mapsTo z.2⟩
  have hk : IsEmbedding k := 𝒦.isEmbedding.codRestrict U fun z => 𝒦.bijOn.mapsTo z.2
  let E : 𝒦.complex.space → M₂ := U.domRestrict h ∘ k
  have hE : IsEmbedding E := hh.comp hk
  have hEz : ∀ z : 𝒦.complex.space, E z = h (𝒦.map z) := fun z => rfl
  have hrange : f₁ '' src (.vertexBall w) ⊆ range E := by
    intro y hy
    obtain ⟨x, hxU, rfl⟩ := hVU hy
    obtain ⟨z, hz, hzx⟩ := 𝒦.bijOn.surjOn hxU
    exact ⟨⟨z, hz⟩, congrArg h hzx⟩
  have hS : IsPreconnected (E ⁻¹' (f₁ '' src (.vertexBall w))) := by
    rw [← hE.isInducing.isPreconnected_image, image_preimage_eq_of_subset hrange]
    exact hVc.isPreconnected
  have hstar : Subtype.val '' (E ⁻¹' (f₁ '' src (.vertexBall w))) ⊆ openStar 𝒦.complex a := by
    refine 𝒦.subset_openStar_of_isPreconnected hK ha
      (hS.image _ continuous_subtype_val.continuousOn)
      (by rintro _ ⟨z, -, rfl⟩; exact z.2) ?_ ?_
    · have hpK : p ∈ 𝒦.complex.space := openStar_subset_space _ _ hpa
      refine ⟨p, ⟨⟨p, hpK⟩, ?_, rfl⟩, hpa⟩
      change h (𝒦.map p) ∈ f₁ '' src (.vertexBall w)
      apply interior_subset
      apply hcore w
      exact ⟨𝒦'.map p, ⟨p, subset_convexHull ℝ _ hpw, rfl⟩, by rw [hmap]⟩
    · intro s hs hs3 has
      rw [Set.disjoint_left]
      rintro _ ⟨z, hzS, rfl⟩ hzs
      have hzS' : h (𝒦.map z) ∈ f₁ '' src (.vertexBall w) := hzS
      have hinc := hvb w ⟨s, hs, hs3⟩ ⟨h (𝒦.map z), hzS', 𝒦.map z, ⟨z, hzs, rfl⟩, rfl⟩
      exact hpa.2 (mem_iUnion₂.mpr ⟨s, ⟨hs, has⟩, hinc hpw⟩)
  intro y hy
  obtain ⟨z, hzy⟩ := hrange hy
  have hzS : z ∈ E ⁻¹' (f₁ '' src (.vertexBall w)) := by
    rw [mem_preimage, hzy]
    exact hy
  exact ⟨𝒦.map z, ⟨z, hstar ⟨z, hzS, rfl⟩, rfl⟩, hzy⟩

theorem image_vertexBall_subset_interior_of_incident (hh : IsEmbedding (U.domRestrict h))
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd) (hctrl : Section34CarrierControl U 𝒦 h η H)
    (hgraph : Section34GraphFrame U W h ψ H 𝒦 𝒦' src cr f₁) (w : Section34VertexIndex 𝒦 𝒦')
    {t : Finset Ea} (ht : t ∈ 𝒦.complex.faces) (hwt : Section34Incident w.1 t) :
    f₁ '' src (.vertexBall w) ⊆ interior (H t) := by
  obtain ⟨p, hp⟩ := Finset.card_eq_one.mp w.2.2.1
  have hpw : p ∈ (w.1 : Set Ea) := by
    rw [hp]
    exact Finset.mem_coe.mpr (Finset.mem_singleton_self p)
  have hpt : p ∈ convexHull ℝ (t : Set Ea) := hwt hpw
  obtain ⟨σ, hσ, hpσ⟩ :=
    exists_face_mem_openSimplex 𝒦.complex (𝒦.complex.convexHull_subset_space ht hpt)
  have hσt : σ ⊆ t := face_subset_of_mem_openSimplex_of_mem_convexHull _ hσ ht hpσ hpt
  obtain ⟨a, haσ⟩ := 𝒦.complex.nonempty_of_mem_faces hσ
  have ha : ({a} : Finset Ea) ∈ 𝒦.complex.faces :=
    𝒦.complex.down_closed hσ (Finset.singleton_subset_iff.mpr haσ) (Finset.singleton_nonempty a)
  have hwa : (w.1 : Set Ea) ⊆ openStar 𝒦.complex a := by
    rw [hp, Finset.coe_singleton, singleton_subset_iff]
    exact ⟨𝒦.complex.convexHull_subset_space ht hpt,
      notMem_avoidingUnion_of_mem_openSimplex _ hσ hpσ haσ⟩
  have hsub := image_vertexBall_subset_image_openStar hh hcut hctrl hgraph w ha hwa
  obtain ⟨hcarrier, -⟩ := hctrl
  exact hsub.trans ((image_mono (image_openStar_subset_section34CarrierSupport (hσt haσ))).trans
    (hcarrier t ht))

theorem section34TetraObstacle_subset_interior (hh : IsEmbedding (U.domRestrict h))
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd) (hctrl : Section34CarrierControl U 𝒦 h η H)
    (hgraph : Section34GraphFrame U W h ψ H 𝒦 𝒦' src cr f₁)
    {fbl : Section34SimplexIndex 𝒦 3 → Set M₂} (t : Section34SimplexIndex 𝒦 4)
    (hfbl : ∀ s : Section34SimplexIndex 𝒦 3, Section34Incident s.1 t.1 →
      fbl s ⊆ interior (H t.1)) :
    section34TetraObstacle (section34VertexBallImage src f₁) fbl t ⊆ interior (H t.1) := by
  refine union_subset (iUnion₂_subset fun x hx => ?_) (iUnion₂_subset fun s hs => hfbl s hs)
  have hinc : Section34Incident x.1.2.1 t.1 := by
    rw [← hx]
    exact x.2
  exact image_vertexBall_subset_interior_of_incident hh hcut hctrl hgraph x.1.2 t.2.1 hinc

end Frames

end DifferentialGeometry.Topology.PiecewiseLinear
