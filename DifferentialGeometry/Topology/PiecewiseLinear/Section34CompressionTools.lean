/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CompressionDiskNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.ProperDiskCompression
import DifferentialGeometry.Topology.PiecewiseLinear.Section34FaceBallUpdate
import DifferentialGeometry.Topology.PiecewiseLinear.Section34FaceBalls
import DifferentialGeometry.Topology.PiecewiseLinear.TorusSubsurfaceCarrier

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)

section Chart

theorem IsPLBall.exists_compression_trace {P D Θ Sph O E K : Set E3} (hP : IsPLBall 3 P)
    {q : (Fin 3 → ℝ) → E3} (hq : IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D) (hDP : D ⊆ P)
    (htrace : D ∩ frontier P = q '' stdSimplexBoundary 2) (hSph : IsPLSphere 2 Sph)
    (hDSph : D ⊆ Sph) (hO : IsOpen O) (hDO : D ⊆ O) (hOΘ : O ∩ Θ = O ∩ Sph)
    (hcross : ∀ x ∈ q '' stdSimplexBoundary 2, HasPLCrossingAt (frontier P) Θ x)
    (hE : IsClosed E) (hDE : Disjoint D E) (hK : IsCompact K) (hKc : IsPreconnected K)
    (hKP : K ⊆ interior P) (hKD : Disjoint K D) :
    ∃ P' Oc : Set E3, IsPLBall 3 P' ∧ P' ⊆ P ∧ K ⊆ interior P' ∧ Disjoint P' D ∧ IsOpen Oc ∧
      frontier P' ∩ Oc = frontier P ∩ Oc ∧ frontier P' ∩ Θ ⊆ Oc ∧ frontier P' ∩ E ⊆ Oc ∧
      frontier P' ∩ Θ = frontier P ∩ Θ ∩ P' := by
  obtain ⟨Uo, hUo, hDUo, hUoΘ⟩ :=
    exists_isOpen_inter_inter_subset_of_isPLSphere hP hq hDP htrace hSph hDSph hO hDO hOΘ hcross
  obtain ⟨P', Oc, hP'b, hP'P, hKP', hP'D, hOc, hP'O, hfrP'⟩ :=
    hP.exists_compression_of_proper_disk hq hDP htrace hK hKc hKP hKD (hUo.inter hE.isOpen_compl)
      fun x hx => ⟨hDUo hx, Set.disjoint_left.mp hDE hx⟩
  have hP'c : IsClosed P' := hP'b.isPolyhedron.isClosed
  have hfrP'P' : frontier P' ⊆ P' := hP'c.frontier_subset
  have hfrO : frontier P' ∩ Oc = frontier P ∩ Oc := by
    rw [← frontier_inter_open_inter hOc, hP'O, frontier_inter_open_inter hOc]
  have hk2 : frontier P' ∩ Θ ⊆ Oc := by
    rintro x ⟨hx, hxΘ⟩
    by_contra hxO
    have hxU := (hfrP' ⟨hx, hxO⟩).1
    exact Set.disjoint_left.mp hP'D (hfrP'P' hx) (hUoΘ ⟨⟨hxU, hxΘ⟩, hP'P (hfrP'P' hx)⟩)
  refine ⟨P', Oc, hP'b, hP'P, hKP', hP'D, hOc, hfrO, hk2, ?_, ?_⟩
  · rintro x ⟨hx, hxE⟩
    by_contra hxO
    exact (hfrP' ⟨hx, hxO⟩).2 hxE
  · apply Subset.antisymm
    · rintro x ⟨hx, hxΘ⟩
      have hx' : x ∈ frontier P ∩ Oc := by
        rw [← hfrO]
        exact ⟨hx, hk2 ⟨hx, hxΘ⟩⟩
      exact ⟨⟨hx'.1, hxΘ⟩, hfrP'P' hx⟩
    · rintro x ⟨⟨hx, hxΘ⟩, hxP'⟩
      refine ⟨?_, hxΘ⟩
      rw [hP'c.frontier_eq]
      exact ⟨hxP', fun hxi => hx.2 (interior_mono hP'P hxi)⟩

end Chart

section Torus

variable {Y : Type u} [TopologicalSpace Y] [T2Space Y] {φ : E3 → Y} {S : Set Y}

theorem IsPLTorus.carriesFirstHomologyOnto_image_inter_of_isClopen {ι : Type*} [Finite ι]
    {Θ Z P' Oc : Set E3} {C : ι → Set E3} (hΘ : IsPLTorus Θ) (hC : ∀ i, IsPLSphere 1 (C i))
    (hCd : Pairwise fun i j => Disjoint (C i) (C j)) (hZ : Z = ⋃ i, C i) (hZΘ : Z ⊆ Θ)
    (hP'c : IsClosed P') (hOc : IsOpen Oc) (hZP' : Z ∩ P' = Z ∩ Oc)
    (hfr : ∀ x ∈ P' ∩ Θ, x ∉ interior P' → x ∈ Z) (hφ : ContinuousOn φ Θ) (hφi : InjOn φ Θ)
    (hS : φ '' Θ ⊆ S) (hZS : CarriesFirstHomologyOnto (φ '' Z) S)
    (hWS : CarriesFirstHomologyOnto (φ '' (P' ∩ Θ)) S) :
    CarriesFirstHomologyOnto (φ '' (Z ∩ P')) S := by
  have hCsub : ∀ i, C i ⊆ Z := fun i => by
    rw [hZ]
    exact subset_iUnion C i
  have hCΘ : ∀ i, C i ⊆ Θ := fun i => (hCsub i).trans hZΘ
  have hsub : φ '' (Z ∩ P') ⊆ S := (image_mono (inter_subset_left.trans hZΘ)).trans hS
  have hCsplit : ∀ i, C i ⊆ P' ∨ Disjoint (C i) P' := by
    intro i
    have hpc : IsPreconnected (C i) := (hC i).isConnected.isPreconnected
    have hin : ∀ x ∈ C i, x ∈ Oc → x ∈ P' := fun x hx hxO => by
      have h1 : x ∈ Z ∩ Oc := ⟨hCsub i hx, hxO⟩
      rw [← hZP'] at h1
      exact h1.2
    have hout : ∀ x ∈ C i, x ∈ P' → x ∈ Oc := fun x hx hxP' => by
      have h1 : x ∈ Z ∩ P' := ⟨hCsub i hx, hxP'⟩
      rw [hZP'] at h1
      exact h1.2
    have hcover : C i ⊆ Oc ∪ P'ᶜ := by
      intro x hx
      by_cases hxP' : x ∈ P'
      · exact Or.inl (hout x hx hxP')
      · exact Or.inr hxP'
    have hdisj : C i ∩ (Oc ∩ P'ᶜ) = ∅ :=
      eq_empty_iff_forall_notMem.mpr fun x ⟨hx, hxO, hxP'⟩ => hxP' (hin x hx hxO)
    rcases isPreconnected_iff_subset_of_disjoint.mp hpc Oc P'ᶜ hOc hP'c.isOpen_compl hcover
      hdisj with h1 | h1
    · exact Or.inl fun x hx => hin x hx (h1 hx)
    · exact Or.inr (Set.disjoint_left.mpr fun x hx hxP' => h1 hx hxP')
  have hZP'eq : Z ∩ P' = ⋃ j : {j // C j ⊆ P'}, C j.1 := by
    apply Subset.antisymm
    · rintro x ⟨hxZ, hxP'⟩
      rw [hZ] at hxZ
      obtain ⟨j, hxj⟩ := mem_iUnion.mp hxZ
      rcases hCsplit j with hjP' | hjP'
      · exact mem_iUnion.mpr ⟨⟨j, hjP'⟩, hxj⟩
      · exact absurd hxP' (Set.disjoint_left.mp hjP' hxj)
    · exact iUnion_subset fun j x hx => ⟨hCsub j.1 hx, j.2 hx⟩
  have hZS' : CarriesFirstHomologyOnto (φ '' ⋃ i, C i) S := by
    rw [← hZ]
    exact hZS
  rcases hΘ.carriesFirstHomologyOnto_or_subsingleton_of_iUnion hC hCΘ hCd hφ hφi hS hZS'
    with ⟨i, hisep, hicarry⟩ | hsing
  · rcases hCsplit i with hiP' | hiP'
    · exact hicarry.mono (image_mono fun x hx => ⟨hCsub i hx, hiP' hx⟩) hsub
    · have hCne : ∀ j : {j // C j ⊆ P'}, j.1 ≠ i := by
        intro j hji
        obtain ⟨x, hx⟩ := (hC j.1).nonempty
        exact Set.disjoint_left.mp hiP' (hji ▸ hx) (j.2 hx)
      have hWfr : P' ∩ Θ ∩ closure (Θ \ (P' ∩ Θ)) ⊆ ⋃ j : {j // C j ⊆ P'}, C j.1 := by
        rintro x ⟨⟨hxP', hxΘ⟩, hxcl⟩
        have hxi : x ∉ interior P' := by
          have hsub' : Θ \ (P' ∩ Θ) ⊆ P'ᶜ := fun z hz hzP' => hz.2 ⟨hzP', hz.1⟩
          have h1 : x ∈ closure P'ᶜ := closure_mono hsub' hxcl
          rw [closure_compl] at h1
          exact h1
        rw [← hZP'eq]
        exact ⟨hfr x ⟨hxP', hxΘ⟩ hxi, hxP'⟩
      have hres := hΘ.carriesFirstHomologyOnto_iUnion_of_disjoint
        (C := fun j : {j // C j ⊆ P'} => C j.1) (hC i) (hCΘ i) hisep (fun j => hC j.1)
        (fun j => hCΘ j.1) (fun j j' hjj' => hCd fun h1 => hjj' (Subtype.ext h1))
        (fun j => hCd (hCne j)) inter_subset_right (hP'c.inter hΘ.1.isClosed)
        (Set.disjoint_left.mpr fun x hx hxi => Set.disjoint_left.mp hiP' hxi hx.1)
        hWfr hφ hφi hS hWS
      rw [hZP'eq]
      exact hres
  · exact carriesFirstHomologyOnto_of_subsingleton hsub hsing

end Torus

section Setup

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
  {U W : Set M₁} {h : M₁ → M₂} {η ψ : M₁ → ℝ} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁} {H : Finset Ea → Set M₂}
  {cr : Section34VertexIndex 𝒦 𝒦' → Finset Ea} {f₁ : M₁ → M₂}

omit [FiniteDimensional ℝ Ea] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂] in
theorem finite_setOf_section34Incident_graphIndex
    (hsub : IsSubdivision 𝒦'.complex 𝒦.complex) (Γ : Set M₁) (k : ℕ) {σ : Finset Ea}
    (hσ : σ ∈ 𝒦.complex.faces) :
    {w : Section34GraphIndex 𝒦' Γ k | Section34Incident w.1 σ}.Finite := by
  have hσK : convexHull ℝ (σ : Set Ea) ⊆ 𝒦'.complex.space := by
    rw [hsub.space_eq]
    exact 𝒦.complex.convexHull_subset_space hσ
  refine Set.Finite.of_finite_image (f := fun w : Section34GraphIndex 𝒦' Γ k => w.1)
    ((𝒦'.finite_faces_inter_of_isCompact (σ.finite_toSet.isCompact_convexHull (𝕜 := ℝ))
      hσK).subset ?_) Subtype.val_injective.injOn
  rintro _ ⟨w, hw, rfl⟩
  obtain ⟨q, hq⟩ := 𝒦'.complex.nonempty_of_mem_faces w.2.1
  exact ⟨w.2.1, q, subset_convexHull ℝ _ (Finset.mem_coe.mpr hq), hw (Finset.mem_coe.mpr hq)⟩

theorem exists_chart_section34FaceBall (hh : IsEmbedding (U.domRestrict h))
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd) (hctrl : Section34CarrierControl U 𝒦 h η H)
    (hgraph : Section34GraphFrame U W h ψ H 𝒦 𝒦' src cr f₁)
    {fbl : Section34SimplexIndex 𝒦 3 → Set M₂}
    (hext : Section34Exterior 𝒦 𝒦' h H (section34VertexBallImage src f₁) fbl)
    (s : Section34SimplexIndex 𝒦 3)
    (hfV : ∀ w : Section34VertexIndex 𝒦 𝒦', ¬ Section34Incident w.1 s.1 →
      fbl s ∩ section34VertexBallImage src f₁ w = ∅) :
    ∃ c ∈ (plGroupoid 3).maximalAtlas M₂, fbl s ⊆ c.source ∧
      section34FaceTorus (section34VertexBallImage src f₁) s ⊆ c.source ∧
      IsCompact (section34FaceTorus (section34VertexBallImage src f₁) s) ∧
      ∃ O₀ : Set M₂, IsOpen O₀ ∧ fbl s ⊆ O₀ ∧
        frontier (⋃ w, section34VertexBallImage src f₁ w) ∩ O₀ =
          frontier (section34FaceTorus (section34VertexBallImage src f₁) s) ∩ O₀ := by
  obtain ⟨hext1, -, -⟩ := hext
  obtain ⟨-, hsubdiv, -, hcell, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    hcof⟩ := id hcut
  obtain ⟨-, -, hf₁, -, -, -, -, -, -, -, -, -, -, -⟩ := id hgraph
  obtain ⟨-, -, -, -, -, hchart⟩ := id hctrl
  obtain ⟨t, hst⟩ := hcof s
  obtain ⟨c, hc, hHc⟩ := hchart t.1 t.2.1
  have hNV : ∀ v : Section34VertexIndex 𝒦 𝒦',
      src (.vertexBall v) ⊆ section34CutNeighborhood src :=
    fun v => subset_iUnion (fun v => src (Section34Label.vertexBall v)) v
  have hVcell : ∀ w' : Section34VertexIndex 𝒦 𝒦',
      IsPLCellOn 3 (section34VertexBallImage src f₁ w') (section34VertexBallImage srcBd f₁ w') :=
    fun w' => (hcell (.vertexBall w')).image
      (hf₁.mono_of_isPLCellOn (hcell (.vertexBall w')) (hNV w'))
  have hVt : ∀ w' : Section34VertexIndex 𝒦 𝒦', Section34Incident w'.1 s.1 →
      section34VertexBallImage src f₁ w' ⊆ interior (H t.1) := fun w' hw =>
    image_vertexBall_subset_interior_of_incident hh hcut hctrl hgraph w' t.2.1
      (Subset.trans hw (convexHull_min hst (convex_convexHull ℝ _)))
  have hTeq : section34FaceTorus (section34VertexBallImage src f₁) s =
      ⋃ w' ∈ {w' : Section34VertexIndex 𝒦 𝒦' | Section34Incident w'.1 s.1},
        section34VertexBallImage src f₁ w' := by
    apply Subset.antisymm
    · intro z hz
      obtain ⟨a, ha, hza⟩ := mem_iUnion₂.mp hz
      have hia : Section34Incident a.1.2.1 s.1 := by
        rw [← ha]
        exact a.2
      exact mem_iUnion₂.mpr ⟨a.1.2, hia, hza⟩
    · exact iUnion₂_subset fun w' hw' z hz => mem_iUnion₂.mpr ⟨⟨(s, w'), hw'⟩, rfl, hz⟩
  have hfsH : fbl s ⊆ interior (H t.1) := by
    refine Subset.trans ?_ (hext1 t)
    unfold section34TetraObstacle
    exact subset_union_of_subset_right
      (subset_iUnion₂ (s := fun s' (_ : Section34Incident s'.1 t.1) => fbl s') s hst) _
  have hTH : section34FaceTorus (section34VertexBallImage src f₁) s ⊆ interior (H t.1) := by
    rw [hTeq]
    exact iUnion₂_subset fun w' hw' => hVt w' hw'
  have hQc : IsClosed (⋃ w' ∈ {w' : Section34VertexIndex 𝒦 𝒦' |
      (section34VertexBallImage src f₁ w' ∩ H t.1).Nonempty ∧ ¬ Section34Incident w'.1 s.1},
      section34VertexBallImage src f₁ w') :=
    ((finite_setOf_vertexBallImage_inter_nonempty hctrl hgraph t.2.1).subset
      fun w' hw' => hw'.1).isClosed_biUnion fun w' _ => (hVcell w').isCompact.isClosed
  have hO₀o := isOpen_interior (s := H t.1) |>.sdiff hQc
  have hUO₀ : ∀ Y : Set M₂, Y = interior (H t.1) \ ⋃ w' ∈ {w' : Section34VertexIndex 𝒦 𝒦' |
      (section34VertexBallImage src f₁ w' ∩ H t.1).Nonempty ∧ ¬ Section34Incident w'.1 s.1},
      section34VertexBallImage src f₁ w' →
      (⋃ w', section34VertexBallImage src f₁ w') ∩ Y =
        section34FaceTorus (section34VertexBallImage src f₁) s ∩ Y := by
    rintro Y rfl
    apply Subset.antisymm
    · rintro z ⟨hz, hzH, hzQ⟩
      obtain ⟨w', hzw'⟩ := mem_iUnion.mp hz
      by_cases hw' : Section34Incident w'.1 s.1
      · exact ⟨mem_iUnion₂.mpr ⟨⟨(s, w'), hw'⟩, rfl, hzw'⟩, hzH, hzQ⟩
      · exact absurd (mem_iUnion₂.mpr ⟨w', ⟨⟨z, hzw', interior_subset hzH⟩, hw'⟩, hzw'⟩) hzQ
    · rintro z ⟨hz, hzO⟩
      obtain ⟨a, -, hza⟩ := mem_iUnion₂.mp hz
      exact ⟨mem_iUnion.mpr ⟨a.1.2, hza⟩, hzO⟩
  refine ⟨c, hc, hfsH.trans (interior_subset.trans hHc),
    hTH.trans (interior_subset.trans hHc), ?_, _, hO₀o, ?_, ?_⟩
  · rw [hTeq]
    exact (finite_setOf_section34Incident_graphIndex hsubdiv _ 1 s.2.1).isCompact_biUnion
      fun w' _ => (hVcell w').isCompact
  · intro z hz
    refine ⟨hfsH hz, fun hzQ => ?_⟩
    obtain ⟨w', ⟨-, hw'⟩, hzw'⟩ := mem_iUnion₂.mp hzQ
    have hmem : z ∈ fbl s ∩ section34VertexBallImage src f₁ w' := ⟨hz, hzw'⟩
    rw [hfV w' hw'] at hmem
    exact hmem
  · rw [← frontier_inter_open_inter hO₀o, hUO₀ _ rfl, frontier_inter_open_inter hO₀o]

end Setup

section Fields

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
  {U : Set M₁} {h : M₁ → M₂} {H : Finset Ea → Set M₂} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}

theorem section34FaceBall_fields_of_inter_eq
    {tgtV : Section34VertexIndex 𝒦 𝒦' → Set M₂} {tgtEBd : Section34EdgeIndex 𝒦 𝒦' → Set M₂}
    {fbl fblBd : Section34SimplexIndex 𝒦 3 → Set M₂}
    (hinv : Section34FaceBallInvariants 𝒦 𝒦' h H tgtV tgtEBd fbl fblBd)
    {s : Section34SimplexIndex 𝒦 3} {F Fb OM : Set M₂} (hOM : IsOpen OM) (hF : IsClosed F)
    (hFbO : Fb ∩ OM = fblBd s ∩ OM) (hZO : Fb ∩ frontier (⋃ w, tgtV w) ⊆ OM)
    (hEO : ∀ e, Fb ∩ tgtEBd e ⊆ OM)
    (hZF : Fb ∩ frontier (⋃ w, tgtV w) = fblBd s ∩ frontier (⋃ w, tgtV w) ∩ F)
    {y₀ : M₂} (hy₀ : y₀ ∈ fblBd s ∩ frontier (⋃ w, tgtV w)) (hy₀F : y₀ ∉ F) :
    (∀ y ∈ Fb ∩ frontier (⋃ w, tgtV w), ∃ c ∈ (plGroupoid 3).maximalAtlas M₂,
      y ∈ c.source ∧ HasPLCrossingAt (c '' (Fb ∩ c.source))
        (c '' (frontier (⋃ w, tgtV w) ∩ c.source)) (c y)) ∧
    (∀ e : Section34EdgeIndex 𝒦 𝒦', ∀ y ∈ Fb ∩ tgtEBd e,
      ∃ c ∈ (plGroupoid 3).maximalAtlas M₂, y ∈ c.source ∧
        HasPLCurveCrossingOnAt (c '' (frontier (⋃ w, tgtV w) ∩ c.source))
          (c '' (Fb ∩ frontier (⋃ w, tgtV w) ∩ c.source)) (c '' (tgtEBd e ∩ c.source)) (c y)) ∧
    (Fb ∩ ⋃ e : Section34EdgeIndex 𝒦 𝒦', tgtEBd e).Finite ∧
    ((fun y => connectedComponentIn (Fb ∩ frontier (⋃ w, tgtV w)) y) ''
      (Fb ∩ frontier (⋃ w, tgtV w))).Finite ∧
    ((fun y => connectedComponentIn (Fb ∩ frontier (⋃ w, tgtV w)) y) ''
      (Fb ∩ frontier (⋃ w, tgtV w))).ncard + 1 ≤
      ((fun y => connectedComponentIn (fblBd s ∩ frontier (⋃ w, tgtV w)) y) ''
        (fblBd s ∩ frontier (⋃ w, tgtV w))).ncard ∧
    (Fb ∩ ⋃ e : Section34EdgeIndex 𝒦 𝒦', tgtEBd e).ncard ≤
      (fblBd s ∩ ⋃ e : Section34EdgeIndex 𝒦 𝒦', tgtEBd e).ncard := by
  obtain ⟨-, -, -, -, hf5, hf6, -, hf8, hf9, -⟩ := hinv
  have hZ'O : Fb ∩ frontier (⋃ w, tgtV w) = fblBd s ∩ frontier (⋃ w, tgtV w) ∩ OM := by
    ext y
    constructor
    · intro hy
      have h1 : y ∈ Fb ∩ OM := ⟨hy.1, hZO hy⟩
      rw [hFbO] at h1
      exact ⟨⟨h1.1, hy.2⟩, h1.2⟩
    · rintro ⟨⟨hy, hySg⟩, hyOM⟩
      have h1 : y ∈ fblBd s ∩ OM := ⟨hy, hyOM⟩
      rw [← hFbO] at h1
      exact ⟨h1.1, hySg⟩
  have hy₀' : y₀ ∉ Fb ∩ frontier (⋃ w, tgtV w) := fun hy => by
    rw [hZF] at hy
    exact hy₀F hy.2
  have hsub := image_connectedComponentIn_subset_diff hOM hF hZ'O hZF hy₀ hy₀'
  have h8sub : Fb ∩ ⋃ e : Section34EdgeIndex 𝒦 𝒦', tgtEBd e ⊆
      fblBd s ∩ ⋃ e : Section34EdgeIndex 𝒦 𝒦', tgtEBd e := by
    rintro y ⟨hy, hyE⟩
    obtain ⟨e, hye⟩ := mem_iUnion.mp hyE
    have h1 : y ∈ Fb ∩ OM := ⟨hy, hEO e ⟨hy, hye⟩⟩
    rw [hFbO] at h1
    exact ⟨h1.1, hyE⟩
  refine ⟨fun y hy => ?_, fun e y hy => ?_, (hf8 s).subset h8sub,
    (hf9 s).subset (hsub.trans sdiff_subset),
    ncard_image_connectedComponentIn_add_one_le hOM hF hZ'O hZF hy₀ hy₀' (hf9 s),
    Set.ncard_le_ncard h8sub (hf8 s)⟩
  · have hy' := (Set.ext_iff.mp hZ'O y).mp hy
    obtain ⟨c, hc, hyc, hcr⟩ := hf5 s y hy'.1
    exact ⟨c, hc, hyc, hcr.congr (eventually_mem_image_inter_source_iff hOM hFbO.symm hy'.2 hyc)
      (Filter.Eventually.of_forall fun _ => Iff.rfl)⟩
  · have hyOM := hEO e hy
    have hyb : y ∈ fblBd s := by
      have h1 : y ∈ Fb ∩ OM := ⟨hy.1, hyOM⟩
      rw [hFbO] at h1
      exact h1.1
    obtain ⟨c, hc, hyc, hcr⟩ := hf6 s e y ⟨hyb, hy.2⟩
    refine ⟨c, hc, hyc, hcr.congr (Filter.Eventually.of_forall fun _ => Iff.rfl) ?_
      (Filter.Eventually.of_forall fun _ => Iff.rfl)⟩
    refine eventually_mem_image_inter_source_iff hOM ?_ hyOM hyc
    rw [inter_right_comm, ← hFbO, inter_right_comm]

end Fields

end DifferentialGeometry.Topology.PiecewiseLinear
