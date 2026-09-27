import DifferentialGeometry.Topology.PiecewiseLinear.Section34SeamBicollarExtension
import DifferentialGeometry.Topology.PiecewiseLinear.AnnulusBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldSubcomplexBoundary

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_short_bicollar_image_subset_of_compact
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {S : Set X} (hS : IsCompact S) {T V O : Set Y} {d : ℝ} (hd : 0 < d)
    {f : X × ℝ → Y} (hf : ContinuousOn f (S ×ˢ Icc (-d) d))
    (hV : MapsTo f (S ×ˢ Icc (-d) d) V) (hzero : ∀ x ∈ S, f (x, 0) ∈ T)
    (hO : O ∈ 𝓝ˢ[V] T) :
    ∃ c : ℝ, 0 < c ∧ c ≤ d ∧ f '' (S ×ˢ Icc (-c) c) ⊆ O := by
  have hpre := hf.preimage_mem_nhdsSetWithin hO
  rw [show (S ×ˢ Icc (-d) d) ∩ f ⁻¹' V = S ×ˢ Icc (-d) d from
    inter_eq_left.mpr hV] at hpre
  have hcenter : S ×ˢ {(0 : ℝ)} ⊆ (S ×ˢ Icc (-d) d) ∩ f ⁻¹' T := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    have ht0 : t = 0 := ht
    subst t
    exact ⟨⟨hx, by constructor <;> linarith⟩, hzero x hx⟩
  obtain ⟨U, hU, hSU⟩ := generalized_tube_lemma_right hS isCompact_singleton
    ((nhdsSetWithin_mono_left hcenter) hpre)
  rw [nhdsSetWithin_singleton,
    nhdsWithin_eq_nhds.mpr (Icc_mem_nhds (by linarith : -d < 0) hd)] at hU
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨min d (r / 2), lt_min hd (by linarith), min_le_left _ _, ?_⟩
  rintro _ ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
  apply hSU ⟨hx, hrU ?_⟩
  rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
  have hcr := min_le_right d (r / 2)
  constructor <;> linarith [ht.1, ht.2]

open Classical in
theorem IsPLHomeomorphOn.annulus_mem_nhdsSetWithin_core
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Geometry.SimplicialComplex ℝ E) [Finite L.faces]
    (hL : IsCombinatorialManifoldWithBoundary 2 L)
    {A : Set E} {φ : (Fin 3 → ℝ) × ℝ → E}
    (hφ : IsPLHomeomorphOn φ (stdSimplexBoundary 2 ×ˢ Icc (-1 : ℝ) 1) A)
    (hAL : A ⊆ L.space) :
    A ∈ 𝓝ˢ[L.space] (φ '' (stdSimplexBoundary 2 ×ˢ {(0 : ℝ)})) := by
  have hS : IsPLSphere 1 (stdSimplexBoundary 2) := by
    simpa only [simplexBoundary_stdVertices_space] using isPLSphere_simplexBoundary_std 1
  obtain ⟨K, hKfin, hK, -, hKA, hKbd⟩ :=
    hφ.exists_annulus_complex hS (by norm_num : (-1 : ℝ) < 1)
  let _ : Finite K.faces := hKfin.to_subtype
  have hKL : K.space ⊆ L.space := hKA.subset.trans hAL
  rw [nhdsSetWithin, Filter.mem_inf_principal, mem_nhdsSet_iff_forall]
  rintro y ⟨⟨z, t⟩, ⟨hz, ht⟩, rfl⟩
  have ht0 : t = 0 := ht
  subst t
  have hyK : φ (z, 0) ∈ K.space := hKA.symm.subset (hφ.bijOn.mapsTo ⟨hz, by norm_num⟩)
  have hynot : φ (z, 0) ∉ (boundaryComplex 2 K).space := by
    rw [hKbd]
    rintro ⟨⟨w, s⟩, ⟨hw, hs⟩, heq⟩
    have hsI : s ∈ Icc (-1 : ℝ) 1 := by rcases hs with rfl | rfl <;> norm_num
    have hsame := congrArg Prod.snd (hφ.bijOn.injOn ⟨hw, hsI⟩ ⟨hz, by norm_num⟩ heq)
    rcases hs with h | h <;> change s = _ at h <;> simp_all
  have hnot : φ (z, 0) ∉ closure (L.space \ K.space) := fun h => hynot
    (inter_closure_sdiff_subset_boundaryComplex L K hL hK hKL ⟨hyK, h⟩)
  apply Filter.mem_inf_principal.mp
  refine mem_nhdsWithin.mpr ⟨(closure (L.space \ K.space))ᶜ,
    isClosed_closure.isOpen_compl, hnot, ?_⟩
  intro x hx
  apply hKA.subset
  by_contra hxK
  exact hx.1 (subset_closure ⟨hx.2, hxK⟩)

theorem IsPLHomeomorphOn.exists_bicollar_matching_from_surface_sides
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Geometry.SimplicialComplex ℝ E) [Finite L.faces]
    (hL : IsCombinatorialManifoldWithBoundary 2 L)
    {A W P N : Set E} {φ ρ : (Fin 3 → ℝ) × ℝ → E}
    (hφ : IsPLHomeomorphOn φ (stdSimplexBoundary 2 ×ˢ Icc (-1 : ℝ) 1) A)
    (hAL : A ⊆ L.space) {d : ℝ} (hd : 0 < d)
    (hρ : IsPLHomeomorphOn ρ (stdSimplexBoundary 2 ×ˢ Icc (-d) d) W)
    (hWL : W ⊆ L.space)
    (hzero : ∀ z ∈ stdSimplexBoundary 2, ρ (z, 0) = φ (z, 0))
    (hpos : ρ '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) d) ⊆ P)
    (hneg : ρ '' (stdSimplexBoundary 2 ×ˢ Icc (-d) 0) ⊆ N)
    (hAP : A ∩ P = φ '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1))
    (hAN : A ∩ N = φ '' (stdSimplexBoundary 2 ×ˢ Icc (-1 : ℝ) 0)) :
    ∃ (e : ℝ) (F : E → E), 0 < e ∧ e ≤ d ∧ e ≤ 1 ∧ IsPLHomeomorphOn F A A ∧
      EqOn F id (φ '' (stdSimplexBoundary 2 ×ˢ {0})) ∧
      (∀ r ∈ ({-1, 1} : Set ℝ), F '' (φ '' (stdSimplexBoundary 2 ×ˢ {r})) =
        φ '' (stdSimplexBoundary 2 ×ˢ {r})) ∧
      F '' (A ∩ N) = A ∩ N ∧ F '' (A ∩ P) = A ∩ P ∧
      ∀ z ∈ stdSimplexBoundary 2, ∀ t ∈ Icc (-e) e, F (φ (z, t)) = ρ (z, t) := by
  have hS : IsPolyhedron (stdSimplexBoundary 2) := by
    simpa only [simplexBoundary_stdVertices_space] using
      (isPLSphere_simplexBoundary_std 1).isPolyhedron
  obtain ⟨c, hc, hcd, hcA⟩ := exists_short_bicollar_image_subset_of_compact hS.isCompact hd
    hρ.isPiecewiseAffineOn.continuousOn (hρ.bijOn.mapsTo.mono_right hWL)
    (fun z hz => by rw [hzero z hz]; exact ⟨(z, 0), ⟨hz, rfl⟩, rfl⟩)
    (hφ.annulus_mem_nhdsSetWithin_core L hL hAL)
  let q := min c 1
  have hq : 0 < q := lt_min hc zero_lt_one
  have hq1 : q ≤ 1 := min_le_right _ _
  have hqc : q ≤ c := min_le_left _ _
  have hqd : q ≤ d := hqc.trans hcd
  have hsmall : stdSimplexBoundary 2 ×ˢ Icc (-q) q ⊆
      stdSimplexBoundary 2 ×ˢ Icc (-d) d :=
    prod_mono_right (Icc_subset_Icc (neg_le_neg hqd) hqd)
  have hφs := hφ.restrict (hS.prod isHPolytope_Icc.isPolyhedron)
    (prod_mono_right (Icc_subset_Icc (neg_le_neg hq1) hq1))
  have hρs := hρ.restrict (hS.prod isHPolytope_Icc.isPolyhedron) hsmall
  have hposq : ρ '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) q) ⊆
      φ '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) := by
    rintro y ⟨⟨z, t⟩, ⟨hz, ht⟩, rfl⟩
    apply hAP.subset
    exact ⟨hcA ⟨(z, t), ⟨hz, by constructor <;> linarith [ht.1, ht.2]⟩, rfl⟩,
      hpos ⟨(z, t), ⟨hz, ht.1, ht.2.trans hqd⟩, rfl⟩⟩
  have hnegq : ρ '' (stdSimplexBoundary 2 ×ˢ Icc (-q) 0) ⊆
      φ '' (stdSimplexBoundary 2 ×ˢ Icc (-1 : ℝ) 0) := by
    rintro y ⟨⟨z, t⟩, ⟨hz, ht⟩, rfl⟩
    apply hAN.subset
    exact ⟨hcA ⟨(z, t), ⟨hz, by constructor <;> linarith [ht.1, ht.2]⟩, rfl⟩,
      hneg ⟨(z, t), ⟨hz, by linarith [ht.1], ht.2⟩, rfl⟩⟩
  obtain ⟨e, F, he, heq, hF, hFcore, hFm, hFp, hFN, hFP, hmatch⟩ :=
    hφ.exists_annulus_map_matching_short_bicollar_charts hq hφs hρs
      (fun _ _ => rfl) hzero
      (image_mono (prod_mono_right (Icc_subset_Icc le_rfl hq1))) hposq
      (image_mono (prod_mono_right (Icc_subset_Icc (neg_le_neg hq1) le_rfl))) hnegq
  refine ⟨e, F, he, heq.trans hqd, heq.trans hq1, hF, hFcore, ?_, ?_, ?_, hmatch⟩
  · intro r hr
    rcases hr with rfl | rfl
    · exact hFm
    · exact hFp
  · rwa [← hAN] at hFN
  · rwa [← hAP] at hFP

end DifferentialGeometry.Topology.PiecewiseLinear
