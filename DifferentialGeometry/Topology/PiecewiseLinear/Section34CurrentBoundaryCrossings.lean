import DifferentialGeometry.Topology.PiecewiseLinear.Section34AnnularBandNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CrossingPreservation
import DifferentialGeometry.Topology.PiecewiseLinear.Section34AnnularCrossingGerms

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem chart_images_eventually_iff_of_relative_neighborhood
    {M E : Type*} [TopologicalSpace M] [TopologicalSpace E]
    (c : OpenPartialHomeomorph M E) {x : M} (hxc : x ∈ c.source)
    {A S : Set M} (hAS : A ⊆ S) (hA : A ∈ 𝓝[S] x) :
    ∀ᶠ z in 𝓝 (c x), z ∈ c '' (A ∩ c.source) ↔ z ∈ c '' (S ∩ c.source) := by
  obtain ⟨V, hV, hVA⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hA
  obtain ⟨O, hOV, hO, hxO⟩ := mem_nhds_iff.mp hV
  filter_upwards [(c.isOpen_image_source_inter hO).mem_nhds
    ⟨x, ⟨hxc, hxO⟩, rfl⟩] with z hz
  obtain ⟨y, ⟨hyc, hyO⟩, rfl⟩ := hz
  have hmem (T : Set M) : c y ∈ c '' (T ∩ c.source) ↔ y ∈ T := by
    constructor
    · rintro ⟨w, ⟨hw, hwc⟩, hwy⟩
      exact c.injOn hwc hyc hwy ▸ hw
    · exact fun hy => ⟨y, ⟨hy, hyc⟩, rfl⟩
  rw [hmem, hmem]
  exact ⟨fun hy => hAS hy, fun hy => hVA ⟨hOV hyO, hy⟩⟩

theorem HasPLCrossingAt.of_relative_neighborhoods
    {M : Type*} [TopologicalSpace M]
    {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))} {x : M}
    {A B S T : Set M}
    (hcross : HasPLCrossingAt (c '' (A ∩ c.source)) (c '' (B ∩ c.source)) (c x))
    (hxc : x ∈ c.source) (hAS : A ⊆ S) (hBT : B ⊆ T)
    (hA : A ∈ 𝓝[S] x) (hB : B ∈ 𝓝[T] x) :
    HasPLCrossingAt (c '' (S ∩ c.source)) (c '' (T ∩ c.source)) (c x) :=
  hcross.congr (chart_images_eventually_iff_of_relative_neighborhood c hxc hAS hA)
    (chart_images_eventually_iff_of_relative_neighborhood c hxc hBT hB)

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


theorem section34_current_boundary_chart_crossing
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦') (Ψ : M₂ ≃ₜ M₂) {x : M₂}
    (hx : x ∈ G (ends e).1 '' CpBd (ends e).1 ∩ G (ends e).2 '' CpBd (ends e).2)
    (hfix : Ψ =ᶠ[𝓝 x] id) :
    ∃ c ∈ (plGroupoid 3).maximalAtlas M₂, x ∈ c.source ∧
      HasPLCrossingAt (c '' (Ψ '' (G (ends e).2 '' CpBd (ends e).2) ∩ c.source))
        (c '' (G (ends e).1 '' CpBd (ends e).1 ∩ c.source)) (c x) := by
  obtain ⟨-, -, -, -, hCp, -, -, -, -, -, -, -, -, -, -, hBb, -⟩ := id hprep
  obtain ⟨-, -, -, -, -, -, hmeet, -, hBdis, -, hGp, -, -, -, -, -, -, -, -, hcross, -⟩ :=
    id hpack
  have hm := hmeet e hx
  have hxtrace : x ∈ G (ends e).1 '' Aa e ∩ G (ends e).2 '' Bb e :=
    ⟨image_mono sdiff_subset hm.1.1, image_mono sdiff_subset hm.1.2⟩
  obtain ⟨c, hc, hxc, hcross⟩ := hcross e x hxtrace
  have hAeq := section34_first_annulus_eq_boundary_inter_tube hprep hpack e
  have hAn : G (ends e).1 '' Aa e ∈ 𝓝[G (ends e).1 '' CpBd (ends e).1] x := by
    refine mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
      ⟨interior (Tp e), isOpen_interior.mem_nhds hm.2, ?_⟩
    intro y hy
    rw [hAeq]
    exact ⟨hy.2, interior_subset hy.1⟩
  have hAsub : G (ends e).1 '' Aa e ⊆ G (ends e).1 '' CpBd (ends e).1 := by
    rw [hAeq]
    exact inter_subset_left
  have hcellB := (hCp (ends e).2).image (hGp (ends e).2)
  have hBn := hcellB.annulus_mem_nhdsWithin_of_not_mem_ends
    (section34_piercing_annuli hprep hpack e).2 (image_mono (hBb e).1) hxtrace.2
      (by
        intro hxends
        rw [← image_union] at hxends
        exact disjoint_left.mp (hBdis e).2 hxends (interior_subset hm.2))
  have hwhole := hcross.of_relative_neighborhoods hxc hAsub (image_mono (hBb e).1) hAn hBn
  obtain ⟨O, hOsub, hO, hxO⟩ := mem_nhds_iff.mp hfix
  have hOeq : EqOn Ψ id O := fun _ hy => hOsub hy
  exact ⟨c, hc, hxc, (hwhole.image_right_of_fixed_neighborhood Ψ hO hOeq hxO hxc).symm⟩

end DifferentialGeometry.Topology.PiecewiseLinear
