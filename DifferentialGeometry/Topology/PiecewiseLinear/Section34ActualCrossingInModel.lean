import DifferentialGeometry.Topology.PiecewiseLinear.Section34ModelCrossingPullback
import DifferentialGeometry.Topology.PiecewiseLinear.Section34AnnularCrossingGerms
import DifferentialGeometry.Topology.PiecewiseLinear.Section34AnnularBandNeighborhood

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

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

theorem section34_hasPLCrossingAt_boundary_preimages
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦')
    {P : Set (EuclideanSpace ℝ (Fin 3))} {u : EuclideanSpace ℝ (Fin 3) → M₂}
    (hu : IsPLHomeomorphInto 3 u P) {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ interior P)
    (hxy : u x ∈ G (ends e).1 '' CpBd (ends e).1 ∩ G (ends e).2 '' CpBd (ends e).2) :
    HasPLCrossingAt (u ⁻¹' (G (ends e).1 '' CpBd (ends e).1))
      (u ⁻¹' (G (ends e).2 '' CpBd (ends e).2)) x := by
  obtain ⟨-, -, -, -, hCp, -, -, -, -, -, -, -, -, -, -, hBb, -⟩ := id hprep
  obtain ⟨-, -, -, -, -, -, hmeet, -, hBdis, -, hGp, -, -, -, -, -, -, -, -, hcross, -⟩ :=
    id hpack
  have hm := hmeet e hxy
  have hxtrace : u x ∈ G (ends e).1 '' Aa e ∩ G (ends e).2 '' Bb e :=
    ⟨image_mono sdiff_subset hm.1.1, image_mono sdiff_subset hm.1.2⟩
  obtain ⟨c, hc, hxc, hcross⟩ := hcross e (u x) hxtrace
  have hpull := hu.hasPLCrossingAt_preimage_of_chart hx hc hxc hcross
  have huc := hu.continuousOn.continuousAt (mem_interior_iff_mem_nhds.mp hx)
  have hAeq := section34_first_annulus_eq_boundary_inter_tube hprep hpack e
  have hann := (section34_piercing_annuli hprep hpack e).2
  have hcellB := (hCp (ends e).2).image (hGp (ends e).2)
  have hBn := hcellB.annulus_mem_nhdsWithin_of_not_mem_ends
    hann (image_mono (hBb e).1) hxtrace.2
      (by
        intro hxends
        rw [← image_union] at hxends
        exact disjoint_left.mp (hBdis e).2 hxends (interior_subset hm.2))
  obtain ⟨V, hV, hVB⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hBn
  apply hpull.congr
  · filter_upwards [huc.preimage_mem_nhds (isOpen_interior.mem_nhds hm.2)] with y hy
    change u y ∈ G (ends e).1 '' Aa e ↔ u y ∈ G (ends e).1 '' CpBd (ends e).1
    rw [hAeq]
    exact and_iff_left (interior_subset hy)
  · filter_upwards [huc.preimage_mem_nhds hV] with y hy
    change u y ∈ G (ends e).2 '' Bb e ↔ u y ∈ G (ends e).2 '' CpBd (ends e).2
    exact ⟨fun hb => image_mono (hBb e).1 hb, fun hb => hVB ⟨hy, hb⟩⟩

end DifferentialGeometry.Topology.PiecewiseLinear
