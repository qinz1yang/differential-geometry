import DifferentialGeometry.Topology.PiecewiseLinear.Section34DiskTraceDeletion
import DifferentialGeometry.Topology.PiecewiseLinear.Section34AnnulusDiskLocalization
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingGenerators

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

theorem section34_piercing_disk_disjoint_first_rims
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦') {i : ℕ} (hi : i < cnt e)
    {D : Set M₂} (hD : IsPLCellOn 2 D (Pg e i)) (hDA : D ⊆ G (ends e).1 '' Aa e) :
    Disjoint D (G (ends e).1 '' (Ab₀ e ∪ Ab₁ e)) := by
  have hann := (section34_piercing_annuli hprep hpack e).1
  have htor := (section34_tubes_are_topological_solid_tori hprep hpack e).2
  have hgen := section34_piercing_generators hprep hpack e
  obtain ⟨-, -, -, -, hCp, -, -, -, -, -, -, -, -, -, hAa, -⟩ := hprep
  obtain ⟨-, -, -, htube, -, -, -, -, -, -, hG, -, -, -, -, -, -, hPg, -⟩ := hpack
  have hAB : Aa e ⊆ CpBd (ends e).1 := (hAa e).1 ▸ inter_subset_left
  have hDB : D ⊆ G (ends e).1 '' CpBd (ends e).1 := hDA.trans (image_mono hAB)
  have hDT : D ⊆ Tp e := by
    rw [(htube e).2]
    exact hDA.trans (image_mono ((hAa e).1 ▸ inter_subset_right))
  have hR : Ab₀ e ∪ Ab₁ e ⊆ Cp (ends e).1 :=
    (union_subset (hAa e).2.first_subset (hAa e).2.second_subset).trans
      (hAB.trans (hCp _).boundary_subset)
  have hsep : Disjoint (G (ends e).1 '' (Ab₀ e ∪ Ab₁ e)) (Pg e i) := by
    apply disjoint_left.mpr
    rintro _ ⟨x, hx, rfl⟩ hxJ
    obtain ⟨y, hy, hyx⟩ := ((hPg e i hi).2 hxJ).1
    have hxy := (hG _).injOn ((hCp _).boundary_subset (hAB hy.1)) (hR hx) hyx
    exact hy.2 (hxy.symm ▸ hx)
  have hdis (Y : Set M₂) (hY : IsPreconnected Y) (hne : Y.Nonempty)
      (hYR : Y ⊆ G (ends e).1 '' (Ab₀ e ∪ Ab₁ e))
      (hYB : Y ⊆ G (ends e).1 '' CpBd (ends e).1)
      (hcarry : CarriesFundamentalGroupOnto Y (Tp e)) : Disjoint D Y := by
    rcases ((hCp _).image (hG _)).subset_or_disjoint_boundary_disk hD hDB hY hYB
      (hsep.mono_left hYR) with hsub | hdis
    · exact (htor.not_carriesFundamentalGroupOnto_of_subset_isPLCellOn hD hDT hne hsub
        hcarry).elim
    · exact hdis
  rw [image_union, disjoint_union_right]
  exact ⟨hdis _ hann.isPreconnected_ends.1 hann.ends_nonempty.1
      (image_mono subset_union_left) (image_mono ((hAa e).2.first_subset.trans hAB)) hgen.1,
    hdis _ hann.isPreconnected_ends.2 hann.ends_nonempty.2
      (image_mono subset_union_right) (image_mono ((hAa e).2.second_subset.trans hAB)) hgen.2.1⟩

end DifferentialGeometry.Topology.PiecewiseLinear
