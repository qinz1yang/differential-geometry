import DifferentialGeometry.Topology.PiecewiseLinear.Section34AnnulusFrontier
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingDiskComponents
import DifferentialGeometry.Topology.PiecewiseLinear.Section34RimAnchoredTrapping

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLCellOn.disjoint_annulus_ends_of_disk_subset {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {S B A A₀ A₁ D J : Set M} (hS : IsPLCellOn 3 S B) (hA : IsAnnulusOn A A₀ A₁)
    (hAB : A ⊆ B) (hD : IsPLCellOn 2 D J) (hDA : D ⊆ A)
    (hends : Disjoint J (A₀ ∪ A₁)) : Disjoint D (A₀ ∪ A₁) := by
  obtain ⟨E, hE, hcover, hmeet⟩ :=
    hS.exists_closed_boundary_disk_complement hD (hDA.trans hAB)
  obtain ⟨hchart⟩ := hS.nonempty_chartedSpace_boundary
  let _ := hchart
  have hcomp : ((Subtype.val : B → M) ⁻¹' E)ᶜ ⊆ Subtype.val ⁻¹' D := by
    intro x hx
    exact ((hcover.superset x.property).resolve_right hx)
  have hint := interior_maximal hcomp ((hE.preimage continuous_subtype_val).isOpen_compl)
  have hfront := (hA.preimage_subtype hAB).frontier_eq_ends
  refine disjoint_left.mpr fun x hx hxrim => ?_
  have hxE : x ∉ E := fun hxE => disjoint_left.mp hends (hmeet.subset ⟨hx, hxE⟩) hxrim
  have hxfront : (⟨x, hAB (hDA hx)⟩ : B) ∈ frontier ((Subtype.val : B → M) ⁻¹' A) := by
    rw [hfront]
    exact hxrim
  have hsub : (Subtype.val : B → M) ⁻¹' D ⊆ Subtype.val ⁻¹' A := fun _ hy => hDA hy
  exact hxfront.2 (interior_mono hsub (hint hxE))

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

theorem exists_section34_interior_innermost_disk
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦')
    (hanchors : ∃ a ∈ G (ends e).2 '' Bb e ∩ G (ends e).1 '' Cp (ends e).1,
      ∃ b ∈ G (ends e).2 '' Bb e \ G (ends e).1 '' Cp (ends e).1,
        (∀ y ∈ G (ends e).2 '' Bb e ∩ G (ends e).1 '' Cp (ends e).1,
          y ∉ connectedComponentIn
            (G (ends e).2 '' Bb e ∩ G (ends e).1 '' Cp (ends e).1) a →
          closure (connectedComponentIn
            (G (ends e).2 '' Bb e ∩ G (ends e).1 '' Cp (ends e).1) y) ⊆ interior (Tp e)) ∧
        ∀ y ∈ G (ends e).2 '' Bb e \ G (ends e).1 '' Cp (ends e).1,
          y ∉ connectedComponentIn
            (G (ends e).2 '' Bb e \ G (ends e).1 '' Cp (ends e).1) b →
          closure (connectedComponentIn
            (G (ends e).2 '' Bb e \ G (ends e).1 '' Cp (ends e).1) y) ⊆ interior (Tp e))
    (hexists : ∃ i < cnt e, ∃ D : Set M₂, IsPLCellOn 2 D (Pg e i) ∧
      D ⊆ G (ends e).2 '' Bb e) :
    ∃ (i : ℕ) (D : Set M₂), i < cnt e ∧ IsPLCellOn 2 D (Pg e i) ∧
      D ⊆ G (ends e).2 '' Bb e ∩ interior (Tp e) ∧
      D ∩ G (ends e).1 '' CpBd (ends e).1 = Pg e i ∧ IsConnected (D \ Pg e i) := by
  obtain ⟨i, D, hi, hD, hDB, htrace, hconn, -, -⟩ :=
    exists_section34_innermost_disk_component hprep hpack e hexists
  have hann := (section34_piercing_annuli hprep hpack e).2
  obtain ⟨-, -, -, -, hCp, -, -, -, -, -, -, -, -, -, -, hBb, -⟩ := id hprep
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hGp, -, -, -, -, -, -, hPg, -⟩ := id hpack
  have hcell := (hCp (ends e).2).image (hGp (ends e).2)
  have hBCp := (hBb e).1.trans (hCp (ends e).2).boundary_subset
  have hends : Disjoint (Pg e i)
      (G (ends e).2 '' Bb₀ e ∪ G (ends e).2 '' Bb₁ e) := by
    rw [← image_union]
    refine disjoint_left.mpr ?_
    rintro y hy ⟨z, hz, hzy⟩
    obtain ⟨x, hx, hxy⟩ := ((hPg e i hi).2 hy).2
    have hzCp := hBCp ((union_subset (hBb e).2.first_subset (hBb e).2.second_subset) hz)
    have heq := (hGp (ends e).2).injOn (hBCp hx.1) hzCp (hxy.trans hzy.symm)
    exact hx.2 (heq.symm ▸ hz)
  have hdis := hcell.disjoint_annulus_ends_of_disk_subset hann (image_mono (hBb e).1)
    hD hDB hends
  have hDS := hDB.trans (image_mono (hBb e).1)
  have hDconn : IsPreconnected D := by
    rw [← hD.closure_sdiff_boundary]
    exact hconn.isPreconnected.closure
  have hcomponent : ∀ z ∈ D \ G (ends e).1 '' CpBd (ends e).1,
      connectedComponentIn
        (G (ends e).2 '' CpBd (ends e).2 \ G (ends e).1 '' CpBd (ends e).1) z ⊆ D := by
    intro z hz
    have hJT : Pg e i ⊆ G (ends e).1 '' CpBd (ends e).1 := htrace ▸ inter_subset_right
    have hz' : z ∈ D \ Pg e i := ⟨hz.1, fun h => hz.2 (hJT h)⟩
    rw [hcell.connectedComponentIn_sdiff_eq_disk hD Subset.rfl hDS htrace
      hconn.isPreconnected hz']
    exact sdiff_subset
  obtain ⟨x, hx⟩ := hD.nonempty
  exact ⟨i, D, hi, hD,
    section34_region_subset_inner_tube_interior_of_rim_avoidance hprep hpack e hanchors
      hD.isCompact.isClosed hDconn hDS ⟨x, hx, hDB hx⟩ hcomponent hdis, htrace, hconn⟩

end DifferentialGeometry.Topology.PiecewiseLinear
