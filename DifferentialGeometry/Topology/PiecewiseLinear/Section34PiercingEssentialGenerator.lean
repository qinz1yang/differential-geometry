import DifferentialGeometry.Topology.PiecewiseLinear.Section34AnnulusCircleDichotomy
import DifferentialGeometry.Topology.PiecewiseLinear.Section34AnnulusGeneratorBridge

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

theorem section34_piercing_generators_of_essential_first
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦') {i : ℕ} (hi : i < cnt e)
    (hess : ¬ ∃ D : Set M₂, IsPLCellOn 2 D (Pg e i) ∧ D ⊆ G (ends e).1 '' Aa e) :
    CarriesFundamentalGroupOnto (Pg e i) (Sp e) ∧
      CarriesFundamentalGroupOnto (Pg e i) (Tp e) ∧
      ¬ ∃ D : Set M₂, IsPLCellOn 2 D (Pg e i) ∧ D ⊆ G (ends e).2 '' Bb e := by
  have hann := (section34_piercing_annuli hprep hpack e).1
  have hgen := section34_piercing_generators hprep hpack e
  have htor := (section34_tubes_are_topological_solid_tori hprep hpack e).1
  have hTS := (section34_inner_tube_subset_interior_outer hprep hpack e).trans interior_subset
  obtain ⟨-, -, -, -, hCp, -, -, -, -, -, -, -, -, -, hAa, -⟩ := hprep
  obtain ⟨-, -, -, hEq, -, -, -, -, hBbSp, -, hG, -, -, -, -, -, -, hPg, -⟩ := hpack
  have hAS : G (ends e).1 '' Aa e ⊆ G (ends e).1 '' CpBd (ends e).1 :=
    image_mono ((hAa e).1 ▸ inter_subset_left)
  have hACp := ((hAa e).1 ▸ inter_subset_left).trans (hCp (ends e).1).boundary_subset
  have hAT : G (ends e).1 '' Aa e ⊆ Tp e := by
    rw [(hEq e).2]
    exact image_mono ((hAa e).1 ▸ inter_subset_right)
  have hJA : Pg e i ⊆ G (ends e).1 '' Aa e := fun x hx =>
    image_mono sdiff_subset ((hPg e i hi).2 hx).1
  have hends : Disjoint (Pg e i)
      (G (ends e).1 '' Ab₀ e ∪ G (ends e).1 '' Ab₁ e) := by
    rw [← image_union]
    refine disjoint_left.mpr ?_
    rintro y hy ⟨z, hz, hzy⟩
    obtain ⟨x, hx, hxy⟩ := ((hPg e i hi).2 hy).1
    have hzCp := hACp ((union_subset (hAa e).2.first_subset (hAa e).2.second_subset) hz)
    have heq := (hG (ends e).1).injOn (hACp hx.1) hzCp (hxy.trans hzy.symm)
    exact hx.2 (heq.symm ▸ hz)
  have hcell := (hCp (ends e).1).image (hG (ends e).1)
  have hdich := hcell.exists_disk_in_annulus_or_separating_ends
    hann hAS (hPg e i hi).1 hJA hends
  obtain ⟨D₀, D₁, hcover, hmeet, hD₀, -, h₀, h₁⟩ := hdich.resolve_left hess
  have hD₀S : D₀ ⊆ G (ends e).1 '' CpBd (ends e).1 :=
    hcover ▸ subset_union_left
  have h₀J : Disjoint (G (ends e).1 '' Ab₀ e) (Pg e i) :=
    (hends.mono_right subset_union_left).symm
  have hD₁ : Disjoint D₀ (G (ends e).1 '' Ab₁ e) := by
    refine disjoint_left.mpr fun x hxD hx₁ => ?_
    exact disjoint_left.mp hends (hmeet ▸ And.intro hxD (h₁ hx₁)) (Or.inr hx₁)
  have hSp := hcell.carriesFundamentalGroupOnto_boundary_of_annulus_end hD₀ hann hAS
    hD₀S hJA h₀ h₀J hD₁ (hAT.trans hTS) hgen.2.2
  have hTp := hcell.carriesFundamentalGroupOnto_boundary_of_annulus_end hD₀ hann hAS
    hD₀S hJA h₀ h₀J hD₁ hAT hgen.1
  have hne : (Pg e i).Nonempty := by
    obtain ⟨P, hP⟩ := (hPg e i hi).1
    obtain ⟨x, hx⟩ := hP.nonempty
    exact ⟨P.piece.map x, P.piece.bijOn.mapsTo hx⟩
  refine ⟨hSp, hTp, ?_⟩
  rintro ⟨D, hD, hDB⟩
  exact htor.not_carriesFundamentalGroupOnto_of_subset_isPLCellOn hD
    (hDB.trans ((hBbSp e).1.trans interior_subset)) hne hD.boundary_subset hSp

theorem section34_piercing_disk_in_first_of_disk_in_second
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦') {i : ℕ} (hi : i < cnt e)
    (hD : ∃ D : Set M₂, IsPLCellOn 2 D (Pg e i) ∧ D ⊆ G (ends e).2 '' Bb e) :
    ∃ D : Set M₂, IsPLCellOn 2 D (Pg e i) ∧ D ⊆ G (ends e).1 '' Aa e := by
  by_contra hess
  exact (section34_piercing_generators_of_essential_first hprep hpack e hi hess).2.2 hD

theorem exists_section34_piercing_circle_carrying_generators
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦') :
    ∃ i < cnt e, CarriesFundamentalGroupOnto (Pg e i) (Sp e) ∧
      CarriesFundamentalGroupOnto (Pg e i) (Tp e) ∧
      ¬ ∃ D : Set M₂, IsPLCellOn 2 D (Pg e i) ∧ D ⊆ G (ends e).2 '' Bb e := by
  obtain ⟨i, hi, -, hess⟩ :=
    exists_section34_piercing_circle_essential_in_first_annulus hprep hpack e
  exact ⟨i, hi, section34_piercing_generators_of_essential_first hprep hpack e hi hess⟩

end DifferentialGeometry.Topology.PiecewiseLinear
