import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingEssentialGenerator
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingAnnularBand
import DifferentialGeometry.Topology.PiecewiseLinear.Section34AnnularBandComponents

open Set

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

theorem section34_piercing_generators_of_essential_second
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦') {i : ℕ} (hi : i < cnt e)
    (hess : ¬ ∃ D : Set M₂, IsPLCellOn 2 D (Pg e i) ∧ D ⊆ G (ends e).2 '' Bb e) :
    CarriesFundamentalGroupOnto (Pg e i) (Sp e) ∧
      CarriesFundamentalGroupOnto (Pg e i) (Tp e) ∧
      ¬ ∃ D : Set M₂, IsPLCellOn 2 D (Pg e i) ∧ D ⊆ G (ends e).1 '' Aa e := by
  obtain ⟨j, hj, hjS, -, hjess⟩ :=
    exists_section34_piercing_circle_carrying_generators hprep hpack e
  have hSp : CarriesFundamentalGroupOnto (Pg e i) (Sp e) := by
    by_cases hij : i = j
    · exact hij ▸ hjS
    · obtain ⟨P, u, φ, -, hu, hφ, hφP, hband, hzero, hone⟩ :=
        exists_section34_piercing_annular_band hprep hpack e hi hj hij hess hjess
      have hmap : MapsTo φ (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) P :=
        fun x hx => hφP ⟨x, hx, rfl⟩
      have hcont : ContinuousOn (u ∘ φ) (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) :=
        hu.continuousOn.comp hφ.isPiecewiseAffineOn.continuousOn hmap
      have hinj : InjOn (u ∘ φ) (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) :=
        fun x hx y hy hxy => hφ.bijOn.injOn hx hy (hu.injOn (hmap hx) (hmap hy) hxy)
      have hann := isAnnulusOn_stdSimplex_lateral.image_of_continuousOn_injOn hcont hinj
      rw [hzero, hone] at hann
      have hBS : G (ends e).2 '' Bb e ⊆ Sp e := by
        obtain ⟨-, -, -, -, -, -, -, -, hBb, -⟩ := hpack
        exact (hBb e).1.trans interior_subset
      exact hann.carriesFundamentalGroupOnto_first_of_second (hband.trans hBS) hjS
  have htor := (section34_tubes_are_topological_solid_tori hprep hpack e).1
  have hTS := (section34_inner_tube_subset_interior_outer hprep hpack e).trans interior_subset
  have hAT : G (ends e).1 '' Aa e ⊆ Tp e := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hAa, -⟩ := hprep
    obtain ⟨-, -, -, htube, -⟩ := hpack
    rw [(htube e).2]
    exact image_mono ((hAa e).1 ▸ inter_subset_right)
  have hnonempty : (Pg e i).Nonempty := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hPg, -⟩ := hpack
    obtain ⟨P, hP⟩ := (hPg e i hi).1
    obtain ⟨x, hx⟩ := hP.nonempty
    exact ⟨P.piece.map x, P.piece.bijOn.mapsTo hx⟩
  have hfirst : ¬ ∃ D : Set M₂, IsPLCellOn 2 D (Pg e i) ∧ D ⊆ G (ends e).1 '' Aa e := by
    rintro ⟨D, hD, hDA⟩
    exact htor.not_carriesFundamentalGroupOnto_of_subset_isPLCellOn hD
      (hDA.trans (hAT.trans hTS)) hnonempty hD.boundary_subset hSp
  exact ⟨hSp, (section34_piercing_generators_of_essential_first hprep hpack e hi hfirst).2.1,
    hfirst⟩

theorem section34_piercing_disk_annuli_iff
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦') {i : ℕ} (hi : i < cnt e) :
    (∃ D : Set M₂, IsPLCellOn 2 D (Pg e i) ∧ D ⊆ G (ends e).1 '' Aa e) ↔
      ∃ D : Set M₂, IsPLCellOn 2 D (Pg e i) ∧ D ⊆ G (ends e).2 '' Bb e := by
  constructor
  · intro hD
    by_contra hess
    exact (section34_piercing_generators_of_essential_second hprep hpack e hi hess).2.2 hD
  · exact section34_piercing_disk_in_first_of_disk_in_second hprep hpack e hi

end DifferentialGeometry.Topology.PiecewiseLinear
