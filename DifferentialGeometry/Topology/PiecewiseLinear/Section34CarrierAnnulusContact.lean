import DifferentialGeometry.Topology.PiecewiseLinear.Section34CarrierBandFillingTrace
import DifferentialGeometry.Topology.PiecewiseLinear.Section34AnnularBandUniqueness

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLCellOn.inter_eq_annulus_of_carrier_ends {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {S B A A₀ A₁ J L T F C : Set M} (hS : IsPLCellOn 3 S B)
    (hA : IsAnnulusOn A A₀ A₁) (hAB : A ⊆ B)
    (hJ : IsPolyhedralSphere (n := 3) 1 J) (hL : IsPolyhedralSphere (n := 3) 1 L)
    (hJL : Disjoint J L) (hJend : Disjoint J (A₀ ∪ A₁))
    (hLend : Disjoint L (A₀ ∪ A₁))
    (hT : IsTopologicalSolidTorus T) (hAT : A ⊆ T)
    (hJcarry : CarriesFundamentalGroupOnto J T)
    (hLcarry : CarriesFundamentalGroupOnto L T)
    (hF : IsAnnulusOn F J L) (hFA : F ⊆ A) (hFC : F ⊆ C)
    (hfront : frontier C ∩ B ⊆ F) (hCT : C ⊆ T) : B ∩ C = F := by
  have hJA : J ⊆ A := hF.first_subset.trans hFA
  have hLA : L ⊆ A := hF.second_subset.trans hFA
  have hJess : ¬ ∃ D : Set M, IsPLCellOn 2 D J ∧ D ⊆ A := by
    rintro ⟨D, hD, hDA⟩
    exact hT.not_carriesFundamentalGroupOnto_of_subset_isPLCellOn hD
      (hDA.trans hAT) hF.ends_nonempty.1 hD.boundary_subset hJcarry
  have hLess : ¬ ∃ D : Set M, IsPLCellOn 2 D L ∧ D ⊆ A := by
    rintro ⟨D, hD, hDA⟩
    exact hT.not_carriesFundamentalGroupOnto_of_subset_isPLCellOn hD
      (hDA.trans hAT) hF.ends_nonempty.2 hD.boundary_subset hLcarry
  obtain ⟨P, u, φ, -, hu, hφ, hφP, hband, hzero, hone, hcert⟩ :=
    hS.exists_annular_band_with_carrier_trace hA hAB hJ hL hJA hLA hJL hJend hLend
      hT hAT hJcarry hLcarry
  have hmap : MapsTo φ (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) P :=
    fun x hx => hφP ⟨x, hx, rfl⟩
  have hann := isAnnulusOn_stdSimplex_lateral.image_of_continuousOn_injOn
    (hu.continuousOn.comp hφ.isPiecewiseAffineOn.continuousOn hmap)
    (hu.injOn.comp hφ.bijOn.injOn hmap)
  rw [hzero, hone] at hann
  have heq := hS.annulus_eq_of_same_essential_ends hA hAB hJ hL hJA hLA hJL hJend hLend
    hJess hLess hF hann hFA hband
  rw [← heq] at hcert
  exact hcert C hFC hfront hCT

end DifferentialGeometry.Topology.PiecewiseLinear
