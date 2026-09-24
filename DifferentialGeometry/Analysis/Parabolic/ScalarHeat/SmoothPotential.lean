import DifferentialGeometry.Analysis.Parabolic.ScalarHeat.TimeDependent

open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

namespace DifferentialGeometry.Analysis.Parabolic.IsHeatPotOn

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem of_contMDiffOn
    {D : RealTimeInterval}
    {G : MetricConnectionFamily (I := I) (M := M) ℝ}
    {V u : ℝ → M → ℝ} {J : Set ℝ}
    (hu : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × M => u q.1 q.2) (J ×ˢ Set.univ))
    (hcarrier : D.carrier ⊆ J)
    (hequation : ∀ t ∈ D.regular, ∀ x : M,
      HasDerivAt (fun s : ℝ => u s x)
        (laplacianAt (I := I) G t (u t) x + V t x * u t x) t) :
    IsHeatPotOn D G V u where
  jointSmooth := hu.mono
    (Set.prod_mono (D.regular_subset.trans hcarrier) Set.Subset.rfl)
  jointCont := hu.continuousOn.mono (Set.prod_mono hcarrier Set.Subset.rfl)
  sliceSmooth t ht := by
    have hinsert : ContMDiff I (𝓘(ℝ, ℝ).prod I) ∞
        (fun x : M => (t, x)) :=
      contMDiff_const.prodMk contMDiff_id
    exact hu.comp_contMDiff hinsert (fun x => ⟨hcarrier ht, Set.mem_univ x⟩)
  equation := hequation

end DifferentialGeometry.Analysis.Parabolic.IsHeatPotOn
