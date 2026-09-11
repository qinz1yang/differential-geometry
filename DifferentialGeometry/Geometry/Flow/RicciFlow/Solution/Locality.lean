import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Restriction
import DifferentialGeometry.Geometry.Metric.Family.Continuity

open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M]

theorem isSolutionOn_of_locally
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hloc : ∀ t ∈ D.carrier, ∃ a b : ℝ, ∃ ht : t ∈ Set.Ioo a b,
      IsSolutionOn (S.timeRestrict (RealTimeInterval.openInterval a b t ht))) :
    IsSolutionOn S where
  smoothMetric := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x X Y t ht
      rcases hloc t (D.regular_subset ht) with ⟨a, b, htJ, hJ⟩
      exact ((hJ.smoothMetric.coeff x X Y).contDiffAt
        (Ioo_mem_nhds htJ.1 htJ.2)).contDiffWithinAt
    · intro x X Y t ht
      rcases hloc t ht with ⟨a, b, htJ, hJ⟩
      exact ((hJ.smoothMetric.coeff_cont x X Y).continuousAt
        (Ioo_mem_nhds htJ.1 htJ.2)).continuousWithinAt
    · apply tensor0SFamilyContinuousOnSet.of_locally
      intro t ht
      rcases hloc t ht with ⟨a, b, htJ, hJ⟩
      exact ⟨Set.Ioo a b, isOpen_Ioo, htJ,
        hJ.smoothMetric.metricTensor_cont.mono Set.inter_subset_right⟩
    · intro Idx _ frame u hframe i j
      apply contMDiffOn_of_locally_contMDiffOn
      intro p hp
      rcases hloc p.1 (D.regular_subset hp.1) with ⟨a, b, hpJ, hJ⟩
      refine ⟨Set.Ioo a b ×ˢ (Set.univ : Set M), isOpen_Ioo.prod isOpen_univ,
        ⟨hpJ, trivial⟩, ?_⟩
      exact (hJ.smoothMetric.frameCompSmooth frame hframe i j).mono
        (fun _ hq => ⟨hq.2.1, hq.1.2⟩)
  smoothConnection := by
    intro t
    rcases hloc t t.2 with ⟨a, b, htJ, hJ⟩
    exact hJ.smoothConnection ⟨t, htJ⟩
  equation := by
    intro t x X Y
    rcases hloc t (D.regular_subset t.2) with ⟨a, b, htJ, hJ⟩
    exact ((hJ.equation ⟨t, htJ⟩ x X Y).hasDerivAt
      (Ioo_mem_nhds htJ.1 htJ.2)).hasDerivWithinAt
  scalarCont := by
    intro p hp
    rcases hloc p.1 hp.1 with ⟨a, b, hpJ, hJ⟩
    exact (hJ.scalarCont.continuousAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds
      ⟨hpJ, trivial⟩)).continuousWithinAt
  scalarTime := by
    intro K t ht hK x
    rcases hloc t (hK ht) with ⟨a, b, htJ, hJ⟩
    exact ((hJ.scalarTime htJ Set.Subset.rfl x).differentiableAt
      (Ioo_mem_nhds htJ.1 htJ.2)).differentiableWithinAt
  ricciCont := by
    apply tensor0SFamilyContinuousOnSet.of_locally
    intro t ht
    rcases hloc t ht with ⟨a, b, htJ, hJ⟩
    exact ⟨Set.Ioo a b, isOpen_Ioo, htJ, hJ.ricciCont.mono Set.inter_subset_right⟩
  rm04Cont := by
    apply tensor0SFamilyContinuousOnSet.of_locally
    intro t ht
    rcases hloc t ht with ⟨a, b, htJ, hJ⟩
    exact ⟨Set.Ioo a b, isOpen_Ioo, htJ, hJ.rm04Cont.mono Set.inter_subset_right⟩
  ricciNormSpace := by
    intro t ht x
    rcases hloc t ht with ⟨a, b, htJ, hJ⟩
    exact hJ.ricciNormSpace t htJ x
  ricciNormGrad := by
    intro t ht x
    rcases hloc t ht with ⟨a, b, htJ, hJ⟩
    exact hJ.ricciNormGrad t htJ x

theorem isSolutionOn_ancient_of_open_interval_restrictions
    {T : ℝ} (S : SolutionOn (I := I) (M := M) (RealTimeInterval.ancient T))
    (hloc : ∀ a b t : ℝ, ∀ ht : t ∈ Set.Ioo a b,
      Set.Ioo a b ⊆ Set.Iio T →
      IsSolutionOn (S.timeRestrict (RealTimeInterval.openInterval a b t ht))) :
    IsSolutionOn S := by
  apply isSolutionOn_of_locally (S := S)
  intro t ht
  have htT : t < T := by simpa using ht
  have hmem : t ∈ Set.Ioo (t - 1) T := ⟨by linarith, htT⟩
  refine ⟨t - 1, T, hmem, hloc (t - 1) T t hmem ?_⟩
  exact fun _ hs => hs.2
end DifferentialGeometry.PDE.RicciFlow
