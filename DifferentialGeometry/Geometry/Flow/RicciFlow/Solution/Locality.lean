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

end

noncomputable section

open Set

namespace DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M]

theorem isSolutionOn_of_local_time_restrictions
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hloc : ∀ t ∈ D.carrier, ∃ U : Set ℝ, IsOpen U ∧ t ∈ U ∧
      ∃ D' : RealTimeInterval, D.carrier ∩ U ⊆ D'.carrier ∧
        D.regular ∩ U ⊆ D'.regular ∧ IsSolutionOn (S.timeRestrict D')) :
    IsSolutionOn S where
  smoothMetric := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x X Y t ht
      obtain ⟨U, hU, htU, D', hcar, hreg, hS⟩ := hloc t (D.regular_subset ht)
      exact (hS.smoothMetric.coeff x X Y t (hreg ⟨ht, htU⟩)).mono_of_mem_nhdsWithin
        (Filter.mem_of_superset (inter_mem_nhdsWithin _ (hU.mem_nhds htU)) hreg)
    · intro x X Y t ht
      obtain ⟨U, hU, htU, D', hcar, hreg, hS⟩ := hloc t ht
      exact (hS.smoothMetric.coeff_cont x X Y t (hcar ⟨ht, htU⟩)).mono_of_mem_nhdsWithin
        (Filter.mem_of_superset (inter_mem_nhdsWithin _ (hU.mem_nhds htU)) hcar)
    · apply tensor0SFamilyContinuousOnSet.of_locally
      intro t ht
      obtain ⟨U, hU, htU, D', hcar, hreg, hS⟩ := hloc t ht
      exact ⟨U, hU, htU, hS.smoothMetric.metricTensor_cont.mono hcar⟩
    · intro Idx _ frame u hframe i j
      apply contMDiffOn_of_locally_contMDiffOn
      intro p hp
      obtain ⟨U, hU, htU, D', hcar, hreg, hS⟩ := hloc p.1 (D.regular_subset hp.1)
      refine ⟨U ×ˢ (univ : Set M), hU.prod isOpen_univ, ⟨htU, trivial⟩, ?_⟩
      exact (hS.smoothMetric.frameCompSmooth frame hframe i j).mono
        (fun q hq => ⟨hreg ⟨hq.1.1, hq.2.1⟩, hq.1.2⟩)
  smoothConnection := by
    intro t
    obtain ⟨U, hU, htU, D', hcar, hreg, hS⟩ := hloc t t.2
    exact hS.smoothConnection ⟨t, hcar ⟨t.2, htU⟩⟩
  equation := by
    intro t x X Y
    obtain ⟨U, hU, htU, D', hcar, hreg, hS⟩ := hloc t (D.regular_subset t.2)
    exact (hS.equation ⟨t, hreg ⟨t.2, htU⟩⟩ x X Y).mono_of_mem_nhdsWithin
      (Filter.mem_of_superset (inter_mem_nhdsWithin _ (hU.mem_nhds htU)) hcar)
  scalarCont := by
    intro p hp
    obtain ⟨U, hU, htU, D', hcar, hreg, hS⟩ := hloc p.1 hp.1
    apply (hS.scalarCont p ⟨hcar ⟨hp.1, htU⟩, hp.2⟩).mono_of_mem_nhdsWithin
    exact Filter.mem_of_superset (inter_mem_nhdsWithin _
      ((hU.prod isOpen_univ).mem_nhds ⟨htU, trivial⟩))
      (fun q hq => ⟨hcar ⟨hq.1.1, hq.2.1⟩, hq.1.2⟩)
  scalarTime := by
    intro K t ht hK x
    obtain ⟨U, hU, htU, D', hcar, hreg, hS⟩ := hloc t (hK ht)
    exact (hS.scalarTime (hcar ⟨hK ht, htU⟩) Subset.rfl x).mono_of_mem_nhdsWithin
      (Filter.mem_of_superset (inter_mem_nhdsWithin _ (hU.mem_nhds htU))
        (fun s hs => hcar ⟨hK hs.1, hs.2⟩))
  ricciCont := by
    apply tensor0SFamilyContinuousOnSet.of_locally
    intro t ht
    obtain ⟨U, hU, htU, D', hcar, hreg, hS⟩ := hloc t ht
    exact ⟨U, hU, htU, hS.ricciCont.mono hcar⟩
  rm04Cont := by
    apply tensor0SFamilyContinuousOnSet.of_locally
    intro t ht
    obtain ⟨U, hU, htU, D', hcar, hreg, hS⟩ := hloc t ht
    exact ⟨U, hU, htU, hS.rm04Cont.mono hcar⟩
  ricciNormSpace := by
    intro t ht x
    obtain ⟨U, hU, htU, D', hcar, hreg, hS⟩ := hloc t ht
    exact hS.ricciNormSpace t (hcar ⟨ht, htU⟩) x
  ricciNormGrad := by
    intro t ht x
    obtain ⟨U, hU, htU, D', hcar, hreg, hS⟩ := hloc t ht
    exact hS.ricciNormGrad t (hcar ⟨ht, htU⟩) x

theorem isSolutionOn_of_closed_backward_windows
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    {T : ℝ} (hcarrier : D.carrier ⊆ Iic T)
    (hwin : ∀ n : ℕ, IsSolutionOn (S.timeRestrict
      (RealTimeInterval.closed (T - ((n + 1 : ℕ) : ℝ)) T (sub_le_self _ (Nat.cast_nonneg _))))) :
    IsSolutionOn S := by
  have hregular : D.regular ⊆ Iio T := by
    simpa only [interior_Iic] using
      interior_maximal (D.regular_subset.trans hcarrier) D.regular_isOpen
  apply isSolutionOn_of_local_time_restrictions S
  intro t ht
  obtain ⟨n, hn⟩ := exists_nat_ge (T - t)
  have htN : T - ((n + 1 : ℕ) : ℝ) < t := by
    push_cast
    linarith
  refine ⟨Ioi (T - ((n + 1 : ℕ) : ℝ)), isOpen_Ioi, htN,
    RealTimeInterval.closed (T - ((n + 1 : ℕ) : ℝ)) T
      (sub_le_self _ (Nat.cast_nonneg _)), ?_, ?_, hwin n⟩
  · exact fun s hs => ⟨hs.2.le, hcarrier hs.1⟩
  · exact fun s hs => ⟨hs.2, hregular hs.1⟩

end DifferentialGeometry.PDE.RicciFlow

end
