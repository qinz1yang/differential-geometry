import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Basic
import DifferentialGeometry.Analysis.Integration.Measure.PartitionOfUnity
import DifferentialGeometry.Analysis.Integration.Measure.OpenPartialHomeomorph

noncomputable section

namespace DifferentialGeometry.Integral.Measure

open MeasureTheory Set Manifold
open scoped ContDiff Manifold Topology ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

private abbrev indices (K : Set M) (hK : IsCompact K) : Finset M :=
  (chartAtlasPOU I M).toPartitionOfUnity.fintsupportOn
    K hK

private abbrev carrier (K : Set M) (i : M) : Set M :=
  tsupport ((chartAtlasPOU I M) i) ∩ K

private abbrev image (K : Set M) (i : M) : Set E :=
  extChartAt I i '' carrier (I := I) K i

private theorem carrier_compact {K : Set M} (hK : IsCompact K) (i : M) :
    IsCompact (carrier (I := I) K i) :=
  hK.of_isClosed_subset
    ((isClosed_tsupport _).inter hK.isClosed) inter_subset_right

private theorem carrier_subset_source (K : Set M) (i : M) :
    carrier (I := I) K i ⊆ (extChartAt I i).source := by
  intro y hy
  rw [extChartAt_source]
  exact chartAtlasPOU_isSubordinate I M i hy.1

variable [MeasurableSpace M] [BorelSpace M]

private theorem lintegral_partition (μ : Measure M) {K : Set M} (hK : IsCompact K)
    (F : M → ENNReal) (hF : Measurable F)
    (hFsupp : Function.support F ⊆ K) :
    ∫⁻ y, F y ∂μ =
      ∑ i ∈ indices (I := I) K hK, ∫⁻ y in carrier (I := I) K i,
        ENNReal.ofReal ((chartAtlasPOU I M) i y) * F y ∂μ := by
  exact (chartAtlasPOU I M).toPartitionOfUnity.lintegral_eq_sum_fintsupportOn
    μ hK hF.aemeasurable hFsupp (subset_univ _)

variable {N : Type*} [TopologicalSpace N] [T2Space N]
  [MeasurableSpace N] [OpensMeasurableSpace N]

private theorem lintegral_map_partition (e : OpenPartialHomeomorph M N)
    (μ : Measure N) {K : Set M} (hK : IsCompact K) (F : M → ENNReal) (hF : Measurable F)
    (hFsupp : Function.support F ⊆ K)
    (hSrc : ∀ i ∈ indices (I := I) K hK, carrier (I := I) K i ⊆ e.source) :
    ∫⁻ y, F y ∂Measure.map e.symm (μ.restrict e.target) =
      ∑ i ∈ indices (I := I) K hK, ∫⁻ y in e '' carrier (I := I) K i,
        ENNReal.ofReal ((chartAtlasPOU I M) i (e.symm y)) * F (e.symm y) ∂μ := by
  apply e.lintegral_map_symm_restrict_eq_sum μ (indices (I := I) K hK)
    (fun y => F y)
    (fun i y => ENNReal.ofReal ((chartAtlasPOU I M) i y) * F y)
    (carrier (I := I) K)
  · intro i _
    exact ((chartAtlasPOU I M) i).contMDiff.continuous.measurable.ennreal_ofReal.mul hF
  · intro y
    by_cases hy : F y = 0
    · simp only [hy, mul_zero, Finset.sum_const_zero]
    · have hsum : (∑ i ∈ indices (I := I) K hK, (chartAtlasPOU I M) i y) = 1 :=
        (chartAtlasPOU I M).toPartitionOfUnity.sum_fintsupportOn hK
          (hFsupp hy) (mem_univ y)
      rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg
        (fun i _ => (chartAtlasPOU I M).nonneg i y), hsum,
        ENNReal.ofReal_one, one_mul]
  · exact hSrc
  · intro i _ y hy
    refine ⟨subset_tsupport _ ?_, hFsupp (right_ne_zero_of_mul hy)⟩
    intro hzero
    exact (left_ne_zero_of_mul hy) (by rw [hzero, ENNReal.ofReal_zero])
  · intro i hi
    exact ((carrier_compact hK i).image_of_continuousOn
      (e.continuousOn.mono (hSrc i hi))).measurableSet

private theorem lintegral_withDensity_partition (μ : Measure M) (d : M → ENNReal)
    {K : Set M} (hK : IsCompact K) (F : M → ENNReal) (hF : Measurable F)
    (hFsupp : Function.support F ⊆ K)
    (hd : ∀ i ∈ indices (I := I) K hK,
      AEMeasurable d (μ.restrict (carrier (I := I) K i))) :
    ∫⁻ y, F y ∂μ.withDensity d =
      ∑ i ∈ indices (I := I) K hK, ∫⁻ y in carrier (I := I) K i,
        ENNReal.ofReal ((chartAtlasPOU I M) i y) * F y * d y ∂μ := by
  rw [lintegral_partition (I := I) (μ.withDensity d) hK F hF hFsupp]
  apply Finset.sum_congr rfl
  intro i hi
  have hset : MeasurableSet (carrier (I := I) K i) :=
    (carrier_compact hK i).measurableSet
  have hw : AEMeasurable
      (fun y => ENNReal.ofReal ((chartAtlasPOU I M) i y) * F y)
      (μ.restrict (carrier (I := I) K i)) :=
    (((chartAtlasPOU I M) i).contMDiff.continuous.measurable.ennreal_ofReal.mul
      hF).aemeasurable
  rw [restrict_withDensity hset,
    lintegral_withDensity_eq_lintegral_mul₀ (hd i hi) hw]
  exact lintegral_congr (fun _ => mul_comm _ _)

private theorem lintegral_map_withDensity_partition (e : OpenPartialHomeomorph M N)
    (μ : Measure N) (d : N → ENNReal) {K : Set M} (hK : IsCompact K)
    (F : M → ENNReal) (hF : Measurable F)
    (hFsupp : Function.support F ⊆ K)
    (hSrc : ∀ i ∈ indices (I := I) K hK, carrier (I := I) K i ⊆ e.source)
    (hd : ∀ i ∈ indices (I := I) K hK,
      AEMeasurable d (μ.restrict (e '' carrier (I := I) K i))) :
    ∫⁻ y, F y
        ∂Measure.map e.symm ((μ.withDensity d).restrict e.target) =
      ∑ i ∈ indices (I := I) K hK, ∫⁻ y in e '' carrier (I := I) K i,
        ENNReal.ofReal ((chartAtlasPOU I M) i (e.symm y)) * F (e.symm y) * d y ∂μ := by
  rw [lintegral_map_partition (I := I) e (μ.withDensity d) hK F hF hFsupp hSrc]
  apply Finset.sum_congr rfl
  intro i hi
  have hset : MeasurableSet (e '' carrier (I := I) K i) :=
    ((carrier_compact hK i).image_of_continuousOn
    (e.continuousOn.mono (hSrc i hi))).measurableSet
  have htgt : e '' carrier (I := I) K i ⊆ e.target := by
    rintro _ ⟨p, hp, rfl⟩
    exact e.map_source (hSrc i hi hp)
  have hw : AEMeasurable
      (fun y => ENNReal.ofReal ((chartAtlasPOU I M) i (e.symm y)) * F (e.symm y))
      (μ.restrict (e '' carrier (I := I) K i)) :=
    (Measurable.aemeasurable
      (((chartAtlasPOU I M) i).contMDiff.continuous.measurable.ennreal_ofReal.mul hF)).comp_aemeasurable
      ((e.continuousOn_symm.mono htgt).aemeasurable hset)
  rw [restrict_withDensity hset, lintegral_withDensity_eq_lintegral_mul₀ (hd i hi) hw]
  exact lintegral_congr (fun _ => mul_comm _ _)

theorem lintegral_withDensity_eq_sum_chartAtlasPOU (μ : Measure M) (d : M → ENNReal)
    {K : Set M} (hK : IsCompact K) (F : M → ENNReal) (hF : Measurable F)
    (hFsupp : Function.support F ⊆ K)
    (hd : ∀ i ∈ (chartAtlasPOU I M).toPartitionOfUnity.fintsupportOn K hK,
      AEMeasurable d (μ.restrict (tsupport ((chartAtlasPOU I M) i) ∩ K))) :
    ∫⁻ y, F y ∂μ.withDensity d =
      ∑ i ∈ (chartAtlasPOU I M).toPartitionOfUnity.fintsupportOn K hK,
        ∫⁻ y in (extChartAt I i).symm ''
            (extChartAt I i '' (tsupport ((chartAtlasPOU I M) i) ∩ K)),
          ENNReal.ofReal ((chartAtlasPOU I M) i ((extChartAt I i).symm (extChartAt I i y))) *
            F ((extChartAt I i).symm (extChartAt I i y)) * d y ∂μ := by
  rw [lintegral_withDensity_partition (I := I) μ d hK F hF hFsupp hd]
  apply Finset.sum_congr rfl
  intro i hi
  have hback : (extChartAt I i).symm '' image (I := I) K i = carrier (I := I) K i :=
    (extChartAt I i).symm_image_image_of_subset_source
      (carrier_subset_source K i)
  rw [hback]
  apply setLIntegral_congr_fun (carrier_compact hK i).measurableSet
  intro y hy
  dsimp only
  rw [(extChartAt I i).left_inv (carrier_subset_source K i hy)]

private abbrev chartMap (e : OpenPartialHomeomorph M N) (i : M) : PartialEquiv E N :=
  (extChartAt I i).symm.trans e.toPartialEquiv

theorem _root_.OpenPartialHomeomorph.lintegral_map_symm_withDensity_eq_sum_chartAtlasPOU
    (e : OpenPartialHomeomorph M N) (μ : Measure N) (d : N → ENNReal)
    {K : Set M} (hK : IsCompact K) (F : M → ENNReal) (hF : Measurable F)
    (hFsupp : Function.support F ⊆ K)
    (hSrc : ∀ i ∈ (chartAtlasPOU I M).toPartitionOfUnity.fintsupportOn K hK,
      tsupport ((chartAtlasPOU I M) i) ∩ K ⊆ e.source)
    (hd : ∀ i ∈ (chartAtlasPOU I M).toPartitionOfUnity.fintsupportOn K hK,
      AEMeasurable d (μ.restrict (e '' (tsupport ((chartAtlasPOU I M) i) ∩ K)))) :
    ∫⁻ y, F y
        ∂Measure.map e.symm ((μ.withDensity d).restrict e.target) =
      ∑ i ∈ (chartAtlasPOU I M).toPartitionOfUnity.fintsupportOn K hK,
        ∫⁻ y in ((extChartAt I i).symm.trans e.toPartialEquiv) ''
            (extChartAt I i '' (tsupport ((chartAtlasPOU I M) i) ∩ K)),
          ENNReal.ofReal
            ((chartAtlasPOU I M) i
              ((extChartAt I i).symm (((extChartAt I i).symm.trans e.toPartialEquiv).symm y))) *
            F ((extChartAt I i).symm
              (((extChartAt I i).symm.trans e.toPartialEquiv).symm y)) * d y ∂μ := by
  rw [lintegral_map_withDensity_partition (I := I) e μ d hK F hF hFsupp hSrc hd]
  apply Finset.sum_congr rfl
  intro i hi
  have himage : chartMap (I := I) e i '' image (I := I) K i =
      e '' carrier (I := I) K i := by
    change (fun z => e ((extChartAt I i).symm z)) ''
      (extChartAt I i '' carrier (I := I) K i) = e '' carrier (I := I) K i
    calc
      _ = e '' (extChartAt I i).symm '' (extChartAt I i '' carrier (I := I) K i) :=
        (Set.image_image _ _ _).symm
      _ = e '' carrier (I := I) K i := congrArg (e '' ·)
        ((extChartAt I i).symm_image_image_of_subset_source
          (carrier_subset_source K i))
  rw [himage]
  have hset : MeasurableSet (e '' carrier (I := I) K i) :=
    ((carrier_compact hK i).image_of_continuousOn
      (e.continuousOn.mono (hSrc i hi))).measurableSet
  apply setLIntegral_congr_fun hset
  rintro y ⟨p, hp, rfl⟩
  change ENNReal.ofReal ((chartAtlasPOU I M) i (e.symm (e p))) * F (e.symm (e p)) * d (e p) =
    ENNReal.ofReal
      ((chartAtlasPOU I M) i ((extChartAt I i).symm (extChartAt I i (e.symm (e p))))) *
        F ((extChartAt I i).symm (extChartAt I i (e.symm (e p)))) * d (e p)
  rw [e.left_inv (hSrc i hi hp),
    (extChartAt I i).left_inv (carrier_subset_source K i hp)]

end DifferentialGeometry.Integral.Measure
