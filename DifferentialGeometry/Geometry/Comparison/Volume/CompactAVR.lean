import DifferentialGeometry.Geometry.Comparison.Volume.AsymptoticVolumeRatio

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace Poincare.Geometry.Riemannian.VolumeComparison

open DifferentialGeometry
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  [T2Space (TangentBundle I M)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
variable [PseudoEMetricSpace M] [IsRiemannianManifold I M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

omit [I.Boundaryless] [T2Space (TangentBundle I M)] [PseudoEMetricSpace M]
  [IsRiemannianManifold I M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)] in
theorem asymptoticVolumeRatio_eq_zero_of_compactSpace [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (p : M) :
    asymptoticVolumeRatio g p = 0 := by
  let _ : MeasurableSpace M := borel M
  let _ : BorelSpace M := ⟨rfl⟩
  let n : ℕ := Module.finrank ℝ E
  let μ : Measure M := riemannianVolumeMeasure (I := I) (M := M) g
  let omegaN : ℝ := euclideanUnitBallVolume n
  have hn : n ≠ 0 := NeZero.ne n
  have homega : 0 < omegaN := euclideanUnitBallVolume_pos n
  let _ : IsFiniteMeasure μ :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  have hμ : μ Set.univ ≠ ⊤ := IsFiniteMeasure.measure_univ_lt_top.ne
  have hreal : Tendsto (fun k : ℕ => omegaN * (((k : ℝ) + 1) ^ n)) atTop atTop := by
    exact Tendsto.const_mul_atTop homega
      ((tendsto_pow_atTop hn).comp
        (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop))
  have hden : Tendsto
      (fun k : ℕ => ENNReal.ofReal (omegaN * (((k : ℝ) + 1) ^ n)))
      atTop (𝓝 ⊤) :=
    ENNReal.tendsto_ofReal_nhds_top.mpr hreal
  have hquot : Tendsto
      (fun k : ℕ => μ Set.univ /
        ENNReal.ofReal (omegaN * (((k : ℝ) + 1) ^ n)))
      atTop (𝓝 0) := by
    simpa only [ENNReal.div_top] using
      ENNReal.Tendsto.const_div hden (Or.inr hμ)
  have hle : ∀ k : ℕ,
      asymptoticVolumeRatio g p ≤
        μ Set.univ / ENNReal.ofReal (omegaN * (((k : ℝ) + 1) ^ n)) := by
    intro k
    let R : Set.Ioi (0 : ℝ) := ⟨(k : ℝ) + 1, by
      change (0 : ℝ) < (k : ℝ) + 1
      positivity⟩
    refine (asymptoticVolumeRatio_le_normalizedBallVolume g p R).trans ?_
    change ballVolume g p ((k : ℝ) + 1) /
        ENNReal.ofReal (omegaN * (((k : ℝ) + 1) ^ n)) ≤
      μ Set.univ / ENNReal.ofReal (omegaN * (((k : ℝ) + 1) ^ n))
    apply ENNReal.div_le_div_right
    exact measure_mono (Set.subset_univ _)
  exact le_antisymm
    (ge_of_tendsto hquot (Filter.Eventually.of_forall hle)) bot_le

omit [I.Boundaryless] [T2Space (TangentBundle I M)] [PseudoEMetricSpace M]
  [IsRiemannianManifold I M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)] in
theorem not_compactSpace_of_pos_le_asymptoticVolumeRatio
    (g : SmoothRiemannianMetric I M) (p : M) {v : ℝ≥0∞}
    (hv : 0 < v) (hAVR : v ≤ asymptoticVolumeRatio g p) :
    ¬ CompactSpace M := by
  intro hcompact
  let _ : CompactSpace M := hcompact
  rw [asymptoticVolumeRatio_eq_zero_of_compactSpace (I := I) g p] at hAVR
  exact (not_lt_of_ge hAVR) hv

end Poincare.Geometry.Riemannian.VolumeComparison
