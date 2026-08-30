import DifferentialGeometry.Geometry.Metric.Family.Stationary

noncomputable section

open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Curvature

open DifferentialGeometry.Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]

theorem exists_metric_equivalence_bound_on_compact_time
    [CompactSpace M] [T2Space M]
    (G : Real → SmoothRiemannianMetric I M)
    {K : Set Real} (hK : IsCompact K)
    (hG : tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 K
      (fun t x => metricTensorField (I := I) (G t) x))
    (gRef : SmoothRiemannianMetric I M) :
    ∃ C : Real, 1 ≤ C ∧
      ∀ t ∈ K, ∀ x : M, ∀ v : TangentSpace I x,
        C⁻¹ * gRef.inner x v v ≤ (G t).inner x v v ∧
          (G t).inner x v v ≤ C * gRef.inner x v v := by
  let _ : CompleteSpace E := FiniteDimensional.complete Real E
  let _ : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hsource : IsCompact
      (Set.univ : Set (K × MetricUnitTangent (I := I) (M := M) gRef)) := by
    convert
      (isCompact_univ.prod (metricUnit_compact (I := I) (M := M) gRef) :
        IsCompact
          ((Set.univ : Set K) ×ˢ
            (Set.univ : Set (MetricUnitTangent (I := I) (M := M) gRef)))) using 1
    ext q
    simp
  let DRef := RealTimeInterval.univ 0
  let GRef := (stationaryMetricFamily (I := I) (M := M) gRef).metric
  have hGRef : MetricFamilySmoothOn (I := I) (M := M) DRef GRef := by
    simpa only [GRef] using
      metricFamilySmoothOn_stationary (I := I) (M := M) gRef DRef
  have hGReft : tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 K
      (fun t x => metricTensorField (I := I) (GRef t) x) :=
    metricTensor_cont_restrict_of_metricFamilySmoothOn
      (I := I) (M := M) GRef hGRef (fun _ _ => Set.mem_univ _)
  have hquadG : Continuous
      (metricTimeBundleQuad (I := I) (M := M) G K) := by
    have hquad := tensor0SFamily_quadCont (I := I) (M := M) hG
    exact hquad.congr fun _ => rfl
  have hquadRef : Continuous
      (metricTimeBundleQuad (I := I) (M := M) GRef K) := by
    have hquad := tensor0SFamily_quadCont (I := I) (M := M) hGReft
    exact hquad.congr fun _ => rfl
  have hcompactG : IsCompact
      (Set.univ : Set (MetricUnitTangentTimeSlab (I := I) (M := M) G K)) :=
    metricUnitTimeSlab_compact_of_param_cont
      (I := I) (M := M) G K gRef hsource
      (metricUnitTimeSlabParam_cont_of_bundle
        (I := I) (M := M) G K gRef hquadG)
  have hcompactRef : IsCompact
      (Set.univ : Set (MetricUnitTangentTimeSlab (I := I) (M := M) GRef K)) :=
    metricUnitTimeSlab_compact_of_param_cont
      (I := I) (M := M) GRef K gRef hsource
      (metricUnitTimeSlabParam_cont_of_bundle
        (I := I) (M := M) GRef K gRef hquadRef)
  have habsG := timeSlabAbsQuadCont (I := I) (M := M)
    (G := GRef)
    (A := fun t x => metricTensorField (I := I) (G t) x)
    K (tensor0SFamilyContinuousOnSet.tangentBundle
      (I := I) (M := M) hG)
  have habsRef := timeSlabAbsQuadCont (I := I) (M := M)
    (G := G)
    (A := fun t x => metricTensorField (I := I) (GRef t) x)
    K (tensor0SFamilyContinuousOnSet.tangentBundle
      (I := I) (M := M) hGReft)
  obtain ⟨C₁, -, hupper⟩ := compactUnitTimeSlab_absBound
    (I := I) (M := M) GRef
    (fun t x => metricTensorField (I := I) (G t) x)
    K hcompactRef habsG
  obtain ⟨C₂, -, hlower⟩ := compactUnitTimeSlab_absBound
    (I := I) (M := M) G
    (fun t x => metricTensorField (I := I) (GRef t) x)
    K hcompactG habsRef
  let C : Real := max 1 (max C₁ C₂)
  have hC : 1 ≤ C := le_max_left _ _
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  refine ⟨C, hC, ?_⟩
  intro t ht x v
  have href : 0 ≤ gRef.inner x v v := by
    rcases eq_or_ne v 0 with rfl | hv
    · simp
    · exact (gRef.pos x v hv).le
  have hGt_nonneg : 0 ≤ (G t).inner x v v := by
    rcases eq_or_ne v 0 with rfl | hv
    · simp
    · exact ((G t).pos x v hv).le
  have huAbs := hupper t ht x v
  have hlAbs := hlower t ht x v
  simp only [quad02, metricTensorField_apply, GRef, stationaryMetricFamily] at huAbs hlAbs
  have hu : (G t).inner x v v ≤ C₁ * gRef.inner x v v :=
    (le_abs_self _).trans huAbs
  have hl : gRef.inner x v v ≤ C₂ * (G t).inner x v v :=
    (le_abs_self _).trans hlAbs
  have hC₁C : C₁ ≤ C :=
    le_trans (le_max_left C₁ C₂) (le_max_right 1 _)
  have hC₂C : C₂ ≤ C :=
    le_trans (le_max_right C₁ C₂) (le_max_right 1 _)
  have hlC : gRef.inner x v v ≤ C * (G t).inner x v v :=
    hl.trans (mul_le_mul_of_nonneg_right hC₂C hGt_nonneg)
  constructor
  · calc
      C⁻¹ * gRef.inner x v v ≤ C⁻¹ * (C * (G t).inner x v v) :=
        mul_le_mul_of_nonneg_left hlC (inv_nonneg.mpr hCpos.le)
      _ = (G t).inner x v v := by simp [hCpos.ne']
  · exact hu.trans (mul_le_mul_of_nonneg_right hC₁C href)

theorem exists_metric_equivalence_bound_on_compact_time_of_metricFamilySmoothOn
    [CompactSpace M] [T2Space M]
    {D : RealTimeInterval}
    (G : Real → SmoothRiemannianMetric I M)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    {K : Set Real} (hK : IsCompact K) (hKD : K ⊆ D.carrier)
    (gRef : SmoothRiemannianMetric I M) :
    ∃ C : Real, 1 ≤ C ∧
      ∀ t ∈ K, ∀ x : M, ∀ v : TangentSpace I x,
        C⁻¹ * gRef.inner x v v ≤ (G t).inner x v v ∧
          (G t).inner x v v ≤ C * gRef.inner x v v :=
  exists_metric_equivalence_bound_on_compact_time
    (I := I) (M := M) G hK
    (metricTensor_cont_restrict_of_metricFamilySmoothOn
      (I := I) (M := M) G hG hKD) gRef

theorem exists_metric_equivalence_bound_on_icc
    [CompactSpace M] [T2Space M]
    (G : Real → SmoothRiemannianMetric I M)
    {t₀ t₁ : Real}
    (hG : tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 (Icc t₀ t₁)
      (fun t x => metricTensorField (I := I) (G t) x))
    (gRef : SmoothRiemannianMetric I M) :
    ∃ C : Real, 1 ≤ C ∧
      ∀ t ∈ Icc t₀ t₁, ∀ x : M, ∀ v : TangentSpace I x,
        C⁻¹ * gRef.inner x v v ≤ (G t).inner x v v ∧
          (G t).inner x v v ≤ C * gRef.inner x v v :=
  exists_metric_equivalence_bound_on_compact_time
    (I := I) (M := M) G isCompact_Icc hG gRef

theorem exists_metric_equivalence_bound_on_icc_of_metricFamilySmoothOn
    [CompactSpace M] [T2Space M]
    {D : RealTimeInterval}
    (G : Real → SmoothRiemannianMetric I M)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    {t₀ t₁ : Real} (hIcc : Icc t₀ t₁ ⊆ D.carrier)
    (gRef : SmoothRiemannianMetric I M) :
    ∃ C : Real, 1 ≤ C ∧
      ∀ t ∈ Icc t₀ t₁, ∀ x : M, ∀ v : TangentSpace I x,
        C⁻¹ * gRef.inner x v v ≤ (G t).inner x v v ∧
          (G t).inner x v v ≤ C * gRef.inner x v v :=
  exists_metric_equivalence_bound_on_icc (I := I) (M := M) G
    (metricTensor_cont_restrict_of_metricFamilySmoothOn
      (I := I) (M := M) G hG hIcc) gRef

end DifferentialGeometry.Geometry.Curvature

end
