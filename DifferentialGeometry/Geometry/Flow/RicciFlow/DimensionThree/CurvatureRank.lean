import DifferentialGeometry.Geometry.Curvature.DimensionThree.ExteriorRank
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Uhlenbeck.CurvatureOperatorRank
import DifferentialGeometry.Geometry.Metric.BundlePullbackSmooth
import DifferentialGeometry.Geometry.Connection.ModelNorm

noncomputable section

open Bundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle (MetricFiberData)
open scoped Manifold ContDiff RealInnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [oldNorm : NormedAddCommGroup F] [oldSpace : NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]

private theorem exists_curvature_rank_spreading_metric
    [ConnectedSpace M]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hdim : Module.finrank ℝ F = 3)
    {T : ℝ} (hT : 0 < T) (hreg : Set.Icc 0 T ⊆ D.regular)
    (h : ContMDiffRiemannianMetric I ∞ F V)
    (ι₀ : ∀ x, V x ≃L[ℝ] TangentSpace I x)
    (hι₀ : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (F →L[ℝ] E) x (ι₀ x).toContinuousLinearMap))
    (h₀ : ∀ x v w, (S.family.metric 0).inner x (ι₀ x v) (ι₀ x w) = h.inner x v w)
    (hR : ∀ t ∈ Set.Icc 0 T, ∀ x,
      (⟨metricRm04At (S.family.metric t) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩ :
          algebraicCurvatureTensorSubmodule (I := I) (M := M) x) ∈
            algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M)) :
    letI : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
    letI : RiemannianBundle V := ⟨h.toRiemannianMetric⟩
    letI sourceNorm : ∀ y, NormedAddCommGroup (V y) := fun y =>
      Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal y
    letI : ∀ y, SeminormedAddCommGroup (V y) := fun y => (sourceNorm y).toSeminormedAddCommGroup
    letI : ∀ y, InnerProductSpace ℝ (V y) := fun y => Bundle.instInnerProductSpaceReal y
    ∃ ι : ℝ → ∀ x, V x ≃L[ℝ] TangentSpace I x,
      (∀ x, ι 0 x = ι₀ x) ∧
      (∀ t ∈ Set.Icc 0 T, ∀ x v w,
        (S.family.metric t).inner x (ι t x v) (ι t x w) = h.inner x v w) ∧
      (let R := fun t x => exteriorPower.traceNormalizedCurvatureEndomorphism
        ((S.base.rm04 t x).compContinuousLinearMap (fun _ => (ι t x).toContinuousLinearMap))
        ((mem_algebraicCurvatureTensorSubmodule.mp
          (metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.base.metric t) x)).compContinuousLinearMap
            (ι t x).toContinuousLinearMap)
       (∀ s t, 0 ≤ s → s < t → t ≤ T → ∀ x y,
         Module.finrank ℝ (R s x).range ≤ Module.finrank ℝ (R t y).range) ∧
       (∀ t ∈ Set.Ioc 0 T, ∀ x y,
         Module.finrank ℝ (R t x).range = Module.finrank ℝ (R t y).range) ∧
       (∀ t ∈ Set.Ioc 0 T, ∀ x,
         Module.finrank ℝ (R t x).range = 0 ∨
           Module.finrank ℝ (R t x).range = 1 ∨ Module.finrank ℝ (R t x).range = 3)) := by
  let : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
  let : RiemannianBundle V := ⟨h.toRiemannianMetric⟩
  let sourceNorm : ∀ y, NormedAddCommGroup (V y) := fun y =>
    Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal y
  let : ∀ y, NormedAddCommGroup (V y) := sourceNorm
  let : ∀ y, SeminormedAddCommGroup (V y) := fun y => (sourceNorm y).toSeminormedAddCommGroup
  let : ∀ y, InnerProductSpace ℝ (V y) := fun y => Bundle.instInnerProductSpaceReal y
  let : IsContMDiffRiemannianBundle I ∞ F V := ⟨h.inner, h.contMDiff, fun _ _ _ => rfl⟩
  let m := MetricFiberData.ofFiniteDimensional F
  have hιwithin := fun y =>
    (contMDiffWithinAt_hom_totalSpace_domain_model_metric_iff
      (IA := I) (IB := I) (F := E) (V := TangentSpace I) (W := V) m
      (n := ∞) (f := fun z => TotalSpace.mk' (F →L[ℝ] E) z (ι₀ z).toContinuousLinearMap)
      (s := Set.univ) (x := y)).mpr ((hι₀ y).contMDiffWithinAt (s := Set.univ))
  let vb := vector_bundle_model_metric (V := V) m
  let svb := contMDiffVectorBundle_model_metric (IB := I) (V := V) (n := ∞) m
  let rm := isContMDiffRiemannianBundle_model_metric (IB := I) (V := V) (n := ∞) m
  let : NormedAddCommGroup F := m.toNormedAddCommGroupOfTopology
  let : InnerProductSpace ℝ F := @MetricFiberData.toInnerProductSpaceOfTopology F oldNorm.toAddCommGroup oldSpace.toModule
      _ _ (by let : SeminormedAddCommGroup F := oldNorm.toSeminormedAddCommGroup
              let : NormedSpace ℝ F := oldSpace
              infer_instance) _ _ m
  let : VectorBundle ℝ F V := vb
  let : ContMDiffVectorBundle ∞ F V I := svb
  let : IsContMDiffRiemannianBundle I ∞ F V := rm
  have hιnew : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
      (fun y => TotalSpace.mk' (F →L[ℝ] E) y (ι₀ y).toContinuousLinearMap) :=
    fun y => contMDiffWithinAt_univ.mp (hιwithin y)
  have hex := exists_uhlenbeck_isometry_with_curvatureOperator_rank_and_kernel
    (F := F) (V := V) S hS hdim hT hreg ι₀ hιnew h₀ hR
  rcases hex with ⟨ι, hi, -, -, -, hm, hh⟩
  refine ⟨ι, hi, hm, hh.1, hh.2.1, hh.2.2.2.2.1⟩

private theorem intrinsic_curvature_rank_spreading
    [ConnectedSpace M]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hdim : Module.finrank ℝ E = 3)
    {T : ℝ} (hreg : Set.Icc 0 T ⊆ D.regular)
    (hR : ∀ t ∈ Set.Icc 0 T, ∀ x,
      (⟨metricRm04At (S.family.metric t) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩ :
          algebraicCurvatureTensorSubmodule (I := I) (M := M) x) ∈
            algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M)) :
    ∀ s t, 0 ≤ s → s < t → t ≤ T → ∀ x y,
      Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric s) x
        ⟨metricRm04At (S.family.metric s) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric s) x⟩) ≤
      Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric t) y
        ⟨metricRm04At (S.family.metric t) y,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) y⟩) := by
  intro s t hs hst ht x y
  have hT : 0 < T := hs.trans_lt (hst.trans_le ht)
  have h := exists_curvature_rank_spreading_metric (F := E) (V := TangentSpace I)
    S hS hdim hT hreg (S.family.metric 0) (fun x => ContinuousLinearEquiv.refl ℝ (TangentSpace I x))
    (show ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E) x
        (ContinuousLinearMap.id ℝ (TangentSpace I x))) from
      (contMDiff_id : ContMDiff I I ∞ (fun x : M => x)).clm_bundle_id)
    (fun _ _ _ => rfl) hR
  let : RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨(S.family.metric 0).toRiemannianMetric⟩
  let sourceNorm : ∀ y : M, NormedAddCommGroup (TangentSpace I y) := fun y =>
    Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal y
  let : ∀ y : M, NormedAddCommGroup (TangentSpace I y) := sourceNorm
  let : ∀ y : M, SeminormedAddCommGroup (TangentSpace I y) := fun y => (sourceNorm y).toSeminormedAddCommGroup
  let : ∀ y : M, InnerProductSpace ℝ (TangentSpace I y) := fun y => Bundle.instInnerProductSpaceReal y
  obtain ⟨ι, hi, hm, hr, hsp, htri⟩ := h
  have hsT : s ∈ Set.Icc 0 T := ⟨hs, hst.le.trans ht⟩
  have htT : t ∈ Set.Icc 0 T := ⟨hs.trans hst.le, ht⟩
  have hx := traceNormalizedCurvatureEndomorphism_pullback_finrank_range
    hdim (S.family.metric s) x
      ⟨metricRm04At (S.family.metric s) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric s) x⟩ (ι s x) (hm s hsT x)
  have hy := traceNormalizedCurvatureEndomorphism_pullback_finrank_range
    hdim (S.family.metric t) y
      ⟨metricRm04At (S.family.metric t) y,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) y⟩ (ι t y) (hm t htT y)
  rw [← hx, ← hy]
  exact hr s t hs hst ht x y

private theorem intrinsic_curvature_rank_constancy_and_trichotomy
    [ConnectedSpace M]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hdim : Module.finrank ℝ E = 3)
    {T : ℝ} (hT : 0 < T) (hreg : Set.Icc 0 T ⊆ D.regular)
    (hR : ∀ t ∈ Set.Icc 0 T, ∀ x,
      (⟨metricRm04At (S.family.metric t) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩ :
          algebraicCurvatureTensorSubmodule (I := I) (M := M) x) ∈
            algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M)) :
    (∀ t ∈ Set.Ioc 0 T, ∀ x y,
      Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric t) x
        ⟨metricRm04At (S.family.metric t) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩) =
      Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric t) y
        ⟨metricRm04At (S.family.metric t) y,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) y⟩)) ∧
    (∀ t ∈ Set.Ioc 0 T, ∀ x,
      let q := Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric t) x
        ⟨metricRm04At (S.family.metric t) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩)
      q = 0 ∨ q = 1 ∨ q = 3) := by
  have h := exists_curvature_rank_spreading_metric (F := E) (V := TangentSpace I)
    S hS hdim hT hreg (S.family.metric 0) (fun x => ContinuousLinearEquiv.refl ℝ (TangentSpace I x))
    (show ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E) x
        (ContinuousLinearMap.id ℝ (TangentSpace I x))) from
      (contMDiff_id : ContMDiff I I ∞ (fun x : M => x)).clm_bundle_id)
    (fun _ _ _ => rfl) hR
  let : RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨(S.family.metric 0).toRiemannianMetric⟩
  let sourceNorm : ∀ y : M, NormedAddCommGroup (TangentSpace I y) := fun y =>
    Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal y
  let : ∀ y : M, NormedAddCommGroup (TangentSpace I y) := sourceNorm
  let : ∀ y : M, SeminormedAddCommGroup (TangentSpace I y) := fun y => (sourceNorm y).toSeminormedAddCommGroup
  let : ∀ y : M, InnerProductSpace ℝ (TangentSpace I y) := fun y => Bundle.instInnerProductSpaceReal y
  obtain ⟨ι, hi, hm, hr, hsp, htri⟩ := h
  have hRank (t : ℝ) (ht : t ∈ Set.Ioc 0 T) (x : M) :=
    traceNormalizedCurvatureEndomorphism_pullback_finrank_range
      hdim (S.family.metric t) x
        ⟨metricRm04At (S.family.metric t) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩ (ι t x) (hm t ⟨ht.1.le, ht.2⟩ x)
  constructor
  · intro t ht x y
    rw [← hRank t ht x, ← hRank t ht y]
    exact hsp t ht x y
  · intro t ht x
    dsimp only
    rw [← hRank t ht x]
    exact htri t ht x



theorem curvatureOperatorImageAt_finrank_le_at_later_time
    [ConnectedSpace M]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hdim : Module.finrank ℝ E = 3)
    {s t : ℝ} (hst : s < t) (hreg : Set.Icc s t ⊆ D.regular)
    (hR : ∀ r ∈ Set.Icc s t, ∀ x,
      (⟨metricRm04At (S.family.metric r) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric r) x⟩ :
          algebraicCurvatureTensorSubmodule (I := I) (M := M) x) ∈
            algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M)) :
    ∀ x y,
      Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric s) x
        ⟨metricRm04At (S.family.metric s) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric s) x⟩) ≤
      Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric t) y
        ⟨metricRm04At (S.family.metric t) y,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) y⟩) := by
  have hreg' : Set.Icc 0 (t - s) ⊆ (D.timeShift s).regular := by
    intro r hr
    exact hreg ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have hR' : ∀ r ∈ Set.Icc 0 (t - s), ∀ x,
      (⟨metricRm04At ((S.timeShift s).family.metric r) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule ((S.timeShift s).family.metric r) x⟩ :
          algebraicCurvatureTensorSubmodule (I := I) (M := M) x) ∈
            algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M) := by
    intro r hr x
    exact hR (r + s) ⟨by linarith [hr.1], by linarith [hr.2]⟩ x
  let q (r : ℝ) (x : M) := Module.finrank ℝ
    (curvatureOperatorImageAt (S.family.metric r) x
      ⟨metricRm04At (S.family.metric r) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric r) x⟩)
  intro x y
  have h : q (0 + s) x ≤ q (t - s + s) y :=
    intrinsic_curvature_rank_spreading (S.timeShift s) (isSolutionOn_timeShift hS s)
      hdim hreg' hR' 0 (t - s) le_rfl (sub_pos.mpr hst) le_rfl x y
  simpa only [zero_add, sub_add_cancel] using h

private theorem curvature_rank_constancy_and_trichotomy_on_interval
    [ConnectedSpace M]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hdim : Module.finrank ℝ E = 3)
    {s t : ℝ} (hst : s < t) (hreg : Set.Icc s t ⊆ D.regular)
    (hR : ∀ r ∈ Set.Icc s t, ∀ x,
      (⟨metricRm04At (S.family.metric r) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric r) x⟩ :
          algebraicCurvatureTensorSubmodule (I := I) (M := M) x) ∈
            algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M)) :
    (∀ x y,
      Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric t) x
        ⟨metricRm04At (S.family.metric t) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩) =
      Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric t) y
        ⟨metricRm04At (S.family.metric t) y,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) y⟩)) ∧
    (∀ x,
      let q := Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric t) x
        ⟨metricRm04At (S.family.metric t) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩)
      q = 0 ∨ q = 1 ∨ q = 3) := by
  have hreg' : Set.Icc 0 (t - s) ⊆ (D.timeShift s).regular := by
    intro r hr
    exact hreg ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have hR' : ∀ r ∈ Set.Icc 0 (t - s), ∀ x,
      (⟨metricRm04At ((S.timeShift s).family.metric r) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule ((S.timeShift s).family.metric r) x⟩ :
          algebraicCurvatureTensorSubmodule (I := I) (M := M) x) ∈
            algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M) := by
    intro r hr x
    exact hR (r + s) ⟨by linarith [hr.1], by linarith [hr.2]⟩ x
  have h := intrinsic_curvature_rank_constancy_and_trichotomy (S.timeShift s)
    (isSolutionOn_timeShift hS s) hdim (sub_pos.mpr hst) hreg' hR'
  let q (r : ℝ) (x : M) := Module.finrank ℝ
    (curvatureOperatorImageAt (S.family.metric r) x
      ⟨metricRm04At (S.family.metric r) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric r) x⟩)
  constructor
  · have heq : ∀ x y, q (t - s + s) x = q (t - s + s) y :=
      h.1 (t - s) ⟨sub_pos.mpr hst, le_rfl⟩
    simpa only [sub_add_cancel] using heq
  · have htri : ∀ x, q (t - s + s) x = 0 ∨ q (t - s + s) x = 1 ∨
        q (t - s + s) x = 3 := h.2 (t - s) ⟨sub_pos.mpr hst, le_rfl⟩
    simpa only [sub_add_cancel] using htri

theorem curvatureOperatorImageAt_finrank_eq_at_later_time
    [ConnectedSpace M]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hdim : Module.finrank ℝ E = 3)
    {s t : ℝ} (hst : s < t) (hreg : Set.Icc s t ⊆ D.regular)
    (hR : ∀ r ∈ Set.Icc s t, ∀ x,
      (⟨metricRm04At (S.family.metric r) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric r) x⟩ :
          algebraicCurvatureTensorSubmodule (I := I) (M := M) x) ∈
            algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M)) :
    ∀ x y,
      Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric t) x
        ⟨metricRm04At (S.family.metric t) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩) =
      Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric t) y
        ⟨metricRm04At (S.family.metric t) y,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) y⟩) := by
  exact (curvature_rank_constancy_and_trichotomy_on_interval S hS hdim hst hreg hR).1

theorem curvatureOperatorImageAt_finrank_trichotomy_at_later_time
    [ConnectedSpace M]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hdim : Module.finrank ℝ E = 3)
    {s t : ℝ} (hst : s < t) (hreg : Set.Icc s t ⊆ D.regular)
    (hR : ∀ r ∈ Set.Icc s t, ∀ x,
      (⟨metricRm04At (S.family.metric r) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric r) x⟩ :
          algebraicCurvatureTensorSubmodule (I := I) (M := M) x) ∈
            algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M)) :
    ∀ x,
      let q := Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric t) x
        ⟨metricRm04At (S.family.metric t) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩)
      q = 0 ∨ q = 1 ∨ q = 3 := by
  exact (curvature_rank_constancy_and_trichotomy_on_interval S hS hdim hst hreg hR).2

theorem curvatureOperatorImageAt_finrank_le_on_nonnegative_interval
    [ConnectedSpace M]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hdim : Module.finrank ℝ E = 3)
    {T : ℝ} (hreg : Set.Icc 0 T ⊆ D.regular)
    (hR : ∀ t ∈ Set.Icc 0 T, ∀ x,
      (⟨metricRm04At (S.family.metric t) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩ :
          algebraicCurvatureTensorSubmodule (I := I) (M := M) x) ∈
            algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M)) :
    ∀ s t, 0 ≤ s → s < t → t ≤ T → ∀ x y,
      Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric s) x
        ⟨metricRm04At (S.family.metric s) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric s) x⟩) ≤
      Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric t) y
        ⟨metricRm04At (S.family.metric t) y,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) y⟩) := by
  intro s t hs hst ht x y
  apply curvatureOperatorImageAt_finrank_le_at_later_time S hS hdim hst
    (fun _ hr => hreg ⟨hs.trans hr.1, hr.2.trans ht⟩)
    (fun r hr => hR r ⟨hs.trans hr.1, hr.2.trans ht⟩)

theorem curvatureOperatorImageAt_finrank_eq_at_positive_time
    [ConnectedSpace M]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hdim : Module.finrank ℝ E = 3)
    {T : ℝ} (hreg : Set.Icc 0 T ⊆ D.regular)
    (hR : ∀ t ∈ Set.Icc 0 T, ∀ x,
      (⟨metricRm04At (S.family.metric t) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩ :
          algebraicCurvatureTensorSubmodule (I := I) (M := M) x) ∈
            algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M)) :
    ∀ t ∈ Set.Ioc 0 T, ∀ x y,
      Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric t) x
        ⟨metricRm04At (S.family.metric t) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩) =
      Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric t) y
        ⟨metricRm04At (S.family.metric t) y,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) y⟩) := by
  intro t ht x y
  apply curvatureOperatorImageAt_finrank_eq_at_later_time S hS hdim ht.1
    (fun _ hr => hreg ⟨hr.1, hr.2.trans ht.2⟩)
    (fun r hr => hR r ⟨hr.1, hr.2.trans ht.2⟩)

theorem curvatureOperatorImageAt_finrank_trichotomy_at_positive_time
    [ConnectedSpace M]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hdim : Module.finrank ℝ E = 3)
    {T : ℝ} (hreg : Set.Icc 0 T ⊆ D.regular)
    (hR : ∀ t ∈ Set.Icc 0 T, ∀ x,
      (⟨metricRm04At (S.family.metric t) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩ :
          algebraicCurvatureTensorSubmodule (I := I) (M := M) x) ∈
            algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M)) :
    ∀ t ∈ Set.Ioc 0 T, ∀ x,
      let q := Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric t) x
        ⟨metricRm04At (S.family.metric t) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩)
      q = 0 ∨ q = 1 ∨ q = 3 := by
  intro t ht x
  apply curvatureOperatorImageAt_finrank_trichotomy_at_later_time S hS hdim ht.1
    (fun _ hr => hreg ⟨hr.1, hr.2.trans ht.2⟩)
    (fun r hr => hR r ⟨hr.1, hr.2.trans ht.2⟩)

end DifferentialGeometry.PDE.RicciFlow
