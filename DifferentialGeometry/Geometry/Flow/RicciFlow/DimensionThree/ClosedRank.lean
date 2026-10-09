import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Uhlenbeck.ClosedCurvatureEvolution
import DifferentialGeometry.Geometry.Curvature.DimensionThree.ExteriorRank
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.ExteriorPositivity
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureReactionRegularity
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureReactionPositivity
import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.SystemSource
import DifferentialGeometry.Geometry.Metric.BundlePullbackSmooth
import DifferentialGeometry.Geometry.Connection.ModelNorm
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.RankContinuity

noncomputable section

open Bundle Set CovariantDerivative
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Tensor0SBundle (MetricFiberData)

section IsometricBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [SigmaCompactSpace M] [ConnectedSpace M]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  [IsContMDiffRiemannianBundle I ∞ F V]

private theorem curvature_rank_spreading_on_closed_interval
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a T : ℝ} (ha : a < 0) (hT : 0 < T)
    (hslab : Icc a T ⊆ D.carrier) (hreg : Ioo a T ⊆ D.regular)
    (hdim : Module.finrank ℝ F = 3)
    (ι₀ : ∀ x, V x ≃L[ℝ] TangentSpace I x)
    (hι₀ : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (F →L[ℝ] E) x (ι₀ x).toContinuousLinearMap))
    (h₀ : ∀ x v w, (S.family.metric 0).inner x (ι₀ x v) (ι₀ x w) = ⟪v, w⟫)
    (hR : ∀ t ∈ Icc 0 T, ∀ x,
      metricAlgebraicCurvatureTensorAt (S.family.metric t) x ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M)) :
    ∀ s t, 0 ≤ s → s < t → t ≤ T → ∀ x y,
      Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric s) x
        (metricAlgebraicCurvatureTensorAt (S.family.metric s) x)) ≤
      Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric t) y
        (metricAlgebraicCurvatureTensorAt (S.family.metric t) y)) := by
  classical
  let _ : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
  let _ := Bundle.ExteriorPower.totalSpaceTopology F V 2
  let _ := Bundle.ExteriorPower.fiberBundle F V 2
  let _ := Bundle.ExteriorPower.vector_bundle F V 2
  let _ := Bundle.ExteriorPower.contMDiffVectorBundle (IB := I) (n := ∞) F V 2
  let _ := Bundle.ExteriorPower.isContMDiffRiemannianBundle (IB := I) (n := ∞) F V 2
  obtain ⟨ι, _, hmetric, A, hA, _, _, hAcont, hevol⟩ :=
    exists_uhlenbeck_curvatureOperator_sections_evolution_on_closed_interval
      (F := F) (V := V) S hS ha hT hslab hreg ⟨le_rfl, hT.le⟩ hdim ι₀ hι₀ h₀
  let cov₀ (q : ℝ) (hq : q ∈ Ioo 0 T) := (hevol q hq).choose
  have hmid : T / 2 ∈ Ioo 0 T := ⟨half_pos hT, half_lt_self hT⟩
  let cov := fun q => if hq : q ∈ Ioo 0 T then cov₀ q hq else cov₀ (T / 2) hmid
  have hcovsmooth : ∀ q ∈ Ioo 0 T, ContMDiffCovariantDerivative (cov q) ∞ := by
    intro q hq
    simpa only [cov, dite_eq_left hq, cov₀] using (hevol q hq).choose_spec.1
  have hcovmetric : ∀ q ∈ Ioo 0 T, (cov q).IsMetricCompatible := by
    intro q hq
    simpa only [cov, dite_eq_left hq, cov₀] using (hevol q hq).choose_spec.2.1
  have hpos : ∀ q ∈ Icc 0 T, ∀ x, (A q x).IsPositive := by
    intro q hq x
    rw [hA q hq x]
    exact traceNormalizedCurvatureEndomorphism_pullback_isPositive_of_mem_nonnegativeCone
      (metricAlgebraicCurvatureTensorAt (S.family.metric q) x) (hR q hq x)
      (ι q x).toContinuousLinearMap
  let reaction := fun (_ : ℝ) (x : M) (B : (⋀[ℝ]^2 (V x)) →L[ℝ] ⋀[ℝ]^2 (V x)) =>
    (curvatureOperatorReactionEndomorphism3 B.toLinearMap).toContinuousLinearMap
  have hzero : ContinuousOn (fun p : ℝ × M =>
      (TotalSpace.mk' E p.2 (0 : TangentSpace I p.2) : TangentBundle I M))
      (Icc 0 T ×ˢ (univ : Set M)) :=
    ((Bundle.contMDiff_zeroSection ℝ (TangentSpace I) (IB := I) (F := E)
      (n := ∞)).continuous.comp continuous_snd).continuousOn
  intro s t hs hst ht x y
  have hmain := PositiveSystem.finrank_range_le_at_later_time_of_contMDiffOn_on_Icc
    S.family.metric cov (solution_metricCLMSection_contMDiffOn_closed S hS ha hT hslab hreg)
    hcovsmooth hcovmetric A hpos hAcont (fun _ _ => 0) hzero reaction
    (fun q _ z B hB v _ =>
      (curvatureOperatorReactionEndomorphism3_isPositive hB.toLinearMap).inner_nonneg_left v)
    (by
      intro l u hl hlu hu K hK R hR
      obtain ⟨L, hL⟩ := curvatureOperatorReactionEndomorphism3_exists_uniform_lipschitzOn_closedBall
        (fun z => ⋀[ℝ]^2 (V z)) (Module.finrank ℝ (⋀[ℝ]^2 F))
        (fun z => VectorBundle.finrank_eq ℝ (⋀[ℝ]^2 F) (fun z => ⋀[ℝ]^2 (V z)) z) R
      refine ⟨L, L.coe_nonneg, ?_⟩
      intro q hq z hz B C hB hC hBn hCn
      exact (hL z).norm_sub_le (mem_closedBall_zero_iff.mpr hBn)
        (mem_closedBall_zero_iff.mpr hCn))
    (by
      intro q hq z
      simpa only [cov, dite_eq_left hq, cov₀, map_zero, add_zero, reaction] using
        (hevol q hq).choose_spec.2.2 z) hs hst ht x y
  have hsT : s ∈ Icc 0 T := ⟨hs, hst.le.trans ht⟩
  have htT : t ∈ Icc 0 T := ⟨hs.trans hst.le, ht⟩
  rw [hA s hsT x, hA t htT y] at hmain
  have hx := traceNormalizedCurvatureEndomorphism_pullback_finrank_range
    ((VectorBundle.finrank_eq ℝ F V x).trans hdim) (S.family.metric s) x
    (metricAlgebraicCurvatureTensorAt (S.family.metric s) x) (ι s x) (hmetric s hsT x)
  have hy := traceNormalizedCurvatureEndomorphism_pullback_finrank_range
    ((VectorBundle.finrank_eq ℝ F V y).trans hdim) (S.family.metric t) y
    (metricAlgebraicCurvatureTensorAt (S.family.metric t) y) (ι t y) (hmetric t htT y)
  exact hx ▸ hy ▸ hmain

end IsometricBundle

section MetricBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  {F : Type*} [oldNorm : NormedAddCommGroup F] [oldSpace : NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]

private theorem curvature_rank_spreading_metric_on_closed_interval
    [ConnectedSpace M]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hdim : Module.finrank ℝ F = 3)
    {a T : ℝ} (ha : a < 0) (hT : 0 < T)
    (hslab : Set.Icc a T ⊆ D.carrier) (hreg : Set.Ioo a T ⊆ D.regular)
    (h : ContMDiffRiemannianMetric I ∞ F V)
    (ι₀ : ∀ x, V x ≃L[ℝ] TangentSpace I x)
    (hι₀ : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (F →L[ℝ] E) x (ι₀ x).toContinuousLinearMap))
    (h₀ : ∀ x v w, (S.family.metric 0).inner x (ι₀ x v) (ι₀ x w) = h.inner x v w)
    (hR : ∀ t ∈ Set.Icc 0 T, ∀ x,
      metricAlgebraicCurvatureTensorAt (S.family.metric t) x ∈
            algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M)) :
    ∀ s t, 0 ≤ s → s < t → t ≤ T → ∀ x y,
      Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric s) x
        (metricAlgebraicCurvatureTensorAt (S.family.metric s) x)) ≤
      Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric t) y
        (metricAlgebraicCurvatureTensorAt (S.family.metric t) y)) := by
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
  exact curvature_rank_spreading_on_closed_interval (F := F) (V := V)
    S hS ha hT hslab hreg hdim ι₀ hιnew h₀ hR

end MetricBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [SigmaCompactSpace M] [ConnectedSpace M]

theorem curvatureOperatorImageAt_finrank_le_at_later_time_on_closed_interval
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hdim : Module.finrank ℝ E = 3)
    {a s t : ℝ} (has : a < s) (hst : s < t)
    (hslab : Icc a t ⊆ D.carrier) (hreg : Ioo a t ⊆ D.regular)
    (hR : ∀ r ∈ Icc s t, ∀ x,
      metricAlgebraicCurvatureTensorAt (S.family.metric r) x ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M)) :
    ∀ x y,
      Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric s) x
        (metricAlgebraicCurvatureTensorAt (S.family.metric s) x)) ≤
      Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric t) y
        (metricAlgebraicCurvatureTensorAt (S.family.metric t) y)) := by
  let U := S.timeShift s
  have hU := isSolutionOn_timeShift hS s
  have hcar : Icc (a - s) (t - s) ⊆ (D.timeShift s).carrier := by
    intro r hr
    exact hslab ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have hregular : Ioo (a - s) (t - s) ⊆ (D.timeShift s).regular := by
    intro r hr
    exact hreg ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have hcone : ∀ r ∈ Icc 0 (t - s), ∀ x,
      metricAlgebraicCurvatureTensorAt (U.family.metric r) x ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M) := by
    intro r hr x
    exact hR (r + s) ⟨by linarith [hr.1], by linarith [hr.2]⟩ x
  have h := curvature_rank_spreading_metric_on_closed_interval (F := E) (V := TangentSpace I)
    U hU hdim (sub_neg.mpr has) (sub_pos.mpr hst) hcar hregular (U.family.metric 0)
    (fun x => ContinuousLinearEquiv.refl ℝ (TangentSpace I x))
    (show ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E) x
        (ContinuousLinearMap.id ℝ (TangentSpace I x))) from
      (contMDiff_id : ContMDiff I I ∞ (fun x : M => x)).clm_bundle_id)
    (fun _ _ _ => rfl) hcone
  let q (r : ℝ) (z : M) := Module.finrank ℝ
    (curvatureOperatorImageAt (S.family.metric r) z
      (metricAlgebraicCurvatureTensorAt (S.family.metric r) z))
  intro x y
  have hout : q (0 + s) x ≤ q (t - s + s) y :=
    h 0 (t - s) le_rfl (sub_pos.mpr hst) le_rfl x y
  simpa only [zero_add, sub_add_cancel] using hout

theorem curvatureOperatorImageAt_finrank_eq_at_right_endpoint
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hdim : Module.finrank ℝ E = 3)
    {a b : ℝ} (hab : a < b)
    (hslab : Icc a b ⊆ D.carrier) (hreg : Ioo a b ⊆ D.regular)
    (hR : ∀ r ∈ Icc a b, ∀ x,
      metricAlgebraicCurvatureTensorAt (S.family.metric r) x ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M)) :
    ∀ x y,
      Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric b) x
        (metricAlgebraicCurvatureTensorAt (S.family.metric b) x)) =
      Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric b) y
        (metricAlgebraicCurvatureTensorAt (S.family.metric b) y)) := by
  let c := (a + b) / 2
  let T := b - c
  have hac : a < c := by dsimp only [c]; linarith
  have hcb : c < b := by dsimp only [c]; linarith
  have hT : 0 < T := sub_pos.mpr hcb
  let U := S.timeShift c
  have hU := isSolutionOn_timeShift hS c
  let rank := fun r x => Module.finrank ℝ (curvatureOperatorImageAt (U.family.metric r) x
    (metricAlgebraicCurvatureTensorAt (U.family.metric r) x))
  have hcar : Icc 0 T ⊆ (D.timeShift c).carrier := by
    intro r hr
    exact hslab ⟨by linarith [hr.1], by dsimp only [T] at hr; linarith [hr.2]⟩
  have hlower : ∀ r ∈ Ioc 0 T, ∀ x,
      ∀ᶠ s in 𝓝[Icc 0 T] r, rank r x ≤ rank s x := by
    intro r hr x
    exact (curvatureOperatorImageAt_finrank_eventually_ge U hU hdim x
      (hcar ⟨hr.1.le, hr.2⟩)).filter_mono (nhdsWithin_mono r hcar)
  have hspread : ∀ {s t : ℝ}, 0 ≤ s → s < t → t ≤ T → ∀ x y,
      rank s x ≤ rank t y := by
    intro s t hs hst ht x y
    apply curvatureOperatorImageAt_finrank_le_at_later_time_on_closed_interval
      U hU hdim (a := a - c) (by linarith) hst
    · intro r hr
      exact hslab ⟨by linarith [hr.1], by dsimp only [T] at ht; linarith [hr.2]⟩
    · intro r hr
      exact hreg ⟨by linarith [hr.1], by dsimp only [T] at ht; linarith [hr.2]⟩
    · intro r hr z
      exact hR (r + c) ⟨by linarith [hr.1], by dsimp only [T] at ht; linarith [hr.2]⟩ z
  intro x y
  have heq := rank_eq_at_positive_time_of_spreading
    hlower hspread (show T ∈ Ioc 0 T from ⟨hT, le_rfl⟩) x y
  let q (r : ℝ) (z : M) := Module.finrank ℝ
    (curvatureOperatorImageAt (S.family.metric r) z
      (metricAlgebraicCurvatureTensorAt (S.family.metric r) z))
  change q (T + c) x = q (T + c) y at heq
  have hTc : T + c = b := sub_add_cancel b c
  simpa only [hTc] using heq

end DifferentialGeometry.PDE.RicciFlow
