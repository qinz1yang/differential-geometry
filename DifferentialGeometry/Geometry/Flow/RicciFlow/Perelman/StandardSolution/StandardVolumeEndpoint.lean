import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardCostEndpoint
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CostChartLipComplete
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.ReducedVolumeBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardSolutionRealization
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.SpecificLimits.Basic
import DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram

set_option autoImplicit false

noncomputable section

open Bundle Filter Function MeasureTheory Set Manifold DifferentialGeometry
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.PDE.RicciFlow

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

private local instance : MeasurableSpace E3 := borel E3
private local instance : BorelSpace E3 := ⟨rfl⟩

private def standardVolumeIdentity : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 E3 1 where
  toPartialEquiv := PartialEquiv.refl E3
  open_source := isOpen_univ
  open_target := isOpen_univ
  contMDiffOn_toFun := contMDiff_id.contMDiffOn
  contMDiffOn_invFun := contMDiff_id.contMDiffOn

private theorem standardVolume_modelHaar
    (S : PartialStandardSolution) (T : ℝ) (x : E3) (tau : ℝ) :
    DifferentialGeometry.PDE.RicciFlow.redVolume S.toSolutionOn T x tau =
      ∫⁻ y : E3,
        ENNReal.ofReal (paramDensity (S.metric (T - tau)) standardVolumeIdentity y) *
          ENNReal.ofReal (redDensity S.toSolutionOn T x y tau)
        ∂modelHaar (E := E3) := by
  have h := riemVol_param_lint (S.metric (T - tau)) standardVolumeIdentity
    (fun y : E3 ↦ ENNReal.ofReal (redDensity S.toSolutionOn T x y tau))
    (B := univ) MeasurableSet.univ (subset_refl _)
  unfold DifferentialGeometry.PDE.RicciFlow.redVolume
  rw [show S.toSolutionOn.base.metric (T - tau) = S.metric (T - tau) from rfl]
  simpa only [standardVolumeIdentity, PartialEquiv.refl_coe, image_id, id_eq,
    Measure.restrict_univ] using h

private theorem standardVolume_metricDensity_continuousOn
    (S : PartialStandardSolution) (y : E3) :
    ContinuousOn
      (fun t : ℝ ↦ paramDensity (S.metric t) standardVolumeIdentity y) S.domain := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hmetric : Continuous (fun t : S.domain ↦ cartesianMetricFamily S.metric (t, y)) :=
    S.smooth.continuousOn.comp_continuous
      (continuous_subtype_val.prodMk continuous_const)
      (fun t ↦ ⟨t.property, mem_univ y⟩)
  have hgram : Continuous
      (fun t : S.domain ↦ paramGramMatrix (S.metric t) standardVolumeIdentity y) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    have hpair := (hmetric.clm_apply (continuous_const (y := DifferentialGeometry.Tensor.Coordinates.chartModelBasis E3 i))).clm_apply
      (continuous_const (y := DifferentialGeometry.Tensor.Coordinates.chartModelBasis E3 j))
    change Continuous (fun t : S.domain ↦
      (S.metric t).inner y (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E3 i) (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E3 j)) at hpair
    have heq : (fun t : S.domain ↦
        paramGramMatrix (S.metric t) standardVolumeIdentity y i j) =
        (fun t : S.domain ↦ (S.metric t).inner y
          (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E3 i) (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E3 j)) := by
      funext t
      change (S.metric t).inner y
        (mfderiv (𝓡 3) (𝓡 3) id y (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E3 i))
        (mfderiv (𝓡 3) (𝓡 3) id y (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E3 j)) = _
      rw [mfderiv_id]
      rfl
    rw [heq]
    exact hpair
  exact Real.continuous_sqrt.comp hgram.matrix_det

private theorem standardVolume_regular_slab
    (S : PartialStandardSolution) (T : ℝ) (hT : T ∈ S.domain)
    (tau : ℝ) (htauT : tau < T) :
    Icc (T - tau) T ⊆ (lifetimeInterval S.lifetime S.lifetime_pos).regular := by
  have hTlife := ((mem_lifetimeInterval_carrier S.lifetime S.lifetime_pos T).mp hT).2
  intro t ht
  exact (mem_lifetimeInterval_regular S.lifetime S.lifetime_pos t).mpr
    ⟨(sub_pos.mpr htauT).trans_le ht.1,
      (ENNReal.ofReal_le_ofReal ht.2).trans_lt hTlife⟩

private theorem standardVolume_integrand_measurable
    (S : PartialStandardSolution) (T : ℝ) (hT : T ∈ S.domain)
    (K : ℝ) (x : E3) (tau : ℝ) (htau : 0 < tau) (htauT : tau < T)
    (hRm : ∀ t ∈ Icc (T - tau) T, ∀ y : E3,
      normSq0S (I := 𝓡 3) (S.toSolutionOn.base.metric t) y 4
        (S.toSolutionOn.base.rm04 t y) ≤ K) :
    Measurable (fun y : E3 ↦
      ENNReal.ofReal (paramDensity (S.metric (T - tau)) standardVolumeIdentity y) *
        ENNReal.ofReal (redDensity S.toSolutionOn T x y tau)) := by
  let : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩
  have hcostChart := lCost_chart_lip_of_rm (I := 𝓡 3)
    S.toSolutionOn S.isSolutionOn K T (S.complete T hT) x tau htau
    (standardVolume_regular_slab S T hT tau htauT) hRm x
  have hcost : Continuous (fun y : E3 ↦ lCost S.toSolutionOn T x y tau) := by
    simpa only [extChartAt_model_space_eq_id,
      PartialEquiv.refl_target, PartialEquiv.refl_symm,
      PartialEquiv.refl_coe, Function.comp_id, continuousOn_univ] using hcostChart.continuousOn
  have hred : Continuous (fun y : E3 ↦ redDensity S.toSolutionOn T x y tau) := by
    unfold redDensity redLength
    exact Real.continuous_exp.comp
      (((hcost.div_const (2 * Real.sqrt tau)).neg.sub continuous_const).sub continuous_const)
  have hmetric : Continuous
      (fun y : E3 ↦ paramDensity (S.metric (T - tau)) standardVolumeIdentity y) :=
    continuousOn_univ.mp (paramDensity_contOn (S.metric (T - tau)) standardVolumeIdentity)
  exact (ENNReal.measurable_ofReal.comp hmetric.measurable).mul
    (ENNReal.measurable_ofReal.comp hred.measurable)

theorem PartialStandardSolution.redVolume_initial_le_liminf
    (S : PartialStandardSolution) (T : ℝ) (hT : T ∈ S.domain)
    (hTpos : 0 < T) (x : E3) (tau : ℕ → ℝ)
    (htau : ∀ n, 0 < tau n ∧ tau n < T)
    (hlim : Tendsto tau atTop (𝓝 T)) :
    DifferentialGeometry.PDE.RicciFlow.redVolume S.toSolutionOn T x T ≤
      liminf (fun n ↦ DifferentialGeometry.PDE.RicciFlow.redVolume
        S.toSolutionOn T x (tau n)) atTop := by
  have hTlife := ((mem_lifetimeInterval_carrier S.lifetime S.lifetime_pos T).mp hT).2
  have hcarrier : Icc (0 : ℝ) T ⊆ S.domain :=
    (Icc_subset_lifetimeInterval_iff S.lifetime S.lifetime_pos T hTpos.le).mpr hTlife
  have hzero : (0 : ℝ) ∈ S.domain := hcarrier ⟨le_rfl, hTpos.le⟩
  obtain ⟨K, _hK, hbound⟩ := S.curvature_bound T hTpos.le hTlife
  have hRmClosed : ∀ t ∈ Icc (0 : ℝ) T, ∀ y : E3,
      normSq0S (I := 𝓡 3) (S.toSolutionOn.base.metric t) y 4
        (S.toSolutionOn.base.rm04 t y) ≤ K ^ 2 := by
    intro t ht y
    change normSq0S (S.metric t) y 4 (metricRm04 (S.metric t) y) ≤ K ^ 2
    exact (Real.sqrt_le_iff.mp (hbound t ht y)).2
  let F : ℝ → E3 → ℝ≥0∞ := fun r y ↦
    ENNReal.ofReal (paramDensity (S.metric (T - r)) standardVolumeIdentity y) *
      ENNReal.ofReal (redDensity S.toSolutionOn T x y r)
  have hmeas (n : ℕ) : Measurable (F (tau n)) := by
    apply standardVolume_integrand_measurable S T hT (K ^ 2) x (tau n)
      (htau n).1 (htau n).2
    intro t ht y
    exact hRmClosed t ⟨(sub_nonneg.mpr (htau n).2.le).trans ht.1, ht.2⟩ y
  have hclock : Tendsto tau atTop (𝓝[Ioc (0 : ℝ) T] T) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨hlim, Eventually.of_forall (fun n ↦ ⟨(htau n).1, (htau n).2.le⟩)⟩
  have hphysical : Tendsto (fun n ↦ T - tau n) atTop (𝓝[S.domain] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨by simpa only [sub_self] using (tendsto_const_nhds (x := T)).sub hlim, ?_⟩
    exact Eventually.of_forall (fun n ↦ hcarrier
      ⟨(sub_pos.mpr (htau n).2).le, sub_le_self T (htau n).1.le⟩)
  have hpoint (y : E3) : F T y ≤ liminf (fun n ↦ F (tau n) y) atTop := by
    have hmetric : Tendsto
        (fun n ↦ ENNReal.ofReal
          (paramDensity (S.metric (T - tau n)) standardVolumeIdentity y))
        atTop (𝓝 (ENNReal.ofReal (paramDensity (S.metric 0) standardVolumeIdentity y))) :=
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        ((standardVolume_metricDensity_continuousOn S y 0 hzero).tendsto.comp hphysical)
    have hweight : ENNReal.ofReal (redDensity S.toSolutionOn T x y T) ≤
        liminf (fun n ↦ ENNReal.ofReal
          (redDensity S.toSolutionOn T x y (tau n))) atTop :=
      (S.redDensity_lowerSemicontinuousWithinAt T hT x y T hTpos le_rfl).le_liminf.trans
        hclock.liminf_le_liminf_comp
    have hmul := ENNReal.le_liminf_mul
      (u := fun n ↦ ENNReal.ofReal
        (paramDensity (S.metric (T - tau n)) standardVolumeIdentity y))
      (v := fun n ↦ ENNReal.ofReal (redDensity S.toSolutionOn T x y (tau n)))
      (f := atTop)
    rw [hmetric.liminf_eq, Pi.mul_def] at hmul
    simpa only [F, sub_self, Pi.mul_apply] using
      (mul_le_mul (le_rfl : ENNReal.ofReal (paramDensity (S.metric 0) standardVolumeIdentity y) ≤ _)
        hweight (by positivity) (by positivity)).trans hmul
  calc
    DifferentialGeometry.PDE.RicciFlow.redVolume S.toSolutionOn T x T =
        ∫⁻ y : E3, F T y ∂modelHaar (E := E3) := standardVolume_modelHaar S T x T
    _ ≤ ∫⁻ y : E3, liminf (fun n ↦ F (tau n) y) atTop ∂modelHaar (E := E3) :=
      lintegral_mono hpoint
    _ ≤ liminf (fun n ↦ ∫⁻ y : E3, F (tau n) y ∂modelHaar (E := E3)) atTop :=
      lintegral_liminf_le hmeas
    _ = liminf (fun n ↦ DifferentialGeometry.PDE.RicciFlow.redVolume
        S.toSolutionOn T x (tau n)) atTop := by
      congr 1
      funext n
      exact (standardVolume_modelHaar S T x (tau n)).symm

theorem PartialStandardSolution.redVolume_initial_le
    (S : PartialStandardSolution) (T : ℝ) (hT : T ∈ S.domain)
    (x : E3) (tau : ℝ) (htau : 0 < tau) (htauT : tau < T) :
    DifferentialGeometry.PDE.RicciFlow.redVolume S.toSolutionOn T x T ≤
      DifferentialGeometry.PDE.RicciFlow.redVolume S.toSolutionOn T x tau := by
  let : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩
  have hTpos : 0 < T := htau.trans htauT
  have hTlife := ((mem_lifetimeInterval_carrier S.lifetime S.lifetime_pos T).mp hT).2
  obtain ⟨K, _hK, hbound⟩ := S.curvature_bound T hTpos.le hTlife
  have hRm : ∀ sigma : ℝ, 0 < sigma →
      Icc (T - sigma) T ⊆ (lifetimeInterval S.lifetime S.lifetime_pos).regular →
      ∃ K' : ℝ, ∀ t ∈ Icc (T - sigma) T, ∀ y : E3,
        normSq0S (I := 𝓡 3) (S.toSolutionOn.base.metric t) y 4
          (S.toSolutionOn.base.rm04 t y) ≤ K' := by
    intro sigma _hsigma hslab
    refine ⟨K ^ 2, ?_⟩
    intro t ht y
    have htpos := ((mem_lifetimeInterval_regular S.lifetime S.lifetime_pos t).mp
      (hslab ht)).1
    change normSq0S (S.metric t) y 4 (metricRm04 (S.metric t) y) ≤ K ^ 2
    exact (Real.sqrt_le_iff.mp (hbound t ⟨htpos.le, ht.2⟩ y)).2
  let u : ℕ → ℝ := fun n ↦ T - (T - tau) * (1 / ((n : ℝ) + 1))
  have hu (n : ℕ) : tau ≤ u n ∧ u n < T := by
    have hden : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hfracpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hfracle : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 :=
      (div_le_one hden).mpr (by linarith only [Nat.cast_nonneg (α := ℝ) n])
    have hdiff : 0 < T - tau := sub_pos.mpr htauT
    have hprod := mul_le_mul_of_nonneg_left hfracle hdiff.le
    have hprodpos := mul_pos hdiff hfracpos
    constructor <;> dsimp only [u] <;> nlinarith
  have hup (n : ℕ) : 0 < u n ∧ u n < T := ⟨htau.trans_le (hu n).1, (hu n).2⟩
  have hulim : Tendsto u atTop (𝓝 T) := by
    simpa only [u, mul_zero, sub_zero] using
      (tendsto_const_nhds.sub (tendsto_const_nhds.mul
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))))
  have hanti (n : ℕ) :
      DifferentialGeometry.PDE.RicciFlow.redVolume S.toSolutionOn T x (u n) ≤
        DifferentialGeometry.PDE.RicciFlow.redVolume S.toSolutionOn T x tau :=
    redVolume_anti_of_rm (I := 𝓡 3) S.toSolutionOn S.isSolutionOn T
      (S.complete T hT) x hRm htau (hu n).1
      (standardVolume_regular_slab S T hT (u n) (hu n).2)
  exact (S.redVolume_initial_le_liminf T hT hTpos x u hup hulim).trans
    (liminf_le_of_frequently_le (Eventually.of_forall hanti).frequently)

theorem PartialStandardSolution.redVolume_initial_le_one
    (S : PartialStandardSolution) (T : ℝ) (hT : T ∈ S.domain)
    (hTpos : 0 < T) (x : E3) :
    DifferentialGeometry.PDE.RicciFlow.redVolume S.toSolutionOn T x T ≤ 1 := by
  let : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩
  have hTlife := ((mem_lifetimeInterval_carrier S.lifetime S.lifetime_pos T).mp hT).2
  obtain ⟨K, _hK, hbound⟩ := S.curvature_bound T hTpos.le hTlife
  have hRm : ∀ sigma : ℝ, 0 < sigma →
      Icc (T - sigma) T ⊆ (lifetimeInterval S.lifetime S.lifetime_pos).regular →
      ∃ K' : ℝ, ∀ t ∈ Icc (T - sigma) T, ∀ y : E3,
        normSq0S (I := 𝓡 3) (S.toSolutionOn.base.metric t) y 4
          (S.toSolutionOn.base.rm04 t y) ≤ K' := by
    intro sigma _hsigma hslab
    refine ⟨K ^ 2, ?_⟩
    intro t ht y
    have htpos := ((mem_lifetimeInterval_regular S.lifetime S.lifetime_pos t).mp
      (hslab ht)).1
    change normSq0S (S.metric t) y 4 (metricRm04 (S.metric t) y) ≤ K ^ 2
    exact (Real.sqrt_le_iff.mp (hbound t ⟨htpos.le, ht.2⟩ y)).2
  have hhalfpos : 0 < T / 2 := by positivity
  have hhalfT : T / 2 < T := by linarith
  exact (S.redVolume_initial_le T hT x (T / 2) hhalfpos hhalfT).trans
    (redVolume_le_one_of_rm (I := 𝓡 3) S.toSolutionOn S.isSolutionOn T
      (S.complete T hT) x hRm (T / 2) hhalfpos
      (standardVolume_regular_slab S T hT (T / 2) hhalfT))

end DifferentialGeometry.PDE.RicciFlow

end
