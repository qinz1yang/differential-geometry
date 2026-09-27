import DifferentialGeometry.Analysis.Sobolev.WithBoundary.Chart.WeakDerivative
import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletCompactness
import DifferentialGeometry.Analysis.Sobolev.WithBoundary.Chart.Completeness

noncomputable section

open Manifold MeasureTheory Filter
open scoped Manifold Topology ContDiff ENNReal

namespace DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

local notation "I_hs" => modelWithCornersEuclideanHalfSpace n

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

open DifferentialGeometry.Integral.Measure

private theorem exists_smooth_approximation_H1ComplDirichletToLp
    (g : SmoothRiemannianMetric I_hs M) (u : H1ComplDirichlet g) :
    ∃ s : ℕ → SmoothScalarDirichlet g,
      Tendsto (fun k => smoothToH1ComplDirichlet g (s k)) atTop (𝓝 u) ∧
      DifferentialGeometry.Analysis.Sobolev.WithBoundary.MemWkpChart
        (n := n) (M := M) 1 2 (H1ComplDirichletToLp g u) ∧
      Tendsto (fun k => DifferentialGeometry.Analysis.Sobolev.WithBoundary.wkpNormChart
        (n := n) (M := M) 1 2
        ((s k).toFun - (H1ComplDirichletToLp g u : M → ℝ))) atTop (𝓝 0) := by
  classical
  obtain ⟨v, hv, hvlim⟩ := mem_closure_iff_seq_limit.mp
    ((denseRange_smoothToH1ComplDirichlet g) u)
  choose s hs using hv
  have hslim : Tendsto (fun k => smoothToH1ComplDirichlet g (s k)) atTop (𝓝 u) := by
    simpa only [hs] using hvlim
  let w : ℕ → DirichletChartWkp (n := n) (M := M) :=
    fun k => smoothToDirichletChartWkp g (s k)
  have hwlim : Tendsto (fun k => (w k : H1ComplDirichletChartWkp (n := n) (M := M)))
      atTop (𝓝 (H1ComplDirichletToChartWkp g u)) := by
    simpa only [Function.comp_def, H1ComplDirichletToChartWkp_smoothToH1ComplDirichlet] using
      (H1ComplDirichletToChartWkp g).continuous.continuousAt.tendsto.comp hslim
  have hwcauchy : CauchySeq w := by
    apply (UniformSpace.Completion.isUniformInducing_coe
      (DirichletChartWkp (n := n) (M := M))).cauchy_map_iff.mp
    simpa only [CauchySeq, Filter.map_map, Function.comp_def] using hwlim.cauchySeq
  have hLp : Tendsto (fun k => smoothToLpDirichlet g (s k)) atTop
      (𝓝 (H1ComplDirichletToLp g u)) := by
    simpa only [Function.comp_def, H1ComplDirichletToLp_smoothToH1ComplDirichlet] using
      (H1ComplDirichletToLp g).continuous.continuousAt.tendsto.comp hslim
  have heLp : Tendsto (fun k => eLpNorm
      ((s k).toFun - (H1ComplDirichletToLp g u : M → ℝ)) 2
      (riemannianVolumeMeasure I_hs M g)) atTop (𝓝 0) := by
    have h := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'
      (fun k => smoothToLpDirichlet g (s k)) (H1ComplDirichletToLp g u)).mp hLp
    convert h using 1
    funext k
    apply eLpNorm_congr_ae
    have hsLp : (smoothToLpDirichlet g (s k) : M → ℝ) =ᵐ[
        riemannianVolumeMeasure I_hs M g] (s k).toFun :=
      MemLp.coeFn_toLp (s k).memLp_two
    filter_upwards [hsLp] with x hx
    simp only [Pi.sub_apply]
    rw [hx]
  have hcharts : ∀ α : M,
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace (d := n) 1 2
        (DifferentialGeometry.Analysis.Sobolev.WithBoundary.chartPushed
          (n := n) (M := M) (chartAtlasPOU I_hs M) α (H1ComplDirichletToLp g u))
        (DifferentialGeometry.Analysis.Sobolev.WithBoundary.chartTargetEuclid
          (n := n) (M := M) α) ∧
      Tendsto (fun k => DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace
        (d := n) 1 2
        (DifferentialGeometry.Analysis.Sobolev.WithBoundary.chartPushed
          (n := n) (M := M) (chartAtlasPOU I_hs M) α
          ((s k).toFun - (H1ComplDirichletToLp g u : M → ℝ)))
        (DifferentialGeometry.Analysis.Sobolev.WithBoundary.chartTargetEuclid
          (n := n) (M := M) α)) atTop (𝓝 0) := by
    intro α
    obtain ⟨z, hzmem, hzlim⟩ :=
      DifferentialGeometry.Analysis.Sobolev.WithBoundary.exists_chart_limit
        (n := n) (M := M) (by norm_num : 1 ≤ (2 : ℝ≥0∞))
        (DifferentialGeometry.Analysis.Sobolev.WithBoundary.wkpNormChart_cauchy_of_seminormCauchySeq
          hwcauchy) α
    have hzmeasure := DifferentialGeometry.Analysis.Sobolev.WithBoundary.chartPushed_tendstoInMeasure
      (n := n) (M := M) (by norm_num : 1 ≤ (2 : ℝ≥0∞)) (by norm_num)
      α hzmem hzlim
    have humeasure :=
      DifferentialGeometry.Analysis.Sobolev.WithBoundary.EquivalenceReverse.tendstoInMeasure_chartPushed_of_tendsto_eLpNorm
        (n := n) (M := M) g α (by norm_num : 1 ≤ (2 : ℝ≥0∞)) (by norm_num)
        (fun k => (s k).smooth.continuous.measurable)
        (Lp.stronglyMeasurable (H1ComplDirichletToLp g u)).measurable heLp
    have hae : z =ᵐ[volume.restrict
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
          (DifferentialGeometry.Analysis.Sobolev.WithBoundary.chartTargetEuclid
            (n := n) (M := M) α))]
        DifferentialGeometry.Analysis.Sobolev.WithBoundary.chartPushed
          (n := n) (M := M) (chartAtlasPOU I_hs M) α (H1ComplDirichletToLp g u) :=
      tendstoInMeasure_ae_unique hzmeasure humeasure
    have hmem := (DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace_congr_ae
      (by norm_num : 1 ≤ (2 : ℝ≥0∞))
      (DifferentialGeometry.Analysis.Sobolev.WithBoundary.chartTargetEuclid_isHalfSpaceRelOpen
        (n := n) (M := M) α) hae).mp hzmem
    refine ⟨hmem, ?_⟩
    convert hzlim using 1
    funext k
    apply DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_congr_ae
      (by norm_num : 1 ≤ (2 : ℝ≥0∞))
      (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace_isOpen
        (DifferentialGeometry.Analysis.Sobolev.WithBoundary.chartTargetEuclid_isHalfSpaceRelOpen
          (n := n) (M := M) α))
    filter_upwards [hae] with y hy
    change _ * ((s k).toFun _ - (H1ComplDirichletToLp g u) _) =
      _ * (s k).toFun _ - z y
    rw [hy]
    simp only [DifferentialGeometry.Analysis.Sobolev.WithBoundary.chartPushed, mul_sub]
  exact ⟨s, hslim, fun α => (hcharts α).1,
    DifferentialGeometry.Analysis.Sobolev.WithBoundary.tendsto_wkpNormChart_zero
      (by norm_num : 1 ≤ (2 : ℝ≥0∞)) (fun α => (hcharts α).2)⟩

theorem memWkpChart_H1ComplDirichletToLp
    (g : SmoothRiemannianMetric I_hs M) (u : H1ComplDirichlet g) :
    DifferentialGeometry.Analysis.Sobolev.WithBoundary.MemWkpChart
      (n := n) (M := M) 1 2 (H1ComplDirichletToLp g u) := by
  obtain ⟨_, _, hmem, _⟩ := exists_smooth_approximation_H1ComplDirichletToLp g u
  exact hmem

theorem H1ComplDirichletToChartWkp_eq
    (g : SmoothRiemannianMetric I_hs M) (u : H1ComplDirichlet g) :
    H1ComplDirichletToChartWkp g u =
      (UniformSpace.Completion.toComplL : DirichletChartWkp (n := n) (M := M) →L[ℝ]
        H1ComplDirichletChartWkp (n := n) (M := M))
        ⟨(H1ComplDirichletToLp g u : M → ℝ), memWkpChart_H1ComplDirichletToLp g u⟩ := by
  obtain ⟨s, hslim, hmem, hW⟩ := exists_smooth_approximation_H1ComplDirichletToLp g u
  let v : DirichletChartWkp (n := n) (M := M) :=
    ⟨(H1ComplDirichletToLp g u : M → ℝ), hmem⟩
  have hWlim : Tendsto (fun k => smoothToDirichletChartWkp g (s k)) atTop (𝓝 v) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have h := (ENNReal.tendsto_toReal (by norm_num : (0 : ℝ≥0∞) ≠ ⊤)).comp hW
    have hn : ∀ k, ‖smoothToDirichletChartWkp g (s k) - v‖ =
        (DifferentialGeometry.Analysis.Sobolev.WithBoundary.wkpNormChart
          (n := n) (M := M) 1 2
          ((s k).toFun - (H1ComplDirichletToLp g u : M → ℝ))).toReal := by
      intro k
      rfl
    simpa only [hn, Function.comp_def, ENNReal.toReal_zero] using h
  have hcomplim : Tendsto
      (fun k => (smoothToDirichletChartWkp g (s k) : H1ComplDirichletChartWkp (n := n) (M := M)))
      atTop (𝓝 (v : H1ComplDirichletChartWkp (n := n) (M := M))) :=
    (UniformSpace.Completion.continuous_coe
      (DirichletChartWkp (n := n) (M := M))).continuousAt.tendsto.comp hWlim
  have hmaplim : Tendsto
      (fun k => (smoothToDirichletChartWkp g (s k) : H1ComplDirichletChartWkp (n := n) (M := M)))
      atTop (𝓝 (H1ComplDirichletToChartWkp g u)) := by
    simpa only [Function.comp_def, H1ComplDirichletToChartWkp_smoothToH1ComplDirichlet] using
      (H1ComplDirichletToChartWkp g).continuous.continuousAt.tendsto.comp hslim
  have heq := tendsto_nhds_unique hmaplim hcomplim
  simpa only [UniformSpace.Completion.coe_toComplL] using heq

theorem norm_H1ComplDirichletToChartWkp_eq
    (g : SmoothRiemannianMetric I_hs M) (u : H1ComplDirichlet g) :
    ‖H1ComplDirichletToChartWkp g u‖ =
      (DifferentialGeometry.Analysis.Sobolev.WithBoundary.wkpNormChart
        (n := n) (M := M) 1 2 (H1ComplDirichletToLp g u)).toReal := by
  let v : DirichletChartWkp (n := n) (M := M) :=
    ⟨(H1ComplDirichletToLp g u : M → ℝ), memWkpChart_H1ComplDirichletToLp g u⟩
  have hvnorm : ‖(UniformSpace.Completion.toComplL :
      DirichletChartWkp (n := n) (M := M) →L[ℝ]
        H1ComplDirichletChartWkp (n := n) (M := M)) v‖ = ‖v‖ := by
    simpa only [UniformSpace.Completion.coe_toComplL] using UniformSpace.Completion.norm_coe v
  calc
    ‖H1ComplDirichletToChartWkp g u‖ =
        ‖(UniformSpace.Completion.toComplL :
          DirichletChartWkp (n := n) (M := M) →L[ℝ]
            H1ComplDirichletChartWkp (n := n) (M := M)) v‖ :=
      congrArg norm (H1ComplDirichletToChartWkp_eq g u)
    _ = ‖v‖ := hvnorm
    _ = _ := rfl


theorem wkpNormChart_H1ComplDirichletToLp_le
    (g : SmoothRiemannianMetric I_hs M) (u : H1ComplDirichlet g) :
    DifferentialGeometry.Analysis.Sobolev.WithBoundary.wkpNormChart
      (n := n) (M := M) 1 2 (H1ComplDirichletToLp g u) ≤
        ENNReal.ofReal ‖H1ComplDirichletToChartWkp (n := n) (M := M) g‖ * ENNReal.ofReal ‖u‖ := by
  have hfinite := (DifferentialGeometry.Analysis.Sobolev.WithBoundary.wkpNormChart_lt_top_of_memWkpChart
    (by norm_num : 1 ≤ (2 : ℝ≥0∞)) (memWkpChart_H1ComplDirichletToLp g u)).ne
  calc
    DifferentialGeometry.Analysis.Sobolev.WithBoundary.wkpNormChart
        (n := n) (M := M) 1 2 (H1ComplDirichletToLp g u) =
        ENNReal.ofReal ‖H1ComplDirichletToChartWkp g u‖ := by
      rw [norm_H1ComplDirichletToChartWkp_eq, ENNReal.ofReal_toReal hfinite]
    _ ≤ ENNReal.ofReal (‖H1ComplDirichletToChartWkp (n := n) (M := M) g‖ * ‖u‖) :=
      ENNReal.ofReal_le_ofReal ((H1ComplDirichletToChartWkp g).le_opNorm u)
    _ = _ := ENNReal.ofReal_mul (norm_nonneg _)


noncomputable def dirichletChartWeakPartialLp
    (g : SmoothRiemannianMetric I_hs M) (α : M) (i : Fin n) :
    H1ComplDirichlet g →L[ℝ]
      Lp ℝ 2 (volume.restrict
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
          (DifferentialGeometry.Analysis.Sobolev.WithBoundary.chartTargetEuclid
            (n := n) (M := M) α))) :=
  (DifferentialGeometry.Analysis.Sobolev.WithBoundary.chartIterWeakPartialComplLp
    (k := 1) (p := 2) (Nat.le_refl 1) α (fun _ => i)).comp
      (H1ComplDirichletToChartWkp g)

theorem dirichletChartWeakPartialLp_apply_coeFn
    (g : SmoothRiemannianMetric I_hs M) (α : M) (i : Fin n) (u : H1ComplDirichlet g) :
    (dirichletChartWeakPartialLp g α i u : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[
      volume.restrict
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
          (DifferentialGeometry.Analysis.Sobolev.WithBoundary.chartTargetEuclid
            (n := n) (M := M) α))]
      DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartialOrZero 2 i
        (DifferentialGeometry.Analysis.Sobolev.WithBoundary.chartPushed
          (chartAtlasPOU I_hs M) α (H1ComplDirichletToLp g u))
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
          (DifferentialGeometry.Analysis.Sobolev.WithBoundary.chartTargetEuclid α)) := by
  let v : DirichletChartWkp (n := n) (M := M) :=
    ⟨(H1ComplDirichletToLp g u : M → ℝ), memWkpChart_H1ComplDirichletToLp g u⟩
  have heq : dirichletChartWeakPartialLp g α i u =
      DifferentialGeometry.Analysis.Sobolev.WithBoundary.chartIterWeakPartialLp
        (p := 2) (Nat.le_refl 1) α (fun _ => i) v := by
    change DifferentialGeometry.Analysis.Sobolev.WithBoundary.chartIterWeakPartialComplLp
      (p := 2) (Nat.le_refl 1) α (fun _ => i) (H1ComplDirichletToChartWkp g u) = _
    calc
      DifferentialGeometry.Analysis.Sobolev.WithBoundary.chartIterWeakPartialComplLp
          (p := 2) (Nat.le_refl 1) α (fun _ => i) (H1ComplDirichletToChartWkp g u) =
          DifferentialGeometry.Analysis.Sobolev.WithBoundary.chartIterWeakPartialComplLp
            (p := 2) (Nat.le_refl 1) α (fun _ => i)
            ((UniformSpace.Completion.toComplL : DirichletChartWkp (n := n) (M := M) →L[ℝ]
              H1ComplDirichletChartWkp (n := n) (M := M)) v) :=
        congrArg
          (DifferentialGeometry.Analysis.Sobolev.WithBoundary.chartIterWeakPartialComplLp
            (p := 2) (Nat.le_refl 1) α (fun _ => i)) (H1ComplDirichletToChartWkp_eq g u)
      _ = _ := by
        simpa only [UniformSpace.Completion.coe_toComplL] using
          DifferentialGeometry.Analysis.Sobolev.WithBoundary.chartIterWeakPartialComplLp_coe
            (Nat.le_refl 1) α (fun _ => i) v
  rw [heq]
  exact DifferentialGeometry.Analysis.Sobolev.WithBoundary.chartIterWeakPartialLp_apply_coeFn
    (Nat.le_refl 1) α (fun _ => i) v

theorem hasWeakPartialDeriv_dirichletChartWeakPartialLp
    (g : SmoothRiemannianMetric I_hs M) (α : M) (i : Fin n) (u : H1ComplDirichlet g) :
    DeGiorgi.HasWeakPartialDeriv i (dirichletChartWeakPartialLp g α i u)
      (DifferentialGeometry.Analysis.Sobolev.WithBoundary.chartPushed
        (chartAtlasPOU I_hs M) α (H1ComplDirichletToLp g u))
      (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
        (DifferentialGeometry.Analysis.Sobolev.WithBoundary.chartTargetEuclid α)) := by
  have hweak := DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartialOrZero_isWeakPartial_of_mem
    ((memWkpChart_H1ComplDirichletToLp g u α).memW1p) i
  intro φ hφ hφc hφs
  rw [hweak φ hφ hφc hφs]
  congr 1
  apply integral_congr_ae
  filter_upwards [dirichletChartWeakPartialLp_apply_coeFn g α i u] with y hy
  rw [hy]

theorem norm_dirichletChartWeakPartialLp_apply_le
    (g : SmoothRiemannianMetric I_hs M) (α : M) (i : Fin n) (u : H1ComplDirichlet g) :
    ‖dirichletChartWeakPartialLp g α i u‖ ≤
      ‖H1ComplDirichletToChartWkp (n := n) (M := M) g‖ * ‖u‖ :=
  (DifferentialGeometry.Analysis.Sobolev.WithBoundary.norm_chartIterWeakPartialComplLp_apply_le
    (Nat.le_refl 1) α (fun _ => i) (H1ComplDirichletToChartWkp g u)).trans
      ((H1ComplDirichletToChartWkp g).le_opNorm u)

theorem norm_dirichletChartWeakPartialLp_le
    (g : SmoothRiemannianMetric I_hs M) (α : M) (i : Fin n) :
    ‖dirichletChartWeakPartialLp (n := n) (M := M) g α i‖ ≤
      ‖H1ComplDirichletToChartWkp (n := n) (M := M) g‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  exact norm_dirichletChartWeakPartialLp_apply_le g α i


end DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
