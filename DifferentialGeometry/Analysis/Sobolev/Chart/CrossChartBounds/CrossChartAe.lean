import DifferentialGeometry.Analysis.Sobolev.Chart.CrossChartBounds.CrossChartBoundStrictMemWkpHigherOrder
import DifferentialGeometry.Analysis.Sobolev.Chart.CrossChartBounds.CrossChartTransfer
import DifferentialGeometry.Analysis.Sobolev.Chart.ChartTransition.QuasiMeasurePreserving

/-!
# Cross-chart Sobolev transfer for almost-everywhere compact support

The per-chart limits used in the Banach-completeness construction have a fixed
compact support only up to almost-everywhere equality.  This file turns such a
limit into its closed-set indicator representative, applies the arbitrary-order
cross-chart theorem, and transports the result back to the original
representative.

The public headline `crossChartAeJoint` returns both `MemWkp` membership and the
quantitative `wkpNorm` estimate.  Its constant depends only on the two charts,
the fixed compact manifold set, the metric, the Sobolev order, and the exponent;
it is independent of the input function.
-/

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Function
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Chart

variable {E H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- Replace a Euclidean function by the representative which is pointwise zero
off a fixed set. -/
def compactRep (K : Set EuclN) (v : EuclN → ℝ) : EuclN → ℝ :=
  K.indicator v

/-- The closed-set representative has topological support inside the fixed
closed set. -/
omit [FiniteDimensional ℝ E] in
lemma compactRep_support {K : Set EuclN} (hK : IsClosed K) (v : EuclN → ℝ) :
    tsupport (compactRep K v) ⊆ K := by
  change closure (Function.support (K.indicator v)) ⊆ K
  calc
    closure (Function.support (K.indicator v)) ⊆ closure K :=
      closure_mono Set.support_indicator_subset
    _ = K := hK.closure_eq

/-- If `v` vanishes almost everywhere on `Ω \ K`, its closed-set indicator is
almost everywhere equal to `v` on `Ω`. -/
omit [FiniteDimensional ℝ E] in
lemma compactRep_ae {Ω K : Set EuclN} (hK : MeasurableSet K)
    {v : EuclN → ℝ}
    (hv : v =ᵐ[(volume : Measure EuclN).restrict (Ω \ K)] 0) :
    compactRep K v =ᵐ[(volume : Measure EuclN).restrict Ω] v := by
  have hv' : v =ᵐ[((volume : Measure EuclN).restrict Ω).restrict Kᶜ] 0 := by
    rw [Measure.restrict_restrict hK.compl]
    simpa only [Set.diff_eq, Set.inter_comm] using hv
  simpa only [compactRep] using
    (indicator_ae_eq_of_restrict_compl_ae_eq_zero
      (μ := (volume : Measure EuclN).restrict Ω) hK hv')

/-- Raw pushforward after pulling back through the same chart recovers the
Euclidean input on that chart target. -/
lemma rawPullback_self (α : M) (v : EuclN → ℝ) {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    chartPushedRaw I α (chartPullback I α v) y = v y := by
  rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy]
  have hx := symm_toEuclidean_symm_mem_chartAtSource
    (I := I) (M := M) α hy
  rw [chartPullback_apply_of_mem (I := I) (M := M) α v hx]
  have hy_target : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
    rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
    exact hy
  rw [(extChartAt I α).right_inv hy_target,
    (toEuclidean (E := E)).apply_symm_apply]

/-- Cross-chart pullback preserves almost-everywhere equality.  The proof uses
quasi-measure preservation of the chart transition on the overlap; off the
overlap both chart pullbacks vanish pointwise. -/
theorem crossPullback_ae [I.Boundaryless]
    (ρ : SmoothPartitionOfUnity M I M Set.univ) (γ α : M)
    {v w : EuclN → ℝ}
    (hvw : v =ᵐ[(volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α)] w) :
    chartPushed (I := I) (M := M) ρ γ (chartPullback I α v) =ᵐ[
      (volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) γ)]
      chartPushed (I := I) (M := M) ρ γ (chartPullback I α w) := by
  let Oγα := chartOverlapEuclid (I := I) (M := M) γ α
  let Oαγ := chartOverlapEuclid (I := I) (M := M) α γ
  let Tγ := chartTargetEuclid (I := I) (M := M) γ
  have hOγα_open : IsOpen Oγα :=
    chartOverlapEuclid_isOpen (I := I) (M := M) γ α
  have hOαγ_sub : Oαγ ⊆ chartTargetEuclid (I := I) (M := M) α :=
    chartOverlapEuclid_subset_chartTarget (I := I) (M := M) α γ
  have hOγα_sub : Oγα ⊆ Tγ :=
    chartOverlapEuclid_subset_chartTarget (I := I) (M := M) γ α
  have hvw_overlap : v =ᵐ[(volume : Measure EuclN).restrict Oαγ] w :=
    hvw.filter_mono
      (ae_mono (Measure.restrict_mono_set volume hOαγ_sub))
  have hcomp := chartTransitionEuclid_comp_ae_eq_restrict
    (I := I) (M := M) γ α hvw_overlap
  have h_on_overlap :
      chartPushed (I := I) (M := M) ρ γ (chartPullback I α v) =ᵐ[
        (volume : Measure EuclN).restrict Oγα]
        chartPushed (I := I) (M := M) ρ γ (chartPullback I α w) := by
    rw [Filter.EventuallyEq, ae_restrict_iff' hOγα_open.measurableSet] at hcomp ⊢
    filter_upwards [hcomp] with y hycomp
    intro hy
    have hTy_overlap :=
      chartTransitionEuclid_mapsTo_overlap (I := I) (M := M) γ α hy
    have hTy_target : chartTransitionEuclid (I := I) (M := M) γ α y ∈
        chartTargetEuclid (I := I) (M := M) α :=
      chartOverlapEuclid_subset_chartTarget (I := I) (M := M) α γ hTy_overlap
    rw [crossChart_pushed_eq_pou_mul_comp_on_overlap
          (I := I) (M := M) ρ γ α (chartPullback I α v) hy,
      crossChart_pushed_eq_pou_mul_comp_on_overlap
          (I := I) (M := M) ρ γ α (chartPullback I α w) hy,
      rawPullback_self (I := I) (M := M) α v hTy_target,
      rawPullback_self (I := I) (M := M) α w hTy_target,
      hycomp hy]
  have hdiff_meas : MeasurableSet (Tγ \ Oγα) :=
    (chartTargetEuclid_isOpen (I := I) (M := M) γ).measurableSet.diff
      hOγα_open.measurableSet
  have h_on_diff :
      chartPushed (I := I) (M := M) ρ γ (chartPullback I α v) =ᵐ[
        (volume : Measure EuclN).restrict (Tγ \ Oγα)]
        chartPushed (I := I) (M := M) ρ γ (chartPullback I α w) := by
    refine (ae_restrict_iff' hdiff_meas).mpr ?_
    refine Filter.Eventually.of_forall fun y hy => ?_
    let x : M := (extChartAt I γ).symm ((toEuclidean (E := E)).symm y)
    have hxγ : x ∈ (chartAt H γ).source :=
      symm_toEuclidean_symm_mem_chartAtSource (I := I) (M := M) γ hy.1
    have hxα : x ∉ (chartAt H α).source := by
      intro hxα
      apply hy.2
      have hcoord : (toEuclidean (E := E)) (extChartAt I γ x) = y := by
        have hy_target : (toEuclidean (E := E)).symm y ∈ (extChartAt I γ).target := by
          have hyT : y ∈ chartTargetEuclid (I := I) (M := M) γ := by
            simpa only [Tγ] using hy.1
          rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hyT
          exact hyT
        dsimp only [x]
        rw [(extChartAt I γ).right_inv hy_target,
          (toEuclidean (E := E)).apply_symm_apply]
      exact ⟨extChartAt I γ x, ⟨x, ⟨hxγ, hxα⟩, rfl⟩, hcoord⟩
    unfold chartPushed
    change (ρ γ : C^∞⟮I, M; ℝ⟯) x * chartPullback I α v x =
      (ρ γ : C^∞⟮I, M; ℝ⟯) x * chartPullback I α w x
    rw [chartPullback_apply_of_notMem (I := I) (M := M) α v hxα,
      chartPullback_apply_of_notMem (I := I) (M := M) α w hxα]
  have h_union :
      chartPushed (I := I) (M := M) ρ γ (chartPullback I α v) =ᵐ[
        (volume : Measure EuclN).restrict (Oγα ∪ (Tγ \ Oγα))]
        chartPushed (I := I) (M := M) ρ γ (chartPullback I α w) := by
    rw [Filter.EventuallyEq, ae_restrict_union_eq]
    exact ⟨h_on_overlap, h_on_diff⟩
  rw [Set.union_diff_cancel hOγα_sub] at h_union
  exact h_union

/-- **Headline a.e.-support transfer.** A `W^{k,p}` function which vanishes
almost everywhere off the Euclidean image of a fixed compact chart kernel has
a chart-pushed cross-pullback in `W^{k,p}` in every other chart, with a uniform
per-pair norm bound. -/
theorem crossChartAeJoint
    [I.Boundaryless] [NeZero (Module.finrank ℝ E)]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (k : ℕ) {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ (⊤ : ℝ≥0∞))
    (γ α : M) {K_α : Set M} (hK_compact : IsCompact K_α)
    (hK_α_in_α : K_α ⊆ (chartAt H α).source) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {v : EuclN → ℝ},
        DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
            (d := Module.finrank ℝ E) k p v
            (chartTargetEuclid (I := I) (M := M) α) →
        v =ᵐ[(volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α \
            (fun x : M => (toEuclidean (E := E)) (extChartAt I α x)) '' K_α)] 0 →
        DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
            (d := Module.finrank ℝ E) k p
            (chartPushed (I := I) (M := M)
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) γ
              (chartPullback I α v))
            (chartTargetEuclid (I := I) (M := M) γ) ∧
          DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
            (d := Module.finrank ℝ E) k p
            (chartPushed (I := I) (M := M)
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) γ
              (chartPullback I α v))
            (chartTargetEuclid (I := I) (M := M) γ) ≤
          ENNReal.ofReal C *
            DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
              (d := Module.finrank ℝ E) k p v
              (chartTargetEuclid (I := I) (M := M) α) := by
  let K_E : Set EuclN :=
    (fun x : M => (toEuclidean (E := E)) (extChartAt I α x)) '' K_α
  have hKE_compact : IsCompact K_E :=
    chartImage_isCompact_of_compact_in_source (I := I) (M := M) α
      hK_compact hK_α_in_α
  have hKE_closed : IsClosed K_E := hKE_compact.isClosed
  obtain ⟨C, hC, hjoint⟩ := crossChartJointK (I := I) (M := M)
    g k hp_one hp_top γ α hK_compact hK_α_in_α
  refine ⟨C, hC, ?_⟩
  intro v hv hvzero
  let vK : EuclN → ℝ := compactRep K_E v
  have hvK_ae : vK =ᵐ[(volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α)] v := by
    exact compactRep_ae hKE_compact.measurableSet hvzero
  have hvK_mem : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) k p vK
      (chartTargetEuclid (I := I) (M := M) α) :=
    (DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_congr_ae
      (d := Module.finrank ℝ E) hp_one
      (chartTargetEuclid_isOpen (I := I) (M := M) α) hvK_ae).mpr hv
  have hvK_supp : tsupport vK ⊆
      (fun x : M => (toEuclidean (E := E)) (extChartAt I α x)) '' K_α := by
    exact compactRep_support hKE_closed v
  have hj := hjoint hvK_mem hvK_supp
  have hout_ae := crossPullback_ae (I := I) (M := M)
    (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) γ α hvK_ae
  have hout_mem : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) k p
      (chartPushed (I := I) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) γ
        (chartPullback I α v))
      (chartTargetEuclid (I := I) (M := M) γ) :=
    (DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_congr_ae
      (d := Module.finrank ℝ E) hp_one
      (chartTargetEuclid_isOpen (I := I) (M := M) γ) hout_ae).mp hj.1
  refine ⟨hout_mem, ?_⟩
  calc
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
        (d := Module.finrank ℝ E) k p
        (chartPushed (I := I) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) γ
          (chartPullback I α v))
        (chartTargetEuclid (I := I) (M := M) γ) =
      DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
        (d := Module.finrank ℝ E) k p
        (chartPushed (I := I) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) γ
          (chartPullback I α vK))
        (chartTargetEuclid (I := I) (M := M) γ) :=
      (DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_congr_ae
        (d := Module.finrank ℝ E) hp_one
        (chartTargetEuclid_isOpen (I := I) (M := M) γ) hout_ae).symm
    _ ≤ ENNReal.ofReal C *
        DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
          (d := Module.finrank ℝ E) k p vK
          (chartTargetEuclid (I := I) (M := M) α) := hj.2
    _ = ENNReal.ofReal C *
        DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
          (d := Module.finrank ℝ E) k p v
          (chartTargetEuclid (I := I) (M := M) α) := by
      rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_congr_ae
        (d := Module.finrank ℝ E) hp_one
        (chartTargetEuclid_isOpen (I := I) (M := M) α) hvK_ae]

end Chart
end Sobolev
end Analysis
end DifferentialGeometry
