import DifferentialGeometry.Analysis.Sobolev.Chart.BanachCompleteness.ManifoldLimitWkp
import DifferentialGeometry.Analysis.Sobolev.Approximation.ContMDiffDenseLemmas

/-!
# Convergence to the assembled manifold Sobolev limit

This file finishes the sequence-level Banach-completeness argument begun in
`BanachManifold.lean`.  The chosen Euclidean chart limits are assembled by the
finite canonical partition of unity.  A fixed-support cross-chart estimate
controls the error contributed by every source/target chart pair, and the
finite double sum tends to zero.

The final completeness declarations return `CompleteSpace` structures as
ordinary theorem values.  They deliberately do not register global instances.
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

/-- The source-chart error between an iterate and its chosen Euclidean limit. -/
noncomputable def chartErr
    [NeZero (Module.finrank ℝ E)]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    {g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M}
    {k : ℕ} {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ (⊤ : ℝ≥0∞))
    {hp : 1 ≤ p}
    {f : ℕ → WkpChart (I := I) (M := M) g k p hp}
    (h_cauchy : ∀ ε > 0, ∃ N, ∀ m n, N ≤ m → N ≤ n →
      wkpNormChart (I := I) (M := M) g k p
        (fun x => wkpChartFun (f m) x - wkpChartFun (f n) x) ≤
        ENNReal.ofReal ε)
    (n : ℕ) (β : M) : EuclN → ℝ :=
  fun y =>
    chartPushed (I := I) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) β
        (wkpChartFun (f n)) y -
      chartLimit (I := I) (M := M) hp_one hp_top h_cauchy β y

/-- Every source-chart error remains in the Euclidean Sobolev class. -/
lemma chartErr_mem
    [NeZero (Module.finrank ℝ E)]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    {g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M}
    {k : ℕ} {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ (⊤ : ℝ≥0∞))
    {hp : 1 ≤ p}
    {f : ℕ → WkpChart (I := I) (M := M) g k p hp}
    (h_cauchy : ∀ ε > 0, ∃ N, ∀ m n, N ≤ m → N ≤ n →
      wkpNormChart (I := I) (M := M) g k p
        (fun x => wkpChartFun (f m) x - wkpChartFun (f n) x) ≤
        ENNReal.ofReal ε)
    (n : ℕ) (β : M) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) k p
      (chartErr (I := I) (M := M) hp_one hp_top h_cauchy n β)
      (chartTargetEuclid (I := I) (M := M) β) := by
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.sub
    (d := Module.finrank ℝ E) hp_one
    (chartTargetEuclid_isOpen (I := I) (M := M) β)
    ((wkpChartFun_memWkpChart (f n)) β)
    (chartLimit_memWkp (I := I) (M := M) (g := g)
      hp_one hp_top h_cauchy β)

/-- The source-chart error is almost everywhere zero off the fixed compact
POU kernel. -/
lemma chartErr_ae_zero
    [NeZero (Module.finrank ℝ E)]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    {g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M}
    {k : ℕ} {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ (⊤ : ℝ≥0∞))
    {hp : 1 ≤ p}
    {f : ℕ → WkpChart (I := I) (M := M) g k p hp}
    (h_cauchy : ∀ ε > 0, ∃ N, ∀ m n, N ≤ m → N ≤ n →
      wkpNormChart (I := I) (M := M) g k p
        (fun x => wkpChartFun (f m) x - wkpChartFun (f n) x) ≤
        ENNReal.ofReal ε)
    (n : ℕ) (β : M) :
    chartErr (I := I) (M := M) hp_one hp_top h_cauchy n β =ᵐ[
      (volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) β \
          toEuclidean ''
            ((extChartAt I β) ''
              tsupport
                ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) β : M → ℝ)))] 0 := by
  classical
  let Kβ : Set M := tsupport
    ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) β : M → ℝ)
  let KβE : Set EuclN := toEuclidean '' ((extChartAt I β) '' Kβ)
  have hKβ_compact : IsCompact Kβ := (isClosed_tsupport _).isCompact
  have hKβ_sub : Kβ ⊆ (chartAt H β).source :=
    DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M β
  have hKβE_compact : IsCompact KβE := by
    simpa only [KβE, Set.image_image, Function.comp_apply] using
      (chartImage_isCompact_of_compact_in_source (I := I) (M := M) β
        hKβ_compact hKβ_sub)
  have h_off_meas : MeasurableSet
      (chartTargetEuclid (I := I) (M := M) β \ KβE) :=
    (chartTargetEuclid_measurableSet (I := I) (M := M) β).diff
      hKβE_compact.measurableSet
  have h_lim_zero :
      chartLimit (I := I) (M := M) hp_one hp_top h_cauchy β =ᵐ[
        (volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) β \ KβE)] 0 := by
    simpa only [KβE, Kβ] using
      (chartLimit_ae_zero (I := I) (M := M) (g := g)
        hp_one hp_top h_cauchy β)
  have h_mem : ∀ᵐ y ∂(volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) β \ KβE),
      y ∈ chartTargetEuclid (I := I) (M := M) β \ KβE :=
    ae_restrict_mem h_off_meas
  have h_err : chartErr (I := I) (M := M) hp_one hp_top h_cauchy n β =ᵐ[
      (volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) β \ KβE)] 0 := by
    filter_upwards [h_lim_zero, h_mem] with y hy_lim hy
    have hy_push : chartPushed (I := I) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) β
        (wkpChartFun (f n)) y = 0 := by
      exact chartPushed_eq_zero_off_compact (I := I) (M := M) β
        (wkpChartFun (f n)) hy.1 (by
          simpa only [KβE, Kβ] using hy.2)
    change chartPushed (I := I) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) β
        (wkpChartFun (f n)) y -
      chartLimit (I := I) (M := M) hp_one hp_top h_cauchy β y = 0
    rw [hy_push, hy_lim, sub_zero]
  simpa only [KβE, Kβ] using h_err

/-- Measurable pullback is additive with respect to subtraction. -/
lemma pullback_sub (β : M) (v w : EuclN → ℝ) :
    pullbackToManifold (I := I) β (fun y => v y - w y) =
      fun x => pullbackToManifold (I := I) β v x -
        pullbackToManifold (I := I) β w x := by
  classical
  funext x
  by_cases hx : x ∈ (chartAt H β).source
  · simp only [pullbackToManifold_apply_of_mem (I := I) (α := β) _ hx]
  · simp only [pullbackToManifold_apply_of_notMem (I := I) (α := β) _ hx,
      sub_zero]

/-- The manifold error is the finite sum of pulled-back source-chart errors. -/
lemma limitFun_decomp
    [NeZero (Module.finrank ℝ E)]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    {g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M}
    {k : ℕ} {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ (⊤ : ℝ≥0∞))
    {hp : 1 ≤ p}
    {f : ℕ → WkpChart (I := I) (M := M) g k p hp}
    (h_cauchy : ∀ ε > 0, ∃ N, ∀ m n, N ≤ m → N ≤ n →
      wkpNormChart (I := I) (M := M) g k p
        (fun x => wkpChartFun (f m) x - wkpChartFun (f n) x) ≤
        ENNReal.ofReal ε)
    (n : ℕ) :
    (fun x => wkpChartFun (f n) x -
        manifoldLimitFun (I := I) (M := M) hp_one hp_top h_cauchy x) =
      fun x =>
        ∑ β ∈ DifferentialGeometry.Integral.Measure.chartAtlasPOU_finset
            (I := I) (M := M),
          chartPullback I β
            (chartErr (I := I) (M := M) hp_one hp_top h_cauchy n β) x := by
  classical
  let S := DifferentialGeometry.Integral.Measure.chartAtlasPOU_finset
    (I := I) (M := M)
  funext x
  have h_iter := congrFun
    (wkpChartFun_eq_finset_sum_pullback (I := I) (M := M) (f n)) x
  rw [h_iter]
  unfold manifoldLimitFun
  change
    (∑ β ∈ S, pullbackToManifold (I := I) β
        (chartPushed (I := I) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) β
          (wkpChartFun (f n))) x) -
      (∑ β ∈ S, pullbackToManifold (I := I) β
        (chartLimit (I := I) (M := M) hp_one hp_top h_cauchy β) x) =
    ∑ β ∈ S, chartPullback I β
      (chartErr (I := I) (M := M) hp_one hp_top h_cauchy n β) x
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro β _
  rw [← pullback_eq_chart (I := I) (M := M)]
  unfold chartErr
  rw [pullback_sub]
  rfl

/-- The original Cauchy sequence converges in `wkpNormChart` to the finite POU
assembly of its chosen Euclidean chart limits. -/
theorem limitFun_tendsto
    [NeZero (Module.finrank ℝ E)]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {k : ℕ} {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ (⊤ : ℝ≥0∞))
    {hp : 1 ≤ p}
    {f : ℕ → WkpChart (I := I) (M := M) g k p hp}
    (h_cauchy : ∀ ε > 0, ∃ N, ∀ m n, N ≤ m → N ≤ n →
      wkpNormChart (I := I) (M := M) g k p
        (fun x => wkpChartFun (f m) x - wkpChartFun (f n) x) ≤
        ENNReal.ofReal ε) :
    Tendsto
      (fun n => wkpNormChart (I := I) (M := M) g k p
        (fun x => wkpChartFun (f n) x -
          manifoldLimitFun (I := I) (M := M) hp_one hp_top h_cauchy x))
      atTop (𝓝 0) := by
  classical
  let ρ := DifferentialGeometry.Integral.Measure.chartAtlasPOU I M
  let S := DifferentialGeometry.Integral.Measure.chartAtlasPOU_finset
    (I := I) (M := M)
  let K : M → Set M := fun β => tsupport ((ρ β : C^∞⟮I, M; ℝ⟯) : M → ℝ)
  have hK_compact : ∀ β : M, IsCompact (K β) := fun _ =>
    (isClosed_tsupport _).isCompact
  have hK_sub : ∀ β : M, K β ⊆ (chartAt H β).source := fun β =>
    DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M β
  let C : M → M → ℝ := fun γ β =>
    (crossChartAeJoint (I := I) (M := M) g k hp_one hp_top γ β
      (hK_compact β) (hK_sub β)).choose
  have hcross : ∀ γ β : M, ∀ {v : EuclN → ℝ},
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) k p v
          (chartTargetEuclid (I := I) (M := M) β) →
      v =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) β \
          (fun x : M => (toEuclidean (E := E)) (extChartAt I β x)) '' K β)] 0 →
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) k p
          (chartPushed (I := I) (M := M) ρ γ (chartPullback I β v))
          (chartTargetEuclid (I := I) (M := M) γ) ∧
        DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
          (d := Module.finrank ℝ E) k p
          (chartPushed (I := I) (M := M) ρ γ (chartPullback I β v))
          (chartTargetEuclid (I := I) (M := M) γ) ≤
        ENNReal.ofReal (C γ β) *
          DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
            (d := Module.finrank ℝ E) k p v
            (chartTargetEuclid (I := I) (M := M) β) := by
    intro γ β v
    exact (crossChartAeJoint (I := I) (M := M) g k hp_one hp_top γ β
      (hK_compact β) (hK_sub β)).choose_spec.2
  have h_err_zero : ∀ n β,
      chartErr (I := I) (M := M) hp_one hp_top h_cauchy n β =ᵐ[
        (volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) β \
            (fun x : M => (toEuclidean (E := E)) (extChartAt I β x)) '' K β)] 0 := by
    intro n β
    simpa only [K, ρ, Set.image_image, Function.comp_apply] using
      (chartErr_ae_zero (I := I) (M := M) (g := g)
        hp_one hp_top h_cauchy n β)
  have hq : ∀ n γ β,
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) k p
          (chartPushed (I := I) (M := M) ρ γ
            (chartPullback I β
              (chartErr (I := I) (M := M) hp_one hp_top h_cauchy n β)))
          (chartTargetEuclid (I := I) (M := M) γ) ∧
        DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
          (d := Module.finrank ℝ E) k p
          (chartPushed (I := I) (M := M) ρ γ
            (chartPullback I β
              (chartErr (I := I) (M := M) hp_one hp_top h_cauchy n β)))
          (chartTargetEuclid (I := I) (M := M) γ) ≤
        ENNReal.ofReal (C γ β) *
          DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
            (d := Module.finrank ℝ E) k p
            (chartErr (I := I) (M := M) hp_one hp_top h_cauchy n β)
            (chartTargetEuclid (I := I) (M := M) β) := by
    intro n γ β
    exact hcross γ β
      (chartErr_mem (I := I) (M := M) (g := g)
        hp_one hp_top h_cauchy n β)
      (h_err_zero n β)
  let term : ℕ → M → M → ℝ := fun n β =>
    chartPullback I β
      (chartErr (I := I) (M := M) hp_one hp_top h_cauchy n β)
  have hterm_mem : ∀ n β,
      MemWkpChart (I := I) (M := M) g k p (term n β) := by
    intro n β γ
    exact (hq n γ β).1
  have h_bound : ∀ n,
      wkpNormChart (I := I) (M := M) g k p
          (fun x => wkpChartFun (f n) x -
            manifoldLimitFun (I := I) (M := M) hp_one hp_top h_cauchy x) ≤
        ∑ β ∈ S, ∑ γ ∈ S,
          ENNReal.ofReal (C γ β) *
            DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
              (d := Module.finrank ℝ E) k p
              (chartErr (I := I) (M := M) hp_one hp_top h_cauchy n β)
              (chartTargetEuclid (I := I) (M := M) β) := by
    intro n
    rw [limitFun_decomp (I := I) (M := M) hp_one hp_top h_cauchy n]
    refine (wkpNormChart_finset_sum_le (I := I) (M := M) g hp_one S
      (term n) (fun β _ => hterm_mem n β)).trans ?_
    refine Finset.sum_le_sum ?_
    intro β _
    rw [wkpNormChart_eq_finset_sum (I := I) (M := M) g k hp_one]
    exact Finset.sum_le_sum (fun γ _ => (hq n γ β).2)
  have h_pair : ∀ β ∈ S, ∀ γ ∈ S,
      Tendsto
        (fun n => ENNReal.ofReal (C γ β) *
          DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
            (d := Module.finrank ℝ E) k p
            (chartErr (I := I) (M := M) hp_one hp_top h_cauchy n β)
            (chartTargetEuclid (I := I) (M := M) β))
        atTop (𝓝 0) := by
    intro β _ γ _
    have h_err_tendsto : Tendsto
        (fun n => DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
          (d := Module.finrank ℝ E) k p
          (chartErr (I := I) (M := M) hp_one hp_top h_cauchy n β)
          (chartTargetEuclid (I := I) (M := M) β))
        atTop (𝓝 0) := by
      simpa only [chartErr] using
        (chartLimit_tendsto (I := I) (M := M) (g := g)
          hp_one hp_top h_cauchy β)
    have hC_ne_top : ENNReal.ofReal (C γ β) ≠ (⊤ : ℝ≥0∞) :=
      ENNReal.ofReal_ne_top
    have hmul := ENNReal.Tendsto.const_mul
      (a := ENNReal.ofReal (C γ β)) (b := 0) h_err_tendsto
      (Or.inr hC_ne_top)
    simpa using hmul
  have h_inner : ∀ β ∈ S,
      Tendsto
        (fun n => ∑ γ ∈ S,
          ENNReal.ofReal (C γ β) *
            DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
              (d := Module.finrank ℝ E) k p
              (chartErr (I := I) (M := M) hp_one hp_top h_cauchy n β)
              (chartTargetEuclid (I := I) (M := M) β))
        atTop (𝓝 0) := by
    intro β hβ
    simpa using tendsto_finset_sum S (fun γ hγ => h_pair β hβ γ hγ)
  have h_rhs : Tendsto
      (fun n => ∑ β ∈ S, ∑ γ ∈ S,
        ENNReal.ofReal (C γ β) *
          DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
            (d := Module.finrank ℝ E) k p
            (chartErr (I := I) (M := M) hp_one hp_top h_cauchy n β)
            (chartTargetEuclid (I := I) (M := M) β))
      atTop (𝓝 0) := by
    simpa using tendsto_finset_sum S h_inner
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds h_rhs
    (Filter.Eventually.of_forall (fun _ => zero_le _))
    (Filter.Eventually.of_forall h_bound)

/-- Sequence-level completeness packaged as an ordinary theorem value, not a
global typeclass instance. -/
theorem wkpChart_complete
    [NeZero (Module.finrank ℝ E)]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (k : ℕ) {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ (⊤ : ℝ≥0∞)) :
    CompleteSpace (WkpChart (I := I) (M := M) g k p hp_one) := by
  apply Metric.complete_of_cauchySeq_tendsto
  intro f hf
  let h_cauchy := wkpNormChart_cauchy_of_seminormCauchySeq
    (I := I) (M := M) (g := g) (k := k) (p := p) hf
  let uFun := manifoldLimitFun (I := I) (M := M)
    hp_one hp_top h_cauchy
  have hu_mem : MemWkpChart (I := I) (M := M) g k p uFun := by
    exact limitFun_memWkp (I := I) (M := M) (g := g)
      hp_one hp_top h_cauchy
  let u : WkpChart (I := I) (M := M) g k p hp_one := ⟨uFun, hu_mem⟩
  refine ⟨u, ?_⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h_enn := limitFun_tendsto (I := I) (M := M) g
    hp_one hp_top h_cauchy
  have h_real : Tendsto
      (fun n => (wkpNormChart (I := I) (M := M) g k p
        (fun x => wkpChartFun (f n) x -
          manifoldLimitFun (I := I) (M := M) hp_one hp_top h_cauchy x)).toReal)
      atTop (𝓝 (0 : ℝ)) := by
    simpa using ((ENNReal.tendsto_toReal
      (by simp : (0 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞))).comp h_enn)
  have hfun : ∀ n,
      wkpChartFun (f n - u) =
        fun x => wkpChartFun (f n) x - uFun x := by
    intro n
    rfl
  have hnorm_eq : (fun n => ‖f n - u‖) =
      fun n => (wkpNormChart (I := I) (M := M) g k p
        (fun x => wkpChartFun (f n) x - uFun x)).toReal := by
    funext n
    rw [norm_wkpChart_def, hfun n]
  rw [hnorm_eq]
  simpa only [uFun] using h_real

/-- Completeness of the separated chart-Sobolev space, again returned as a
theorem value rather than installed globally. -/
theorem wkpQuot_complete
    [NeZero (Module.finrank ℝ E)]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (k : ℕ) {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ (⊤ : ℝ≥0∞)) :
    CompleteSpace (WkpChartQuot (I := I) (M := M) g k p hp_one) :=
  SeparationQuotient.completeSpace_iff.mpr
    (wkpChart_complete (I := I) (M := M) g k hp_one hp_top)

end Chart
end Sobolev
end Analysis
end DifferentialGeometry
