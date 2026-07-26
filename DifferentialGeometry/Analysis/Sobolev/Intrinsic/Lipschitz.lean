import DifferentialGeometry.Analysis.Sobolev.Manifold.Lipschitz
import DifferentialGeometry.Analysis.Sobolev.Intrinsic.Lp
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.Closed
import DifferentialGeometry.Geometry.Metric.LipschitzGradient

/-!
# Intrinsic weak gradients of Lipschitz functions

This file promotes bounded functions that are Lipschitz for an explicit
Riemannian distance to the intrinsic weak-gradient interface.  The proof is
assembled from chart-local Lipschitz integration by parts and the finite
partition of unity on a compact manifold.
-/

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Function
open scoped Manifold ContDiff ENNReal NNReal BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace IntrinsicLp

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Sobolev.Chart

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ⊤ M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩
private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩

private lemma pull_lip_of_raw
    (α : M) (φ : M → ℝ) {C : NNReal}
    (hφ : LipschitzWith C (chartPushedRaw (I := I) (M := M) α φ)) :
    ∃ D : NNReal, LipschitzWith D (chartPullZero (I := I) α φ) := by
  have heq : chartPullZero (I := I) α φ =
      chartPushedRaw (I := I) (M := M) α φ ∘ (toEuclidean (E := E)) := by
    funext y
    by_cases hy : y ∈ (extChartAt I α).target
    · have hy' : toEuclidean y ∈ chartTargetEuclid (I := I) (M := M) α := by
        rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)]
        simpa only [Set.mem_preimage,
          (toEuclidean (E := E)).symm_apply_apply] using hy
      rw [chartPullZero_mem (I := I) α φ hy, Function.comp_apply,
        chartPushedRaw_apply_of_mem (I := I) (M := M) α φ hy']
      simp only [scalarOnE_def, (toEuclidean (E := E)).symm_apply_apply]
    · have hy' : toEuclidean y ∉ chartTargetEuclid (I := I) (M := M) α := by
        rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)]
        simpa only [Set.mem_preimage,
          (toEuclidean (E := E)).symm_apply_apply] using hy
      rw [chartPullZero_nmem (I := I) α φ hy, Function.comp_apply,
        chartPushedRaw_apply_of_notMem (I := I) (M := M) α φ hy']
  refine ⟨C * ‖(toEuclidean (E := E)).toContinuousLinearMap‖₊, ?_⟩
  rw [heq]
  exact hφ.comp (toEuclidean (E := E)).lipschitz

omit [IsManifold I ⊤ M] in
attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- A function Lipschitz for the extended distance of an explicit smooth
Riemannian metric is continuous in the manifold topology. -/
theorem intrinsic_lip_cont
    [IsManifold I ∞ M] [T2Space M] [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) {u : M → ℝ} {L : NNReal}
    (hu : ∀ x y, edist (u x) (u y) ≤ (L : ENNReal) *
      riemannianEDistOf (I := I) g x y) :
    Continuous u := by
  letI : RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  letI : LocallyCompactSpace M :=
    Manifold.locallyCompact_of_finiteDimensional (M := M) I
  letI : RegularSpace M := inferInstance
  letI : PseudoEMetricSpace M := PseudoEMetricSpace.ofRiemannianMetric I M
  apply LipschitzWith.continuous (K := L)
  intro x y
  rw [IsRiemannianManifold.out (I := I) x y]
  simpa only [riemannianEDistOf] using hu x y

private theorem global_lip_ibp
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {u : M → ℝ} {L B : NNReal}
    (hu : ∀ x y, edist (u x) (u y) ≤ (L : ENNReal) *
      riemannianEDistOf (I := I) g x y)
    (hB : ∀ x, ‖u x‖₊ ≤ B) :
    Integrable (tangentSectionAction (I := I) X u)
        (riemannianVolumeMeasure (I := I) (M := M) g) ∧
      ∫ x, tangentSectionAction (I := I) X u x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        -∫ x, u x * divergence_g (I := I) g X x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  let ρ : SmoothPartitionOfUnity M I M (Set.univ : Set M) :=
    chartAtlasPOU I M
  let S : Finset M := chartAtlasPOU_finset (I := I) (M := M)
  let φ : M → M → ℝ := fun α x => ρ α x * u x
  have hρsub : ρ.IsSubordinate (fun α : M => (chartAt H α).source) := by
    simpa only [ρ] using chartAtlasPOU_isSubordinate I M
  have hu_cont : Continuous u := intrinsic_lip_cont (I := I) g hu
  have hdiv_cont : Continuous (divergence_g (I := I) g X) :=
    (divergence_g_contMDiff (I := I) g X).continuous
  haveI : IsFiniteMeasureOnCompacts
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasureOnCompacts (I := I) (M := M) g
  have hudiv_int : Integrable (fun x => u x * divergence_g (I := I) g X x)
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    (hu_cont.mul hdiv_cont).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hφ_supp (α : M) : tsupport (φ α) ⊆ (chartAt H α).source := by
    exact tsupport_mul_subset_left.trans (hρsub α)
  have hφ_compact (α : M) : HasCompactSupport (φ α) :=
    HasCompactSupport.of_compactSpace _
  have hφ_lip (α : M) : ∃ D : NNReal,
      LipschitzWith D (chartPullZero (I := I) α (φ α)) := by
    obtain ⟨C, hraw⟩ := chart_pou_lip (I := I) g α hu hB
    apply pull_lip_of_raw (I := I) α (φ α)
    simpa only [φ, ρ] using hraw
  let D : M → NNReal := fun α => Classical.choose (hφ_lip α)
  have hD (α : M) : LipschitzWith (D α)
      (chartPullZero (I := I) α (φ α)) :=
    Classical.choose_spec (hφ_lip α)
  have hstep_a :
      ∑ α ∈ S, ∫ x,
          (u x * divergence_g (I := I) g X x) * ρ α x
            ∂(chartLocalMeasure (I := I) g α) =
        ∫ x, u x * divergence_g (I := I) g X x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    simpa only [S, ρ] using chart_sum_integral (I := I) (M := M) g _ hudiv_int
  have hstep_b : ∀ α ∈ S,
      ∫ x, (u x * divergence_g (I := I) g X x) * ρ α x
          ∂(chartLocalMeasure (I := I) g α) =
        ∫ x, localDivergence (I := I) g α X x * φ α x
          ∂(chartLocalMeasure (I := I) g α) := by
    intro α _
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ (chartAt H α).source
    · simp only [φ]
      rw [voss_weyl_divergence_formula (I := I) g α X hx]
      ring
    · have hρzero : ρ α x = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        exact fun h => hx (hρsub α h)
      simp only [φ, hρzero, mul_zero, zero_mul]
  have hstep_c : ∀ α ∈ S,
      ∫ x, localDivergence (I := I) g α X x * φ α x
          ∂(chartLocalMeasure (I := I) g α) =
        -∫ x, tangentSectionAction (I := I) X (φ α) x
          ∂(chartLocalMeasure (I := I) g α) := by
    intro α _
    exact chart_local_ibp_lip (I := I) g α X (hD α)
      (hφ_compact α) (hφ_supp α)
  have htrans : ∀ α ∈ S,
      Integrable (tangentSectionAction (I := I) X (φ α))
          (riemannianVolumeMeasure (I := I) (M := M) g) ∧
        ∫ x, tangentSectionAction (I := I) X (φ α) x
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
          ∫ x, tangentSectionAction (I := I) X (φ α) x
            ∂(chartLocalMeasure (I := I) g α) := by
    intro α _
    apply chart_int_eq_global (I := I) (M := M) g α
      (tangent_lip_int (I := I) g α X (hD α) (hφ_compact α) (hφ_supp α))
    intro x hx
    have hxt : x ∉ tsupport (φ α) := fun h => hx (hφ_supp α h)
    have hev : (φ α) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
      simpa only [Pi.zero_apply] using notMem_tsupport_iff_eventuallyEq.mp hxt
    have hmfderiv_zero : mfderiv I 𝓘(ℝ) (φ α) x = 0 := by
      rw [Filter.EventuallyEq.mfderiv_eq hev, mfderiv_const]
      rfl
    unfold tangentSectionAction
    rw [hmfderiv_zero]
    rfl
  have heach : ∀ α ∈ S, Integrable
      (tangentSectionAction (I := I) X (φ α))
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    fun α hα => (htrans α hα).1
  have hsumφ : (∑ α ∈ S, φ α) = u := by
    funext x
    simp only [Finset.sum_apply, φ, ← Finset.sum_mul]
    have hone : ∑ α ∈ S, ρ α x = 1 := by
      simpa only [S, ρ] using
        chartAtlasPOU_finset_sum_eq_one (I := I) (M := M) x
    rw [hone, one_mul]
  have hact_ae : (fun x => ∑ α ∈ S,
      tangentSectionAction (I := I) X (φ α) x) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
      tangentSectionAction (I := I) X u := by
    filter_upwards [ae_mdiff_of_lip (I := I) g hu hB] with x hux
    have hφdiff : ∀ α ∈ S, MDifferentiableAt I 𝓘(ℝ, ℝ) (φ α) x := by
      intro α _
      simpa only [φ] using
        ((ρ α).contMDiff.mdifferentiableAt (by simp)).mul hux
    have hcomm := tangentSectionAction_finset_sum (I := I) X S φ x hφdiff
    rw [hsumφ] at hcomm
    exact hcomm.symm
  have hsum_int : Integrable (fun x => ∑ α ∈ S,
      tangentSectionAction (I := I) X (φ α) x)
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    integrable_finset_sum S heach
  have htu_int : Integrable (tangentSectionAction (I := I) X u)
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    hsum_int.congr hact_ae
  have hint_sum :
      ∑ α ∈ S, ∫ x, tangentSectionAction (I := I) X (φ α) x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        ∫ x, tangentSectionAction (I := I) X u x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    calc
      _ = ∫ x, ∑ α ∈ S, tangentSectionAction (I := I) X (φ α) x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
        (integral_finset_sum (μ := riemannianVolumeMeasure (I := I) (M := M) g)
          S heach).symm
      _ = _ := integral_congr_ae hact_ae
  have hdiv_eq :
      ∫ x, u x * divergence_g (I := I) g X x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        -∫ x, tangentSectionAction (I := I) X u x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    calc
      _ = ∑ α ∈ S, ∫ x,
          (u x * divergence_g (I := I) g X x) * ρ α x
            ∂(chartLocalMeasure (I := I) g α) := hstep_a.symm
      _ = ∑ α ∈ S, ∫ x, localDivergence (I := I) g α X x * φ α x
            ∂(chartLocalMeasure (I := I) g α) :=
        Finset.sum_congr rfl hstep_b
      _ = ∑ α ∈ S, -∫ x, tangentSectionAction (I := I) X (φ α) x
            ∂(chartLocalMeasure (I := I) g α) :=
        Finset.sum_congr rfl hstep_c
      _ = ∑ α ∈ S, -∫ x, tangentSectionAction (I := I) X (φ α) x
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
        refine Finset.sum_congr rfl ?_
        intro α hα
        rw [(htrans α hα).2]
      _ = -(∑ α ∈ S, ∫ x, tangentSectionAction (I := I) X (φ α) x
            ∂(riemannianVolumeMeasure (I := I) (M := M) g)) := by
        rw [Finset.sum_neg_distrib]
      _ = -∫ x, tangentSectionAction (I := I) X u x
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
        rw [hint_sum]
  refine ⟨htu_int, ?_⟩
  linarith

/-- The pointwise metric gradient is a weak Riemannian gradient of every
bounded function that is Lipschitz for the explicit Riemannian distance. -/
theorem weak_grad_of_lip
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) {u : M → ℝ} {L B : NNReal}
    (hu : ∀ x y, edist (u x) (u y) ≤ (L : ENNReal) *
      riemannianEDistOf (I := I) g x y)
    (hB : ∀ x, ‖u x‖₊ ≤ B) :
    HasWeakRiemannianGradLp (I := I) (M := M) g u
      (fun x => (gradFun (I := I) g u x : E)) := by
  refine ⟨?_, ?_⟩
  · intro Y
    have hint := (global_lip_ibp (I := I) g Y hu hB).1
    apply hint.aestronglyMeasurable.congr
    exact Filter.Eventually.of_forall fun x => by
      simpa only [tangentSectionAction] using
        (inner_gradFun (I := I) g u x (Y x)).symm
  · intro X _
    have hibp := (global_lip_ibp (I := I) g X hu hB).2
    calc
      ∫ x, g.inner x (gradFun (I := I) g u x) (X x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        ∫ x, tangentSectionAction (I := I) X u x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by
          simpa only [tangentSectionAction] using
            inner_gradFun (I := I) g u x (X x)
      _ = _ := hibp

omit [IsManifold I ⊤ M] in
/-- The metric norm of `gradFun` is strongly measurable whenever the scalar
function is manifold-differentiable almost everywhere. -/
theorem grad_norm_aesm
    [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) {u : M → ℝ}
    (hu : ∀ᵐ x ∂riemannianVolumeMeasure I M g,
      MDifferentiableAt I 𝓘(ℝ, ℝ) u x) :
    AEStronglyMeasurable
      (fun x : M => Real.sqrt
        (g.inner x (gradFun (I := I) g u x) (gradFun (I := I) g u x)))
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  let source : M → Set M := fun α => (chartAt H α).source
  let gram : M → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → M → ℝ :=
    fun α i j => (source α).piecewise
      (fun x => chartInvGramMatrix (I := I) g α x i j) (fun _ => 0)
  let part : M → Fin (Module.finrank ℝ E) → M → ℝ := fun α i x =>
    partialDeriv (E := E) i (scalarOnE (I := I) α u)
      (extChartAtExt (I := I) α x)
  let q : M → M → ℝ := fun α x =>
    ∑ i, ∑ j, gram α i j x * part α j x * part α i x
  let ρ : M → M → ℝ := fun α x => (chartAtlasPOU I M α) x
  let S : Finset M := chartAtlasPOU_finset (I := I) (M := M)
  let qsum : M → ℝ := fun x => ∑ α ∈ S, ρ α x * q α x
  have hsource (α : M) : MeasurableSet (source α) := by
    simpa only [source] using (chartAt H α).open_source.measurableSet
  have hgram (α : M) (i j : Fin (Module.finrank ℝ E)) :
      Measurable (gram α i j) := by
    have hcont : ContinuousOn
        (fun x : M => chartInvGramMatrix (I := I) g α x i j) (source α) := by
      have h :=
        (chartInvGramMatrix_entry_contMDiffOn (I := I) g α i j).continuousOn
      simpa only [source, trivializationAt_baseSet_eq_chartAt_source] using h
    exact ContinuousOn.measurable_piecewise hcont continuous_const.continuousOn
      (hsource α)
  have hpart (α : M) (i : Fin (Module.finrank ℝ E)) :
      Measurable (part α i) := by
    unfold part partialDeriv
    exact (measurable_fderiv_apply_const ℝ
      (scalarOnE (I := I) α u) ((chartModelBasis E) i)).comp
        (extChartAtExt_measurable (I := I) (α := α))
  have hq (α : M) : Measurable (q α) := by
    unfold q
    refine Finset.measurable_fun_sum Finset.univ fun i _ => ?_
    refine Finset.measurable_fun_sum Finset.univ fun j _ => ?_
    exact ((hgram α i j).mul (hpart α j)).mul (hpart α i)
  have hρ (α : M) : Measurable (ρ α) := by
    exact ((chartAtlasPOU I M α).contMDiff.continuous).measurable
  have hqsum : Measurable qsum := by
    unfold qsum
    refine Finset.measurable_fun_sum S fun α _ => ?_
    exact (hρ α).mul (hq α)
  have hqsum_eq : ∀ᵐ x ∂(riemannianVolumeMeasure (I := I) (M := M) g),
      qsum x = g.inner x (gradFun (I := I) g u x) (gradFun (I := I) g u x) := by
    filter_upwards [hu] with x hx
    have hterm : ∀ α ∈ S,
        ρ α x * q α x = ρ α x *
          g.inner x (gradFun (I := I) g u x) (gradFun (I := I) g u x) := by
      intro α _
      by_cases hρα : ρ α x = 0
      · simp only [hρα, zero_mul]
      · have hxs : x ∈ source α := by
          apply (chartAtlasPOU_isSubordinate I M) α
          apply subset_closure
          simpa only [Function.mem_support, ρ] using hρα
        congr 1
        unfold q gram part
        simp only [Set.piecewise_eq_of_mem (source α) _ _ hxs]
        rw [extChartAtExt_apply_of_mem (I := I) (α := α)]
        · exact (grad_norm_sq_chart (I := I) g α hx hxs).symm
        · simpa only [source] using hxs
    calc
      qsum x = ∑ α ∈ S, ρ α x * q α x := rfl
      _ = ∑ α ∈ S, ρ α x *
          g.inner x (gradFun (I := I) g u x) (gradFun (I := I) g u x) :=
        Finset.sum_congr rfl hterm
      _ = (∑ α ∈ S, ρ α x) *
          g.inner x (gradFun (I := I) g u x) (gradFun (I := I) g u x) := by
        rw [Finset.sum_mul]
      _ = _ := by
        have hone : ∑ α ∈ S, ρ α x = 1 := by
          simpa only [S, ρ] using
            chartAtlasPOU_finset_sum_eq_one (I := I) (M := M) x
        rw [hone, one_mul]
  apply (Real.continuous_sqrt.measurable.comp hqsum).aestronglyMeasurable.congr
  filter_upwards [hqsum_eq] with x hx
  simpa only [Function.comp_apply] using congrArg Real.sqrt hx

/-- Every bounded intrinsically Lipschitz real function belongs to the
intrinsic first-order Sobolev space at every exponent. -/
theorem memW1p_of_lip
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (p : ENNReal)
    {u : M → ℝ} {L B : NNReal}
    (hu : ∀ x y, edist (u x) (u y) ≤ (L : ENNReal) *
      riemannianEDistOf (I := I) g x y)
    (hB : ∀ x, ‖u x‖₊ ≤ B) :
    MemW1pIntrinsicLp (I := I) (M := M) g p u := by
  haveI : IsFiniteMeasure
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  refine ⟨MemLp.of_bound (intrinsic_lip_cont (I := I) g hu).aestronglyMeasurable
      (B : ℝ) ?_, ?_⟩
  · exact Filter.Eventually.of_forall fun x => by
      exact_mod_cast hB x
  · refine ⟨(fun x => (gradFun (I := I) g u x : E)),
      weak_grad_of_lip (I := I) g hu hB, ?_⟩
    refine MemLp.of_bound (grad_norm_aesm (I := I) g
      (ae_mdiff_of_lip (I := I) g hu hB)) (L : ℝ) ?_
    exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact Geometry.Riemannian.grad_norm_le_lip_all (I := I) g hu

end IntrinsicLp
end Sobolev
end Analysis
end DifferentialGeometry
