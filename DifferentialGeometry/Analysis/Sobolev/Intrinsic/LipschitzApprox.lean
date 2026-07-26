import DifferentialGeometry.Analysis.Sobolev.Intrinsic.Lipschitz
import DifferentialGeometry.Analysis.Elliptic.MetricBounds
import DifferentialGeometry.Analysis.Sobolev.Manifold.Rellich
import DifferentialGeometry.Analysis.Sobolev.Manifold.MeasureBridgeUniform
import DifferentialGeometry.Analysis.Sobolev.Approximation.ContMDiffDenseLemmas
import DifferentialGeometry.Analysis.Sobolev.Approximation.ContMDiffDense
import DifferentialGeometry.Analysis.Sobolev.Chart.SmoothDensity.SmoothMulQuant
import DifferentialGeometry.Analysis.Sobolev.Intrinsic.EquivalenceForward
import DifferentialGeometry.Analysis.Calculus.CompactCutoff
import DifferentialGeometry.Geometry.Connection.ChartBridge.Gradient

/-!
# Chart control of gradient differences

This file records the pointwise quantitative bridge used when a bounded
intrinsically Lipschitz function is compared with a smooth chart-Sobolev
approximant.  The constant is uniform over the finite canonical partition of
unity and depends only on the background metric and that fixed atlas.
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
open DifferentialGeometry.Analysis.Sobolev.Chart.ChartTower

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private lemma raw_eq_smooth
    (α : M) (f : M → ℝ) :
    DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α f =
      DifferentialGeometry.Analysis.Sobolev.Chart.chartSmoothExt
        (I := I) (M := M) α f := by
  classical
  funext y
  unfold DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw
    DifferentialGeometry.Analysis.Sobolev.Chart.chartSmoothExt
  rw [DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_eq_preimage_symm
    (I := I) (M := M) α]
  rfl

private lemma raw_fderiv_eq
    [I.Boundaryless] (α : M) (f : M → ℝ)
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∈ DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
      (I := I) (M := M) α)
    (i : Fin (Module.finrank ℝ E)) :
    fderiv ℝ
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α f) y
        (EuclideanSpace.single i 1) =
      partialDeriv (E := E) i (scalarOnE (I := I) α f)
        ((toEuclidean (E := E)).symm y) := by
  classical
  have hopen : IsOpen
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) α
  have heq :
      DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α f =ᶠ[𝓝 y]
        (fun z => scalarOnE (I := I) α f ((toEuclidean (E := E)).symm z)) := by
    filter_upwards [hopen.mem_nhds hy] with z hz
    rw [DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw_apply_of_mem
      (I := I) α f hz]
    rfl
  rw [Filter.EventuallyEq.fderiv_eq heq]
  change fderiv ℝ (scalarOnE (I := I) α f ∘ (toEuclidean (E := E)).symm) y
      (EuclideanSpace.single i 1) = _
  rw [(toEuclidean (E := E)).symm.comp_right_fderiv,
    ContinuousLinearMap.coe_comp', Function.comp_apply]
  have hb : ((toEuclidean (E := E)).symm :
      EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) →L[ℝ] E)
      (EuclideanSpace.single i 1) = chartModelBasis E i := by
    rw [chartModelBasis_apply]
    rfl
  rw [hb]
  rfl

private lemma raw_sub_lip
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M) {u v : M → ℝ} {L B : NNReal}
    (hu : ∀ x y, edist (u x) (u y) ≤ (L : ENNReal) *
      riemannianEDistOf (I := I) g x y)
    (hB : ∀ x, ‖u x‖₊ ≤ B) (hv : ContMDiff I 𝓘(ℝ, ℝ) ∞ v) :
    ∃ C : NNReal, LipschitzWith C
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α
        (fun x => (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x * (u x - v x))) := by
  obtain ⟨Cu, hu_lip⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chart_pou_lip
      (I := I) (M := M) g α hu hB
  let fv : M → ℝ := fun x =>
    (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x * v x
  have hv_smooth : ContDiff ℝ ∞
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartSmoothExt
        (I := I) (M := M) α fv) := by
    exact DifferentialGeometry.Analysis.Sobolev.Chart.contDiff_chartSmoothExt_pou_mul
      (I := I) (M := M) α (chartAtlasPOU I M)
        (chartAtlasPOU_isSubordinate I M) hv
  have hv_compact : HasCompactSupport
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartSmoothExt
        (I := I) (M := M) α fv) := by
    exact DifferentialGeometry.Analysis.Sobolev.Chart.hasCompactSupport_chartSmoothExt_pou_mul
      (I := I) (M := M) α (chartAtlasPOU I M)
        (chartAtlasPOU_isSubordinate I M) v
  obtain ⟨Cv, hv_lip0⟩ : ∃ Cv : NNReal, LipschitzWith Cv
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartSmoothExt
        (I := I) (M := M) α fv) :=
    ContDiff.lipschitzWith_of_hasCompactSupport hv_compact hv_smooth (by simp)
  have hv_lip : LipschitzWith Cv
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α fv) := by
    rwa [raw_eq_smooth (I := I) (M := M) α fv]
  refine ⟨Cu + Cv, ?_⟩
  have hsub := hu_lip.sub hv_lip
  have heq :
      DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α
          (fun x => (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x * (u x - v x)) =
        fun y =>
          DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α
              (fun x => (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x * u x) y -
            DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α fv y := by
    funext y
    classical
    unfold DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw fv
    split_ifs <;> ring
  rw [heq]
  exact hsub

private lemma raw_wkp_eq
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (α : M) (u : M → ℝ) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
        (d := Module.finrank ℝ E) 1 2
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α
          (fun x => (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x * u x))
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α) =
      DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
        (d := Module.finrank ℝ E) 1 2
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
          (I := I) (M := M) (chartAtlasPOU I M) α u)
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α) := by
  refine DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_congr_ae
    (d := Module.finrank ℝ E) (by norm_num)
    (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) α) ?_
  exact (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed_eq_chartPushedRaw_pou_ae
    (I := I) (M := M) (chartAtlasPOU I M) α u).symm

private lemma grad_eq_pou
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    (g : SmoothRiemannianMetric I M) {u v : M → ℝ} {x : M}
    (hu : MDifferentiableAt I 𝓘(ℝ, ℝ) u x)
    (hv : MDifferentiableAt I 𝓘(ℝ, ℝ) v x) :
    gradFun (I := I) g (fun y => u y - v y) x =
      ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        gradFun (I := I) g (fun y =>
          (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) y * (u y - v y)) x := by
  classical
  let S : Finset M := chartAtlasPOU_finset (I := I) (M := M)
  let w : M → ℝ := fun y => u y - v y
  let f : M → M → ℝ := fun α y =>
    (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) y * w y
  have hw : w = S.sum f := by
    funext y
    simp only [w, f, Finset.sum_apply]
    change u y - v y = ∑ α ∈ S,
      (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) y * (u y - v y)
    rw [← Finset.sum_mul]
    simpa only [S, one_mul] using
      (congrArg (fun c : ℝ => c * (u y - v y))
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartAtlasPOU_finset_sum_eq_one
          (I := I) (M := M) y)).symm
  have hf : ∀ α ∈ S, MDifferentiableAt I 𝓘(ℝ, ℝ) (f α) x := by
    intro α _
    exact (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯).contMDiff.contMDiffAt.mdifferentiableAt
      (by simp) |>.mul (hu.sub hv)
  change gradFun (I := I) g w x = S.sum (fun α => gradFun (I := I) g (f α) x)
  rw [hw]
  exact DifferentialGeometry.Integral.Connection.gradFun_finset (I := I) g S f hf

private lemma gNorm_sum_le
    (g : SmoothRiemannianMetric I M) (x : M) {ι : Type*}
    (s : Finset ι) (v : ι → TangentSpace I x) :
    Real.sqrt (g.inner x (s.sum v) (s.sum v)) ≤
      s.sum (fun i => Real.sqrt (g.inner x (v i) (v i))) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      exact (DifferentialGeometry.Analysis.Laplacian.gNorm_add_le
        (I := I) (M := M) g x (v i) (s.sum v)).trans
          (by simpa only [add_comm] using
            add_le_add_right ih (Real.sqrt (g.inner x (v i) (v i))))

/-- At a common differentiability point, the metric norm of the gradient of a
difference is bounded by the sum of the norms of its canonical POU pieces. -/
theorem gNorm_sub_le_sum
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    (g : SmoothRiemannianMetric I M) {u v : M → ℝ} {x : M}
    (hu : MDifferentiableAt I 𝓘(ℝ, ℝ) u x)
    (hv : MDifferentiableAt I 𝓘(ℝ, ℝ) v x) :
    Real.sqrt (g.inner x
        (gradFun (I := I) g (fun y => u y - v y) x)
        (gradFun (I := I) g (fun y => u y - v y) x)) ≤
      ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        Real.sqrt (g.inner x
          (gradFun (I := I) g (fun y =>
            (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) y * (u y - v y)) x)
          (gradFun (I := I) g (fun y =>
            (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) y * (u y - v y)) x)) := by
  rw [grad_eq_pou (I := I) (M := M) g hu hv]
  exact gNorm_sum_le (I := I) (M := M) g x
    (chartAtlasPOU_finset (I := I) (M := M))
    (fun α => gradFun (I := I) g (fun y =>
      (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) y * (u y - v y)) x)

private noncomputable def gramSup
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M) : ℝ := by
  classical
  let K : Set M := tsupport
    ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
  by_cases hK : K.Nonempty
  · have hKc : IsCompact K := (isClosed_tsupport _).isCompact
    have hKs : K ⊆ (chartAt H α).source :=
      chartAtlasPOU_isSubordinate I M α
    have hc : ContinuousOn
        (chartInvGramMatrix_l1Sum (I := I) (M := M) g α) K :=
      (chartInvGramMatrix_l1Sum_continuousOn (I := I) (M := M) g α).mono hKs
    exact (hKc.image_of_continuousOn hc).bddAbove.choose
  · exact 0

private lemma gramSup_nonneg
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M) :
    0 ≤ gramSup (I := I) (M := M) g α := by
  classical
  unfold gramSup
  let K : Set M := tsupport
    ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
  by_cases hK : K.Nonempty
  · rw [dif_pos hK]
    have hKc : IsCompact K := (isClosed_tsupport _).isCompact
    have hKs : K ⊆ (chartAt H α).source :=
      chartAtlasPOU_isSubordinate I M α
    have hc : ContinuousOn
        (chartInvGramMatrix_l1Sum (I := I) (M := M) g α) K :=
      (chartInvGramMatrix_l1Sum_continuousOn (I := I) (M := M) g α).mono hKs
    obtain ⟨x, hx⟩ := hK
    exact (chartInvGramMatrix_l1Sum_nonneg
      (I := I) (M := M) g α x).trans
        ((hKc.image_of_continuousOn hc).bddAbove.choose_spec ⟨x, hx, rfl⟩)
  · rw [dif_neg hK]

private lemma gram_le_sup
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M) {x : M}
    (hx : x ∈ tsupport
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) :
    chartInvGramMatrix_l1Sum (I := I) (M := M) g α x ≤
      gramSup (I := I) (M := M) g α := by
  classical
  unfold gramSup
  let K : Set M := tsupport
    ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
  have hK : K.Nonempty := ⟨x, hx⟩
  rw [dif_pos hK]
  have hKc : IsCompact K := (isClosed_tsupport _).isCompact
  have hKs : K ⊆ (chartAt H α).source :=
    chartAtlasPOU_isSubordinate I M α
  have hc : ContinuousOn
      (chartInvGramMatrix_l1Sum (I := I) (M := M) g α) K :=
    (chartInvGramMatrix_l1Sum_continuousOn (I := I) (M := M) g α).mono hKs
  exact (hKc.image_of_continuousOn hc).bddAbove.choose_spec ⟨x, hx, rfl⟩

/-- The metric gradient error is bounded, on every active canonical chart, by
a single metric-dependent constant times the coordinate partial square sum. -/
theorem grad_sub_chart_le
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {α : M}, α ∈ chartAtlasPOU_finset (I := I) (M := M) →
      ∀ {u v : M → ℝ} {x : M},
        MDifferentiableAt I 𝓘(ℝ, ℝ) u x →
        MDifferentiableAt I 𝓘(ℝ, ℝ) v x →
        x ∈ tsupport
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) →
        g.inner x
            (gradFun (I := I) g (fun y ↦
              (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) y * (u y - v y)) x)
            (gradFun (I := I) g (fun y ↦
              (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) y * (u y - v y)) x) ≤
          C * ∑ i : Fin (Module.finrank ℝ E),
            (partialDeriv (E := E) i
              (scalarOnE (I := I) α (fun y ↦
                (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) y * (u y - v y)))
              (extChartAt I α x)) ^ 2 := by
  classical
  let S : Finset M := chartAtlasPOU_finset (I := I) (M := M)
  let C : ℝ := ∑ α ∈ S, gramSup (I := I) (M := M) g α
  refine ⟨C, Finset.sum_nonneg (fun α _ ↦ gramSup_nonneg
    (I := I) (M := M) g α), ?_⟩
  intro α hα u v x hu hv hx
  have hxsrc : x ∈ (chartAt H α).source :=
    chartAtlasPOU_isSubordinate I M α hx
  have hdiff : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y ↦ u y - v y) x := hu.sub hv
  have hlocal : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y ↦
      (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) y * (u y - v y)) x :=
    (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯).contMDiff.contMDiffAt.mdifferentiableAt
      (by simp) |>.mul hdiff
  have hbase := g_inner_gradFun_le_chartInvGramMatrix_l1Sum_mul_sum_sq_partials
    (I := I) (M := M) g α hlocal hxsrc
  have hcoef : chartInvGramMatrix_l1Sum (I := I) (M := M) g α x ≤ C := by
    refine (gram_le_sup (I := I) (M := M) g α hx).trans ?_
    exact Finset.single_le_sum
      (fun β _ ↦ gramSup_nonneg (I := I) (M := M) g β)
      (by simpa only [S] using hα)
  have hsum : 0 ≤ ∑ i : Fin (Module.finrank ℝ E),
      (partialDeriv (E := E) i
        (scalarOnE (I := I) α (fun y ↦
          (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) y * (u y - v y)))
        (extChartAt I α x)) ^ 2 :=
    Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
  exact hbase.trans (mul_le_mul_of_nonneg_right hcoef hsum)

private lemma local_grad_l2_le
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    (g : SmoothRiemannianMetric I M) (α : M)
    (hα : α ∈ chartAtlasPOU_finset (I := I) (M := M)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {u v : M → ℝ} {L B : NNReal},
      (∀ x y, edist (u x) (u y) ≤ (L : ENNReal) *
        riemannianEDistOf (I := I) g x y) →
      (∀ x, ‖u x‖₊ ≤ B) → ContMDiff I 𝓘(ℝ, ℝ) ∞ v →
      ∃ q : M → ℝ,
      (∀ x, 0 ≤ q x) ∧
      AEStronglyMeasurable[borel M] q
        (riemannianMeasure (I := I) g (chartAtlasPOU I M)) ∧
      (∀ᵐ x ∂riemannianMeasure (I := I) g (chartAtlasPOU I M),
        Real.sqrt (g.inner x
          (gradFun (I := I) g (fun y =>
            (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) y * (u y - v y)) x)
          (gradFun (I := I) g (fun y =>
            (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) y * (u y - v y)) x)) ≤ q x) ∧
      eLpNorm q 2 (riemannianMeasure (I := I) g (chartAtlasPOU I M)) ≤
        ENNReal.ofReal C *
        DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
          (d := Module.finrank ℝ E) 1 2
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α
            (fun x => (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x * (u x - v x)))
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α) := by
  classical
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  let K : Set M := tsupport
    ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
  have hKc : IsCompact K := (isClosed_tsupport _).isCompact
  have hKs : K ⊆ (chartAt H α).source :=
    chartAtlasPOU_isSubordinate I M α
  obtain ⟨Cg, hCg, hgrad⟩ := grad_sub_chart_le (I := I) (M := M) g
  obtain ⟨Cb, hCb, hbridge⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Chart.eLpNorm_riemannianMeasure_le_const_mul_eLpNorm_chartPushedRaw_uniform_of_subset
      (I := I) (M := M) g α hKc hKs (p := (2 : ENNReal))
        (by norm_num) (by norm_num)
  refine ⟨Cb * Real.sqrt Cg,
    mul_nonneg hCb.le (Real.sqrt_nonneg _), ?_⟩
  intro u v L B hu hB hv
  let f : M → ℝ := fun x =>
    (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x * (u x - v x)
  let raw : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α f
  let coord : M → EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) := fun x =>
    toEuclidean (E := E) (extChartAtExt (I := I) α x)
  let part : Fin (Module.finrank ℝ E) → M → ℝ := fun i x =>
    fderiv ℝ raw (coord x) (EuclideanSpace.single i 1)
  let q : M → ℝ := fun x => if x ∈ K then
    Real.sqrt (Cg * ∑ i : Fin (Module.finrank ℝ E), (part i x) ^ 2) else 0
  have hcoord : Measurable coord := by
    exact (toEuclidean (E := E)).continuous.measurable.comp
      (extChartAtExt_measurable (I := I) (α := α))
  have hpart (i : Fin (Module.finrank ℝ E)) : Measurable (part i) := by
    exact (measurable_fderiv_apply_const ℝ raw
      (EuclideanSpace.single i 1)).comp hcoord
  have hsum : Measurable (fun x : M =>
      ∑ i : Fin (Module.finrank ℝ E), (part i x) ^ 2) := by
    exact Finset.measurable_fun_sum Finset.univ fun i _ => (hpart i).pow_const 2
  have hq : Measurable q := by
    exact Measurable.ite (isClosed_tsupport _).measurableSet
      (Real.continuous_sqrt.measurable.comp (measurable_const.mul hsum)) measurable_const
  have hq_supp : tsupport q ⊆ K := by
    apply closure_minimal
    · intro x hx
      by_contra hxK
      exact hx (by simp only [q, if_neg hxK])
    · exact isClosed_tsupport _
  have hGq : ∀ᵐ x ∂riemannianMeasure (I := I) g (chartAtlasPOU I M),
      Real.sqrt (g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g f x)) ≤
        q x := by
    filter_upwards [DifferentialGeometry.Analysis.Sobolev.Chart.ae_mdiff_of_lip
      (I := I) (M := M) g hu hB] with x hux
    by_cases hxK : x ∈ K
    · have hxsrc : x ∈ (chartAt H α).source := hKs hxK
      have hvx : MDifferentiableAt I 𝓘(ℝ, ℝ) v x :=
        hv.mdifferentiable (by simp) x
      have hbase := hgrad (α := α) hα (u := u) (v := v) (x := x) hux hvx hxK
      have hcoordx : coord x = toEuclidean (E := E) (extChartAt I α x) := by
        simp only [coord, extChartAtExt_apply_of_mem (I := I) (α := α) hxsrc]
      have hpartx (i : Fin (Module.finrank ℝ E)) :
          part i x = partialDeriv (E := E) i (scalarOnE (I := I) α f)
            (extChartAt I α x) := by
        simp only [part]
        rw [hcoordx, raw_fderiv_eq (I := I) (M := M) α f]
        · simp only [ContinuousLinearEquiv.symm_apply_apply]
        · rw [DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_eq_preimage_symm]
          simp only [Set.mem_preimage, ContinuousLinearEquiv.symm_apply_apply]
          have hx0 : x ∈ (extChartAt I α).source := by
            rwa [extChartAt_source_eq_chartAt_source (I := I)]
          exact (extChartAt I α).map_source hx0
      simp only [q, if_pos hxK]
      refine Real.sqrt_le_sqrt ?_
      simpa only [f, hpartx] using hbase
    · have hρ :
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) =ᶠ[𝓝 x] 0 :=
        notMem_tsupport_iff_eventuallyEq.mp hxK
      have hf0 : f =ᶠ[𝓝 x] 0 := by
        filter_upwards [hρ] with y hy
        simp only [f, hy, zero_mul, Pi.zero_apply]
      have hg0 : gradFun (I := I) g f x = 0 :=
        gradFun_eq_zero_of_eventuallyEq_zero (I := I) g hf0
      simp only [q, if_neg hxK, hg0, map_zero,
        Real.sqrt_zero, le_refl]
  have hq_nonneg : ∀ x, 0 ≤ q x := by
    intro x
    simp only [q]
    split_ifs
    · exact Real.sqrt_nonneg _
    · exact le_rfl
  refine ⟨q, hq_nonneg,
    hq.aestronglyMeasurable, (by simpa only [f] using hGq), ?_⟩
  refine (hbridge hq hq_supp).trans ?_
  have hraw_lip := raw_sub_lip (I := I) (M := M) g α hu hB hv
  obtain ⟨Cr, hraw_lip⟩ := hraw_lip
  have hraw_compact : HasCompactSupport raw := by
    simpa only [raw, f] using
      DifferentialGeometry.Analysis.Sobolev.Chart.ChartTower.hasCompactSupport_chartPushedRaw_pou_mul
        (I := I) (M := M) α (fun x => u x - v x)
  have hchart_pt (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
      DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α q y ≤
        Real.sqrt Cg * Real.sqrt (∑ i : Fin (Module.finrank ℝ E),
          (fderiv ℝ raw y (EuclideanSpace.single i 1)) ^ 2) := by
    by_cases hy : y ∈ DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α
    · rw [DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw_apply_of_mem
        (I := I) α q hy]
      let x : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y)
      have hxsrc : x ∈ (chartAt H α).source := by
        have hx0 := (extChartAt I α).map_target
          ((DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_eq_preimage_symm
            (I := I) (M := M) α) ▸ hy)
        rwa [extChartAt_source_eq_chartAt_source (I := I)] at hx0
      by_cases hxK : x ∈ K
      · have hcoordxy : coord x = y := by
          have htgt : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
            simpa only [DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_eq_preimage_symm,
              Set.mem_preimage] using hy
          simp only [coord, x, extChartAtExt_apply_of_mem (I := I) (α := α) hxsrc,
            (extChartAt I α).right_inv htgt,
            ContinuousLinearEquiv.apply_symm_apply]
        change (if x ∈ K then
          Real.sqrt (Cg * ∑ i : Fin (Module.finrank ℝ E), (part i x) ^ 2) else 0) ≤ _
        rw [if_pos hxK, Real.sqrt_mul hCg]
        have hpartsum :
            (∑ i : Fin (Module.finrank ℝ E), (part i x) ^ 2) =
              ∑ i : Fin (Module.finrank ℝ E),
                (fderiv ℝ raw y (EuclideanSpace.single i 1)) ^ 2 := by
          apply Finset.sum_congr rfl
          intro i _
          simp only [part, hcoordxy]
        rw [hpartsum]
      · change (if x ∈ K then
          Real.sqrt (Cg * ∑ i : Fin (Module.finrank ℝ E), (part i x) ^ 2) else 0) ≤ _
        rw [if_neg hxK]
        exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    · rw [DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw_apply_of_notMem
        (I := I) α q hy]
      exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hchart_nonneg (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
      0 ≤ DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α q y := by
    by_cases hy : y ∈ DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α
    · rw [DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw_apply_of_mem
        (I := I) α q hy]
      simp only [q]
      split_ifs
      · exact Real.sqrt_nonneg _
      · exact le_rfl
    · rw [DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw_apply_of_notMem
        (I := I) α q hy]
  have hchart_norm :
      eLpNorm (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α q) 2
          (volume.restrict
            (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
              (I := I) (M := M) α)) ≤
        ENNReal.ofReal (Real.sqrt Cg) *
          DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
            (d := Module.finrank ℝ E) 1 2 raw
            (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
              (I := I) (M := M) α) := by
    have hmono_chart :
        eLpNorm (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α q) 2
            (volume.restrict
              (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
                (I := I) (M := M) α)) ≤
          eLpNorm (fun y => Real.sqrt Cg * Real.sqrt
            (∑ i : Fin (Module.finrank ℝ E),
              (fderiv ℝ raw y (EuclideanSpace.single i 1)) ^ 2)) 2
            (volume.restrict
              (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
                (I := I) (M := M) α)) := by
      apply eLpNorm_mono_ae_real
      exact Filter.Eventually.of_forall fun y => by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (hchart_nonneg y)] using hchart_pt y
    refine hmono_chart.trans ?_
    have hmul : (fun y => Real.sqrt Cg * Real.sqrt
        (∑ i : Fin (Module.finrank ℝ E),
          (fderiv ℝ raw y (EuclideanSpace.single i 1)) ^ 2)) =
        Real.sqrt Cg • (fun y => Real.sqrt
          (∑ i : Fin (Module.finrank ℝ E),
            (fderiv ℝ raw y (EuclideanSpace.single i 1)) ^ 2)) := by
      funext y
      simp only [Pi.smul_apply, smul_eq_mul]
    rw [hmul, eLpNorm_const_smul]
    simp only [Real.enorm_eq_ofReal_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    gcongr
    exact DifferentialGeometry.Analysis.Sobolev.Euclidean.partials_l2_le_wkp
      (d := Module.finrank ℝ E)
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
        (I := I) (M := M) α) hraw_lip hraw_compact
  refine (mul_le_mul_right hchart_norm (ENNReal.ofReal Cb)).trans ?_
  rw [← mul_assoc, ← ENNReal.ofReal_mul hCb.le]

/-- On a compact manifold, chart-Sobolev approximation controls the intrinsic
`L²` norm of the metric gradient error. -/
theorem grad_sub_l2_le
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {u v : M → ℝ} {L B : NNReal},
      (∀ x y, edist (u x) (u y) ≤ (L : ENNReal) *
        riemannianEDistOf (I := I) g x y) →
      (∀ x, ‖u x‖₊ ≤ B) → ContMDiff I 𝓘(ℝ, ℝ) ∞ v →
      eLpNorm (fun x : M => Real.sqrt (g.inner x
          (gradFun (I := I) g (fun y => u y - v y) x)
          (gradFun (I := I) g (fun y => u y - v y) x))) 2
        (riemannianMeasure (I := I) g (chartAtlasPOU I M)) ≤
      ENNReal.ofReal C * wkpNormChart (I := I) (M := M) g 1 2
        (fun x => u x - v x) := by
  classical
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  let S : Finset M := chartAtlasPOU_finset (I := I) (M := M)
  have hlocal (a : S) :=
    local_grad_l2_le (I := I) (M := M) g a.1 a.2
  choose C hC hlocal_bound using hlocal
  let Ctot : ℝ := ∑ a : S, C a
  have hCtot : 0 ≤ Ctot := Finset.sum_nonneg fun a _ => hC a
  refine ⟨Ctot, hCtot, ?_⟩
  intro u v L B hu hB hv
  have hmajor (a : S) := hlocal_bound a hu hB hv
  choose q hq_nonneg hq_meas hq_dom hq_bound using hmajor
  let n : S → M → ℝ := fun a x => Real.sqrt (g.inner x
    (gradFun (I := I) g (fun y =>
      (chartAtlasPOU I M a.1 : C^∞⟮I, M; ℝ⟯) y * (u y - v y)) x)
    (gradFun (I := I) g (fun y =>
      (chartAtlasPOU I M a.1 : C^∞⟮I, M; ℝ⟯) y * (u y - v y)) x))
  let W : S → ENNReal := fun a =>
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
      (d := Module.finrank ℝ E) 1 2
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I a.1
        (fun x => (chartAtlasPOU I M a.1 : C^∞⟮I, M; ℝ⟯) x * (u x - v x)))
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) a.1)
  have hdom_all : ∀ᵐ x ∂riemannianMeasure (I := I) g (chartAtlasPOU I M),
      ∀ a : S, n a x ≤ q a x := by
    rw [Filter.eventually_all]
    intro a
    simpa only [n] using hq_dom a
  have hmdiff : ∀ᵐ x ∂riemannianMeasure (I := I) g (chartAtlasPOU I M),
      MDifferentiableAt I 𝓘(ℝ, ℝ) u x :=
    DifferentialGeometry.Analysis.Sobolev.Chart.ae_mdiff_of_lip
      (I := I) (M := M) g hu hB
  have hglobal : ∀ᵐ x ∂riemannianMeasure (I := I) g (chartAtlasPOU I M),
      Real.sqrt (g.inner x
          (gradFun (I := I) g (fun y => u y - v y) x)
          (gradFun (I := I) g (fun y => u y - v y) x)) ≤
        ∑ a : S, q a x := by
    filter_upwards [hmdiff, hdom_all] with x hux hxdom
    have hvx : MDifferentiableAt I 𝓘(ℝ, ℝ) v x :=
      hv.mdifferentiable (by simp) x
    calc
      Real.sqrt (g.inner x
          (gradFun (I := I) g (fun y => u y - v y) x)
          (gradFun (I := I) g (fun y => u y - v y) x)) ≤
          ∑ α ∈ S, Real.sqrt (g.inner x
            (gradFun (I := I) g (fun y =>
              (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) y * (u y - v y)) x)
            (gradFun (I := I) g (fun y =>
              (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) y * (u y - v y)) x)) := by
        simpa only [S] using gNorm_sub_le_sum (I := I) (M := M) g hux hvx
      _ = ∑ a : S, n a x := by
        simpa only [n, Finset.attach_eq_univ] using
          (Finset.sum_attach S (fun α => Real.sqrt (g.inner x
            (gradFun (I := I) g (fun y =>
              (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) y * (u y - v y)) x)
            (gradFun (I := I) g (fun y =>
              (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) y * (u y - v y)) x)))).symm
      _ ≤ ∑ a : S, q a x := Finset.sum_le_sum fun a _ => hxdom a
  have hmono :
      eLpNorm (fun x : M => Real.sqrt (g.inner x
          (gradFun (I := I) g (fun y => u y - v y) x)
          (gradFun (I := I) g (fun y => u y - v y) x))) 2
          (riemannianMeasure (I := I) g (chartAtlasPOU I M)) ≤
        eLpNorm (fun x => ∑ a : S, q a x) 2
          (riemannianMeasure (I := I) g (chartAtlasPOU I M)) := by
    apply eLpNorm_mono_ae_real
    filter_upwards [hglobal] with x hx
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] using hx
  have hsum :
      eLpNorm (fun x => ∑ a : S, q a x) 2
          (riemannianMeasure (I := I) g (chartAtlasPOU I M)) ≤
        ∑ a : S, eLpNorm (q a) 2
          (riemannianMeasure (I := I) g (chartAtlasPOU I M)) := by
    have heq : (fun x => ∑ a : S, q a x) = ∑ a : S, q a := by
      funext x
      simp only [Finset.sum_apply]
    rw [heq]
    exact eLpNorm_sum_le (fun a _ => hq_meas a) (by norm_num)
  have hper : (∑ a : S, eLpNorm (q a) 2
        (riemannianMeasure (I := I) g (chartAtlasPOU I M))) ≤
      ∑ a : S, ENNReal.ofReal (C a) * W a := by
    exact Finset.sum_le_sum fun a _ => by
      simpa only [W] using hq_bound a
  have hconst : (∑ a : S, ENNReal.ofReal (C a) * W a) ≤
      ENNReal.ofReal Ctot * ∑ a : S, W a := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a _
    gcongr
    exact Finset.single_le_sum (fun b _ => hC b) (Finset.mem_univ a)
  have hWsum : (∑ a : S, W a) =
      wkpNormChart (I := I) (M := M) g 1 2 (fun x => u x - v x) := by
    rw [DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart_eq_finset_sum
      (I := I) (M := M) g 1 (by norm_num) (fun x => u x - v x)]
    change (∑ a : S, W a) = ∑ α ∈ S,
      DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
        (d := Module.finrank ℝ E) 1 2
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
          (I := I) (M := M) (chartAtlasPOU I M) α (fun x => u x - v x))
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α)
    calc
      (∑ a : S, W a) = ∑ a : S,
          DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
            (d := Module.finrank ℝ E) 1 2
            (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
              (I := I) (M := M) (chartAtlasPOU I M) a.1 (fun x => u x - v x))
            (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
              (I := I) (M := M) a.1) := by
        apply Finset.sum_congr rfl
        intro a _
        simpa only [W] using raw_wkp_eq (I := I) (M := M) a.1
          (fun x => u x - v x)
      _ = _ := Finset.sum_attach S (fun α =>
        DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
          (d := Module.finrank ℝ E) 1 2
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
            (I := I) (M := M) (chartAtlasPOU I M) α (fun x => u x - v x))
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α))
  refine hmono.trans (hsum.trans (hper.trans ?_))
  simpa only [hWsum] using hconst

/-- A bounded intrinsically Lipschitz function admits smooth approximants with
arbitrarily small intrinsic `L²` metric-gradient error. -/
theorem exists_smooth_grad
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    (g : SmoothRiemannianMetric I M) {u : M → ℝ} {L B : NNReal}
    (hu : ∀ x y, edist (u x) (u y) ≤ (L : ENNReal) *
      riemannianEDistOf (I := I) g x y)
    (hB : ∀ x, ‖u x‖₊ ≤ B) {ε : ℝ} (hε : 0 < ε) :
    ∃ v : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ v ∧
      eLpNorm (fun x : M => Real.sqrt (g.inner x
          (gradFun (I := I) g (fun y => u y - v y) x)
          (gradFun (I := I) g (fun y => u y - v y) x))) 2
        (riemannianMeasure (I := I) g (chartAtlasPOU I M)) ≤
      ENNReal.ofReal ε := by
  obtain ⟨C, hC, hgrad⟩ := grad_sub_l2_le (I := I) (M := M) g
  have hC1 : 0 < C + 1 := by linarith
  let δ : ℝ := ε / (C + 1)
  have hδ : 0 < δ := div_pos hε hC1
  have hu_chart : MemWkpChart (I := I) (M := M) g 1 2 u :=
    DifferentialGeometry.Analysis.Sobolev.Chart.mem_chart_one_of_lip
      (I := I) (M := M) g (by norm_num) hu hB
  obtain ⟨v, hv, happ⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Chart.contMDiff_dense_in_WkpChart
      (I := I) (M := M) g (p := (2 : ENNReal)) (by norm_num) (by norm_num)
        hu_chart hδ
  refine ⟨v, hv, hgrad hu hB hv |>.trans ?_⟩
  have hmul : C * δ ≤ ε := by
    change C * (ε / (C + 1)) ≤ ε
    calc
      C * (ε / (C + 1)) = (C * ε) / (C + 1) := by ring
      _ ≤ ε := (div_le_iff₀ hC1).2 (by nlinarith)
  calc
    ENNReal.ofReal C * wkpNormChart (I := I) (M := M) g 1 2
          (fun x => u x - v x) ≤
        ENNReal.ofReal C * ENNReal.ofReal δ :=
      mul_le_mul_right happ _
    _ = ENNReal.ofReal (C * δ) := by
      rw [ENNReal.ofReal_mul hC]
    _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal hmul

/-- A compactly supported bounded intrinsic-Lipschitz function admits smooth
approximants with the same prescribed open support margin and simultaneous
`L²` function and metric-gradient control. -/
theorem exists_smooth_supp
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    (g : SmoothRiemannianMetric I M) {u : M → ℝ} {L B : NNReal}
    (hu : ∀ x y, edist (u x) (u y) ≤ (L : ENNReal) *
      riemannianEDistOf (I := I) g x y)
    (hB : ∀ x, ‖u x‖₊ ≤ B) {U : Set M} (hU : IsOpen U)
    (huU : tsupport u ⊆ U) {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ φ ∧ tsupport φ ⊆ U ∧
      eLpNorm (fun x => u x - φ x) 2
          (riemannianVolumeMeasure I M g) ≤ ENNReal.ofReal ε ∧
      eLpNorm (fun x : M => Real.sqrt (g.inner x
          (gradFun (I := I) g (fun y => u y - φ y) x)
          (gradFun (I := I) g (fun y => u y - φ y) x))) 2
        (riemannianVolumeMeasure I M g) ≤ ENNReal.ofReal ε := by
  classical
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  obtain ⟨Cl2, hCl2, hl2⟩ :=
    DifferentialGeometry.Analysis.Sobolev.EquivalenceFull.eLpNorm_riemannianVolumeMeasure_le_const_mul_wkpNormChart_uniform
      (I := I) (M := M) g (p := (2 : ENNReal)) (by norm_num) (by norm_num)
  obtain ⟨Cg, hCg, hgrad⟩ := grad_sub_l2_le (I := I) (M := M) g
  obtain ⟨χ, hχ, _hχc, hχone, hχsupp, _hχrange⟩ :=
    DifferentialGeometry.Analysis.exists_mfd_bump
      (I := I) (M := M) (K := tsupport u) (U := U)
        (isClosed_tsupport u).isCompact hU huU
  let χs : C^∞⟮I, M; ℝ⟯ := ⟨χ, fun x => hχ.contMDiffAt⟩
  obtain ⟨Cm, hCm, hmul⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart_smooth_mul_le
      (I := I) (M := M) g 1 (p := (2 : ENNReal)) (by norm_num) (by norm_num) χs
  let D : ℝ := (Cl2 + Cg) * Cm
  have hD : 0 ≤ D := mul_nonneg (add_nonneg hCl2 hCg) hCm.le
  have hD1 : 0 < D + 1 := by linarith
  let δ : ℝ := ε / (D + 1)
  have hδ : 0 < δ := div_pos hε hD1
  have hu_chart : MemWkpChart (I := I) (M := M) g 1 2 u :=
    DifferentialGeometry.Analysis.Sobolev.Chart.mem_chart_one_of_lip
      (I := I) (M := M) g (by norm_num) hu hB
  obtain ⟨v, hv, happ⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Chart.contMDiff_dense_in_WkpChart
      (I := I) (M := M) g (p := (2 : ENNReal)) (by norm_num) (by norm_num)
        hu_chart hδ
  let φ : M → ℝ := fun x => χ x * v x
  have hφ : ContMDiff I 𝓘(ℝ, ℝ) ∞ φ := hχ.mul hv
  have hφsupp : tsupport φ ⊆ U := by
    refine (closure_minimal ?_ (isClosed_tsupport χ)).trans hχsupp
    intro x hx
    apply subset_closure
    intro hχx
    exact hx (by simp only [φ, hχx, zero_mul])
  have hχu : (fun x => χ x * u x) = u := by
    funext x
    by_cases hx : x ∈ tsupport u
    · have hχx : χ x = 1 := by
        simpa only [Pi.one_apply] using hχone.self_of_nhdsSet hx
      rw [hχx, one_mul]
    · have hux : u x = 0 := by
        by_contra hux
        exact hx (subset_closure hux)
      rw [hux, mul_zero]
  have herr : (fun x => u x - φ x) = fun x => χ x * (u x - v x) := by
    funext x
    have hx := congrFun hχu x
    simp only [φ] at hx ⊢
    linarith
  have hv_chart : MemWkpChart (I := I) (M := M) g 1 2 v :=
    DifferentialGeometry.Analysis.Sobolev.Equivalence.MemWkpChart_of_contMDiff
      (I := I) (M := M) g (by norm_num) hv
  have hdiff_chart : MemWkpChart (I := I) (M := M) g 1 2
      (fun x => u x - v x) :=
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart_sub
      (I := I) (M := M) g (by norm_num) hu_chart hv_chart
  have hchart : wkpNormChart (I := I) (M := M) g 1 2
      (fun x => u x - φ x) ≤
      ENNReal.ofReal Cm * ENNReal.ofReal δ := by
    rw [herr]
    exact (hmul hdiff_chart).trans (mul_le_mul_right happ _)
  have hbase : D * δ ≤ ε := by
    change D * (ε / (D + 1)) ≤ ε
    calc
      D * (ε / (D + 1)) = (D * ε) / (D + 1) := by ring
      _ ≤ ε := (div_le_iff₀ hD1).2 (by nlinarith)
  have hCl2D : Cl2 * Cm ≤ D := by
    dsimp only [D]
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hCg) hCm.le
  have hCgD : Cg * Cm ≤ D := by
    dsimp only [D]
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hCl2) hCm.le
  have hl2scale : Cl2 * Cm * δ ≤ ε :=
    (mul_le_mul_of_nonneg_right hCl2D hδ.le).trans hbase
  have hgscale : Cg * Cm * δ ≤ ε :=
    (mul_le_mul_of_nonneg_right hCgD hδ.le).trans hbase
  refine ⟨φ, hφ, hφsupp, ?_, ?_⟩
  · have hu_cont : Continuous u :=
      DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.intrinsic_lip_cont
        (I := I) (M := M) g hu
    have hφ_cont : Continuous φ := hφ.continuous
    have herr_meas : Measurable (fun x => u x - φ x) :=
      (hu_cont.sub hφ_cont).measurable
    refine (hl2 herr_meas).trans ((mul_le_mul_right hchart _).trans ?_)
    calc
      ENNReal.ofReal Cl2 * (ENNReal.ofReal Cm * ENNReal.ofReal δ) =
          ENNReal.ofReal (Cl2 * Cm * δ) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hCl2,
          ← ENNReal.ofReal_mul (mul_nonneg hCl2 hCm.le)]
      _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal hl2scale
  · refine (hgrad hu hB hφ).trans ((mul_le_mul_right hchart _).trans ?_)
    calc
      ENNReal.ofReal Cg * (ENNReal.ofReal Cm * ENNReal.ofReal δ) =
          ENNReal.ofReal (Cg * Cm * δ) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hCg,
          ← ENNReal.ofReal_mul (mul_nonneg hCg hCm.le)]
      _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal hgscale

end IntrinsicLp
end Sobolev
end Analysis
end DifferentialGeometry
