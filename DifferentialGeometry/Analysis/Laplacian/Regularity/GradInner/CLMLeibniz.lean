import DifferentialGeometry.Analysis.Laplacian.Regularity.GradInner.CLM
import DifferentialGeometry.Analysis.Laplacian.Regularity.LaplacianDomain.SmoothMulH1Compl
import DifferentialGeometry.Analysis.Laplacian.Regularity.SmoothScalar.MulLp
import DifferentialGeometry.Analysis.Laplacian.Regularity.LaplacianDomain.L2Inclusion
import DifferentialGeometry.Analysis.Laplacian.Regularity.LaplacianDomain.ChartData
import DifferentialGeometry.Geometry.NormGradSq

/-!
# Leibniz identity for `gradInnerCLM` on `H1Compl`

For a closed Riemannian manifold `(M, g)` and a bundled smooth function
`ρα : C^∞⟮I, M; ℝ⟯`, the **pointwise gradient Leibniz rule**
`∇(ρα · v) = ρα · ∇v + v · ∇ρα` for smooth `ρα, v` yields, after taking the
metric inner product with `∇ρα`,

```
g(∇ρα, ∇(ρα · v)) = ρα · g(∇ρα, ∇v) + |∇ρα|²_g · v.
```

Rearranging,

```
ρα · g(∇ρα, ∇v) = g(∇ρα, ∇(ρα · v)) − |∇ρα|²_g · v.
```

Both sides are bilinear in `(ρα, v)`. We package this identity at the
`Lp ℝ 2 μ_g` class level, first for smooth `v ∈ SmoothScalar g`, and then
extend by `H1Compl`-density to all `u_h ∈ H1Compl g`:

```
smoothMulLp g ρα (gradInnerCLM g ρα u_h)
  = gradInnerCLM g ρα (smoothMulH1Compl g ρα u_h)
    − smoothMulLp g (gradRhoSqSmooth g ρα) (H1ComplToLp u_h).
```

Both sides of this identity are continuous linear maps `H1Compl g →L[ℝ]
Lp ℝ 2 μ_g`. The first ingredient `smoothMulLp g ρα ∘ gradInnerCLM g ρα`
multiplies the gradient inner product by `ρα`. The second ingredient
`gradInnerCLM g ρα ∘ smoothMulH1Compl g ρα` first multiplies `u_h` by `ρα`
inside the H¹-completion (using `smoothMulH1Compl`, which preserves H¹ regularity)
and then takes the gradient inner product with `∇ρα`. The third ingredient
`smoothMulLp g (gradRhoSqSmooth g ρα) ∘ H1ComplToLp` multiplies `u_h.coeFn`
by the smooth bounded scalar `|∇ρα|²_g`.

## Main results

* `gradRhoSqSmooth` : the smooth scalar function `x ↦ g(∇ρα(x), ∇ρα(x))`
  packaged as a `C^∞⟮I, M; ℝ⟯` bundle.
* `gradInner_leibniz_pointwise` : the pointwise smooth Leibniz identity
  `ρα · g(∇ρα, ∇v) = g(∇ρα, ∇(ρα · v)) − |∇ρα|²_g · v`.
* `gradInner_leibniz_smooth_Lp` : the Lp-class smooth-case Leibniz identity.
* `gradInner_leibniz_H1Compl` : the Lp-class identity at `H1Compl g`,
  obtained by H¹Compl-density extension of the smooth-case identity.

## Strategy

The H¹Compl extension proceeds via the standard density-extension pattern:
both sides of the desired identity are continuous linear maps from
`H1Compl g` into `Lp ℝ 2 μ_g`. Agreement on the dense range of
`smoothToH1Compl` (the smooth-case identity) extends to agreement on all of
`H1Compl g` by continuity.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter Topology Function
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace GradInnerCLMLeibniz

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainChartData
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Sobolev.Chart

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

/-- The pointwise squared metric norm of `∇ρα`, packaged as a bundled smooth
map `M → ℝ`. -/
noncomputable def gradRhoSqSmooth
    (g : SmoothRiemannianMetric I M) (ρα : C^∞⟮I, M; ℝ⟯) :
    C^∞⟮I, M; ℝ⟯ :=
  ⟨normGradSqFun (I := I) g (ρα : M → ℝ),
    normGradSqFun_contMDiff (I := I) g ρα.contMDiff⟩

@[simp] lemma gradRhoSqSmooth_apply
    (g : SmoothRiemannianMetric I M) (ρα : C^∞⟮I, M; ℝ⟯) (x : M) :
    (gradRhoSqSmooth (I := I) (M := M) g ρα : M → ℝ) x =
      g.inner x (gradFun (I := I) g ρα x) (gradFun (I := I) g ρα x) := rfl

/-- **Pointwise smooth Leibniz identity** for the gradient inner product. -/
lemma gradInner_leibniz_pointwise
    (g : SmoothRiemannianMetric I M) (ρα : C^∞⟮I, M; ℝ⟯)
    (v : SmoothScalar g) (x : M) :
    (ρα : M → ℝ) x *
        g.inner x (gradFun (I := I) g ρα x)
          (gradFun (I := I) g v.toFun x) =
      g.inner x (gradFun (I := I) g ρα x)
          (gradFun (I := I) g
            (smoothScalarMulFun (I := I) (M := M) g ρα v).toFun x) -
        (gradRhoSqSmooth (I := I) (M := M) g ρα : M → ℝ) x * v.toFun x := by
  classical
  have h_grad := gradFun_smoothScalarMulFun (I := I) (M := M) g ρα v x
  rw [h_grad]
  rw [ContinuousLinearMap.map_add, ContinuousLinearMap.map_smul,
    ContinuousLinearMap.map_smul]
  simp only [smul_eq_mul, gradRhoSqSmooth_apply]
  ring

/-- **Smooth Leibniz identity at the Lp class level**: for smooth `v`,
```
smoothMulLp g ρα (gradInnerSmooth g ρα v)
  = gradInnerSmooth g ρα (smoothScalarMulFun g ρα v)
    − smoothMulLp g (gradRhoSqSmooth g ρα) (smoothToLp g v).
``` -/
theorem gradInner_leibniz_smooth_Lp
    (g : SmoothRiemannianMetric I M) (ρα : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    smoothMulLp (I := I) (M := M) g ρα
        (gradInnerSmooth (I := I) (M := M) g ρα v) =
      gradInnerSmooth (I := I) (M := M) g ρα
          (smoothScalarMulFun (I := I) (M := M) g ρα v) -
        smoothMulLp (I := I) (M := M) g
          (gradRhoSqSmooth (I := I) (M := M) g ρα)
          (smoothToLp (I := I) (M := M) g v) := by
  classical
  apply MeasureTheory.Lp.ext
  have h_lhs_aeEq : (smoothMulLp (I := I) (M := M) g ρα
        (gradInnerSmooth (I := I) (M := M) g ρα v) :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
      fun x : M => (ρα : M → ℝ) x *
        g.inner x (gradFun (I := I) g ρα x)
          (gradFun (I := I) g v.toFun x) := by
    have h1 := smoothMulLp_apply_coeFn (I := I) (M := M) g ρα
      (gradInnerSmooth (I := I) (M := M) g ρα v)
    have h2 := gradInnerSmooth_coeFn (I := I) (M := M) g ρα v
    refine h1.trans ?_
    filter_upwards [h2] with x hx
    rw [hx]
  have h_rhs1_aeEq : (gradInnerSmooth (I := I) (M := M) g ρα
        (smoothScalarMulFun (I := I) (M := M) g ρα v) :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
      fun x : M =>
        g.inner x (gradFun (I := I) g ρα x)
          (gradFun (I := I) g
            (smoothScalarMulFun (I := I) (M := M) g ρα v).toFun x) :=
    gradInnerSmooth_coeFn (I := I) (M := M) g ρα
      (smoothScalarMulFun (I := I) (M := M) g ρα v)
  have h_rhs2_aeEq : (smoothMulLp (I := I) (M := M) g
        (gradRhoSqSmooth (I := I) (M := M) g ρα)
        (smoothToLp (I := I) (M := M) g v) :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
      fun x : M =>
        (gradRhoSqSmooth (I := I) (M := M) g ρα : M → ℝ) x * v.toFun x := by
    have h1 := smoothMulLp_apply_coeFn (I := I) (M := M) g
      (gradRhoSqSmooth (I := I) (M := M) g ρα)
      (smoothToLp (I := I) (M := M) g v)
    have h2 : ((smoothToLp (I := I) (M := M) g v :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) =ᵐ[
          riemannianVolumeMeasure (I := I) (M := M) g] v.toFun :=
      MeasureTheory.MemLp.coeFn_toLp v.memLp_two
    refine h1.trans ?_
    filter_upwards [h2] with x hx
    rw [hx]
  have h_diff_coe := MeasureTheory.Lp.coeFn_sub
    (gradInnerSmooth (I := I) (M := M) g ρα
      (smoothScalarMulFun (I := I) (M := M) g ρα v))
    (smoothMulLp (I := I) (M := M) g
      (gradRhoSqSmooth (I := I) (M := M) g ρα)
      (smoothToLp (I := I) (M := M) g v))
  refine h_lhs_aeEq.trans ?_
  refine EventuallyEq.symm ?_
  filter_upwards [h_diff_coe, h_rhs1_aeEq, h_rhs2_aeEq]
    with x hx_diff hx_rhs1 hx_rhs2
  rw [hx_diff, Pi.sub_apply, hx_rhs1, hx_rhs2]
  exact (gradInner_leibniz_pointwise (I := I) (M := M) g ρα v x).symm

/-- The LHS CLM: `u_h ↦ smoothMulLp g ρα (gradInnerCLM g ρα u_h)`. -/
noncomputable def leibnizLhsCLM
    (g : SmoothRiemannianMetric I M) (ρα : C^∞⟮I, M; ℝ⟯) :
    H1Compl g →L[ℝ] Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  (smoothMulLp (I := I) (M := M) g ρα).comp
    (gradInnerCLM (I := I) (M := M) g ρα)

@[simp] lemma leibnizLhsCLM_apply
    (g : SmoothRiemannianMetric I M) (ρα : C^∞⟮I, M; ℝ⟯) (u_h : H1Compl g) :
    leibnizLhsCLM (I := I) (M := M) g ρα u_h =
      smoothMulLp (I := I) (M := M) g ρα
        (gradInnerCLM (I := I) (M := M) g ρα u_h) := rfl

/-- The RHS CLM: `u_h ↦ gradInnerCLM g ρα (smoothMulH1Compl g ρα u_h)
      - smoothMulLp g (|∇ρα|²_g) (H1ComplToLp u_h)`. -/
noncomputable def leibnizRhsCLM
    (g : SmoothRiemannianMetric I M) (ρα : C^∞⟮I, M; ℝ⟯) :
    H1Compl g →L[ℝ] Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  (gradInnerCLM (I := I) (M := M) g ρα).comp
    (smoothMulH1Compl (I := I) (M := M) g ρα) -
  (smoothMulLp (I := I) (M := M) g
    (gradRhoSqSmooth (I := I) (M := M) g ρα)).comp
    (H1ComplToLp (I := I) (M := M) g)

@[simp] lemma leibnizRhsCLM_apply
    (g : SmoothRiemannianMetric I M) (ρα : C^∞⟮I, M; ℝ⟯) (u_h : H1Compl g) :
    leibnizRhsCLM (I := I) (M := M) g ρα u_h =
      gradInnerCLM (I := I) (M := M) g ρα
          (smoothMulH1Compl (I := I) (M := M) g ρα u_h) -
        smoothMulLp (I := I) (M := M) g
          (gradRhoSqSmooth (I := I) (M := M) g ρα)
          (H1ComplToLp (I := I) (M := M) g u_h) := by
  unfold leibnizRhsCLM
  rfl

/-- **Smooth-case agreement**: `leibnizLhsCLM` and `leibnizRhsCLM` agree on
`smoothToH1Compl g v` for every `v : SmoothScalar g`. -/
private lemma leibnizCLM_agree_on_smooth
    (g : SmoothRiemannianMetric I M) (ρα : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    leibnizLhsCLM (I := I) (M := M) g ρα
        (smoothToH1Compl (I := I) (M := M) g v) =
      leibnizRhsCLM (I := I) (M := M) g ρα
          (smoothToH1Compl (I := I) (M := M) g v) := by
  classical
  rw [leibnizLhsCLM_apply, leibnizRhsCLM_apply]
  rw [gradInnerCLM_smoothToH1Compl]
  rw [smoothMulH1Compl_smoothToH1Compl, gradInnerCLM_smoothToH1Compl,
    H1ComplToLp_smoothToH1Compl]
  exact gradInner_leibniz_smooth_Lp (I := I) (M := M) g ρα v

/-- `smoothToH1Compl` has dense range. -/
private lemma denseRange_smoothToH1Compl_aux
    (g : SmoothRiemannianMetric I M) :
    DenseRange (smoothToH1Compl (I := I) (M := M) g) := by
  unfold smoothToH1Compl
  rw [show (UniformSpace.Completion.toComplL : SmoothScalar g → H1Compl g) =
      ((↑) : SmoothScalar g → UniformSpace.Completion (SmoothScalar g)) from
      UniformSpace.Completion.coe_toComplL]
  exact UniformSpace.Completion.denseRange_coe

/-- **H¹Compl Leibniz identity at the CLM level**: the two CLMs `leibnizLhsCLM`
and `leibnizRhsCLM` are equal. -/
theorem leibnizLhsCLM_eq_leibnizRhsCLM
    (g : SmoothRiemannianMetric I M) (ρα : C^∞⟮I, M; ℝ⟯) :
    leibnizLhsCLM (I := I) (M := M) g ρα =
      leibnizRhsCLM (I := I) (M := M) g ρα := by
  classical
  apply ContinuousLinearMap.ext
  intro u_h
  have h_eq_on_range :
      ∀ v : SmoothScalar g,
        (leibnizLhsCLM (I := I) (M := M) g ρα :
            H1Compl g → Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
          (smoothToH1Compl (I := I) (M := M) g v) =
        (leibnizRhsCLM (I := I) (M := M) g ρα :
            H1Compl g → Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
          (smoothToH1Compl (I := I) (M := M) g v) :=
    leibnizCLM_agree_on_smooth (I := I) (M := M) g ρα
  have h_eq_funs : (leibnizLhsCLM (I := I) (M := M) g ρα :
        H1Compl g → Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) =
      (leibnizRhsCLM (I := I) (M := M) g ρα :
        H1Compl g → Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) := by
    apply DenseRange.equalizer (denseRange_smoothToH1Compl_aux
      (I := I) (M := M) g) (leibnizLhsCLM (I := I) (M := M) g ρα).continuous
      (leibnizRhsCLM (I := I) (M := M) g ρα).continuous
    funext v
    exact h_eq_on_range v
  exact congr_fun h_eq_funs u_h

/-- **Headline Leibniz identity at `H1Compl g`**: for every `u_h ∈ H1Compl g`,
```
smoothMulLp g ρα (gradInnerCLM g ρα u_h)
  = gradInnerCLM g ρα (smoothMulH1Compl g ρα u_h)
    − smoothMulLp g (gradRhoSqSmooth g ρα) (H1ComplToLp u_h).
```
This generalises the smooth pointwise identity `ρα · g(∇ρα, ∇v) =
g(∇ρα, ∇(ρα · v)) − |∇ρα|²_g · v` to non-smooth `H1Compl`-completion
elements. -/
theorem gradInner_leibniz_H1Compl
    (g : SmoothRiemannianMetric I M) (ρα : C^∞⟮I, M; ℝ⟯) (u_h : H1Compl g) :
    smoothMulLp (I := I) (M := M) g ρα
        (gradInnerCLM (I := I) (M := M) g ρα u_h) =
      gradInnerCLM (I := I) (M := M) g ρα
          (smoothMulH1Compl (I := I) (M := M) g ρα u_h) -
        smoothMulLp (I := I) (M := M) g
          (gradRhoSqSmooth (I := I) (M := M) g ρα)
          (H1ComplToLp (I := I) (M := M) g u_h) := by
  have h := congr_fun (congrArg DFunLike.coe
    (leibnizLhsCLM_eq_leibnizRhsCLM (I := I) (M := M) g ρα)) u_h
  rw [leibnizLhsCLM_apply, leibnizRhsCLM_apply] at h
  exact h

variable [NeZero (Module.finrank ℝ E)]

/-- Chart-pulled-raw distribution over subtraction of Lp classes. -/
lemma chartPushedRawLpFromLp_coeFn_sub
    (g : SmoothRiemannianMetric I M) (α : M)
    (F G : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    ((chartPushedRawLpFromLp (I := I) (M := M) g α (F - G) :
        Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) =ᵐ[
        (chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      (fun y => ((chartPushedRawLpFromLp (I := I) (M := M) g α F :
        Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) y -
        ((chartPushedRawLpFromLp (I := I) (M := M) g α G :
          Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) y) := by
  classical
  have h_FG_coeFn := chartPushedRawLpFromLp_coeFn (I := I) (M := M) g α (F - G)
  have h_F_coeFn := chartPushedRawLpFromLp_coeFn (I := I) (M := M) g α F
  have h_G_coeFn := chartPushedRawLpFromLp_coeFn (I := I) (M := M) g α G
  set diffFun : M → ℝ := fun x =>
    ((F : Lp ℝ 2 _) : M → ℝ) x - ((G : Lp ℝ 2 _) : M → ℝ) x with hdiffFun_def
  have h_sub_coe : ((F - G : Lp ℝ 2 _) : M → ℝ) =ᵐ[
      riemannianVolumeMeasure (I := I) (M := M) g] diffFun :=
    MeasureTheory.Lp.coeFn_sub F G
  have h_FG_meas : Measurable ((F - G : Lp ℝ 2 _) : M → ℝ) :=
    (Lp.stronglyMeasurable (F - G)).measurable
  have hF_meas : Measurable ((F : Lp ℝ 2 _) : M → ℝ) :=
    (Lp.stronglyMeasurable F).measurable
  have hG_meas : Measurable ((G : Lp ℝ 2 _) : M → ℝ) :=
    (Lp.stronglyMeasurable G).measurable
  have hdiff_meas : Measurable diffFun := hF_meas.sub hG_meas
  have h_chartPushedRaw_FG :
      chartPushedRaw (I := I) α ((F - G : Lp ℝ 2 _) : M → ℝ) =ᵐ[
        (chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      chartPushedRaw (I := I) α diffFun :=
    chartPushedRaw_aeEq_of_aeEq (I := I) (M := M) g α
      h_FG_meas hdiff_meas h_sub_coe
  have h_chartPushedRaw_diff_pointwise :
      ∀ y : EuclN,
        chartPushedRaw (I := I) α diffFun y =
          chartPushedRaw (I := I) α ((F : Lp ℝ 2 _) : M → ℝ) y -
            chartPushedRaw (I := I) α ((G : Lp ℝ 2 _) : M → ℝ) y := by
    intro y
    by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) α
    · rw [chartPushedRaw_apply_of_mem (I := I) (M := M) (α := α) diffFun hy,
        chartPushedRaw_apply_of_mem (I := I) (M := M) (α := α)
          ((F : Lp ℝ 2 _) : M → ℝ) hy,
        chartPushedRaw_apply_of_mem (I := I) (M := M) (α := α)
          ((G : Lp ℝ 2 _) : M → ℝ) hy]
    · rw [chartPushedRaw_apply_of_notMem (I := I) (M := M) (α := α) diffFun hy,
        chartPushedRaw_apply_of_notMem (I := I) (M := M) (α := α)
          ((F : Lp ℝ 2 _) : M → ℝ) hy,
        chartPushedRaw_apply_of_notMem (I := I) (M := M) (α := α)
          ((G : Lp ℝ 2 _) : M → ℝ) hy]
      ring
  filter_upwards [h_FG_coeFn, h_F_coeFn, h_G_coeFn, h_chartPushedRaw_FG]
    with y hy_FG hy_F hy_G hy_chart
  rw [hy_FG, hy_chart, h_chartPushedRaw_diff_pointwise y]
  rw [← hy_F, ← hy_G]

/-- The chart-pull of `smoothMulLp g φ F` equals `(φ ∘ symm) · chartPushedRawLpFromLp F` ae
on the chart-pulled weighted measure restricted to chartTarget. -/
private lemma chartPushedRawLpFromLp_smoothMulLp_coeFn
    (g : SmoothRiemannianMetric I M) (α : M) (φ : C^∞⟮I, M; ℝ⟯)
    (F : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    ((chartPushedRawLpFromLp (I := I) (M := M) g α
        (smoothMulLp (I := I) (M := M) g φ F) :
        Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) =ᵐ[
        (chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      (fun y =>
        chartPushedRaw (I := I) α (fun x : M => (φ : M → ℝ) x) y *
        ((chartPushedRawLpFromLp (I := I) (M := M) g α F :
          Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) y) := by
  classical
  have h_smoothMulLp_coeFn := chartPushedRawLpFromLp_coeFn (I := I) (M := M) g α
    (smoothMulLp (I := I) (M := M) g φ F)
  have h_F_coeFn := chartPushedRawLpFromLp_coeFn (I := I) (M := M) g α F
  have h_M_aeEq : ((smoothMulLp (I := I) (M := M) g φ F :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
      (fun x : M => (φ : M → ℝ) x * ((F : Lp ℝ 2 _) : M → ℝ) x) :=
    smoothMulLp_apply_coeFn (I := I) (M := M) g φ F
  have hF_meas : Measurable ((F : Lp ℝ 2 _) : M → ℝ) :=
    (Lp.stronglyMeasurable F).measurable
  have h_smoothMulLp_meas :
      Measurable ((smoothMulLp (I := I) (M := M) g φ F :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) :=
    (Lp.stronglyMeasurable _).measurable
  have h_prod_meas :
      Measurable (fun x : M => (φ : M → ℝ) x * ((F : Lp ℝ 2 _) : M → ℝ) x) :=
    φ.contMDiff.continuous.measurable.mul hF_meas
  have h_chartPushedRaw_aeEq :
      chartPushedRaw (I := I) α
        ((smoothMulLp (I := I) (M := M) g φ F :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) =ᵐ[
        (chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      chartPushedRaw (I := I) α
        (fun x : M => (φ : M → ℝ) x * ((F : Lp ℝ 2 _) : M → ℝ) x) :=
    chartPushedRaw_aeEq_of_aeEq (I := I) (M := M) g α
      h_smoothMulLp_meas h_prod_meas h_M_aeEq
  have h_pointwise : ∀ y : EuclN,
      chartPushedRaw (I := I) α
          (fun x : M => (φ : M → ℝ) x * ((F : Lp ℝ 2 _) : M → ℝ) x) y =
        chartPushedRaw (I := I) α (fun x : M => (φ : M → ℝ) x) y *
          chartPushedRaw (I := I) α ((F : Lp ℝ 2 _) : M → ℝ) y := by
    intro y
    by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) α
    · rw [chartPushedRaw_apply_of_mem (I := I) (M := M) (α := α) _ hy,
        chartPushedRaw_apply_of_mem (I := I) (M := M) (α := α)
          (fun x : M => (φ : M → ℝ) x) hy,
        chartPushedRaw_apply_of_mem (I := I) (M := M) (α := α)
          ((F : Lp ℝ 2 _) : M → ℝ) hy]
    · rw [chartPushedRaw_apply_of_notMem (I := I) (M := M) (α := α) _ hy,
        chartPushedRaw_apply_of_notMem (I := I) (M := M) (α := α)
          (fun x : M => (φ : M → ℝ) x) hy,
        chartPushedRaw_apply_of_notMem (I := I) (M := M) (α := α)
          ((F : Lp ℝ 2 _) : M → ℝ) hy]
      ring
  filter_upwards [h_smoothMulLp_coeFn, h_F_coeFn, h_chartPushedRaw_aeEq]
    with y hy_smoothMul hy_F hy_chart
  rw [hy_smoothMul, hy_chart, h_pointwise y]
  rw [← hy_F]

/-- **Chart-pulled Leibniz identity**: chart-pulling the M-side identity
`smoothMulLp ρα (gradInnerCLM ρα u_h) = gradInnerCLM ρα (smoothMulH1Compl ρα u_h)
− smoothMulLp (|∇ρα|²_g) (H1ComplToLp u_h)` via `chartPushedRawLpFromLp g α`
produces an ae-identity on the chart-pulled weighted measure restricted to
`chartTargetEuclid α`. The chart-pulled LHS is the chart-pull of
`ρα · g(∇ρα, ∇u_h)`, the chart-pulled RHS is expressed by chart-pulling each
summand of the M-side identity. -/
theorem chartPushedRawLpFromLp_gradInner_leibniz_H1Compl
    (g : SmoothRiemannianMetric I M) (α : M) (ρα : C^∞⟮I, M; ℝ⟯)
    (u_h : H1Compl g) :
    ((chartPushedRawLpFromLp (I := I) (M := M) g α
        (smoothMulLp (I := I) (M := M) g ρα
          (gradInnerCLM (I := I) (M := M) g ρα u_h)) :
        Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) =ᵐ[
        (chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      (fun y =>
        ((chartPushedRawLpFromLp (I := I) (M := M) g α
          (gradInnerCLM (I := I) (M := M) g ρα
            (smoothMulH1Compl (I := I) (M := M) g ρα u_h)) :
          Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) y -
        chartPushedRaw (I := I) α
          (fun x : M => (gradRhoSqSmooth (I := I) (M := M) g ρα : M → ℝ) x) y *
        ((chartPushedRawLpFromLp (I := I) (M := M) g α
          (H1ComplToLp (I := I) (M := M) g u_h) :
          Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) y) := by
  classical
  have h_M_eq := gradInner_leibniz_H1Compl (I := I) (M := M) g ρα u_h
  rw [h_M_eq]
  have h_sub_chartPushed := chartPushedRawLpFromLp_coeFn_sub
    (I := I) (M := M) g α
    (gradInnerCLM (I := I) (M := M) g ρα
      (smoothMulH1Compl (I := I) (M := M) g ρα u_h))
    (smoothMulLp (I := I) (M := M) g
      (gradRhoSqSmooth (I := I) (M := M) g ρα)
      (H1ComplToLp (I := I) (M := M) g u_h))
  have h_smoothMul_chartPushed := chartPushedRawLpFromLp_smoothMulLp_coeFn
    (I := I) (M := M) g α (gradRhoSqSmooth (I := I) (M := M) g ρα)
    (H1ComplToLp (I := I) (M := M) g u_h)
  filter_upwards [h_sub_chartPushed, h_smoothMul_chartPushed]
    with y hy_sub hy_smooth
  rw [hy_sub, hy_smooth]

/-- The chart-pulled Leibniz identity, restated for smooth `v`. -/
theorem chartPushedRawLpFromLp_gradInner_leibniz_smoothToH1Compl
    (g : SmoothRiemannianMetric I M) (α : M) (ρα : C^∞⟮I, M; ℝ⟯)
    (v : SmoothScalar g) :
    ((chartPushedRawLpFromLp (I := I) (M := M) g α
        (smoothMulLp (I := I) (M := M) g ρα
          (gradInnerSmooth (I := I) (M := M) g ρα v)) :
        Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) =ᵐ[
        (chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      (fun y =>
        ((chartPushedRawLpFromLp (I := I) (M := M) g α
          (gradInnerSmooth (I := I) (M := M) g ρα
            (smoothScalarMulFun (I := I) (M := M) g ρα v)) :
          Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) y -
        chartPushedRaw (I := I) α
          (fun x : M => (gradRhoSqSmooth (I := I) (M := M) g ρα : M → ℝ) x) y *
        ((chartPushedRawLpFromLp (I := I) (M := M) g α
          (smoothToLp (I := I) (M := M) g v) :
          Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) y) := by
  classical
  have h_gen := chartPushedRawLpFromLp_gradInner_leibniz_H1Compl
    (I := I) (M := M) g α ρα (smoothToH1Compl (I := I) (M := M) g v)
  have h_grad_smooth : gradInnerCLM (I := I) (M := M) g ρα
        (smoothToH1Compl (I := I) (M := M) g v) =
      gradInnerSmooth (I := I) (M := M) g ρα v :=
    gradInnerCLM_smoothToH1Compl (I := I) (M := M) g ρα v
  rw [h_grad_smooth] at h_gen
  have h_smoothMul_smooth : smoothMulH1Compl (I := I) (M := M) g ρα
        (smoothToH1Compl (I := I) (M := M) g v) =
      smoothToH1Compl (I := I) (M := M) g
        (smoothScalarMulFun (I := I) (M := M) g ρα v) :=
    smoothMulH1Compl_smoothToH1Compl (I := I) (M := M) g ρα v
  rw [h_smoothMul_smooth] at h_gen
  have h_grad_smooth_2 : gradInnerCLM (I := I) (M := M) g ρα
        (smoothToH1Compl (I := I) (M := M) g
          (smoothScalarMulFun (I := I) (M := M) g ρα v)) =
      gradInnerSmooth (I := I) (M := M) g ρα
        (smoothScalarMulFun (I := I) (M := M) g ρα v) :=
    gradInnerCLM_smoothToH1Compl (I := I) (M := M) g ρα _
  rw [h_grad_smooth_2] at h_gen
  have h_H1ComplToLp_smooth : H1ComplToLp (I := I) (M := M) g
        (smoothToH1Compl (I := I) (M := M) g v) =
      smoothToLp (I := I) (M := M) g v :=
    H1ComplToLp_smoothToH1Compl (I := I) (M := M) g v
  rw [h_H1ComplToLp_smooth] at h_gen
  exact h_gen

end GradInnerCLMLeibniz
end Laplacian
end Analysis
end DifferentialGeometry

end
