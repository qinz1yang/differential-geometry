import DifferentialGeometry.Analysis.Laplacian.Regularity.LaplacianDomain.VariationalLimit
import DifferentialGeometry.Analysis.Sobolev.Intrinsic.EquivalenceReverse
import DifferentialGeometry.Integral.DivergenceTheorem.POUReduction
import DifferentialGeometry.Geometry.Laplacian
import DifferentialGeometry.Geometry.Gradient

/-!
# Leibniz rule for `Δ_g` and the `fHLeibniz`/`(pouScalar α v).oneSubLap` bridge

This file proves two infrastructure results that connect the existing
chart-bilinear smooth-case variational identity from
`LaplacianDomainVariationalLimit` to the corrected
`f_chart`-via-`fHLeibniz` formulation.

## Main results

* **`Δ_g_smul_eq`** — the Leibniz product rule for the variational
  Laplacian: for any two smooth scalar functions `φ`, `v` on a closed
  Riemannian manifold,
  ```
  Δ_g (φ · v) x = φ x · Δ_g v x + 2 · g(grad φ x, grad v x) + v x · Δ_g φ x.
  ```
  The proof composes the gradient Leibniz rule
  (`gradFun_mul_pointwise`) with the divergence Leibniz rule
  (`divergence_g_smoothSmul`).

* **`pouScalar_oneSubLapClassical_pointwise_leibniz`** — for a smooth
  scalar `v` and chart point `α`, the smooth function
  `(pouScalar α v).oneSubLapClassical.toFun = ρα·v - Δ_g(ρα·v)`
  expands at every point to the pointwise Leibniz combination
  ```
  ρα · v.oneSubLapClassical.toFun
    - 2 · g(grad ρα, grad v)
    - v · Δρα.
  ```

* **`pouScalar_oneSubLap_aeEq_fHLeibniz_smooth`** — the smooth function
  `(pouScalar α v).oneSubLapClassical.toFun` agrees a.e.-`μ_g` with the
  `M → ℝ` representative of `fHLeibniz (smoothToH1Compl v) _ : Lp _`.
  This identification factors through the smooth-case `Lp` arithmetic
  formula `fHLeibniz_smoothToH1Compl` and the pointwise Leibniz
  expansion.

These results are the natural prerequisites for the headline
chart-bilinear identity for `u_h ∈ laplacianDomain g` in the
no-ρα `f_chart` form. They reformulate the existing smooth-case
RHS — written via the explicit smooth function
`(pouScalar α v).oneSubLapClassical` — in terms of the abstract
`Lp` class `fHLeibniz u_h`, providing the smooth-case
ingredient for any limit-passage argument that builds the general
identity.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace LaplacianDomainVariationalLimitGeneral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainVariationalLimit
open DifferentialGeometry.Analysis.Sobolev.Chart

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

/-- Pointwise gradient Leibniz rule, in the smooth-witness form: for
smooth `φ` and `v`,
`grad_g (φ · v) x = φ x • grad_g v x + v x • grad_g φ x`. -/
theorem gradFun_smul_smooth_eq_pointwise
    (g : SmoothRiemannianMetric I M)
    {φ v : M → ℝ}
    (hφ : ContMDiff I 𝓘(ℝ, ℝ) ∞ φ)
    (hv : ContMDiff I 𝓘(ℝ, ℝ) ∞ v) (x : M) :
    gradFun (I := I) g (fun y : M => φ y * v y) x =
      φ x • gradFun (I := I) g v x + v x • gradFun (I := I) g φ x := by
  classical
  have hρ_md := hφ.mdifferentiable (by simp) x
  have hu_md := hv.mdifferentiable (by simp) x
  apply DifferentialGeometry.Integral.DivergenceTheorem.metricFlatLinear_injective
    (I := I) g x
  ext w
  change g.inner x
      (gradFun (I := I) g (fun y : M => φ y * v y) x) w =
    g.inner x (φ x • gradFun (I := I) g v x + v x • gradFun (I := I) g φ x) w
  rw [inner_gradFun (I := I) g _ x w]
  have h_fun_eq : (fun y : M => φ y * v y) = φ * v := by funext y; rfl
  set d_φ : TangentSpace I x →L[ℝ] ℝ := mfderiv I 𝓘(ℝ, ℝ) φ x with hd_φ_def
  set d_v : TangentSpace I x →L[ℝ] ℝ := mfderiv I 𝓘(ℝ, ℝ) v x with hd_v_def
  have h_mfderiv_mul : mfderiv I 𝓘(ℝ, ℝ) (fun y : M => φ y * v y) x w =
      φ x * d_v w + v x * d_φ w := by
    rw [h_fun_eq]
    have h_φ_at : HasMFDerivAt I 𝓘(ℝ, ℝ) φ x d_φ := hρ_md.hasMFDerivAt
    have h_v_at : HasMFDerivAt I 𝓘(ℝ, ℝ) v x d_v := hu_md.hasMFDerivAt
    have hAt : HasMFDerivAt I 𝓘(ℝ, ℝ) (φ * v) x
        ((φ x • d_v + v x • d_φ : TangentSpace I x →L[ℝ] ℝ)) :=
      h_φ_at.mul h_v_at
    rw [hAt.mfderiv]
    change ((φ x • d_v + v x • d_φ : TangentSpace I x →L[ℝ] ℝ)) w =
        φ x * d_v w + v x * d_φ w
    rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.smul_apply]
    simp [smul_eq_mul]
  rw [h_mfderiv_mul]
  symm
  have h_add : (g.inner x)
      (φ x • gradFun (I := I) g v x +
       v x • gradFun (I := I) g φ x) =
      (g.inner x) (φ x • gradFun (I := I) g v x) +
      (g.inner x) (v x • gradFun (I := I) g φ x) :=
    (g.inner x).map_add _ _
  change ((g.inner x)
      (φ x • gradFun (I := I) g v x +
       v x • gradFun (I := I) g φ x)) w =
    φ x * d_v w + v x * d_φ w
  rw [h_add]
  rw [show (((g.inner x) (φ x • gradFun (I := I) g v x)) +
      ((g.inner x) (v x • gradFun (I := I) g φ x))) w =
      ((g.inner x) (φ x • gradFun (I := I) g v x)) w +
      ((g.inner x) (v x • gradFun (I := I) g φ x)) w from rfl]
  rw [(g.inner x).map_smul, (g.inner x).map_smul]
  rw [show (φ x • (g.inner x) (gradFun (I := I) g v x)) w =
      φ x • ((g.inner x) (gradFun (I := I) g v x)) w from rfl]
  rw [show (v x • (g.inner x) (gradFun (I := I) g φ x)) w =
      v x • ((g.inner x) (gradFun (I := I) g φ x)) w from rfl]
  simp only [smul_eq_mul]
  rw [show ((g.inner x) (gradFun (I := I) g v x)) w = d_v w from by
    rw [hd_v_def]
    exact inner_gradFun (I := I) g v x w]
  rw [show ((g.inner x) (gradFun (I := I) g φ x)) w = d_φ w from by
    rw [hd_φ_def]
    exact inner_gradFun (I := I) g φ x w]

/-- The smooth tangent section `grad_g (φ · v)` equals
`smoothSmul φ (grad_g v) + smoothSmul v (grad_g φ)` as smooth tangent
sections. -/
private lemma grad_g_smul_smooth_section_eq
    (g : SmoothRiemannianMetric I M)
    {φ v : M → ℝ}
    (hφ : ContMDiff I 𝓘(ℝ, ℝ) ∞ φ)
    (hv : ContMDiff I 𝓘(ℝ, ℝ) ∞ v) :
    (grad_g (I := I) g (hφ.mul hv) :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) =
      smoothSmul (I := I) φ hφ
          (grad_g (I := I) g hv : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) +
        smoothSmul (I := I) v hv
          (grad_g (I := I) g hφ :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) := by
  ext x
  rw [ContMDiffSection.coe_add]
  rw [grad_g_apply]
  change gradFun (I := I) g (fun y : M => φ y * v y) x =
    (smoothSmul (I := I) φ hφ
        (grad_g (I := I) g hv : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)) x +
      (smoothSmul (I := I) v hv
        (grad_g (I := I) g hφ : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)) x
  rw [smoothSmul_apply, smoothSmul_apply]
  rw [grad_g_apply, grad_g_apply]
  exact gradFun_smul_smooth_eq_pointwise (I := I) (M := M) g hφ hv x

/-- For smooth `φ`, `v`, the tangent action of `grad_g v` on `φ` equals the
metric inner product `g(grad_g φ, grad_g v)`. -/
private lemma tangentSectionAction_grad_g_eq_inner_grad
    (g : SmoothRiemannianMetric I M)
    {φ v : M → ℝ}
    (_hφ : ContMDiff I 𝓘(ℝ, ℝ) ∞ φ)
    (hv : ContMDiff I 𝓘(ℝ, ℝ) ∞ v) (x : M) :
    tangentSectionAction (I := I)
        (grad_g (I := I) g hv :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) φ x =
      g.inner x (gradFun (I := I) g φ x) (gradFun (I := I) g v x) := by
  unfold tangentSectionAction
  rw [show ((grad_g (I := I) g hv :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) =
        gradFun (I := I) g v x from grad_g_apply (I := I) g hv x]
  exact (inner_gradFun (I := I) g φ x _).symm

/-- **Leibniz rule for `Δ_g` on a product of smooth scalars.** For smooth
`φ`, `v` on a closed Riemannian manifold,
```
Δ_g (φ · v) x = φ x · Δ_g v x + 2 · g(grad_g φ x, grad_g v x) + v x · Δ_g φ x.
```
-/
theorem Δ_g_smul_eq
    (g : SmoothRiemannianMetric I M)
    {φ v : M → ℝ}
    (hφ : ContMDiff I 𝓘(ℝ, ℝ) ∞ φ)
    (hv : ContMDiff I 𝓘(ℝ, ℝ) ∞ v) (x : M) :
    Δ_g (I := I) g (hφ.mul hv) x =
      φ x * Δ_g (I := I) g hv x +
        2 * g.inner x (gradFun (I := I) g φ x) (gradFun (I := I) g v x) +
        v x * Δ_g (I := I) g hφ x := by
  classical
  rw [Δ_g_def]
  rw [grad_g_smul_smooth_section_eq (I := I) (M := M) g hφ hv]
  rw [divergence_g_add (I := I) g]
  rw [divergence_g_smoothSmul (I := I) g φ hφ _ x]
  rw [divergence_g_smoothSmul (I := I) g v hv _ x]
  rw [tangentSectionAction_grad_g_eq_inner_grad (I := I) (M := M) g hφ hv x]
  rw [tangentSectionAction_grad_g_eq_inner_grad (I := I) (M := M) g hv hφ x]
  rw [show divergence_g (I := I) g (grad_g (I := I) g hv) x =
        Δ_g (I := I) g hv x from (Δ_g_def (I := I) g hv x).symm,
      show divergence_g (I := I) g (grad_g (I := I) g hφ) x =
        Δ_g (I := I) g hφ x from (Δ_g_def (I := I) g hφ x).symm]
  have h_symm : g.inner x (gradFun (I := I) g v x) (gradFun (I := I) g φ x) =
      g.inner x (gradFun (I := I) g φ x) (gradFun (I := I) g v x) :=
    g.symm x _ _
  rw [h_symm]
  ring

/-- Pointwise expression of `(pouScalar α v).oneSubLapClassical.toFun`
via the Leibniz expansion: for any `x : M`,
```
(pouScalar α v).oneSubLapClassical.toFun x =
  ρα x · v.oneSubLapClassical.toFun x
    - 2 · g(grad ρα x, grad v x)
    - v.toFun x · Δρα x.
```
-/
theorem pouScalar_oneSubLapClassical_pointwise_leibniz
    (g : SmoothRiemannianMetric I M) (α : M) (v : SmoothScalar g) (x : M) :
    (pouScalar (I := I) (M := M) α v).oneSubLapClassical.toFun x =
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x *
          v.oneSubLapClassical.toFun x -
        2 * g.inner x (gradFun (I := I) g
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)
          (gradFun (I := I) g v.toFun x) -
        v.toFun x *
          Δ_g (I := I) g (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯).contMDiff x := by
  classical
  set ρα : M → ℝ := ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) with hρα_def
  set V : M → ℝ := v.toFun with hV_def
  have hρα_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ ρα :=
    (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯).contMDiff
  have hV_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ V := v.smooth
  have h_pou_toFun :
      (pouScalar (I := I) (M := M) α v).toFun =
        fun y : M => ρα y * V y := rfl
  change (pouScalar (I := I) (M := M) α v).toFun x -
      Δ_g (I := I) g
        (pouScalar (I := I) (M := M) α v).smooth x =
    ρα x * v.oneSubLapClassical.toFun x -
      2 * g.inner x (gradFun (I := I) g
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)
        (gradFun (I := I) g v.toFun x) -
      v.toFun x *
        Δ_g (I := I) g (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯).contMDiff x
  have h_lap_eq : Δ_g (I := I) g
      (pouScalar (I := I) (M := M) α v).smooth x =
        Δ_g (I := I) g (hρα_smooth.mul hV_smooth) x := rfl
  rw [h_lap_eq]
  rw [Δ_g_smul_eq (I := I) (M := M) g hρα_smooth hV_smooth x]
  rw [h_pou_toFun]
  change ρα x * V x -
      (ρα x * Δ_g (I := I) g hV_smooth x +
        2 * g.inner x (gradFun (I := I) g ρα x) (gradFun (I := I) g V x) +
        V x * Δ_g (I := I) g hρα_smooth x) =
    ρα x * (V x - Δ_g (I := I) g v.smooth x) -
      2 * g.inner x (gradFun (I := I) g ρα x) (gradFun (I := I) g V x) -
      V x * Δ_g (I := I) g hρα_smooth x
  have h_lap_v_eq :
      Δ_g (I := I) g v.smooth x = Δ_g (I := I) g hV_smooth x := rfl
  rw [h_lap_v_eq]
  ring

/-- The `M → ℝ` representative of `fHLeibniz (smoothToH1Compl v) _` is
a.e.-`riemannianVolumeMeasure g` equal to the smooth pointwise Leibniz
combination
```
ρα · v.oneSubLapClassical.toFun - 2 g(grad ρα, grad v) - v · Δρα.
```
-/
private lemma fHLeibniz_smoothCase_coeFn_aeEq
    (g : SmoothRiemannianMetric I M) (α : M) (v : SmoothScalar g) :
    ((fHLeibniz (I := I) (M := M) g α
          (smoothToH1Compl (I := I) (M := M) g v)
          (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v)
          : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
        : M → ℝ) =ᵐ[riemannianVolumeMeasure (I := I) (M := M) g]
      (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x *
          v.oneSubLapClassical.toFun x -
        2 * g.inner x (gradFun (I := I) g
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)
          (gradFun (I := I) g v.toFun x) -
        v.toFun x *
          Δ_g (I := I) g (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯).contMDiff x) := by
  classical
  rw [fHLeibniz_smoothToH1Compl (I := I) (M := M) g α v]
  set ρα : C^∞⟮I, M; ℝ⟯ := chartAtlasPOU I M α with hρα_def
  set ρα_fun : M → ℝ := (ρα : M → ℝ) with hρα_fun_def
  set Δρα : C^∞⟮I, M; ℝ⟯ := laplacianOfChartPOU (I := I) (M := M) g α
    with hΔρα_def
  have h_sub1 := MeasureTheory.Lp.coeFn_sub
      ((smoothMulLp (I := I) (M := M) g ρα
          (smoothToLp (I := I) (M := M) g v.oneSubLapClassical)
        - (2 : ℝ) • gradInnerSmooth (I := I) (M := M) g ρα v))
      (smoothMulLp (I := I) (M := M) g Δρα
          (smoothToLp (I := I) (M := M) g v))
  have h_sub2 := MeasureTheory.Lp.coeFn_sub
      (smoothMulLp (I := I) (M := M) g ρα
        (smoothToLp (I := I) (M := M) g v.oneSubLapClassical))
      ((2 : ℝ) • gradInnerSmooth (I := I) (M := M) g ρα v)
  have h_mul1 := smoothMulLp_apply_coeFn (I := I) (M := M) g ρα
    (smoothToLp (I := I) (M := M) g v.oneSubLapClassical)
  have h_mul2 := smoothMulLp_apply_coeFn (I := I) (M := M) g Δρα
    (smoothToLp (I := I) (M := M) g v)
  have h_smul := MeasureTheory.Lp.coeFn_smul (2 : ℝ)
    (gradInnerSmooth (I := I) (M := M) g ρα v)
  have h_grad := gradInnerSmooth_coeFn (I := I) (M := M) g ρα v
  have h_smoothToLp1 :
      ((smoothToLp (I := I) (M := M) g v.oneSubLapClassical
         : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g] v.oneSubLapClassical.toFun :=
    MemLp.coeFn_toLp v.oneSubLapClassical.memLp_two
  have h_smoothToLp2 :
      ((smoothToLp (I := I) (M := M) g v
         : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g] v.toFun :=
    MemLp.coeFn_toLp v.memLp_two
  filter_upwards [h_sub1, h_sub2, h_mul1, h_mul2, h_smul, h_grad, h_smoothToLp1,
    h_smoothToLp2] with x hx1 hx2 hx_mul1 hx_mul2 hx_smul hx_grad hx_lp1 hx_lp2
  rw [hx1]
  change ((smoothMulLp (I := I) (M := M) g ρα
            (smoothToLp (I := I) (M := M) g v.oneSubLapClassical) -
          (2 : ℝ) • gradInnerSmooth (I := I) (M := M) g ρα v
         : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x -
        ((smoothMulLp (I := I) (M := M) g Δρα
            (smoothToLp (I := I) (M := M) g v)
         : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x =
      ρα_fun x * v.oneSubLapClassical.toFun x -
        2 * g.inner x (gradFun (I := I) g ρα x) (gradFun (I := I) g v.toFun x) -
        v.toFun x *
          Δ_g (I := I) g (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯).contMDiff x
  rw [hx2]
  change ((smoothMulLp (I := I) (M := M) g ρα
            (smoothToLp (I := I) (M := M) g v.oneSubLapClassical)
         : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x -
        (((2 : ℝ) • gradInnerSmooth (I := I) (M := M) g ρα v
         : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x -
        ((smoothMulLp (I := I) (M := M) g Δρα
            (smoothToLp (I := I) (M := M) g v)
         : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x =
      ρα_fun x * v.oneSubLapClassical.toFun x -
        2 * g.inner x (gradFun (I := I) g ρα x) (gradFun (I := I) g v.toFun x) -
        v.toFun x *
          Δ_g (I := I) g (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯).contMDiff x
  rw [hx_mul1, hx_mul2, hx_smul]
  change ρα_fun x * ((smoothToLp (I := I) (M := M) g v.oneSubLapClassical
            : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x -
        ((2 : ℝ) • ((gradInnerSmooth (I := I) (M := M) g ρα v
            : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) x -
        (Δρα : M → ℝ) x *
          ((smoothToLp (I := I) (M := M) g v
            : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x =
      ρα_fun x * v.oneSubLapClassical.toFun x -
        2 * g.inner x (gradFun (I := I) g ρα x) (gradFun (I := I) g v.toFun x) -
        v.toFun x *
          Δ_g (I := I) g (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯).contMDiff x
  rw [show ((2 : ℝ) • ((gradInnerSmooth (I := I) (M := M) g ρα v
            : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) x =
      (2 : ℝ) • ((gradInnerSmooth (I := I) (M := M) g ρα v
            : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x from rfl]
  rw [hx_grad, hx_lp1, hx_lp2]
  change ρα_fun x * v.oneSubLapClassical.toFun x -
        (2 : ℝ) • g.inner x (gradFun (I := I) g ρα x)
          (gradFun (I := I) g v.toFun x) -
        Δ_g (I := I) g (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯).contMDiff x * v.toFun x =
      ρα_fun x * v.oneSubLapClassical.toFun x -
        2 * g.inner x (gradFun (I := I) g ρα x) (gradFun (I := I) g v.toFun x) -
        v.toFun x *
          Δ_g (I := I) g (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯).contMDiff x
  rw [smul_eq_mul]
  ring

/-- For smooth `v`, the smooth function `(pouScalar α v).oneSubLapClassical.toFun`
agrees a.e.-`riemannianVolumeMeasure g` with the `M → ℝ` representative of
`fHLeibniz (smoothToH1Compl v) _`. -/
theorem pouScalar_oneSubLap_aeEq_fHLeibniz_smooth
    (g : SmoothRiemannianMetric I M) (α : M) (v : SmoothScalar g) :
    (pouScalar (I := I) (M := M) α v).oneSubLapClassical.toFun =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
      ((fHLeibniz (I := I) (M := M) g α
          (smoothToH1Compl (I := I) (M := M) g v)
          (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v)
          : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
        : M → ℝ) := by
  classical
  have h := fHLeibniz_smoothCase_coeFn_aeEq (I := I) (M := M) g α v
  have h_pointwise : ∀ x : M,
      (pouScalar (I := I) (M := M) α v).oneSubLapClassical.toFun x =
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x *
            v.oneSubLapClassical.toFun x -
          2 * g.inner x (gradFun (I := I) g
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)
            (gradFun (I := I) g v.toFun x) -
          v.toFun x *
            Δ_g (I := I) g (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯).contMDiff x :=
    pouScalar_oneSubLapClassical_pointwise_leibniz (I := I) (M := M) g α v
  refine Filter.EventuallyEq.trans (Filter.Eventually.of_forall h_pointwise) ?_
  exact h.symm

end LaplacianDomainVariationalLimitGeneral
end Laplacian
end Analysis
end DifferentialGeometry

end
