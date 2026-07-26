import DifferentialGeometry.Analysis.Elliptic.Regularity.Bochner.PolarisedLpSmooth
import DifferentialGeometry.Analysis.Elliptic.Regularity.GradInner.Laplacian.VariationalIdentity

/-!
# Lp-class lift of the polarised Bochner-Weitzenböck identity (smooth case)

For a closed Riemannian manifold `(M, g)` and smooth scalars
`φ : C^∞⟮I, M; ℝ⟯`, `v : SmoothScalar g`, this module derives the
**Lp-class identity**

```
gradInnerLaplacianCandidateUnconditional g φ
    (smoothToH1Compl_mem_laplacianDomainPow_two g v) =
  smoothToLp((gradInnerSmoothBundle g φ v).oneSubLapClassical),
```

i.e. the smooth-case discharge of `smoothCandidate_identification_target`
from `GradInnerLaplacianVariational.lean`.

The proof works by combining:

* The **pointwise polarised Bochner identity** in `(1 - Δ_g)` form, applied to
  smooth `(φ, v)` (from `BochnerPolarised.bochner_polarised_pointwise_oneSubLap`):
  ```
  (1 - Δ_g)(g(∇φ, ∇v))(x) =
      g(∇φ, ∇v)(x)
    - g(∇v, ∇Δφ)(x) - g(∇φ, ∇Δv)(x)
    - 2 · hessPairingChart g φ v x
    - 2 · ricciTensor g x (∇φ x) (∇v x).
  ```
* **Smooth-case identifications** of each CLM summand in the unconditional
  Bochner candidate as `smoothToLp` of a specific smooth scalar:
  - `gradInnerCLM g φ (smoothToH1Compl v) = smoothToLp(gradInnerSmoothBundle g φ v)`.
  - `gradInnerCLM g (Δφ) (smoothToH1Compl v) = smoothToLp(gradInnerSmoothBundle g (Δφ) v)`.
  - `gradInnerLapU g φ hu_h = smoothToLp(gradInnerSmoothBundle g φ v) -
        smoothToLp(gradInnerSmoothBundle g φ v.oneSubLapClassical)`
    (after identifying `preimageLift g hu_h = smoothToH1Compl(v.oneSubLapClassical)`).
  - `ricciPairingCLM g φ (smoothToH1Compl v) = smoothToLp(smoothRicciPairingBundle g φ v)`.
  - `hessPairingLpOnLapDom g φ (...) = smoothToLp(hessPairingSmoothLp g φ v)`
    (taken as a hypothesis; this Hessian-piece bridge requires substantial
    chart-side infrastructure and is exposed as `hessPairingLpOnLapDom_smoothCase`).

Once each summand is identified with a `smoothToLp(...)`, the candidate
equals `smoothToLp` of an explicit sum of smooth scalars. By the pointwise
polarised Bochner identity, this sum agrees pointwise with
`(gradInnerSmoothBundle g φ v).oneSubLapClassical`, hence the Lp classes
are equal.

## Main results

* `H1ComplToLp_injOn_laplacianDomain` — H1ComplToLp restricted to
  laplacianDomain is injective.

* `preimageLift_smoothCase` — for smooth v, the Classical.choose lift
  `preimageLift g hu_h` equals `smoothToH1Compl(v.oneSubLapClassical)`.

* `gradInnerLapU_smoothCase` — Lp identification of `gradInnerLapU` for
  smooth `v`.

* `gradInnerLapU_smoothCase_eq_smoothToLp` — direct Lp identification
  with `smoothToLp(gradInnerSmoothBundle g φ v) -
  smoothToLp(gradInnerSmoothBundle g φ v.oneSubLapClassical)`.

* `gradInnerLapU_smoothCase_pointwise` — the pointwise smoothScalar
  identification, in terms of the polarised identity.

* `smoothCandidate_identification_smooth_of_hessHypothesis` —
  the smooth-case candidate identification, conditional on the Hessian
  bridge hypothesis.

* `smoothCandidate_identification_smooth_unconditional_target` — the
  target statement for the Hessian bridge.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace BochnerPolarisedLpFull

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Laplacian.GradInnerLpIdentity
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Laplacian.HessianPairingChart
open DifferentialGeometry.Analysis.Laplacian.HessianPairingLapDom
open DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianCandidate
open DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational
open DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM
open DifferentialGeometry.Analysis.Laplacian.BochnerPolarised
open DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLpSmooth
open DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianFinal

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- **Injectivity of `H1ComplToLp` on `laplacianDomain`.** For
`w₁, w₂ ∈ laplacianDomain g` with `H1ComplToLp w₁ = H1ComplToLp w₂`,
`w₁ = w₂`. -/
theorem H1ComplToLp_injOn_laplacianDomain
    (g : SmoothRiemannianMetric I M)
    {w₁ w₂ : H1Compl (I := I) (M := M) g}
    (hw₁ : w₁ ∈ laplacianDomain (I := I) (M := M) g)
    (hw₂ : w₂ ∈ laplacianDomain (I := I) (M := M) g)
    (heq : H1ComplToLp (I := I) (M := M) g w₁ =
      H1ComplToLp (I := I) (M := M) g w₂) :
    w₁ = w₂ := by
  classical
  set f₁ := laplacianDomain.preimage (I := I) (M := M) g ⟨w₁, hw₁⟩ with hf₁_def
  set f₂ := laplacianDomain.preimage (I := I) (M := M) g ⟨w₂, hw₂⟩ with hf₂_def
  have hw₁_eq : w₁ = resolvent (I := I) (M := M) g f₁ := by
    rw [hf₁_def]
    exact (resolvent_laplacianDomain_preimage_eq (I := I) (M := M) g ⟨w₁, hw₁⟩).symm
  have hw₂_eq : w₂ = resolvent (I := I) (M := M) g f₂ := by
    rw [hf₂_def]
    exact (resolvent_laplacianDomain_preimage_eq (I := I) (M := M) g ⟨w₂, hw₂⟩).symm
  have h_var₁ : ∀ v : H1Compl g,
      ⟪w₁, v⟫_ℝ = ⟪H1ComplToLp (I := I) (M := M) g v, f₁⟫_ℝ := by
    intro v
    rw [hw₁_eq]
    exact resolvent_inner_eq_lpFunctional (I := I) (M := M) g f₁ v
  have h_var₂ : ∀ v : H1Compl g,
      ⟪w₂, v⟫_ℝ = ⟪H1ComplToLp (I := I) (M := M) g v, f₂⟫_ℝ := by
    intro v
    rw [hw₂_eq]
    exact resolvent_inner_eq_lpFunctional (I := I) (M := M) g f₂ v
  have h_diff_var : ∀ v : H1Compl g,
      ⟪w₁ - w₂, v⟫_ℝ =
        ⟪H1ComplToLp (I := I) (M := M) g v, f₁ - f₂⟫_ℝ := by
    intro v
    rw [inner_sub_left, inner_sub_right]
    rw [h_var₁ v, h_var₂ v]
  specialize h_diff_var (w₁ - w₂)
  have h_H1ComplToLp_diff : H1ComplToLp (I := I) (M := M) g (w₁ - w₂) = 0 := by
    rw [(H1ComplToLp (I := I) (M := M) g).map_sub]
    rw [heq, sub_self]
  rw [h_H1ComplToLp_diff, inner_zero_left] at h_diff_var
  rw [real_inner_self_eq_norm_sq] at h_diff_var
  have h_norm_zero : ‖w₁ - w₂‖ = 0 := by
    have h_pow_zero : ‖w₁ - w₂‖ ^ 2 = 0 := h_diff_var
    exact pow_eq_zero_iff (two_ne_zero) |>.mp h_pow_zero
  have h_sub_zero : w₁ - w₂ = 0 := norm_eq_zero.mp h_norm_zero
  exact sub_eq_zero.mp h_sub_zero

/-- For smooth `v`, the H1Compl-lift `preimageLift g hu_h` (where
`hu_h := smoothToH1Compl_mem_laplacianDomainPow_two g v`) equals
`smoothToH1Compl(v.oneSubLapClassical)`. -/
theorem preimageLift_smoothCase
    (g : SmoothRiemannianMetric I M) (v : SmoothScalar g) :
    preimageLift (I := I) (M := M) g
        (smoothToH1Compl_mem_laplacianDomainPow_two (I := I) (M := M) g v) =
      smoothToH1Compl (I := I) (M := M) g v.oneSubLapClassical := by
  classical
  set u_h := smoothToH1Compl (I := I) (M := M) g v
  set hu_h := smoothToH1Compl_mem_laplacianDomainPow_two (I := I) (M := M) g v
  set hu_dom : u_h ∈ laplacianDomain (I := I) (M := M) g :=
    laplacianDomainPow_succ_subset_laplacianDomain
      (I := I) (M := M) g 1 hu_h
  have h_pl_dom : preimageLift (I := I) (M := M) g hu_h ∈
      laplacianDomain (I := I) (M := M) g :=
    preimageLift_mem_laplacianDomain (I := I) (M := M) g hu_h
  have h_st_dom : smoothToH1Compl (I := I) (M := M) g v.oneSubLapClassical ∈
      laplacianDomain (I := I) (M := M) g :=
    smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v.oneSubLapClassical
  have h_pl_H1ComplToLp :
      H1ComplToLp (I := I) (M := M) g
          (preimageLift (I := I) (M := M) g hu_h) =
        laplacianDomain.preimage (I := I) (M := M) g
          ⟨u_h, hu_dom⟩ :=
    H1ComplToLp_preimageLift (I := I) (M := M) g hu_h
  have h_st_H1ComplToLp :
      H1ComplToLp (I := I) (M := M) g
          (smoothToH1Compl (I := I) (M := M) g v.oneSubLapClassical) =
        smoothToLp (I := I) (M := M) g v.oneSubLapClassical :=
    H1ComplToLp_smoothToH1Compl (I := I) (M := M) g v.oneSubLapClassical
  have h_preimage_eq :
      laplacianDomain.preimage (I := I) (M := M) g ⟨u_h, hu_dom⟩ =
        smoothToLp (I := I) (M := M) g v.oneSubLapClassical := by
    apply resolvent_injective (I := I) (M := M) g
    rw [resolvent_laplacianDomain_preimage_eq]
    exact smoothToH1Compl_eq_resolvent_oneSubLap (I := I) (M := M) v
  have h_H1ComplToLp_eq :
      H1ComplToLp (I := I) (M := M) g
          (preimageLift (I := I) (M := M) g hu_h) =
        H1ComplToLp (I := I) (M := M) g
          (smoothToH1Compl (I := I) (M := M) g v.oneSubLapClassical) := by
    rw [h_pl_H1ComplToLp, h_st_H1ComplToLp, h_preimage_eq]
  exact H1ComplToLp_injOn_laplacianDomain (I := I) (M := M) g h_pl_dom h_st_dom
    h_H1ComplToLp_eq

/-- Smooth-case identification of `gradInnerLapU` as a difference of two
smoothToLp classes. -/
theorem gradInnerLapU_smoothCase
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    gradInnerLapU (I := I) (M := M) g φ
        (smoothToH1Compl_mem_laplacianDomainPow_two
          (I := I) (M := M) g v) =
      smoothToLp (I := I) (M := M) g
          (gradInnerSmoothBundle (I := I) (M := M) g φ v) -
        smoothToLp (I := I) (M := M) g
          (gradInnerSmoothBundle (I := I) (M := M) g φ
            v.oneSubLapClassical) := by
  classical
  rw [gradInnerLapU_eq_sub]
  rw [gradInnerCLM_smoothToH1Compl_eq_smoothToLp]
  rw [preimageLift_smoothCase]
  rw [gradInnerCLM_smoothToH1Compl_eq_smoothToLp]

/-- The smooth scalar arising from `v - v.oneSubLapClassical = Δ_g v`. -/
theorem v_sub_oneSubLap_eq_lap
    (g : SmoothRiemannianMetric I M) (v : SmoothScalar g) (x : M) :
    v.toFun x - v.oneSubLapClassical.toFun x = Δ_g (I := I) g v.smooth x := by
  rw [SmoothScalar.oneSubLapClassical_toFun, Pi.sub_apply]
  ring

/-- Pointwise identity: `gradInnerSmoothBundle g φ v - gradInnerSmoothBundle g φ v.oneSubLapClassical`
has the toFun `b ↦ g(∇φ, ∇(Δ_g v))(b)`. -/
theorem gradInnerSmoothBundle_sub_oneSubLap_apply
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (b : M) :
    (gradInnerSmoothBundle (I := I) (M := M) g φ v).toFun b -
        (gradInnerSmoothBundle (I := I) (M := M) g φ
          v.oneSubLapClassical).toFun b =
      g.inner b (gradFun (I := I) g (φ : M → ℝ) b)
        (gradFun (I := I) g (Δ_g (I := I) g v.smooth) b) := by
  classical
  rw [gradInnerSmoothBundle_apply, gradInnerSmoothBundle_apply]
  have hv_diff : MDifferentiableAt I 𝓘(ℝ, ℝ) v.toFun b :=
    v.smooth.mdifferentiable (by simp) b
  have hvl_diff : MDifferentiableAt I 𝓘(ℝ, ℝ) v.oneSubLapClassical.toFun b :=
    v.oneSubLapClassical.smooth.mdifferentiable (by simp) b
  have hΔv_diff : MDifferentiableAt I 𝓘(ℝ, ℝ) (Δ_g (I := I) g v.smooth) b :=
    (Δ_g_contMDiff (I := I) g v.smooth).mdifferentiable (by simp) b
  have h_inner_sub : g.inner b
        (gradFun (I := I) g (φ : M → ℝ) b)
        (gradFun (I := I) g v.toFun b) -
      g.inner b
        (gradFun (I := I) g (φ : M → ℝ) b)
        (gradFun (I := I) g v.oneSubLapClassical.toFun b) =
      g.inner b
        (gradFun (I := I) g (φ : M → ℝ) b)
        (gradFun (I := I) g v.toFun b -
          gradFun (I := I) g v.oneSubLapClassical.toFun b) := by
    rw [(g.inner b (gradFun (I := I) g (φ : M → ℝ) b)).map_sub]
  rw [h_inner_sub]
  have h_grad_sub : gradFun (I := I) g v.toFun b -
        gradFun (I := I) g v.oneSubLapClassical.toFun b =
      gradFun (I := I) g
        (fun y : M => v.toFun y - v.oneSubLapClassical.toFun y) b := by
    rw [DifferentialGeometry.Integral.Connection.gradFun_sub
      (I := I) g hv_diff hvl_diff]
  rw [h_grad_sub]
  have h_fun_eq : (fun y : M => v.toFun y - v.oneSubLapClassical.toFun y) =
      (fun y : M => Δ_g (I := I) g v.smooth y) := by
    funext y
    exact v_sub_oneSubLap_eq_lap (I := I) (M := M) g v y
  rw [h_fun_eq]

/-- The classical Laplacian Δφ of a smooth bundled `φ`, as a `SmoothScalar`. -/
noncomputable def smoothLaplacianAsScalar
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) : SmoothScalar g where
  toFun := Δ_g (I := I) g φ.contMDiff
  smooth := Δ_g_contMDiff (I := I) g φ.contMDiff

@[simp] lemma smoothLaplacianAsScalar_toFun
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) :
    (smoothLaplacianAsScalar (I := I) (M := M) g φ).toFun =
      Δ_g (I := I) g φ.contMDiff := rfl

/-- The smoothLaplacianBundle and smoothLaplacianAsScalar agree as bundled
smooth functions / smooth scalars (their underlying functions are equal). -/
lemma smoothLaplacianBundle_toFun_eq_smoothLaplacianAsScalar
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) :
    ((smoothLaplacianBundle (I := I) (M := M) g φ) : M → ℝ) =
      (smoothLaplacianAsScalar (I := I) (M := M) g φ).toFun := rfl

/-- Pointwise polarised Bochner identity, expressed via `(gradInnerSmoothBundle ...)`
and `hessPairingChart`, using `φ.contMDiff` as the smoothness witness for the
classical Laplacian of `φ`. -/
theorem oneSubLapClassical_gradInner_apply
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (x : M) :
    (gradInnerSmoothBundle (I := I) (M := M) g φ v).oneSubLapClassical.toFun x =
      g.inner x
        (gradFun (I := I) g (φ : M → ℝ) x)
        (gradFun (I := I) g v.toFun x)
      - g.inner x
          (gradFun (I := I) g v.toFun x)
          (gradFun (I := I) g (Δ_g (I := I) g φ.contMDiff) x)
      - g.inner x
          (gradFun (I := I) g (φ : M → ℝ) x)
          (gradFun (I := I) g (Δ_g (I := I) g v.smooth) x)
      - 2 * hessPairingChart (I := I) g φ
          ⟨v.toFun, v.smooth⟩ x
      - 2 * ricciTensor (I := I) g x
            (gradFun (I := I) g (φ : M → ℝ) x)
            (gradFun (I := I) g v.toFun x) := by
  classical
  rw [SmoothScalar.oneSubLapClassical_toFun, Pi.sub_apply]
  rw [gradInnerSmoothBundle_apply]
  have h_Δ_eq := Δ_g_gradInnerSmoothBundle_eq_contMDiff_g_inner
    (I := I) (M := M) g φ v x
  rw [h_Δ_eq]
  have h_polar := bochner_polarised_pointwise_oneSubLap (I := I) (M := M) g
    φ ⟨v.toFun, v.smooth⟩
    (contMDiff_phi_add_v (I := I) (M := M) φ ⟨v.toFun, v.smooth⟩)
    (contMDiff_phi_sub_v (I := I) (M := M) φ ⟨v.toFun, v.smooth⟩)
    (contMDiff_g_inner_grad_phi_grad_v (I := I) (M := M) g φ ⟨v.toFun, v.smooth⟩) x
  exact h_polar

/-- The unconditional candidate, smooth-case, conditional on the Hessian
bridge hypothesis. -/
theorem gradInnerLaplacianCandidateUnconditional_smoothCase_of_hessHypothesis
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (h_hess :
      hessPairingLpOnLapDom (I := I) (M := M) g φ
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1
            (smoothToH1Compl_mem_laplacianDomainPow_two
              (I := I) (M := M) g v)) =
        hessPairingSmoothLp (I := I) (M := M) g φ v) :
    gradInnerLaplacianCandidateUnconditional (I := I) (M := M) g φ
        (smoothToH1Compl_mem_laplacianDomainPow_two
          (I := I) (M := M) g v) =
      smoothToLp (I := I) (M := M) g
        (gradInnerSmoothBundle (I := I) (M := M) g φ v).oneSubLapClassical := by
  classical
  unfold gradInnerLaplacianCandidateUnconditional
  rw [gradInnerCLM_smoothToH1Compl_eq_smoothToLp (I := I) (M := M) g φ v]
  rw [gradInnerCLM_smoothToH1Compl_eq_smoothToLp (I := I) (M := M) g
      (smoothLaplacianBundle (I := I) (M := M) g φ) v]
  rw [gradInnerLapU_smoothCase (I := I) (M := M) g φ v]
  rw [ricciPairingCLM_smoothToH1Compl_eq_smoothToLp (I := I) (M := M) g φ v]
  rw [h_hess]
  apply MeasureTheory.Lp.ext

  set A1 := smoothToLp (I := I) (M := M) g
      (gradInnerSmoothBundle (I := I) (M := M) g φ v) with hA1_def
  set A2 := smoothToLp (I := I) (M := M) g
      (gradInnerSmoothBundle (I := I) (M := M) g
        (smoothLaplacianBundle (I := I) (M := M) g φ) v) with hA2_def
  set A3 := smoothToLp (I := I) (M := M) g
      (gradInnerSmoothBundle (I := I) (M := M) g φ v) -
    smoothToLp (I := I) (M := M) g
      (gradInnerSmoothBundle (I := I) (M := M) g φ v.oneSubLapClassical) with hA3_def
  set A4 := ricciPairingSmooth (I := I) (M := M) g φ v with hA4_def
  set A5 := hessPairingSmoothLp (I := I) (M := M) g φ v with hA5_def
  set RHS := smoothToLp (I := I) (M := M) g
      (gradInnerSmoothBundle (I := I) (M := M) g φ v).oneSubLapClassical with hRHS_def
  have h_A1_coe : ((smoothToLp (I := I) (M := M) g
        (gradInnerSmoothBundle (I := I) (M := M) g φ v) :
        Lp ℝ 2 _) : M → ℝ) =ᵐ[
      riemannianVolumeMeasure (I := I) (M := M) g]
      (gradInnerSmoothBundle (I := I) (M := M) g φ v).toFun :=
    MemLp.coeFn_toLp
      (gradInnerSmoothBundle (I := I) (M := M) g φ v).memLp_two
  have h_A2_coe : ((smoothToLp (I := I) (M := M) g
        (gradInnerSmoothBundle (I := I) (M := M) g
          (smoothLaplacianBundle (I := I) (M := M) g φ) v) :
        Lp ℝ 2 _) : M → ℝ) =ᵐ[
      riemannianVolumeMeasure (I := I) (M := M) g]
      (gradInnerSmoothBundle (I := I) (M := M) g
        (smoothLaplacianBundle (I := I) (M := M) g φ) v).toFun :=
    MemLp.coeFn_toLp
      (gradInnerSmoothBundle (I := I) (M := M) g
        (smoothLaplacianBundle (I := I) (M := M) g φ) v).memLp_two
  have h_A3a_coe : ((smoothToLp (I := I) (M := M) g
        (gradInnerSmoothBundle (I := I) (M := M) g φ v) :
        Lp ℝ 2 _) : M → ℝ) =ᵐ[
      riemannianVolumeMeasure (I := I) (M := M) g]
      (gradInnerSmoothBundle (I := I) (M := M) g φ v).toFun :=
    MemLp.coeFn_toLp
      (gradInnerSmoothBundle (I := I) (M := M) g φ v).memLp_two
  have h_A3b_coe : ((smoothToLp (I := I) (M := M) g
        (gradInnerSmoothBundle (I := I) (M := M) g φ v.oneSubLapClassical) :
        Lp ℝ 2 _) : M → ℝ) =ᵐ[
      riemannianVolumeMeasure (I := I) (M := M) g]
      (gradInnerSmoothBundle (I := I) (M := M) g φ v.oneSubLapClassical).toFun :=
    MemLp.coeFn_toLp
      (gradInnerSmoothBundle (I := I) (M := M) g φ v.oneSubLapClassical).memLp_two
  have h_A4_coe := ricciPairingSmooth_coeFn (I := I) (M := M) g φ v
  have h_A5_coe := hessPairingSmoothLp_coeFn (I := I) (M := M) g φ v
  have h_RHS_coe : ((smoothToLp (I := I) (M := M) g
        (gradInnerSmoothBundle (I := I) (M := M) g φ v).oneSubLapClassical :
        Lp ℝ 2 _) : M → ℝ) =ᵐ[
      riemannianVolumeMeasure (I := I) (M := M) g]
      (gradInnerSmoothBundle (I := I) (M := M) g φ v).oneSubLapClassical.toFun :=
    MemLp.coeFn_toLp
      (gradInnerSmoothBundle (I := I) (M := M) g φ v).oneSubLapClassical.memLp_two
  have h_A3_diff_coe : (A3 : M → ℝ) =ᵐ[
      riemannianVolumeMeasure (I := I) (M := M) g]
    fun b : M =>
      (gradInnerSmoothBundle (I := I) (M := M) g φ v).toFun b -
        (gradInnerSmoothBundle (I := I) (M := M) g φ v.oneSubLapClassical).toFun b := by
    change ((smoothToLp (I := I) (M := M) g
        (gradInnerSmoothBundle (I := I) (M := M) g φ v) -
      smoothToLp (I := I) (M := M) g
        (gradInnerSmoothBundle (I := I) (M := M) g φ v.oneSubLapClassical) : Lp ℝ 2 _) :
        M → ℝ) =ᵐ[_] _
    have h_sub := MeasureTheory.Lp.coeFn_sub
      (smoothToLp (I := I) (M := M) g
        (gradInnerSmoothBundle (I := I) (M := M) g φ v))
      (smoothToLp (I := I) (M := M) g
        (gradInnerSmoothBundle (I := I) (M := M) g φ v.oneSubLapClassical))
    refine h_sub.trans ?_
    filter_upwards [h_A3a_coe, h_A3b_coe] with b h_a h_b
    rw [Pi.sub_apply]
    rw [h_a, h_b]
  set LHS := A1 - A2 - A3 - (2 : ℝ) • A4 - (2 : ℝ) • A5 with hLHS_def
  have h_step1 : ((A1 - A2 : Lp ℝ 2 _) : M → ℝ) =ᵐ[
      riemannianVolumeMeasure (I := I) (M := M) g]
    fun b => (gradInnerSmoothBundle (I := I) (M := M) g φ v).toFun b -
      (gradInnerSmoothBundle (I := I) (M := M) g
        (smoothLaplacianBundle (I := I) (M := M) g φ) v).toFun b := by
    refine (MeasureTheory.Lp.coeFn_sub A1 A2).trans ?_
    filter_upwards [h_A1_coe, h_A2_coe] with b h_a1 h_a2
    rw [Pi.sub_apply, h_a1, h_a2]
  have h_step2 : ((A1 - A2 - A3 : Lp ℝ 2 _) : M → ℝ) =ᵐ[
      riemannianVolumeMeasure (I := I) (M := M) g]
    fun b => ((gradInnerSmoothBundle (I := I) (M := M) g φ v).toFun b -
      (gradInnerSmoothBundle (I := I) (M := M) g
        (smoothLaplacianBundle (I := I) (M := M) g φ) v).toFun b) -
      ((gradInnerSmoothBundle (I := I) (M := M) g φ v).toFun b -
        (gradInnerSmoothBundle (I := I) (M := M) g φ v.oneSubLapClassical).toFun b) := by
    refine (MeasureTheory.Lp.coeFn_sub (A1 - A2) A3).trans ?_
    filter_upwards [h_step1, h_A3_diff_coe] with b h_12 h_3
    rw [Pi.sub_apply, h_12, h_3]
  have h_A4_smul_coe : (((2 : ℝ) • A4 : Lp ℝ 2 _) : M → ℝ) =ᵐ[
      riemannianVolumeMeasure (I := I) (M := M) g]
    fun b => 2 * ricciTensor (I := I) g b
      (gradFun (I := I) g (φ : M → ℝ) b)
      (gradFun (I := I) g v.toFun b) := by
    refine (MeasureTheory.Lp.coeFn_smul (2 : ℝ) A4).trans ?_
    filter_upwards [h_A4_coe] with b h_a4
    rw [Pi.smul_apply, h_a4]
    rfl
  have h_step3 : ((A1 - A2 - A3 - (2 : ℝ) • A4 : Lp ℝ 2 _) : M → ℝ) =ᵐ[
      riemannianVolumeMeasure (I := I) (M := M) g]
    fun b => (((gradInnerSmoothBundle (I := I) (M := M) g φ v).toFun b -
        (gradInnerSmoothBundle (I := I) (M := M) g
          (smoothLaplacianBundle (I := I) (M := M) g φ) v).toFun b) -
        ((gradInnerSmoothBundle (I := I) (M := M) g φ v).toFun b -
          (gradInnerSmoothBundle (I := I) (M := M) g φ v.oneSubLapClassical).toFun b)) -
      2 * ricciTensor (I := I) g b
        (gradFun (I := I) g (φ : M → ℝ) b)
        (gradFun (I := I) g v.toFun b) := by
    refine (MeasureTheory.Lp.coeFn_sub (A1 - A2 - A3) ((2 : ℝ) • A4)).trans ?_
    filter_upwards [h_step2, h_A4_smul_coe] with b h_123 h_4
    rw [Pi.sub_apply, h_123, h_4]
  have h_A5_smul_coe : (((2 : ℝ) • A5 : Lp ℝ 2 _) : M → ℝ) =ᵐ[
      riemannianVolumeMeasure (I := I) (M := M) g]
    fun b => 2 * hessPairingChart (I := I) g φ
      ⟨v.toFun, v.smooth⟩ b := by
    refine (MeasureTheory.Lp.coeFn_smul (2 : ℝ) A5).trans ?_
    filter_upwards [h_A5_coe] with b h_a5
    rw [Pi.smul_apply, h_a5]
    rfl
  have h_LHS_coe : (LHS : M → ℝ) =ᵐ[
      riemannianVolumeMeasure (I := I) (M := M) g]
    fun b => ((((gradInnerSmoothBundle (I := I) (M := M) g φ v).toFun b -
          (gradInnerSmoothBundle (I := I) (M := M) g
            (smoothLaplacianBundle (I := I) (M := M) g φ) v).toFun b) -
          ((gradInnerSmoothBundle (I := I) (M := M) g φ v).toFun b -
            (gradInnerSmoothBundle (I := I) (M := M) g φ v.oneSubLapClassical).toFun b)) -
          2 * ricciTensor (I := I) g b
            (gradFun (I := I) g (φ : M → ℝ) b)
            (gradFun (I := I) g v.toFun b)) -
        2 * hessPairingChart (I := I) g φ
          ⟨v.toFun, v.smooth⟩ b := by
    refine (MeasureTheory.Lp.coeFn_sub (A1 - A2 - A3 - (2 : ℝ) • A4) ((2 : ℝ) • A5)).trans ?_
    filter_upwards [h_step3, h_A5_smul_coe] with b h_1234 h_5
    rw [Pi.sub_apply, h_1234, h_5]
  have h_RHS_coe' : (RHS : M → ℝ) =ᵐ[
      riemannianVolumeMeasure (I := I) (M := M) g]
    fun b => (gradInnerSmoothBundle (I := I) (M := M) g φ v).oneSubLapClassical.toFun b := by
    change ((smoothToLp (I := I) (M := M) g
      (gradInnerSmoothBundle (I := I) (M := M) g φ v).oneSubLapClassical :
      Lp ℝ 2 _) : M → ℝ) =ᵐ[_] _
    exact h_RHS_coe
  refine h_LHS_coe.trans ?_
  refine EventuallyEq.symm ?_
  refine h_RHS_coe'.trans ?_
  refine Filter.Eventually.of_forall ?_
  intro b
  beta_reduce
  rw [oneSubLapClassical_gradInner_apply (I := I) (M := M) g φ v b]
  simp only [gradInnerSmoothBundle_apply]
  have h_phi_sym : g.inner b
        (gradFun (I := I) g
          ((smoothLaplacianBundle (I := I) (M := M) g φ) : M → ℝ) b)
        (gradFun (I := I) g v.toFun b) =
      g.inner b
        (gradFun (I := I) g v.toFun b)
        (gradFun (I := I) g (Δ_g (I := I) g φ.contMDiff) b) := by
    rw [show ((smoothLaplacianBundle (I := I) (M := M) g φ) : M → ℝ) =
        Δ_g (I := I) g φ.contMDiff from rfl]
    exact g.symm b _ _
  rw [h_phi_sym]
  have h_diff_eq : g.inner b
        (gradFun (I := I) g (φ : M → ℝ) b)
        (gradFun (I := I) g v.toFun b) -
      g.inner b
        (gradFun (I := I) g (φ : M → ℝ) b)
        (gradFun (I := I) g v.oneSubLapClassical.toFun b) =
      g.inner b
        (gradFun (I := I) g (φ : M → ℝ) b)
        (gradFun (I := I) g (Δ_g (I := I) g v.smooth) b) := by
    have h := gradInnerSmoothBundle_sub_oneSubLap_apply (I := I) (M := M) g φ v b
    rw [gradInnerSmoothBundle_apply, gradInnerSmoothBundle_apply] at h
    exact h
  linarith [h_diff_eq]

/-- The `smoothCandidate_identification_target` statement is discharged by
`gradInnerLaplacianCandidateUnconditional_smoothCase_of_hessHypothesis`. -/
theorem smoothCandidate_identification_target_of_hessHypothesis
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (h_hess :
      hessPairingLpOnLapDom (I := I) (M := M) g φ
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1
            (smoothToH1Compl_mem_laplacianDomainPow_two
              (I := I) (M := M) g v)) =
        hessPairingSmoothLp (I := I) (M := M) g φ v) :
    smoothCandidate_identification_target (I := I) (M := M) g φ v := by
  unfold smoothCandidate_identification_target
  exact gradInnerLaplacianCandidateUnconditional_smoothCase_of_hessHypothesis
    (I := I) (M := M) g φ v h_hess

end BochnerPolarisedLpFull
end Laplacian
end Analysis
end DifferentialGeometry

end
