import DifferentialGeometry.Analysis.Integration.Measure.Pullback
import DifferentialGeometry.Analysis.Integration.Measure.Scaling
import DifferentialGeometry.Geometry.Flow.RicciFlow.Soliton.Canonical
import DifferentialGeometry.Geometry.Metric.RicciSoliton.Normalized
import DifferentialGeometry.Geometry.Operator.LaplacianBridge
import DifferentialGeometry.Geometry.Operator.Operators
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Soliton

open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [T2Space (TangentBundle I M)]
  [SigmaCompactSpace M] [ConnectedSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

noncomputable def canonicalConjugateHeatDensity
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯)
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (t : Real) : C^∞⟮I, M; Real⟯ :=
  ⟨fun x =>
      (4 * Real.pi * (1 - t)) ^
          (-(Module.finrank Real E : Real) / 2) *
        Real.exp (-(canonicalPotential (I := I) g f 1 h.1 h.2.1 t x)),
    contMDiff_const.mul
      (Real.contDiff_exp.contMDiff.comp
        (canonicalPotential (I := I) g f 1 h.1 h.2.1 t).contMDiff.neg)⟩

theorem canonicalConjugateHeatDensity_conjugateHeat
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯)
    (h : normalizedGradientRicciSoliton (I := I) g f)
    {t : Real} (ht : t ∈ canonicalTimeDomain 1) (x : M) :
    HasDerivAt
      (fun s : Real => canonicalConjugateHeatDensity (I := I) g f h s x)
      (-ΔG (I := I) (canonicalMetric (I := I) g f 1 h.1 h.2.1 ht)
          (canonicalConjugateHeatDensity (I := I) g f h t) x +
        metricScalarAt (I := I)
            (canonicalMetric (I := I) g f 1 h.1 h.2.1 ht) x *
          canonicalConjugateHeatDensity (I := I) g f h t x) t := by
  let G := canonicalMetric (I := I) g f 1 h.1 h.2.1 ht
  let F : C^∞⟮I, M; Real⟯ := canonicalPotential (I := I) g f 1 h.1 h.2.1 t
  let n : Real := Module.finrank Real E
  let tau : Real := 1 - t
  let base : Real := 4 * Real.pi * tau
  let p : Real := -n / 2
  have htau : 0 < tau := by
    dsimp only [tau]
    simpa only [one_mul] using (mem_canonicalTimeDomain_iff.mp ht)
  have hbasePos : 0 < base := by
    dsimp only [base]
    positivity
  have htauDeriv : HasDerivAt (fun s : Real => 1 - s) (-1) t := by
    change HasDerivAt ((fun _ : Real => 1) - id) (-1) t
    simpa only [zero_sub] using
      (hasDerivAt_const (c := (1 : Real)) (x := t)).sub (hasDerivAt_id t)
  have hbaseDeriv : HasDerivAt
      (fun s : Real => 4 * Real.pi * (1 - s)) (-4 * Real.pi) t := by
    have hraw := htauDeriv.const_mul (4 * Real.pi)
    apply hraw.congr_deriv
    ring
  have hAraw := hbaseDeriv.rpow_const
    (p := p) (Or.inl hbasePos.ne')
  have hA : HasDerivAt
      (fun s : Real =>
        (4 * Real.pi * (1 - s)) ^
          (-(Module.finrank Real E : Real) / 2))
      ((n / (2 * tau)) * base ^ p) t := by
    have hpow : base ^ (p - 1) = base ^ p / base :=
      Real.rpow_sub_one hbasePos.ne' p
    change HasDerivAt (fun s : Real => (4 * Real.pi * (1 - s)) ^ p)
      ((n / (2 * tau)) * base ^ p) t
    apply hAraw.congr_deriv
    rw [show 4 * Real.pi * (1 - t) = base by rfl, hpow]
    dsimp only [p, base]
    field_simp [Real.pi_ne_zero, ne_of_gt htau]
  have hF := canonicalPotential_evolution_slice
    (I := I) g f 1 h.1 h.2.1 ht x
  have hExp : HasDerivAt
      (fun s : Real => Real.exp
        (-(canonicalPotential (I := I) g f 1 h.1 h.2.1 s x)))
      (-Real.exp (-F x) * normGradSqFun (I := I) G F x) t := by
    have hraw := hF.neg.exp
    apply hraw.congr_deriv
    change Real.exp (-F x) * (-normGradSqFun (I := I) G F x) =
      -Real.exp (-F x) * normGradSqFun (I := I) G F x
    ring
  have htime := hA.mul hExp
  have htime' : HasDerivAt
      (fun s : Real => canonicalConjugateHeatDensity (I := I) g f h s x)
      ((base ^ p * Real.exp (-F x)) *
        (n / (2 * tau) - normGradSqFun (I := I) G F x)) t := by
    apply htime.congr_deriv
    dsimp only [base, p, n, tau, F, G]
    ring
  let phi : Real → Real := fun z => Real.exp (-z)
  have hphi : Differentiable Real phi := by
    exact Real.differentiable_exp.comp
      (differentiable_neg : Differentiable Real fun z : Real => -z)
  have hphiDeriv : deriv phi = fun z : Real => -Real.exp (-z) := by
    funext z
    have hz : HasDerivAt phi (-Real.exp (-z)) z := by
      change HasDerivAt (fun y : Real => Real.exp (-y)) (-Real.exp (-z)) z
      have hraw := (Real.hasDerivAt_exp (-z)).comp z (hasDerivAt_neg z)
      apply hraw.congr_deriv
      ring
    exact hz.deriv
  have hphiDeriv2 : deriv (deriv phi) = fun z : Real => Real.exp (-z) := by
    rw [hphiDeriv]
    funext z
    have hz : HasDerivAt (fun y : Real => -Real.exp (-y)) (Real.exp (-z)) z := by
      have hraw := ((Real.hasDerivAt_exp (-z)).comp z (hasDerivAt_neg z)).neg
      apply hraw.congr_deriv
      ring
    exact hz.deriv
  have hphi' : DifferentiableAt Real (deriv phi) (F x) := by
    rw [hphiDeriv]
    fun_prop
  have hgradF : MDiffAt
      (T% fun y : M => gradientFun (I := I) G F y) x := by
    exact (gradFun_contMDiff_total_section (I := I) G F.contMDiff x).mdifferentiableAt
      (by simp)
  let expF : C^∞⟮I, M; Real⟯ :=
    ⟨fun y : M => Real.exp (-F y),
      Real.contDiff_exp.contMDiff.comp F.contMDiff.neg⟩
  have hlapExp := laplacian_comp (I := I) (LeviCivita (I := I) G) G
    (φ := phi) (f := (F : M → Real)) (x := x) hphi hphi'
      (fun y => (F.contMDiff y).mdifferentiableAt (by simp)) hgradF
  have hlapF :
      laplacian (I := I) (LeviCivita (I := I) G) G (F : M → Real) x =
        ΔG (I := I) G F x := by
    have hbridge := laplacian_levi_eq (I := I) G F.contMDiff x
    have hpack :
        (⟨(F : M → Real), F.contMDiff⟩ : C^∞⟮I, M; Real⟯) = F := by
      apply ContMDiffMap.ext
      intro y
      rfl
    rw [hpack] at hbridge
    exact hbridge
  have hlapExpRaw :
      laplacian (I := I) (LeviCivita (I := I) G) G
          (expF : M → Real) x =
        ΔG (I := I) G expF x := by
    have hbridge := laplacian_levi_eq (I := I) G expF.contMDiff x
    have hpack :
        (⟨(expF : M → Real), expF.contMDiff⟩ : C^∞⟮I, M; Real⟯) = expF := by
      apply ContMDiffMap.ext
      intro y
      rfl
    rw [hpack] at hbridge
    exact hbridge
  have hlapExpBridge :
      laplacian (I := I) (LeviCivita (I := I) G) G
          (fun y : M => phi (F y)) x =
        ΔG (I := I) G expF x := by
    have hexpFun : (expF : M → Real) = fun y : M => phi (F y) := by
      funext y
      rfl
    rw [← hexpFun]
    exact hlapExpRaw
  have hlapExp' :
      ΔG (I := I) G expF x =
        Real.exp (-F x) *
          (-ΔG (I := I) G F x + normGradSqFun (I := I) G F x) := by
    rw [hphiDeriv2, hphiDeriv] at hlapExp
    calc
      ΔG (I := I) G expF x =
          laplacian (I := I) (LeviCivita (I := I) G) G
            (fun y : M => phi (F y)) x := hlapExpBridge.symm
      _ = Real.exp (-F x) *
          (-ΔG (I := I) G F x + normGradSqFun (I := I) G F x) := by
        rw [hlapExp, hlapF, Connection.gradient_eq_gradFun,
          normGradSqFun_def]
        dsimp only [phi]
        ring
  have hgradExp : MDiffAt
      (T% fun y : M => gradientFun (I := I) G expF y) x := by
    exact (gradFun_contMDiff_total_section (I := I) G expF.contMDiff x).mdifferentiableAt
      (by simp)
  have hlapDensity := laplacian_const_smul (I := I) (LeviCivita (I := I) G) G
    (base ^ p) (f := (expF : M → Real)) (x := x)
      (fun y => (expF.contMDiff y).mdifferentiableAt (by simp)) hgradExp
  have hlapDensity' :
      ΔG (I := I) G (canonicalConjugateHeatDensity (I := I) g f h t) x =
        base ^ p * Real.exp (-F x) *
          (-ΔG (I := I) G F x + normGradSqFun (I := I) G F x) := by
    have hdensityEq : canonicalConjugateHeatDensity (I := I) g f h t =
        (base ^ p) • expF := by
      apply ContMDiffMap.ext
      intro y
      dsimp only [canonicalConjugateHeatDensity, expF, base, p, n, tau, F]
      rfl
    have hdensityFun :
        (canonicalConjugateHeatDensity (I := I) g f h t : M → Real) =
          (base ^ p) • (expF : M → Real) := by
      exact congrArg DFunLike.coe hdensityEq
    calc
      ΔG (I := I) G (canonicalConjugateHeatDensity (I := I) g f h t) x =
          laplacian (I := I) (LeviCivita (I := I) G) G
            (canonicalConjugateHeatDensity (I := I) g f h t : M → Real) x := by
        exact (laplacian_levi_eq (I := I) G
          (canonicalConjugateHeatDensity (I := I) g f h t).contMDiff x).symm
      _ = laplacian (I := I) (LeviCivita (I := I) G) G
          ((base ^ p) • (expF : M → Real)) x := by rw [hdensityFun]
      _ = base ^ p * laplacian (I := I) (LeviCivita (I := I) G) G
          (expF : M → Real) x := hlapDensity
      _ = base ^ p * ΔG (I := I) G expF x := by rw [hlapExpRaw]
      _ = base ^ p * Real.exp (-F x) *
          (-ΔG (I := I) G F x + normGradSqFun (I := I) G F x) := by
        rw [hlapExp']
        ring
  have htrace := gradientRicciSoliton_trace
    (canonicalMetric_gradientRicciSoliton (I := I) g f 1 h.1 h.2.1 ht) x
  have htrace0 :
      metricScalarAt (I := I) G x + ΔG (I := I) G F x =
        n * (1 / tau) / 2 := by
    simpa only [G, F, n, tau, one_mul] using htrace
  have htrace' :
      metricScalarAt (I := I) G x + ΔG (I := I) G F x = n / (2 * tau) := by
    calc
      metricScalarAt (I := I) G x + ΔG (I := I) G F x =
          n * (1 / tau) / 2 := htrace0
      _ = n / (2 * tau) := by
        field_simp [ne_of_gt htau]
  apply htime'.congr_deriv
  rw [hlapDensity']
  change base ^ p * Real.exp (-F x) *
      (n / (2 * tau) - normGradSqFun (I := I) G F x) =
    -(base ^ p * Real.exp (-F x) *
      (-ΔG (I := I) G F x + normGradSqFun (I := I) G F x)) +
      metricScalarAt (I := I) G x * (base ^ p * Real.exp (-F x))
  calc
    base ^ p * Real.exp (-F x) *
        (n / (2 * tau) - normGradSqFun (I := I) G F x) =
      base ^ p * Real.exp (-F x) *
        (metricScalarAt (I := I) G x + ΔG (I := I) G F x -
          normGradSqFun (I := I) G F x) := by rw [htrace']
    _ = -(base ^ p * Real.exp (-F x) *
        (-ΔG (I := I) G F x + normGradSqFun (I := I) G F x)) +
        metricScalarAt (I := I) G x * (base ^ p * Real.exp (-F x)) := by ring

omit [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]
  [T2Space (TangentBundle I M)] [SigmaCompactSpace M] [ConnectedSpace M] in
private theorem conjugateHeat_scale_factor
    (n : Nat) {tau : Real} (htau : 0 < tau) :
    ENNReal.ofReal (Real.sqrt tau) ^ n *
        ENNReal.ofReal ((4 * Real.pi * tau) ^ (-(n : Real) / 2)) =
      ENNReal.ofReal ((4 * Real.pi) ^ (-(n : Real) / 2)) := by
  have hreal :
      Real.sqrt tau ^ n *
          (4 * Real.pi * tau) ^ (-(n : Real) / 2) =
        (4 * Real.pi) ^ (-(n : Real) / 2) := by
    have hsqrtpow : Real.sqrt tau ^ n = tau ^ ((n : Real) / 2) := by
      rw [Real.sqrt_eq_rpow]
      rw [← Real.rpow_mul_natCast htau.le]
      congr 1
      ring
    have hmul :
        (4 * Real.pi * tau) ^ (-(n : Real) / 2) =
          (4 * Real.pi) ^ (-(n : Real) / 2) *
            tau ^ (-(n : Real) / 2) :=
      Real.mul_rpow (show 0 ≤ 4 * Real.pi by positivity) htau.le
    have hcancel :
        tau ^ ((n : Real) / 2) * tau ^ (-(n : Real) / 2) = 1 := by
      rw [← Real.rpow_add htau]
      convert Real.rpow_zero tau using 2
      ring
    calc
      Real.sqrt tau ^ n *
          (4 * Real.pi * tau) ^ (-(n : Real) / 2) =
        tau ^ ((n : Real) / 2) *
          ((4 * Real.pi) ^ (-(n : Real) / 2) *
            tau ^ (-(n : Real) / 2)) := by rw [hsqrtpow, hmul]
      _ = (4 * Real.pi) ^ (-(n : Real) / 2) *
          (tau ^ ((n : Real) / 2) * tau ^ (-(n : Real) / 2)) := by ring
      _ = (4 * Real.pi) ^ (-(n : Real) / 2) := by rw [hcancel, mul_one]
  rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg tau)]
  rw [← ENNReal.ofReal_mul (pow_nonneg (Real.sqrt_nonneg tau) n)]
  rw [hreal]

private theorem canonicalConjugateHeatDensity_symm
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯)
    (h : normalizedGradientRicciSoliton (I := I) g f)
    {t : Real} (ht : t ∈ canonicalTimeDomain 1)
    (Phi : M ≃ₘ⟮I, I⟯ M)
    (hPhi : Phi = canonicalFlowDiffeomorph (I := I) g f 1 h.1 h.2.1
      (canonicalFlowParameter 1 t)) :
    (fun y => ENNReal.ofReal
      (canonicalConjugateHeatDensity (I := I) g f h t (Phi.symm y))) =
      ENNReal.ofReal
          ((4 * Real.pi * (1 - t)) ^
            (-(Module.finrank Real E : Real) / 2)) •
        fun y => ENNReal.ofReal (Real.exp (-f y)) := by
  funext y
  have hbase : 0 < 4 * Real.pi * (1 - t) := by
    have htau : 0 < 1 - t := by
      simpa only [one_mul] using mem_canonicalTimeDomain_iff.mp ht
    positivity
  have hpow_nonneg :
      0 ≤ (4 * Real.pi * (1 - t)) ^
        (-(Module.finrank Real E : Real) / 2) :=
    Real.rpow_nonneg hbase.le _
  have hrho_real :
      canonicalConjugateHeatDensity (I := I) g f h t (Phi.symm y) =
        (4 * Real.pi * (1 - t)) ^
            (-(Module.finrank Real E : Real) / 2) * Real.exp (-f y) := by
    change
      (4 * Real.pi * (1 - t)) ^
            (-(Module.finrank Real E : Real) / 2) *
          Real.exp
            (-(canonicalPotential (I := I) g f 1 h.1 h.2.1 t
              (Phi.symm y))) = _
    dsimp only [canonicalPotential]
    rw [ContMDiffMap.comp_apply]
    rw [← hPhi]
    have hpoint : Phi.toContMDiffMap (Phi.symm y) = y := by
      change Phi (Phi.symm y) = y
      exact Phi.apply_symm_apply y
    rw [hpoint]
  rw [Pi.smul_apply, smul_eq_mul, hrho_real]
  rw [ENNReal.ofReal_mul hpow_nonneg]

private theorem canonicalConjugateHeatDensity_scaledVolume
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯)
    (h : normalizedGradientRicciSoliton (I := I) g f)
    {t : Real} (ht : t ∈ canonicalTimeDomain 1) :
    let tau : Real := 1 - t
    let Phi : M ≃ₘ⟮I, I⟯ M :=
      canonicalFlowDiffeomorph (I := I) g f 1 h.1 h.2.1
        (canonicalFlowParameter 1 t)
    (riemannianVolumeMeasure (I := I) (M := M)
        (scaleMetric (I := I) tau (by
          simpa only [one_mul] using mem_canonicalTimeDomain_iff.mp ht) g)).withDensity
          (fun y => ENNReal.ofReal
            (canonicalConjugateHeatDensity (I := I) g f h t (Phi.symm y))) =
      ENNReal.ofReal
          ((4 * Real.pi) ^ (-(Module.finrank Real E : Real) / 2)) •
        (riemannianVolumeMeasure (I := I) (M := M) g).withDensity
          (fun y => ENNReal.ofReal (Real.exp (-f y))) := by
  dsimp only
  let tau : Real := 1 - t
  let Phi : M ≃ₘ⟮I, I⟯ M :=
    canonicalFlowDiffeomorph (I := I) g f 1 h.1 h.2.1
      (canonicalFlowParameter 1 t)
  let eta : M → ENNReal := fun y => ENNReal.ofReal (Real.exp (-f y))
  let a : ENNReal :=
    ENNReal.ofReal (Real.sqrt tau) ^ Module.finrank Real E
  let b : ENNReal := ENNReal.ofReal
    ((4 * Real.pi * tau) ^ (-(Module.finrank Real E : Real) / 2))
  have htau : 0 < tau := by
    dsimp only [tau]
    simpa only [one_mul] using mem_canonicalTimeDomain_iff.mp ht
  have hcomp := canonicalConjugateHeatDensity_symm
    (I := I) g f h ht Phi rfl
  rw [volume_scaleMetric (I := I) (M := M) tau htau g]
  change (a • riemannianVolumeMeasure (I := I) (M := M) g).withDensity
      (fun y => ENNReal.ofReal
        (canonicalConjugateHeatDensity (I := I) g f h t (Phi.symm y))) = _
  rw [MeasureTheory.withDensity_smul_measure]
  rw [hcomp]
  change (a • (riemannianVolumeMeasure (I := I) (M := M) g).withDensity
      (b • eta)) = _
  rw [MeasureTheory.withDensity_smul' b eta (by simp [b])]
  rw [smul_smul]
  rw [conjugateHeat_scale_factor (Module.finrank Real E) htau]

theorem canonicalConjugateHeatDensity_volumeMeasure
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯)
    (h : normalizedGradientRicciSoliton (I := I) g f)
    {t : Real} (ht : t ∈ canonicalTimeDomain 1) :
    (riemannianVolumeMeasure (I := I) (M := M)
        (canonicalMetric (I := I) g f 1 h.1 h.2.1 ht)).withDensity
          (fun x => ENNReal.ofReal
            (canonicalConjugateHeatDensity (I := I) g f h t x)) =
      ENNReal.ofReal
          ((4 * Real.pi) ^ (-(Module.finrank Real E : Real) / 2)) •
        Measure.map
          ((canonicalFlowDiffeomorph (I := I) g f 1 h.1 h.2.1
            (canonicalFlowParameter 1 t)).symm : M → M)
          ((riemannianVolumeMeasure (I := I) (M := M) g).withDensity
            (fun x => ENNReal.ofReal (Real.exp (-f x)))) := by
  have htau : 0 < 1 - t := by
    simpa only [one_mul] using mem_canonicalTimeDomain_iff.mp ht
  have hrho : Measurable (fun x => ENNReal.ofReal
      (canonicalConjugateHeatDensity (I := I) g f h t x)) := by
    exact ENNReal.measurable_ofReal.comp
      (canonicalConjugateHeatDensity (I := I) g f h t).contMDiff.continuous.measurable
  rw [canonicalMetric]
  simp only [one_mul]
  rw [riemannianVolumeMeasure_pullback_withDensity
    (I := I) (scaleMetric (I := I) (1 - t) htau g)
      (canonicalFlowDiffeomorph (I := I) g f 1 h.1 h.2.1
        (canonicalFlowParameter 1 t)) _ hrho]
  rw [canonicalConjugateHeatDensity_scaledVolume (I := I) g f h ht]
  rw [Measure.map_smul]

end DifferentialGeometry.PDE.RicciFlow.Soliton
