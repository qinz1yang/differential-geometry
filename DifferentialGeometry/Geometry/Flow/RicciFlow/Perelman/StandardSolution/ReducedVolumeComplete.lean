import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume.Basic
import DifferentialGeometry.Analysis.Integration.Measure.Parametric.Evaluation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.ExpDensity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.MinNonconjugacy

set_option autoImplicit false

noncomputable section

open Bundle Filter Function MeasureTheory Set
open DifferentialGeometry
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped ContDiff Manifold Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow

variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
  {D : RealTimeInterval}

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

section VolumeDefinition

variable [T2Space M] [SigmaCompactSpace M]

noncomputable def redVolume
    (S : SolutionOn (I := I) (M := M) D)
    (T : ℝ) (x : M) (tau : ℝ) : ℝ≥0∞ :=
  ∫⁻ y, ENNReal.ofReal
    (DifferentialGeometry.PDE.RicciFlow.Perelman.redDensity S T x y tau)
    ∂riemannianVolumeMeasure (I := I) (M := M)
      (S.base.metric (T - tau))

theorem redVolume_eq_upstream
    (S : SolutionOn (I := I) (M := M) D)
    (T : ℝ) (x : M) (tau : ℝ) :
    DifferentialGeometry.PDE.RicciFlow.redVolume S T x tau =
      DifferentialGeometry.PDE.RicciFlow.Perelman.redVolume S T x tau := by
  rfl

end VolumeDefinition

theorem paramDensity_eq_lExpDensity_of_eqOn [I.Boundaryless] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (T : ℝ) (x : M) (tau : ℝ)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1)
    (hEq : Set.EqOn Ψ (fun W : E ↦ lExp S T x W tau) Ψ.source)
    (Z : E) (hZ : Z ∈ Ψ.source) :
    paramDensity (I := I) (S.base.metric (T - tau)) Ψ Z =
      lExpDensity S T x Z tau := by
  have hev : (Ψ : E → M) =ᶠ[𝓝 Z] (fun W : E ↦ lExp S T x W tau) := by
    refine Filter.eventuallyEq_of_mem (Ψ.open_source.mem_nhds hZ) ?_
    intro W hW
    exact hEq hW
  unfold paramDensity paramGramMatrix lExpDensity lExpGram lGram lExpField
  rw [hev.eq_of_nhds,
    hev.mfderiv_eq (I := modelWithCornersSelf ℝ E) (I' := I),
    hEq hZ]
  simp only [tangentSpaceCast]
  congr 2

section NonconjugateNormalization

variable [I.Boundaryless] [T2Space M]

theorem lRedJac_mul_src_of_nonconj
    (S : SolutionOn (I := I) (M := M) D)
    (T : ℝ) (x : M) (Z : TangentSpace I x) (tau : ℝ)
    (hdom : (Z, tau) ∈ lExpPosDom S T x)
    (hnconj : ¬ IsLConjugate S T x Z tau) :
    lReducedJacobian S T x Z tau * lSourceDensity S T x =
      lExpDensity S T x Z tau *
        DifferentialGeometry.PDE.RicciFlow.Perelman.redDensity
          S T x (lExp S T x Z tau) tau := by
  have hJ : 0 < lExpJacobian S T x Z tau :=
    lExpJac_pos_of_nonconj S T x Z tau hdom hnconj
  have hred : lReducedJacobian S T x Z tau =
      lExpJacobian S T x Z tau *
        DifferentialGeometry.PDE.RicciFlow.Perelman.redDensity
          S T x (lExp S T x Z tau) tau := by
    rw [lReducedJacobian, lRedLog,
      DifferentialGeometry.PDE.RicciFlow.Perelman.redDensity]
    have hexp :
        Real.log (lExpJacobian S T x Z tau) -
            redLength S T x (lExp S T x Z tau) tau -
            ((Module.finrank ℝ E : ℝ) / 2) * Real.log tau -
            ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi) =
          Real.log (lExpJacobian S T x Z tau) +
            (-redLength S T x (lExp S T x Z tau) tau -
              ((Module.finrank ℝ E : ℝ) / 2) * Real.log tau -
              ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi)) := by
      ring
    rw [hexp, Real.exp_add, Real.exp_log hJ]
  rw [hred, lExpJacobian]
  field_simp [ne_of_gt (lSourceDensity_pos S T x)]

private theorem original_inj_domain_nonconj
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : ℝ) (x : M)
    (hRm : ∀ sigma : ℝ, 0 < sigma → Icc (T - sigma) T ⊆ D.regular →
      ∃ K : ℝ, ∀ t ∈ Icc (T - sigma) T, ∀ y : M,
        normSq0S (I := I) (S.base.metric t) y 4
          (S.base.rm04 t y) ≤ K)
    (tau : ℝ) (htau : 0 < tau) {Z : E}
    (hZ : Z ∈ lInjDomain S T x tau) :
    (Z, tau) ∈ lExpPosDom S T x ∧ ¬ IsLConjugate S T x Z tau := by
  obtain ⟨sigma, hlt, hmin⟩ := hZ
  have hsigma : 0 < sigma := lMinDomain_pos S T x Z sigma hmin
  have hdomSigma : (Z, sigma) ∈ lExpPosDom S T x :=
    ((mem_lMinDomain S T x Z sigma).mp hmin).1
  have hreg : Icc (T - sigma) T ⊆ D.regular := by
    intro t ht
    have hnonneg : 0 ≤ T - t := sub_nonneg.mpr ht.2
    have hback : T - t ≤ sigma := by linarith only [ht.1]
    have hsqrt : Real.sqrt (T - t) ∈ Icc (0 : ℝ) (Real.sqrt sigma) :=
      ⟨Real.sqrt_nonneg _, Real.sqrt_le_sqrt hback⟩
    have hclock := lExpPosDom_regularity S T x Z hdomSigma hsqrt
    have heq : T - (Real.sqrt (T - t)) ^ 2 = t := by
      rw [Real.sq_sqrt hnonneg]
      ring
    simpa only [heq] using hclock
  obtain ⟨K, hK⟩ := hRm sigma hsigma hreg
  exact ⟨lExpPosDom_down S T x Z hdomSigma htau hlt.le,
    lMinVec_nconj_lt_of_rm S hS K T x hmin hlt hK⟩

end NonconjugateNormalization

section ChangeOfVariables

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

theorem redVolume_lint_of_param
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : ℝ) (x : M)
    (hRm : ∀ sigma : ℝ, 0 < sigma → Icc (T - sigma) T ⊆ D.regular →
      ∃ K : ℝ, ∀ t ∈ Icc (T - sigma) T, ∀ y : M,
        normSq0S (I := I) (S.base.metric t) y 4
          (S.base.rm04 t y) ≤ K)
    (tau : ℝ) (htau : 0 < tau)
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞)
    (hsource : Φ.source = lInjDomain S T x tau)
    (hmap : Set.EqOn Φ (fun Z : E ↦ lExp S T x Z tau)
      (lInjDomain S T x tau))
    (hnull : riemannianVolumeMeasure (I := I) (M := M)
      (S.base.metric (T - tau)) Φ.targetᶜ = 0) :
    DifferentialGeometry.PDE.RicciFlow.redVolume S T x tau =
      ∫⁻ Z in lInjDomain S T x tau,
        ENNReal.ofReal (lReducedJacobian S T x Z tau * lSourceDensity S T x)
        ∂modelHaar (E := E) := by
  let U : Set E := lInjDomain S T x tau
  let Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1 :=
    { toPartialEquiv := Φ.toPartialEquiv
      open_source := Φ.open_source
      open_target := Φ.open_target
      contMDiffOn_toFun := Φ.contMDiffOn_toFun.of_le (by norm_num)
      contMDiffOn_invFun := Φ.contMDiffOn_invFun.of_le (by norm_num) }
  have hUeq : U = Ψ.source := hsource.symm
  have hUmeas : MeasurableSet U := by
    rw [hUeq]
    exact Ψ.open_source.measurableSet
  have hUsource : U ⊆ Ψ.source := by
    rw [hUeq]
  have hΨmap : Set.EqOn Ψ (fun Z : E ↦ lExp S T x Z tau) Ψ.source := by
    intro Z hZ
    apply hmap
    change Z ∈ U
    rw [hUeq]
    exact hZ
  have himage : Ψ '' U = Φ.target := by
    rw [hUeq]
    exact Ψ.toPartialEquiv.image_source_eq_target
  have htarget : Φ.target ∈ ae
      (riemannianVolumeMeasure (I := I) (M := M)
        (S.base.metric (T - tau))) :=
    mem_ae_iff.mpr hnull
  calc
    DifferentialGeometry.PDE.RicciFlow.redVolume S T x tau =
        ∫⁻ y in Ψ '' U, ENNReal.ofReal
          (DifferentialGeometry.PDE.RicciFlow.Perelman.redDensity S T x y tau)
          ∂riemannianVolumeMeasure (I := I) (M := M)
            (S.base.metric (T - tau)) := by
      unfold DifferentialGeometry.PDE.RicciFlow.redVolume
      rw [himage]
      exact congrArg
        (fun μ : Measure M ↦ ∫⁻ y, ENNReal.ofReal
          (DifferentialGeometry.PDE.RicciFlow.Perelman.redDensity S T x y tau) ∂μ)
        (Measure.restrict_eq_self_of_ae_mem htarget).symm
    _ = ∫⁻ Z in U,
        ENNReal.ofReal (paramDensity (I := I) (S.base.metric (T - tau)) Ψ Z) *
          ENNReal.ofReal
            (DifferentialGeometry.PDE.RicciFlow.Perelman.redDensity
              S T x (Ψ Z) tau)
        ∂modelHaar (E := E) :=
      riemVol_param_lint (I := I) (S.base.metric (T - tau)) Ψ
        (fun y ↦ ENNReal.ofReal
          (DifferentialGeometry.PDE.RicciFlow.Perelman.redDensity S T x y tau))
        hUmeas hUsource
    _ = ∫⁻ Z in U,
        ENNReal.ofReal (lReducedJacobian S T x Z tau * lSourceDensity S T x)
        ∂modelHaar (E := E) := by
      refine MeasureTheory.setLIntegral_congr_fun hUmeas ?_
      intro Z hZ
      dsimp only
      have hZsrc : Z ∈ Ψ.source := hUsource hZ
      have hΨZ : Ψ Z = lExp S T x Z tau := hΨmap hZsrc
      obtain ⟨hdom, hnconj⟩ :=
        original_inj_domain_nonconj S hS T x hRm tau htau hZ
      rw [paramDensity_eq_lExpDensity_of_eqOn S T x tau Ψ hΨmap Z hZsrc,
        hΨZ]
      rw [← ENNReal.ofReal_mul
        (lExpDensity_pos_of_nonconj S T x Z tau hdom hnconj).le]
      exact congrArg ENNReal.ofReal
        (lRedJac_mul_src_of_nonconj S T x Z tau hdom hnconj).symm
    _ = ∫⁻ Z in lInjDomain S T x tau,
        ENNReal.ofReal (lReducedJacobian S T x Z tau * lSourceDensity S T x)
        ∂modelHaar (E := E) := rfl

end ChangeOfVariables

end DifferentialGeometry.PDE.RicciFlow

end
