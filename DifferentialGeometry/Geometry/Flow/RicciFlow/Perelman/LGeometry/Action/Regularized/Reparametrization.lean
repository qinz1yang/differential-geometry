import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Defs
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open DifferentialGeometry.Geometry.Curvature
open Bundle MeasureTheory Set
open scoped Manifold ContDiff Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable {D : RealTimeInterval}

def squareReparametrization (gamma : Real -> M) (s : Real) : M :=
  gamma (s ^ 2)

def squareRootReparametrization (alpha : Real → M) (tau : Real) : M :=
  alpha (Real.sqrt tau)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem lVelocity_squareReparametrization
    (gamma : Real -> M) (s : Real)
    (hgamma : MDifferentiableAt 𝓘(Real, Real) I gamma (s ^ 2))
    :
    lVelocity (I := I) (squareReparametrization gamma) s =
      (2 * s) • lVelocity (I := I) gamma (s ^ 2) := by
  have hsqAt : MDifferentiableAt 𝓘(Real, Real) 𝓘(Real, Real)
      (fun x : Real => x ^ 2) s :=
    mdifferentiableAt_iff_differentiableAt.mpr (differentiableAt_id.pow 2)
  have hchain := mfderiv_comp
    (I := 𝓘(Real, Real)) (I' := 𝓘(Real, Real)) (I'' := I)
    (f := fun x : Real => x ^ 2) (g := gamma) s hgamma hsqAt
  have hsq :
      (mfderiv 𝓘(Real, Real) 𝓘(Real, Real)
        (fun x : Real => x ^ 2) s) (1 : Real) = 2 * s := by
    rw [mfderiv_eq_fderiv]
    change deriv (fun x : Real => x ^ 2) s = 2 * s
    rw [deriv_pow_field]
    norm_num
  have hchain1 := congrArg (fun L => L (1 : Real)) hchain
  have hcompval :
      ((mfderiv 𝓘(Real, Real) I gamma (s ^ 2)).comp
        (mfderiv 𝓘(Real, Real) 𝓘(Real, Real)
          (fun x : Real => x ^ 2) s)) (1 : Real) =
        (mfderiv 𝓘(Real, Real) I gamma (s ^ 2)) (2 * s) := by
    with_unfolding_all
      exact congrArg (mfderiv 𝓘(Real, Real) I gamma (s ^ 2)) hsq
  have hmid := hchain1.trans hcompval
  have hlin :
      (mfderiv 𝓘(Real, Real) I gamma (s ^ 2)) (2 * s) =
        (2 * s) • lVelocity (I := I) gamma (s ^ 2) := by
    let oneT : TangentSpace 𝓘(Real, Real) (s ^ 2) := (1 : Real)
    let twoST : TangentSpace 𝓘(Real, Real) (s ^ 2) := (2 * s : Real)
    have hmap := (mfderiv 𝓘(Real, Real) I gamma (s ^ 2)).map_smul
      (2 * s) oneT
    have harg : (2 * s) • oneT = twoST := by
      with_unfolding_all
        change (2 * s) * 1 = 2 * s
        ring
    rw [harg] at hmap
    with_unfolding_all exact hmap
  with_unfolding_all exact hmid.trans hlin

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem lVelocity_squareReparametrization_of_pos
    (gamma : Real → M) (s : Real) (hs : 0 < s) :
    lVelocity (I := I) (squareReparametrization gamma) s =
      (2 * s) • lVelocity (I := I) gamma (s ^ 2) := by
  by_cases hgamma : MDifferentiableAt 𝓘(Real, Real) I gamma (s ^ 2)
  · exact lVelocity_squareReparametrization (I := I) gamma s hgamma
  · have hs2 : 0 < s ^ 2 := sq_pos_of_pos hs
    have halpha : ¬ MDifferentiableAt 𝓘(Real, Real) I
        (squareReparametrization gamma) s := by
      intro halpha
      have hsqrt : Real.sqrt (s ^ 2) = s := Real.sqrt_sq hs.le
      have hsqrtDiff : MDifferentiableAt 𝓘(Real, Real) 𝓘(Real, Real)
          Real.sqrt (s ^ 2) :=
        mdifferentiableAt_iff_differentiableAt.mpr
          (Real.hasDerivAt_sqrt (ne_of_gt hs2)).differentiableAt
      have halpha' : MDifferentiableAt 𝓘(Real, Real) I
          (squareReparametrization gamma) (Real.sqrt (s ^ 2)) := by
        simpa only [hsqrt] using halpha
      have hcomp : MDifferentiableAt 𝓘(Real, Real) I
          (squareReparametrization gamma ∘ Real.sqrt) (s ^ 2) :=
        halpha'.comp (s ^ 2) hsqrtDiff
      have heq : (squareReparametrization gamma ∘ Real.sqrt) =ᶠ[𝓝 (s ^ 2)] gamma := by
        filter_upwards [eventually_gt_nhds hs2] with r hr
        simp only [Function.comp_apply, squareReparametrization, Real.sq_sqrt hr.le]
      exact hgamma (hcomp.congr_of_eventuallyEq heq.symm)
    have hleft : lVelocity (I := I) (squareReparametrization gamma) s = 0 := by
      unfold lVelocity
      rw [mfderiv_zero_of_not_mdifferentiableAt halpha]
      exact zero_apply _
    have hright : lVelocity (I := I) gamma (s ^ 2) = 0 := by
      unfold lVelocity
      rw [mfderiv_zero_of_not_mdifferentiableAt hgamma]
      exact zero_apply _
    rw [hleft, hright, smul_zero]
    rfl

variable [IsManifold I ∞ M] [FiniteDimensional Real E]
variable [IsManifold I 1 M]
variable [T2Space M] [SigmaCompactSpace M]

noncomputable def lRegDensity
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (gamma : Real -> M)
    (s : Real) : Real :=
  (1 / 2 : Real) *
      (S.base.metric (T - s ^ 2)).inner (squareReparametrization gamma s)
        (lVelocity (I := I) (squareReparametrization gamma) s)
        (lVelocity (I := I) (squareReparametrization gamma) s) +
    2 * s ^ 2 * S.scalar (T - s ^ 2) (squareReparametrization gamma s)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space M] [SigmaCompactSpace M] in
theorem lDensity_squareReparametrization
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (gamma : Real -> M)
    (s : Real)
    (hgamma : MDifferentiableAt 𝓘(Real, Real) I gamma (s ^ 2))
    (hs : 0 <= s) :
    lDensity S T gamma (s ^ 2) * (2 * s) = lRegDensity S T gamma s := by
  let g := S.base.metric (T - s ^ 2)
  let p := gamma (s ^ 2)
  let v := lVelocity (I := I) gamma (s ^ 2)
  have hfirst : (g.inner p) ((2 * s) • v) = (2 * s) • (g.inner p) v :=
    (g.inner p).map_smul (2 * s) v
  have hsecond : (g.inner p v) ((2 * s) • v) =
      (2 * s) • (g.inner p v) v :=
    (g.inner p v).map_smul (2 * s) v
  have hquad : g.inner p ((2 * s) • v) ((2 * s) • v) =
      (2 * s) ^ 2 * g.inner p v v := by
    calc
      g.inner p ((2 * s) • v) ((2 * s) • v) =
          ((2 * s) • (g.inner p v)) ((2 * s) • v) :=
        congrArg (fun L => L ((2 * s) • v)) hfirst
      _ = (2 * s) * ((2 * s) * g.inner p v v) := by
        rw [smul_apply, hsecond, smul_eq_mul, smul_eq_mul]
      _ = (2 * s) ^ 2 * g.inner p v v := by ring
  have hquad' : (S.base.metric (T - s ^ 2)).inner (gamma (s ^ 2))
      ((2 * s) • lVelocity (I := I) gamma (s ^ 2))
      ((2 * s) • lVelocity (I := I) gamma (s ^ 2)) =
      (2 * s) ^ 2 * (S.base.metric (T - s ^ 2)).inner (gamma (s ^ 2))
        (lVelocity (I := I) gamma (s ^ 2))
        (lVelocity (I := I) gamma (s ^ 2)) := by
    simpa only [g, p, v] using hquad
  rw [lRegDensity, lDensity, lSpeedSq, Real.sqrt_sq hs,
    lVelocity_squareReparametrization gamma s hgamma]
  simp only [squareReparametrization]
  calc
    _ = (1 / 2 : Real) * ((2 * s) ^ 2 *
          (S.base.metric (T - s ^ 2)).inner (gamma (s ^ 2))
            (lVelocity (I := I) gamma (s ^ 2))
            (lVelocity (I := I) gamma (s ^ 2))) +
        2 * s ^ 2 * S.scalar (T - s ^ 2) (gamma (s ^ 2)) := by ring
    _ = _ := by
      exact congrArg
        (fun z : Real => (1 / 2 : Real) * z +
          2 * s ^ 2 * S.scalar (T - s ^ 2) (gamma (s ^ 2))) hquad'.symm

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space M] [SigmaCompactSpace M] in
theorem lDensity_squareReparametrization_of_pos
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (gamma : Real → M)
    (s : Real) (hs : 0 < s) :
    lDensity S T gamma (s ^ 2) * (2 * s) =
      lRegDensity S T gamma s := by
  by_cases hgamma : MDifferentiableAt 𝓘(Real, Real) I gamma (s ^ 2)
  · exact lDensity_squareReparametrization S T gamma s hgamma hs.le
  · have hvel : lVelocity (I := I) gamma (s ^ 2) = 0 := by
      unfold lVelocity
      rw [mfderiv_zero_of_not_mdifferentiableAt hgamma]
      exact zero_apply _
    have hvelsq : lVelocity (I := I) (squareReparametrization gamma) s = 0 := by
      have h := lVelocity_squareReparametrization_of_pos (I := I) gamma s hs
      rw [hvel, smul_zero] at h
      with_unfolding_all exact h
    have hspeed0 : lSpeedSq S T gamma (s ^ 2) = 0 := by
      simp [lSpeedSq, hvel]
    have hreg0 :
        (S.base.metric (T - s ^ 2)).inner (squareReparametrization gamma s)
          (lVelocity (I := I) (squareReparametrization gamma) s)
          (lVelocity (I := I) (squareReparametrization gamma) s) = 0 := by
      simp [hvelsq]
    rw [lDensity, lRegDensity, Real.sqrt_sq hs.le, hspeed0, hreg0]
    simp only [squareReparametrization]
    ring

omit [T2Space M] [SigmaCompactSpace M] in
theorem lLength_squareReparametrization
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (gamma : Real -> M)
    (tau1 tau2 : Real) (htau1 : 0 <= tau1) (htau2 : 0 <= tau2)
    (hgamma : ∀ s ∈ uIcc (Real.sqrt tau1) (Real.sqrt tau2),
      MDifferentiableAt 𝓘(Real, Real) I gamma (s ^ 2)) :
    lLength S T gamma tau1 tau2 =
      ∫ s in Real.sqrt tau1..Real.sqrt tau2, lRegDensity S T gamma s := by
  have hsub :=
    intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
      (g := lDensity S T gamma) (f := fun s : Real => s ^ 2)
      (f' := fun s : Real => 2 * s)
      (a := Real.sqrt tau1) (b := Real.sqrt tau2)
      (continuous_id.pow 2).continuousOn
      (by
        intro s hs
        simpa using hasDerivAt_pow 2 s)
      (by
        intro s hs
        have hmin : 0 <= min (Real.sqrt tau1) (Real.sqrt tau2) :=
          le_min (Real.sqrt_nonneg tau1) (Real.sqrt_nonneg tau2)
        exact mul_nonneg (by norm_num) (hmin.trans hs.1.le))
  have hsub' :
      (∫ s in Real.sqrt tau1..Real.sqrt tau2,
        (lDensity S T gamma ∘ fun r : Real => r ^ 2) s * (2 * s)) =
        ∫ tau in tau1..tau2, lDensity S T gamma tau := by
    simpa only [Real.sq_sqrt htau1, Real.sq_sqrt htau2] using hsub
  have hcongr :
      (∫ s in Real.sqrt tau1..Real.sqrt tau2,
        (lDensity S T gamma ∘ fun r : Real => r ^ 2) s * (2 * s)) =
        ∫ s in Real.sqrt tau1..Real.sqrt tau2, lRegDensity S T gamma s := by
    apply intervalIntegral.integral_congr
    intro s hs
    have hs0 : 0 <= s := by
      rcases mem_uIcc.mp hs with hs | hs
      · exact (Real.sqrt_nonneg tau1).trans hs.1
      · exact (Real.sqrt_nonneg tau2).trans hs.1
    simpa only [Function.comp_apply] using
      lDensity_squareReparametrization S T gamma s (hgamma s hs) hs0
  simpa only [lLength] using hsub'.symm.trans hcongr

omit [T2Space M] [SigmaCompactSpace M] in
theorem lLength_squareReparametrization_ae
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (gamma : Real → M)
    (tau1 tau2 : Real) (htau1 : 0 ≤ tau1) (htau2 : 0 ≤ tau2) :
    lLength S T gamma tau1 tau2 =
      ∫ s in Real.sqrt tau1..Real.sqrt tau2, lRegDensity S T gamma s := by
  have hsub :=
    intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
      (g := lDensity S T gamma) (f := fun s : Real => s ^ 2)
      (f' := fun s : Real => 2 * s)
      (a := Real.sqrt tau1) (b := Real.sqrt tau2)
      (continuous_id.pow 2).continuousOn
      (by
        intro s _
        simpa using hasDerivAt_pow 2 s)
      (by
        intro s hs
        have hmin : 0 ≤ min (Real.sqrt tau1) (Real.sqrt tau2) :=
          le_min (Real.sqrt_nonneg tau1) (Real.sqrt_nonneg tau2)
        exact mul_nonneg (by norm_num) (hmin.trans hs.1.le))
  have hsub' :
      (∫ s in Real.sqrt tau1..Real.sqrt tau2,
        (lDensity S T gamma ∘ fun r : Real => r ^ 2) s * (2 * s)) =
        ∫ tau in tau1..tau2, lDensity S T gamma tau := by
    simpa only [Real.sq_sqrt htau1, Real.sq_sqrt htau2] using hsub
  have hcongr :
      (∫ s in Real.sqrt tau1..Real.sqrt tau2,
        (lDensity S T gamma ∘ fun r : Real => r ^ 2) s * (2 * s)) =
        ∫ s in Real.sqrt tau1..Real.sqrt tau2, lRegDensity S T gamma s := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards
      [MeasureTheory.Measure.ae_ne MeasureTheory.volume (0 : Real)]
        with s hs0 hsmem
    have hsu := Set.uIoc_subset_uIcc hsmem
    have hsnonneg : 0 ≤ s := by
      rcases Set.mem_uIcc.mp hsu with hs | hs
      · exact (Real.sqrt_nonneg tau1).trans hs.1
      · exact (Real.sqrt_nonneg tau2).trans hs.1
    have hspos : 0 < s := lt_of_le_of_ne hsnonneg hs0.symm
    simpa only [Function.comp_apply] using
      lDensity_squareReparametrization_of_pos (I := I) S T gamma s hspos
  simpa only [lLength] using hsub'.symm.trans hcongr

end DifferentialGeometry.PDE.RicciFlow.Perelman
