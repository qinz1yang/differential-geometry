import DifferentialGeometry.Analysis.Calculus.HilbertBasisDerivative
import DifferentialGeometry.Analysis.Heat.Semigroup.MildSolutionPDE
import DifferentialGeometry.Analysis.Heat.Smoothing.SmoothingOfClosed
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace HeatEquation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

def IsStrongSolutionAt
    (g : SmoothRiemannianMetric I M)
    (u f : ℝ → Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    (t : ℝ) : Prop :=
  ∃ u_h : laplacianDomain (I := I) (M := M) g,
    H1ComplToLp (I := I) (M := M) g (u_h : H1Compl g) = u t ∧
      HasDerivAt u (laplacianOp (I := I) (M := M) g u_h + f t) t

def IsStrongSolutionOn
    (g : SmoothRiemannianMetric I M)
    (u f : ℝ → Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    (s : Set ℝ) : Prop :=
  ∀ t ∈ s, IsStrongSolutionAt (I := I) (M := M) g u f t

theorem mildSolution_hasDerivAt_laplacianOp_add_of_lift
    (g : SmoothRiemannianMetric I M)
    (u_0 : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    {f : ℝ → Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)}
    (hf : Continuous f) {t : ℝ} (ht : 0 < t)
    {v : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)}
    (hderiv : HasDerivAt (mildSolution (I := I) (M := M) g u_0 f) v t)
    (u_h : laplacianDomain (I := I) (M := M) g)
    (hu_h : H1ComplToLp (I := I) (M := M) g (u_h : H1Compl g) =
      mildSolution (I := I) (M := M) g u_0 f t) :
    HasDerivAt (mildSolution (I := I) (M := M) g u_0 f)
      (laplacianOp (I := I) (M := M) g u_h + f t) t := by
  have hv : v = laplacianOp (I := I) (M := M) g u_h + f t := by
    set b := resolventHilbertEigenbasisSigma (I := I) (M := M) g
    apply b.repr.injective
    ext i
    rw [b.repr_apply_apply, b.repr_apply_apply]
    have hinner : HasDerivAt
        (fun s : ℝ => ⟪b i, mildSolution (I := I) (M := M) g u_0 f s⟫_ℝ)
        ⟪b i, v⟫_ℝ t := by
      have hcomp := (innerSL (𝕜 := ℝ)
        (E := Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
        (b i)).hasFDerivAt.comp_hasDerivAt t hderiv
      simpa [Function.comp_def, innerSL_apply_apply] using hcomp
    have hmodal := hasDerivAt_mildSolution_inner_basis
      (I := I) (M := M) g u_0 hf ht i
    have hcoeff := hinner.unique hmodal
    rw [inner_add_right,
      laplacianOp_inner_eigenbasis (I := I) (M := M) g u_h i,
      hu_h]
    exact hcoeff
  simpa [hv] using hderiv

theorem mildSolution_isStrongSolutionAt_of_differentiable
    (g : SmoothRiemannianMetric I M)
    (u_0 : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    {f : ℝ → Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)}
    (hf : Continuous f) {t : ℝ} (ht : 0 < t)
    (hdiff : DifferentiableAt ℝ (mildSolution (I := I) (M := M) g u_0 f) t)
    (u_h : laplacianDomain (I := I) (M := M) g)
    (hu_h : H1ComplToLp (I := I) (M := M) g (u_h : H1Compl g) =
      mildSolution (I := I) (M := M) g u_0 f t) :
    IsStrongSolutionAt (I := I) (M := M) g
      (mildSolution (I := I) (M := M) g u_0 f) f t := by
  refine ⟨u_h, hu_h, ?_⟩
  exact mildSolution_hasDerivAt_laplacianOp_add_of_lift
    (I := I) (M := M) g u_0 hf ht hdiff.hasDerivAt u_h hu_h

theorem heatSemigroup_isStrongSolutionAt
    (g : SmoothRiemannianMetric I M)
    (u_0 : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    {t : ℝ} (ht : 0 < t) :
    IsStrongSolutionAt (I := I) (M := M) g
      (fun s : ℝ => heatSemigroup (I := I) (M := M) g s u_0)
      (fun _ => 0) t := by
  let u_h : laplacianDomain (I := I) (M := M) g :=
    ⟨heatSemigroupExplicitLift (I := I) (M := M) g 0 t u_0,
      heatSemigroupExplicitLift_zero_mem_laplacianDomain
        (I := I) (M := M) g t u_0⟩
  refine ⟨u_h, ?_, ?_⟩
  · exact H1ComplToLp_heatSemigroupExplicitLift (I := I) (M := M) g 0 ht u_0
  · simpa [u_h] using
      hasDerivAt_heatSemigroup_eq_laplacianOp (I := I) (M := M) g ht u_0

theorem heatSemigroup_isStrongSolutionOn
    (g : SmoothRiemannianMetric I M)
    (u_0 : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    IsStrongSolutionOn (I := I) (M := M) g
      (fun s : ℝ => heatSemigroup (I := I) (M := M) g s u_0)
      (fun _ => 0) (Set.Ioi 0) := by
  intro t ht
  exact heatSemigroup_isStrongSolutionAt (I := I) (M := M) g u_0 ht

theorem mildSolution_zero_forcing_isStrongSolutionAt
    (g : SmoothRiemannianMetric I M)
    (u_0 : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    {t : ℝ} (ht : 0 < t) :
    IsStrongSolutionAt (I := I) (M := M) g
      (mildSolution (I := I) (M := M) g u_0 (fun _ => 0))
      (fun _ => 0) t := by
  have hpath : mildSolution (I := I) (M := M) g u_0 (fun _ => 0) =
      fun s => heatSemigroup (I := I) (M := M) g s u_0 := by
    funext s
    exact mildSolution_zero_forcing (I := I) (M := M) g u_0 s
  rw [hpath]
  exact heatSemigroup_isStrongSolutionAt (I := I) (M := M) g u_0 ht

theorem mildSolution_zero_forcing_isStrongSolutionOn
    (g : SmoothRiemannianMetric I M)
    (u_0 : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    IsStrongSolutionOn (I := I) (M := M) g
      (mildSolution (I := I) (M := M) g u_0 (fun _ => 0))
      (fun _ => 0) (Set.Ioi 0) := by
  intro t ht
  exact mildSolution_zero_forcing_isStrongSolutionAt
    (I := I) (M := M) g u_0 ht

private lemma exp_convolution_derivative_identity
    (lam : ℝ) {t : ℝ}
    {h dh : ℝ → ℝ}
    (hderiv : ∀ s : ℝ, HasDerivAt h (dh s) s)
    (hdh : Continuous dh) :
    Real.exp (-lam * t) * h 0 +
        ∫ s in (0 : ℝ)..t, Real.exp (-lam * (t - s)) * dh s =
      -lam * (∫ s in (0 : ℝ)..t, Real.exp (-lam * (t - s)) * h s) + h t := by
  let phi : ℝ → ℝ := fun s => Real.exp (-lam * (t - s))
  have hh : Continuous h := continuous_iff_continuousAt.mpr fun s => (hderiv s).continuousAt
  have hphi : Continuous phi := by
    unfold phi
    fun_prop
  have hphi_deriv : ∀ s : ℝ, HasDerivAt phi (lam * phi s) s := by
    intro s
    have harg : HasDerivAt (fun r : ℝ => -lam * (t - r)) lam s := by
      convert ((hasDerivAt_const s t).sub (hasDerivAt_id s)).const_mul (-lam) using 1
      all_goals ring
    have hexp := harg.exp
    simpa [phi, mul_comm] using hexp
  have hprod : ∀ s : ℝ, HasDerivAt (fun r => phi r * h r)
      (lam * (phi s * h s) + phi s * dh s) s := by
    intro s
    convert (hphi_deriv s).mul (hderiv s) using 1
    all_goals ring
  have hfirst : Continuous (fun s => lam * (phi s * h s)) :=
    continuous_const.mul (hphi.mul hh)
  have hsecond : Continuous (fun s => phi s * dh s) := hphi.mul hdh
  have hsum : Continuous (fun s => lam * (phi s * h s) + phi s * dh s) := by
    exact hfirst.add hsecond
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := t) (fun s _ => hprod s) (hsum.intervalIntegrable 0 t)
  rw [intervalIntegral.integral_add (hfirst.intervalIntegrable 0 t)
      (hsecond.intervalIntegrable 0 t),
    intervalIntegral.integral_const_mul] at hftc
  have hphi_zero : phi 0 = Real.exp (-lam * t) := by simp [phi]
  have hphi_t : phi t = 1 := by simp [phi]
  rw [hphi_zero, hphi_t, one_mul] at hftc
  have hphi_identity : phi 0 * h 0 + ∫ s in (0 : ℝ)..t, phi s * dh s =
      -lam * (∫ s in (0 : ℝ)..t, phi s * h s) + h t := by
    rw [hphi_zero]
    ring_nf at hftc ⊢
    linarith
  simpa [phi] using hphi_identity

private theorem mildSolution_strongDerivative_inner_basis
    (g : SmoothRiemannianMetric I M)
    (u_0 : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    {f f' : ℝ → Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)}
    (hf : ∀ s : ℝ, HasDerivAt f (f' s) s)
    (hf' : Continuous f') {t : ℝ} (ht : 0 < t)
    (i : EigenIdx (I := I) (M := M) g) :
    ⟪resolventHilbertEigenbasisSigma (I := I) (M := M) g i,
      -(heatPower (I := I) (M := M) g 1 t u_0) +
        mildSolution (I := I) (M := M) g (f 0) f' t⟫_ℝ =
      -(EigenIdx.lambda (I := I) (M := M) i) *
        ⟪resolventHilbertEigenbasisSigma (I := I) (M := M) g i,
          mildSolution (I := I) (M := M) g u_0 f t⟫_ℝ +
        ⟪resolventHilbertEigenbasisSigma (I := I) (M := M) g i, f t⟫_ℝ := by
  set b := resolventHilbertEigenbasisSigma (I := I) (M := M) g
  set lam := EigenIdx.lambda (I := I) (M := M) i
  let h : ℝ → ℝ := fun s => ⟪b i, f s⟫_ℝ
  let dh : ℝ → ℝ := fun s => ⟪b i, f' s⟫_ℝ
  have hf_cont : Continuous f := continuous_iff_continuousAt.mpr fun s => (hf s).continuousAt
  have hderiv : ∀ s : ℝ, HasDerivAt h (dh s) s := by
    intro s
    have hcomp := (innerSL (𝕜 := ℝ)
      (E := Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
      (b i)).hasFDerivAt.comp_hasDerivAt s (hf s)
    simpa [h, dh, Function.comp_def, innerSL_apply_apply] using hcomp
  have hdh : Continuous dh := by
    exact (innerSL (𝕜 := ℝ)
      (E := Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
      (b i)).continuous.comp hf'
  have hconv := exp_convolution_derivative_identity (t := t) lam hderiv hdh
  have horig := mildSolution_inner_basis (I := I) (M := M) g u_0 hf_cont ht.le i
  have hder := mildSolution_inner_basis (I := I) (M := M) g (f 0) hf' ht.le i
  rw [inner_add_right, inner_neg_right,
    heatPower_inner_eigenbasis (I := I) (M := M) g 1 ht i u_0,
    pow_one, hder, horig]
  change -(lam * Real.exp (-lam * t) * ⟪b i, u_0⟫_ℝ) +
      (Real.exp (-lam * t) * h 0 +
        ∫ s in (0 : ℝ)..t, Real.exp (-lam * (t - s)) * dh s) =
    -lam * (Real.exp (-lam * t) * ⟪b i, u_0⟫_ℝ +
      ∫ s in (0 : ℝ)..t, Real.exp (-lam * (t - s)) * h s) + h t
  rw [hconv]
  ring

theorem mildSolution_hasDerivAt_of_hasDerivAt_forcing
    (g : SmoothRiemannianMetric I M)
    (u_0 : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    {f f' : ℝ → Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)}
    (hf : ∀ s : ℝ, HasDerivAt f (f' s) s)
    (hf' : Continuous f') {t : ℝ} (ht : 0 < t) :
    HasDerivAt (mildSolution (I := I) (M := M) g u_0 f)
      (-(heatPower (I := I) (M := M) g 1 t u_0) +
        mildSolution (I := I) (M := M) g (f 0) f' t) t := by
  let v : ℝ → Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
    fun s => -(heatPower (I := I) (M := M) g 1 s u_0) +
      mildSolution (I := I) (M := M) g (f 0) f' s
  have hpow : ContinuousOn
      (fun s : ℝ => heatPower (I := I) (M := M) g 1 s u_0) (Set.Ioi 0) :=
    (continuousOn_heatPower_Ioi (I := I) (M := M) g 1).clm_apply continuousOn_const
  have hmild : ContinuousOn
      (mildSolution (I := I) (M := M) g (f 0) f') (Set.Ioi 0) :=
    (mildSolution_continuous (I := I) (M := M) g (f 0) hf').mono Ioi_subset_Ici_self
  have hv : ContinuousOn v (Set.Ioi 0) := hpow.neg.add hmild
  have hf_cont : Continuous f := continuous_iff_continuousAt.mpr fun s => (hf s).continuousAt
  apply hasDerivAt_of_inner_hilbertBasis
    (resolventHilbertEigenbasisSigma (I := I) (M := M) g)
    isOpen_Ioi hv
  · intro s hs i
    have hmodal := hasDerivAt_mildSolution_inner_basis
      (I := I) (M := M) g u_0 hf_cont hs i
    have hcoeff := mildSolution_strongDerivative_inner_basis
      (I := I) (M := M) g u_0 hf hf' hs i
    rw [hcoeff]
    exact hmodal
  · exact ht

theorem mildSolution_isStrongSolutionAt_of_hasDerivAt_forcing
    (g : SmoothRiemannianMetric I M)
    (u_0 : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    {f f' : ℝ → Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)}
    (hf : ∀ s : ℝ, HasDerivAt f (f' s) s)
    (hf' : Continuous f') {t : ℝ} (ht : 0 < t) :
    IsStrongSolutionAt (I := I) (M := M) g
      (mildSolution (I := I) (M := M) g u_0 f) f t := by
  let derivative := -(heatPower (I := I) (M := M) g 1 t u_0) +
    mildSolution (I := I) (M := M) g (f 0) f' t
  let laplacian := derivative - f t
  have hcoeff : ∀ i : EigenIdx (I := I) (M := M) g,
      ⟪resolventHilbertEigenbasisSigma (I := I) (M := M) g i, laplacian⟫_ℝ =
        -(EigenIdx.lambda (I := I) (M := M) i) *
          ⟪resolventHilbertEigenbasisSigma (I := I) (M := M) g i,
            mildSolution (I := I) (M := M) g u_0 f t⟫_ℝ := by
    intro i
    rw [show laplacian = derivative - f t from rfl, inner_sub_right,
      show derivative = -(heatPower (I := I) (M := M) g 1 t u_0) +
        mildSolution (I := I) (M := M) g (f 0) f' t from rfl,
      mildSolution_strongDerivative_inner_basis
        (I := I) (M := M) g u_0 hf hf' ht i]
    ring
  obtain ⟨u_h, hu_h, hlap⟩ :=
    (exists_laplacianDomain_lift_iff_inner_eigenbasis
      (I := I) (M := M) g
      (mildSolution (I := I) (M := M) g u_0 f t) laplacian).mpr hcoeff
  refine ⟨u_h, hu_h, ?_⟩
  rw [hlap]
  have hderiv := mildSolution_hasDerivAt_of_hasDerivAt_forcing
    (I := I) (M := M) g u_0 hf hf' ht
  change HasDerivAt (mildSolution (I := I) (M := M) g u_0 f)
    (laplacian + f t) t
  convert hderiv using 1
  change (derivative - f t) + f t = derivative
  abel

theorem mildSolution_isStrongSolutionOn_of_hasDerivAt_forcing
    (g : SmoothRiemannianMetric I M)
    (u_0 : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    {f f' : ℝ → Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)}
    (hf : ∀ s : ℝ, HasDerivAt f (f' s) s)
    (hf' : Continuous f') :
    IsStrongSolutionOn (I := I) (M := M) g
      (mildSolution (I := I) (M := M) g u_0 f) f (Set.Ioi 0) := by
  intro t ht
  exact mildSolution_isStrongSolutionAt_of_hasDerivAt_forcing
    (I := I) (M := M) g u_0 hf hf' ht

theorem mildSolution_hasDerivAt_of_contDiff_forcing
    (g : SmoothRiemannianMetric I M)
    (u_0 : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    {f : ℝ → Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)}
    (hf : ContDiff ℝ 1 f) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (mildSolution (I := I) (M := M) g u_0 f)
      (-(heatPower (I := I) (M := M) g 1 t u_0) +
        mildSolution (I := I) (M := M) g (f 0) (deriv f) t) t := by
  apply mildSolution_hasDerivAt_of_hasDerivAt_forcing
    (I := I) (M := M) g u_0 (f' := deriv f)
  · intro s
    exact (hf.differentiable (by norm_num) s).hasDerivAt
  · exact hf.continuous_deriv_one
  · exact ht

theorem mildSolution_isStrongSolutionOn_of_contDiff_forcing
    (g : SmoothRiemannianMetric I M)
    (u_0 : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    {f : ℝ → Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)}
    (hf : ContDiff ℝ 1 f) :
    IsStrongSolutionOn (I := I) (M := M) g
      (mildSolution (I := I) (M := M) g u_0 f) f (Set.Ioi 0) := by
  apply mildSolution_isStrongSolutionOn_of_hasDerivAt_forcing
    (I := I) (M := M) g u_0 (f' := deriv f)
  · intro s
    exact (hf.differentiable (by norm_num) s).hasDerivAt
  · exact hf.continuous_deriv_one

end HeatEquation
end Analysis
end DifferentialGeometry

end
