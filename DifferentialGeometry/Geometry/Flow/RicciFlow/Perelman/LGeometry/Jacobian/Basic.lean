import DifferentialGeometry.Analysis.Integration.Measure.Jacobian.Derivative
import DifferentialGeometry.Geometry.Comparison.Variation.Jacobi.Gram
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Jacobi.ExponentialMap
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedLength.HamiltonBound

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Matrix Set
open scoped Manifold ContDiff Topology

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor0SBundle

universe u uE uH

variable {E : Type uE}
variable {H : Type uH} [TopologicalSpace H]

private theorem trace_mul_trans
    {ι : Type*} [Fintype ι]
    (G A : Matrix ι ι Real) (hG : ∀ i j, G i j = G j i) :
    trace (G * A.transpose) = trace (G * A) := by
  classical
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.transpose_apply]
  calc
    (∑ i : ι, ∑ j : ι, G i j * A i j) =
      ∑ j : ι, ∑ i : ι, G i j * A i j := Finset.sum_comm
    _ = ∑ i : ι, ∑ j : ι, G i j * A j i := by
      refine Finset.sum_congr rfl fun i _ => ?_
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hG j i]

section Gram

variable [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {D : RealTimeInterval}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def lGram
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (gamma : Real → M) (Y : ι → ∀ tau, TangentSpace I (gamma tau))
    (tau : Real) : Matrix ι ι Real :=
  Matrix.of fun i j =>
    (S.base.metric (T - tau)).inner (gamma tau) (Y i tau) (Y j tau)

noncomputable def lGramDeriv
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (gamma : Real → M) (Y : ι → ∀ tau, TangentSpace I (gamma tau))
    (tau : Real) : Matrix ι ι Real :=
  Matrix.of fun i j =>
    (S.base.metric (T - tau)).inner (gamma tau)
        (covDerivAlong (I := I) (S.base.metric (T - tau)) gamma (Y i) tau)
        (Y j tau) +
      (S.base.metric (T - tau)).inner (gamma tau) (Y i tau)
        (covDerivAlong (I := I) (S.base.metric (T - tau)) gamma (Y j) tau) +
      2 * S.ricciAt (T - tau) (gamma tau) (vec2 (Y i tau) (Y j tau))

noncomputable def lJacDensity
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (gamma : Real → M) (Y : ι → ∀ tau, TangentSpace I (gamma tau))
    (tau : Real) : Real :=
  Real.sqrt (lGram S T gamma Y tau).det

omit [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] [Fintype ι] [DecidableEq ι] in
theorem lGram_hasDeriv
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (gamma : Real → M)
    (Y : ι → ∀ tau, TangentSpace I (gamma tau)) (tau : Real)
    (ht : T - tau ∈ D.regular)
    (hgamma : MDifferentiableAt 𝓘(Real, Real) I gamma tau)
    (hY : ∀ i, DifferentiableAt Real
      (chartRepAt (I := I) gamma (Y i) tau) tau)
    (i j : ι) :
    HasDerivAt (fun r => lGram S T gamma Y r i j)
      (lGramDeriv S T gamma Y tau i j) tau := by
  simpa only [lGram, lGramDeriv, Matrix.of_apply, add_assoc] using
    lInner_deriv S hS T gamma (Y i) (Y j) tau ht hgamma (hY i) (hY j)

omit [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
theorem lJacDen_hasDeriv
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (gamma : Real → M)
    (Y : ι → ∀ tau, TangentSpace I (gamma tau)) (tau : Real)
    (ht : T - tau ∈ D.regular)
    (hgamma : MDifferentiableAt 𝓘(Real, Real) I gamma tau)
    (hY : ∀ i, DifferentiableAt Real
      (chartRepAt (I := I) gamma (Y i) tau) tau)
    (hpos : 0 < (lGram S T gamma Y tau).det) :
    HasDerivAt (lJacDensity S T gamma Y)
      ((1 / 2) * trace
          ((lGram S T gamma Y tau)⁻¹ * lGramDeriv S T gamma Y tau) *
        lJacDensity S T gamma Y tau) tau := by
  with_unfolding_all
    exact DifferentialGeometry.Integral.Measure.hasDerivAt_sqrt_det_eq_half_trace_inv_mul
      (lGram S T gamma Y) (lGramDeriv S T gamma Y tau) tau
      (lGram_hasDeriv S hS T gamma Y tau ht hgamma hY) hpos

omit [NeZero (Module.finrank Real E)]
  [FiniteDimensional Real E] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M] in
theorem lGram_det_pos
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (gamma : Real → M) (Y : ι → ∀ tau, TangentSpace I (gamma tau))
    (tau : Real) (hY : LinearIndependent Real fun i => Y i tau) :
    0 < (lGram S T gamma Y tau).det := by
  simpa only [lGram, DifferentialGeometry.Geometry.Riemannian.Variation.curveGram,
    Matrix.of_apply] using
    DifferentialGeometry.Geometry.Riemannian.Variation.curveGram_det_pos
      (I := I) (S.base.metric (T - tau)) gamma Y tau hY

omit [NeZero (Module.finrank Real E)]
  [FiniteDimensional Real E] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M] in
theorem lJacDensity_pos
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (gamma : Real → M) (Y : ι → ∀ tau, TangentSpace I (gamma tau))
    (tau : Real) (hY : LinearIndependent Real fun i => Y i tau) :
    0 < lJacDensity S T gamma Y tau := by
  exact Real.sqrt_pos.mpr (lGram_det_pos S T gamma Y tau hY)

end Gram

section Exp

variable [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
variable {D : RealTimeInterval}

noncomputable def lExpField
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (x : M)
    (Z V : TangentSpace I x) (tau : Real) :
    TangentSpace I (lExp S T x Z tau) :=
  mfderiv 𝓘(Real, E) I (fun W : E => lExp S T x W tau) Z V

noncomputable def lRegFieldVel
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (x : M)
    (Z V : TangentSpace I x) (tau : Real) :
    TangentSpace I (lRegCurve S T x Z (Real.sqrt tau)) :=
  covDerivAlong (I := I) (S.base.metric (T - tau))
    (lRegCurve S T x Z) (lRegJacobiField S T x Z V) (Real.sqrt tau)

noncomputable def lExpFieldVel
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (x : M)
    (Z V : TangentSpace I x) (tau : Real) :
    TangentSpace I (lExp S T x Z tau) :=
  lJacobiVelocity S T (fun q => lExp S T x Z q)
    (fun q => lExpField S T x Z V q) tau

noncomputable def lExpSqVel
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (x : M)
    (Z V : TangentSpace I x) (tau : Real) :
    TangentSpace I (lExp S T x Z ((Real.sqrt tau) ^ 2)) :=
  covDerivAlong (I := I) (S.base.metric (T - tau))
    (fun r : Real => lExp S T x Z (r ^ 2))
    (fun r => lExpField S T x Z V (r ^ 2)) (Real.sqrt tau)

omit [NeZero (Module.finrank Real E)] [CompactSpace M] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem lRegSq_pair
    (S : SolutionOn (I := I) (M := M) D)
    (T : Real) (x : M)
    (Z V : TangentSpace I x) (tau : Real)
    (htau : 0 < tau)
    (Q : TangentSpace I (lExp S T x Z tau)) :
    (S.base.metric (T - tau)).inner (lExp S T x Z tau)
      (lRegFieldVel S T x Z V tau : E) (Q : E) =
      (S.base.metric (T - tau)).inner (lExp S T x Z tau)
        (lExpSqVel S T x Z V tau : E) (Q : E) := by
  let b : Real := Real.sqrt tau
  let gamma : Real → M := fun q => lExp S T x Z q
  let Y : ∀ q, TangentSpace I (gamma q) := fun q =>
    lExpField S T x Z V q
  have hb : 0 < b := by
    exact Real.sqrt_pos.2 htau
  have hcurve : (fun r : Real => gamma (r ^ 2)) =ᶠ[nhds b]
      lRegCurve S T x Z := by
    filter_upwards [Ioi_mem_nhds hb] with r hr
    simp only [gamma, lExp]
    rw [Real.sqrt_sq hr.le]
  have hfield : ∀ᶠ r in nhds b,
      (Y (r ^ 2) : E) = (lRegJacobiField S T x Z V r : E) := by
    filter_upwards [Ioi_mem_nhds hb] with r hr
    simp only [Y, lExpField, lExpJacobi_eq]
    rw [Real.sqrt_sq hr.le]
  have hcongr :=
    DifferentialGeometry.Geometry.Riemannian.covDerivAlong_congr_curve
      (I := I) (S.base.metric (T - tau))
      (fun r : Real => Y (r ^ 2)) (lRegJacobiField S T x Z V)
      hcurve hfield
  have hleft := congrArg
    (fun W : E => (S.base.metric (T - tau)).inner
      (lExp S T x Z tau) W Q) hcongr.symm
  simpa only [lRegFieldVel, lExpSqVel, b, gamma, Y] using hleft

omit [NeZero (Module.finrank Real E)] [I.Boundaryless]
  [T2Space M] [CompactSpace M] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem sqVel_pair
    (g : SmoothRiemannianMetric I M)
    (gamma : Real → M) (Y : ∀ q, TangentSpace I (gamma q))
    (tau : Real) (htau : 0 < tau)
    (hgamma : MDifferentiableAt 𝓘(Real, Real) I gamma tau)
    (hY : DifferentiableAt Real
      (chartRepAt (I := I) gamma Y tau) tau)
    (Q : TangentSpace I (gamma tau)) :
    g.inner (gamma tau)
        ((covDerivAlong (I := I) g
          (fun r : Real => gamma (r ^ 2)) (fun r => Y (r ^ 2))
          (Real.sqrt tau) : TangentSpace I
            (gamma ((Real.sqrt tau) ^ 2))) : E) Q =
      (2 * Real.sqrt tau) * g.inner (gamma tau)
        ((covDerivAlong (I := I) g gamma Y tau :
          TangentSpace I (gamma tau)) : E) Q := by
  let b : Real := Real.sqrt tau
  have hsq : b ^ 2 = tau := Real.sq_sqrt htau.le
  have hdiff : DifferentiableAt Real (fun r : Real => r ^ 2) b :=
    differentiableAt_id.pow 2
  have hcomp := covDerivAlong_comp (I := I) g gamma Y
    (fun r : Real => r ^ 2) b
      (by simpa only [hsq] using hgamma)
      (by simpa only [hsq] using hY) hdiff
  have hderiv : deriv (fun r : Real => r ^ 2) b = 2 * b := by
    rw [deriv_pow_field]
    norm_num
  rw [hderiv] at hcomp
  change covDerivAlong (I := I) g
      (fun r : Real => gamma (r ^ 2)) (fun r => Y (r ^ 2)) b =
    (2 * b) • covDerivAlong (I := I) g gamma Y (b ^ 2) at hcomp
  rw [hsq] at hcomp
  have hright := congrArg (fun W : E => g.inner (gamma tau) W Q) hcomp
  calc
    _ = g.inner (gamma tau)
        ((2 * b) • covDerivAlong (I := I) g gamma Y tau) Q := by
      simpa only [b] using hright
    _ = _ := by
      rw [map_smul (g.inner (gamma tau)),
        _root_.smul_apply, smul_eq_mul]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
theorem lExpSq_pair
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (x : M)
    (Z V : TangentSpace I x) (tau : Real)
    (hpos : (Z, tau) ∈ lExpPosDom (E := E) (I := I) S T x)
    (Q : TangentSpace I (lExp S T x Z tau)) :
    (S.base.metric (T - tau)).inner (lExp S T x Z tau)
        (lExpSqVel S T x Z V tau : E) (Q : E) =
      (2 * Real.sqrt tau) *
        (S.base.metric (T - tau)).inner (lExp S T x Z tau)
          (lExpFieldVel S T x Z V tau : E) (Q : E) := by
  let gamma : Real → M := fun q => lExp S T x Z q
  let Y : ∀ q, TangentSpace I (gamma q) := fun q =>
    lExpField S T x Z V q
  have hJac : HasLJacobiAt S T gamma Y tau := by
    simpa only [gamma, Y, lExpField] using
      hasLJacobiAt_lExp S hS T x Z V tau hpos
  with_unfolding_all
    exact sqVel_pair (I := I) (S.base.metric (T - tau)) gamma Y tau
      ((mem_lExpPosDom S T x Z tau).1 hpos).1 hJac.1 hJac.2.1 Q

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
theorem lRegJacobi_pair
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (x : M)
    (Z V : TangentSpace I x) (tau : Real)
    (hpos : (Z, tau) ∈ lExpPosDom (E := E) (I := I) S T x)
    (Q : TangentSpace I (lExp S T x Z tau)) :
    (S.base.metric (T - tau)).inner (lExp S T x Z tau)
      (lRegFieldVel S T x Z V tau : E) (Q : E) =
      (2 * Real.sqrt tau) *
        (S.base.metric (T - tau)).inner (lExp S T x Z tau)
          (lExpFieldVel S T x Z V tau : E) (Q : E) := by
  exact (lRegSq_pair S T x Z V tau
    ((mem_lExpPosDom S T x Z tau).1 hpos).1 Q).trans
      (lExpSq_pair S hS T x Z V tau hpos Q)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem redHess_lJac
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (x : M)
    {Z : TangentSpace I x} {tau : Real}
    (htau : 0 < tau)
    (hZ : Z ∈ lInjDomain (E := E) (I := I) S T x tau)
    (V W : TangentSpace I x) :
    hessFun (I := I) (S.base.metric (T - tau))
        (fun y : M => redLength S T x y tau)
        (lExp S T x Z tau) (lExpField S T x Z V tau)
          (lExpField S T x Z W tau) =
      (S.base.metric (T - tau)).inner (lExp S T x Z tau)
        (lExpFieldVel S T x Z V tau)
          (lExpField S T x Z W tau) := by
  let zE : E := show E from Z
  let : NormedAddCommGroup (TangentSpace 𝓘(Real, E) zE) :=
    Tensor0SBundle.tangentSpaceNormedAddCommGroup
      (I := 𝓘(Real, E)) (M := E) zE
  let : NormedSpace Real (TangentSpace 𝓘(Real, E) zE) :=
    Tensor0SBundle.tangentSpaceNormedSpace
      (I := 𝓘(Real, E)) (M := E) zE
  have hZinj := hZ
  obtain ⟨sigma, hsigma, hmin⟩ := hZ
  have hminTau : (Z, tau) ∈ lMinDomain S T x :=
    lMinDomain_down S hS T x Z hmin htau hsigma.le
  have hdom : (Z, tau) ∈ lExpPosDom S T x :=
    ((mem_lMinDomain S T x Z tau).1 hminTau).1
  have hconj : ¬ IsLConj S T x Z tau :=
    lMinVec_nconj_lt S hS T x hmin hsigma
  have hdomE : (zE, tau) ∈ lExpPosDom S T x := by
    exact hdom
  have hconjE : ¬ IsLConj S T x zE tau := by
    exact hconj
  let y : M := lExp S T x Z tau
  let g := S.base.metric (T - tau)
  let endMap : E → M := fun Q => lExp S T x Q tau
  let hloc := lExp_localDiffeo S hS T x zE tau hdomE hconjE
  let YV : TangentSpace I y := lExpField S T x Z V tau
  let YW : TangentSpace I y := lExpField S T x Z W tau
  have hInv : mfderiv I 𝓘(Real, E) hloc.localInverse y YV = V := by
    have hleft := by
      with_unfolding_all
        exact (hloc.mfderivToContinuousLinearEquiv (by simp)).left_inv V
    change mfderiv I 𝓘(Real, E) hloc.localInverse y
      (mfderiv 𝓘(Real, E) I endMap zE V) = V at hleft
    simpa only [YV, lExpField, endMap, zE] using hleft
  have hcostBranch :
      hessFun (I := I) g (fun q : M => lCost S T x q tau) y YV YW =
        hessFun (I := I) g
          (lActBranch S hS T x Z tau hdom hconj) y YV YW := by
    exact congrArg (fun A => A YV YW)
      (hessFun_congr (I := I) g
        (lCost_eq_branch S hS T x hZinj hdom hconj))
  have hbranch :
      hessFun (I := I) g
          (lActBranch S hS T x Z tau hdom hconj) y YV YW =
        g.inner y (lRegFieldVel S T x Z V tau) YW := by
    have hout := lActBranch_hess S hS T x Z tau hdom hconj YV YW
    simpa only [y, g, YV, YW, hloc, hInv, lRegFieldVel] using hout
  let c : Real := (2 * Real.sqrt tau)⁻¹
  have hfun :
      (fun q : M => redLength S T x q tau) =
        c • (fun q : M => lCost S T x q tau) := by
    funext q
    simp only [redLength, c, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv]
    ring
  rw [hfun, hessFun_smul]
  change c * hessFun (I := I) g (fun q : M => lCost S T x q tau)
      y YV YW = g.inner y (lExpFieldVel S T x Z V tau) YW
  rw [hcostBranch, hbranch]
  rw [lRegJacobi_pair S hS T x Z V tau hdom YW]
  have hb : 2 * Real.sqrt tau ≠ 0 :=
    mul_ne_zero (by norm_num) (Real.sqrt_pos.2 htau).ne'
  dsimp only [c]
  field_simp
  rfl

omit [NeZero (Module.finrank Real E)] [I.Boundaryless]
  [T2Space M] [CompactSpace M] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem trace_invGram
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : SmoothRiemannianMetric I M) {y : M}
    (basis : Module.Basis ι Real (TangentSpace I y))
    (B : Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 2 y)
    (hdet : IsUnit (Matrix.of fun i j =>
      g.inner y (basis i) (basis j)).det) :
    trace ((Matrix.of fun i j => g.inner y (basis i) (basis j))⁻¹ *
        Matrix.of fun i j => B (vec2 (I := I) (basis i) (basis j))) =
      metricTracePair0SAt (I := I) g B := by
  classical
  let G : Matrix ι ι Real :=
    Matrix.of fun i j => g.inner y (basis i) (basis j)
  have hGherm : G.IsHermitian := by
    refine Matrix.IsHermitian.ext ?_
    intro i j
    simp only [star_trivial, G, Matrix.of_apply]
    exact g.symm y (basis j) (basis i)
  have hGinv : ∀ i j, G⁻¹ i j = G⁻¹ j i := by
    intro i j
    simpa only [star_trivial] using hGherm.inv.apply j i
  have hinv : MetricInverseInBasis (I := I) g y basis
      (fun i j => G⁻¹ i j) := by
    intro i j
    constructor
    · have hmat := congrArg (fun A : Matrix ι ι Real => A i j)
        (Matrix.nonsing_inv_mul G hdet)
      simpa only [Matrix.mul_apply, Matrix.one_apply, G, Matrix.of_apply] using hmat
    · have hmat := congrArg (fun A : Matrix ι ι Real => A i j)
        (Matrix.mul_nonsing_inv G hdet)
      simpa only [Matrix.mul_apply, Matrix.one_apply, G, Matrix.of_apply] using hmat
  rw [metricTracePair0SAt_eq_sum_basis (I := I) g basis
    (fun i j => G⁻¹ i j) hinv B]
  change trace (G⁻¹ * Matrix.of fun i j =>
      B (vec2 (I := I) (basis i) (basis j))) = _
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.of_apply]
  calc
    (∑ i : ι, ∑ j : ι,
        G⁻¹ i j * B (vec2 (I := I) (basis j) (basis i))) =
      ∑ j : ι, ∑ i : ι,
        G⁻¹ i j * B (vec2 (I := I) (basis j) (basis i)) :=
      Finset.sum_comm
    _ = ∑ i : ι, ∑ j : ι,
        G⁻¹ i j * B (vec2 (I := I) (basis i) (basis j)) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hGinv j i]

noncomputable def lExpGram
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (x : M)
    (Z : TangentSpace I x) (tau : Real) :
    Matrix (Fin (Module.finrank Real E)) (Fin (Module.finrank Real E)) Real :=
  lGram S T (fun q => lExp S T x Z q)
    (fun i q => lExpField S T x Z ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i) q) tau

noncomputable def lExpGramDeriv
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (x : M)
    (Z : TangentSpace I x) (tau : Real) :
    Matrix (Fin (Module.finrank Real E)) (Fin (Module.finrank Real E)) Real :=
  lGramDeriv S T (fun q => lExp S T x Z q)
    (fun i q => lExpField S T x Z ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i) q) tau

noncomputable def lExpHess
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (x : M)
    (Z : TangentSpace I x) (tau : Real) :
    Matrix (Fin (Module.finrank Real E)) (Fin (Module.finrank Real E)) Real :=
  Matrix.of fun i j =>
    hessFun (I := I) (S.base.metric (T - tau))
      (fun y : M => redLength S T x y tau) (lExp S T x Z tau)
      (lExpField S T x Z ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i) tau)
      (lExpField S T x Z ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j) tau)

noncomputable def lExpRicci
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (x : M)
    (Z : TangentSpace I x) (tau : Real) :
    Matrix (Fin (Module.finrank Real E)) (Fin (Module.finrank Real E)) Real :=
  Matrix.of fun i j =>
    S.ricciAt (T - tau) (lExp S T x Z tau)
      (vec2
        (lExpField S T x Z ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i) tau)
        (lExpField S T x Z ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j) tau))

noncomputable def lExpVelGram
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (x : M)
    (Z : TangentSpace I x) (tau : Real) :
    Matrix (Fin (Module.finrank Real E)) (Fin (Module.finrank Real E)) Real :=
  Matrix.of fun i j =>
    (S.base.metric (T - tau)).inner (lExp S T x Z tau)
      (lExpFieldVel S T x Z ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i) tau)
      (lExpField S T x Z ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j) tau)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem lExpVel_eq_hess
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (x : M)
    {Z : TangentSpace I x} {tau : Real}
    (htau : 0 < tau)
    (hZ : Z ∈ lInjDomain (E := E) (I := I) S T x tau) :
    lExpVelGram S T x Z tau = lExpHess S T x Z tau := by
  ext i j
  exact (redHess_lJac S hS T x htau hZ
    ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i) ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j)).symm

omit [NeZero (Module.finrank Real E)] [CompactSpace M] in
theorem lExpGramDeriv_eq
    (S : SolutionOn (I := I) (M := M) D)
    (T : Real) (x : M) (Z : TangentSpace I x) (tau : Real) :
    lExpGramDeriv S T x Z tau =
      lExpVelGram S T x Z tau + (lExpVelGram S T x Z tau).transpose +
        2 • lExpRicci S T x Z tau := by
  ext i j
  simp only [lExpGramDeriv, lGramDeriv, lExpVelGram, lExpRicci,
    Matrix.of_apply, Matrix.add_apply, Matrix.transpose_apply,
    Matrix.smul_apply, lExpFieldVel, lJacobiVelocity]
  rw [(S.base.metric (T - tau)).symm (lExp S T x Z tau)
    (lExpField S T x Z ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i) tau)
    (covDerivAlong (I := I) (S.base.metric (T - tau))
      (fun q => lExp S T x Z q)
      (fun q => lExpField S T x Z ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j) q) tau)]
  ring

noncomputable def lExpDensity
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (x : M)
    (Z : TangentSpace I x) (tau : Real) : Real :=
  Real.sqrt (lExpGram S T x Z tau).det

noncomputable def lSrcGram
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (x : M) :
    Matrix (Fin (Module.finrank Real E)) (Fin (Module.finrank Real E)) Real :=
  Matrix.of fun i j =>
    (S.base.metric T).inner x ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i) ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j)

noncomputable def lSrcDensity
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (x : M) : Real :=
  Real.sqrt (lSrcGram S T x).det

noncomputable def lExpJac
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (x : M)
    (Z : TangentSpace I x) (tau : Real) : Real :=
  lExpDensity S T x Z tau / lSrcDensity S T x

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [NeZero (Module.finrank ℝ E)] in
theorem lExpGram_pos
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (x : M)
    {Z : TangentSpace I x} {tau : Real}
    (htau : 0 < tau)
    (hZ : Z ∈ lInjDomain (E := E) (I := I) S T x tau) :
    0 < (lExpGram S T x Z tau).det := by
  let zE : E := show E from Z
  let : NormedAddCommGroup (TangentSpace 𝓘(Real, E) zE) :=
    Tensor0SBundle.tangentSpaceNormedAddCommGroup
      (I := 𝓘(Real, E)) (M := E) zE
  let : NormedSpace Real (TangentSpace 𝓘(Real, E) zE) :=
    Tensor0SBundle.tangentSpaceNormedSpace
      (I := 𝓘(Real, E)) (M := E) zE
  have hZE : zE ∈ lInjDomain S T x tau := by
    exact hZ
  let f : E → M := fun W => lExp S T x W tau
  let L := mfderiv 𝓘(Real, E) I f zE
  have hinj : Function.Injective L := by
    with_unfolding_all
      exact
        ((lInj_local (E := E) (I := I) S hS T x tau htau hZE).mfderivToContinuousLinearEquiv
          (by simp)).injective
  have hker : L.toLinearMap.ker = ⊥ := LinearMap.ker_eq_bot.mpr hinj
  have hLI : LinearIndependent Real
      (fun i : Fin (Module.finrank Real E) => L ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)) := by
    with_unfolding_all
      exact (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).linearIndependent.map' L.toLinearMap hker
  simpa only [lExpGram, lExpField, f, L, zE] using
    lGram_det_pos S T (fun q => lExp S T x Z q)
      (fun i q => lExpField S T x Z ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i) q) tau hLI

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem lExpTrace_hess
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (x : M)
    {Z : TangentSpace I x} {tau : Real}
    (htau : 0 < tau)
    (hZ : Z ∈ lInjDomain (E := E) (I := I) S T x tau) :
    trace ((lExpGram S T x Z tau)⁻¹ * lExpHess S T x Z tau) =
      laplacian (I := I) (LeviCivita (I := I)
        (S.base.metric (T - tau))) (S.base.metric (T - tau))
        (fun y : M => redLength S T x y tau) (lExp S T x Z tau) := by
  classical
  let zE : E := show E from Z
  let : NormedAddCommGroup (TangentSpace 𝓘(Real, E) zE) :=
    Tensor0SBundle.tangentSpaceNormedAddCommGroup
      (I := 𝓘(Real, E)) (M := E) zE
  let : NormedSpace Real (TangentSpace 𝓘(Real, E) zE) :=
    Tensor0SBundle.tangentSpaceNormedSpace
      (I := 𝓘(Real, E)) (M := E) zE
  have hZE : zE ∈ lInjDomain S T x tau := by
    exact hZ
  let y : M := lExp S T x Z tau
  let g := S.base.metric (T - tau)
  let L :=
    (lInj_local (E := E) (I := I) S hS T x tau htau hZE)
      |>.mfderivToContinuousLinearEquiv (by simp)
  let basis : Module.Basis (Fin (Module.finrank Real E)) Real
      (TangentSpace I y) := by
    with_unfolding_all
      exact (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).map L.toLinearEquiv
  have hbasis (i : Fin (Module.finrank Real E)) :
      basis i = lExpField S T x Z ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i) tau := by
    simp only [basis, L, lExpField, zE]
    rfl
  have hGram : (Matrix.of fun i j => g.inner y (basis i) (basis j)) =
      lExpGram S T x Z tau := by
    ext i j
    simp only [lExpGram, lGram, Matrix.of_apply, g, y, hbasis]
  have hunit : IsUnit (lExpGram S T x Z tau).det :=
    (ne_of_gt (lExpGram_pos S hS T x htau hZ)).isUnit
  have htrace := trace_invGram (I := I) g basis
    (hessTensorAt (I := I) g
      (fun q : M => redLength S T x q tau) y)
    (by simpa only [hGram] using hunit)
  rw [hGram] at htrace
  have htrace' :
      trace ((lExpGram S T x Z tau)⁻¹ * lExpHess S T x Z tau) =
        metricTracePair0SAt (I := I) g
          (hessTensorAt (I := I) g
            (fun q : M => redLength S T x q tau) y) := by
    simpa only [lExpHess, Matrix.of_apply, hbasis,
      hessTensorAt_apply, g, y] using htrace
  obtain ⟨U, hUopen, hyU, hsmooth⟩ :=
    redLength_smooth S hS T x htau hZ
  have hlap := lap_eq_hess_on (I := I) g hUopen hsmooth hyU
  exact htrace'.trans (by simpa only [g, y] using hlap.symm)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [NeZero (Module.finrank ℝ E)] in
theorem lExpTrace_ricci
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (x : M)
    {Z : TangentSpace I x} {tau : Real}
    (htau : 0 < tau)
    (hZ : Z ∈ lInjDomain (E := E) (I := I) S T x tau) :
    trace ((lExpGram S T x Z tau)⁻¹ * lExpRicci S T x Z tau) =
      S.scalar (T - tau) (lExp S T x Z tau) := by
  classical
  let zE : E := show E from Z
  let : NormedAddCommGroup (TangentSpace 𝓘(Real, E) zE) :=
    Tensor0SBundle.tangentSpaceNormedAddCommGroup
      (I := 𝓘(Real, E)) (M := E) zE
  let : NormedSpace Real (TangentSpace 𝓘(Real, E) zE) :=
    Tensor0SBundle.tangentSpaceNormedSpace
      (I := 𝓘(Real, E)) (M := E) zE
  have hZE : zE ∈ lInjDomain S T x tau := by
    exact hZ
  let y : M := lExp S T x Z tau
  let g := S.base.metric (T - tau)
  let L :=
    (lInj_local (E := E) (I := I) S hS T x tau htau hZE)
      |>.mfderivToContinuousLinearEquiv (by simp)
  let basis : Module.Basis (Fin (Module.finrank Real E)) Real
      (TangentSpace I y) := by
    with_unfolding_all
      exact (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).map L.toLinearEquiv
  have hbasis (i : Fin (Module.finrank Real E)) :
      basis i = lExpField S T x Z ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i) tau := by
    simp only [basis, L, lExpField, zE]
    rfl
  have hGram : (Matrix.of fun i j => g.inner y (basis i) (basis j)) =
      lExpGram S T x Z tau := by
    ext i j
    simp only [lExpGram, lGram, Matrix.of_apply, g, y, hbasis]
  have hunit : IsUnit (lExpGram S T x Z tau).det :=
    (ne_of_gt (lExpGram_pos S hS T x htau hZ)).isUnit
  have htrace := trace_invGram (I := I) g basis
    (S.ricciAt (T - tau) y) (by simpa only [hGram] using hunit)
  rw [hGram] at htrace
  have htrace' :
      trace ((lExpGram S T x Z tau)⁻¹ * lExpRicci S T x Z tau) =
        metricTracePair0SAt (I := I) g (S.ricciAt (T - tau) y) := by
    simpa only [lExpRicci, Matrix.of_apply, hbasis, g, y] using htrace
  have hscalar := S.scalar_eq_metricTrace (I := I) (T - tau) y
  exact htrace'.trans (by
    simpa only [g, y, SolutionOn.family_metric] using hscalar.symm)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem lExpTrace_eq
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (x : M)
    {Z : TangentSpace I x} {tau : Real}
    (htau : 0 < tau)
    (hZ : Z ∈ lInjDomain (E := E) (I := I) S T x tau) :
    (1 / 2) * trace
        ((lExpGram S T x Z tau)⁻¹ * lExpGramDeriv S T x Z tau) =
      laplacian (I := I) (LeviCivita (I := I)
        (S.base.metric (T - tau))) (S.base.metric (T - tau))
        (fun y : M => redLength S T x y tau) (lExp S T x Z tau) +
      S.scalar (T - tau) (lExp S T x Z tau) := by
  classical
  let G := lExpGram S T x Z tau
  let Hm := lExpHess S T x Z tau
  have hGherm : G.IsHermitian := by
    refine Matrix.IsHermitian.ext ?_
    intro i j
    simp only [star_trivial, G, lExpGram, lGram, Matrix.of_apply]
    exact (S.base.metric (T - tau)).symm (lExp S T x Z tau)
      (lExpField S T x Z ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j) tau)
      (lExpField S T x Z ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i) tau)
  have hGinv : ∀ i j, G⁻¹ i j = G⁻¹ j i := by
    intro i j
    simpa only [star_trivial] using hGherm.inv.apply j i
  have htrans : trace (G⁻¹ * Hm.transpose) = trace (G⁻¹ * Hm) :=
    trace_mul_trans G⁻¹ Hm hGinv
  rw [lExpGramDeriv_eq, lExpVel_eq_hess S hS T x htau hZ]
  change (1 / 2) * trace (G⁻¹ * (Hm + Hm.transpose +
    2 • lExpRicci S T x Z tau)) = _
  simp only [Matrix.mul_add, Matrix.trace_add, Matrix.mul_smul,
    Matrix.trace_smul]
  rw [htrans, lExpTrace_hess S hS T x htau hZ,
    lExpTrace_ricci S hS T x htau hZ]
  ring

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [NeZero (Module.finrank ℝ E)] in
theorem lExpDensity_pos
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (x : M)
    {Z : TangentSpace I x} {tau : Real}
    (htau : 0 < tau)
    (hZ : Z ∈ lInjDomain (E := E) (I := I) S T x tau) :
    0 < lExpDensity S T x Z tau := by
  exact Real.sqrt_pos.mpr (lExpGram_pos S hS T x htau hZ)

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [T2Space M]
  [CompactSpace M] in
theorem lSrcDensity_pos
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (x : M) :
    0 < lSrcDensity S T x := by
  let gamma : Real → M := fun _ => x
  let V : Fin (Module.finrank Real E) →
      ∀ _ : Real, TangentSpace I x := fun i _ => (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i
  have hLI : LinearIndependent Real (fun i => V i 0) := by
    with_unfolding_all
      exact (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).linearIndependent
  have hdet : 0 <
      (DifferentialGeometry.Geometry.Riemannian.Variation.curveGram
        (I := I) (S.base.metric T) gamma V 0).det :=
    DifferentialGeometry.Geometry.Riemannian.Variation.curveGram_det_pos
      (I := I) (S.base.metric T) gamma V 0
        hLI
  exact Real.sqrt_pos.mpr (by
    simpa only [lSrcGram,
      DifferentialGeometry.Geometry.Riemannian.Variation.curveGram,
      Matrix.of_apply, gamma, V] using hdet)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [NeZero (Module.finrank ℝ E)] in
theorem lExpJac_pos
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (x : M)
    {Z : TangentSpace I x} {tau : Real}
    (htau : 0 < tau)
    (hZ : Z ∈ lInjDomain (E := E) (I := I) S T x tau) :
    0 < lExpJac S T x Z tau := by
  exact div_pos (lExpDensity_pos S hS T x htau hZ)
    (lSrcDensity_pos S T x)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem lExpDen_hasDeriv
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (x : M)
    {Z : TangentSpace I x} {tau : Real}
    (htau : 0 < tau)
    (hZ : Z ∈ lInjDomain (E := E) (I := I) S T x tau) :
    HasDerivAt (lExpDensity S T x Z)
      ((1 / 2) * trace
      ((lExpGram S T x Z tau)⁻¹ * lExpGramDeriv S T x Z tau) *
        lExpDensity S T x Z tau) tau := by
  have hZinj := hZ
  obtain ⟨sigma, hsigma, hmin⟩ := hZ
  have hminTau : (Z, tau) ∈ lMinDomain S T x :=
    lMinDomain_down S hS T x Z hmin htau hsigma.le
  have hdom : (Z, tau) ∈ lExpPosDom S T x :=
    ((mem_lMinDomain S T x Z tau).1 hminTau).1
  have ht : T - tau ∈ D.regular := by
    have hreg := lExpPosDom_reg S T x Z hdom
      (show Real.sqrt tau ∈ Set.Icc (0 : Real) (Real.sqrt tau) from
        ⟨Real.sqrt_nonneg tau, le_rfl⟩)
    simpa only [Real.sq_sqrt htau.le] using hreg
  let gamma : Real → M := fun q => lExp S T x Z q
  let Y : Fin (Module.finrank Real E) →
      ∀ q, TangentSpace I (gamma q) := fun i q =>
    lExpField S T x Z ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i) q
  have hJac (i : Fin (Module.finrank Real E)) :
      HasLJacobiAt S T gamma (Y i) tau := by
    simpa only [gamma, Y, lExpField] using
      hasLJacobiAt_lExp S hS T x Z ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i) tau hdom
  have hgamma : MDifferentiableAt 𝓘(Real, Real) I gamma tau :=
    (hJac (Classical.choice inferInstance)).1
  have hY : ∀ i, DifferentiableAt Real
      (chartRepAt (I := I) gamma (Y i) tau) tau := fun i => (hJac i).2.1
  have hout := lJacDen_hasDeriv S hS T gamma Y tau ht hgamma hY
    (by simpa only [lExpGram, gamma, Y] using
      lExpGram_pos S hS T x htau hZinj)
  with_unfolding_all
    exact hout

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem lExpJac_hasDeriv
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (x : M)
    {Z : TangentSpace I x} {tau : Real}
    (htau : 0 < tau)
    (hZ : Z ∈ lInjDomain (E := E) (I := I) S T x tau) :
    HasDerivAt (lExpJac S T x Z)
      ((laplacian (I := I) (LeviCivita (I := I)
          (S.base.metric (T - tau))) (S.base.metric (T - tau))
          (fun y : M => redLength S T x y tau) (lExp S T x Z tau) +
        S.scalar (T - tau) (lExp S T x Z tau)) *
        lExpJac S T x Z tau) tau := by
  have hout :=
    (lExpDen_hasDeriv S hS T x htau hZ).div_const (lSrcDensity S T x)
  rw [lExpTrace_eq S hS T x htau hZ] at hout
  have hfun :
      (fun q => lExpDensity S T x Z q / lSrcDensity S T x) =
        lExpJac S T x Z := rfl
  rw [hfun] at hout
  have hcoef :
      ((laplacian (I := I) (LeviCivita (I := I)
          (S.base.metric (T - tau))) (S.base.metric (T - tau))
          (fun y : M => redLength S T x y tau) (lExp S T x Z tau) +
        S.scalar (T - tau) (lExp S T x Z tau)) *
        lExpDensity S T x Z tau / lSrcDensity S T x) =
      ((laplacian (I := I) (LeviCivita (I := I)
          (S.base.metric (T - tau))) (S.base.metric (T - tau))
          (fun y : M => redLength S T x y tau) (lExp S T x Z tau) +
        S.scalar (T - tau) (lExp S T x Z tau)) *
        lExpJac S T x Z tau) := by
    rw [lExpJac]
    ring
  rw [hcoef] at hout
  with_unfolding_all exact hout

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem lExpLog_hasDeriv
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (x : M)
    {Z : TangentSpace I x} {tau : Real}
    (htau : 0 < tau)
    (hZ : Z ∈ lInjDomain (E := E) (I := I) S T x tau) :
    HasDerivAt (fun q => Real.log (lExpJac S T x Z q))
      (laplacian (I := I) (LeviCivita (I := I)
          (S.base.metric (T - tau))) (S.base.metric (T - tau))
          (fun y : M => redLength S T x y tau) (lExp S T x Z tau) +
        S.scalar (T - tau) (lExp S T x Z tau)) tau := by
  have hpos := lExpJac_pos S hS T x htau hZ
  have hout := (lExpJac_hasDeriv S hS T x htau hZ).log hpos.ne'
  convert hout using 1
  field_simp

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem lExpLog_deriv_le
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (x : M)
    {Z : TangentSpace I x} {tau : Real}
    (htau : 0 < tau)
    (hZ : Z ∈ lInjDomain (E := E) (I := I) S T x tau)
    (P : Fin (Module.finrank Real E) →
      ∀ s, TangentSpace I (lRegCurve S T x Z s))
    {Ω : Set Real} (hΩ : IsOpen Ω)
    (hΩseg : Set.Icc (0 : Real) (Real.sqrt tau) ⊆ Ω)
    (hW : ∀ i, ContMDiffOn (modelWithCornersSelf Real Real) I.tangent
      (8 : Nat)
      (fun s : Real ↦ (TotalSpace.mk' E
        (E := (TangentSpace I : M → Type _))
        (lRegCurve S T x Z s) ((s / Real.sqrt tau) • P i s) :
          TangentBundle I M)) Ω)
    (hP : ∀ i s, s ∈ Set.Icc (0 : Real) (Real.sqrt tau) →
      DifferentiableAt Real
        (chartRepAt (I := I) (lRegCurve S T x Z) (P i) s) s)
    (hDP : ∀ i s, s ∈ Set.Icc (0 : Real) (Real.sqrt tau) →
      covDerivAlong (I := I) (S.base.metric (T - s ^ 2))
          (lRegCurve S T x Z) (P i) s =
        (-2 * s) • ricciSharp (I := I) (S.base.metric (T - s ^ 2))
          (lRegCurve S T x Z s) (P i s))
    (hON : ∀ i j,
      (S.base.metric (T - tau)).inner (lExp S T x Z tau)
          (P i (Real.sqrt tau)) (P j (Real.sqrt tau)) =
        if i = j then 1 else 0)
    (hIint : ∀ i, IntervalIntegrable
      (fun s : Real ↦ (s / Real.sqrt tau) ^ 2 *
        lRegIndexIntegrand S T (lRegCurve S T x Z) (P i) (P i) s)
      MeasureTheory.volume 0 (Real.sqrt tau))
    (hRint : ∀ i, IntervalIntegrable
      (fun s : Real ↦ (2 * s ^ 2 / (Real.sqrt tau) ^ 2) *
        S.ricciAt (T - s ^ 2) (lRegCurve S T x Z s)
          (vec2 (P i s) (P i s)))
      MeasureTheory.volume 0 (Real.sqrt tau)) :
    deriv (fun q ↦ Real.log (lExpJac S T x Z q)) tau ≤
      (Module.finrank Real E : Real) / (2 * tau) -
        lK S T (lRegCurve S T x Z) (Real.sqrt tau) /
          (2 * tau * Real.sqrt tau) := by
  rw [(lExpLog_hasDeriv S hS T x htau hZ).deriv]
  calc
    _ ≤ ((Module.finrank Real E : Real) / (2 * tau) -
          S.scalar (T - tau) (lExp S T x Z tau) -
          lK S T (lRegCurve S T x Z) (Real.sqrt tau) /
            (2 * tau * Real.sqrt tau)) +
        S.scalar (T - tau) (lExp S T x Z tau) :=
      by
        simpa only [add_comm] using
          add_le_add_right
            (redLength_lap_K S hS T x htau hZ P hΩ hΩseg hW hP hDP
              hON hIint hRint)
            (S.scalar (T - tau) (lExp S T x Z tau))
    _ = _ := by ring

end Exp

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
