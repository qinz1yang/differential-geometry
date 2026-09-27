import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Jacobi.Basic

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

section normedSpaceCompatibility

attribute [-instance] InnerProductSpace.toNormedSpace

open Bundle Filter Set
open scoped Manifold ContDiff Topology

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.TensorLieDeriv
open MeasureTheory

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {D : RealTimeInterval}

omit [InnerProductSpace Real E] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem hasLJacobiAt_lExp
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (x : M)
    (Z V : TangentSpace I x) (tau : Real)
    (hpos : (Z, tau) ∈ lExpPosDom S T x) :
    HasLJacobiAt S T
      (fun q ↦ lExp S T x Z q)
      (fun q ↦ mfderiv 𝓘(Real, E) I
        (fun W : E ↦ lExp S T x W q) Z V)
      tau := by
  let s : Real := Real.sqrt tau
  let alpha : Real → M := lRegularizedCurve S T x Z
  let J : ∀ r, TangentSpace I (alpha r) :=
    fun r ↦ lRegularizedJacobiField S T x Z V r
  let gamma : Real → M := fun q ↦ lExp S T x Z q
  let Y : ∀ q, TangentSpace I (gamma q) := fun q ↦
    mfderiv 𝓘(Real, E) I (fun W : E ↦ lExp S T x W q) Z V
  change 0 < tau ∧ Real.sqrt tau ∈ lRegularizedDomain S T x Z at hpos
  rcases hpos with ⟨htau, hsdom⟩
  have hs : 0 < s := by
    simpa only [s] using Real.sqrt_pos.2 htau
  have hsq : s ^ 2 = tau := by
    simpa only [s] using Real.sq_sqrt htau.le
  have ht : T - s ^ 2 ∈ D.regular := by
    rcases hsdom with ⟨beta, K, _hKopen, _hKconn, _h0K, hsK, hbeta⟩
    exact (hbeta.2.2 s hsK).1
  have hregAll : IsLRegularizedJacobi S T alpha J (lRegularizedDomain S T x Z) := by
    simpa only [alpha, J] using
      lRegularizedCurve_jacobi (I := I) S hS T x Z V
        (lRegularizedDomain S T x Z) (fun _ hr ↦ hr)
  have hreg : HasLRegularizedJacobiAt S T alpha J s := hregAll s hsdom
  have hdom : ∀ᶠ r in nhds s, r ∈ lRegularizedDomain S T x Z :=
    (lRegularizedDomain_isOpen S T x Z).mem_nhds hsdom
  have hgamma_sq : ∀ᶠ r in nhds s,
      MDifferentiableAt (modelWithCornersSelf Real Real) I gamma (r ^ 2) := by
    filter_upwards [hdom, Ioi_mem_nhds hs] with r hrdom hr
    have hrreg := hregAll r hrdom
    have hsqrt : DifferentiableAt Real Real.sqrt (r ^ 2) :=
      differentiableAt_id.sqrt (sq_pos_of_pos hr).ne'
    have hsqrtMD : MDifferentiableAt
        (modelWithCornersSelf Real Real) (modelWithCornersSelf Real Real)
        Real.sqrt (r ^ 2) :=
      mdifferentiableAt_iff_differentiableAt.mpr hsqrt
    have hroot : Real.sqrt (r ^ 2) = r := Real.sqrt_sq hr.le
    have halpha : MDifferentiableAt
        (modelWithCornersSelf Real Real) I alpha (Real.sqrt (r ^ 2)) := by
      simpa only [hroot] using hrreg.1
    have hcomp := halpha.comp (f := Real.sqrt) (r ^ 2) hsqrtMD
    simpa only [gamma, alpha, lExp, Function.comp_def] using hcomp
  have hY_sq : ∀ᶠ r in nhds s,
      DifferentiableAt Real (chartRepAt (I := I) gamma Y (r ^ 2))
        (r ^ 2) := by
    filter_upwards [hdom, Ioi_mem_nhds hs] with r hrdom hr
    have hrreg := hregAll r hrdom
    have hsqrt : DifferentiableAt Real Real.sqrt (r ^ 2) :=
      differentiableAt_id.sqrt (sq_pos_of_pos hr).ne'
    have hroot : Real.sqrt (r ^ 2) = r := Real.sqrt_sq hr.le
    have hJ : DifferentiableAt Real
        (chartRepAt (I := I) alpha J r) (Real.sqrt (r ^ 2)) := by
      simpa only [hroot] using hrreg.2.1
    have hcomp := hJ.comp (r ^ 2) hsqrt
    have heq : chartRepAt (I := I) gamma Y (r ^ 2) =
        chartRepAt (I := I) alpha J r ∘ Real.sqrt := by
      funext q
      have hbase : gamma (r ^ 2) = alpha r := by
        simp only [gamma, alpha, lExp, hroot]
      have hcurve : gamma q = alpha (Real.sqrt q) := by
        rfl
      have hYq : Y q = J (Real.sqrt q) := by
        simpa only [Y, J] using
          lExpJacobi_eq (I := I) S T x Z V q
      simp only [chartRepAt_apply, Function.comp_def]
      rw [hbase, hcurve, hYq]
    rw [heq]
    exact hcomp
  let delta : Real → M := squareReparametrization gamma
  have halphaInf : ContMDiffAt (modelWithCornersSelf Real Real) I ∞ alpha s := by
    have hparam : ContMDiffAt (modelWithCornersSelf Real Real)
        (𝓘(Real, E).prod 𝓘(Real, Real)) ∞
        (fun r : Real ↦ (((Z : E), r) : E × Real)) s :=
      (contMDiff_const.prodMk contMDiff_id).contMDiffAt
    have hcomp := (lRegularizedCurve_smooth (I := I) (M := M) S hS T x hsdom).comp
      s hparam
    simpa only [alpha, Function.comp_def] using hcomp
  have hdelta_eq : delta =ᶠ[nhds s] alpha := by
    filter_upwards [Ioi_mem_nhds hs] with r hr
    simp only [delta, gamma, alpha, squareReparametrization, lExp]
    rw [Real.sqrt_sq hr.le]
  have hdeltaInf : ContMDiffAt
      (modelWithCornersSelf Real Real) I ∞ delta s :=
    halphaInf.congr_of_eventuallyEq hdelta_eq
  have hdelta2 : ContMDiffAt
      (modelWithCornersSelf Real Real) I 2 delta s :=
    hdeltaInf.of_le (by
      change (↑(2 : ENat) : WithTop ENat) ≤ ↑(⊤ : ENat)
      exact WithTop.coe_le_coe.mpr le_top)
  have hA : DifferentiableAt Real
      (chartRepAt (I := I) delta
        (fun r : Real ↦ lVelocity (I := I) delta r) s) s := by
    exact differentiableAt_chartRepAt_lVelocity (I := I) delta s hdelta2
  have hcurve : Set.EqOn alpha delta (Set.Ioi 0) := by
    intro r hr
    simp only [alpha, delta, gamma, squareReparametrization, lExp]
    rw [Real.sqrt_sq hr.le]
  have hfield : ∀ r ∈ Set.Ioi (0 : Real),
      (J r : E) = (Y (r ^ 2) : E) := by
    intro r hr
    simp only [J, Y, lExpJacobi_eq]
    rw [Real.sqrt_sq hr.le]
  have hregSq : HasLRegularizedJacobiAt S T delta
      (fun r : Real ↦ Y (r ^ 2)) s :=
    HasLRegularizedJacobiAt.congr_of_eqOn (I := I) S T J (fun r : Real ↦ Y (r ^ 2)) s
      (Set.Ioi 0) isOpen_Ioi hs hcurve hfield hreg
  have hout := hasLJacobiAt_of_squareReparametrization (I := I) S hS T gamma Y s hs ht
    hgamma_sq hY_sq (by simpa only [delta] using hA)
    (by simpa only [delta] using hregSq)
  simpa only [gamma, Y, hsq] using hout

end normedSpaceCompatibility

end DifferentialGeometry.PDE.RicciFlow.Perelman
