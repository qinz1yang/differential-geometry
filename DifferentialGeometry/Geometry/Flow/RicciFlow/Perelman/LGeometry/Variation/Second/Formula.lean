import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Index.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Variation.Second.Regularity

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
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem lLength_second_variation
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    (f : Real → Real → M) (hf : IsSmoothVariation (I := I) f)
    (a b : Real)
    (hgeo : IsLGeodesic S T (f 0) (Set.uIcc a b))
    (hfixa : ∀ u : Real, f u a = f 0 a)
    (hfixb : ∀ u : Real, f u b = f 0 b) :
    HasDerivAt
      (fun u : Real =>
        deriv (fun v : Real =>
          lLength S T (fun tau : Real => f v tau) a b) u)
      (2 * lIndex S T (f 0)
        (fun tau : Real =>
          lVelocity (I := I) (fun u : Real => f u tau) 0)
        (fun tau : Real =>
          lVelocity (I := I) (fun u : Real => f u tau) 0) a b)
      0 := by
  let gamma : Real → M := f 0
  let Y : (tau : Real) → TangentSpace I (gamma tau) := fun tau =>
    lVelocity (I := I) (fun u : Real => f u tau) 0
  let DY : (tau : Real) → TangentSpace I (gamma tau) :=
    lJacobiVelocity S T gamma Y
  let U : Real → Real := fun tau =>
    (S.base.metric (T - tau)).inner (gamma tau) (DY tau) (Y tau)
  let P : Real → Real := fun tau =>
    ((S.base.metric (T - tau)).inner (gamma tau)
        (covDerivAlong (I := I) (S.base.metric (T - tau)) gamma DY tau)
        (Y tau) +
      (S.base.metric (T - tau)).inner (gamma tau) (DY tau) (DY tau)) +
      2 * S.ricciAt (T - tau) (gamma tau) (vec2 (DY tau) (Y tau))
  let J : Real → Real := fun tau =>
    Real.sqrt tau * lJacobiPair S T gamma Y tau (Y tau)
  let G : Real → Real := lIndexIntegrand S T gamma Y Y
  let Q : Real → Real := fun tau => (1 / Real.sqrt tau) * U tau
  let V : Set Real := {tau : Real | T - tau ∈ D.regular}
  let A : Set (Real × Real) :=
    {p : Real × Real | 0 < p.2 ∧ T - p.2 ∈ D.regular}
  let Eul : Real × Real → Real := fun p =>
    (-2 * Real.sqrt p.2) *
      lEulerPair S T (f p.1) p.2
        (lVelocity (I := I) (fun u : Real => f u p.2) p.1)
  let dEul : Real → Real := fun tau =>
    fderiv Real Eul (0, tau) (1, 0)
  have hpos : 0 < min a b :=
    lt_min (hgeo.pos Set.left_mem_uIcc) (hgeo.pos Set.right_mem_uIcc)
  have ht : ∀ tau ∈ Set.uIcc a b, T - tau ∈ D.regular :=
    fun tau htau => hgeo.regular htau
  have hgamma : ∀ tau ∈ Set.uIcc a b,
      MDifferentiableAt 𝓘(Real, Real) I gamma tau := by
    intro tau htau
    simpa only [gamma] using hgeo.mdiffAt htau
  have hY : ∀ tau ∈ Set.uIcc a b,
      DifferentiableAt Real (chartRepAt (I := I) gamma Y tau) tau := by
    intro tau _
    simpa only [gamma, Y, lVelocity, varFst] using
      variationField_chartRep_differentiableAt
        (I := I) f hf tau
  have hDY : ∀ tau ∈ Set.uIcc a b,
      DifferentiableAt Real
        (chartRepAt (I := I) gamma DY tau) tau := by
    intro tau htau
    simpa only [gamma, Y, DY] using
      differentiableAt_chartRepAt_lJacobiVelocity_variation_field (I := I) S hS T f hf tau
        (hgeo.pos htau) (ht tau htau)
  have hVopen : IsOpen V :=
    D.regular_isOpen.preimage (continuous_const.sub continuous_id)
  have hU1 : ContDiffOn Real 1 U V := by
    simpa only [U, DY, gamma, Y, V] using
      contDiffOn_one_metric_inner_lJacobiVelocity_variation_field (I := I) S hS T f hf 0
  have hUcont : ContinuousOn U (Set.uIcc a b) :=
    hU1.continuousOn.mono (fun tau htau => ht tau htau)
  have hdUcont : ContinuousOn (deriv U) (Set.uIcc a b) :=
    (hU1.continuousOn_deriv_of_isOpen hVopen (by norm_num)).mono
      (fun tau htau => ht tau htau)
  have hdUEq : ∀ tau ∈ Set.uIcc a b, deriv U tau = P tau := by
    intro tau htau
    have hinner := lInner_deriv S hS T gamma DY Y tau (ht tau htau)
      (hgamma tau htau) (hDY tau htau) (hY tau htau)
    simpa only [U, P, DY, lJacobiVelocity] using hinner.deriv
  have hPcont : ContinuousOn P (Set.uIcc a b) :=
    hdUcont.congr (fun tau htau => (hdUEq tau htau).symm)
  have hPint : IntervalIntegrable P MeasureTheory.volume a b :=
    hPcont.intervalIntegrable
  have hAopen : IsOpen A := by
    change IsOpen
      ({p : Real × Real | 0 < p.2} ∩
        {p : Real × Real | T - p.2 ∈ D.regular})
    exact (isOpen_lt continuous_const continuous_snd).inter
      (D.regular_isOpen.preimage (continuous_const.sub continuous_snd))
  have hEul1 : ContDiffOn Real 1 Eul A := by
    simpa only [Eul, A] using lEuler_var_c1 (I := I) S hS T f hf
  have hEulDiff : DifferentiableOn Real Eul A :=
    hEul1.differentiableOn (by norm_num)
  have hdEulJoint : ContinuousOn
      (fun p : Real × Real => fderiv Real Eul p (1, 0)) A := by
    exact (hEul1.continuousOn_fderiv_of_isOpen hAopen (by norm_num)).clm_apply
      continuousOn_const
  have hdEulCont : ContinuousOn dEul (Set.uIcc a b) := by
    have hmap : ContinuousOn (fun tau : Real => ((0 : Real), tau))
        (Set.uIcc a b) := continuousOn_const.prodMk continuousOn_id
    apply hdEulJoint.comp hmap
    intro tau htau
    exact ⟨lt_of_lt_of_le hpos htau.1, ht tau htau⟩
  have hEulSlice : ∀ tau ∈ Set.uIcc a b,
      HasDerivAt (fun u : Real => Eul (u, tau)) (dEul tau) 0 := by
    intro tau htau
    have hpA : ((0 : Real), tau) ∈ A :=
      ⟨lt_of_lt_of_le hpos htau.1, ht tau htau⟩
    have hEulAt : DifferentiableAt Real Eul (0, tau) :=
      (hEulDiff (0, tau) hpA).differentiableAt (hAopen.mem_nhds hpA)
    simpa only [dEul] using Aux2.hasDerivAt_slice_fst
      (fun u s : Real => Eul (u, s)) 0 tau hEulAt
  have hdEulEq : ∀ tau ∈ Set.uIcc a b, dEul tau = -2 * J tau := by
    intro tau htau
    let W : (u : Real) → TangentSpace I (f u tau) := fun u =>
      lVelocity (I := I) (fun v : Real => f v tau) u
    have hslice : ContMDiffAt 𝓘(Real, Real) I 2
        (fun u : Real => f u tau) 0 := by
      have hincl : ContMDiff 𝓘(Real, Real)
          (𝓘(Real, Real).prod 𝓘(Real, Real)) (8 : ℕ)
          (fun u : Real => (u, tau)) :=
        contMDiff_id.prodMk contMDiff_const
      have hcomp := (hf : ContMDiff _ _ (8 : ℕ) _).comp hincl
      exact hcomp.contMDiffAt.of_le (by norm_num)
    have hW : DifferentiableAt Real
        (chartRepAt (I := I) (fun u : Real => f u tau) W 0) 0 := by
      change DifferentiableAt Real
        (chartRepAt (I := I) (fun u : Real ↦ f u tau)
          (fun u : Real ↦ lVelocity (I := I) (fun v : Real ↦ f v tau) u) 0) 0
      exact differentiableAt_chartRepAt_lVelocity (I := I) (fun u : Real ↦ f u tau) 0 hslice
    have hpoint := hasDerivAt_lEulerPair_variation_of_hasLEquationAt (I := I) S hS T f hf tau
      (hgeo.pos htau) (ht tau htau) W hW (hgeo.at htau)
    have hweighted : HasDerivAt (fun u : Real => Eul (u, tau))
        ((-2 * Real.sqrt tau) * lJacobiPair S T gamma Y tau (Y tau)) 0 := by
      simpa only [Eul, W, gamma, Y] using
        hpoint.const_mul (-2 * Real.sqrt tau)
    have heq := (hEulSlice tau htau).unique hweighted
    rw [heq]
    simp only [J]
    ring
  have hJcont : ContinuousOn J (Set.uIcc a b) := by
    have hraw : ContinuousOn (fun tau : Real => (-1 / 2 : Real) * dEul tau)
        (Set.uIcc a b) := continuousOn_const.mul hdEulCont
    apply hraw.congr
    intro tau htau
    change J tau = (-1 / 2 : Real) * dEul tau
    rw [hdEulEq tau htau]
    ring
  have hJint : IntervalIntegrable J MeasureTheory.volume a b :=
    hJcont.intervalIntegrable
  have hinvSqrt : ContinuousOn (fun tau : Real => 1 / Real.sqrt tau)
      (Set.uIcc a b) :=
    continuousOn_const.div continuousOn_id.sqrt (fun tau htau =>
      ne_of_gt (Real.sqrt_pos.2 (lt_of_lt_of_le hpos htau.1)))
  have hQcont : ContinuousOn Q (Set.uIcc a b) := by
    exact hinvSqrt.mul hUcont
  have hpoint : ∀ tau ∈ Set.uIcc a b,
      2 * G tau + 2 * J tau =
        (2 * Real.sqrt tau) * P tau + Q tau := by
    intro tau htau
    simpa only [G, J, P, Q, U, DY] using
      lIndex_balance (I := I) S T gamma Y Y tau
        (lt_of_lt_of_le hpos htau.1)
  let Graw : Real → Real := fun tau =>
    (((2 * Real.sqrt tau) * P tau + Q tau) - 2 * J tau) / 2
  have hGrawCont : ContinuousOn Graw (Set.uIcc a b) := by
    exact ((((continuousOn_const.mul continuousOn_id.sqrt).mul hPcont).add
      hQcont).sub (continuousOn_const.mul hJcont)).div_const 2
  have hGeq : Set.EqOn G Graw (Set.uIcc a b) := by
    intro tau htau
    dsimp only [Graw]
    linarith [hpoint tau htau]
  have hGcont : ContinuousOn G (Set.uIcc a b) :=
    hGrawCont.congr (fun tau htau => hGeq htau)
  have hIint : IntervalIntegrable G MeasureTheory.volume a b :=
    hGcont.intervalIntegrable
  have hYa : Y a = 0 := by
    have hconst : (fun u : Real => f u a) = fun _ : Real => f 0 a := by
      funext u
      exact hfixa u
    simp only [Y]
    rw [hconst]
    simp only [lVelocity, mfderiv_const]
    rfl
  have hYb : Y b = 0 := by
    have hconst : (fun u : Real => f u b) = fun _ : Real => f 0 b := by
      funext u
      exact hfixb u
    simp only [Y]
    rw [hconst]
    simp only [lVelocity, mfderiv_const]
    rfl
  have hzero := lIndex_eq_neg_integral_lJacobiPair_of_boundary_eq_zero (I := I) S hS T gamma Y Y a b hpos ht
    hgamma hDY hY (by simpa only [P, DY] using hPint)
    (by simpa only [J] using hJint) (by simpa only [G] using hIint) hYa hYb
  have hcoef :
      (∫ tau in a..b,
        (-2 * Real.sqrt tau) * lJacobiPair S T gamma Y tau (Y tau)) =
        2 * lIndex S T gamma Y Y a b := by
    calc
      _ = ∫ tau in a..b, (-2 : Real) * J tau := by
        apply intervalIntegral.integral_congr
        intro tau _
        simp only [J]
        ring
      _ = (-2 : Real) * ∫ tau in a..b, J tau := by
        rw [intervalIntegral.integral_const_mul]
      _ = 2 * lIndex S T gamma Y Y a b := by
        rw [hzero]
        ring
  have hsecond := lLength_second_variation_eq_integral_lJacobiPair (I := I)
    S hS T f hf a b hgeo hfixa hfixb
  rw [show
    (∫ tau in a..b,
      (-2 * Real.sqrt tau) *
        lJacobiPair S T (f 0)
          (fun r : Real =>
            lVelocity (I := I) (fun u : Real => f u r) 0)
          tau (lVelocity (I := I) (fun u : Real => f u tau) 0)) =
      2 * lIndex S T gamma Y Y a b by
        simpa only [gamma, Y] using hcoef] at hsecond
  simpa only [gamma, Y] using hsecond

end normedSpaceCompatibility

end DifferentialGeometry.PDE.RicciFlow.Perelman
