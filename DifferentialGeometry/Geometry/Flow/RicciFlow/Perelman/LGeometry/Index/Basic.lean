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

noncomputable def lIndexIntegrand
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (gamma : Real → M)
    (Y W : ∀ tau, TangentSpace I (gamma tau)) (tau : Real) : Real :=
  let t := T - tau
  let g := S.base.metric t
  let cov := S.base.connection t
  let X := lVelocity (I := I) gamma tau
  let DY := lJacobiVelocity S T gamma Y tau
  let DW := lJacobiVelocity S T gamma W tau
  let dRic := totalNabla0SFun (𝕜 := Real) (I := I)
    2 cov (S.ricci t) (gamma tau)
  Real.sqrt tau *
    (g.inner (gamma tau) DY DW -
      S.base.rm04 t (gamma tau) (vec4 (Y tau) X X (W tau)) +
      (1 / 2 : Real) *
        hessianSec (I := I) cov (metricCov_smooth (I := I) g)
          (S.scalar t) (scalarSmoothOfSolution (I := I) S t) (gamma tau)
          (vec2 (Y tau) (W tau)) +
      dRic (vec3 X (Y tau) (W tau)) -
      dRic (vec3 (Y tau) X (W tau)) -
      dRic (vec3 (W tau) X (Y tau)))

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem lIndexIntegrand_symm
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (gamma : Real → M)
    (Y W : ∀ tau, TangentSpace I (gamma tau)) (tau : Real) :
    lIndexIntegrand S T gamma Y W tau =
      lIndexIntegrand S T gamma W Y tau := by
  let t := T - tau
  let g := S.base.metric t
  let x := gamma tau
  let X := lVelocity (I := I) gamma tau
  let DY := lJacobiVelocity S T gamma Y tau
  let DW := lJacobiVelocity S T gamma W tau
  let dRic := totalNabla0SFun (𝕜 := Real) (I := I)
    2 (S.base.connection t) (S.ricci t) x
  have hinner : g.inner x DY DW = g.inner x DW DY :=
    g.symm x DY DW
  have hreal : rm04RealizesConnection (I := I) g
      (leviCivitaConnectionOfMetric (I := I) g) (S.base.rm04 t) := by
    change rm04RealizesConnection (I := I) g
      (leviCivitaConnectionOfMetric (I := I) g)
      (metricRm04 (I := I) (M := M) g)
    rw [show metricRm04 (I := I) (M := M) g =
      (metricCurvatureSections (I := I) (M := M) g).rm04 by rfl]
    exact (metricCurvatureSections (I := I) (M := M) g).rm04Realizes
  have hpair :=
    rm04PairSymmAt_of_leviCivita_realizes
      (I := I) g (S.base.rm04 t) hreal (x := x)
  have hinput :=
    rm04InputSkewAt_of_leviCivita_realizes
      (I := I) g (S.base.rm04 t) hreal (x := x)
  have houtput :=
    rm04OutputSkewAt_of_leviCivita_realizes
      (I := I) g (S.base.rm04 t) hreal (x := x)
  have hcurv :
      S.base.rm04 t x (vec4 (Y tau) X X (W tau)) =
        S.base.rm04 t x (vec4 (W tau) X X (Y tau)) := by
    linarith [hpair (Y tau) X X (W tau),
      hinput (W tau) X (Y tau) X,
      houtput (W tau) X (Y tau) X]
  have hhess :
      hessianSec (I := I) (S.base.connection t)
          (metricCov_smooth (I := I) g)
          (S.scalar t) (scalarSmoothOfSolution (I := I) S t) x
          (vec2 (Y tau) (W tau)) =
        hessianSec (I := I) (S.base.connection t)
          (metricCov_smooth (I := I) g)
          (S.scalar t) (scalarSmoothOfSolution (I := I) S t) x
          (vec2 (W tau) (Y tau)) := by
    simpa only [g, t, SolutionFamily.connection] using
      DifferentialGeometry.Geometry.Connection.hessSymm
        (I := I) (M := M) g (S.scalar t)
        (scalarSmoothOfSolution (I := I) S t) (Y tau) (W tau)
  have hdRic :
      dRic (vec3 X (Y tau) (W tau)) =
        dRic (vec3 X (W tau) (Y tau)) := by
    simpa only [dRic, g, t, x, SolutionFamily.connection,
      SolutionFamily.ricci, SolutionOn.ricci, metricCov] using
      DifferentialGeometry.Geometry.Curvature.metricNablaSymm
        (I := I) (M := M) g x X (Y tau) (W tau)
  simp only [lIndexIntegrand]
  rw [hinner, hcurv, hhess, hdRic]
  ring

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless]
  [SigmaCompactSpace M] in
theorem lIndexIntegrand_self
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (gamma : Real → M) (Y : ∀ tau, TangentSpace I (gamma tau))
    (tau : Real) :
    lIndexIntegrand S T gamma Y Y tau =
      let t := T - tau
      let g := S.base.metric t
      let cov := S.base.connection t
      let X := lVelocity (I := I) gamma tau
      let DY := lJacobiVelocity S T gamma Y tau
      let dRic := totalNabla0SFun (𝕜 := Real) (I := I)
        2 cov (S.ricci t) (gamma tau)
      Real.sqrt tau *
        (g.inner (gamma tau) DY DY -
          S.base.rm04 t (gamma tau) (vec4 (Y tau) X X (Y tau)) +
          (1 / 2 : Real) *
            hessianSec (I := I) cov (metricCov_smooth (I := I) g)
              (S.scalar t) (scalarSmoothOfSolution (I := I) S t) (gamma tau)
              (vec2 (Y tau) (Y tau)) +
          dRic (vec3 X (Y tau) (Y tau)) -
          2 * dRic (vec3 (Y tau) X (Y tau))) := by
  simp only [lIndexIntegrand]
  ring

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [SigmaCompactSpace M] in
theorem lIndex_balance
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (gamma : Real → M) (Y W : ∀ tau, TangentSpace I (gamma tau))
    (tau : Real) (hpos : 0 < tau) :
    2 * lIndexIntegrand S T gamma Y W tau +
        2 * (Real.sqrt tau * lJacobiPair S T gamma Y tau (W tau)) =
      (2 * Real.sqrt tau) *
          (((S.base.metric (T - tau)).inner (gamma tau)
              (covDerivAlong (I := I) (S.base.metric (T - tau)) gamma
                (lJacobiVelocity S T gamma Y) tau) (W tau) +
            (S.base.metric (T - tau)).inner (gamma tau)
              (lJacobiVelocity S T gamma Y tau)
              (lJacobiVelocity S T gamma W tau)) +
            2 * S.ricciAt (T - tau) (gamma tau)
              (vec2 (lJacobiVelocity S T gamma Y tau) (W tau))) +
        (1 / Real.sqrt tau) *
          (S.base.metric (T - tau)).inner (gamma tau)
            (lJacobiVelocity S T gamma Y tau) (W tau) := by
  have hsqrt_ne : Real.sqrt tau ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hpos)
  simp only [lIndexIntegrand, lJacobiPair, lJacobiVelocity]
  field_simp [hsqrt_ne, ne_of_gt hpos]
  rw [Real.sq_sqrt hpos.le]
  ring

noncomputable def lIndex
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (gamma : Real → M) (Y W : ∀ tau, TangentSpace I (gamma tau))
    (a b : Real) : Real :=
  ∫ tau in a..b, lIndexIntegrand S T gamma Y W tau

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem lIndex_symm
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (gamma : Real → M)
    (Y W : ∀ tau, TangentSpace I (gamma tau)) (a b : Real) :
    lIndex S T gamma Y W a b =
      lIndex S T gamma W Y a b := by
  apply intervalIntegral.integral_congr
  intro tau _
  exact lIndexIntegrand_symm (I := I) S T gamma Y W tau

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless]
  [SigmaCompactSpace M] in
@[simp] theorem lIndex_self
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (gamma : Real → M) (Y W : ∀ tau, TangentSpace I (gamma tau))
    (a : Real) :
    lIndex S T gamma Y W a a = 0 := by
  simp [lIndex]

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless]
  [SigmaCompactSpace M] in
theorem lIndex_add_adjacent
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (gamma : Real → M) (Y W : ∀ tau, TangentSpace I (gamma tau))
    (a b c : Real)
    (hab : IntervalIntegrable (lIndexIntegrand S T gamma Y W)
      MeasureTheory.volume a b)
    (hbc : IntervalIntegrable (lIndexIntegrand S T gamma Y W)
      MeasureTheory.volume b c) :
    lIndex S T gamma Y W a b + lIndex S T gamma Y W b c =
      lIndex S T gamma Y W a c := by
  simpa [lIndex] using intervalIntegral.integral_add_adjacent_intervals hab hbc

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
theorem lIndex_green
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (gamma : Real → M)
    (Y W : ∀ tau, TangentSpace I (gamma tau)) (a b : Real)
    (hpos : 0 < min a b)
    (ht : ∀ tau ∈ Set.uIcc a b, T - tau ∈ D.regular)
    (hgamma : ∀ tau ∈ Set.uIcc a b,
      MDifferentiableAt 𝓘(Real, Real) I gamma tau)
    (hDY : ∀ tau ∈ Set.uIcc a b,
      DifferentiableAt Real
        (chartRepAt (I := I) gamma (lJacobiVelocity S T gamma Y) tau) tau)
    (hW : ∀ tau ∈ Set.uIcc a b,
      DifferentiableAt Real (chartRepAt (I := I) gamma W tau) tau)
    (hPint : IntervalIntegrable
      (fun tau : Real ↦
        ((S.base.metric (T - tau)).inner (gamma tau)
            (covDerivAlong (I := I) (S.base.metric (T - tau)) gamma
              (lJacobiVelocity S T gamma Y) tau) (W tau) +
          (S.base.metric (T - tau)).inner (gamma tau)
            (lJacobiVelocity S T gamma Y tau)
            (lJacobiVelocity S T gamma W tau)) +
          2 * S.ricciAt (T - tau) (gamma tau)
            (vec2 (lJacobiVelocity S T gamma Y tau) (W tau)))
      MeasureTheory.volume a b)
    (hJint : IntervalIntegrable
      (fun tau : Real ↦ Real.sqrt tau * lJacobiPair S T gamma Y tau (W tau))
      MeasureTheory.volume a b)
    (hIint : IntervalIntegrable (lIndexIntegrand S T gamma Y W)
      MeasureTheory.volume a b) :
    lIndex S T gamma Y W a b =
      Real.sqrt b * (S.base.metric (T - b)).inner (gamma b)
          (lJacobiVelocity S T gamma Y b) (W b) -
        Real.sqrt a * (S.base.metric (T - a)).inner (gamma a)
          (lJacobiVelocity S T gamma Y a) (W a) -
        ∫ tau in a..b,
          Real.sqrt tau * lJacobiPair S T gamma Y tau (W tau) := by
  let DY : ∀ tau, TangentSpace I (gamma tau) := lJacobiVelocity S T gamma Y
  let U : Real → Real := fun tau ↦
    (S.base.metric (T - tau)).inner (gamma tau) (DY tau) (W tau)
  let P : Real → Real := fun tau ↦
    ((S.base.metric (T - tau)).inner (gamma tau)
        (covDerivAlong (I := I) (S.base.metric (T - tau)) gamma DY tau)
        (W tau) +
      (S.base.metric (T - tau)).inner (gamma tau) (DY tau)
        (lJacobiVelocity S T gamma W tau)) +
      2 * S.ricciAt (T - tau) (gamma tau) (vec2 (DY tau) (W tau))
  let Q : Real → Real := fun tau ↦ (1 / Real.sqrt tau) * U tau
  let J : Real → Real := fun tau ↦
    Real.sqrt tau * lJacobiPair S T gamma Y tau (W tau)
  let G : Real → Real := lIndexIntegrand S T gamma Y W
  let B : Real :=
    Real.sqrt b * U b - Real.sqrt a * U a
  have hP : IntervalIntegrable P MeasureTheory.volume a b := by
    simpa only [P, DY, lJacobiVelocity] using hPint
  have hPw : IntervalIntegrable
      (fun tau : Real ↦ (2 * Real.sqrt tau) * P tau)
      MeasureTheory.volume a b :=
    hP.continuousOn_mul (continuousOn_const.mul continuousOn_id.sqrt)
  have hUcont : ContinuousOn U (Set.uIcc a b) := by
    intro tau htau
    simpa only [U, DY] using
      (lInner_deriv S hS T gamma DY W tau (ht tau htau)
        (hgamma tau htau) (hDY tau htau) (hW tau htau)).continuousAt.continuousWithinAt
  have hInvcont : ContinuousOn (fun tau : Real ↦ 1 / Real.sqrt tau)
      (Set.uIcc a b) :=
    continuousOn_const.div continuousOn_id.sqrt (fun tau htau ↦
      ne_of_gt (Real.sqrt_pos.2 (lt_of_lt_of_le hpos htau.1)))
  have hQ : IntervalIntegrable Q MeasureTheory.volume a b := by
    exact (hInvcont.mul hUcont).intervalIntegrable
  have hG : IntervalIntegrable G MeasureTheory.volume a b := by
    simpa only [G] using hIint
  have hJ : IntervalIntegrable J MeasureTheory.volume a b := by
    simpa only [J] using hJint
  have hparts :
      (∫ tau in a..b, (2 * Real.sqrt tau) * P tau) =
        2 * B - ∫ tau in a..b, Q tau := by
    have hraw := lInner_parts S hS T gamma DY W a b hpos ht hgamma hDY hW hP
    simp only [P, Q, U, B, DY, lJacobiVelocity] at hraw ⊢
    linarith
  have hpoint : ∀ tau ∈ Set.uIcc a b,
      2 * G tau + 2 * J tau =
        (2 * Real.sqrt tau) * P tau + Q tau := by
    intro tau htau
    simpa only [G, J, P, Q, U, DY] using
      lIndex_balance (I := I) S T gamma Y W tau
        (lt_of_lt_of_le hpos htau.1)
  have hint :
      (∫ tau in a..b, (2 * G tau + 2 * J tau)) =
        ∫ tau in a..b, ((2 * Real.sqrt tau) * P tau + Q tau) :=
    intervalIntegral.integral_congr hpoint
  rw [intervalIntegral.integral_add (hG.const_mul 2) (hJ.const_mul 2),
    intervalIntegral.integral_add hPw hQ] at hint
  simp only [intervalIntegral.integral_const_mul] at hint
  rw [hparts] at hint
  unfold lIndex
  simpa only [G, J, B, U, DY] using (by linarith :
    (∫ tau in a..b, G tau) = B - ∫ tau in a..b, J tau)

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
theorem lIndex_eq_neg_integral_lJacobiPair_of_boundary_eq_zero
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (gamma : Real → M)
    (Y W : ∀ tau, TangentSpace I (gamma tau)) (a b : Real)
    (hpos : 0 < min a b)
    (ht : ∀ tau ∈ Set.uIcc a b, T - tau ∈ D.regular)
    (hgamma : ∀ tau ∈ Set.uIcc a b,
      MDifferentiableAt 𝓘(Real, Real) I gamma tau)
    (hDY : ∀ tau ∈ Set.uIcc a b,
      DifferentiableAt Real
        (chartRepAt (I := I) gamma (lJacobiVelocity S T gamma Y) tau) tau)
    (hW : ∀ tau ∈ Set.uIcc a b,
      DifferentiableAt Real (chartRepAt (I := I) gamma W tau) tau)
    (hPint : IntervalIntegrable
      (fun tau : Real ↦
        ((S.base.metric (T - tau)).inner (gamma tau)
            (covDerivAlong (I := I) (S.base.metric (T - tau)) gamma
              (lJacobiVelocity S T gamma Y) tau) (W tau) +
          (S.base.metric (T - tau)).inner (gamma tau)
            (lJacobiVelocity S T gamma Y tau)
            (lJacobiVelocity S T gamma W tau)) +
          2 * S.ricciAt (T - tau) (gamma tau)
            (vec2 (lJacobiVelocity S T gamma Y tau) (W tau)))
      MeasureTheory.volume a b)
    (hJint : IntervalIntegrable
      (fun tau : Real ↦ Real.sqrt tau * lJacobiPair S T gamma Y tau (W tau))
      MeasureTheory.volume a b)
    (hIint : IntervalIntegrable (lIndexIntegrand S T gamma Y W)
      MeasureTheory.volume a b)
    (hWa : W a = 0) (hWb : W b = 0) :
    lIndex S T gamma Y W a b =
      -∫ tau in a..b,
        Real.sqrt tau * lJacobiPair S T gamma Y tau (W tau) := by
  have hgreen := lIndex_green (I := I) S hS T gamma Y W a b hpos ht
    hgamma hDY hW hPint hJint hIint
  rw [hWa, hWb] at hgreen
  simpa only [map_zero, mul_zero, neg_zero, zero_sub] using hgreen

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
theorem lIndex_eq_boundary_of_isLJacobi
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (gamma : Real → M)
    (Y W : ∀ tau, TangentSpace I (gamma tau)) (a b : Real)
    (hpos : 0 < min a b)
    (ht : ∀ tau ∈ Set.uIcc a b, T - tau ∈ D.regular)
    (hjac : IsLJacobi S T gamma Y (Set.uIcc a b))
    (hW : ∀ tau ∈ Set.uIcc a b,
      DifferentiableAt Real (chartRepAt (I := I) gamma W tau) tau)
    (hPint : IntervalIntegrable
      (fun tau : Real ↦
        ((S.base.metric (T - tau)).inner (gamma tau)
            (covDerivAlong (I := I) (S.base.metric (T - tau)) gamma
              (lJacobiVelocity S T gamma Y) tau) (W tau) +
          (S.base.metric (T - tau)).inner (gamma tau)
            (lJacobiVelocity S T gamma Y tau)
            (lJacobiVelocity S T gamma W tau)) +
          2 * S.ricciAt (T - tau) (gamma tau)
            (vec2 (lJacobiVelocity S T gamma Y tau) (W tau)))
      MeasureTheory.volume a b)
    (hIint : IntervalIntegrable (lIndexIntegrand S T gamma Y W)
      MeasureTheory.volume a b) :
    lIndex S T gamma Y W a b =
      Real.sqrt b * (S.base.metric (T - b)).inner (gamma b)
          (lJacobiVelocity S T gamma Y b) (W b) -
        Real.sqrt a * (S.base.metric (T - a)).inner (gamma a)
          (lJacobiVelocity S T gamma Y a) (W a) := by
  have hJzero : ∀ tau ∈ Set.uIcc a b,
      Real.sqrt tau * lJacobiPair S T gamma Y tau (W tau) = 0 := by
    intro tau htau
    rw [(hjac tau htau).2.2.2 (W tau), mul_zero]
  have hJint : IntervalIntegrable
      (fun tau : Real ↦ Real.sqrt tau *
        lJacobiPair S T gamma Y tau (W tau))
      MeasureTheory.volume a b := by
    rw [intervalIntegrable_congr
      (f := fun tau : Real ↦ Real.sqrt tau *
        lJacobiPair S T gamma Y tau (W tau))
      (g := fun _ : Real ↦ (0 : Real)) (by
        intro tau htau
        exact hJzero tau (Set.uIoc_subset_uIcc htau))]
    exact intervalIntegrable_const
  have hgreen := lIndex_green (I := I) S hS T gamma Y W a b hpos ht
    (fun tau htau ↦ (hjac tau htau).1)
    (fun tau htau ↦ (hjac tau htau).2.2.1)
    hW hPint hJint hIint
  have hJintegral :
      (∫ tau in a..b,
        Real.sqrt tau * lJacobiPair S T gamma Y tau (W tau)) = 0 := by
    calc
      _ = ∫ _tau in a..b, (0 : Real) :=
        intervalIntegral.integral_congr hJzero
      _ = 0 := by simp
  rw [hJintegral] at hgreen
  simpa only [sub_zero] using hgreen

end normedSpaceCompatibility

end DifferentialGeometry.PDE.RicciFlow.Perelman
