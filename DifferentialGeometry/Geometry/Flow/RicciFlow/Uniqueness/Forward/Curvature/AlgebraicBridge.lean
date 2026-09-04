import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.Curvature.TimeDerivative

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

section Raise

variable {Idx : Type*} [Fintype Idx] {x : M}

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private theorem metField0 (g : SmoothRiemannianMetric I M) (x : M)
    (u Z : TangentSpace I x) :
    metricTensorField (I := I) g x (fun i : Fin 2 => if i = 0 then u else Z) =
      g.inner x u Z := by
  rw [metricTensorField_apply]; simp

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private theorem inner_expand (g : SmoothRiemannianMetric I M)
    (basis : Module.Basis Idx Real (TangentSpace I x)) (W Z : TangentSpace I x) :
    g.inner x W Z = ∑ p : Idx, basis.repr W p * g.inner x (basis p) Z := by
  classical
  rw [← metField0 (I := I) g x W Z,
    tensor02_expand (I := I) (metricTensorField (I := I) g x) basis W Z]
  exact Finset.sum_congr rfl fun p _ => by rw [metField0]

def raiseAt (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x)) (a : Idx -> Real) :
    TangentSpace I x :=
  ∑ p : Idx, (∑ l : Idx, basisInvMetric (I := I) g x basis p l * a l) • basis p

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem raiseAt_eq (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x)) (a : Idx -> Real) :
    raiseAt (I := I) g x basis a =
      ∑ p : Idx, (∑ l : Idx, basisInvMetric (I := I) g x basis p l * a l) • basis p := rfl

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem raiseAt_lower (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x)) (V : TangentSpace I x) :
    raiseAt (I := I) g x basis (fun l : Idx => g.inner x V (basis l)) = V := by
  classical
  have hcoord : ∀ p : Idx,
      (∑ l : Idx, basisInvMetric (I := I) g x basis p l * g.inner x V (basis l)) =
        basis.repr V p := by
    intro p
    set S : TangentSpace I x :=
      (tangentFlatEquivGen (I := I) g x).symm (basis.coord p) with hS
    have hb : ∀ l : Idx, basisInvMetric (I := I) g x basis p l = basis.repr S l := by
      intro l
      rw [hS]
      exact basis.coord_apply l _
    have hsum : (∑ l : Idx, basis.repr S l * g.inner x V (basis l)) = g.inner x V S := by
      conv_rhs => rw [← basis.sum_repr S]
      rw [map_sum]
      exact Finset.sum_congr rfl fun l _ => by rw [map_smul, smul_eq_mul]
    have hflat : g.inner x V S = basis.repr V p := by
      have h1 : g.inner x V S = g.inner x S V := g.symm x V S
      have h2 : g.inner x S V = tangentFlatEquivGen (I := I) g x S V :=
        (tangentFlatEquiv_apply_gen (I := I) g x S V).symm
      have h3 : tangentFlatEquivGen (I := I) g x S = basis.coord p := by
        rw [hS]
        exact (tangentFlatEquivGen (I := I) g x).apply_symm_apply _
      rw [h1, h2, h3]
      exact basis.coord_apply p V
    calc (∑ l : Idx, basisInvMetric (I := I) g x basis p l * g.inner x V (basis l))
        = ∑ l : Idx, basis.repr S l * g.inner x V (basis l) :=
          Finset.sum_congr rfl fun l _ => by rw [hb l]
      _ = g.inner x V S := hsum
      _ = basis.repr V p := hflat
  rw [raiseAt_eq]
  calc (∑ p : Idx,
        (∑ l : Idx, basisInvMetric (I := I) g x basis p l * g.inner x V (basis l)) • basis p)
      = ∑ p : Idx, basis.repr V p • basis p :=
        Finset.sum_congr rfl fun p _ => by rw [hcoord p]
    _ = V := basis.sum_repr V

private theorem mulVanish_deriv {f A : Real -> Real} {A' : Real} {s : Set Real} {t : Real}
    (hf : ContinuousWithinAt f s t) (hA : HasDerivWithinAt A A' s t) (hA0 : A t = 0) :
    HasDerivWithinAt (fun r : Real => f r * A r) (f t * A') s t := by
  rw [hasDerivWithinAt_iff_tendsto_slope] at hA ⊢
  have hslope : ∀ r : Real,
      slope (fun y : Real => f y * A y) t r = f r * slope A t r := by
    intro r
    simp only [slope_def_field, hA0]
    ring
  refine Filter.Tendsto.congr (fun r => (hslope r).symm) ?_
  exact Filter.Tendsto.mul (hf.mono Set.sdiff_subset) hA

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem vecCurve_deriv
    (g : Real -> SmoothRiemannianMetric I M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (V : Real -> TangentSpace I x) (a : Idx -> Real)
    (Ric : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    {s : Set Real} {t : Real}
    (hcont : ContinuousWithinAt V s t)
    (hPDE : ∀ X Y : TangentSpace I x,
      HasDerivWithinAt (fun r : Real => (g r).inner x X Y)
        ((-2 : Real) * Ric (fun i : Fin 2 => if i = 0 then X else Y)) s t)
    (hlow : ∀ l : Idx,
      HasDerivWithinAt (fun r : Real => (g r).inner x (V r) (basis l)) (a l) s t) :
    HasDerivWithinAt V
      (raiseAt (I := I) (g t) x basis
        (fun l : Idx => a l +
          2 * Ric (fun i : Fin 2 => if i = 0 then V t else basis l))) s t := by
  classical
  have hc : ∀ p : Idx, ContinuousWithinAt (fun r : Real => basis.repr (V r) p) s t := by
    intro p
    have h := (LinearMap.toContinuousLinearMap
      (basis.coord p)).continuous.continuousAt.comp_continuousWithinAt hcont
    simpa [Function.comp_def, Module.Basis.coord_apply] using h
  have hfroz : ∀ l : Idx,
      HasDerivWithinAt (fun r : Real => (g t).inner x (V r) (basis l))
        (a l + 2 * Ric (fun i : Fin 2 => if i = 0 then V t else basis l)) s t := by
    intro l
    have hsplit : ∀ r : Real,
        (g t).inner x (V r) (basis l) =
          (g r).inner x (V r) (basis l) +
            ∑ p : Idx, basis.repr (V r) p *
              ((g t).inner x (basis p) (basis l) - (g r).inner x (basis p) (basis l)) := by
      intro r
      have hd : (∑ p : Idx, basis.repr (V r) p *
            ((g t).inner x (basis p) (basis l) - (g r).inner x (basis p) (basis l))) =
          (g t).inner x (V r) (basis l) - (g r).inner x (V r) (basis l) := by
        rw [inner_expand (I := I) (g t) basis (V r) (basis l),
          inner_expand (I := I) (g r) basis (V r) (basis l), ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun p _ => by ring
      rw [hd]; ring
    have hterm : ∀ p : Idx, HasDerivWithinAt
        (fun r : Real => basis.repr (V r) p *
          ((g t).inner x (basis p) (basis l) - (g r).inner x (basis p) (basis l)))
        (basis.repr (V t) p *
          (2 * Ric (fun i : Fin 2 => if i = 0 then basis p else basis l))) s t := by
      intro p
      refine mulVanish_deriv (hc p) ?_ (sub_self _)
      have hsub := (hasDerivWithinAt_const t s
        ((g t).inner x (basis p) (basis l))).sub (hPDE (basis p) (basis l))
      exact hsub.congr_deriv (by ring)
    have hsum : HasDerivWithinAt
        (fun r : Real => ∑ p : Idx, basis.repr (V r) p *
          ((g t).inner x (basis p) (basis l) - (g r).inner x (basis p) (basis l)))
        (∑ p : Idx, basis.repr (V t) p *
          (2 * Ric (fun i : Fin 2 => if i = 0 then basis p else basis l))) s t :=
      HasDerivWithinAt.fun_sum fun p _ => hterm p
    have hval : (∑ p : Idx, basis.repr (V t) p *
          (2 * Ric (fun i : Fin 2 => if i = 0 then basis p else basis l))) =
        2 * Ric (fun i : Fin 2 => if i = 0 then V t else basis l) := by
      rw [tensor02_expand (I := I) Ric basis (V t) (basis l), Finset.mul_sum]
      exact Finset.sum_congr rfl fun p _ => by ring
    have hfun : (fun r : Real => (g t).inner x (V r) (basis l)) =
        (fun r : Real => (g r).inner x (V r) (basis l) +
          ∑ p : Idx, basis.repr (V r) p *
            ((g t).inner x (basis p) (basis l) - (g r).inner x (basis p) (basis l))) :=
      funext hsplit
    rw [hfun, ← hval]
    exact (hlow l).add hsum
  have hV : ∀ r : Real,
      V r = ∑ p : Idx, (∑ l : Idx, basisInvMetric (I := I) (g t) x basis p l *
        ((g t).inner x (V r) (basis l))) • basis p := by
    intro r
    have h := raiseAt_lower (I := I) (g t) x basis (V r)
    rw [raiseAt_eq] at h
    exact h.symm
  have hderiv : HasDerivWithinAt
      (fun r : Real => ∑ p : Idx, (∑ l : Idx, basisInvMetric (I := I) (g t) x basis p l *
          ((g t).inner x (V r) (basis l))) • basis p)
      (∑ p : Idx, (∑ l : Idx, basisInvMetric (I := I) (g t) x basis p l *
          (a l + 2 * Ric (fun i : Fin 2 => if i = 0 then V t else basis l))) • basis p) s t :=
    HasDerivWithinAt.fun_sum fun p _ =>
      (HasDerivWithinAt.fun_sum fun l _ => (hfroz l).const_mul _).smul_const (basis p)
  rw [raiseAt_eq]
  exact hderiv.congr (fun y _ => hV y) (hV t)

end Raise

section Curvature

variable {Idx : Type*} [Fintype Idx] {x : M}

omit [SigmaCompactSpace M] in
theorem metricRm04At_inner (g : SmoothRiemannianMetric I M) (x : M)
    (X Y Z W : TangentSpace I x) :
    metricRm04At (I := I) g x
        (DifferentialGeometry.Geometry.Curvature.vec4 (I := I) X Y Z W) =
      g.inner x
        (DifferentialGeometry.Geometry.Curvature.riemannOp (metricCov (I := I) g) x X Y Z)
        W := by
  have h :=
    DifferentialGeometry.Geometry.Curvature.CovariantDerivative.riemannCurvature04At_apply_const
      (I := I) g (metricCov (I := I) g) (metricCov_smooth (I := I) g) X Y Z W
  rw [DifferentialGeometry.riemannCurvatureAux_tangentConst_eq_riemannOp
    (I := I) (metricCov (I := I) g) (metricCov_smooth (I := I) g) x X Y Z] at h
  rw [show metricRm04At (I := I) g x =
      DifferentialGeometry.Geometry.Curvature.CovariantDerivative.riemannCurvature04At
        (I := I) g (metricCov (I := I) g) (metricCov_smooth (I := I) g) x from rfl, h]
  exact g.symm x W _

omit [SigmaCompactSpace M] in
theorem rmVec_deriv
    (g : Real -> SmoothRiemannianMetric I M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (X Y Z : TangentSpace I x) (rhs : Idx -> Real)
    (Ric : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    {s : Set Real} {t : Real}
    (hcont : ContinuousWithinAt
      (fun r : Real =>
        DifferentialGeometry.Geometry.Curvature.riemannOp (metricCov (I := I) (g r)) x X Y Z)
      s t)
    (hPDE : ∀ U W : TangentSpace I x,
      HasDerivWithinAt (fun r : Real => (g r).inner x U W)
        ((-2 : Real) * Ric (fun i : Fin 2 => if i = 0 then U else W)) s t)
    (hev : ∀ l : Idx,
      HasDerivWithinAt
        (fun r : Real => metricRm04At (I := I) (g r) x
          (DifferentialGeometry.Geometry.Curvature.vec4 (I := I) X Y Z (basis l)))
        (rhs l) s t) :
    HasDerivWithinAt
      (fun r : Real =>
        DifferentialGeometry.Geometry.Curvature.riemannOp (metricCov (I := I) (g r)) x X Y Z)
      (raiseAt (I := I) (g t) x basis
        (fun l : Idx => rhs l +
          2 * Ric (fun i : Fin 2 => if i = 0 then
            DifferentialGeometry.Geometry.Curvature.riemannOp
              (metricCov (I := I) (g t)) x X Y Z
            else basis l))) s t := by
  refine vecCurve_deriv (I := I) g basis _ rhs Ric hcont hPDE ?_
  intro l
  have h := hev l
  simpa only [metricRm04At_inner (I := I)] using h

omit [SigmaCompactSpace M] in
theorem rmVecComp_deriv
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (g : Real -> SmoothRiemannianMetric I M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (Rm04 roughLapRm04 B : FourComp M Idx) (ricciOneUp : MatrixComp M Idx)
    (Ric : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (hev : Riemann04BTensorWithRicciDriftEvolutionInFrameOn (D := D)
      Rm04 roughLapRm04 B ricciOneUp)
    (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
    (i j k : Idx)
    (hcont : ContinuousWithinAt
      (fun r : Real =>
        DifferentialGeometry.Geometry.Curvature.riemannOp (metricCov (I := I) (g r)) x
          (basis i) (basis j) (basis k))
      D.carrier (t : Real))
    (hPDE : ∀ U W : TangentSpace I x,
      HasDerivWithinAt (fun r : Real => (g r).inner x U W)
        ((-2 : Real) * Ric (fun q : Fin 2 => if q = 0 then U else W))
        D.carrier (t : Real))
    (hreal : ∀ (r : Real) (l : Idx),
      Rm04 r x i j k l =
        metricRm04At (I := I) (g r) x
          (DifferentialGeometry.Geometry.Curvature.vec4 (I := I)
            (basis i) (basis j) (basis k) (basis l))) :
    HasDerivWithinAt
      (fun r : Real =>
        DifferentialGeometry.Geometry.Curvature.riemannOp (metricCov (I := I) (g r)) x
          (basis i) (basis j) (basis k))
      (raiseAt (I := I) (g (t : Real)) x basis
        (fun l : Idx =>
          (roughLapRm04 (t : Real) x i j k l -
              2 * (B (t : Real) x i j k l - B (t : Real) x i j l k +
                B (t : Real) x i k j l - B (t : Real) x i l j k) -
              riemann04RicciDriftInFrame ricciOneUp Rm04 (t : Real) x i j k l) +
            2 * Ric (fun q : Fin 2 => if q = 0 then
              DifferentialGeometry.Geometry.Curvature.riemannOp
                (metricCov (I := I) (g (t : Real))) x (basis i) (basis j) (basis k)
              else basis l)))
      D.carrier (t : Real) := by
  refine rmVec_deriv (I := I) g basis (basis i) (basis j) (basis k) _ Ric hcont hPDE ?_
  intro l
  have h := hev t x i j k l
  have hfun : (fun r : Real => Rm04 r x i j k l) =
      (fun r : Real => metricRm04At (I := I) (g r) x
        (DifferentialGeometry.Geometry.Curvature.vec4 (I := I)
          (basis i) (basis j) (basis k) (basis l))) :=
    funext fun r => hreal r l
  rw [hfun] at h
  exact h

omit [SigmaCompactSpace M] in
theorem rmDiffVec_deriv
    (g₁ g₂ : Real -> SmoothRiemannianMetric I M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (X Y Z : TangentSpace I x) (rhs₁ rhs₂ : Idx -> Real)
    (Ric₁ Ric₂ : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    {s : Set Real} {t : Real}
    (hcont₁ : ContinuousWithinAt
      (fun r : Real =>
        DifferentialGeometry.Geometry.Curvature.riemannOp (metricCov (I := I) (g₁ r)) x X Y Z)
      s t)
    (hcont₂ : ContinuousWithinAt
      (fun r : Real =>
        DifferentialGeometry.Geometry.Curvature.riemannOp (metricCov (I := I) (g₂ r)) x X Y Z)
      s t)
    (hPDE₁ : ∀ U W : TangentSpace I x,
      HasDerivWithinAt (fun r : Real => (g₁ r).inner x U W)
        ((-2 : Real) * Ric₁ (fun q : Fin 2 => if q = 0 then U else W)) s t)
    (hPDE₂ : ∀ U W : TangentSpace I x,
      HasDerivWithinAt (fun r : Real => (g₂ r).inner x U W)
        ((-2 : Real) * Ric₂ (fun q : Fin 2 => if q = 0 then U else W)) s t)
    (hev₁ : ∀ l : Idx,
      HasDerivWithinAt
        (fun r : Real => metricRm04At (I := I) (g₁ r) x
          (DifferentialGeometry.Geometry.Curvature.vec4 (I := I) X Y Z (basis l)))
        (rhs₁ l) s t)
    (hev₂ : ∀ l : Idx,
      HasDerivWithinAt
        (fun r : Real => metricRm04At (I := I) (g₂ r) x
          (DifferentialGeometry.Geometry.Curvature.vec4 (I := I) X Y Z (basis l)))
        (rhs₂ l) s t) :
    HasDerivWithinAt (fun r : Real => rmDiffVec (I := I) (g₁ r) (g₂ r) x X Y Z)
      (raiseAt (I := I) (g₁ t) x basis
          (fun l : Idx => rhs₁ l +
            2 * Ric₁ (fun q : Fin 2 => if q = 0 then
              DifferentialGeometry.Geometry.Curvature.riemannOp
                (metricCov (I := I) (g₁ t)) x X Y Z
              else basis l)) -
        raiseAt (I := I) (g₂ t) x basis
          (fun l : Idx => rhs₂ l +
            2 * Ric₂ (fun q : Fin 2 => if q = 0 then
              DifferentialGeometry.Geometry.Curvature.riemannOp
                (metricCov (I := I) (g₂ t)) x X Y Z
              else basis l))) s t := by
  have hfun : (fun r : Real => rmDiffVec (I := I) (g₁ r) (g₂ r) x X Y Z) =
      (fun r : Real =>
        DifferentialGeometry.Geometry.Curvature.riemannOp
            (metricCov (I := I) (g₁ r)) x X Y Z -
          DifferentialGeometry.Geometry.Curvature.riemannOp
            (metricCov (I := I) (g₂ r)) x X Y Z) := rfl
  rw [hfun]
  exact (rmVec_deriv (I := I) g₁ basis X Y Z rhs₁ Ric₁ hcont₁ hPDE₁ hev₁).sub
    (rmVec_deriv (I := I) g₂ basis X Y Z rhs₂ Ric₂ hcont₂ hPDE₂ hev₂)

end Curvature

section Parallel

omit [SigmaCompactSpace M] [BoundarylessManifold I M] in
theorem metricNabla0S_self (g : SmoothRiemannianMetric I M) :
    metricNabla0S (I := I) g (metricTensorField (I := I) g) =
      (0 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) 3) := by
  classical
  have hmc : DifferentialGeometry.Geometry.Connection.IsMetricCompatibleGen
      (I := I) (metricCov (I := I) g) g :=
    DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric_isMetricCompatible
      (I := I) g
  refine DFunLike.ext _ _ fun x => ?_
  have hfib : metricNabla0S (I := I) g (metricTensorField (I := I) g) x = 0 := by
    refine ContinuousMultilinearMap.ext fun v => ?_
    obtain ⟨Xsec, hXx⟩ :=
      ContMDiffSection.exists_eq_at
        (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x (v 0)
    have hv : Fin.cons (Xsec x) (Fin.tail v) = v := by
      rw [hXx]
      exact Fin.cons_self_tail v
    have hsec := totalNabla0SFun_apply_section (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 2 (metricCov (I := I) g) Xsec (metricTensorField (I := I) g) x
      (Fin.tail v)
    rw [hv] at hsec
    have hzero := nabla_metric_zero (I := I) (metricCov (I := I) g) g hmc Xsec x
    rw [metricNabla0S_apply]
    exact hsec.trans (by
      rw [hzero]
      rfl)
  rw [hfib]
  rfl

omit [SigmaCompactSpace M] [BoundarylessManifold I M] in
theorem nabla2_metric1 (g₁ g₂ : SmoothRiemannianMetric I M) :
    metricNabla0S (I := I) g₂ (metricTensorField (I := I) g₁) =
      -lapDiffFlux (I := I) g₁ g₂ (metricTensorField (I := I) g₁) := by
  rw [lapDiffFlux, metricNabla0S_self]
  abel

end Parallel

section ReLower

variable {x : M}

def sharpFlat (g₁ g₂ : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x →ₗ[Real] TangentSpace I x :=
  (tangentFlatEquivGen (I := I) g₂ x).symm.toLinearMap ∘ₗ
    (tangentFlatEquivGen (I := I) g₁ x).toLinearMap

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
@[simp]
theorem sharpFlat_self (g : SmoothRiemannianMetric I M) (x : M) (W : TangentSpace I x) :
    sharpFlat (I := I) g g x W = W := by
  change (tangentFlatEquivGen (I := I) g x).symm
    ((tangentFlatEquivGen (I := I) g x) W) = W
  exact (tangentFlatEquivGen (I := I) g x).symm_apply_apply W

omit [SigmaCompactSpace M] in
theorem mixLow_eq_rm04 (g₁ g₂ : SmoothRiemannianMetric I M) (x : M)
    (X Y Z W : TangentSpace I x) :
    metricRm04At (I := I) g₂ x
        (DifferentialGeometry.Geometry.Curvature.vec4 (I := I) X Y Z
          (sharpFlat (I := I) g₁ g₂ x W)) =
      g₁.inner x
        (DifferentialGeometry.Geometry.Curvature.riemannOp (metricCov (I := I) g₂) x X Y Z)
        W := by
  set V : TangentSpace I x :=
    DifferentialGeometry.Geometry.Curvature.riemannOp (metricCov (I := I) g₂) x X Y Z with hV
  set S : TangentSpace I x := sharpFlat (I := I) g₁ g₂ x W with hSdef
  have hflat : tangentFlatEquivGen (I := I) g₂ x S = tangentFlatEquivGen (I := I) g₁ x W := by
    rw [hSdef]
    change tangentFlatEquivGen (I := I) g₂ x
      ((tangentFlatEquivGen (I := I) g₂ x).symm
        ((tangentFlatEquivGen (I := I) g₁ x) W)) = _
    exact (tangentFlatEquivGen (I := I) g₂ x).apply_symm_apply _
  calc metricRm04At (I := I) g₂ x
        (DifferentialGeometry.Geometry.Curvature.vec4 (I := I) X Y Z S)
      = g₂.inner x V S := metricRm04At_inner (I := I) g₂ x X Y Z S
    _ = g₂.inner x S V := g₂.symm x V S
    _ = tangentFlatEquivGen (I := I) g₂ x S V :=
        (tangentFlatEquiv_apply_gen (I := I) g₂ x S V).symm
    _ = tangentFlatEquivGen (I := I) g₁ x W V := by rw [hflat]
    _ = g₁.inner x W V := tangentFlatEquiv_apply_gen (I := I) g₁ x W V
    _ = g₁.inner x V W := g₁.symm x W V

end ReLower

section Commutator

variable {s : ℕ}

def lapCommFlux (g : SmoothRiemannianMetric I M)
    (L : ∀ k : ℕ, Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) k ->
      Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) k)
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1) :=
  metricNabla0S (I := I) g (L s T) - L (s + 1) (metricNabla0S (I := I) g T)

def lapCommRem (g : SmoothRiemannianMetric I M)
    (L : ∀ k : ℕ, Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) k ->
      Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) k)
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s :=
  covDiv0SField (I := I) g (L (s + 1) (metricNabla0S (I := I) g T)) -
    L s (covDiv0SField (I := I) g (metricNabla0S (I := I) g T))

omit [SigmaCompactSpace M] [BoundarylessManifold I M] in
theorem lapComm_eq_div_flux (g : SmoothRiemannianMetric I M)
    (L : ∀ k : ℕ, Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) k ->
      Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) k)
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) :
    roughLap0SField (I := I) g (L s T) - L s (roughLap0SField (I := I) g T) =
      covDiv0SField (I := I) g (lapCommFlux (I := I) g L T) +
        lapCommRem (I := I) g L T := by
  rw [lapCommFlux, covDiv0SField_sub, lapCommRem, roughLap0SField, roughLap0SField]
  abel

omit [SigmaCompactSpace M] [BoundarylessManifold I M] in
theorem lapComm_self (g : SmoothRiemannianMetric I M)
    (L : ∀ k : ℕ, Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) k ->
      Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) k)
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (hflux : lapCommFlux (I := I) g L T = 0) (hrem : lapCommRem (I := I) g L T = 0) :
    roughLap0SField (I := I) g (L s T) = L s (roughLap0SField (I := I) g T) := by
  have h := lapComm_eq_div_flux (I := I) g L T
  rw [hflux, hrem, add_zero] at h
  have hz : covDiv0SField (I := I) g
      (0 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) (s + 1)) = 0 := by
    have := covDiv0SField_sub (I := I) g
      (0 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) (s + 1)) 0
    simpa using this
  rw [hz] at h
  exact sub_eq_zero.mp h

end Commutator

end DifferentialGeometry.PDE.RicciFlow

end
