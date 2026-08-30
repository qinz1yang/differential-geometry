import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Variation.Second

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Filter Set
open scoped Manifold ContDiff Topology

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Tensor0SBundle
open MeasureTheory

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {D : RealTimeInterval}

noncomputable def lRegIndexInt
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (alpha : Real → M)
    (Y W : ∀ s, TangentSpace I (alpha s)) (s : Real) : Real :=
  let t := T - s ^ 2
  let g := S.base.metric t
  let cov := S.base.connection t
  let A := lVelocity (I := I) alpha s
  let DY := covDerivAlong (I := I) g alpha Y s
  let DW := covDerivAlong (I := I) g alpha W s
  let dRic := totalNabla0SFun (𝕜 := Real) (I := I)
    2 cov (S.ricci t) (alpha s)
  (1 / 2 : Real) *
      (g.inner (alpha s) DY DW -
        S.base.rm04 t (alpha s) (vec4 (Y s) A A (W s))) +
    s ^ 2 *
      hessianSec (I := I) cov (metricCov_smooth (I := I) g)
        (S.scalar t) (scalarSmoothOfSol (I := I) S t) (alpha s)
        (vec2 (Y s) (W s)) +
    s * (dRic (vec3 A (Y s) (W s)) -
      dRic (vec3 (Y s) A (W s)) -
      dRic (vec3 (W s) A (Y s)))

omit [NeZero (Module.finrank Real E)] [I.Boundaryless]
  [SigmaCompactSpace M] in
theorem lRegIndexInt_symm
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (alpha : Real → M)
    (Y W : ∀ s, TangentSpace I (alpha s)) (s : Real) :
    lRegIndexInt S T alpha Y W s =
      lRegIndexInt S T alpha W Y s := by
  let t := T - s ^ 2
  let g := S.base.metric t
  let x := alpha s
  let A := lVelocity (I := I) alpha s
  let DY := covDerivAlong (I := I) g alpha Y s
  let DW := covDerivAlong (I := I) g alpha W s
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
      (metricCurvData (I := I) (M := M) g).rm04 by rfl]
    exact (metricCurvData (I := I) (M := M) g).rm04Realizes
  have hpair := rm04PairSymmAt_of_leviCivita_realizes
    (I := I) g (S.base.rm04 t) hreal (x := x)
  have hinput := rm04InputSkewAt_of_leviCivita_realizes
    (I := I) g (S.base.rm04 t) hreal (x := x)
  have houtput := rm04OutputSkewAt_of_leviCivita_realizes
    (I := I) g (S.base.rm04 t) hreal (x := x)
  have hcurv :
      S.base.rm04 t x (vec4 (Y s) A A (W s)) =
        S.base.rm04 t x (vec4 (W s) A A (Y s)) := by
    linarith [hpair (Y s) A A (W s),
      hinput (W s) A (Y s) A, houtput (W s) A (Y s) A]
  have hhess :
      hessianSec (I := I) (S.base.connection t)
          (metricCov_smooth (I := I) g)
          (S.scalar t) (scalarSmoothOfSol (I := I) S t) x
          (vec2 (Y s) (W s)) =
        hessianSec (I := I) (S.base.connection t)
          (metricCov_smooth (I := I) g)
          (S.scalar t) (scalarSmoothOfSol (I := I) S t) x
          (vec2 (W s) (Y s)) := by
    simpa only [g, t, SolutionFamily.connection] using
      DifferentialGeometry.Geometry.Connection.hessSymm
        (I := I) (M := M) g (S.scalar t)
        (scalarSmoothOfSol (I := I) S t) (Y s) (W s)
  have hdRic :
      dRic (vec3 A (Y s) (W s)) =
        dRic (vec3 A (W s) (Y s)) := by
    simpa only [dRic, g, t, x, SolutionFamily.connection,
      SolutionFamily.ricci, SolutionOn.ricci, metricCov] using
      DifferentialGeometry.Geometry.Curvature.metricNablaSymm
        (I := I) (M := M) g x A (Y s) (W s)
  simp only [lRegIndexInt]
  rw [hinner, hcurv, hhess, hdRic]
  ring

noncomputable def lRegIndex
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (alpha : Real → M) (Y W : ∀ s, TangentSpace I (alpha s))
    (a b : Real) : Real :=
  ∫ s in a..b, lRegIndexInt S T alpha Y W s

omit [NeZero (Module.finrank Real E)] [I.Boundaryless]
  [SigmaCompactSpace M] in
theorem lRegIndex_symm
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (alpha : Real → M) (Y W : ∀ s, TangentSpace I (alpha s))
    (a b : Real) :
    lRegIndex S T alpha Y W a b = lRegIndex S T alpha W Y a b := by
  apply intervalIntegral.integral_congr
  intro s _
  exact lRegIndexInt_symm (I := I) S T alpha Y W s

omit [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [SigmaCompactSpace M] in
theorem lRegIndex_congr
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (alpha : Real → M)
    (Y₁ W₁ Y₂ W₂ : ∀ s, TangentSpace I (alpha s))
    (a b : Real)
    (hY : Set.EqOn Y₁ Y₂ (Set.uIoo a b))
    (hW : Set.EqOn W₁ W₂ (Set.uIoo a b)) :
    lRegIndex S T alpha Y₁ W₁ a b =
      lRegIndex S T alpha Y₂ W₂ a b := by
  unfold lRegIndex
  apply intervalIntegral.integral_congr_ae
  filter_upwards
    [MeasureTheory.Measure.ae_ne MeasureTheory.volume (max a b)]
      with s hsmax hs
  change s ∈ Set.Ioc (min a b) (max a b) at hs
  have hsIoo : s ∈ Set.Ioo (min a b) (max a b) :=
    ⟨hs.1, lt_of_le_of_ne hs.2 hsmax⟩
  have hYev : ∀ᶠ r in 𝓝 s, Y₁ r = Y₂ r := by
    filter_upwards [Ioo_mem_nhds hsIoo.1 hsIoo.2] with r hr
    exact hY (by simpa only [Set.uIoo] using hr)
  have hWev : ∀ᶠ r in 𝓝 s, W₁ r = W₂ r := by
    filter_upwards [Ioo_mem_nhds hsIoo.1 hsIoo.2] with r hr
    exact hW (by simpa only [Set.uIoo] using hr)
  have hYval : Y₁ s = Y₂ s := hYev.self_of_nhds
  have hWval : W₁ s = W₂ s := hWev.self_of_nhds
  have hYcov :=
    DifferentialGeometry.Geometry.Riemannian.Variation.covDerivAlong_congr_of_eventuallyEq
      (I := I)
      (S.base.metric (T - s ^ 2)) alpha hYev
  have hWcov :=
    DifferentialGeometry.Geometry.Riemannian.Variation.covDerivAlong_congr_of_eventuallyEq
      (I := I)
      (S.base.metric (T - s ^ 2)) alpha hWev
  simp only [lRegIndexInt, hYval, hWval, hYcov, hWcov]

omit [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M] in
private theorem tensor_slot_smul
    {n : Nat} {x : M} (L : Tensor0SSpace n I x)
    (v : Fin n → TangentSpace I x) (i : Fin n)
    (c : Real) (z : TangentSpace I x) :
    L (Function.update v i (c • z)) =
      c * L (Function.update v i z) := by
  simpa only [smul_eq_mul] using L.map_update_smul v i c z

omit [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [SigmaCompactSpace M] in
theorem lRegIndexInt_sq
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (gamma : Real → M)
    (Y W : ∀ tau, TangentSpace I (gamma tau))
    (s : Real) (hs : 0 < s)
    (hgamma : MDifferentiableAt 𝓘(Real, Real) I gamma (s ^ 2))
    (hY : DifferentiableAt Real
      (chartRepAt (I := I) gamma Y (s ^ 2)) (s ^ 2))
    (hW : DifferentiableAt Real
      (chartRepAt (I := I) gamma W (s ^ 2)) (s ^ 2)) :
    lIndexInt S T gamma Y W (s ^ 2) * (2 * s) =
      lRegIndexInt S T (sqReparam gamma)
        (fun r ↦ Y (r ^ 2)) (fun r ↦ W (r ^ 2)) s := by
  classical
  let tau : Real := s ^ 2
  let alpha : Real → M := sqReparam gamma
  let Yb : ∀ r, TangentSpace I (alpha r) := fun r ↦ Y (r ^ 2)
  let Wb : ∀ r, TangentSpace I (alpha r) := fun r ↦ W (r ^ 2)
  let q := S.base.metric (T - tau)
  let X := lVelocity (I := I) gamma tau
  let DY := covDerivAlong (I := I) q gamma Y tau
  let DW := covDerivAlong (I := I) q gamma W tau
  let N := totalNabla0SFun (𝕜 := Real) (I := I)
    2 (S.base.connection (T - tau)) (S.ricci (T - tau)) (gamma tau)
  let Rm := S.base.rm04 (T - tau) (gamma tau)
  let c : Real := 2 * s
  let Inn : Real := q.inner (gamma tau) DY DW
  let R : Real := Rm (vec4 (Y tau) X X (W tau))
  let Hess : Real :=
    hessianSec (I := I) (S.base.connection (T - tau))
      (metricCov_smooth (I := I) q) (S.scalar (T - tau))
      (scalarSmoothOfSol (I := I) S (T - tau)) (gamma tau)
      (vec2 (Y tau) (W tau))
  let N0 : Real := N (vec3 X (Y tau) (W tau))
  let N1 : Real := N (vec3 (Y tau) X (W tau))
  let N2 : Real := N (vec3 (W tau) X (Y tau))
  let InnReg : Real := q.inner (gamma tau)
    (covDerivAlong (I := I) q alpha Yb s)
    (covDerivAlong (I := I) q alpha Wb s)
  let Rreg : Real := Rm
    (vec4 (Y tau) (lVelocity (I := I) alpha s)
      (lVelocity (I := I) alpha s) (W tau))
  let Nreg0 : Real := N
    (vec3 (lVelocity (I := I) alpha s) (Y tau) (W tau))
  let Nreg1 : Real := N
    (vec3 (Y tau) (lVelocity (I := I) alpha s) (W tau))
  let Nreg2 : Real := N
    (vec3 (W tau) (lVelocity (I := I) alpha s) (Y tau))
  have hAs : lVelocity (I := I) alpha s = c • X := by
    simpa only [alpha, c, X, tau] using
      lVelocity_sq_pos (I := I) gamma s hs
  have hDY : covDerivAlong (I := I) q alpha Yb s = c • DY := by
    have hcomp := covDerivAlong_comp (I := I) q gamma Y
      (fun r : Real ↦ r ^ 2) s hgamma hY
        (differentiableAt_id.pow 2)
    have hsqderiv : deriv (fun r : Real ↦ r ^ 2) s = c := by
      rw [deriv_pow_field]
      simp only [c]
      norm_num
    rw [hsqderiv] at hcomp
    change covDerivAlong (I := I) q alpha Yb s = c • DY
    exact hcomp
  have hDW : covDerivAlong (I := I) q alpha Wb s = c • DW := by
    have hcomp := covDerivAlong_comp (I := I) q gamma W
      (fun r : Real ↦ r ^ 2) s hgamma hW
        (differentiableAt_id.pow 2)
    have hsqderiv : deriv (fun r : Real ↦ r ^ 2) s = c := by
      rw [deriv_pow_field]
      simp only [c]
      norm_num
    rw [hsqderiv] at hcomp
    change covDerivAlong (I := I) q alpha Wb s = c • DW
    exact hcomp
  have hinner :
      q.inner (gamma tau) (c • DY) (c • DW) =
        c ^ 2 * q.inner (gamma tau) DY DW := by
    rw [(q.inner (gamma tau)).map_smul,
      smul_apply,
      (q.inner (gamma tau) DY).map_smul]
    simp only [smul_eq_mul]
    ring
  have hN0 :
      N (vec3 (c • X) (Y tau) (W tau)) =
        c * N (vec3 X (Y tau) (W tau)) := by
    have h := tensor_slot_smul (I := I) N (vec3 X (Y tau) (W tau))
      (0 : Fin 3) c X
    have hl : Function.update (vec3 X (Y tau) (W tau))
        (0 : Fin 3) (c • X) = vec3 (c • X) (Y tau) (W tau) := by
      funext i
      fin_cases i <;> simp [vec3]
    have hr : Function.update (vec3 X (Y tau) (W tau))
        (0 : Fin 3) X = vec3 X (Y tau) (W tau) := by
      funext i
      fin_cases i <;> simp [vec3]
    simpa only [hl, hr] using h
  have hN1 :
      N (vec3 (Y tau) (c • X) (W tau)) =
        c * N (vec3 (Y tau) X (W tau)) := by
    have h := tensor_slot_smul (I := I) N (vec3 (Y tau) X (W tau))
      (1 : Fin 3) c X
    have hl : Function.update (vec3 (Y tau) X (W tau))
        (1 : Fin 3) (c • X) = vec3 (Y tau) (c • X) (W tau) := by
      funext i
      fin_cases i <;> simp [vec3]
    have hr : Function.update (vec3 (Y tau) X (W tau))
        (1 : Fin 3) X = vec3 (Y tau) X (W tau) := by
      funext i
      fin_cases i <;> simp [vec3]
    simpa only [hl, hr] using h
  have hN2 :
      N (vec3 (W tau) (c • X) (Y tau)) =
        c * N (vec3 (W tau) X (Y tau)) := by
    have h := tensor_slot_smul (I := I) N (vec3 (W tau) X (Y tau))
      (1 : Fin 3) c X
    have hl : Function.update (vec3 (W tau) X (Y tau))
        (1 : Fin 3) (c • X) = vec3 (W tau) (c • X) (Y tau) := by
      funext i
      fin_cases i <;> simp [vec3]
    have hr : Function.update (vec3 (W tau) X (Y tau))
        (1 : Fin 3) X = vec3 (W tau) X (Y tau) := by
      funext i
      fin_cases i <;> simp [vec3]
    simpa only [hl, hr] using h
  have hRm1 :
      Rm (vec4 (Y tau) (c • X) X (W tau)) =
        c * Rm (vec4 (Y tau) X X (W tau)) := by
    have h := tensor_slot_smul (I := I) Rm
      (vec4 (Y tau) X X (W tau)) (1 : Fin 4) c X
    have hl : Function.update (vec4 (Y tau) X X (W tau))
        (1 : Fin 4) (c • X) = vec4 (Y tau) (c • X) X (W tau) := by
      funext i
      fin_cases i <;> simp [vec4]
    have hr : Function.update (vec4 (Y tau) X X (W tau))
        (1 : Fin 4) X = vec4 (Y tau) X X (W tau) := by
      funext i
      fin_cases i <;> simp [vec4]
    simpa only [hl, hr] using h
  have hRm2 :
      Rm (vec4 (Y tau) (c • X) (c • X) (W tau)) =
        c * Rm (vec4 (Y tau) (c • X) X (W tau)) := by
    have h := tensor_slot_smul (I := I) Rm
      (vec4 (Y tau) (c • X) X (W tau)) (2 : Fin 4) c X
    have hl : Function.update (vec4 (Y tau) (c • X) X (W tau))
        (2 : Fin 4) (c • X) =
          vec4 (Y tau) (c • X) (c • X) (W tau) := by
      funext i
      fin_cases i <;> simp [vec4]
    have hr : Function.update (vec4 (Y tau) (c • X) X (W tau))
        (2 : Fin 4) X = vec4 (Y tau) (c • X) X (W tau) := by
      funext i
      fin_cases i <;> simp [vec4]
    simpa only [hl, hr] using h
  have hInnReg : InnReg = c ^ 2 * Inn := by
    dsimp only [InnReg]
    rw [hDY, hDW]
    simpa only [Inn] using hinner
  have hRreg : Rreg = c ^ 2 * R := by
    dsimp only [Rreg]
    rw [hAs, hRm2, hRm1]
    simp only [R]
    ring
  have hNreg0 : Nreg0 = c * N0 := by
    dsimp only [Nreg0]
    rw [hAs, hN0]
  have hNreg1 : Nreg1 = c * N1 := by
    dsimp only [Nreg1]
    rw [hAs, hN1]
  have hNreg2 : Nreg2 = c * N2 := by
    dsimp only [Nreg2]
    rw [hAs, hN2]
  simp only [lIndexInt, lRegIndexInt]
  change Real.sqrt tau *
      (Inn - R + (1 / 2 : Real) * Hess + N0 - N1 - N2) * (2 * s) =
    (1 / 2 : Real) * (InnReg - Rreg) + s ^ 2 * Hess +
      s * (Nreg0 - Nreg1 - Nreg2)
  rw [Real.sqrt_sq hs.le, hInnReg, hRreg, hNreg0, hNreg1, hNreg2]
  simp only [c]
  ring

omit [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [SigmaCompactSpace M] in
theorem lIndex_sq
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (gamma : Real → M) (Y W : ∀ tau, TangentSpace I (gamma tau))
    (tau1 tau2 : Real) (htau1 : 0 ≤ tau1) (htau2 : 0 ≤ tau2)
    (hgamma : ∀ s ∈ Set.uIcc (Real.sqrt tau1) (Real.sqrt tau2),
      0 < s → MDifferentiableAt 𝓘(Real, Real) I gamma (s ^ 2))
    (hY : ∀ s ∈ Set.uIcc (Real.sqrt tau1) (Real.sqrt tau2),
      0 < s → DifferentiableAt Real
        (chartRepAt (I := I) gamma Y (s ^ 2)) (s ^ 2))
    (hW : ∀ s ∈ Set.uIcc (Real.sqrt tau1) (Real.sqrt tau2),
      0 < s → DifferentiableAt Real
        (chartRepAt (I := I) gamma W (s ^ 2)) (s ^ 2)) :
    lIndex S T gamma Y W tau1 tau2 =
      lRegIndex S T (sqReparam gamma)
        (fun s ↦ Y (s ^ 2)) (fun s ↦ W (s ^ 2))
        (Real.sqrt tau1) (Real.sqrt tau2) := by
  have hsub :=
    intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
      (g := lIndexInt S T gamma Y W) (f := fun s : Real ↦ s ^ 2)
      (f' := fun s : Real ↦ 2 * s)
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
        (lIndexInt S T gamma Y W ∘ fun r : Real ↦ r ^ 2) s *
          (2 * s)) =
        ∫ tau in tau1..tau2, lIndexInt S T gamma Y W tau := by
    simpa only [Real.sq_sqrt htau1, Real.sq_sqrt htau2] using hsub
  have hcongr :
      (∫ s in Real.sqrt tau1..Real.sqrt tau2,
        (lIndexInt S T gamma Y W ∘ fun r : Real ↦ r ^ 2) s *
          (2 * s)) =
        ∫ s in Real.sqrt tau1..Real.sqrt tau2,
          lRegIndexInt S T (sqReparam gamma)
            (fun r ↦ Y (r ^ 2)) (fun r ↦ W (r ^ 2)) s := by
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
      lRegIndexInt_sq (I := I) S T gamma Y W s hspos
        (hgamma s hsu hspos) (hY s hsu hspos) (hW s hsu hspos)
  simpa only [lIndex, lRegIndex] using hsub'.symm.trans hcongr

omit [NeZero (Module.finrank Real E)] [SigmaCompactSpace M] in
theorem lRegIndex_balance
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    (alpha : Real → M) (Y W : ∀ r, TangentSpace I (alpha r))
    (s : Real) (ht : T - s ^ 2 ∈ D.regular)
    (halpha : ∀ᶠ r in nhds s,
      MDifferentiableAt (modelWithCornersSelf Real Real) I alpha r)
    (hA : DifferentiableAt Real
      (chartRepAt (I := I) alpha
        (fun r ↦ lVelocity (I := I) alpha r) s) s)
    (hY : DifferentiableAt Real
      (chartRepAt (I := I) alpha Y s) s)
    (hZ : DifferentiableAt Real
      (chartRepAt (I := I) alpha
        (fun r ↦ covDerivAlong (I := I)
          (S.base.metric (T - s ^ 2)) alpha Y r) s) s)
    (hW : DifferentiableAt Real
      (chartRepAt (I := I) alpha W s) s) :
    HasDerivAt
      (fun r : Real ↦
        (S.base.metric (T - r ^ 2)).inner (alpha r)
          (covDerivAlong (I := I)
            (S.base.metric (T - r ^ 2)) alpha Y r) (W r))
      (2 * lRegIndexInt S T alpha Y W s +
        lRegJacobiPair S T alpha Y s (W s)) s := by
  let q := S.base.metric (T - s ^ 2)
  let P : ∀ r, TangentSpace I (alpha r) := fun r ↦
    covDerivAlong (I := I) (S.base.metric (T - r ^ 2)) alpha Y r
  have halpha_s := halpha.self_of_nhds
  have hP : DifferentiableAt Real
      (chartRepAt (I := I) alpha P s) s := by
    simpa only [P] using
      lRegJacobiVel_diff (I := I) S hS T alpha Y s ht
        halpha hY hA hZ
  have hinner := lRegInner_deriv (I := I) S hS T alpha P W s ht
    halpha_s hP hW
  have hdyn := lRegJacobi_dyn_eq (I := I) S hS T alpha Y s ht
    halpha hA hY hZ (W s)
  apply hinner.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun r ↦ rfl) |>.congr_deriv
  rw [hdyn]
  simp only [lRegIndexInt]
  dsimp only [q, P]
  ring

omit [NeZero (Module.finrank Real E)] [SigmaCompactSpace M] in
theorem lRegIndex_green
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    (alpha : Real → M) (Y W : ∀ r, TangentSpace I (alpha r))
    (a b : Real)
    (ht : ∀ s ∈ Set.uIcc a b, T - s ^ 2 ∈ D.regular)
    (halpha : ∀ s ∈ Set.uIcc a b, ∀ᶠ r in nhds s,
      MDifferentiableAt (modelWithCornersSelf Real Real) I alpha r)
    (hA : ∀ s ∈ Set.uIcc a b, DifferentiableAt Real
      (chartRepAt (I := I) alpha
        (fun r ↦ lVelocity (I := I) alpha r) s) s)
    (hY : ∀ s ∈ Set.uIcc a b, DifferentiableAt Real
      (chartRepAt (I := I) alpha Y s) s)
    (hZ : ∀ s ∈ Set.uIcc a b, DifferentiableAt Real
      (chartRepAt (I := I) alpha
        (fun r ↦ covDerivAlong (I := I)
          (S.base.metric (T - s ^ 2)) alpha Y r) s) s)
    (hW : ∀ s ∈ Set.uIcc a b, DifferentiableAt Real
      (chartRepAt (I := I) alpha W s) s)
    (hIint : IntervalIntegrable (lRegIndexInt S T alpha Y W)
      MeasureTheory.volume a b)
    (hJint : IntervalIntegrable
      (fun s ↦ lRegJacobiPair S T alpha Y s (W s))
      MeasureTheory.volume a b) :
    lRegIndex S T alpha Y W a b =
      (1 / 2 : Real) *
        ((S.base.metric (T - b ^ 2)).inner (alpha b)
            (covDerivAlong (I := I)
              (S.base.metric (T - b ^ 2)) alpha Y b) (W b) -
          (S.base.metric (T - a ^ 2)).inner (alpha a)
            (covDerivAlong (I := I)
              (S.base.metric (T - a ^ 2)) alpha Y a) (W a) -
          ∫ s in a..b, lRegJacobiPair S T alpha Y s (W s)) := by
  let B : Real → Real := fun s ↦
    (S.base.metric (T - s ^ 2)).inner (alpha s)
      (covDerivAlong (I := I)
        (S.base.metric (T - s ^ 2)) alpha Y s) (W s)
  let K : Real → Real := lRegIndexInt S T alpha Y W
  let J : Real → Real := fun s ↦ lRegJacobiPair S T alpha Y s (W s)
  have hbal : ∀ s ∈ Set.uIcc a b,
      HasDerivAt B (2 * K s + J s) s := by
    intro s hs
    simpa only [B, K, J] using
      lRegIndex_balance (I := I) S hS T alpha Y W s (ht s hs)
        (halpha s hs) (hA s hs) (hY s hs) (hZ s hs) (hW s hs)
  have hsum : IntervalIntegrable (fun s ↦ 2 * K s + J s)
      MeasureTheory.volume a b := by
    exact (hIint.const_mul 2).add hJint
  have hderiv : IntervalIntegrable (deriv B)
      MeasureTheory.volume a b := by
    exact hsum.congr (fun s hs ↦
      (hbal s (Set.uIoc_subset_uIcc hs)).deriv.symm)
  have hftc := intervalIntegral.integral_deriv_eq_sub
    (fun s hs ↦ (hbal s hs).differentiableAt) hderiv
  have heq :
      (∫ s in a..b, deriv B s) =
        ∫ s in a..b, (2 * K s + J s) := by
    apply intervalIntegral.integral_congr
    intro s hs
    exact (hbal s hs).deriv
  rw [heq] at hftc
  rw [intervalIntegral.integral_add (hIint.const_mul 2) hJint,
    intervalIntegral.integral_const_mul] at hftc
  unfold lRegIndex
  simpa only [B, K, J] using (by linarith :
    (∫ s in a..b, K s) =
      (1 / 2 : Real) * (B b - B a - ∫ s in a..b, J s))

omit [NeZero (Module.finrank Real E)] [SigmaCompactSpace M] in
theorem lRegIndex_zero_ends
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    (alpha : Real → M) (Y W : ∀ r, TangentSpace I (alpha r))
    (a b : Real)
    (ht : ∀ s ∈ Set.uIcc a b, T - s ^ 2 ∈ D.regular)
    (halpha : ∀ s ∈ Set.uIcc a b, ∀ᶠ r in nhds s,
      MDifferentiableAt (modelWithCornersSelf Real Real) I alpha r)
    (hA : ∀ s ∈ Set.uIcc a b, DifferentiableAt Real
      (chartRepAt (I := I) alpha
        (fun r ↦ lVelocity (I := I) alpha r) s) s)
    (hY : ∀ s ∈ Set.uIcc a b, DifferentiableAt Real
      (chartRepAt (I := I) alpha Y s) s)
    (hZ : ∀ s ∈ Set.uIcc a b, DifferentiableAt Real
      (chartRepAt (I := I) alpha
        (fun r ↦ covDerivAlong (I := I)
          (S.base.metric (T - s ^ 2)) alpha Y r) s) s)
    (hW : ∀ s ∈ Set.uIcc a b, DifferentiableAt Real
      (chartRepAt (I := I) alpha W s) s)
    (hIint : IntervalIntegrable (lRegIndexInt S T alpha Y W)
      MeasureTheory.volume a b)
    (hJint : IntervalIntegrable
      (fun s ↦ lRegJacobiPair S T alpha Y s (W s))
      MeasureTheory.volume a b)
    (hWa : W a = 0) (hWb : W b = 0) :
    lRegIndex S T alpha Y W a b =
      -(1 / 2 : Real) *
        ∫ s in a..b, lRegJacobiPair S T alpha Y s (W s) := by
  have hgreen := lRegIndex_green (I := I) S hS T alpha Y W a b ht
    halpha hA hY hZ hW hIint hJint
  rw [hWa, hWb] at hgreen
  simp only [map_zero, sub_zero, zero_sub] at hgreen
  rw [hgreen]
  ring

omit [NeZero (Module.finrank Real E)] [SigmaCompactSpace M] in
theorem lRegIndex_jacobi
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    (alpha : Real → M) (Y W : ∀ r, TangentSpace I (alpha r))
    (a b : Real)
    (ht : ∀ s ∈ Set.uIcc a b, T - s ^ 2 ∈ D.regular)
    (halpha : ∀ s ∈ Set.uIcc a b, ∀ᶠ r in nhds s,
      MDifferentiableAt (modelWithCornersSelf Real Real) I alpha r)
    (hA : ∀ s ∈ Set.uIcc a b, DifferentiableAt Real
      (chartRepAt (I := I) alpha
        (fun r ↦ lVelocity (I := I) alpha r) s) s)
    (hjac : IsLRegJacobi S T alpha Y (Set.uIcc a b))
    (hW : ∀ s ∈ Set.uIcc a b, DifferentiableAt Real
      (chartRepAt (I := I) alpha W s) s)
    (hIint : IntervalIntegrable (lRegIndexInt S T alpha Y W)
      MeasureTheory.volume a b) :
    lRegIndex S T alpha Y W a b =
      (1 / 2 : Real) *
        ((S.base.metric (T - b ^ 2)).inner (alpha b)
            (covDerivAlong (I := I)
              (S.base.metric (T - b ^ 2)) alpha Y b) (W b) -
          (S.base.metric (T - a ^ 2)).inner (alpha a)
            (covDerivAlong (I := I)
              (S.base.metric (T - a ^ 2)) alpha Y a) (W a)) := by
  have hJzero : ∀ s ∈ Set.uIcc a b,
      lRegJacobiPair S T alpha Y s (W s) = 0 := by
    intro s hs
    exact (hjac s hs).2.2.2 (W s)
  have hJint : IntervalIntegrable
      (fun s ↦ lRegJacobiPair S T alpha Y s (W s))
      MeasureTheory.volume a b := by
    rw [intervalIntegrable_congr
      (f := fun s ↦ lRegJacobiPair S T alpha Y s (W s))
      (g := fun _ : Real ↦ (0 : Real)) (by
        intro s hs
        exact hJzero s (Set.uIoc_subset_uIcc hs))]
    exact intervalIntegrable_const
  have hgreen := lRegIndex_green (I := I) S hS T alpha Y W a b ht
    halpha hA (fun s hs ↦ (hjac s hs).2.1)
    (fun s hs ↦ (hjac s hs).2.2.1) hW hIint hJint
  have hJintegral :
      (∫ s in a..b, lRegJacobiPair S T alpha Y s (W s)) = 0 := by
    calc
      _ = ∫ _s in a..b, (0 : Real) :=
        intervalIntegral.integral_congr hJzero
      _ = 0 := by simp
  rw [hJintegral] at hgreen
  simpa only [sub_zero] using hgreen

end DifferentialGeometry.PDE.RicciFlow.Perelman
