import DifferentialGeometry.Geometry.Comparison.Variation.VelocityPairDerivative
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.SecondVariation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Index.Integrability

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Filter Set MeasureTheory
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Variation

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]
  {D : RealTimeInterval}

private theorem lRegularizedIndex_eq_boundary_sub_integral_variation
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    (f : Real → Real → M) (hf : IsSmoothVariation (I := I) f)
    (a b : Real)
    (hgeo : IsLRegularizedGeodesicOn S T (f 0) (uIcc a b)) :
    lRegularizedIndex S T (f 0)
        (fun s : Real ↦ lVelocity (I := I) (fun u : Real ↦ f u s) 0)
        (fun s : Real ↦ lVelocity (I := I) (fun u : Real ↦ f u s) 0) a b =
      (1 / 2 : Real) *
        ((S.base.metric (T - b ^ 2)).inner (f 0 b)
            (covDerivAlong (I := I) (S.base.metric (T - b ^ 2)) (f 0)
              (fun s : Real ↦
                lVelocity (I := I) (fun u : Real ↦ f u s) 0) b)
            (lVelocity (I := I) (fun u : Real ↦ f u b) 0) -
          (S.base.metric (T - a ^ 2)).inner (f 0 a)
            (covDerivAlong (I := I) (S.base.metric (T - a ^ 2)) (f 0)
              (fun s : Real ↦
                lVelocity (I := I) (fun u : Real ↦ f u s) 0) a)
            (lVelocity (I := I) (fun u : Real ↦ f u a) 0) -
          ∫ s in a..b,
            lRegularizedJacobiPair S T (f 0)
              (fun r : Real ↦
                lVelocity (I := I) (fun u : Real ↦ f u r) 0)
              s (lVelocity (I := I) (fun u : Real ↦ f u s) 0)) := by
  have hcurve : IsLRegularizedCurveOn S T (f 0) (uIcc a b) (f 0 0)
      ((1 / 2 : ℝ) • lVelocity (I := I) (f 0) 0) := by
    refine ⟨rfl, ?_, hgeo⟩
    simp only [two_smul, ← add_smul]
    norm_num
  let alpha : Real → M := f 0
  let Y : (s : Real) → TangentSpace I (alpha s) := fun s ↦
    lVelocity (I := I) (fun u : Real ↦ f u s) 0
  have ht : ∀ s ∈ uIcc a b, T - s ^ 2 ∈ D.regular :=
    fun s hs ↦ (hgeo s hs).1
  have halphaAll : ContMDiff (modelWithCornersSelf Real Real) I (8 : Nat) alpha := by
    exact (hf : ContMDiff _ _ _ _).comp
      (contMDiff_const.prodMk contMDiff_id)
  have hswap : IsSmoothVariation (I := I) (fun s u : Real ↦ f u s) := by
    exact (hf : ContMDiff _ _ _ _).comp
      (contMDiff_snd.prodMk contMDiff_fst)
  have hYjoint : ContMDiff
      ((modelWithCornersSelf Real Real).prod (modelWithCornersSelf Real Real))
      I.tangent (7 : Nat)
      (fun q : Real × Real ↦
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (f q.1 q.2)
          (lVelocity (I := I) (fun u : Real ↦ f u q.2) q.1) :
            TangentBundle I M)) := by
    have hbase := velocity_totalSpace_contMDiff
      (I := I) (M := M) (fun s u : Real ↦ f u s) hswap
    have hcomp := hbase.comp
      (contMDiff_snd.prodMk contMDiff_fst :
        ContMDiff
          ((modelWithCornersSelf Real Real).prod
            (modelWithCornersSelf Real Real))
          ((modelWithCornersSelf Real Real).prod
            (modelWithCornersSelf Real Real)) (7 : Nat)
          (fun q : Real × Real ↦ (q.2, q.1)))
    simpa only [Function.comp_def, lVelocity] using hcomp
  have hYall : ContMDiff (modelWithCornersSelf Real Real) I.tangent (7 : Nat)
      (fun s : Real ↦
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (alpha s) (Y s) : TangentBundle I M)) := by
    simpa only [alpha, Y, Function.comp_def, id_eq] using hYjoint.comp
      (contMDiff_const.prodMk contMDiff_id)
  have halpha : ∀ s ∈ uIcc a b, ∀ᶠ r in nhds s,
      MDifferentiableAt (modelWithCornersSelf Real Real) I alpha r := by
    intro s hs
    exact Eventually.of_forall fun r ↦
      halphaAll.mdifferentiableAt (by norm_num)
  have hA : ∀ s ∈ uIcc a b, DifferentiableAt Real
      (chartRepAt (I := I) alpha
        (fun r ↦ lVelocity (I := I) alpha r) s) s := by
    intro s hs
    simpa only [alpha] using (hgeo s hs).2.2.1
  have hY : ∀ s ∈ uIcc a b, DifferentiableAt Real
      (chartRepAt (I := I) alpha Y s) s := by
    intro s hs
    simpa only [alpha, Y] using
      (lRegularizedVar_regularity (I := I) S T s f hf).2.1
  have hZ : ∀ s ∈ uIcc a b, DifferentiableAt Real
      (chartRepAt (I := I) alpha
        (fun r ↦ covDerivAlong (I := I)
          (S.base.metric (T - s ^ 2)) alpha Y r) s) s := by
    intro s hs
    simpa only [alpha, Y] using
      (lRegularizedVar_regularity (I := I) S T s f hf).2.2
  have hY2 : ContMDiff (modelWithCornersSelf Real Real) I.tangent 2
      (fun s : Real ↦
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (alpha s) (Y s) : TangentBundle I M)) :=
    hYall.of_le (by norm_num)
  have hIint := intervalIntegrable_lRegularizedIndexIntegrand_of_contMDiff (I := I)
    S hS T a b alpha Y Y hY2 hY2 ht
  have hJint : IntervalIntegrable
      (fun s : Real ↦ lRegularizedJacobiPair S T alpha Y s (Y s))
      MeasureTheory.volume a b := by
    simpa only [alpha, Y] using
      (continuousOn_lRegularizedJacobiPair_variation (I := I) S hS T f hf a b (f 0 0)
        ((1 / 2 : ℝ) • lVelocity (I := I) (f 0) 0) hcurve).intervalIntegrable
  simpa only [alpha, Y] using
    lRegularizedIndex_green (I := I) S hS T alpha Y Y a b ht
      halpha hA hY hZ hY hIint hJint

theorem lRegularizedAction_second_variation_moving_endpoints
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : ℝ) (f : ℝ → ℝ → M) (hf : IsSmoothVariation (I := I) f)
    (a b : ℝ) (hgeo : IsLRegularizedGeodesicOn S T (f 0) (uIcc a b)) :
    HasDerivAt
      (fun u ↦ deriv (fun v ↦ lRegularizedAction S T (f v) a b) u)
      (2 * lRegularizedIndex S T (f 0)
          (fun s ↦ lVelocity (I := I) (fun u ↦ f u s) 0)
          (fun s ↦ lVelocity (I := I) (fun u ↦ f u s) 0) a b +
        (S.base.metric (T - b ^ 2)).inner (f 0 b)
          (covDerivAlong (I := I) (S.base.metric (T - b ^ 2))
            (fun u ↦ f u b) (fun u ↦ lVelocity (I := I) (fun v ↦ f v b) u) 0)
          (lVelocity (I := I) (f 0) b) -
        (S.base.metric (T - a ^ 2)).inner (f 0 a)
          (covDerivAlong (I := I) (S.base.metric (T - a ^ 2))
            (fun u ↦ f u a) (fun u ↦ lVelocity (I := I) (fun v ↦ f v a) u) 0)
          (lVelocity (I := I) (f 0) a)) 0 := by
  let L : ℝ → ℝ := fun u ↦ lRegularizedAction S T (f u) a b
  let P : ℝ → ℝ → ℝ := fun s u ↦
    (S.base.metric (T - s ^ 2)).inner (f u s)
      (lVelocity (I := I) (fun v ↦ f v s) u) (lVelocity (I := I) (f u) s)
  let Eul : ℝ → ℝ := fun u ↦
    ∫ s in a..b, -lRegularizedEulerPair S T (f u) s
      (lVelocity (I := I) (fun v ↦ f v s) u)
  let A : ℝ → ℝ := fun s ↦
    (S.base.metric (T - s ^ 2)).inner (f 0 s)
      (covDerivAlong (I := I) (S.base.metric (T - s ^ 2))
        (fun u ↦ f u s) (fun u ↦ lVelocity (I := I) (fun v ↦ f v s) u) 0)
      (lVelocity (I := I) (f 0) s)
  let B : ℝ → ℝ := fun s ↦
    (S.base.metric (T - s ^ 2)).inner (f 0 s)
      (covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) (f 0)
        (fun r ↦ lVelocity (I := I) (fun u ↦ f u r) 0) s)
      (lVelocity (I := I) (fun u ↦ f u s) 0)
  let J : ℝ → ℝ := fun s ↦ lRegularizedJacobiPair S T (f 0)
    (fun r ↦ lVelocity (I := I) (fun u ↦ f u r) 0) s
    (lVelocity (I := I) (fun u ↦ f u s) 0)
  have ht : ∀ s ∈ uIcc a b, T - s ^ 2 ∈ D.regular := fun s hs ↦ (hgeo s hs).1
  have hcurve : IsLRegularizedCurveOn S T (f 0) (uIcc a b) (f 0 0)
      ((1 / 2 : ℝ) • lVelocity (I := I) (f 0) 0) := by
    refine ⟨rfl, ?_, hgeo⟩
    simp only [two_smul, ← add_smul]
    norm_num
  have hderivEq (u : ℝ) : deriv L u = P b u - P a u + Eul u := by
    let F : ℝ → ℝ → M := fun v s ↦ f (u + v) s
    have hF : IsSmoothVariation (I := I) F :=
      hf.comp ((contMDiff_const.add contMDiff_fst).prodMk contMDiff_snd)
    have hF0 : F 0 = f u := by
      funext s
      simp only [F, add_zero]
    have hshift (s : ℝ) :
        lVelocity (I := I) (fun v ↦ F v s) 0 =
          lVelocity (I := I) (fun v ↦ f v s) u := by
      simpa only [F, lVelocity, varFst] using varFst_shift (I := I) f hf u s
    have hfirst := lRegularizedAction_first_variation (I := I) S hS T F hF a b ht
    rw [hF0] at hfirst
    have htranslated : HasDerivAt (fun v ↦ L (u + v))
        (P b u - P a u + Eul u) 0 := by
      refine (hfirst.congr_of_eventuallyEq (Eventually.of_forall fun _ ↦ rfl)).congr_deriv ?_
      simp only [P, Eul, hshift, intervalIntegral.integral_neg]
      ring
    have hderiv := htranslated.deriv
    rw [deriv_comp_const_add L u 0, add_zero] at hderiv
    exact hderiv
  have hp (s : ℝ) : HasDerivAt (P s) (A s + B s) 0 := by
    have hp := hasDerivAt_inner_varFst_varSnd (I := I) (S.base.metric (T - s ^ 2))
      f hf s
    apply hp.congr_deriv
    change A s + (S.base.metric (T - s ^ 2)).inner (f 0 s)
        (lVelocity (I := I) (fun u ↦ f u s) 0)
        (covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) (f 0)
          (fun r ↦ lVelocity (I := I) (fun u ↦ f u r) 0) s) = A s + B s
    congr 1
    exact (S.base.metric (T - s ^ 2)).symm (f 0 s) _ _
  have hEul : HasDerivAt Eul (-(∫ s in a..b, J s)) 0 := by
    exact hasDerivAt_integral_lRegularizedEulerPair_variation (I := I) S hS T f hf a b
      (f 0 0) ((1 / 2 : ℝ) • lVelocity (I := I) (f 0) 0) hcurve
  have hraw := ((hp b).sub (hp a)).add hEul
  have hfun : (fun u ↦ deriv L u) = fun u ↦ P b u - P a u + Eul u :=
    funext hderivEq
  change HasDerivAt (fun u ↦ deriv L u) _ 0
  rw [hfun]
  apply hraw.congr_deriv
  have hindex := lRegularizedIndex_eq_boundary_sub_integral_variation (I := I)
    S hS T f hf a b hgeo
  change lRegularizedIndex S T (f 0)
      (fun s ↦ lVelocity (I := I) (fun u ↦ f u s) 0)
      (fun s ↦ lVelocity (I := I) (fun u ↦ f u s) 0) a b =
    (1 / 2 : ℝ) * (B b - B a - ∫ s in a..b, J s) at hindex
  rw [hindex]
  change A b + B b - (A a + B a) + -(∫ s in a..b, J s) =
    2 * ((1 / 2 : ℝ) * (B b - B a - ∫ s in a..b, J s)) + A b - A a
  ring

end DifferentialGeometry.PDE.RicciFlow.Perelman
