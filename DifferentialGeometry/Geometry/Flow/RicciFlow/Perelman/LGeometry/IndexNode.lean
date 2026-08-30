import DifferentialGeometry.Geometry.Comparison.Variation.FieldRealizationPair
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.C1Integrability
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.NodeSplicing
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Minimizer
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.RegIndexSmooth

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Filter Function Set
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Variation

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
variable {D : RealTimeInterval}

omit [NeZero (Module.finrank Real E)] [T2Space M]
  [SigmaCompactSpace M] [CompactSpace M] in
private theorem nodePair_deriv
    (g : SmoothRiemannianMetric I M)
    (f : Real → Real → M) (hf : IsSmoothVariation (I := I) f)
    (c : Real) :
    HasDerivAt
      (fun u : Real ↦
        g.inner (f u c)
          (lVelocity (I := I) (fun v : Real ↦ f v c) u)
          (lVelocity (I := I) (f u) c))
      (g.inner (f 0 c)
          (covDerivAlong (I := I) g (fun u : Real ↦ f u c)
            (fun u : Real ↦
              lVelocity (I := I) (fun v : Real ↦ f v c) u) 0)
          (lVelocity (I := I) (f 0) c) +
        g.inner (f 0 c)
          (lVelocity (I := I) (fun v : Real ↦ f v c) 0)
          (covDerivAlong (I := I) g (f 0)
            (fun s : Real ↦
              lVelocity (I := I) (fun u : Real ↦ f u s) 0) c)) 0 := by
  let node : Real → M := fun u ↦ f u c
  let U : (u : Real) → TangentSpace I (node u) := fun u ↦
    lVelocity (I := I) node u
  let A : (u : Real) → TangentSpace I (node u) := fun u ↦
    lVelocity (I := I) (f u) c
  have hnode : ContMDiff (modelWithCornersSelf Real Real) I (8 : Nat) node := by
    exact (hf : ContMDiff _ _ _ _).comp
      (contMDiff_id.prodMk contMDiff_const)
  have hU : DifferentiableAt Real
      (chartRepAt (I := I) node U 0) 0 := by
    change DifferentiableAt Real
      (fun u ↦
        (trivializationAt E (TangentSpace I) (node 0)).continuousLinearMapAt Real
          (node u) (U u)) 0
    simpa only [node, U, lVelocity] using
      DifferentialGeometry.Geometry.Riemannian.MFDerivAlongCurve.velocity_coord_diff
        (I := I) node 0 (hnode.contMDiffAt.of_le (by norm_num))
  let fs : Real → Real → M := fun s u ↦ f u s
  have hfs : IsSmoothVariation (I := I) fs := by
    exact (hf : ContMDiff _ _ _ _).comp
      (contMDiff_snd.prodMk contMDiff_fst)
  let fc : Real → Real → M := fun s u ↦ fs (c + s) u
  have hfc : IsSmoothVariation (I := I) fc := by
    exact (hfs : ContMDiff _ _ _ _).comp
      ((contMDiff_const.add contMDiff_fst).prodMk contMDiff_snd)
  have hA : DifferentiableAt Real
      (chartRepAt (I := I) node A 0) 0 := by
    have hraw := variationField_chartRep_differentiableAt
      (I := I) fc hfc 0
    change DifferentiableAt Real
      (chartRepAt (I := I) (fun u : Real ↦ fc 0 u)
        (fun u : Real ↦ lVelocity (I := I) (fun s : Real ↦ fc s u) 0) 0) 0 at hraw
    have hbase : (fun u : Real ↦ fc 0 u) = node := by
      funext u
      simp only [fc, fs, node, add_zero]
    have hfield : (fun u : Real ↦
        lVelocity (I := I) (fun s : Real ↦ fc s u) 0) = A := by
      funext u
      simpa only [fc, fs, A, lVelocity, varFst] using
        varFst_shift (I := I) fs hfs c u
    rw [hbase, hfield] at hraw
    exact hraw
  have hinner := inner_deriv_at (I := I) (n := (8 : WithTop ℕ∞))
    (by norm_num) g node U A 0 hnode.contMDiffAt hU hA
  have hcomm := commute_ds_dt_intrinsic (I := I) g f hf c
  have hcomm' :
      covDerivAlong (I := I) g (fun u : Real ↦ f u c)
          (fun u : Real ↦ lVelocity (I := I) (f u) c) 0 =
        covDerivAlong (I := I) g (f 0)
          (fun s : Real ↦
            lVelocity (I := I) (fun u : Real ↦ f u s) 0) c := by
    simpa only [lVelocity] using hcomm
  have hinner' : HasDerivAt
      (fun u : Real ↦
        g.inner (f u c)
          (lVelocity (I := I) (fun v : Real ↦ f v c) u)
          (lVelocity (I := I) (f u) c))
      (g.inner (f 0 c)
          (covDerivAlong (I := I) g (fun u : Real ↦ f u c)
            (fun u : Real ↦
              lVelocity (I := I) (fun v : Real ↦ f v c) u) 0)
          (lVelocity (I := I) (f 0) c) +
        g.inner (f 0 c)
          (lVelocity (I := I) (fun v : Real ↦ f v c) 0)
          (covDerivAlong (I := I) g (fun u : Real ↦ f u c)
            (fun u : Real ↦ lVelocity (I := I) (f u) c) 0)) 0 := by
    simpa only [node, U, A, lVelocity] using hinner
  apply hinner'.congr_deriv
  rw [hcomm']

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
private theorem indexGreen_var
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    (f : Real → Real → M) (hf : IsSmoothVariation (I := I) f)
    (a b : Real) (x : M) (Z : TangentSpace I x)
    (hgeo : IsLRegCurveOn S T (f 0) (uIcc a b) x Z) :
    lRegIndex S T (f 0)
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
            lRegJacobiPair S T (f 0)
              (fun r : Real ↦
                lVelocity (I := I) (fun u : Real ↦ f u r) 0)
              s (lVelocity (I := I) (fun u : Real ↦ f u s) 0)) := by
  let alpha : Real → M := f 0
  let Y : (s : Real) → TangentSpace I (alpha s) := fun s ↦
    lVelocity (I := I) (fun u : Real ↦ f u s) 0
  have ht : ∀ s ∈ uIcc a b, T - s ^ 2 ∈ D.regular :=
    fun s hs ↦ (hgeo.2.2 s hs).1
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
    simpa only [alpha] using (hgeo.2.2 s hs).2.2.1
  have hY : ∀ s ∈ uIcc a b, DifferentiableAt Real
      (chartRepAt (I := I) alpha Y s) s := by
    intro s hs
    simpa only [alpha, Y] using
      (lRegVar_reg (I := I) S T s f hf).2.1
  have hZ : ∀ s ∈ uIcc a b, DifferentiableAt Real
      (chartRepAt (I := I) alpha
        (fun r ↦ covDerivAlong (I := I)
          (S.base.metric (T - s ^ 2)) alpha Y r) s) s := by
    intro s hs
    simpa only [alpha, Y] using
      (lRegVar_reg (I := I) S T s f hf).2.2
  have hY2 : ContMDiff (modelWithCornersSelf Real Real) I.tangent 2
      (fun s : Real ↦
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (alpha s) (Y s) : TangentBundle I M)) :=
    hYall.of_le (by norm_num)
  have hIint := lRegIndex_int (I := I) S hS T a b alpha Y Y
    hY2 hY2 ht
  have hJint : IntervalIntegrable
      (fun s : Real ↦ lRegJacobiPair S T alpha Y s (Y s))
      MeasureTheory.volume a b := by
    simpa only [alpha, Y] using
      (lRegJacobi_contOn (I := I) S hS T f hf a b x Z hgeo).intervalIntegrable
  simpa only [alpha, Y] using
    lRegIndex_green (I := I) S hS T alpha Y Y a b ht
      halpha hA hY hZ hY hIint hJint

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
private theorem nodeAction_second
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    (f0 f1 : Real → Real → M)
    (hf0 : IsSmoothVariation (I := I) f0)
    (hf1 : IsSmoothVariation (I := I) f1)
    (a c b : Real) (x : M) (Z : TangentSpace I x)
    (hgeo0 : IsLRegCurveOn S T (f0 0) (uIcc a c) x Z)
    (hgeo1 : IsLRegCurveOn S T (f1 0) (uIcc c b) x Z)
    (hcenter : f0 0 = f1 0)
    (hfixa : ∀ u : Real, f0 u a = f0 0 a)
    (hfixb : ∀ u : Real, f1 u b = f1 0 b)
    (hnode : ∀ u : Real, f0 u c = f1 u c) :
    HasDerivAt
      (fun u : Real ↦ deriv
        (fun v : Real ↦
          lRegAction S T (f0 v) a c + lRegAction S T (f1 v) c b) u)
      (2 *
        (lRegIndex S T (f0 0)
            (fun s : Real ↦
              lVelocity (I := I) (fun u : Real ↦ f0 u s) 0)
            (fun s : Real ↦
              lVelocity (I := I) (fun u : Real ↦ f0 u s) 0) a c +
          lRegIndex S T (f1 0)
            (fun s : Real ↦
              lVelocity (I := I) (fun u : Real ↦ f1 u s) 0)
            (fun s : Real ↦
              lVelocity (I := I) (fun u : Real ↦ f1 u s) 0) c b)) 0 := by
  let L : Real → Real := fun u ↦
    lRegAction S T (f0 u) a c + lRegAction S T (f1 u) c b
  let P0 : Real → Real := fun u ↦
    (S.base.metric (T - c ^ 2)).inner (f0 u c)
      (lVelocity (I := I) (fun v : Real ↦ f0 v c) u)
      (lVelocity (I := I) (f0 u) c)
  let P1 : Real → Real := fun u ↦
    (S.base.metric (T - c ^ 2)).inner (f1 u c)
      (lVelocity (I := I) (fun v : Real ↦ f1 v c) u)
      (lVelocity (I := I) (f1 u) c)
  let E0 : Real → Real := fun u ↦
    ∫ s in a..c, -lRegEulerPair S T (f0 u) s
      (lVelocity (I := I) (fun v : Real ↦ f0 v s) u)
  let E1 : Real → Real := fun u ↦
    ∫ s in c..b, -lRegEulerPair S T (f1 u) s
      (lVelocity (I := I) (fun v : Real ↦ f1 v s) u)
  have ht0 : ∀ s ∈ uIcc a c, T - s ^ 2 ∈ D.regular :=
    fun s hs ↦ (hgeo0.2.2 s hs).1
  have ht1 : ∀ s ∈ uIcc c b, T - s ^ 2 ∈ D.regular :=
    fun s hs ↦ (hgeo1.2.2 s hs).1
  have hderivEq (u : Real) : deriv L u = P0 u - P1 u + E0 u + E1 u := by
    let F0 : Real → Real → M := fun v s ↦ f0 (u + v) s
    let F1 : Real → Real → M := fun v s ↦ f1 (u + v) s
    have hF0 : IsSmoothVariation (I := I) F0 := by
      exact (hf0 : ContMDiff _ _ _ _).comp
        ((contMDiff_const.add contMDiff_fst).prodMk contMDiff_snd)
    have hF1 : IsSmoothVariation (I := I) F1 := by
      exact (hf1 : ContMDiff _ _ _ _).comp
        ((contMDiff_const.add contMDiff_fst).prodMk contMDiff_snd)
    have hF00 : F0 0 = f0 u := by
      funext s
      simp only [F0, add_zero]
    have hF10 : F1 0 = f1 u := by
      funext s
      simp only [F1, add_zero]
    have hshift0 (s : Real) :
        lVelocity (I := I) (fun v : Real ↦ F0 v s) 0 =
          lVelocity (I := I) (fun v : Real ↦ f0 v s) u := by
      simpa only [F0, lVelocity, varFst] using
        varFst_shift (I := I) f0 hf0 u s
    have hshift1 (s : Real) :
        lVelocity (I := I) (fun v : Real ↦ F1 v s) 0 =
          lVelocity (I := I) (fun v : Real ↦ f1 v s) u := by
      simpa only [F1, lVelocity, varFst] using
        varFst_shift (I := I) f1 hf1 u s
    have hYa : lVelocity (I := I) (fun v : Real ↦ F0 v a) 0 = 0 := by
      have hconst : (fun v : Real ↦ F0 v a) = fun _ : Real ↦ f0 0 a := by
        funext v
        exact hfixa (u + v)
      rw [hconst]
      simp only [lVelocity, mfderiv_const]
      rfl
    have hYb : lVelocity (I := I) (fun v : Real ↦ F1 v b) 0 = 0 := by
      have hconst : (fun v : Real ↦ F1 v b) = fun _ : Real ↦ f1 0 b := by
        funext v
        exact hfixb (u + v)
      rw [hconst]
      simp only [lVelocity, mfderiv_const]
      rfl
    have hfirst0 := lRegAction_first (I := I) S hS T F0 hF0 a c ht0
    have hfirst1 := lRegAction_first (I := I) S hS T F1 hF1 c b ht1
    rw [hYa] at hfirst0
    rw [hYb] at hfirst1
    simp only [map_zero, zero_apply, sub_zero, zero_sub] at hfirst0 hfirst1
    rw [hF00] at hfirst0
    rw [hF10] at hfirst1
    have hsum := hfirst0.add hfirst1
    have hshift : HasDerivAt (fun v : Real ↦ L (u + v))
        (P0 u - P1 u + E0 u + E1 u) 0 := by
      refine (hsum.congr_of_eventuallyEq (Eventually.of_forall fun _ ↦ rfl)).congr_deriv ?_
      simp only [P0, P1, E0, E1, hshift0, hshift1,
        intervalIntegral.integral_neg]
      ring
    have hderiv := hshift.deriv
    rw [deriv_comp_const_add L u 0, add_zero] at hderiv
    exact hderiv
  have hfun : (fun u : Real ↦ deriv L u) =
      fun u : Real ↦ P0 u - P1 u + E0 u + E1 u :=
    funext hderivEq
  rw [show (fun u : Real ↦ deriv
      (fun v : Real ↦
        lRegAction S T (f0 v) a c + lRegAction S T (f1 v) c b) u) =
      (fun u : Real ↦ deriv L u) by rfl, hfun]
  have hpair0 := nodePair_deriv (I := I)
    (S.base.metric (T - c ^ 2)) f0 hf0 c
  have hpair1 := nodePair_deriv (I := I)
    (S.base.metric (T - c ^ 2)) f1 hf1 c
  have hpairs : HasDerivAt (fun u : Real ↦ P0 u - P1 u)
      ((S.base.metric (T - c ^ 2)).inner (f0 0 c)
          (covDerivAlong (I := I) (S.base.metric (T - c ^ 2))
            (f0 0) (fun s : Real ↦
              lVelocity (I := I) (fun u : Real ↦ f0 u s) 0) c)
          (lVelocity (I := I) (fun u : Real ↦ f0 u c) 0) -
        (S.base.metric (T - c ^ 2)).inner (f1 0 c)
          (covDerivAlong (I := I) (S.base.metric (T - c ^ 2))
            (f1 0) (fun s : Real ↦
              lVelocity (I := I) (fun u : Real ↦ f1 u s) 0) c)
          (lVelocity (I := I) (fun u : Real ↦ f1 u c) 0)) 0 := by
    have hraw := hpair0.sub hpair1
    have hnodeFun : (fun u : Real ↦ f0 u c) = fun u : Real ↦ f1 u c :=
      funext hnode
    have hvel : lVelocity (I := I) (f0 0) c =
        lVelocity (I := I) (f1 0) c := by rw [hcenter]
    have hnodeVel : (fun u : Real ↦
        lVelocity (I := I) (fun v : Real ↦ f0 v c) u) =
      fun u : Real ↦
        lVelocity (I := I) (fun v : Real ↦ f1 v c) u := by
      rw [hnodeFun]
    have hnodeCov :
        covDerivAlong (I := I) (S.base.metric (T - c ^ 2))
            (fun u : Real ↦ f0 u c)
            (fun u : Real ↦
              lVelocity (I := I) (fun v : Real ↦ f0 v c) u) 0 =
          covDerivAlong (I := I) (S.base.metric (T - c ^ 2))
            (fun u : Real ↦ f1 u c)
            (fun u : Real ↦
              lVelocity (I := I) (fun v : Real ↦ f1 v c) u) 0 := by
      rw [hnodeFun]
    have hbase : f0 0 c = f1 0 c := hnode 0
    have hpairEq : (fun u : Real ↦ P0 u - P1 u) =ᶠ[nhds 0]
        (fun u : Real ↦
          (S.base.metric (T - c ^ 2)).inner (f0 u c)
              (lVelocity (I := I) (fun v : Real ↦ f0 v c) u)
              (lVelocity (I := I) (f0 u) c) -
            (S.base.metric (T - c ^ 2)).inner (f1 u c)
              (lVelocity (I := I) (fun v : Real ↦ f1 v c) u)
              (lVelocity (I := I) (f1 u) c)) :=
      Eventually.of_forall fun _ ↦ rfl
    have hraw' := hraw.congr_of_eventuallyEq hpairEq
    apply hraw'.congr_deriv
    rw [hbase, hvel, hnodeFun]
    have hsym0 := (S.base.metric (T - c ^ 2)).symm (f1 0 c)
      (lVelocity (I := I) (fun u : Real ↦ f1 u c) 0)
      (covDerivAlong (I := I) (S.base.metric (T - c ^ 2))
        (f0 0) (fun s : Real ↦
          lVelocity (I := I) (fun u : Real ↦ f0 u s) 0) c)
    have hsym1 := (S.base.metric (T - c ^ 2)).symm (f1 0 c)
      (lVelocity (I := I) (fun u : Real ↦ f1 u c) 0)
      (covDerivAlong (I := I) (S.base.metric (T - c ^ 2))
        (f1 0) (fun s : Real ↦
          lVelocity (I := I) (fun u : Real ↦ f1 u s) 0) c)
    rw [hsym0, hsym1]
    ring
  have heuler0 := lRegEulerInt_deriv (I := I) S hS T f0 hf0 a c x Z hgeo0
  have heuler1 := lRegEulerInt_deriv (I := I) S hS T f1 hf1 c b x Z hgeo1
  have htotal := (hpairs.add heuler0).add heuler1
  have hgreen0 := indexGreen_var (I := I) S hS T f0 hf0 a c x Z hgeo0
  have hgreen1 := indexGreen_var (I := I) S hS T f1 hf1 c b x Z hgeo1
  have hYa : lVelocity (I := I) (fun u : Real ↦ f0 u a) 0 = 0 := by
    have hconst : (fun u : Real ↦ f0 u a) = fun _ : Real ↦ f0 0 a :=
      funext hfixa
    rw [hconst]
    simp only [lVelocity, mfderiv_const]
    rfl
  have hYb : lVelocity (I := I) (fun u : Real ↦ f1 u b) 0 = 0 := by
    have hconst : (fun u : Real ↦ f1 u b) = fun _ : Real ↦ f1 0 b :=
      funext hfixb
    rw [hconst]
    simp only [lVelocity, mfderiv_const]
    rfl
  apply htotal.congr_deriv
  rw [hYa] at hgreen0
  rw [hYb] at hgreen1
  simp only [map_zero, sub_zero, zero_sub] at hgreen0 hgreen1
  rw [hgreen0, hgreen1]
  ring

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem lIndex_sum_nonneg
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    (gamma : Real → M) (a c b : Real) (hac : a < c) (hcb : c < b)
    (x : M) (Z : TangentSpace I x)
    (hgeo : IsLRegCurveOn S T gamma (uIcc a b) x Z)
    (hmin : ∀ delta : Real → M,
      ContMDiff (modelWithCornersSelf Real Real) I 1 delta →
      delta a = gamma a → delta b = gamma b →
      lRegAction S T gamma a b ≤ lRegAction S T delta a b)
    (Y0 Y1 : Real → E)
    (hY0 : ContMDiff (modelWithCornersSelf Real Real) I.tangent (8 : Nat)
      (fun s ↦ (TotalSpace.mk' E
        (E := (TangentSpace I : M → Type _)) (gamma s) (Y0 s) :
          TangentBundle I M)))
    (hY1 : ContMDiff (modelWithCornersSelf Real Real) I.tangent (8 : Nat)
      (fun s ↦ (TotalSpace.mk' E
        (E := (TangentSpace I : M → Type _)) (gamma s) (Y1 s) :
          TangentBundle I M)))
    (hY0a : Y0 a = 0) (hY1b : Y1 b = 0) (hYc : Y0 c = Y1 c) :
    0 ≤ lRegIndex S T gamma Y0 Y0 a c +
      lRegIndex S T gamma Y1 Y1 c b := by
  obtain ⟨f0, f1, hf0, hf1, hf00, hf10, hfield0, hfield1,
      hsame, hzero0, hzero1⟩ :=
    exists_var_pair (I := I) (S.base.metric T) gamma Y0 Y1 a b hY0 hY1
  have hcenter0 : f0 0 = gamma := funext hf00
  have hcenter1 : f1 0 = gamma := funext hf10
  have hcenter : f0 0 = f1 0 := hcenter0.trans hcenter1.symm
  have hab : a < b := hac.trans hcb
  have hgeo0 : IsLRegCurveOn S T (f0 0) (uIcc a c) x Z := by
    rw [hcenter0]
    refine ⟨hgeo.1, hgeo.2.1, fun s hs ↦ hgeo.2.2 s ?_⟩
    have hs' : s ∈ Icc a c := by
      simpa only [uIcc_of_le hac.le] using hs
    rw [uIcc_of_le hab.le]
    exact ⟨hs'.1, hs'.2.trans hcb.le⟩
  have hgeo1 : IsLRegCurveOn S T (f1 0) (uIcc c b) x Z := by
    rw [hcenter1]
    refine ⟨hgeo.1, hgeo.2.1, fun s hs ↦ hgeo.2.2 s ?_⟩
    have hs' : s ∈ Icc c b := by
      simpa only [uIcc_of_le hcb.le] using hs
    rw [uIcc_of_le hab.le]
    exact ⟨hac.le.trans hs'.1, hs'.2⟩
  have hfixa : ∀ u : Real, f0 u a = f0 0 a := by
    intro u
    rw [hf00 a]
    exact hzero0 a hY0a u
  have hfixb : ∀ u : Real, f1 u b = f1 0 b := by
    intro u
    rw [hf10 b]
    exact hzero1 b hY1b u
  have hnode : ∀ u : Real, f0 u c = f1 u c :=
    hsame c hYc
  let L : Real → Real := fun u ↦
    lRegAction S T (f0 u) a c + lRegAction S T (f1 u) c b
  have hgammaAll : ContMDiff (modelWithCornersSelf Real Real) I (8 : Nat) gamma := by
    intro s
    exact (Bundle.contMDiffAt_totalSpace.mp (hY0.contMDiffAt (x := s))).1
  have hreg : ∀ s ∈ Icc a b, T - s ^ 2 ∈ D.regular := by
    intro s hs
    exact (hgeo.2.2 s (by
      simpa only [uIcc_of_le hab.le] using hs)).1
  have hLglobal : ∀ u : Real, L 0 ≤ L u := by
    intro u
    have hf0u : ContMDiff (modelWithCornersSelf Real Real) I 1 (f0 u) := by
      exact ((hf0 : ContMDiff _ _ _ _).comp
        (contMDiff_const.prodMk contMDiff_id)).of_le (by norm_num)
    have hf1u : ContMDiff (modelWithCornersSelf Real Real) I 1 (f1 u) := by
      exact ((hf1 : ContMDiff _ _ _ _).comp
        (contMDiff_const.prodMk contMDiff_id)).of_le (by norm_num)
    have hf0on : ContMDiffOn (modelWithCornersSelf Real Real) I 1 (f0 u)
        (Icc a c) := hf0u.contMDiffOn
    have hf1on : ContMDiffOn (modelWithCornersSelf Real Real) I 1 (f1 u)
        (Icc c b) := hf1u.contMDiffOn
    obtain ⟨eta, m, t, p, v, heta0, heta1, htmono, htfirst, htlast,
        _hc, hsrc, hrep⟩ :=
      exists_chartH1_join (E := E) (H := H) (I := I) (M := M)
        a c b hac hcb (f0 u) (f1 u)
        hf0on hf1on (hnode u)
    obtain ⟨alpha, _w, halpha, halphaa, halphab, _hsrcAlpha,
        _hrepAlpha, _hw, _hunif, haction⟩ :=
      lAction_c1_dense (I := I) S hS.smoothMetric ⟨hS.scalarCont⟩
        T a b t htmono htfirst htlast p eta v hsrc hrep hreg
    have hetaA : eta a = gamma a :=
      (heta0 ⟨le_rfl, hac.le⟩).trans (hzero0 a hY0a u)
    have hetaB : eta b = gamma b :=
      (heta1 ⟨hcb.le, le_rfl⟩).trans (hzero1 b hY1b u)
    have hwhole : lRegAction S T gamma a b ≤ lRegAction S T eta a b := by
      apply ge_of_tendsto haction
      exact Eventually.of_forall fun n ↦
        hmin (alpha n) (halpha n) ((halphaa n).trans hetaA)
          ((halphab n).trans hetaB)
    have hgamma0 : ContMDiffOn (modelWithCornersSelf Real Real) I 1 gamma
        (Icc a c) := (hgammaAll.of_le (by norm_num)).contMDiffOn
    have hgamma1 : ContMDiffOn (modelWithCornersSelf Real Real) I 1 gamma
        (Icc c b) := (hgammaAll.of_le (by norm_num)).contMDiffOn
    have hetaHead : ContMDiffOn (modelWithCornersSelf Real Real) I 1 eta
        (Icc a c) := hf0u.contMDiffOn.congr fun s hs ↦ heta0 hs
    have hetaTail : ContMDiffOn (modelWithCornersSelf Real Real) I 1 eta
        (Icc c b) := hf1u.contMDiffOn.congr fun s hs ↦ heta1 hs
    have hreg0 : ∀ s ∈ Icc a c, T - s ^ 2 ∈ D.regular := by
      intro s hs
      exact hreg s ⟨hs.1, hs.2.trans hcb.le⟩
    have hreg1 : ∀ s ∈ Icc c b, T - s ^ 2 ∈ D.regular := by
      intro s hs
      exact hreg s ⟨hac.le.trans hs.1, hs.2⟩
    have hgammaInt0 := lRegLag_int_c1 (I := I) S hS.smoothMetric
      ⟨hS.scalarCont⟩ T a c hac.le gamma hgamma0 hreg0
    have hgammaInt1 := lRegLag_int_c1 (I := I) S hS.smoothMetric
      ⟨hS.scalarCont⟩ T c b hcb.le gamma hgamma1 hreg1
    have hetaInt0 := lRegLag_int_c1 (I := I) S hS.smoothMetric
      ⟨hS.scalarCont⟩ T a c hac.le eta hetaHead hreg0
    have hetaInt1 := lRegLag_int_c1 (I := I) S hS.smoothMetric
      ⟨hS.scalarCont⟩ T c b hcb.le eta hetaTail hreg1
    have hgammaAdd := lRegAction_add (I := I) S T gamma a c b
      hgammaInt0 hgammaInt1
    have hetaAdd := lRegAction_add (I := I) S T eta a c b
      hetaInt0 hetaInt1
    have hetaEq0 : lRegAction S T eta a c =
        lRegAction S T (f0 u) a c := by
      apply lRegAction_congr (I := I) S T
      intro s hs
      have hs' : s ∈ Ioo a c := by
        simpa only [uIoo_of_le hac.le] using hs
      exact heta0 ⟨hs'.1.le, hs'.2.le⟩
    have hetaEq1 : lRegAction S T eta c b =
        lRegAction S T (f1 u) c b := by
      apply lRegAction_congr (I := I) S T
      intro s hs
      have hs' : s ∈ Ioo c b := by
        simpa only [uIoo_of_le hcb.le] using hs
      exact heta1 ⟨hs'.1.le, hs'.2.le⟩
    rw [← hgammaAdd, ← hetaAdd, hetaEq0, hetaEq1] at hwhole
    simpa only [L, hcenter0, hcenter1] using hwhole
  have hLglobal' : IsMinOn L univ 0 := by
    intro u hu
    exact hLglobal u
  have hLmin : IsLocalMin L 0 :=
    hLglobal'.isLocalMin univ_mem
  have hreg0 := fun s hs ↦ (hgeo0.2.2 s hs).1
  have hreg1 := fun s hs ↦ (hgeo1.2.2 s hs).1
  have hfirst0 := lRegAction_deriv (I := I) S hS T f0 hf0 a c hreg0
  have hfirst1 := lRegAction_deriv (I := I) S hS T f1 hf1 c b hreg1
  have hfirst : HasDerivAt L 0 0 := by
    have hraw := hfirst0.add hfirst1
    exact hraw.congr_deriv (hLmin.hasDerivAt_eq_zero hraw)
  have hsecond := nodeAction_second (I := I) S hS T f0 f1 hf0 hf1
    a c b x Z hgeo0 hgeo1 hcenter hfixa hfixb hnode
  have hnonneg := second_deriv_nonneg_of_isLocalMin hLmin hfirst hsecond
  have hEq0 : EqOn
      (fun s : Real ↦ lVelocity (I := I) (fun u : Real ↦ f0 u s) 0)
      Y0 (uIoo a c) := by
    intro s hs
    apply hfield0 s
    have hs' : s ∈ Ioo a c := by
      simpa only [uIoo_of_le hac.le] using hs
    rw [uIcc_of_le hab.le]
    exact ⟨hs'.1.le, (hs'.2.trans hcb).le⟩
  have hEq1 : EqOn
      (fun s : Real ↦ lVelocity (I := I) (fun u : Real ↦ f1 u s) 0)
      Y1 (uIoo c b) := by
    intro s hs
    apply hfield1 s
    have hs' : s ∈ Ioo c b := by
      simpa only [uIoo_of_le hcb.le] using hs
    rw [uIcc_of_le hab.le]
    exact ⟨(hac.trans hs'.1).le, hs'.2.le⟩
  rw [hcenter0, hcenter1,
    lRegIndex_congr (I := I) S T gamma
      (fun s : Real ↦ lVelocity (I := I) (fun u : Real ↦ f0 u s) 0)
      (fun s : Real ↦ lVelocity (I := I) (fun u : Real ↦ f0 u s) 0)
      Y0 Y0 a c hEq0 hEq0,
    lRegIndex_congr (I := I) S T gamma
      (fun s : Real ↦ lVelocity (I := I) (fun u : Real ↦ f1 u s) 0)
      (fun s : Real ↦ lVelocity (I := I) (fun u : Real ↦ f1 u s) 0)
      Y1 Y1 c b hEq1 hEq1] at hnonneg
  linarith

end DifferentialGeometry.PDE.RicciFlow.Perelman
