import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.FirstVariation

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
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Tensor0SBundle
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

omit [InnerProductSpace Real E] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem hasDerivAt_integral_lRegEulerPair_variation
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (f : Real → Real → M) (hf : IsSmoothVariation (I := I) f)
    (a b : Real) (x : M) (Z : TangentSpace I x)
    (hgeo : IsLRegCurveOn S T (f 0) (Set.uIcc a b) x Z) :
    HasDerivAt
      (fun u : Real ↦
        ∫ s in a..b,
          -lRegEulerPair S T (f u) s
            (lVelocity (I := I) (fun v : Real ↦ f v s) u))
      (-(∫ s in a..b,
        lRegJacobiPair S T (f 0)
          (fun r : Real ↦
            lVelocity (I := I) (fun u : Real ↦ f u r) 0)
          s (lVelocity (I := I) (fun u : Real ↦ f u s) 0))) 0 := by
  let U : Set (Real × Real) :=
    {p : Real × Real | T - p.2 ^ 2 ∈ D.regular}
  let F : Real → Real → Real := fun u s ↦
    -lRegEulerPair S T (f u) s
      (lVelocity (I := I) (fun v : Real ↦ f v s) u)
  let dF : Real → Real → Real := fun u s ↦
    fderiv Real (fun p : Real × Real ↦ F p.1 p.2) (u, s) (1, 0)
  let J : Real → Real := fun s ↦
    -lRegJacobiPair S T (f 0)
      (fun r : Real ↦ lVelocity (I := I) (fun u : Real ↦ f u r) 0)
      s (lVelocity (I := I) (fun u : Real ↦ f u s) 0)
  have ht : ∀ s ∈ Set.uIcc a b, T - s ^ 2 ∈ D.regular :=
    fun s hs ↦ (hgeo.2.2 s hs).1
  have hUopen : IsOpen U :=
    D.regular_isOpen.preimage
      (continuous_const.sub (continuous_snd.pow 2))
  have hFJoint : ContDiffOn Real 1
      (fun p : Real × Real ↦ F p.1 p.2) U := by
    simpa only [F, U] using (lRegEulerPair_variation_contDiffOn_one (I := I) S hS T f hf).neg
  have hFContJoint : ContinuousOn
      (fun p : Real × Real ↦ F p.1 p.2) U :=
    hFJoint.continuousOn
  have hfdCont : ContinuousOn
      (fderiv Real (fun p : Real × Real ↦ F p.1 p.2)) U :=
    hFJoint.continuousOn_fderiv_of_isOpen hUopen (by norm_num)
  have hdFJoint : ContinuousOn
      (fun p : Real × Real ↦ dF p.1 p.2) U := by
    simpa only [dF] using hfdCont.clm_apply continuousOn_const
  have hFCont (u : Real) : ContinuousOn (F u) (Set.uIcc a b) := by
    have hmap : ContinuousOn (fun s : Real ↦ (u, s))
        (Set.uIcc a b) := continuousOn_const.prodMk continuousOn_id
    apply hFContJoint.comp hmap
    intro s hs
    exact ht s hs
  have hdFCont (u : Real) : ContinuousOn (dF u) (Set.uIcc a b) := by
    have hmap : ContinuousOn (fun s : Real ↦ (u, s))
        (Set.uIcc a b) := continuousOn_const.prodMk continuousOn_id
    apply hdFJoint.comp hmap
    intro s hs
    exact ht s hs
  have hFDiff : DifferentiableOn Real
      (fun p : Real × Real ↦ F p.1 p.2) U :=
    hFJoint.differentiableOn (by norm_num)
  have hFDeriv (u s : Real) (hs : s ∈ Set.uIcc a b) :
      HasDerivAt (fun z : Real ↦ F z s) (dF u s) u := by
    have hpU : (u, s) ∈ U := ht s hs
    have hFAt : DifferentiableAt Real
        (fun p : Real × Real ↦ F p.1 p.2) (u, s) :=
      (hFDiff (u, s) hpU).differentiableAt (hUopen.mem_nhds hpU)
    simpa only [dF] using Aux2.hasDerivAt_slice_fst
      (fun z r : Real ↦ F z r) u s hFAt
  let K : Set (Real × Real) :=
    Set.Icc (-1 : Real) 1 ×ˢ Set.uIcc a b
  have hKcompact : IsCompact K := by
    simpa only [K] using isCompact_Icc.prod isCompact_uIcc
  have hKsub : K ⊆ U := by
    intro p hp
    exact ht p.2 hp.2
  obtain ⟨C, hC⟩ :=
    hKcompact.bddAbove_image (hdFJoint.mono hKsub).norm
  let C₀ : Real := max C 0
  have hC₀ : ∀ p ∈ K, ‖dF p.1 p.2‖ ≤ C₀ := by
    intro p hp
    exact (hC ⟨p, hp, rfl⟩).trans (le_max_left C 0)
  have hnhds : Set.Icc (-1 : Real) 1 ∈ 𝓝 (0 : Real) :=
    Icc_mem_nhds (by norm_num) (by norm_num)
  have hFmeas : ∀ᶠ u in 𝓝 (0 : Real),
      AEStronglyMeasurable (F u)
        (MeasureTheory.volume.restrict (Set.uIoc a b)) :=
    Filter.Eventually.of_forall fun u ↦
      (hFCont u).aestronglyMeasurable_of_subset_isCompact
        isCompact_uIcc measurableSet_uIoc Set.uIoc_subset_uIcc
  have hFint : IntervalIntegrable (F 0) MeasureTheory.volume a b :=
    (hFCont 0).intervalIntegrable
  have hF'meas : AEStronglyMeasurable (dF 0)
      (MeasureTheory.volume.restrict (Set.uIoc a b)) :=
    (hdFCont 0).aestronglyMeasurable_of_subset_isCompact
      isCompact_uIcc measurableSet_uIoc Set.uIoc_subset_uIcc
  have hbound : ∀ᵐ s ∂MeasureTheory.volume,
      s ∈ Set.uIoc a b → ∀ u ∈ Set.Icc (-1 : Real) 1,
        ‖dF u s‖ ≤ (fun _ : Real ↦ C₀) s :=
    Filter.Eventually.of_forall fun s hs u hu ↦
      hC₀ (u, s) ⟨hu, Set.uIoc_subset_uIcc hs⟩
  have hboundInt : IntervalIntegrable (fun _ : Real ↦ C₀)
      MeasureTheory.volume a b := continuousOn_const.intervalIntegrable
  have hdiff : ∀ᵐ s ∂MeasureTheory.volume,
      s ∈ Set.uIoc a b → ∀ u ∈ Set.Icc (-1 : Real) 1,
        HasDerivAt (fun z : Real ↦ F z s) (dF u s) u :=
    Filter.Eventually.of_forall fun s hs u _ ↦
      hFDeriv u s (Set.uIoc_subset_uIcc hs)
  have hparam :=
    intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := F) (F' := dF) (x₀ := (0 : Real))
      (s := Set.Icc (-1 : Real) 1) (a := a) (b := b)
      (bound := fun _ : Real ↦ C₀) hnhds hFmeas hFint hF'meas
      hbound hboundInt hdiff
  have hJEq : Set.EqOn (dF 0) J (Set.uIcc a b) := by
    intro s hs
    let W : (u : Real) → TangentSpace I (f u s) := fun u ↦
      lVelocity (I := I) (fun v : Real ↦ f v s) u
    have hfAt : ContMDiffAt
        (𝓘(Real, Real).prod 𝓘(Real, Real)) I 3
        (fun p : Real × Real ↦ f p.1 p.2) (0, s) :=
      (hf : ContMDiff _ _ _ _).contMDiffAt.of_le (by norm_num)
    have hslice : ContMDiffAt 𝓘(Real, Real) I 2
        (fun u : Real ↦ f u s) 0 := by
      have hincl : ContMDiff 𝓘(Real, Real)
          (𝓘(Real, Real).prod 𝓘(Real, Real)) (8 : Nat)
          (fun u : Real ↦ (u, s)) :=
        contMDiff_id.prodMk contMDiff_const
      have hcomp := (hf : ContMDiff _ _ (8 : Nat) _).comp hincl
      exact hcomp.contMDiffAt.of_le (by norm_num)
    have hW : DifferentiableAt Real
        (chartRepAt (I := I) (fun u : Real ↦ f u s) W 0) 0 := by
      with_unfolding_all exact
        (DifferentialGeometry.Geometry.Riemannian.MFDerivAlongCurve.velocity_coord_diff
          (I := I) (fun u : Real ↦ f u s) 0 hslice)
    have hpoint := lRegEuler_deriv (I := I) S T s f W hfAt hW
    have hzero :
        lRegEulerPair S T (f 0) s
          (covDerivAlong (I := I) (S.base.metric (T - s ^ 2))
            (fun u : Real ↦ f u s) W 0) = 0 := by
      simp only [lRegEulerPair]
      rw [(hgeo.2.2 s hs).2.2.2, sub_self, map_zero]
    rw [hzero, add_zero] at hpoint
    have hneg : HasDerivAt (fun u : Real ↦ F u s) (J s) 0 := by
      with_unfolding_all exact hpoint.neg
    exact (hFDeriv 0 s hs).unique hneg
  have hint : (∫ s in a..b, dF 0 s) = ∫ s in a..b, J s :=
    intervalIntegral.integral_congr hJEq
  rw [hint] at hparam
  simpa only [F, J, intervalIntegral.integral_neg] using hparam.2

omit [InnerProductSpace Real E] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem hasDerivAt_deriv_lRegAction
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (f : Real → Real → M) (hf : IsSmoothVariation (I := I) f)
    (a b : Real) (x : M) (Z : TangentSpace I x)
    (hgeo : IsLRegCurveOn S T (f 0) (Set.uIcc a b) x Z)
    (hfixa : ∀ u : Real, f u a = f 0 a)
    (hfixb : ∀ u : Real, f u b = f 0 b) :
    HasDerivAt
      (fun u : Real ↦
        deriv (fun v : Real ↦ lRegAction S T (f v) a b) u)
      (-(∫ s in a..b,
        lRegJacobiPair S T (f 0)
          (fun r : Real ↦
            lVelocity (I := I) (fun u : Real ↦ f u r) 0)
          s (lVelocity (I := I) (fun u : Real ↦ f u s) 0))) 0 := by
  let L : Real → Real := fun u ↦ lRegAction S T (f u) a b
  let Eul : Real → Real := fun u ↦
    ∫ s in a..b,
      -lRegEulerPair S T (f u) s
        (lVelocity (I := I) (fun v : Real ↦ f v s) u)
  have ht : ∀ s ∈ Set.uIcc a b, T - s ^ 2 ∈ D.regular :=
    fun s hs ↦ (hgeo.2.2 s hs).1
  have hderivEq (u : Real) : deriv L u = Eul u := by
    let fu : Real → Real → M := fun v s ↦ f (u + v) s
    have hfu : IsSmoothVariation (I := I) fu := by
      exact (hf : ContMDiff _ _ (8 : Nat) _).comp
        ((contMDiff_const.add contMDiff_fst).prodMk contMDiff_snd)
    have hfu0 : fu 0 = f u := by
      funext s
      simp only [fu, add_zero]
    have hYshift (s : Real) :
        lVelocity (I := I) (fun v : Real ↦ fu v s) 0 =
          lVelocity (I := I) (fun v : Real ↦ f v s) u := by
      simpa only [fu, lVelocity, varFst] using
        varFst_shift (I := I) f hf u s
    have hYa :
        lVelocity (I := I) (fun v : Real ↦ fu v a) 0 = 0 := by
      have hconst : (fun v : Real ↦ fu v a) = fun _ : Real ↦ f 0 a := by
        funext v
        exact hfixa (u + v)
      rw [hconst]
      simp only [lVelocity, mfderiv_const]
      rfl
    have hYb :
        lVelocity (I := I) (fun v : Real ↦ fu v b) 0 = 0 := by
      have hconst : (fun v : Real ↦ fu v b) = fun _ : Real ↦ f 0 b := by
        funext v
        exact hfixb (u + v)
      rw [hconst]
      simp only [lVelocity, mfderiv_const]
      rfl
    have hshift := lRegAction_first_variation (I := I) S hS T fu hfu a b ht
    rw [hYa, hYb] at hshift
    simp only [map_zero, zero_apply, sub_self, zero_sub]
      at hshift
    rw [hfu0] at hshift
    have hshift' : HasDerivAt (fun v : Real ↦ L (u + v)) (Eul u) 0 := by
      with_unfolding_all
        simpa only [L, Eul, fu, hYshift, intervalIntegral.integral_neg]
          using hshift
    have hderiv := hshift'.deriv
    rw [deriv_comp_const_add L u 0, add_zero] at hderiv
    exact hderiv
  have hEul := hasDerivAt_integral_lRegEulerPair_variation (I := I) S hS T f hf a b x Z hgeo
  have hfun : (fun u : Real ↦ deriv L u) = Eul :=
    funext hderivEq
  rw [hfun]
  simpa only [L, Eul] using hEul

omit [InnerProductSpace Real E] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem continuousOn_lRegJacobiPair_variation
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (f : Real → Real → M) (hf : IsSmoothVariation (I := I) f)
    (a b : Real) (x : M) (Z : TangentSpace I x)
    (hgeo : IsLRegCurveOn S T (f 0) (Set.uIcc a b) x Z) :
    ContinuousOn
      (fun s : Real ↦
        lRegJacobiPair S T (f 0)
          (fun r : Real ↦
            lVelocity (I := I) (fun u : Real ↦ f u r) 0)
          s (lVelocity (I := I) (fun u : Real ↦ f u s) 0))
      (Set.uIcc a b) := by
  let U : Set (Real × Real) :=
    {p : Real × Real | T - p.2 ^ 2 ∈ D.regular}
  let Eul : Real × Real → Real := fun p ↦
    lRegEulerPair S T (f p.1) p.2
      (lVelocity (I := I) (fun u : Real ↦ f u p.2) p.1)
  let dEul : Real → Real := fun s ↦
    fderiv Real Eul (0, s) (1, 0)
  let J : Real → Real := fun s ↦
    lRegJacobiPair S T (f 0)
      (fun r : Real ↦ lVelocity (I := I) (fun u : Real ↦ f u r) 0)
      s (lVelocity (I := I) (fun u : Real ↦ f u s) 0)
  have ht : ∀ s ∈ Set.uIcc a b, T - s ^ 2 ∈ D.regular :=
    fun s hs ↦ (hgeo.2.2 s hs).1
  have hUopen : IsOpen U :=
    D.regular_isOpen.preimage
      (continuous_const.sub (continuous_snd.pow 2))
  have hEul1 : ContDiffOn Real 1 Eul U := by
    simpa only [Eul, U] using lRegEulerPair_variation_contDiffOn_one (I := I) S hS T f hf
  have hEulDiff : DifferentiableOn Real Eul U :=
    hEul1.differentiableOn (by norm_num)
  have hdJoint : ContinuousOn
      (fun p : Real × Real ↦ fderiv Real Eul p (1, 0)) U :=
    (hEul1.continuousOn_fderiv_of_isOpen hUopen (by norm_num)).clm_apply
      continuousOn_const
  have hdCont : ContinuousOn dEul (Set.uIcc a b) := by
    have hmap : ContinuousOn (fun s : Real ↦ ((0 : Real), s))
        (Set.uIcc a b) := continuousOn_const.prodMk continuousOn_id
    apply hdJoint.comp hmap
    intro s hs
    exact ht s hs
  have hslice : ∀ s ∈ Set.uIcc a b,
      HasDerivAt (fun u : Real ↦ Eul (u, s)) (dEul s) 0 := by
    intro s hs
    have hp : ((0 : Real), s) ∈ U := ht s hs
    have hat : DifferentiableAt Real Eul (0, s) :=
      (hEulDiff (0, s) hp).differentiableAt (hUopen.mem_nhds hp)
    simpa only [dEul] using Aux2.hasDerivAt_slice_fst
      (fun u r : Real ↦ Eul (u, r)) 0 s hat
  have hdEq : ∀ s ∈ Set.uIcc a b, dEul s = J s := by
    intro s hs
    let W : (u : Real) → TangentSpace I (f u s) := fun u ↦
      lVelocity (I := I) (fun v : Real ↦ f v s) u
    have hfAt : ContMDiffAt
        (𝓘(Real, Real).prod 𝓘(Real, Real)) I 3
        (fun p : Real × Real ↦ f p.1 p.2) (0, s) :=
      (hf : ContMDiff _ _ _ _).contMDiffAt.of_le (by norm_num)
    have hline : ContMDiffAt 𝓘(Real, Real) I 2
        (fun u : Real ↦ f u s) 0 := by
      have hincl : ContMDiff 𝓘(Real, Real)
          (𝓘(Real, Real).prod 𝓘(Real, Real)) (8 : Nat)
          (fun u : Real ↦ (u, s)) :=
        contMDiff_id.prodMk contMDiff_const
      exact ((hf : ContMDiff _ _ _ _).comp hincl).contMDiffAt.of_le
        (by norm_num)
    have hW : DifferentiableAt Real
        (chartRepAt (I := I) (fun u : Real ↦ f u s) W 0) 0 := by
      with_unfolding_all exact
        (DifferentialGeometry.Geometry.Riemannian.MFDerivAlongCurve.velocity_coord_diff
          (I := I) (fun u : Real ↦ f u s) 0 hline)
    have hpoint := lRegEuler_deriv (I := I) S T s f W hfAt hW
    have hzero :
        lRegEulerPair S T (f 0) s
          (covDerivAlong (I := I) (S.base.metric (T - s ^ 2))
            (fun u : Real ↦ f u s) W 0) = 0 := by
      simp only [lRegEulerPair]
      rw [(hgeo.2.2 s hs).2.2.2, sub_self, map_zero]
    rw [hzero, add_zero] at hpoint
    have hpoint' : HasDerivAt (fun u : Real ↦ Eul (u, s)) (J s) 0 := by
      simpa only [Eul, J, W] using hpoint
    exact (hslice s hs).unique hpoint'
  exact hdCont.congr (fun s hs ↦ (hdEq s hs).symm)

omit [InnerProductSpace Real E] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem lRegAction_second_variation
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (f : Real → Real → M) (hf : IsSmoothVariation (I := I) f)
    (a b : Real) (x : M) (Z : TangentSpace I x)
    (hgeo : IsLRegCurveOn S T (f 0) (Set.uIcc a b) x Z)
    (hfixa : ∀ u : Real, f u a = f 0 a)
    (hfixb : ∀ u : Real, f u b = f 0 b) :
    HasDerivAt
      (fun u : Real ↦
        deriv (fun v : Real ↦ lRegAction S T (f v) a b) u)
      (2 * lRegIndex S T (f 0)
        (fun s : Real ↦
          lVelocity (I := I) (fun u : Real ↦ f u s) 0)
        (fun s : Real ↦
          lVelocity (I := I) (fun u : Real ↦ f u s) 0) a b) 0 := by
  let alpha : Real → M := f 0
  let Y : (s : Real) → TangentSpace I (alpha s) := fun s ↦
    lVelocity (I := I) (fun u : Real ↦ f u s) 0
  let B : Real → Real := fun s ↦
    (S.base.metric (T - s ^ 2)).inner (alpha s)
      (covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) alpha Y s)
      (Y s)
  let J : Real → Real := fun s ↦
    lRegJacobiPair S T alpha Y s (Y s)
  let G : Real → Real := lRegIndexInt S T alpha Y Y
  let V : Set Real := {s : Real | T - s ^ 2 ∈ D.regular}
  let W : Set (Real × Real) :=
    {p : Real × Real | T - p.1 ∈ D.regular}
  let Q : Real × Real → Real := fun p ↦
    (S.base.metric (T - p.1)).inner (alpha p.2) (Y p.2) (Y p.2)
  let dQ : Real × Real → Real := fun p ↦
    fderiv Real Q p (0, 1)
  let Braw : Real → Real := fun s ↦ dQ (s ^ 2, s) / 2
  have ht : ∀ s ∈ Set.uIcc a b, T - s ^ 2 ∈ D.regular :=
    fun s hs ↦ (hgeo.2.2 s hs).1
  have halphaAll : ContMDiff 𝓘(Real, Real) I (8 : Nat) alpha := by
    exact (hf : ContMDiff _ _ (8 : Nat) _).comp
      (contMDiff_const.prodMk contMDiff_id)
  have halpha : ∀ s ∈ Set.uIcc a b, ∀ᶠ r in nhds s,
      MDifferentiableAt (modelWithCornersSelf Real Real) I alpha r := by
    intro s _
    exact Filter.Eventually.of_forall fun r ↦
      halphaAll.mdifferentiableAt (by norm_num)
  have hA : ∀ s ∈ Set.uIcc a b, DifferentiableAt Real
      (chartRepAt (I := I) alpha
        (fun r : Real ↦ lVelocity (I := I) alpha r) s) s := by
    intro s hs
    simpa only [alpha] using (hgeo.2.2 s hs).2.2.1
  have hY : ∀ s ∈ Set.uIcc a b, DifferentiableAt Real
      (chartRepAt (I := I) alpha Y s) s := by
    intro s _
    simpa only [alpha, Y] using
      (lRegVar_reg (I := I) S T s f hf).2.1
  have hZ : ∀ s ∈ Set.uIcc a b, DifferentiableAt Real
      (chartRepAt (I := I) alpha
        (fun r : Real ↦ covDerivAlong (I := I)
          (S.base.metric (T - s ^ 2)) alpha Y r) s) s := by
    intro s _
    simpa only [alpha, Y] using
      (lRegVar_reg (I := I) S T s f hf).2.2
  have hJcont : ContinuousOn J (Set.uIcc a b) := by
    simpa only [J, alpha, Y] using
      continuousOn_lRegJacobiPair_variation (I := I) S hS T f hf a b x Z hgeo
  have hJint : IntervalIntegrable J MeasureTheory.volume a b :=
    hJcont.intervalIntegrable
  have hVopen : IsOpen V :=
    D.regular_isOpen.preimage
      (continuous_const.sub (continuous_id.pow 2))
  have hWopen : IsOpen W :=
    D.regular_isOpen.preimage (continuous_const.sub continuous_fst)
  have hQ2 : ContDiffOn Real 2 Q W := by
    simpa only [Q, W, alpha, Y] using
      lVarMetric_c2 (I := I) S T f hS.smoothMetric hf 0
  have hdQ : ContDiffOn Real 1 dQ W := by
    have hfd : ContDiffOn Real 1 (fderiv Real Q) W :=
      hQ2.fderiv_of_isOpen hWopen (by norm_num)
    simpa only [dQ] using hfd.clm_apply contDiffOn_const
  have hphi : ContDiffOn Real 1 (fun s : Real ↦ (s ^ 2, s)) V :=
    (contDiffOn_id.pow 2).prodMk contDiffOn_id
  have hdComp : ContDiffOn Real 1
      (fun s : Real ↦ dQ (s ^ 2, s)) V :=
    hdQ.comp hphi (fun s hs ↦ hs)
  have hBraw1 : ContDiffOn Real 1 Braw V := by
    simpa only [Braw] using hdComp.div_const 2
  have hQDiff : DifferentiableOn Real Q W :=
    hQ2.differentiableOn (by norm_num)
  have hBeq : Set.EqOn B Braw V := by
    intro s hs
    have hpW : (s ^ 2, s) ∈ W := hs
    have hQAt : DifferentiableAt Real Q (s ^ 2, s) :=
      (hQDiff (s ^ 2, s) hpW).differentiableAt
        (hWopen.mem_nhds hpW)
    have hslice : HasDerivAt
        (fun r : Real ↦ Q (s ^ 2, r)) (dQ (s ^ 2, s)) s := by
      simpa only [dQ] using Aux2.hasDerivAt_slice_snd
        (fun u r : Real ↦ Q (u, r)) (s ^ 2) s hQAt
    have hYs : DifferentiableAt Real
        (chartRepAt (I := I) alpha Y s) s := by
      simpa only [alpha, Y] using
        (lRegVar_reg (I := I) S T s f hf).2.1
    have hinner := inner_deriv_at
      (I := I) (n := (8 : WithTop ENat)) (by norm_num)
      (S.base.metric (T - s ^ 2)) alpha Y Y s
      halphaAll.contMDiffAt hYs hYs
    have hdQEq : dQ (s ^ 2, s) = 2 * B s := by
      have heq := hslice.unique (by
        simpa only [Q] using hinner)
      rw [heq]
      simp only [B]
      rw [(S.base.metric (T - s ^ 2)).symm]
      ring
    dsimp only [Braw]
    rw [hdQEq]
    ring
  have hB1 : ContDiffOn Real 1 B V :=
    hBraw1.congr (fun s hs ↦ hBeq hs)
  have hdBcont : ContinuousOn (deriv B) (Set.uIcc a b) :=
    (hB1.continuousOn_deriv_of_isOpen hVopen (by norm_num)).mono
      (fun s hs ↦ ht s hs)
  have hbal : ∀ s ∈ Set.uIcc a b,
      HasDerivAt B (2 * G s + J s) s := by
    intro s hs
    simpa only [B, G, J] using
      lRegIndex_balance (I := I) S hS T alpha Y Y s (ht s hs)
        (halpha s hs) (hA s hs) (hY s hs) (hZ s hs) (hY s hs)
  let Graw : Real → Real := fun s ↦ (deriv B s - J s) / 2
  have hGrawCont : ContinuousOn Graw (Set.uIcc a b) := by
    exact (hdBcont.sub hJcont).div_const 2
  have hGeq : Set.EqOn G Graw (Set.uIcc a b) := by
    intro s hs
    dsimp only [Graw]
    have hderiv := (hbal s hs).deriv
    linarith
  have hGcont : ContinuousOn G (Set.uIcc a b) :=
    hGrawCont.congr (fun s hs ↦ hGeq hs)
  have hIint : IntervalIntegrable G MeasureTheory.volume a b :=
    hGcont.intervalIntegrable
  have hYa : Y a = 0 := by
    have hconst : (fun u : Real ↦ f u a) = fun _ : Real ↦ f 0 a := by
      funext u
      exact hfixa u
    simp only [Y, alpha]
    rw [hconst]
    simp only [lVelocity, mfderiv_const]
    rfl
  have hYb : Y b = 0 := by
    have hconst : (fun u : Real ↦ f u b) = fun _ : Real ↦ f 0 b := by
      funext u
      exact hfixb u
    simp only [Y, alpha]
    rw [hconst]
    simp only [lVelocity, mfderiv_const]
    rfl
  have hindex := lRegIndex_zero_ends (I := I) S hS T alpha Y Y a b ht
    halpha hA hY hZ hY hIint hJint hYa hYb
  have hjac := hasDerivAt_deriv_lRegAction (I := I) S hS T f hf a b x Z hgeo hfixa hfixb
  apply hjac.congr_deriv
  symm
  simpa only [alpha, Y, G, J] using (by
    rw [hindex]
    ring : 2 * lRegIndex S T alpha Y Y a b = -(∫ s in a..b, J s))

end DifferentialGeometry.PDE.RicciFlow.Perelman
