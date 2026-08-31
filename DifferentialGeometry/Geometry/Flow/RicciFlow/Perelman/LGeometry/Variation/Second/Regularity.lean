import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Jacobi.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Variation.First
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Ricci.ConnectionBackward
import DifferentialGeometry.Geometry.Connection.ParallelTransport.CovariantDerivativeDifference
import DifferentialGeometry.Geometry.Connection.ParallelTransport.MFDerivAlongCurve

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
private theorem hasDerivAt_lEulerPair_variation_at_sq
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    (f : Real → Real → M) (hf : IsSmoothVariation (I := I) f)
    (s : Real) (hs : 0 < s) (ht : T - s ^ 2 ∈ D.regular)
    (W : (u : Real) → TangentSpace I (f u (s ^ 2)))
    (hW : DifferentiableAt Real
      (chartRepAt (I := I) (fun u ↦ f u (s ^ 2)) W 0) 0) :
    HasDerivAt
      (fun u : Real ↦ lEulerPair S T (f u) (s ^ 2) (W u))
      (lJacobiPair S T (f 0)
          (fun tau ↦ lVelocity (I := I) (fun u ↦ f u tau) 0)
          (s ^ 2) (W 0) +
        lEulerPair S T (f 0) (s ^ 2)
          (covDerivAlong (I := I) (S.base.metric (T - s ^ 2))
            (fun u ↦ f u (s ^ 2)) W 0))
      0 := by
  classical
  let F : Real → Real → M := fun u r ↦ f u (r ^ 2)
  let gamma : Real → M := fun tau ↦ f 0 tau
  let Y : (tau : Real) → TangentSpace I (gamma tau) :=
    fun tau ↦ lVelocity (I := I) (fun u ↦ f u tau) 0
  let c : Real := 4 * s ^ 2
  have hF : IsSmoothVariation (I := I) F := by
    exact (hf : ContMDiff _ _ _ _).comp
      (contMDiff_fst.prodMk (contMDiff_snd.pow 2))
  have hFat : ContMDiffAt
      (𝓘(Real, Real).prod 𝓘(Real, Real)) I 3
      (fun q : Real × Real ↦ F q.1 q.2) (0, s) :=
    (hF : ContMDiff _ _ _ _).contMDiffAt.of_le (by norm_num)
  have hWreg : DifferentiableAt Real
      (chartRepAt (I := I) (fun u ↦ F u s) W 0) 0 := by
    simpa only [F] using hW
  have hreg := lRegEuler_deriv (I := I) S T s F W hFat hWreg
  let DW : TangentSpace I (f 0 (s ^ 2)) :=
    covDerivAlong (I := I) (S.base.metric (T - s ^ 2))
      (fun u ↦ f u (s ^ 2)) W 0
  have hgamma : ContMDiff 𝓘(Real, Real) I (8 : Nat) gamma := by
    exact (hf : ContMDiff _ _ _ _).comp
      (contMDiff_const.prodMk contMDiff_id)
  have hgamma_sq : ∀ᶠ r in nhds s,
      MDifferentiableAt 𝓘(Real, Real) I gamma (r ^ 2) :=
    Filter.Eventually.of_forall (fun _ ↦
      hgamma.mdifferentiableAt (by norm_num))
  have hY_sq : ∀ᶠ r in nhds s,
      DifferentiableAt Real
        (chartRepAt (I := I) gamma Y (r ^ 2)) (r ^ 2) := by
    apply Filter.Eventually.of_forall
    intro r
    simpa only [gamma, Y, lVelocity, varFst] using
      variationField_chartRep_differentiableAt
        (I := I) f hf (r ^ 2)
  have hF0 : ContMDiff 𝓘(Real, Real) I (8 : Nat) (F 0) := by
    exact (hF : ContMDiff _ _ _ _).comp
      (contMDiff_const.prodMk contMDiff_id)
  have hF02 : ContMDiffAt 𝓘(Real, Real) I 2 (F 0) s :=
    hF0.contMDiffAt.of_le (by norm_num)
  have hA : DifferentiableAt Real
      (chartRepAt (I := I) (F 0)
        (fun r : Real ↦ lVelocity (I := I) (F 0) r) s) s := by
    exact differentiableAt_chartRepAt_lVelocity (I := I) (F 0) s hF02
  have hA_sq : DifferentiableAt Real
      (chartRepAt (I := I) (squareReparametrization gamma)
        (fun r : Real ↦ lVelocity (I := I) (squareReparametrization gamma) r) s) s := by
    change DifferentiableAt Real
      (chartRepAt (I := I) (F 0)
        (fun r : Real ↦ lVelocity (I := I) (F 0) r) s) s
    exact hA
  rcases lRegVar_reg (I := I) S T s F hF with
    ⟨_, _, hZraw⟩
  have hZ : DifferentiableAt Real
      (chartRepAt (I := I) (squareReparametrization gamma)
        (fun r : Real ↦
          covDerivAlong (I := I) (S.base.metric (T - s ^ 2))
            (squareReparametrization gamma) (fun u : Real ↦ Y (u ^ 2)) r) s) s := by
    change DifferentiableAt Real
      (chartRepAt (I := I) (F 0)
        (fun r : Real ↦ covDerivAlong (I := I)
          (S.base.metric (T - s ^ 2)) (F 0)
          (fun u : Real ↦ lVelocity (I := I) (fun v : Real ↦ F v u) 0) r)
        s) s
    exact hZraw
  have hDY := differentiableAt_chartRepAt_lJacobiVelocity_of_squareReparametrization (I := I) S hS T gamma Y s hs ht
    hgamma_sq hY_sq hA_sq hZ
  have hpairRaw := lJacobiPair_squareReparametrization (I := I) S hS T gamma Y s hs ht
    hgamma_sq hY_sq hA_sq hDY hZ (W 0)
  have hpair :
      c * lJacobiPair S T gamma Y (s ^ 2) (W 0) =
        lRegJacobiPair S T (F 0)
          (fun r ↦ lVelocity (I := I) (fun u ↦ F u r) 0) s (W 0) := by
    change c * lJacobiPair S T gamma Y (s ^ 2) (W 0) =
      lRegJacobiPair S T (squareReparametrization gamma)
        (fun r ↦ lVelocity (I := I) (fun u ↦ F u r) 0) s (W 0)
    simpa only [c, F, gamma, Y] using hpairRaw
  have hcurve (u : Real) :
      ContMDiff 𝓘(Real, Real) I (8 : Nat) (f u) := by
    exact (hf : ContMDiff _ _ _ _).comp
      (contMDiff_const.prodMk contMDiff_id)
  have htail :
      c * lEulerPair S T gamma (s ^ 2) DW =
        lRegEulerPair S T (F 0) s
          (covDerivAlong (I := I) (S.base.metric (T - s ^ 2))
            (fun u ↦ F u s) W 0) := by
    change c * lEulerPair S T gamma (s ^ 2) DW =
      lRegEulerPair S T (squareReparametrization gamma) s
        (covDerivAlong (I := I) (S.base.metric (T - s ^ 2))
          (fun u ↦ F u s) W 0)
    simpa only [c] using
      lRegEuler_sq (I := I) S T gamma s DW hs
        (hgamma.mdifferentiableAt (by norm_num))
        (differentiableAt_chartRepAt_lVelocity (I := I) gamma (s ^ 2)
          (hgamma.contMDiffAt.of_le (by norm_num)))
  have hscale (u : Real) :
      c * lEulerPair S T (f u) (s ^ 2) (W u) =
        lRegEulerPair S T (F u) s (W u) := by
    change c * lEulerPair S T (f u) (s ^ 2) (W u) =
      lRegEulerPair S T (squareReparametrization (f u)) s (W u)
    simpa only [c] using
      lRegEuler_sq (I := I) S T (f u) s (W u) hs
        ((hcurve u).mdifferentiableAt (by norm_num))
        (differentiableAt_chartRepAt_lVelocity (I := I) (f u) (s ^ 2)
          ((hcurve u).contMDiffAt.of_le (by norm_num)))
  have hfun :
      (fun u : Real ↦ lRegEulerPair S T (F u) s (W u)) =
        fun u : Real ↦ c * lEulerPair S T (f u) (s ^ 2) (W u) := by
    funext u
    exact (hscale u).symm
  have hscaled : HasDerivAt
      (fun u : Real ↦ c * lEulerPair S T (f u) (s ^ 2) (W u))
      (c * (lJacobiPair S T gamma Y (s ^ 2) (W 0) +
        lEulerPair S T gamma (s ^ 2) DW)) 0 := by
    rw [← hfun]
    simpa only [mul_add, hpair, htail] using hreg
  have hc : c ≠ 0 := by
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hs.ne')
  simpa only [← mul_assoc, inv_mul_cancel₀ hc, one_mul, gamma, Y, DW] using
    hscaled.const_mul c⁻¹

omit [InnerProductSpace Real E] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem hasDerivAt_lEulerPair_variation
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    (f : Real → Real → M) (hf : IsSmoothVariation (I := I) f)
    (tau : Real) (hpos : 0 < tau) (ht : T - tau ∈ D.regular)
    (W : (u : Real) → TangentSpace I (f u tau))
    (hW : DifferentiableAt Real
      (chartRepAt (I := I) (fun u ↦ f u tau) W 0) 0) :
    HasDerivAt
      (fun u : Real ↦ lEulerPair S T (f u) tau (W u))
      (lJacobiPair S T (f 0)
          (fun r ↦ lVelocity (I := I) (fun u ↦ f u r) 0)
          tau (W 0) +
        lEulerPair S T (f 0) tau
          (covDerivAlong (I := I) (S.base.metric (T - tau))
            (fun u ↦ f u tau) W 0))
      0 := by
  generalize hsdef : Real.sqrt tau = s
  have hs : 0 < s := by
    rw [← hsdef]
    exact Real.sqrt_pos.2 hpos
  have hsq : s ^ 2 = tau := by
    rw [← hsdef]
    exact Real.sq_sqrt hpos.le
  cases hsq
  exact hasDerivAt_lEulerPair_variation_at_sq (I := I) S hS T f hf s hs ht W hW

omit [InnerProductSpace Real E] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem hasDerivAt_lEulerPair_variation_of_hasLEquationAt
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    (f : Real → Real → M) (hf : IsSmoothVariation (I := I) f)
    (tau : Real) (hpos : 0 < tau) (ht : T - tau ∈ D.regular)
    (W : (u : Real) → TangentSpace I (f u tau))
    (hW : DifferentiableAt Real
      (chartRepAt (I := I) (fun u ↦ f u tau) W 0) 0)
    (hgeo : HasLEquationAt S T (f 0) tau) :
    HasDerivAt
      (fun u : Real ↦ lEulerPair S T (f u) tau (W u))
      (lJacobiPair S T (f 0)
        (fun r ↦ lVelocity (I := I) (fun u ↦ f u r) 0)
        tau (W 0))
      0 := by
  have hfull := hasDerivAt_lEulerPair_variation (I := I)
    S hS T f hf tau hpos ht W hW
  have hzero :
      lEulerPair S T (f 0) tau
        (covDerivAlong (I := I) (S.base.metric (T - tau))
          (fun u ↦ f u tau) W 0) = 0 :=
    hgeo.2.2 _
  simpa only [hzero, add_zero] using hfull

omit [InnerProductSpace Real E] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem hasDerivAt_integral_lEulerPair_variation
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    (f : Real → Real → M) (hf : IsSmoothVariation (I := I) f)
    (a b : Real)
    (hgeo : IsLGeodesic S T (f 0) (Set.uIcc a b)) :
    HasDerivAt
      (fun u : Real =>
        ∫ tau in a..b,
          (-2 * Real.sqrt tau) *
            lEulerPair S T (f u) tau
              (lVelocity (I := I) (fun v : Real => f v tau) u))
      (∫ tau in a..b,
        (-2 * Real.sqrt tau) *
          lJacobiPair S T (f 0)
            (fun r : Real =>
              lVelocity (I := I) (fun u : Real => f u r) 0)
            tau
            (lVelocity (I := I) (fun u : Real => f u tau) 0))
      0 := by
  let U : Set (Real × Real) :=
    {p : Real × Real | 0 < p.2 ∧ T - p.2 ∈ D.regular}
  let F : Real → Real → Real := fun u tau =>
    (-2 * Real.sqrt tau) *
      lEulerPair S T (f u) tau
        (lVelocity (I := I) (fun v : Real => f v tau) u)
  let dF : Real → Real → Real := fun u tau =>
    fderiv Real (fun p : Real × Real => F p.1 p.2) (u, tau) (1, 0)
  let J : Real → Real := fun tau =>
    (-2 * Real.sqrt tau) *
      lJacobiPair S T (f 0)
        (fun r : Real =>
          lVelocity (I := I) (fun u : Real => f u r) 0)
        tau (lVelocity (I := I) (fun u : Real => f u tau) 0)
  have hpos : 0 < min a b :=
    lt_min (hgeo.pos Set.left_mem_uIcc) (hgeo.pos Set.right_mem_uIcc)
  have ht : ∀ tau ∈ Set.uIcc a b, T - tau ∈ D.regular :=
    fun tau htau => hgeo.regular htau
  have hUopen : IsOpen U := by
    change IsOpen
      ({p : Real × Real | 0 < p.2} ∩
        {p : Real × Real | T - p.2 ∈ D.regular})
    exact (isOpen_lt continuous_const continuous_snd).inter
      (D.regular_isOpen.preimage (continuous_const.sub continuous_snd))
  have hFJoint : ContDiffOn Real 1
      (fun p : Real × Real => F p.1 p.2) U := by
    simpa only [F, U] using lEuler_var_c1 S hS T f hf
  have hFContJoint : ContinuousOn
      (fun p : Real × Real => F p.1 p.2) U :=
    hFJoint.continuousOn
  have hfdCont : ContinuousOn
      (fderiv Real (fun p : Real × Real => F p.1 p.2)) U :=
    hFJoint.continuousOn_fderiv_of_isOpen hUopen (by norm_num)
  have hdFJoint : ContinuousOn
      (fun p : Real × Real => dF p.1 p.2) U := by
    simpa only [dF] using hfdCont.clm_apply continuousOn_const
  have hFCont (u : Real) : ContinuousOn (F u) (Set.uIcc a b) := by
    have hmap : ContinuousOn (fun tau : Real => (u, tau))
        (Set.uIcc a b) := continuousOn_const.prodMk continuousOn_id
    apply hFContJoint.comp hmap
    intro tau htau
    exact ⟨lt_of_lt_of_le hpos htau.1, ht tau htau⟩
  have hdFCont (u : Real) : ContinuousOn (dF u) (Set.uIcc a b) := by
    have hmap : ContinuousOn (fun tau : Real => (u, tau))
        (Set.uIcc a b) := continuousOn_const.prodMk continuousOn_id
    apply hdFJoint.comp hmap
    intro tau htau
    exact ⟨lt_of_lt_of_le hpos htau.1, ht tau htau⟩
  have hFDiff : DifferentiableOn Real
      (fun p : Real × Real => F p.1 p.2) U :=
    hFJoint.differentiableOn (by norm_num)
  have hFDeriv (u tau : Real) (htau : tau ∈ Set.uIcc a b) :
      HasDerivAt (fun z : Real => F z tau) (dF u tau) u := by
    have hpU : (u, tau) ∈ U :=
      ⟨lt_of_lt_of_le hpos htau.1, ht tau htau⟩
    have hFAt : DifferentiableAt Real
        (fun p : Real × Real => F p.1 p.2) (u, tau) :=
      (hFDiff (u, tau) hpU).differentiableAt (hUopen.mem_nhds hpU)
    simpa only [dF] using Aux2.hasDerivAt_slice_fst
      (fun z s : Real => F z s) u tau hFAt
  let K : Set (Real × Real) :=
    Set.Icc (-1 : Real) 1 ×ˢ Set.uIcc a b
  have hKcompact : IsCompact K := by
    simpa only [K] using isCompact_Icc.prod isCompact_uIcc
  have hKsub : K ⊆ U := by
    intro p hp
    exact ⟨lt_of_lt_of_le hpos hp.2.1, ht p.2 hp.2⟩
  obtain ⟨C, hC⟩ :=
    hKcompact.bddAbove_image (hdFJoint.mono hKsub).norm
  let C₀ : Real := max C 0
  have hC₀ : ∀ p ∈ K, ‖dF p.1 p.2‖ ≤ C₀ := by
    intro p hp
    exact (hC ⟨p, hp, rfl⟩).trans (le_max_left C 0)
  have hs : Set.Icc (-1 : Real) 1 ∈ 𝓝 (0 : Real) :=
    Icc_mem_nhds (by norm_num) (by norm_num)
  have hFmeas : ∀ᶠ u in 𝓝 (0 : Real),
      AEStronglyMeasurable (F u)
        (MeasureTheory.volume.restrict (Set.uIoc a b)) :=
    Filter.Eventually.of_forall fun u =>
      (hFCont u).aestronglyMeasurable_of_subset_isCompact
        isCompact_uIcc measurableSet_uIoc Set.uIoc_subset_uIcc
  have hFint : IntervalIntegrable (F 0) MeasureTheory.volume a b :=
    (hFCont 0).intervalIntegrable
  have hF'meas : AEStronglyMeasurable (dF 0)
      (MeasureTheory.volume.restrict (Set.uIoc a b)) :=
    (hdFCont 0).aestronglyMeasurable_of_subset_isCompact
      isCompact_uIcc measurableSet_uIoc Set.uIoc_subset_uIcc
  have hbound : ∀ᵐ tau ∂MeasureTheory.volume,
      tau ∈ Set.uIoc a b → ∀ u ∈ Set.Icc (-1 : Real) 1,
        ‖dF u tau‖ ≤ (fun _ : Real => C₀) tau :=
    Filter.Eventually.of_forall fun tau htau u hu =>
      hC₀ (u, tau) ⟨hu, Set.uIoc_subset_uIcc htau⟩
  have hboundInt : IntervalIntegrable (fun _ : Real => C₀)
      MeasureTheory.volume a b :=
    continuousOn_const.intervalIntegrable
  have hdiff : ∀ᵐ tau ∂MeasureTheory.volume,
      tau ∈ Set.uIoc a b → ∀ u ∈ Set.Icc (-1 : Real) 1,
        HasDerivAt (fun z : Real => F z tau) (dF u tau) u :=
    Filter.Eventually.of_forall fun tau htau u _ =>
      hFDeriv u tau (Set.uIoc_subset_uIcc htau)
  have hparam :=
    intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := F) (F' := dF) (x₀ := (0 : Real))
      (s := Set.Icc (-1 : Real) 1) (a := a) (b := b)
      (bound := fun _ : Real => C₀) hs hFmeas hFint hF'meas
      hbound hboundInt hdiff
  have hJEq : Set.EqOn (dF 0) J (Set.uIcc a b) := by
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
    have hpoint := hasDerivAt_lEulerPair_variation_of_hasLEquationAt (I := I)
      S hS T f hf tau (hgeo.pos htau) (ht tau htau)
      W hW (hgeo.at htau)
    have hweighted : HasDerivAt (fun u : Real => F u tau) (J tau) 0 := by
      simpa only [F, J, W] using
        hpoint.const_mul (-2 * Real.sqrt tau)
    exact (hFDeriv 0 tau htau).unique hweighted
  have hint : (∫ tau in a..b, dF 0 tau) =
      ∫ tau in a..b, J tau :=
    intervalIntegral.integral_congr hJEq
  rw [hint] at hparam
  simpa only [F, J] using hparam.2

omit [InnerProductSpace Real E] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem lLength_second_variation_eq_integral_lJacobiPair
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
      (∫ tau in a..b,
        (-2 * Real.sqrt tau) *
          lJacobiPair S T (f 0)
            (fun r : Real =>
              lVelocity (I := I) (fun u : Real => f u r) 0)
            tau
            (lVelocity (I := I) (fun u : Real => f u tau) 0))
      0 := by
  let L : Real → Real := fun u =>
    lLength S T (fun tau : Real => f u tau) a b
  let Eul : Real → Real := fun u =>
    ∫ tau in a..b,
      (-2 * Real.sqrt tau) *
        lEulerPair S T (f u) tau
          (lVelocity (I := I) (fun v : Real => f v tau) u)
  have hpos : 0 < min a b :=
    lt_min (hgeo.pos Set.left_mem_uIcc) (hgeo.pos Set.right_mem_uIcc)
  have ht : ∀ tau ∈ Set.uIcc a b, T - tau ∈ D.regular :=
    fun tau htau => hgeo.regular htau
  have hderivEq (u : Real) : deriv L u = Eul u := by
    let fu : Real → Real → M := fun v tau => f (u + v) tau
    have hfu : IsSmoothVariation (I := I) fu := by
      exact (hf : ContMDiff _ _ (8 : ℕ) _).comp
        ((contMDiff_const.add contMDiff_fst).prodMk contMDiff_snd)
    have hfu0 : fu 0 = f u := by
      funext tau
      simp only [fu, add_zero]
    have hYshift (tau : Real) :
        lVelocity (I := I) (fun v : Real => fu v tau) 0 =
          lVelocity (I := I) (fun v : Real => f v tau) u := by
      simpa only [fu, lVelocity, varFst] using
        varFst_shift (I := I) f hf u tau
    have hYa :
        lVelocity (I := I) (fun v : Real => fu v a) 0 = 0 := by
      have hconst : (fun v : Real => fu v a) = fun _ : Real => f 0 a := by
        funext v
        exact hfixa (u + v)
      rw [hconst]
      simp only [lVelocity, mfderiv_const]
      rfl
    have hYb :
        lVelocity (I := I) (fun v : Real => fu v b) 0 = 0 := by
      have hconst : (fun v : Real => fu v b) = fun _ : Real => f 0 b := by
        funext v
        exact hfixb (u + v)
      rw [hconst]
      simp only [lVelocity, mfderiv_const]
      rfl
    have hshift := lLength_euler S hS T fu hfu a b hpos ht
    rw [hYa, hYb] at hshift
    rw [hfu0] at hshift
    have hshift' : HasDerivAt (fun v : Real => L (u + v)) (Eul u) 0 := by
      simpa [L, Eul, fu, hYshift] using hshift
    have hderiv := hshift'.deriv
    rw [deriv_comp_const_add L u 0, add_zero] at hderiv
    exact hderiv
  have hEul := hasDerivAt_integral_lEulerPair_variation (I := I) S hS T f hf a b hgeo
  have hfun : (fun u : Real => deriv L u) = Eul :=
    funext hderivEq
  rw [hfun]
  simpa only [L, Eul] using hEul

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem contDiffOn_two_metric_inner_variation_field
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (f : Real → Real → M)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    (hf : IsSmoothVariation (I := I) f) (u : Real) :
    ContDiffOn Real 2
      (fun p : Real × Real =>
        (S.base.metric (T - p.1)).inner (f u p.2)
          (lVelocity (I := I) (fun v : Real => f v p.2) u)
          (lVelocity (I := I) (fun v : Real => f v p.2) u))
      {p : Real × Real | T - p.1 ∈ D.regular} := by
  have hswap : IsSmoothVariation (I := I)
      (fun a b : Real => f b a) := by
    exact (hf : ContMDiff _ _ _ _).comp
      (contMDiff_snd.prodMk contMDiff_fst)
  have hYone : ContMDiff 𝓘(Real, Real) (I.prod 𝓘(Real, E)) (7 : ℕ)
      (fun tau : Real =>
        (TotalSpace.mk' E (E := TangentSpace I) (f u tau)
          (lVelocity (I := I) (fun v : Real => f v tau) u) :
            TangentBundle I M)) := by
    have hbase := velocity_totalSpace_contMDiff
      (I := I) (M := M) (fun a b : Real => f b a) hswap
    have hcomp := hbase.comp
      (contMDiff_id.prodMk contMDiff_const : ContMDiff 𝓘(Real, Real)
        (𝓘(Real, Real).prod 𝓘(Real, Real)) (7 : ℕ)
        (fun tau : Real => (tau, u)))
    simpa only [lVelocity, Function.comp_def, id_eq] using hcomp
  have hYall : ContMDiff
      (𝓘(Real, Real).prod 𝓘(Real, Real)) (I.prod 𝓘(Real, E)) (7 : ℕ)
      (fun p : Real × Real =>
        (TotalSpace.mk' E (E := TangentSpace I) (f u p.2)
          (lVelocity (I := I) (fun v : Real => f v p.2) u) :
            TangentBundle I M)) := by
    have hcomp := hYone.comp
      (contMDiff_snd : ContMDiff
        (𝓘(Real, Real).prod 𝓘(Real, Real)) 𝓘(Real, Real) (7 : ℕ)
        (fun p : Real × Real => p.2))
    simpa only [Function.comp_def] using hcomp
  have hbaseAll : ContMDiff
      (𝓘(Real, Real).prod 𝓘(Real, Real)) I (8 : ℕ)
      (fun p : Real × Real => f u p.2) := by
    exact (hf : ContMDiff _ _ (8 : ℕ) _).comp
      (contMDiff_const.prodMk contMDiff_snd)
  intro p hp
  have hbaseAt : ContMDiffAt
      (𝓘(Real, Real).prod 𝓘(Real, Real)) I (2 : WithTop ℕ∞)
      (fun q : Real × Real => f u q.2) p :=
    hbaseAll.contMDiffAt.of_le (by norm_num)
  have harg : ContMDiffAt
      (𝓘(Real, Real).prod 𝓘(Real, Real))
      (𝓘(Real, Real).prod I) (2 : WithTop ℕ∞)
      (fun q : Real × Real => (T - q.1, f u q.2)) p :=
    (contMDiffAt_const.sub contMDiffAt_fst).prodMk hbaseAt
  have hmetric₀ := hG.metricCLMSmoothAt
    (t := T - p.1) (x := f u p.2) (D.regular_isOpen.mem_nhds hp)
  have hmetric : ContMDiffAt
      (𝓘(Real, Real).prod 𝓘(Real, Real))
      (I.prod 𝓘(Real, E →L[Real] E →L[Real] Real)) (2 : WithTop ℕ∞)
      (fun q : Real × Real =>
        TotalSpace.mk' (E →L[Real] E →L[Real] Real)
          (E := fun y => TangentSpace I y →L[Real]
            TangentSpace I y →L[Real] Real)
          (f u q.2) ((S.base.metric (T - q.1)).inner (f u q.2))) p := by
    simpa only [SolutionOn.family_metric, Function.comp_def] using
      (hmetric₀.of_le (by
        change (↑(2 : ENat) : WithTop ENat) ≤ ↑(⊤ : ENat)
        exact WithTop.coe_le_coe.mpr le_top)).comp p harg
  have hY : ContMDiffAt
      (𝓘(Real, Real).prod 𝓘(Real, Real)) (I.prod 𝓘(Real, E))
      (2 : WithTop ℕ∞)
      (fun q : Real × Real =>
        (TotalSpace.mk' E (E := TangentSpace I) (f u q.2)
          (lVelocity (I := I) (fun v : Real => f v q.2) u) :
            TangentBundle I M)) p :=
    hYall.contMDiffAt.of_le (by norm_num)
  have htotal := ContMDiffAt.clm_bundle_apply₂
    (E₁ := fun y : M => TangentSpace I y)
    (E₂ := fun y : M => TangentSpace I y)
    (E₃ := fun _ : M => Real) hmetric hY hY
  have hscalar : ContMDiffAt
      (𝓘(Real, Real).prod 𝓘(Real, Real)) 𝓘(Real, Real)
      (2 : WithTop ℕ∞)
      (fun q : Real × Real =>
        (S.base.metric (T - q.1)).inner (f u q.2)
          (lVelocity (I := I) (fun v : Real => f v q.2) u)
          (lVelocity (I := I) (fun v : Real => f v q.2) u)) p := by
    rw [Bundle.contMDiffAt_totalSpace] at htotal
    convert htotal.2 using 1 ; rfl
  have hcd : ContDiffAt Real 2
      (fun q : Real × Real =>
        (S.base.metric (T - q.1)).inner (f u q.2)
          (lVelocity (I := I) (fun v : Real => f v q.2) u)
          (lVelocity (I := I) (fun v : Real => f v q.2) u)) p := by
    rw [← contMDiffAt_iff_contDiffAt, modelWithCornersSelf_prod,
      ← chartedSpaceSelf_prod]
    exact hscalar
  exact hcd.contDiffWithinAt

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private theorem lVarNorm_c2
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (f : Real → Real → M)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    (hf : IsSmoothVariation (I := I) f) (u : Real) :
    ContDiffOn Real 2
      (fun tau : Real =>
        (S.base.metric (T - tau)).inner (f u tau)
          (lVelocity (I := I) (fun v : Real => f v tau) u)
          (lVelocity (I := I) (fun v : Real => f v tau) u))
      {tau : Real | T - tau ∈ D.regular} := by
  let V : Set Real := {tau : Real | T - tau ∈ D.regular}
  let Q : Real × Real → Real := fun p =>
    (S.base.metric (T - p.1)).inner (f u p.2)
      (lVelocity (I := I) (fun v : Real => f v p.2) u)
      (lVelocity (I := I) (fun v : Real => f v p.2) u)
  have hQ : ContDiffOn Real 2 Q
      {p : Real × Real | T - p.1 ∈ D.regular} := by
    simpa only [Q] using contDiffOn_two_metric_inner_variation_field S T f hG hf u
  have hdiag : ContDiffOn Real 2
      (fun tau : Real => (tau, tau)) V :=
    contDiffOn_id.prodMk contDiffOn_id
  have hout := hQ.comp hdiag (fun tau htau => htau)
  simpa only [Q, V, Function.comp_def] using hout

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [SigmaCompactSpace M] in
private theorem lVarRicci_c1
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    (f : Real → Real → M) (hf : IsSmoothVariation (I := I) f)
    (u : Real) :
    ContDiffOn Real 1
      (fun tau : Real =>
        S.ricciAt (T - tau) (f u tau)
          (vec2
            (lVelocity (I := I) (fun v : Real => f v tau) u)
            (lVelocity (I := I) (fun v : Real => f v tau) u)))
      {tau : Real | T - tau ∈ D.regular} := by
  let V : Set Real := {tau : Real | T - tau ∈ D.regular}
  let W : Set (Real × Real) :=
    {p : Real × Real | T - p.1 ∈ D.regular}
  let Q : Real × Real → Real := fun p =>
    (S.base.metric (T - p.1)).inner (f u p.2)
      (lVelocity (I := I) (fun v : Real => f v p.2) u)
      (lVelocity (I := I) (fun v : Real => f v p.2) u)
  let dQ : Real × Real → Real := fun p =>
    fderiv Real Q p (1, 0)
  let raw : Real → Real := fun tau => dQ (tau, tau) / 2
  let ric : Real → Real := fun tau =>
    S.ricciAt (T - tau) (f u tau)
      (vec2
        (lVelocity (I := I) (fun v : Real => f v tau) u)
        (lVelocity (I := I) (fun v : Real => f v tau) u))
  have hWopen : IsOpen W :=
    D.regular_isOpen.preimage (continuous_const.sub continuous_fst)
  have hQ2 : ContDiffOn Real 2 Q W := by
    simpa only [Q, W] using
      contDiffOn_two_metric_inner_variation_field S T f hS.smoothMetric hf u
  have hdQ : ContDiffOn Real 1 dQ W := by
    have hfd : ContDiffOn Real 1 (fderiv Real Q) W :=
      hQ2.fderiv_of_isOpen hWopen (by norm_num)
    simpa only [dQ] using hfd.clm_apply contDiffOn_const
  have hdiag : ContDiffOn Real 1 (fun tau : Real => (tau, tau)) V :=
    contDiffOn_id.prodMk contDiffOn_id
  have hdDiag : ContDiffOn Real 1 (fun tau : Real => dQ (tau, tau)) V :=
    hdQ.comp hdiag (fun tau htau => htau)
  have hraw : ContDiffOn Real 1 raw V := by
    simpa only [raw] using hdDiag.div_const 2
  have hQDiff : DifferentiableOn Real Q W :=
    hQ2.differentiableOn (by norm_num)
  have heq : Set.EqOn ric raw V := by
    intro tau htau
    have hpW : (tau, tau) ∈ W := htau
    have hQAt : DifferentiableAt Real Q (tau, tau) :=
      (hQDiff (tau, tau) hpW).differentiableAt
        (hWopen.mem_nhds hpW)
    have hslice : HasDerivAt
        (fun s : Real => Q (s, tau)) (dQ (tau, tau)) tau := by
      simpa only [dQ] using Aux2.hasDerivAt_slice_fst
        (fun s r : Real => Q (s, r)) tau tau hQAt
    let Y : TangentSpace I (f u tau) :=
      lVelocity (I := I) (fun v : Real => f v tau) u
    have hmetric := metricDerivAt (I := I) S hS
      (⟨T - tau, htau⟩ :
        DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
      (f u tau) Y Y
    have hsub := (hasDerivAt_id (x := tau)).const_sub T
    have htime := hmetric.comp tau hsub
    have htimeQ : HasDerivAt (fun s : Real => Q (s, tau))
        (2 * S.ricciAt (T - tau) (f u tau) (vec2 Y Y)) tau := by
      simpa only [Q, Y, SolutionOn.family_metric, Function.comp_def,
        id_eq, mul_neg, neg_mul, neg_neg, mul_one] using htime
    have hdQEq :
        dQ (tau, tau) =
          2 * S.ricciAt (T - tau) (f u tau) (vec2 Y Y) :=
      hslice.unique htimeQ
    dsimp only [ric, raw]
    rw [hdQEq]
    ring
  have hout : ContDiffOn Real 1 ric V :=
    hraw.congr (fun tau htau => heq htau)
  simpa only [ric, V] using hout

omit [InnerProductSpace Real E] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem differentiableAt_chartRepAt_lJacobiVelocity_variation_field
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    (f : Real → Real → M) (hf : IsSmoothVariation (I := I) f)
    (tau : Real) (hpos : 0 < tau) (ht : T - tau ∈ D.regular) :
    DifferentiableAt Real
      (chartRepAt (I := I) (f 0)
        (lJacobiVelocity S T (f 0)
          (fun r : Real =>
            lVelocity (I := I) (fun u : Real => f u r) 0)) tau) tau := by
  let s : Real := Real.sqrt tau
  let F : Real → Real → M := fun u r => f u (r ^ 2)
  let gamma : Real → M := f 0
  let Y : (r : Real) → TangentSpace I (gamma r) := fun r =>
    lVelocity (I := I) (fun u : Real => f u r) 0
  have hs : 0 < s := Real.sqrt_pos.2 hpos
  have hsq : s ^ 2 = tau := Real.sq_sqrt hpos.le
  have ht_sq : T - s ^ 2 ∈ D.regular := by
    simpa only [hsq] using ht
  have hF : IsSmoothVariation (I := I) F := by
    exact (hf : ContMDiff _ _ (8 : ℕ) _).comp
      (contMDiff_fst.prodMk (contMDiff_snd.pow 2))
  have hgamma : ContMDiff 𝓘(Real, Real) I (8 : ℕ) gamma := by
    exact (hf : ContMDiff _ _ (8 : ℕ) _).comp
      (contMDiff_const.prodMk contMDiff_id)
  have hgamma_sq : ∀ᶠ r in nhds s,
      MDifferentiableAt 𝓘(Real, Real) I gamma (r ^ 2) :=
    Filter.Eventually.of_forall (fun _ =>
      hgamma.mdifferentiableAt (by norm_num))
  have hY_sq : ∀ᶠ r in nhds s,
      DifferentiableAt Real
        (chartRepAt (I := I) gamma Y (r ^ 2)) (r ^ 2) := by
    apply Filter.Eventually.of_forall
    intro r
    simpa only [gamma, Y, lVelocity, varFst] using
      variationField_chartRep_differentiableAt
        (I := I) f hf (r ^ 2)
  have hF0 : ContMDiff 𝓘(Real, Real) I (8 : ℕ) (F 0) := by
    exact (hF : ContMDiff _ _ (8 : ℕ) _).comp
      (contMDiff_const.prodMk contMDiff_id)
  have hF02 : ContMDiffAt 𝓘(Real, Real) I 2 (F 0) s :=
    hF0.contMDiffAt.of_le (by norm_num)
  have hA : DifferentiableAt Real
      (chartRepAt (I := I) (F 0)
        (fun r : Real => lVelocity (I := I) (F 0) r) s) s := by
    exact differentiableAt_chartRepAt_lVelocity (I := I) (F 0) s hF02
  have hA_sq : DifferentiableAt Real
      (chartRepAt (I := I) (squareReparametrization gamma)
        (fun r : Real ↦ lVelocity (I := I) (squareReparametrization gamma) r) s) s := by
    change DifferentiableAt Real
      (chartRepAt (I := I) (F 0)
        (fun r : Real ↦ lVelocity (I := I) (F 0) r) s) s
    exact hA
  rcases lRegVar_reg (I := I) S T s F hF with ⟨_, _, hZraw⟩
  have hZ : DifferentiableAt Real
      (chartRepAt (I := I) (squareReparametrization gamma)
        (fun r : Real =>
          covDerivAlong (I := I) (S.base.metric (T - s ^ 2))
            (squareReparametrization gamma) (fun u : Real => Y (u ^ 2)) r) s) s := by
    change DifferentiableAt Real
      (chartRepAt (I := I) (F 0)
        (fun r : Real ↦ covDerivAlong (I := I)
          (S.base.metric (T - s ^ 2)) (F 0)
          (fun u : Real ↦ lVelocity (I := I) (fun v : Real ↦ F v u) 0) r)
        s) s
    exact hZraw
  have hout := differentiableAt_chartRepAt_lJacobiVelocity_of_squareReparametrization (I := I) S hS T gamma Y s hs ht_sq
    hgamma_sq hY_sq hA_sq hZ
  simpa only [gamma, Y, hsq] using hout

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
theorem contDiffOn_one_metric_inner_lJacobiVelocity_variation_field
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    (f : Real → Real → M) (hf : IsSmoothVariation (I := I) f)
    (u : Real) :
    ContDiffOn Real 1
      (fun tau : Real =>
        (S.base.metric (T - tau)).inner (f u tau)
          (lJacobiVelocity S T (f u)
            (fun r : Real =>
              lVelocity (I := I) (fun v : Real => f v r) u) tau)
          (lVelocity (I := I) (fun v : Real => f v tau) u))
      {tau : Real | T - tau ∈ D.regular} := by
  let V : Set Real := {tau : Real | T - tau ∈ D.regular}
  let gamma : Real → M := f u
  let Y : ∀ tau, TangentSpace I (gamma tau) := fun tau =>
    lVelocity (I := I) (fun v : Real => f v tau) u
  let N : Real → Real := fun tau =>
    (S.base.metric (T - tau)).inner (gamma tau) (Y tau) (Y tau)
  let dN : Real → Real := fun tau => fderiv Real N tau 1
  let R : Real → Real := fun tau =>
    S.ricciAt (T - tau) (gamma tau) (vec2 (Y tau) (Y tau))
  let raw : Real → Real := fun tau => (dN tau - 2 * R tau) / 2
  let inner : Real → Real := fun tau =>
    (S.base.metric (T - tau)).inner (gamma tau)
      (lJacobiVelocity S T gamma Y tau) (Y tau)
  have hVopen : IsOpen V :=
    D.regular_isOpen.preimage (continuous_const.sub continuous_id)
  have hN2 : ContDiffOn Real 2 N V := by
    simpa only [N, gamma, Y, V] using
      lVarNorm_c2 S T f hS.smoothMetric hf u
  have hdN : ContDiffOn Real 1 dN V := by
    have hfd : ContDiffOn Real 1 (fderiv Real N) V :=
      hN2.fderiv_of_isOpen hVopen (by norm_num)
    simpa only [dN] using hfd.clm_apply contDiffOn_const
  have hR : ContDiffOn Real 1 R V := by
    simpa only [R, gamma, Y, V] using lVarRicci_c1 S hS T f hf u
  have hraw : ContDiffOn Real 1 raw V := by
    simpa only [raw] using (hdN.sub (contDiffOn_const.mul hR)).div_const 2
  have hNDiff : DifferentiableOn Real N V :=
    hN2.differentiableOn (by norm_num)
  have heq : Set.EqOn inner raw V := by
    intro tau htau
    have hNAt : DifferentiableAt Real N tau :=
      (hNDiff tau htau).differentiableAt (hVopen.mem_nhds htau)
    have hNderiv : HasDerivAt N (dN tau) tau := by
      simpa only [dN] using hNAt.hasFDerivAt.hasDerivAt
    have hgamma : MDifferentiableAt 𝓘(Real, Real) I gamma tau := by
      have hcurve : ContMDiff 𝓘(Real, Real) I (8 : ℕ) gamma := by
        exact (hf : ContMDiff _ _ (8 : ℕ) _).comp
          (contMDiff_const.prodMk contMDiff_id)
      exact hcurve.mdifferentiableAt (by norm_num)
    let fu : Real → Real → M := fun a r => f (u + a) r
    have hfu : IsSmoothVariation (I := I) fu := by
      exact (hf : ContMDiff _ _ (8 : ℕ) _).comp
        ((contMDiff_const.add contMDiff_fst).prodMk contMDiff_snd)
    have hfu0 : fu 0 = gamma := by
      funext r
      simp only [fu, gamma, add_zero]
    have hYshift (r : Real) :
        lVelocity (I := I) (fun a : Real => fu a r) 0 = Y r := by
      simpa only [fu, Y, lVelocity, varFst] using
        varFst_shift (I := I) f hf u r
    have hYfun :
        (fun r : Real =>
          lVelocity (I := I) (fun a : Real => fu a r) 0) = Y :=
      funext hYshift
    have hY : DifferentiableAt Real
        (chartRepAt (I := I) gamma Y tau) tau := by
      have hout : DifferentiableAt Real
          (chartRepAt (I := I) (fu 0)
            (fun r : Real =>
              lVelocity (I := I) (fun a : Real => fu a r) 0) tau) tau := by
        simpa only [lVelocity, chartRepAt_apply] using
          variationField_chartRep_differentiableAt
            (I := I) fu hfu tau
      rw [hfu0, hYfun] at hout
      exact hout
    have hinner := lInner_deriv S hS T gamma Y Y tau htau
      hgamma hY hY
    have hdNEq :
        dN tau =
          ((S.base.metric (T - tau)).inner (gamma tau)
              (lJacobiVelocity S T gamma Y tau) (Y tau) +
            (S.base.metric (T - tau)).inner (gamma tau)
              (Y tau) (lJacobiVelocity S T gamma Y tau)) +
            2 * R tau := by
      exact hNderiv.unique (by
        simpa only [N, R, lJacobiVelocity] using hinner)
    have hsymm :
        (S.base.metric (T - tau)).inner (gamma tau)
            (Y tau) (lJacobiVelocity S T gamma Y tau) =
          (S.base.metric (T - tau)).inner (gamma tau)
            (lJacobiVelocity S T gamma Y tau) (Y tau) :=
      (S.base.metric (T - tau)).symm _ _ _
    dsimp only [inner, raw]
    rw [hdNEq, hsymm]
    ring
  have hout : ContDiffOn Real 1 inner V :=
    hraw.congr (fun tau htau => heq htau)
  simpa only [inner, gamma, Y, V] using hout

end normedSpaceCompatibility

end DifferentialGeometry.PDE.RicciFlow.Perelman
