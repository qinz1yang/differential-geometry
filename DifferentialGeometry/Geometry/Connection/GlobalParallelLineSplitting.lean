import DifferentialGeometry.Geometry.Connection.GlobalParallelLine
import DifferentialGeometry.Tensor.Exterior.GlobalPoincare
import DifferentialGeometry.Analysis.ODE.LinearGrowthComplete
import DifferentialGeometry.Analysis.Calculus.CurveDerivative
import DifferentialGeometry.Topology.Morse.RegularSublevel
import DifferentialGeometry.Geometry.Metric.LieDerivative.Flow
import DifferentialGeometry.Geometry.Metric.PullbackCompleteness
import DifferentialGeometry.Geometry.Metric.ProductSlice
import Mathlib.Analysis.Convex.Contractible

set_option autoImplicit false

noncomputable section

open Bundle Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Connection

universe uE uH uM

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [T2Space M]

attribute [local instance] DifferentialGeometry.seminormedAddCommGroupTangentSpace
attribute [local instance] DifferentialGeometry.normedAddCommGroupTangentSpace
attribute [local instance] DifferentialGeometry.normedSpaceTangentSpace

theorem exists_global_gradient_potential_of_parallel_section
    [SimplyConnectedSpace M]
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, TangentSpace I⟯)
    (hparallel : ∀ x, ∀ v : TangentSpace I x,
      (LeviCivita (I := I) g) X x v = 0) :
    ∃ f : M → ℝ,
      ContMDiff I 𝓘(ℝ, ℝ) ∞ f ∧
      ∀ x, ∀ v : TangentSpace I x,
        mvfderiv (I := I) f x v = g.inner x (X x) v := by
  let theta := metricFlat g fun x => X x
  have htheta : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] ℝ)
        (E := fun y : M => TangentSpace I y →L[ℝ] ℝ) x (theta x)) := by
    exact ContMDiff.clm_bundle_apply (b := id) g.contMDiff X.contMDiff
  let alpha : DifferentialGeometry.DifferentialForm I M 1 :=
    DifferentialGeometry.DifferentialForm.ofCotangent theta htheta
  have hcovtheta :
      (cotangentCov (LeviCivita (I := I) g)).toFun theta = 0 := by
    funext x
    apply ContinuousLinearMap.ext
    intro v
    apply ContinuousLinearMap.ext
    intro y
    rw [cotangentCov_metricDuality g
      (X.contMDiff.mdifferentiableAt (by simp)) v y]
    rw [hparallel x v]
    simp
  have halpha : DifferentialGeometry.DifferentialForm.isClosed alpha := by
    exact DifferentialGeometry.DifferentialForm.isClosed_of_cotangentCov_eq_zero_of_torsion_eq_zero
      (LeviCivita (I := I) g) theta htheta hcovtheta
      (LeviCivita_torsion_eq_zero (I := I) g)
  obtain ⟨f, hf, hdf⟩ :=
    DifferentialGeometry.DifferentialForm.exists_global_potential alpha halpha
  refine ⟨f, hf, ?_⟩
  intro x v
  rw [hdf x v]
  rw [DifferentialGeometry.DifferentialForm.ofCotangent_apply]
  rfl

theorem exists_globalIntegralCurve_of_unit_section
    [T2Space (TangentBundle I M)] [SigmaCompactSpace M] [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M)
    (hg : RiemannianMetricComplete (I := I) g)
    (X : Cₛ^∞⟮I; E, TangentSpace I⟯)
    (hunit : ∀ x, g.inner x (X x) (X x) = 1) :
    ∀ x : M, ∃ gamma : ℝ → M,
      And (gamma 0 = x) (IsMIntegralCurve gamma X) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let p : M := Classical.arbitrary M
  exact DifferentialGeometry.Analysis.ODE.exists_globalIntegralCurve_of_linearGrowth
    g hg X X.contMDiff p zero_le_one fun x => by
      rw [hunit x, Real.sqrt_one, one_mul]
      exact le_add_of_nonneg_right ENNReal.toReal_nonneg

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] in
theorem globalIntegralCurve_potential_hasDerivAt
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, TangentSpace I⟯)
    (hcomplete : ∀ x : M, ∃ gamma : ℝ → M,
      And (gamma 0 = x) (IsMIntegralCurve gamma X))
    (f : M → ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hdf : ∀ x, ∀ v : TangentSpace I x,
      mvfderiv (I := I) f x v = g.inner x (X x) v)
    (hunit : ∀ x, g.inner x (X x) (X x) = 1)
    (t : ℝ) (x : M) :
    HasDerivAt
      (fun r : ℝ => f (DifferentialGeometry.Analysis.ODE.curveAt X hcomplete x r)) 1 t := by
  let gamma : ℝ → M :=
    DifferentialGeometry.Analysis.ODE.curveAt X hcomplete x
  have hgamma : IsMIntegralCurve gamma X :=
    DifferentialGeometry.Analysis.ODE.curveAt_integralCurve X hcomplete x
  have hgammaMD : MDifferentiableAt 𝓘(ℝ, ℝ) I gamma t :=
    (hgamma t).mdifferentiableAt
  have hfMD : MDifferentiableAt I 𝓘(ℝ, ℝ) f (gamma t) :=
    (hf (gamma t)).mdifferentiableAt (by simp)
  have hcomp := DifferentialGeometry.Analysis.Calculus.hasDerivAt_comp_mfderiv_along
    I f gamma t hfMD hgammaMD
  have hvel :
      mfderiv 𝓘(ℝ, ℝ) I gamma t
          (DifferentialGeometry.Analysis.Calculus.realTangentOne t) = X (gamma t) := by
    rw [(hgamma t).mfderiv]
    change (1 : ℝ) • X (gamma t) = X (gamma t)
    exact one_smul ℝ (X (gamma t))
  have hrate :
      (NormedSpace.fromTangentSpace (f (gamma t)))
        ((mfderiv I 𝓘(ℝ, ℝ) f (gamma t))
          (mfderiv 𝓘(ℝ, ℝ) I gamma t
            (DifferentialGeometry.Analysis.Calculus.realTangentOne t))) = 1 := by
    rw [hvel]
    change mvfderiv (I := I) f (gamma t) (X (gamma t)) = 1
    rw [hdf, hunit]
  simpa only [gamma] using hcomp.congr_deriv hrate

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] in
theorem globalIntegralCurve_potential_eq_add
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, TangentSpace I⟯)
    (hcomplete : ∀ x : M, ∃ gamma : ℝ → M,
      And (gamma 0 = x) (IsMIntegralCurve gamma X))
    (f : M → ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hdf : ∀ x, ∀ v : TangentSpace I x,
      mvfderiv (I := I) f x v = g.inner x (X x) v)
    (hunit : ∀ x, g.inner x (X x) (X x) = 1)
    (t : ℝ) (x : M) :
    f (DifferentialGeometry.Analysis.ODE.curveAt X hcomplete x t) = f x + t := by
  let P : ℝ → ℝ := fun r =>
    f (DifferentialGeometry.Analysis.ODE.curveAt X hcomplete x r)
  let Q : ℝ → ℝ := fun r => P r - r
  have hzero : DifferentialGeometry.Analysis.ODE.curveAt X hcomplete x 0 = x :=
    DifferentialGeometry.Analysis.ODE.curveAt_zero X hcomplete x
  have hhas : ∀ r : ℝ, HasDerivAt P 1 r := by
    intro r
    exact globalIntegralCurve_potential_hasDerivAt
      g X hcomplete f hf hdf hunit r x
  have hQhas : ∀ r : ℝ, HasDerivAt Q 0 r := by
    intro r
    change HasDerivAt (P - id) 0 r
    simpa only [sub_self] using (hhas r).sub (hasDerivAt_id r)
  by_cases ht : 0 ≤ t
  · rcases ht.eq_or_lt with rfl | htpos
    · simp only [add_zero, hzero]
    · have hdiff : DifferentiableOn ℝ Q (Set.Icc 0 t) := by
        intro r _
        exact (hQhas r).differentiableAt.differentiableWithinAt
      have hderiv : ∀ r ∈ Set.Ico 0 t,
          derivWithin Q (Set.Icc 0 t) r = 0 := by
        intro r hr
        have hrIcc : r ∈ Set.Icc 0 t := ⟨hr.1, le_of_lt hr.2⟩
        exact (hQhas r).hasDerivWithinAt.derivWithin
          ((uniqueDiffOn_Icc htpos) r hrIcc)
      have hconst := constant_of_derivWithin_zero hdiff hderiv t
        (right_mem_Icc.mpr ht)
      change P t - t = P 0 - 0 at hconst
      dsimp only [P] at hconst
      rw [sub_zero, hzero] at hconst
      linarith
  · have htneg : t < 0 := lt_of_not_ge ht
    have hdiff : DifferentiableOn ℝ Q (Set.Icc t 0) := by
      intro r _
      exact (hQhas r).differentiableAt.differentiableWithinAt
    have hderiv : ∀ r ∈ Set.Ico t 0,
        derivWithin Q (Set.Icc t 0) r = 0 := by
      intro r hr
      have hrIcc : r ∈ Set.Icc t 0 := ⟨hr.1, le_of_lt hr.2⟩
      exact (hQhas r).hasDerivWithinAt.derivWithin
        ((uniqueDiffOn_Icc htneg) r hrIcc)
    have hconst := constant_of_derivWithin_zero hdiff hderiv 0
      (right_mem_Icc.mpr (le_of_lt htneg))
    change P 0 - 0 = P t - t at hconst
    dsimp only [P] at hconst
    rw [sub_zero, hzero] at hconst
    linarith

private noncomputable def globalIntegralCurveDiffeomorph
    [CompleteSpace E]
    (X : Cₛ^∞⟮I; E, TangentSpace I⟯)
    (hcomplete : ∀ x : M, ∃ gamma : ℝ → M,
      And (gamma 0 = x) (IsMIntegralCurve gamma X))
    (t : ℝ) : Diffeomorph I I M M ∞ := by
  have hX1 : CMDiff 1
      (fun x : M => (⟨x, X x⟩ : TangentBundle I M)) :=
    X.contMDiff.of_le (by norm_num)
  have hleft : ∀ x : M,
      DifferentialGeometry.Analysis.ODE.curveAt X hcomplete
          (DifferentialGeometry.Analysis.ODE.curveAt X hcomplete x t) (-t) = x := by
    intro x
    rw [← DifferentialGeometry.Analysis.ODE.curveAt_add X hX1 hcomplete]
    simpa using DifferentialGeometry.Analysis.ODE.curveAt_zero X hcomplete x
  have hright : ∀ x : M,
      DifferentialGeometry.Analysis.ODE.curveAt X hcomplete
          (DifferentialGeometry.Analysis.ODE.curveAt X hcomplete x (-t)) t = x := by
    intro x
    rw [← DifferentialGeometry.Analysis.ODE.curveAt_add X hX1 hcomplete]
    simpa [add_comm] using DifferentialGeometry.Analysis.ODE.curveAt_zero X hcomplete x
  have hforward : ContMDiff I I ∞
      (fun x : M => DifferentialGeometry.Analysis.ODE.curveAt X hcomplete x t) := by
    intro x
    exact DifferentialGeometry.Analysis.ODE.contMDiffAt_globalFlow_of_complete
      X X.contMDiff hcomplete t x
  have hreverse : ContMDiff I I ∞
      (fun x : M => DifferentialGeometry.Analysis.ODE.curveAt X hcomplete x (-t)) := by
    intro x
    exact DifferentialGeometry.Analysis.ODE.contMDiffAt_globalFlow_of_complete
      X X.contMDiff hcomplete (-t) x
  exact
    { toEquiv :=
        { toFun := fun x => DifferentialGeometry.Analysis.ODE.curveAt X hcomplete x t
          invFun := fun x => DifferentialGeometry.Analysis.ODE.curveAt X hcomplete x (-t)
          left_inv := hleft
          right_inv := hright }
      contMDiff_toFun := hforward
      contMDiff_invFun := hreverse }

private theorem globalIntegralCurveDiffeomorph_apply
    [CompleteSpace E]
    (X : Cₛ^∞⟮I; E, TangentSpace I⟯)
    (hcomplete : ∀ x : M, ∃ gamma : ℝ → M,
      And (gamma 0 = x) (IsMIntegralCurve gamma X))
    (t : ℝ) (x : M) :
    globalIntegralCurveDiffeomorph X hcomplete t x =
      DifferentialGeometry.Analysis.ODE.curveAt X hcomplete x t := rfl

private theorem globalIntegralCurve_pairing_hasDerivAt
    [CompleteSpace E]
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, TangentSpace I⟯)
    (hcomplete : ∀ x : M, ∃ gamma : ℝ → M,
      And (gamma 0 = x) (IsMIntegralCurve gamma X))
    (t : ℝ) (x : M) (v w : TangentSpace I x) :
    HasDerivAt
      (fun r : ℝ => g.inner
        (DifferentialGeometry.Analysis.ODE.curveAt X hcomplete x r)
        (mfderiv I I
          (fun y : M => DifferentialGeometry.Analysis.ODE.curveAt X hcomplete y r) x v)
        (mfderiv I I
          (fun y : M => DifferentialGeometry.Analysis.ODE.curveAt X hcomplete y r) x w))
      (DifferentialGeometry.PDE.DeTurck.lieDerivMetric (I := I) g X
        (DifferentialGeometry.Analysis.ODE.curveAt X hcomplete x t)
        (mfderiv I I
          (fun y : M => DifferentialGeometry.Analysis.ODE.curveAt X hcomplete y t) x v)
        (mfderiv I I
          (fun y : M => DifferentialGeometry.Analysis.ODE.curveAt X hcomplete y t) x w)) t := by
  let fam : ℝ → M ≃ₘ⟮I, I⟯ M := fun u =>
    globalIntegralCurveDiffeomorph X hcomplete (u + t - 1)
  have hfamOde : ∀ y : M, ∀ u ∈ Set.Ioo (0 : ℝ) 2,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun a : ℝ => (fam a : M → M) y)
        (Set.Ici (0 : ℝ)) u
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X ((fam u : M → M) y))) := by
    intro y u _
    have hcurve : IsMIntegralCurve
        (fun a : ℝ => DifferentialGeometry.Analysis.ODE.curveAt
          X hcomplete y (a + t - 1)) X := by
      have h :=
        (DifferentialGeometry.Analysis.ODE.curveAt_integralCurve
          X hcomplete y).comp_add (t - 1)
      convert h using 1
      funext a
      simp only [Function.comp_apply]
      congr 1
      ring
    change HasMFDerivWithinAt 𝓘(ℝ, ℝ) I
      (fun a : ℝ => DifferentialGeometry.Analysis.ODE.curveAt
        X hcomplete y (a + t - 1)) (Set.Ici (0 : ℝ)) u
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (X (DifferentialGeometry.Analysis.ODE.curveAt
          X hcomplete y (u + t - 1))))
    exact (hcurve u).hasMFDerivWithinAt
  have hfamJoint : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞
      (fun q : ℝ × M => (fam q.1 : M → M) q.2)
      (Set.Ioo (0 : ℝ) 2 ×ˢ Set.univ) := by
    have hflow :=
      DifferentialGeometry.Analysis.ODE.contMDiff_globalFlow_joint_of_complete
        X X.contMDiff hcomplete
    have hinput : ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) ∞
        (fun q : ℝ × M => (q.1 + t - 1, q.2)) :=
      ((contMDiff_fst.add contMDiff_const).sub contMDiff_const).prodMk contMDiff_snd
    have hcomp := hflow.comp hinput
    apply hcomp.contMDiffOn.congr
    intro q _
    rfl
  have hshift :=
    DifferentialGeometry.Geometry.Riemannian.Variation.flow_metric_pairing_hasDerivWithinAt
      (I := I) g (fun _ => X) 2 fam hfamOde hfamJoint 1 (by norm_num) x v w
  have hshiftAt : HasDerivAt
      (fun u : ℝ => g.inner ((fam u : M → M) x)
        (mfderiv I I (fam u : M → M) x v)
        (mfderiv I I (fam u : M → M) x w))
      (DifferentialGeometry.PDE.DeTurck.lieDerivMetric (I := I) g X
        ((fam 1 : M → M) x)
        (mfderiv I I (fam 1 : M → M) x v)
        (mfderiv I I (fam 1 : M → M) x w)) 1 :=
    hshift.hasDerivAt (Ici_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hback : HasDerivAt (fun r : ℝ => r - t + 1) 1 t := by
    simpa only [id_eq] using ((hasDerivAt_id t).sub_const t).add_const 1
  have hbase : t - t + 1 = (1 : ℝ) := by ring
  have hshiftAt' : HasDerivAt
      (fun u : ℝ => g.inner ((fam u : M → M) x)
        (mfderiv I I (fam u : M → M) x v)
        (mfderiv I I (fam u : M → M) x w))
      (DifferentialGeometry.PDE.DeTurck.lieDerivMetric (I := I) g X
        ((fam 1 : M → M) x)
        (mfderiv I I (fam 1 : M → M) x v)
        (mfderiv I I (fam 1 : M → M) x w)) (t - t + 1) := by
    rw [hbase]
    exact hshiftAt
  have hcomp := hshiftAt'.comp t hback
  have hfamOne : fam 1 = globalIntegralCurveDiffeomorph X hcomplete t := by
    dsimp only [fam]
    congr 1
    ring
  have hfamBack : ∀ r : ℝ,
      fam (r - t + 1) = globalIntegralCurveDiffeomorph X hcomplete r := by
    intro r
    dsimp only [fam]
    congr 1
    ring
  rw [hfamOne] at hcomp
  have hfun :
      ((fun u : ℝ => g.inner ((fam u : M → M) x)
        (mfderiv I I (fam u : M → M) x v)
        (mfderiv I I (fam u : M → M) x w)) ∘ fun r : ℝ => r - t + 1) =
      (fun r : ℝ => g.inner
        (DifferentialGeometry.Analysis.ODE.curveAt X hcomplete x r)
        (mfderiv I I
          (fun y : M => DifferentialGeometry.Analysis.ODE.curveAt X hcomplete y r) x v)
        (mfderiv I I
          (fun y : M => DifferentialGeometry.Analysis.ODE.curveAt X hcomplete y r) x w)) := by
    funext r
    rw [Function.comp_apply, hfamBack r]
    rfl
  rw [hfun] at hcomp
  rw [globalIntegralCurveDiffeomorph_apply] at hcomp
  have hderivOne :
      mfderiv I I (globalIntegralCurveDiffeomorph X hcomplete t : M → M) x =
        mfderiv I I
          (fun y : M => DifferentialGeometry.Analysis.ODE.curveAt X hcomplete y t) x := by
    apply Filter.EventuallyEq.mfderiv_eq
    filter_upwards with y
    rw [globalIntegralCurveDiffeomorph_apply]
  rw [hderivOne] at hcomp
  simpa only [mul_one] using hcomp

theorem globalIntegralCurve_inner_eq_of_parallel_section
    [CompleteSpace E]
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, TangentSpace I⟯)
    (hcomplete : ∀ x : M, ∃ gamma : ℝ → M,
      And (gamma 0 = x) (IsMIntegralCurve gamma X))
    (hparallel : ∀ x, ∀ q : TangentSpace I x,
      (LeviCivita (I := I) g) X x q = 0)
    (t : ℝ) (x : M) (v w : TangentSpace I x) :
    g.inner (DifferentialGeometry.Analysis.ODE.curveAt X hcomplete x t)
        (mfderiv I I
          (fun y : M => DifferentialGeometry.Analysis.ODE.curveAt X hcomplete y t) x v)
        (mfderiv I I
          (fun y : M => DifferentialGeometry.Analysis.ODE.curveAt X hcomplete y t) x w) =
      g.inner x v w := by
  let P : ℝ → ℝ := fun r =>
    g.inner (DifferentialGeometry.Analysis.ODE.curveAt X hcomplete x r)
      (mfderiv I I
        (fun y : M => DifferentialGeometry.Analysis.ODE.curveAt X hcomplete y r) x v)
      (mfderiv I I
        (fun y : M => DifferentialGeometry.Analysis.ODE.curveAt X hcomplete y r) x w)
  have hhas : ∀ r : ℝ, HasDerivAt P 0 r := by
    intro r
    have h := globalIntegralCurve_pairing_hasDerivAt
      g X hcomplete r x v w
    apply h.congr_deriv
    rw [DifferentialGeometry.PDE.RicciFlow.Pullback.cartan_formula_for_lie_deriv_metric]
    rw [hparallel, hparallel]
    simp
  have hzero : DifferentialGeometry.Analysis.ODE.curveAt X hcomplete x 0 = x :=
    DifferentialGeometry.Analysis.ODE.curveAt_zero X hcomplete x
  have hzeroDeriv :
      mfderiv I I
          (fun y : M => DifferentialGeometry.Analysis.ODE.curveAt X hcomplete y 0) x =
        ContinuousLinearMap.id ℝ (TangentSpace I x) := by
    have hfun :
        (fun y : M => DifferentialGeometry.Analysis.ODE.curveAt X hcomplete y 0) = id := by
      funext y
      exact DifferentialGeometry.Analysis.ODE.curveAt_zero X hcomplete y
    rw [hfun, mfderiv_id]
  by_cases ht : 0 ≤ t
  · rcases ht.eq_or_lt with rfl | htpos
    · rw [hzero, hzeroDeriv]
      rfl
    · have hdiff : DifferentiableOn ℝ P (Set.Icc 0 t) := by
        intro r _
        exact (hhas r).differentiableAt.differentiableWithinAt
      have hderiv : ∀ r ∈ Set.Ico 0 t,
          derivWithin P (Set.Icc 0 t) r = 0 := by
        intro r hr
        have hrIcc : r ∈ Set.Icc 0 t := ⟨hr.1, le_of_lt hr.2⟩
        exact (hhas r).hasDerivWithinAt.derivWithin
          ((uniqueDiffOn_Icc htpos) r hrIcc)
      have hconst := constant_of_derivWithin_zero hdiff hderiv t
        (right_mem_Icc.mpr ht)
      change P t = P 0 at hconst
      dsimp only [P] at hconst
      rw [hzero, hzeroDeriv] at hconst
      simpa only [ContinuousLinearMap.id_apply] using hconst
  · have htneg : t < 0 := lt_of_not_ge ht
    have hdiff : DifferentiableOn ℝ P (Set.Icc t 0) := by
      intro r _
      exact (hhas r).differentiableAt.differentiableWithinAt
    have hderiv : ∀ r ∈ Set.Ico t 0,
        derivWithin P (Set.Icc t 0) r = 0 := by
      intro r hr
      have hrIcc : r ∈ Set.Icc t 0 := ⟨hr.1, le_of_lt hr.2⟩
      exact (hhas r).hasDerivWithinAt.derivWithin
        ((uniqueDiffOn_Icc htneg) r hrIcc)
    have hconst := constant_of_derivWithin_zero hdiff hderiv 0
      (right_mem_Icc.mpr (le_of_lt htneg))
    change P 0 = P t at hconst
    dsimp only [P] at hconst
    rw [hzero, hzeroDeriv] at hconst
    simpa only [ContinuousLinearMap.id_apply] using hconst.symm

private theorem mfderiv_globalIntegralCurve_joint_apply
    [CompleteSpace E]
    (X : Cₛ^∞⟮I; E, TangentSpace I⟯)
    (hcomplete : ∀ x : M, ∃ gamma : ℝ → M,
      And (gamma 0 = x) (IsMIntegralCurve gamma X))
    (t : ℝ) (x : M) (r : ℝ) (v : TangentSpace I x) :
    (mfderiv (𝓘(ℝ, ℝ).prod I) I
      (fun p : ℝ × M =>
        DifferentialGeometry.Analysis.ODE.curveAt X hcomplete p.2 p.1) (t, x))
      (show TangentSpace (𝓘(ℝ, ℝ).prod I) (t, x) from (r, v)) =
        r • X (DifferentialGeometry.Analysis.ODE.curveAt X hcomplete x t) +
          (mfderiv I I
            (fun y : M => DifferentialGeometry.Analysis.ODE.curveAt X hcomplete y t) x) v := by
  let Phi : ℝ × M → M := fun p =>
    DifferentialGeometry.Analysis.ODE.curveAt X hcomplete p.2 p.1
  have hPhi : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ Phi :=
    DifferentialGeometry.Analysis.ODE.contMDiff_globalFlow_joint_of_complete
      X X.contMDiff hcomplete
  have hPhiMD : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) I Phi (t, x) :=
    (hPhi (t, x)).mdifferentiableAt (by simp)
  have htime :
      (mfderiv 𝓘(ℝ, ℝ) I (fun u : ℝ => Phi (u, x)) t) r =
        r • X (DifferentialGeometry.Analysis.ODE.curveAt X hcomplete x t) := by
    have hcurve :=
      DifferentialGeometry.Analysis.ODE.curveAt_integralCurve X hcomplete x t
    rw [hcurve.mfderiv]
    rfl
  change (mfderiv (𝓘(ℝ, ℝ).prod I) I Phi (t, x))
      (show TangentSpace (𝓘(ℝ, ℝ).prod I) (t, x) from (r, v)) = _
  rw [mfderiv_prod_eq_add_apply hPhiMD, htime]

private theorem mfderiv_globalIntegralCurve_product_apply
    [CompleteSpace E]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H' : Type*} [TopologicalSpace H']
    {J : ModelWithCorners ℝ E' H'}
    {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
    (X : Cₛ^∞⟮I; E, TangentSpace I⟯)
    (hcomplete : ∀ x : M, ∃ gamma : ℝ → M,
      And (gamma 0 = x) (IsMIntegralCurve gamma X))
    (Y : N → M) (hY : ContMDiff J I ∞ Y)
    (y : N) (t : ℝ) (u : TangentSpace J y) (r : ℝ) :
    (mfderiv (J.prod 𝓘(ℝ, ℝ)) I
      (fun z : N × ℝ =>
        DifferentialGeometry.Analysis.ODE.curveAt X hcomplete (Y z.1) z.2) (y, t))
      (show TangentSpace (J.prod 𝓘(ℝ, ℝ)) (y, t) from (u, r)) =
        r • X (DifferentialGeometry.Analysis.ODE.curveAt X hcomplete (Y y) t) +
          (mfderiv I I
            (fun z : M => DifferentialGeometry.Analysis.ODE.curveAt X hcomplete z t) (Y y))
            ((mfderiv J I Y y) u) := by
  let Phi : ℝ × M → M := fun p =>
    DifferentialGeometry.Analysis.ODE.curveAt X hcomplete p.2 p.1
  let input : N × ℝ → ℝ × M := fun z => (z.2, Y z.1)
  have hPhi : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ Phi :=
    DifferentialGeometry.Analysis.ODE.contMDiff_globalFlow_joint_of_complete
      X X.contMDiff hcomplete
  have hinput : ContMDiff (J.prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod I) ∞ input :=
    contMDiff_snd.prodMk (hY.comp contMDiff_fst)
  have hPhiMD : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) I Phi (t, Y y) :=
    (hPhi (t, Y y)).mdifferentiableAt (by simp)
  have hinputMD : MDifferentiableAt (J.prod 𝓘(ℝ, ℝ))
      (𝓘(ℝ, ℝ).prod I) input (y, t) :=
    (hinput (y, t)).mdifferentiableAt (by simp)
  have hcomp := mfderiv_comp
    (I := J.prod 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ).prod I) (I'' := I)
    (f := input) (g := Phi) (y, t) hPhiMD hinputMD
  have hinputApply :
      (mfderiv (J.prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod I) input (y, t))
          (show TangentSpace (J.prod 𝓘(ℝ, ℝ)) (y, t) from (u, r)) =
        (r, (mfderiv J I Y y) u) := by
    have hYProdMD : MDifferentiableAt (J.prod 𝓘(ℝ, ℝ)) I
        (fun z : N × ℝ => Y z.1) (y, t) :=
      ((hY.comp contMDiff_fst) (y, t)).mdifferentiableAt (by simp)
    have hderiv :
        mfderiv (J.prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod I) input (y, t) =
          (mfderiv (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ)
            (fun z : N × ℝ => z.2) (y, t)).prod
          (mfderiv (J.prod 𝓘(ℝ, ℝ)) I
            (fun z : N × ℝ => Y z.1) (y, t)) :=
      mfderiv_prodMk mdifferentiableAt_snd
        hYProdMD
    rw [hderiv]
    apply Prod.ext
    · rw [mfderiv_snd]
      rfl
    · have hYcomp :
          mfderiv (J.prod 𝓘(ℝ, ℝ)) I
              (fun z : N × ℝ => Y z.1) (y, t) =
            (mfderiv J I Y y).comp
              (mfderiv (J.prod 𝓘(ℝ, ℝ)) J (fun z : N × ℝ => z.1) (y, t)) :=
        mfderiv_comp (y, t)
          ((hY y).mdifferentiableAt (by simp)) mdifferentiableAt_fst
      rw [hYcomp, mfderiv_fst]
      rfl
  change (mfderiv (J.prod 𝓘(ℝ, ℝ)) I (Phi ∘ input) (y, t))
      (show TangentSpace (J.prod 𝓘(ℝ, ℝ)) (y, t) from (u, r)) = _
  rw [hcomp]
  change (mfderiv (𝓘(ℝ, ℝ).prod I) I Phi (t, Y y))
      ((mfderiv (J.prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod I) input (y, t))
        (show TangentSpace (J.prod 𝓘(ℝ, ℝ)) (y, t) from (u, r))) = _
  rw [hinputApply]
  exact mfderiv_globalIntegralCurve_joint_apply
    X hcomplete t (Y y) r ((mfderiv J I Y y) u)

private theorem globalIntegralCurve_metric_pairing_eq
    [CompleteSpace E]
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, TangentSpace I⟯)
    (hcomplete : ∀ x : M, ∃ gamma : ℝ → M,
      And (gamma 0 = x) (IsMIntegralCurve gamma X))
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hdf : ∀ x, ∀ v : TangentSpace I x,
      mvfderiv (I := I) f x v = g.inner x (X x) v)
    (hunit : ∀ x, g.inner x (X x) (X x) = 1)
    (t : ℝ) (x : M) (v : TangentSpace I x) :
    g.inner (DifferentialGeometry.Analysis.ODE.curveAt X hcomplete x t)
        (X (DifferentialGeometry.Analysis.ODE.curveAt X hcomplete x t))
        ((mfderiv I I
          (fun y : M => DifferentialGeometry.Analysis.ODE.curveAt X hcomplete y t) x) v) =
      g.inner x (X x) v := by
  let Phi : M → M := fun y =>
    DifferentialGeometry.Analysis.ODE.curveAt X hcomplete y t
  have hPhi : ContMDiff I I ∞ Phi := by
    intro y
    exact DifferentialGeometry.Analysis.ODE.contMDiffAt_globalFlow_of_complete
      X X.contMDiff hcomplete t y
  have hPhiMD : MDifferentiableAt I I Phi x :=
    (hPhi x).mdifferentiableAt (by simp)
  have hfMD : MDifferentiableAt I 𝓘(ℝ, ℝ) f (Phi x) :=
    (hf (Phi x)).mdifferentiableAt (by simp)
  have hcomp := mvfderiv_comp_apply (I := I) (I' := I)
    (f := Phi) (g := f) x hfMD hPhiMD v
  have hfun : (f ∘ Phi) = fun y : M => f y + t := by
    funext y
    exact globalIntegralCurve_potential_eq_add
      g X hcomplete f hf hdf hunit t y
  have heq : mvfderiv (I := I) (f ∘ Phi) x v =
      mvfderiv (I := I) (fun y : M => f y + t) x v := by
    rw [hfun]
  have hrhs :
      mvfderiv (I := I) (fun y : M => f y + t) x v =
        mvfderiv (I := I) f x v := by
    change mvfderiv (I := I) (f + fun _ : M => t) x v = _
    rw [mvfderiv_add
      ((hf x).mdifferentiableAt (by simp)) mdifferentiableAt_const,
      mvfderiv_const]
    simp
  calc
    g.inner (DifferentialGeometry.Analysis.ODE.curveAt X hcomplete x t)
        (X (DifferentialGeometry.Analysis.ODE.curveAt X hcomplete x t))
        ((mfderiv I I
          (fun y : M => DifferentialGeometry.Analysis.ODE.curveAt X hcomplete y t) x) v) =
        mvfderiv (I := I) f (Phi x) ((mfderiv I I Phi x) v) := by
      rw [hdf]
    _ = mvfderiv (I := I) (f ∘ Phi) x v := hcomp.symm
    _ = mvfderiv (I := I) (fun y : M => f y + t) x v := heq
    _ = mvfderiv (I := I) f x v := hrhs
    _ = g.inner x (X x) v := hdf x v

theorem exists_global_product_diffeomorph_with_potential_from_parallel_unit_section
    {m : ℕ}
    {H : Type} [TopologicalSpace H]
    {I : ModelWithCorners ℝ
      (DifferentialGeometry.Topology.Morse.MorseModel (m + 1)) H}
    [I.Boundaryless]
    {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [T2Space M]
    [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
    [ConnectedSpace M] [SimplyConnectedSpace M]
    (g : SmoothRiemannianMetric I M)
    (hg : RiemannianMetricComplete (I := I) g)
    (X : Cₛ^∞⟮I; DifferentialGeometry.Topology.Morse.MorseModel (m + 1),
      TangentSpace I⟯)
    (hunit : ∀ x, g.inner x (X x) (X x) = 1)
    (hparallel : ∀ x, ∀ v : TangentSpace I x,
      (LeviCivita (I := I) g) X x v = 0) :
    ∃ (f : M → ℝ)
      (_ : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
      (_ : ∀ x, ∀ v : TangentSpace I x,
        mvfderiv (I := I) f x v = g.inner x (X x) v)
      (_ : ∀ x, f x = 0 →
        ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x),
      ∃ hcs : ChartedSpace
          (DifferentialGeometry.Topology.Morse.MorseModel m)
          (DifferentialGeometry.Topology.Morse.LevelSetSpace (M := M) f 0),
        let _ := hcs
        ∃ hmanifold : IsManifold
            (𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel m))
            (↑(⊤ : ℕ∞) : WithTop ℕ∞)
            (DifferentialGeometry.Topology.Morse.LevelSetSpace (M := M) f 0),
          let _ := hmanifold
          ∃ hσ : SigmaCompactSpace
              (DifferentialGeometry.Topology.Morse.LevelSetSpace (M := M) f 0),
            let _ := hσ
            ∃ h : SmoothRiemannianMetric
                (𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel m))
                (DifferentialGeometry.Topology.Morse.LevelSetSpace (M := M) f 0),
              And (RiemannianMetricComplete
                (I := 𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel m)) h)
              (∃ F : Diffeomorph
              ((𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel m)).prod 𝓘(ℝ, ℝ)) I
              (DifferentialGeometry.Topology.Morse.LevelSetSpace (M := M) f 0 × ℝ) M
              (↑(⊤ : ℕ∞) : WithTop ℕ∞),
            And
              (∀ (y : DifferentialGeometry.Topology.Morse.LevelSetSpace (M := M) f 0)
                  (t : ℝ),
                F (y, t) =
                  DifferentialGeometry.Analysis.ODE.curveAt X
                    (exists_globalIntegralCurve_of_unit_section g hg X hunit)
                    (show M from y.1) t)
              (And
                (∀ (y : DifferentialGeometry.Topology.Morse.LevelSetSpace (M := M) f 0)
                    (t r : ℝ),
                  (mfderiv
                    ((𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel m)).prod
                      𝓘(ℝ, ℝ)) I
                    (fun z :
                      DifferentialGeometry.Topology.Morse.LevelSetSpace (M := M) f 0 × ℝ =>
                        F z) (y, t))
                    (show TangentSpace
                      ((𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel m)).prod
                        𝓘(ℝ, ℝ)) (y, t) from (0, r)) =
                      r • X (F (y, t)))
                (And
                  (ConnectedSpace
                    (DifferentialGeometry.Topology.Morse.LevelSetSpace (M := M) f 0))
                  (And
                    (SimplyConnectedSpace
                      (DifferentialGeometry.Topology.Morse.LevelSetSpace (M := M) f 0))
                    (∀ (y : DifferentialGeometry.Topology.Morse.LevelSetSpace (M := M) f 0)
                        (t : ℝ)
                        (u v : TangentSpace
                          (𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel m)) y)
                        (r q : ℝ),
                      g.inner (F (y, t))
                          ((mfderiv
                            ((𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel m)).prod
                              𝓘(ℝ, ℝ)) I
                            (fun z :
                              DifferentialGeometry.Topology.Morse.LevelSetSpace (M := M) f 0 × ℝ =>
                                F z) (y, t))
                            (show TangentSpace
                              ((𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel m)).prod
                                𝓘(ℝ, ℝ)) (y, t) from (u, r)))
                          ((mfderiv
                            ((𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel m)).prod
                              𝓘(ℝ, ℝ)) I
                            (fun z :
                              DifferentialGeometry.Topology.Morse.LevelSetSpace (M := M) f 0 × ℝ =>
                                F z) (y, t))
                            (show TangentSpace
                              ((𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel m)).prod
                                𝓘(ℝ, ℝ)) (y, t) from (v, q))) =
                        h.inner y u v + r * q))))) := by
  obtain ⟨f0, hf0, hdf0⟩ :=
    exists_global_gradient_potential_of_parallel_section g X hparallel
  let p0 : M := Classical.arbitrary M
  let f : M → ℝ := fun x => f0 x - f0 p0
  have hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f := by
    exact hf0.sub contMDiff_const
  have hdf : ∀ x, ∀ v : TangentSpace I x,
      mvfderiv (I := I) f x v = g.inner x (X x) v := by
    intro x v
    change mvfderiv (I := I) (f0 - fun _ => f0 p0) x v = _
    rw [mvfderiv_sub
      ((hf0 x).mdifferentiableAt (by simp)) mdifferentiableAt_const,
      mvfderiv_const, sub_zero, hdf0]
  have hreg : ∀ x, f x = 0 →
      ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I f x := by
    intro x _ hx
    unfold DifferentialGeometry.Topology.Morse.IsCriticalPointAt at hx
    have hxX := congrArg (fun L : TangentSpace I x →L[ℝ] ℝ => L (X x)) hx
    change mvfderiv (I := I) f x (X x) = 0 at hxX
    rw [hdf x (X x), hunit x] at hxX
    norm_num at hxX
  let hcs := DifferentialGeometry.Topology.Morse.manifoldLevelSetChartedSpace
    I f 0 hf hreg
  let _ := hcs
  have hmanifold : IsManifold
      (𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel m))
      (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (DifferentialGeometry.Topology.Morse.LevelSetSpace (M := M) f 0) :=
    DifferentialGeometry.Topology.Morse.manifoldLevelSetIsManifold
      I f 0 hf hreg
  let _ := hmanifold
  have hclosed : IsClosed {x : M | f x = 0} :=
    isClosed_eq hf.continuous continuous_const
  let hσ : SigmaCompactSpace
      (DifferentialGeometry.Topology.Morse.LevelSetSpace (M := M) f 0) :=
    hclosed.sigmaCompactSpace
  let _ := hσ
  refine ⟨f, hf, hdf, hreg, hcs, hmanifold, hσ, ?_⟩
  let hcomplete := exists_globalIntegralCurve_of_unit_section g hg X hunit
  let forward :
      DifferentialGeometry.Topology.Morse.LevelSetSpace (M := M) f 0 × ℝ → M :=
    fun p => DifferentialGeometry.Analysis.ODE.curveAt X hcomplete p.1.1 p.2
  have hflowPotential : ∀ t x,
      f (DifferentialGeometry.Analysis.ODE.curveAt X hcomplete x t) = f x + t := by
    intro t x
    exact globalIntegralCurve_potential_eq_add
      g X hcomplete f hf hdf hunit t x
  let backward : M →
      DifferentialGeometry.Topology.Morse.LevelSetSpace (M := M) f 0 × ℝ :=
    fun p =>
      (⟨DifferentialGeometry.Analysis.ODE.curveAt X hcomplete p (-f p), by
        rw [hflowPotential]
        ring⟩, f p)
  have hX1 : CMDiff 1
      (fun x : M => (⟨x, X x⟩ : TangentBundle I M)) :=
    X.contMDiff.of_le (by norm_num)
  have hleft : ∀ p, backward (forward p) = p := by
    rintro ⟨y, t⟩
    apply Prod.ext
    · apply Subtype.ext
      change DifferentialGeometry.Analysis.ODE.curveAt X hcomplete
          (DifferentialGeometry.Analysis.ODE.curveAt X hcomplete y.1 t)
          (-f (DifferentialGeometry.Analysis.ODE.curveAt X hcomplete y.1 t)) = y.1
      rw [hflowPotential t y.1, y.2]
      simp only [zero_add]
      rw [← DifferentialGeometry.Analysis.ODE.curveAt_add X hX1 hcomplete]
      simpa using DifferentialGeometry.Analysis.ODE.curveAt_zero X hcomplete y.1
    · change f (DifferentialGeometry.Analysis.ODE.curveAt X hcomplete y.1 t) = t
      rw [hflowPotential t y.1, y.2, zero_add]
  have hright : ∀ p, forward (backward p) = p := by
    intro p
    change DifferentialGeometry.Analysis.ODE.curveAt X hcomplete
        (DifferentialGeometry.Analysis.ODE.curveAt X hcomplete p (-f p)) (f p) = p
    rw [← DifferentialGeometry.Analysis.ODE.curveAt_add X hX1 hcomplete]
    simpa using DifferentialGeometry.Analysis.ODE.curveAt_zero X hcomplete p
  have hflow : ContMDiff (𝓘(ℝ, ℝ).prod I) I
      (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × M =>
        DifferentialGeometry.Analysis.ODE.curveAt X hcomplete p.2 p.1) := by
    let _ : CompleteSpace
        (DifferentialGeometry.Topology.Morse.MorseModel (m + 1)) :=
      FiniteDimensional.complete ℝ
        (DifferentialGeometry.Topology.Morse.MorseModel (m + 1))
    exact DifferentialGeometry.Analysis.ODE.contMDiff_globalFlow_joint_of_complete
      X X.contMDiff hcomplete
  have hinclusion : ContMDiff
      (𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel m)) I
      (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : DifferentialGeometry.Topology.Morse.LevelSetSpace (M := M) f 0 => y.1) :=
    DifferentialGeometry.Topology.Morse.contMDiff_levelSetInclusion
      I f 0 hf hreg
  have hforward : ContMDiff
      ((𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel m)).prod 𝓘(ℝ, ℝ)) I
      (↑(⊤ : ℕ∞) : WithTop ℕ∞) forward := by
    have hinput : ContMDiff
        ((𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel m)).prod 𝓘(ℝ, ℝ))
        (𝓘(ℝ, ℝ).prod I) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : DifferentialGeometry.Topology.Morse.LevelSetSpace (M := M) f 0 × ℝ =>
          (p.2, p.1.1)) :=
      contMDiff_snd.prodMk (hinclusion.comp contMDiff_fst)
    exact hflow.comp hinput
  let base : M → M := fun p =>
    DifferentialGeometry.Analysis.ODE.curveAt X hcomplete p (-f p)
  have hbase : ContMDiff I I (↑(⊤ : ℕ∞) : WithTop ℕ∞) base := by
    have hinput : ContMDiff I (𝓘(ℝ, ℝ).prod I)
        (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun p : M => (-f p, p)) :=
      hf.neg.prodMk contMDiff_id
    exact hflow.comp hinput
  have hbaseLevel : ∀ p, f (base p) = 0 := by
    intro p
    change f (DifferentialGeometry.Analysis.ODE.curveAt X hcomplete p (-f p)) = 0
    rw [hflowPotential]
    ring
  have hbaseFactor : ContMDiff I
      (𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel m))
      (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : M =>
        (⟨base p, hbaseLevel p⟩ :
          DifferentialGeometry.Topology.Morse.LevelSetSpace (M := M) f 0)) :=
    DifferentialGeometry.Topology.Morse.contMDiff_levelSet_factor
      I f 0 hf hreg base hbase hbaseLevel
  have hbackward : ContMDiff I
      ((𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel m)).prod 𝓘(ℝ, ℝ))
      (↑(⊤ : ℕ∞) : WithTop ℕ∞) backward := by
    exact hbaseFactor.prodMk hf
  let e :
      DifferentialGeometry.Topology.Morse.LevelSetSpace (M := M) f 0 × ℝ ≃ M :=
    { toFun := forward
      invFun := backward
      left_inv := hleft
      right_inv := hright }
  let F : Diffeomorph
      ((𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel m)).prod 𝓘(ℝ, ℝ)) I
      (DifferentialGeometry.Topology.Morse.LevelSetSpace (M := M) f 0 × ℝ) M
      (↑(⊤ : ℕ∞) : WithTop ℕ∞) :=
    { toEquiv := e
      contMDiff_toFun := hforward
      contMDiff_invFun := hbackward }
  let G := Diffeomorph.pullbackMetricCross g F
  let h := G.sliceFst 0
  have hGcomplete : RiemannianMetricComplete
      (I := (𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel m)).prod 𝓘(ℝ, ℝ)) G :=
    RiemannianMetricComplete.pullbackCross g F hg
  have hhcomplete : RiemannianMetricComplete
      (I := 𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel m)) h :=
    RiemannianMetricComplete.sliceFst G 0 hGcomplete
  refine ⟨h, hhcomplete, F, ?_, ?_, ?_, ?_, ?_⟩
  · intro y t
    rfl
  · intro y t r
    let J := 𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel m)
    let inclusion :
        DifferentialGeometry.Topology.Morse.LevelSetSpace (M := M) f 0 → M :=
      fun z => z.1
    have hdirection := mfderiv_globalIntegralCurve_product_apply
      X hcomplete inclusion hinclusion y t 0 r
    have hzero : (mfderiv J I inclusion y) 0 = 0 :=
      map_zero (mfderiv J I inclusion y)
    rw [hzero, map_zero, add_zero] at hdirection
    exact hdirection
  · let p : M → DifferentialGeometry.Topology.Morse.LevelSetSpace (M := M) f 0 :=
      fun x => (F.symm x).1
    have hp : Function.Surjective p := by
      intro y
      exact ⟨F (y, 0), by simp [p]⟩
    exact hp.connectedSpace (continuous_fst.comp F.toHomeomorph.symm.continuous)
  · have hprod : SimplyConnectedSpace
        (DifferentialGeometry.Topology.Morse.LevelSetSpace (M := M) f 0 × ℝ) :=
      F.toHomeomorph.toHomotopyEquiv.simplyConnectedSpace_iff.mpr inferInstance
    let eR : ContinuousMap.HomotopyEquiv ℝ Unit :=
      Classical.choice (ContractibleSpace.hequiv ℝ Unit)
    let e : ContinuousMap.HomotopyEquiv
        (DifferentialGeometry.Topology.Morse.LevelSetSpace (M := M) f 0 × ℝ)
        (DifferentialGeometry.Topology.Morse.LevelSetSpace (M := M) f 0) :=
      ((ContinuousMap.HomotopyEquiv.refl
        (DifferentialGeometry.Topology.Morse.LevelSetSpace (M := M) f 0)).prodCongr eR).trans
        (Homeomorph.prodUnique
          (DifferentialGeometry.Topology.Morse.LevelSetSpace (M := M) f 0) Unit).toHomotopyEquiv
    exact e.simplyConnectedSpace_iff.mp hprod
  · intro y t u v r q
    let J := 𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel m)
    let inclusion :
        DifferentialGeometry.Topology.Morse.LevelSetSpace (M := M) f 0 → M :=
      fun z => z.1
    let Phi : M → M := fun z =>
      DifferentialGeometry.Analysis.ODE.curveAt X hcomplete z t
    let du : TangentSpace I y.1 := (mfderiv J I inclusion y) u
    let dv : TangentSpace I y.1 := (mfderiv J I inclusion y) v
    let z : TangentSpace I
        (DifferentialGeometry.Analysis.ODE.curveAt X hcomplete y.1 t) :=
      X (DifferentialGeometry.Analysis.ODE.curveAt X hcomplete y.1 t)
    let A : TangentSpace I
        (DifferentialGeometry.Analysis.ODE.curveAt X hcomplete y.1 t) :=
      (mfderiv I I Phi y.1) du
    let B : TangentSpace I
        (DifferentialGeometry.Analysis.ODE.curveAt X hcomplete y.1 t) :=
      (mfderiv I I Phi y.1) dv
    have hinclusionMD : MDifferentiableAt J I inclusion y :=
      (hinclusion y).mdifferentiableAt (by simp)
    have hfMD : MDifferentiableAt I 𝓘(ℝ, ℝ) f y.1 :=
      (hf y.1).mdifferentiableAt (by simp)
    have hchainU := mvfderiv_comp_apply (I := I) (I' := J)
      (f := inclusion) (g := f) y hfMD hinclusionMD u
    have hchainV := mvfderiv_comp_apply (I := I) (I' := J)
      (f := inclusion) (g := f) y hfMD hinclusionMD v
    have hlevelU : mvfderiv (I := J) (f ∘ inclusion) y u = 0 := by
      have hfun : (f ∘ inclusion) = fun _ => (0 : ℝ) := by
        funext w
        exact w.2
      rw [hfun, mvfderiv_const]
      rfl
    have hlevelV : mvfderiv (I := J) (f ∘ inclusion) y v = 0 := by
      have hfun : (f ∘ inclusion) = fun _ => (0 : ℝ) := by
        funext w
        exact w.2
      rw [hfun, mvfderiv_const]
      rfl
    rw [hchainU] at hlevelU
    rw [hchainV] at hlevelV
    have horthU : g.inner y.1 (X y.1) du = 0 := by
      rw [← hdf]
      exact hlevelU
    have horthV : g.inner y.1 (X y.1) dv = 0 := by
      rw [← hdf]
      exact hlevelV
    have hpair :
        g.inner (DifferentialGeometry.Analysis.ODE.curveAt X hcomplete y.1 t) A B =
          g.inner y.1 du dv := by
      exact globalIntegralCurve_inner_eq_of_parallel_section
        g X hcomplete hparallel t y.1 du dv
    have hzA :
        g.inner (DifferentialGeometry.Analysis.ODE.curveAt X hcomplete y.1 t) z A = 0 := by
      have hpairing := globalIntegralCurve_metric_pairing_eq
        g X hcomplete f hf hdf hunit t y.1 du
      simpa [z, A, Phi] using hpairing.trans horthU
    have hzB :
        g.inner (DifferentialGeometry.Analysis.ODE.curveAt X hcomplete y.1 t) z B = 0 := by
      have hpairing := globalIntegralCurve_metric_pairing_eq
        g X hcomplete f hf hdf hunit t y.1 dv
      simpa [z, B, Phi] using hpairing.trans horthV
    have hAz :
        g.inner (DifferentialGeometry.Analysis.ODE.curveAt X hcomplete y.1 t) A z = 0 := by
      rw [g.symm]
      exact hzA
    have hunitFlow :
        g.inner (DifferentialGeometry.Analysis.ODE.curveAt X hcomplete y.1 t) z z = 1 := by
      exact hunit _
    have hdu := mfderiv_globalIntegralCurve_product_apply
      X hcomplete inclusion hinclusion y t u r
    have hdv := mfderiv_globalIntegralCurve_product_apply
      X hcomplete inclusion hinclusion y t v q
    change g.inner (DifferentialGeometry.Analysis.ODE.curveAt X hcomplete y.1 t)
      ((mfderiv (J.prod 𝓘(ℝ, ℝ)) I forward (y, t))
        (show TangentSpace (J.prod 𝓘(ℝ, ℝ)) (y, t) from (u, r)))
      ((mfderiv (J.prod 𝓘(ℝ, ℝ)) I forward (y, t))
        (show TangentSpace (J.prod 𝓘(ℝ, ℝ)) (y, t) from (v, q))) =
      h.inner y u v + r * q
    rw [hdu, hdv]
    change g.inner (DifferentialGeometry.Analysis.ODE.curveAt X hcomplete y.1 t)
      (r • z + A) (q • z + B) = _
    have hexpand :
        g.inner (DifferentialGeometry.Analysis.ODE.curveAt X hcomplete y.1 t)
            (r • z + A) (q • z + B) =
          r * q * g.inner
              (DifferentialGeometry.Analysis.ODE.curveAt X hcomplete y.1 t) z z +
            r * g.inner
              (DifferentialGeometry.Analysis.ODE.curveAt X hcomplete y.1 t) z B +
            q * g.inner
              (DifferentialGeometry.Analysis.ODE.curveAt X hcomplete y.1 t) A z +
            g.inner
              (DifferentialGeometry.Analysis.ODE.curveAt X hcomplete y.1 t) A B := by
      simp [smul_eq_mul]
      ring
    have hh : h.inner y u v = g.inner y.1 du dv := by
      have hflowZero :
          (fun w : M =>
            DifferentialGeometry.Analysis.ODE.curveAt X hcomplete w 0) = id := by
        funext w
        exact DifferentialGeometry.Analysis.ODE.curveAt_zero X hcomplete w
      have hduZero := mfderiv_globalIntegralCurve_product_apply
        X hcomplete inclusion hinclusion y 0 u 0
      have hdvZero := mfderiv_globalIntegralCurve_product_apply
        X hcomplete inclusion hinclusion y 0 v 0
      calc
        h.inner y u v =
            G.inner (y, 0)
              (show TangentSpace (J.prod 𝓘(ℝ, ℝ)) (y, 0) from (u, 0))
              (show TangentSpace (J.prod 𝓘(ℝ, ℝ)) (y, 0) from (v, 0)) := by
          exact SmoothRiemannianMetric.sliceFst_inner G 0 y u v
        _ = g.inner (F (y, 0))
            ((mfderiv (J.prod 𝓘(ℝ, ℝ)) I (fun w => F w) (y, 0))
              (show TangentSpace (J.prod 𝓘(ℝ, ℝ)) (y, 0) from (u, 0)))
            ((mfderiv (J.prod 𝓘(ℝ, ℝ)) I (fun w => F w) (y, 0))
              (show TangentSpace (J.prod 𝓘(ℝ, ℝ)) (y, 0) from (v, 0))) := by
          exact Diffeomorph.pullbackMetricCross_inner g F (y, 0)
            (show TangentSpace (J.prod 𝓘(ℝ, ℝ)) (y, 0) from (u, 0))
            (show TangentSpace (J.prod 𝓘(ℝ, ℝ)) (y, 0) from (v, 0))
        _ = g.inner y.1 du dv := by
          change g.inner
            (DifferentialGeometry.Analysis.ODE.curveAt X hcomplete y.1 0)
            ((mfderiv (J.prod 𝓘(ℝ, ℝ)) I forward (y, 0))
              (show TangentSpace (J.prod 𝓘(ℝ, ℝ)) (y, 0) from (u, 0)))
            ((mfderiv (J.prod 𝓘(ℝ, ℝ)) I forward (y, 0))
              (show TangentSpace (J.prod 𝓘(ℝ, ℝ)) (y, 0) from (v, 0))) =
              g.inner y.1 du dv
          rw [hduZero, hdvZero, hflowZero, mfderiv_id]
          simp only [zero_smul, zero_add]
          rw [DifferentialGeometry.Analysis.ODE.curveAt_zero]
          rfl
    rw [hexpand, hunitFlow, hzB, hAz, hpair, hh]
    ring

theorem exists_global_product_diffeomorph_from_parallel_unit_section
    {m : ℕ}
    {H : Type} [TopologicalSpace H]
    {I : ModelWithCorners ℝ
      (DifferentialGeometry.Topology.Morse.MorseModel (m + 1)) H}
    [I.Boundaryless]
    {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [T2Space M]
    [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
    [ConnectedSpace M] [SimplyConnectedSpace M]
    (g : SmoothRiemannianMetric I M)
    (hg : RiemannianMetricComplete (I := I) g)
    (X : Cₛ^∞⟮I; DifferentialGeometry.Topology.Morse.MorseModel (m + 1),
      TangentSpace I⟯)
    (hunit : ∀ x, g.inner x (X x) (X x) = 1)
    (hparallel : ∀ x, ∀ v : TangentSpace I x,
      (LeviCivita (I := I) g) X x v = 0) :
    ∃ (N : Type) (_ : TopologicalSpace N)
      (hcs : ChartedSpace
        (DifferentialGeometry.Topology.Morse.MorseModel m) N),
      let _ := hcs
      ∃ hmanifold : IsManifold
          (𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel m))
          (↑(⊤ : ℕ∞) : WithTop ℕ∞) N,
        let _ := hmanifold
        ∃ ht2 : T2Space N,
          let _ := ht2
          ∃ hσ : SigmaCompactSpace N,
            let _ := hσ
            ∃ h : SmoothRiemannianMetric
                (𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel m)) N,
              And (ConnectedSpace N)
              (And (SimplyConnectedSpace N)
              (And (RiemannianMetricComplete
                (I := 𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel m)) h)
              (∃ F : Diffeomorph
                  ((𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel m)).prod
                    𝓘(ℝ, ℝ)) I (N × ℝ) M
                  (↑(⊤ : ℕ∞) : WithTop ℕ∞),
                And
                  (∀ (y : N) (t r : ℝ),
                    (mfderiv
                      ((𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel m)).prod
                        𝓘(ℝ, ℝ)) I
                      (fun z : N × ℝ => F z) (y, t))
                      (show TangentSpace
                        ((𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel m)).prod
                          𝓘(ℝ, ℝ)) (y, t) from (0, r)) =
                        r • X (F (y, t)))
                  (∀ (y : N) (t : ℝ)
                      (u v : TangentSpace
                        (𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel m)) y)
                      (r q : ℝ),
                    g.inner (F (y, t))
                        ((mfderiv
                          ((𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel m)).prod
                            𝓘(ℝ, ℝ)) I
                          (fun z : N × ℝ => F z) (y, t))
                          (show TangentSpace
                            ((𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel m)).prod
                              𝓘(ℝ, ℝ)) (y, t) from (u, r)))
                        ((mfderiv
                          ((𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel m)).prod
                            𝓘(ℝ, ℝ)) I
                          (fun z : N × ℝ => F z) (y, t))
                          (show TangentSpace
                            ((𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel m)).prod
                              𝓘(ℝ, ℝ)) (y, t) from (v, q))) =
                      h.inner y u v + r * q)))) := by
  obtain ⟨f, hf, hdf, hreg, hcs, hmanifold, hσ, h, hhcomplete,
      F, hF, hdirection, hconnected, hsimplyConnected, hmetric⟩ :=
    exists_global_product_diffeomorph_with_potential_from_parallel_unit_section
      g hg X hunit hparallel
  let _ := hcs
  let _ := hmanifold
  let _ := hσ
  exact ⟨DifferentialGeometry.Topology.Morse.LevelSetSpace (M := M) f 0,
    inferInstance, hcs, hmanifold, inferInstance, hσ, h,
    hconnected, hsimplyConnected, hhcomplete, F, hdirection, hmetric⟩

theorem ContMDiffVectorSubbundle.exists_global_product_diffeomorph_of_rank_eq_one
    {m : ℕ}
    {H : Type} [TopologicalSpace H]
    {I : ModelWithCorners ℝ
      (DifferentialGeometry.Topology.Morse.MorseModel (m + 1)) H}
    [I.Boundaryless]
    {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [T2Space M]
    [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
    [ConnectedSpace M] [SimplyConnectedSpace M]
    (g : SmoothRiemannianMetric I M)
    (hg : RiemannianMetricComplete (I := I) g)
    (S : ContMDiffVectorSubbundle
      (I := I) (F := DifferentialGeometry.Topology.Morse.MorseModel (m + 1))
      (V := TangentSpace I) (n := (∞ : WithTop ℕ∞)))
    (hSrank : S.rank = 1)
    (hS : IsParallelSubmoduleFamily g S.fiber) :
    ∃ (N : Type) (_ : TopologicalSpace N)
      (hcs : ChartedSpace
        (DifferentialGeometry.Topology.Morse.MorseModel m) N),
      let _ := hcs
      ∃ hmanifold : IsManifold
          (𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel m))
          (↑(⊤ : ℕ∞) : WithTop ℕ∞) N,
        let _ := hmanifold
        ∃ ht2 : T2Space N,
          let _ := ht2
          ∃ hσ : SigmaCompactSpace N,
            let _ := hσ
            ∃ h : SmoothRiemannianMetric
                (𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel m)) N,
              And (ConnectedSpace N)
              (And (SimplyConnectedSpace N)
              (And (RiemannianMetricComplete
                (I := 𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel m)) h)
              (∃ F : Diffeomorph
                  ((𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel m)).prod
                    𝓘(ℝ, ℝ)) I (N × ℝ) M
                  (↑(⊤ : ℕ∞) : WithTop ℕ∞),
                And
                  (∀ (y : N) (t : ℝ),
                    S.fiber (F (y, t)) =
                      ℝ ∙
                        ((mfderiv
                          ((𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel m)).prod
                            𝓘(ℝ, ℝ)) I
                          (fun z : N × ℝ => F z) (y, t))
                          (show TangentSpace
                            ((𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel m)).prod
                              𝓘(ℝ, ℝ)) (y, t) from (0, 1))))
                  (∀ (y : N) (t : ℝ)
                      (u v : TangentSpace
                        (𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel m)) y)
                      (r q : ℝ),
                    g.inner (F (y, t))
                        ((mfderiv
                          ((𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel m)).prod
                            𝓘(ℝ, ℝ)) I
                          (fun z : N × ℝ => F z) (y, t))
                          (show TangentSpace
                            ((𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel m)).prod
                              𝓘(ℝ, ℝ)) (y, t) from (u, r)))
                        ((mfderiv
                          ((𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel m)).prod
                            𝓘(ℝ, ℝ)) I
                          (fun z : N × ℝ => F z) (y, t))
                          (show TangentSpace
                            ((𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel m)).prod
                              𝓘(ℝ, ℝ)) (y, t) from (v, q))) =
                      h.inner y u v + r * q)))) := by
  obtain ⟨X, hXmem, hunit, hparallel⟩ :=
    DifferentialGeometry.Geometry.Connection.ContMDiffVectorSubbundle.exists_global_parallel_unit_section_of_rank_eq_one
      g S hSrank hS
  obtain ⟨N, topologyN, hcs, hmanifold, ht2, hσ, h,
      hconnected, hsimplyConnected, hhcomplete, F, hdirection, hmetric⟩ :=
    exists_global_product_diffeomorph_from_parallel_unit_section
      g hg X hunit hparallel
  let _ := topologyN
  let _ := hcs
  let _ := hmanifold
  let _ := ht2
  let _ := hσ
  refine ⟨N, topologyN, hcs, hmanifold, ht2, hσ, h,
    hconnected, hsimplyConnected, hhcomplete, F, ?_, hmetric⟩
  intro y t
  have hfin : Module.finrank ℝ (S.fiber (F (y, t))) = 1 := by
    rw [S.finrank_fiber, hSrank]
  have hXne : X (F (y, t)) ≠ 0 := by
    intro hzero
    have hx := hunit (F (y, t))
    rw [hzero] at hx
    simp at hx
  have hspan : S.fiber (F (y, t)) = ℝ ∙ X (F (y, t)) :=
    eq_span_singleton_of_mem_of_finrank_eq_one
      hfin (hXmem (F (y, t))) hXne
  rw [hdirection y t 1, one_smul]
  exact hspan

end DifferentialGeometry.Geometry.Connection
