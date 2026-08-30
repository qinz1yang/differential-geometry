import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Tail.ActionBranch
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Index.PiecewiseNonnegativity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Index.Algebra
import DifferentialGeometry.Geometry.Connection.ChartBridge.Hessian
import DifferentialGeometry.Geometry.Connection.ChartBridge.Gradient
import DifferentialGeometry.Geometry.Comparison.Variation.BoundedCurve
import DifferentialGeometry.Geometry.Comparison.Variation.CovariantChainRule
import DifferentialGeometry.Analysis.Calculus.SmoothClamp

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Filter Set
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {D : RealTimeInterval}

private theorem tailHess_clamp
    {K : Set Real} {a b : Real} (hKopen : IsOpen K)
    (hKconn : IsPreconnected K) (haK : a ∈ K) (hbK : b ∈ K)
    (hab : a < b) :
    ∃ rho : Real → Real, ∃ lo hi : Real,
      lo < a ∧ b < hi ∧ ContDiff Real ∞ rho ∧
        Set.EqOn rho id (Icc lo hi) ∧ ∀ s, rho s ∈ K := by
  have hseg : Icc a b ⊆ K := by
    simpa only [uIcc_of_le hab.le] using
      hKconn.ordConnected.uIcc_subset haK hbK
  obtain ⟨margin, hmargin, hbuffer⟩ :=
    isCompact_Icc.exists_cthickening_subset_open hKopen hseg
  let lo := a - margin / 2
  let hi := b + margin / 2
  let eps := margin / 4
  obtain ⟨rho, hrho, hrhoId, _hrho', hrange⟩ :=
    DifferentialGeometry.exists_smooth_time_clamp lo hi eps (by
      dsimp only [lo, hi]; linarith) (by dsimp only [eps]; linarith)
  refine ⟨rho, lo, hi, (by dsimp only [lo]; linarith),
    (by dsimp only [hi]; linarith), hrho, hrhoId, fun s ↦ hbuffer ?_⟩
  by_cases hsa : rho s ≤ a
  · refine Metric.mem_cthickening_of_dist_le (rho s) a margin
      (Icc a b) ⟨le_rfl, hab.le⟩ ?_
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hsa)]
    have hlo := (hrange s).1
    dsimp only [lo, eps] at hlo
    linarith
  · by_cases hsb : rho s ≤ b
    · exact Metric.mem_cthickening_of_dist_le (rho s) (rho s) margin
        (Icc a b) ⟨(not_le.mp hsa).le, hsb⟩ (by simpa using hmargin.le)
    · refine Metric.mem_cthickening_of_dist_le (rho s) b margin
        (Icc a b) ⟨hab.le, le_rfl⟩ ?_
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (not_le.mp hsb).le)]
      have hhi := (hrange s).2
      dsimp only [hi, eps] at hhi
      linarith

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [NeZero (Module.finrank Real E)] [SigmaCompactSpace M] in
private theorem lTail_mfd_at
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T a b : Real) (hab : a < b)
    {alpha : E × Real → M} {V : Set E} {K : Set Real} {A0 : E}
    (hVopen : IsOpen V) (hA0V : A0 ∈ V)
    (hKopen : IsOpen K) (hKconn : IsPreconnected K)
    (haK : a ∈ K) (hbK : b ∈ K)
    (hstart : ∀ A ∈ V, alpha (A, a) = alpha (A0, a))
    (halpha : ContMDiffOn
      (𝓘(Real, E).prod 𝓘(Real, Real)) I ∞ alpha (V ×ˢ K))
    (hreg : ∀ q ∈ V ×ˢ K, T - q.2 ^ 2 ∈ D.regular)
    (hEuler : ∀ A ∈ V, ∀ s ∈ Icc a b,
      covDerivAlong (I := I) (S.base.metric (T - s ^ 2))
          (fun r : Real ↦ alpha (A, r))
          (fun r : Real ↦
            lVelocity (I := I) (fun z : Real ↦ alpha (A, z)) r) s =
        lRegAccel S T s (alpha (A, s))
          (lVelocity (I := I) (fun r : Real ↦ alpha (A, r)) s))
    (hinj : Function.Injective fun B : E ↦
      mfderiv 𝓘(Real, E) I (fun A : E ↦ alpha (A, b)) A0 B)
    (y : M)
    (hySrc : y ∈
      (lTail_localDiffeo hVopen hA0V hbK halpha hinj).localInverse.source)
    (hyV : (lTail_localDiffeo hVopen hA0V hbK halpha hinj).localInverse y ∈ V) :
    HasMFDerivAt I 𝓘(Real, Real)
      (fun q : M ↦ lRegAction S T
        (fun s ↦ alpha
          ((lTail_localDiffeo hVopen hA0V hbK halpha hinj).localInverse q, s))
        a b) y
      ((S.base.metric (T - b ^ 2)).inner y
        (lVelocity (I := I)
          (fun s : Real ↦ alpha
            ((lTail_localDiffeo hVopen hA0V hbK halpha hinj).localInverse y, s))
          b)) := by
  let hloc := lTail_localDiffeo hVopen hA0V hbK halpha hinj
  let A : E := hloc.localInverse y
  let endMap : E → M := fun B ↦ alpha (B, b)
  let act : E → Real := fun B ↦
    lRegAction S T (fun s ↦ alpha (B, s)) a b
  let flat : TangentSpace I (alpha (A, b)) →L[Real] Real :=
    (S.base.metric (T - b ^ 2)).inner (alpha (A, b))
      (lVelocity (I := I) (fun s : Real ↦ alpha (A, s)) b)
  have hright : endMap A = y := hloc.localInverse_right_inv hySrc
  have hstartA : ∀ B ∈ V, alpha (B, a) = alpha (A, a) := by
    intro B hBV
    exact (hstart B hBV).trans (hstart A hyV).symm
  have hjoint := lTailAct_joint S hS T a b hab hVopen hyV hKopen
    hKconn haK hbK hstartA halpha hreg (hEuler A hyV)
  have hins : HasFDerivAt (fun B : E ↦ (B, b))
      ((1 : E →L[Real] E).prod (0 : E →L[Real] Real)) A :=
    hasFDerivAt_prodMk_left A b
  have hact : HasFDerivAt act
      (flat.comp (mfderiv 𝓘(Real, E) I endMap A)) A := by
    have h := hjoint.comp A hins
    change HasFDerivAt act _ A at h
    refine h.congr_fderiv ?_
    apply ContinuousLinearMap.ext
    intro B
    change flat (mfderiv 𝓘(Real, E) I endMap A B) +
        lRegLag S T (fun s : Real ↦ alpha (A, s)) b * 0 =
      flat (mfderiv 𝓘(Real, E) I endMap A B)
    ring
  have hInv : MDifferentiableAt I 𝓘(Real, E) hloc.localInverse y :=
    (hloc.localInverse_contMDiffOn y hySrc).contMDiffAt
      (hloc.localInverse_open_source.mem_nhds hySrc) |>.mdifferentiableAt (by simp)
  have hEnd : MDifferentiableAt 𝓘(Real, E) I endMap A := by
    have hpair : ContMDiffAt 𝓘(Real, E)
        (𝓘(Real, E).prod 𝓘(Real, Real)) ∞
        (fun B : E ↦ (B, b)) A :=
      contMDiffAt_id.prodMk contMDiffAt_const
    exact ((halpha (A, b) ⟨hyV, hbK⟩).contMDiffAt
      ((hVopen.prod hKopen).mem_nhds ⟨hyV, hbK⟩)).comp A hpair
        |>.mdifferentiableAt (by simp)
  have hcomp := hact.hasMFDerivAt.comp y hInv.hasMFDerivAt
  have hEq : (endMap ∘ hloc.localInverse) =ᶠ[nhds y] id := by
    exact Filter.eventuallyEq_of_mem
      (hloc.localInverse_open_source.mem_nhds hySrc)
      (fun q hq ↦ hloc.localInverse_right_inv hq)
  have hchain := mfderiv_comp y hEnd hInv
  have hcancel :
      (mfderiv 𝓘(Real, E) I endMap A).comp
          (mfderiv I 𝓘(Real, E) hloc.localInverse y) =
        (1 : TangentSpace I y →L[Real] TangentSpace I y) := by
    have hd := hEq.mfderiv_eq (I := I) (I' := I)
    have hc := hchain.symm.trans hd
    change (mfderiv 𝓘(Real, E) I endMap A).comp
        (mfderiv I 𝓘(Real, E) hloc.localInverse y) =
      mfderiv I I id y at hc
    rw [mfderiv_id] at hc
    exact hc
  have hderiv :
      (flat.comp (mfderiv 𝓘(Real, E) I endMap A)).comp
          (mfderiv I 𝓘(Real, E) hloc.localInverse y) =
        (S.base.metric (T - b ^ 2)).inner y
          (lVelocity (I := I) (fun s : Real ↦ alpha (A, s)) b) := by
    apply ContinuousLinearMap.ext
    intro Y
    have hc := congrArg
      (fun L : TangentSpace I y →L[Real] TangentSpace I y ↦ L Y) hcancel
    change flat
        (mfderiv 𝓘(Real, E) I endMap A
          (mfderiv I 𝓘(Real, E) hloc.localInverse y Y)) =
      (S.base.metric (T - b ^ 2)).inner y
        (lVelocity (I := I) (fun s : Real ↦ alpha (A, s)) b) Y
    change (S.base.metric (T - b ^ 2)).inner (alpha (A, b))
        (lVelocity (I := I) (fun s : Real ↦ alpha (A, s)) b)
        (mfderiv 𝓘(Real, E) I endMap A
          (mfderiv I 𝓘(Real, E) hloc.localInverse y Y)) = _
    change mfderiv 𝓘(Real, E) I endMap A
        (mfderiv I 𝓘(Real, E) hloc.localInverse y Y) = Y at hc
    change alpha (A, b) = y at hright
    rw [hright]
    exact congrArg
      ((S.base.metric (T - b ^ 2)).inner y
        (lVelocity (I := I) (fun s : Real ↦ alpha (A, s)) b)) hc
  have hout := hcomp.congr_mfderiv hderiv
  change HasMFDerivAt I 𝓘(Real, Real)
    (act ∘ hloc.localInverse) y
    ((S.base.metric (T - b ^ 2)).inner y
      (lVelocity (I := I) (fun s : Real ↦ alpha (A, s)) b)) at hout
  change HasMFDerivAt I 𝓘(Real, Real)
    (act ∘ hloc.localInverse) y
    ((S.base.metric (T - b ^ 2)).inner y
      (lVelocity (I := I) (fun s : Real ↦ alpha (A, s)) b))
  exact hout

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [NeZero (Module.finrank Real E)] [SigmaCompactSpace M] in
private theorem lTail_grad_on
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T a b : Real) (hab : a < b)
    {alpha : E × Real → M} {V : Set E} {K : Set Real} {A0 : E}
    (hVopen : IsOpen V) (hA0V : A0 ∈ V)
    (hKopen : IsOpen K) (hKconn : IsPreconnected K)
    (haK : a ∈ K) (hbK : b ∈ K)
    (hstart : ∀ A ∈ V, alpha (A, a) = alpha (A0, a))
    (halpha : ContMDiffOn
      (𝓘(Real, E).prod 𝓘(Real, Real)) I ∞ alpha (V ×ˢ K))
    (hreg : ∀ q ∈ V ×ˢ K, T - q.2 ^ 2 ∈ D.regular)
    (hEuler : ∀ A ∈ V, ∀ s ∈ Icc a b,
      covDerivAlong (I := I) (S.base.metric (T - s ^ 2))
          (fun r : Real ↦ alpha (A, r))
          (fun r : Real ↦
            lVelocity (I := I) (fun z : Real ↦ alpha (A, z)) r) s =
        lRegAccel S T s (alpha (A, s))
          (lVelocity (I := I) (fun r : Real ↦ alpha (A, r)) s))
    (hinj : Function.Injective fun B : E ↦
      mfderiv 𝓘(Real, E) I (fun A : E ↦ alpha (A, b)) A0 B) :
    let hloc := lTail_localDiffeo hVopen hA0V hbK halpha hinj
    let branch : M → Real := fun y ↦
      lRegAction S T (fun s ↦ alpha (hloc.localInverse y, s)) a b
    ∃ U : Set M, IsOpen U ∧ alpha (A0, b) ∈ U ∧
      ContMDiffOn I 𝓘(Real, Real) ∞ branch U ∧
      (∀ y ∈ U, y ∈ hloc.localInverse.source) ∧
      (∀ y ∈ U, hloc.localInverse y ∈ V) ∧
      ∀ y ∈ U, gradientFun (I := I) (S.base.metric (T - b ^ 2))
        branch y = lVelocity (I := I)
          (fun s : Real ↦ alpha (hloc.localInverse y, s)) b := by
  dsimp only
  obtain ⟨W, hWopen, hA0W, hWV, hact⟩ :=
    lTailAct_smooth S hS T a b hab hVopen hA0V hKopen hKconn
      haK hbK halpha hreg
  let hloc := lTail_localDiffeo hVopen hA0V hbK halpha hinj
  let branch : M → Real := fun y ↦
    lRegAction S T (fun s ↦ alpha (hloc.localInverse y, s)) a b
  let U : Set M := hloc.localInverse.source ∩ hloc.localInverse ⁻¹' W
  have hUopen : IsOpen U :=
    hloc.localInverse_contMDiffOn.continuousOn.isOpen_inter_preimage
      hloc.localInverse_open_source hWopen
  have hinv : hloc.localInverse (alpha (A0, b)) = A0 :=
    hloc.localInverse_left_inv hloc.localInverse_mem_target
  have hyU : alpha (A0, b) ∈ U := by
    refine ⟨hloc.localInverse_mem_source, ?_⟩
    change hloc.localInverse (alpha (A0, b)) ∈ W
    rw [hinv]
    exact hA0W
  have hactM : ContMDiffOn 𝓘(Real, E) 𝓘(Real, Real) ∞
      (fun A : E ↦ lRegAction S T (fun s ↦ alpha (A, s)) a b) W :=
    contMDiffOn_iff_contDiffOn.mpr hact
  have hbranch : ContMDiffOn I 𝓘(Real, Real) ∞ branch U := by
    have hcomp := hactM.comp
      (hloc.localInverse_contMDiffOn.mono inter_subset_left)
      (fun _ hy ↦ hy.2)
    change ContMDiffOn I 𝓘(Real, Real) ∞
      ((fun A : E ↦ lRegAction S T (fun s ↦ alpha (A, s)) a b) ∘
        hloc.localInverse) U
    exact hcomp
  refine ⟨U, hUopen, hyU, hbranch, (fun _ hy ↦ hy.1),
    (fun _ hy ↦ hWV hy.2), ?_⟩
  intro y hy
  apply gradientFun_eq_of_flat
  have hmfd := lTail_mfd_at S hS T a b hab hVopen hA0V hKopen
    hKconn haK hbK hstart halpha hreg hEuler hinj y hy.1 (hWV hy.2)
  ext Y
  have hd := congrArg (fun L : TangentSpace I y →L[Real]
    TangentSpace 𝓘(Real, Real) (branch y) ↦ L Y) hmfd.mfderiv
  change mvfderiv (I := I) branch y Y = _
  rw [DifferentialGeometry.mvfderiv_real_eq_mfderiv]
  have hd' := congrArg
    (NormedSpace.fromTangentSpace (𝕜 := Real) (branch y)) hd
  let vel : TangentSpace I y :=
    lVelocity (I := I) (fun s : Real ↦ alpha (hloc.localInverse y, s)) b
  have hcast :
      ((S.base.metric (T - b ^ 2)).inner y vel) Y =
        (NormedSpace.fromTangentSpace (𝕜 := Real) (branch y)).symm
          (metricFlatEquiv (I := I) (S.base.metric (T - b ^ 2)) y vel Y) := by
    rfl
  calc
    _ = (NormedSpace.fromTangentSpace (𝕜 := Real) (branch y))
        (((S.base.metric (T - b ^ 2)).inner y vel) Y) := hd'
    _ = (NormedSpace.fromTangentSpace (𝕜 := Real) (branch y))
        ((NormedSpace.fromTangentSpace (𝕜 := Real) (branch y)).symm
          (metricFlatEquiv (I := I) (S.base.metric (T - b ^ 2)) y vel Y)) :=
      congrArg (NormedSpace.fromTangentSpace (𝕜 := Real) (branch y)) hcast
    _ = _ := ContinuousLinearEquiv.apply_symm_apply _ _

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [NeZero (Module.finrank Real E)] in
omit [SigmaCompactSpace M] in
private theorem lTailEnd_cov
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T a b : Real) (hab : a < b)
    {alpha : E × Real → M} {V : Set E} {K : Set Real} {A0 : E}
    (hVopen : IsOpen V) (hA0V : A0 ∈ V)
    (hKopen : IsOpen K) (hKconn : IsPreconnected K)
    (haK : a ∈ K) (hbK : b ∈ K)
    (hstart : ∀ A ∈ V, alpha (A, a) = alpha (A0, a))
    (halpha : ContMDiffOn
      (𝓘(Real, E).prod 𝓘(Real, Real)) I ∞ alpha (V ×ˢ K))
    (hreg : ∀ q ∈ V ×ˢ K, T - q.2 ^ 2 ∈ D.regular)
    (hEuler : ∀ A ∈ V, ∀ s ∈ Icc a b,
      covDerivAlong (I := I) (S.base.metric (T - s ^ 2))
          (fun r : Real ↦ alpha (A, r))
          (fun r : Real ↦
            lVelocity (I := I) (fun z : Real ↦ alpha (A, z)) r) s =
        lRegAccel S T s (alpha (A, s))
          (lVelocity (I := I) (fun r : Real ↦ alpha (A, r)) s))
    (hinj : Function.Injective fun B : E ↦
      mfderiv 𝓘(Real, E) I (fun A : E ↦ alpha (A, b)) A0 B)
    (Y : TangentSpace I (alpha (A0, b))) :
    let hloc := lTail_localDiffeo hVopen hA0V hbK halpha hinj
    let W := mfderiv I 𝓘(Real, E) hloc.localInverse (alpha (A0, b)) Y
    let J : ∀ s, TangentSpace I (alpha (A0, s)) := fun s ↦
      mfderiv 𝓘(Real, E) I (fun A : E ↦ alpha (A, s)) A0 W
    (LeviCivita (I := I) (S.base.metric (T - b ^ 2))).toFun
        (fun y ↦ gradientFun (I := I) (S.base.metric (T - b ^ 2))
          (fun q : M ↦ lRegAction S T
            (fun s ↦ alpha (hloc.localInverse q, s)) a b) y)
        (alpha (A0, b)) Y =
      covDerivAlong (I := I) (S.base.metric (T - b ^ 2))
        (fun s ↦ alpha (A0, s)) J b := by
  dsimp only
  let g := S.base.metric (T - b ^ 2)
  let y : M := alpha (A0, b)
  let hloc := lTail_localDiffeo hVopen hA0V hbK halpha hinj
  let branch : M → Real := fun q ↦
    lRegAction S T (fun s ↦ alpha (hloc.localInverse q, s)) a b
  let W : E := mfderiv I 𝓘(Real, E) hloc.localInverse y Y
  let J : (s : Real) → TangentSpace I (alpha (A0, s)) := fun s ↦
    mfderiv 𝓘(Real, E) I (fun A : E ↦ alpha (A, s)) A0 W
  obtain ⟨U, hUopen, hyU, hsmooth, hsource, hparam, hgrad⟩ :=
    lTail_grad_on S hS T a b hab hVopen hA0V hKopen hKconn
      haK hbK hstart halpha hreg hEuler hinj
  obtain ⟨eta, heta, hetaU, heta0, hetaVel⟩ :=
    exists_smooth_curve y Y U hUopen (by simpa only [y] using hyU)
  let zeta : Real → E := fun u ↦ hloc.localInverse (eta u)
  have hzeta : ContMDiff 𝓘(Real, Real) 𝓘(Real, E) ∞ zeta := by
    rw [← contMDiffOn_univ]
    exact hloc.localInverse_contMDiffOn.comp heta.contMDiffOn
      (fun u _hu ↦ hsource (eta u) (hetaU u))
  have hzetaV : ∀ u : Real, zeta u ∈ V := by
    exact fun u ↦ by
      simpa only [zeta, hloc] using hparam (eta u) (hetaU u)
  have hinv0 : hloc.localInverse y = A0 :=
    hloc.localInverse_left_inv hloc.localInverse_mem_target
  have hzeta0 : zeta 0 = A0 := by
    dsimp only [zeta]
    rw [heta0]
    exact hinv0
  have hzetaVel : mfderiv 𝓘(Real, Real) 𝓘(Real, E) zeta 0
      (1 : Real) = W := by
    have hInv0 : MDifferentiableAt I 𝓘(Real, E)
        hloc.localInverse (eta 0) := by
      simpa only [heta0, y] using
        hloc.localInverse_contMDiffAt.mdifferentiableAt (by simp)
    have hc := mfderiv_comp 0 hInv0
      (heta.contMDiffAt.mdifferentiableAt (by simp))
    change mfderiv 𝓘(Real, Real) 𝓘(Real, E)
      (hloc.localInverse ∘ eta) 0 1 = W
    rw [hc]
    change mfderiv I 𝓘(Real, E) hloc.localInverse (eta 0)
      (mfderiv 𝓘(Real, Real) I eta 0 1) = W
    rw [heta0]
    exact congrArg (mfderiv I 𝓘(Real, E) hloc.localInverse y) hetaVel
  obtain ⟨rho, lo, hi, hloa, hbhi, hrho, hrhoId, hrhoK⟩ :=
    tailHess_clamp hKopen hKconn haK hbK hab
  have hrhoM : ContMDiff 𝓘(Real, Real) 𝓘(Real, Real) ∞ rho :=
    contMDiff_iff_contDiff.mpr hrho
  let F : Real → Real → M := fun u s ↦ alpha (zeta u, rho s)
  have hpair : ContMDiff
      (𝓘(Real, Real).prod 𝓘(Real, Real))
      (𝓘(Real, E).prod 𝓘(Real, Real)) ∞
      (fun p : Real × Real ↦ (zeta p.1, rho p.2)) :=
    (hzeta.comp contMDiff_fst).prodMk (hrhoM.comp contMDiff_snd)
  have hF : IsSmoothVariation (I := I) F := by
    have h8inf : (↑(8 : ENat) : WithTop ENat) ≤ ↑(⊤ : ENat) :=
      WithTop.coe_le_coe.mpr le_top
    unfold IsSmoothVariation
    rw [← contMDiffOn_univ]
    change ContMDiffOn
      (𝓘(Real, Real).prod 𝓘(Real, Real)) I 8
      (alpha ∘ fun p : Real × Real ↦ (zeta p.1, rho p.2)) univ
    exact (halpha.of_le h8inf).comp
      (hpair.of_le h8inf).contMDiffOn
      (fun p _hp ↦ ⟨hzetaV p.1, hrhoK p.2⟩)
  have hbad : b ∈ Icc lo hi :=
    ⟨(hloa.trans hab).le, hbhi.le⟩
  have hrhob : rho b = b := by
    simpa only [id_eq] using hrhoId hbad
  have hend : (fun u : Real ↦ F u b) = eta := by
    funext u
    change alpha (zeta u, rho b) = eta u
    rw [hrhob]
    exact hloc.localInverse_right_inv (hsource (eta u) (hetaU u))
  let Vterm : ∀ u, TangentSpace I (eta u) := fun u ↦
    lVelocity (I := I) (fun s : Real ↦ alpha (zeta u, s)) b
  have hgradEv :
      (fun u ↦ gradientFun (I := I) g branch (eta u)) =ᶠ[nhds 0]
        Vterm := by
    exact Filter.Eventually.of_forall fun u ↦ by
      change gradientFun (I := I) g branch (eta u) =
        lVelocity (I := I) (fun s : Real ↦ alpha (zeta u, s)) b
      have hu := hgrad (eta u) (hetaU u)
      change gradientFun (I := I) g branch (eta u) =
        lVelocity (I := I) (fun s : Real ↦ alpha (zeta u, s)) b at hu
      exact hu
  have hcovGrad := covDerivAlong_congr_of_eventuallyEq
    (I := I) g eta hgradEv
  obtain ⟨f₀, hf₀, hf₀eq⟩ :=
    DifferentialGeometry.exists_smooth_germ (I := I) hUopen hyU hsmooth
  have hgradEq :
      (T% fun q ↦ gradientFun (I := I) g f₀ q) =ᶠ[nhds y]
        (T% fun q ↦ gradientFun (I := I) g branch q) := by
    filter_upwards [hf₀eq.eventuallyEq_nhds] with q hq
    have hq' : f₀ =ᶠ[nhds q] branch := by
      change f₀ =ᶠ[nhds q] branch at hq
      exact hq
    change TotalSpace.mk' E q (gradientFun (I := I) g f₀ q) =
      TotalSpace.mk' E q (gradientFun (I := I) g branch q)
    unfold gradientFun
    have hmv : (mvfderiv (I := I) f₀ q).toLinearMap =
        (mvfderiv (I := I) branch q).toLinearMap := by
      apply LinearMap.ext
      intro V
      change mvfderiv (I := I) f₀ q V =
        mvfderiv (I := I) branch q V
      rw [DifferentialGeometry.mvfderiv_real_eq_mfderiv,
        DifferentialGeometry.mvfderiv_real_eq_mfderiv,
        hq'.mfderiv_eq (I := I) (I' := 𝓘(Real, Real))]
      rw [hq'.self_of_nhds]
    exact congrArg
      (fun L : TangentSpace I q →ₗ[Real] Real ↦
        TotalSpace.mk' E q (metricSharp (I := I) g q L)) hmv
  have hgradAt : MDifferentiableAt I
      (I.prod 𝓘(Real, E))
      (fun q ↦ TotalSpace.mk' E q
        (gradientFun (I := I) g branch q)) y := by
    have hs := gradientFun_smooth (I := I) g hf₀
    exact (hs.contMDiffAt.congr_of_eventuallyEq hgradEq.symm).mdifferentiableAt
      (by simp)
  have hchain := covDerivAlong_restrict_eq_leviCivita
    (I := I) g eta (fun q ↦ gradientFun (I := I) g branch q) 0 heta
      (by simpa only [heta0] using hgradAt)
  have hchain' :
      covDerivAlong (I := I) g eta
          (fun u ↦ gradientFun (I := I) g branch (eta u)) 0 =
        (LeviCivita (I := I) g).toFun
          (fun q ↦ gradientFun (I := I) g branch q) y Y := by
    rw [heta0] at hchain
    exact hchain.trans (congrArg
      (fun Q : TangentSpace I y ↦
        (LeviCivita (I := I) g).toFun
          (fun q ↦ gradientFun (I := I) g branch q) y Q) hetaVel)
  have hcomm := commute_ds_dt_intrinsic (I := I) g F hF b
  have hbase : (fun s : Real ↦ F 0 s) =ᶠ[nhds b]
      (fun s : Real ↦ alpha (A0, s)) := by
    filter_upwards [isOpen_Ioo.mem_nhds ⟨hloa.trans hab, hbhi⟩] with s hs
    change alpha (zeta 0, rho s) = alpha (A0, s)
    rw [hzeta0]
    exact congrArg (fun r ↦ alpha (A0, r))
      (by simpa only [id_eq] using hrhoId ⟨hs.1.le, hs.2.le⟩)
  have hfield : (fun s : Real ↦
      mfderiv 𝓘(Real, Real) I (fun u ↦ F u s) 0 (1 : Real))
      =ᶠ[nhds b] J := by
    filter_upwards [isOpen_Ioo.mem_nhds ⟨hloa.trans hab, hbhi⟩] with s hs
    have hrs : rho s = s := by
      simpa only [id_eq] using hrhoId ⟨hs.1.le, hs.2.le⟩
    change mfderiv 𝓘(Real, Real) I
      (fun u ↦ alpha (zeta u, rho s)) 0 1 = _
    rw [hrs]
    change mfderiv 𝓘(Real, Real) I
      ((fun A : E ↦ alpha (A, s)) ∘ zeta) 0 1 = _
    have hAlpha : MDifferentiableAt 𝓘(Real, E) I
        (fun A : E ↦ alpha (A, s)) A0 := by
      have hsK : s ∈ K := by
        rw [← hrs]
        exact hrhoK s
      have hp : (A0, s) ∈ V ×ˢ K := ⟨hA0V, hsK⟩
      have hAt := (halpha (A0, s) hp).contMDiffAt
        ((hVopen.prod hKopen).mem_nhds hp)
      exact (hAt.comp A0 (contMDiffAt_id.prodMk contMDiffAt_const))
        |>.mdifferentiableAt (by simp)
    have hAlpha0 : MDifferentiableAt 𝓘(Real, E) I
        (fun A : E ↦ alpha (A, s)) (zeta 0) := by
      simpa only [hzeta0] using hAlpha
    have hzcomp := mfderiv_comp 0 hAlpha0
      (hzeta.contMDiffAt.mdifferentiableAt (by simp))
    rw [hzcomp, hzeta0]
    exact congrArg
      (mfderiv 𝓘(Real, E) I (fun A : E ↦ alpha (A, s)) A0)
      hzetaVel
  have hcomm' : covDerivAlong (I := I) g eta Vterm 0 =
      covDerivAlong (I := I) g (fun s ↦ alpha (A0, s)) J b := by
    have hendVel : (fun u : Real ↦
        lVelocity (I := I) (fun s ↦ F u s) b) = Vterm := by
      funext u
      have heq : (fun s ↦ F u s) =ᶠ[nhds b]
          (fun s ↦ alpha (zeta u, s)) := by
        filter_upwards [isOpen_Ioo.mem_nhds
          ⟨hloa.trans hab, hbhi⟩] with s hs
        change alpha (zeta u, rho s) = alpha (zeta u, s)
        exact congrArg (fun r ↦ alpha (zeta u, r))
          (by simpa only [id_eq] using hrhoId ⟨hs.1.le, hs.2.le⟩)
      unfold lVelocity
      exact congrArg (fun L ↦ L (1 : Real))
        (heq.mfderiv_eq (I := 𝓘(Real, Real)) (I' := I))
    change covDerivAlong (I := I) g (fun u ↦ F u b)
        (fun u ↦ lVelocity (I := I) (fun s ↦ F u s) b) 0 = _ at hcomm
    rw [hend, hendVel] at hcomm
    have hc := DifferentialGeometry.Geometry.Riemannian.covDerivAlong_congr_curve
      (I := I) g _ _ hbase hfield
    exact hcomm.trans (by simpa using hc)
  exact hchain'.symm.trans (hcovGrad.trans hcomm')

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [NeZero (Module.finrank Real E)] in
omit [SigmaCompactSpace M] in
theorem lTailBranch_hess
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T a b : Real) (hab : a < b)
    {alpha : E × Real → M} {V : Set E} {K : Set Real} {A0 : E}
    (hVopen : IsOpen V) (hA0V : A0 ∈ V)
    (hKopen : IsOpen K) (hKconn : IsPreconnected K)
    (haK : a ∈ K) (hbK : b ∈ K)
    (hstart : ∀ A ∈ V, alpha (A, a) = alpha (A0, a))
    (halpha : ContMDiffOn
      (𝓘(Real, E).prod 𝓘(Real, Real)) I ∞ alpha (V ×ˢ K))
    (hreg : ∀ q ∈ V ×ˢ K, T - q.2 ^ 2 ∈ D.regular)
    (hEuler : ∀ A ∈ V, ∀ s ∈ Icc a b,
      covDerivAlong (I := I) (S.base.metric (T - s ^ 2))
          (fun r : Real ↦ alpha (A, r))
          (fun r : Real ↦
            lVelocity (I := I) (fun z : Real ↦ alpha (A, z)) r) s =
        lRegAccel S T s (alpha (A, s))
          (lVelocity (I := I) (fun r : Real ↦ alpha (A, r)) s))
    (hinj : Function.Injective fun B : E ↦
      mfderiv 𝓘(Real, E) I (fun A : E ↦ alpha (A, b)) A0 B)
    (Y Z : TangentSpace I (alpha (A0, b))) :
    let hloc := lTail_localDiffeo hVopen hA0V hbK halpha hinj
    let branch : M → Real := fun y ↦
      lRegAction S T (fun s ↦ alpha (hloc.localInverse y, s)) a b
    let W := mfderiv I 𝓘(Real, E) hloc.localInverse (alpha (A0, b)) Y
    let J : ∀ s, TangentSpace I (alpha (A0, s)) := fun s ↦
      mfderiv 𝓘(Real, E) I (fun A : E ↦ alpha (A, s)) A0 W
    hessFun (I := I) (S.base.metric (T - b ^ 2)) branch
        (alpha (A0, b)) Y Z =
      (S.base.metric (T - b ^ 2)).inner (alpha (A0, b))
        (covDerivAlong (I := I) (S.base.metric (T - b ^ 2))
          (fun s ↦ alpha (A0, s)) J b) Z := by
  dsimp only
  obtain ⟨U, hUopen, hyU, hsmooth, _hsource, _hparam, _hgrad⟩ :=
    lTail_grad_on S hS T a b hab hVopen hA0V hKopen hKconn
      haK hbK hstart halpha hreg hEuler hinj
  have hhess := hessFun_eq_cov_local (I := I)
    (S.base.metric (T - b ^ 2)) hUopen hsmooth hyU Y Z
  have hcov := lTailEnd_cov S hS T a b hab hVopen hA0V hKopen
    hKconn haK hbK hstart halpha hreg hEuler hinj Y
  simp only [gradient_eq_gradFun] at hcov
  exact hhess.trans (congrArg
    (fun Q : TangentSpace I (alpha (A0, b)) ↦
      (S.base.metric (T - b ^ 2)).inner (alpha (A0, b)) Q Z) hcov)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem lTail_hess_le
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T a b : Real) (ha0 : 0 < a) (hab : a < b)
    {gamma : Real → M} {x : M} {Z : TangentSpace I x}
    (hgeo : IsLRegCurveOn S T gamma (uIcc (0 : Real) b) x Z)
    (hmin : ∀ delta : Real → M,
      ContMDiff 𝓘(Real, Real) I 1 delta →
      delta 0 = gamma 0 → delta b = gamma b →
      lRegAction S T gamma 0 b ≤ lRegAction S T delta 0 b)
    {alpha : E × Real → M} {V : Set E} {K : Set Real} {A0 : E}
    (hVopen : IsOpen V) (hA0V : A0 ∈ V)
    (hKopen : IsOpen K) (hKconn : IsPreconnected K)
    (h0K : 0 ∈ K) (hbK : b ∈ K)
    (hstart : ∀ A ∈ V, alpha (A, a) = alpha (A0, a))
    (halpha : ContMDiffOn
      (𝓘(Real, E).prod 𝓘(Real, Real)) I ∞ alpha (V ×ˢ K))
    (hreg : ∀ q ∈ V ×ˢ K, T - q.2 ^ 2 ∈ D.regular)
    (hEuler : ∀ A ∈ V, ∀ s ∈ K,
      covDerivAlong (I := I) (S.base.metric (T - s ^ 2))
          (fun r : Real ↦ alpha (A, r))
          (fun r : Real ↦
            lVelocity (I := I) (fun z : Real ↦ alpha (A, z)) r) s =
        lRegAccel S T s (alpha (A, s))
          (lVelocity (I := I) (fun r : Real ↦ alpha (A, r)) s))
    (hcenter : ∀ s ∈ Icc (0 : Real) b,
      (fun r ↦ alpha (A0, r)) =ᶠ[nhds s] gamma)
    (hinj : Function.Injective fun B : E ↦
      mfderiv 𝓘(Real, E) I (fun A : E ↦ alpha (A, b)) A0 B)
    (Y : TangentSpace I (alpha (A0, b)))
    (W : ∀ s, TangentSpace I (alpha (A0, s)))
    {Omega : Set Real} (hOmega : IsOpen Omega)
    (hOmegaSeg : Icc (0 : Real) b ⊆ Omega)
    (hW : ContMDiffOn 𝓘(Real, Real) I.tangent (8 : Nat)
      (fun s : Real ↦
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (alpha (A0, s)) (W s) : TangentBundle I M)) Omega)
    (hWa : W a = 0) (hWb : W b = Y) :
    let hloc := lTail_localDiffeo hVopen hA0V hbK halpha hinj
    let branch : M → Real := fun y ↦
      lRegAction S T (fun s ↦ alpha (hloc.localInverse y, s)) a b
    hessFun (I := I) (S.base.metric (T - b ^ 2)) branch
        (alpha (A0, b)) Y Y ≤
      2 * lRegIndex S T (fun s ↦ alpha (A0, s)) W W a b := by
  dsimp only
  let beta : Real → M := fun s ↦ alpha (A0, s)
  let y : M := beta b
  let g := S.base.metric (T - b ^ 2)
  let hloc := lTail_localDiffeo hVopen hA0V hbK halpha hinj
  let branch : M → Real := fun q ↦
    lRegAction S T (fun s ↦ alpha (hloc.localInverse q, s)) a b
  let B : E := mfderiv I 𝓘(Real, E) hloc.localInverse y Y
  let J : (s : Real) → TangentSpace I (beta s) := fun s ↦
    lVelocity (I := I) (fun u : Real ↦ alpha (A0 + u • B, s)) 0
  let Q : (s : Real) → TangentSpace I (beta s) := fun s ↦ W s - J s
  have hb0 : 0 < b := ha0.trans hab
  have hsegK : Icc (0 : Real) b ⊆ K :=
    hKconn.ordConnected.out h0K hbK
  have haK : a ∈ K := hsegK ⟨ha0.le, hab.le⟩
  have hlineSmooth : ContMDiffOn 𝓘(Real, Real) I.tangent ∞
      (fun s : Real ↦
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (beta s) (J s) : TangentBundle I M)) K := by
    simpa only [beta, J] using
      lTailLine_smooth (I := I) (B := B)
        hVopen hA0V hKopen halpha
  have hlineJac := lTailLine_jacobi (I := I) (B := B) S T (beta a)
    hVopen hA0V hKopen halpha
    (by simpa only [beta] using hstart) hEuler
  have hJacK : IsLRegJacobi S T beta J K := by
    simpa only [beta, J] using hlineJac.1
  have hJa : J a = 0 := by
    change lVelocity (I := I)
      (fun u : Real ↦ alpha (A0 + u • B, a)) 0 =
        (0 : TangentSpace I (beta a))
    rw [show beta a = alpha (A0 + 0 • B, a) by
      simp only [beta, zero_smul, add_zero]]
    exact hlineJac.2
  have halphaB : ContMDiffAt
      (𝓘(Real, E).prod 𝓘(Real, Real)) I ∞ alpha (A0, b) :=
    (halpha (A0, b) ⟨hA0V, hbK⟩).contMDiffAt
      ((hVopen.prod hKopen).mem_nhds ⟨hA0V, hbK⟩)
  have hJb : J b = Y := by
    have hline := lTailLine_deriv (I := I) A0 B b halphaB
    have hright :=
      (hloc.mfderivToContinuousLinearEquiv (by simp)).right_inv Y
    change lVelocity (I := I)
        (fun u : Real ↦ alpha (A0 + u • B, b)) 0 = Y
    have hline' : lVelocity (I := I)
        (fun u : Real ↦ alpha (A0 + u • B, b)) 0 =
      mfderiv 𝓘(Real, E) I (fun W : E ↦ alpha (W, b)) A0 B := by
      simpa only [zero_smul, add_zero] using hline
    rw [hline']
    change mfderiv 𝓘(Real, E) I (fun W : E ↦ alpha (W, b)) A0
      (mfderiv I 𝓘(Real, E) hloc.localInverse (alpha (A0, b)) Y) = Y at hright
    change mfderiv 𝓘(Real, E) I (fun W : E ↦ alpha (W, b)) A0 B = Y
    exact hright
  have hQa : Q a = 0 := by
    change W a - J a = 0
    rw [hWa, hJa, sub_self]
  have hQb : Q b = 0 := by
    change W b - J b = 0
    rw [hWb, hJb, sub_self]
  have hsegInter : Icc (0 : Real) b ⊆ K ∩ Omega := by
    intro s hs
    exact ⟨hsegK hs, hOmegaSeg hs⟩
  obtain ⟨rho, lo, hi, hlo0, hbhi, hrho, hrhoEq, _hrhoDeriv,
      hrhoRange, hJgSmooth, _hpairEq⟩ :=
    exists_lTail_germ (I := I) (hKopen.inter hOmega) hb0 hsegInter
      (hlineSmooth.mono inter_subset_left)
  let gammaG : Real → M := fun s ↦ beta (rho s)
  let Jg : (s : Real) → TangentSpace I (gammaG s) := fun s ↦ J (rho s)
  let Wg : (s : Real) → TangentSpace I (gammaG s) := fun s ↦ W (rho s)
  let Qg : (s : Real) → TangentSpace I (gammaG s) := fun s ↦ Wg s - Jg s
  have hsegLoHi : Icc (0 : Real) b ⊆ Ioo lo hi := by
    intro s hs
    exact ⟨hlo0.trans_le hs.1, hs.2.trans_lt hbhi⟩
  have hrhoGerm : ∀ s ∈ Icc (0 : Real) b, rho =ᶠ[nhds s] id := by
    intro s hs
    have hshi := hsegLoHi hs
    filter_upwards [Ioo_mem_nhds hshi.1 hshi.2] with r hr
    exact hrhoEq ⟨hr.1.le, hr.2.le⟩
  have hGBGerm : ∀ s ∈ Icc (0 : Real) b,
      gammaG =ᶠ[nhds s] beta := by
    intro s hs
    filter_upwards [hrhoGerm s hs] with r hr
    simp only [gammaG, id_eq, hr]
  have hJgGerm : ∀ s ∈ Icc (0 : Real) b,
      ∀ᶠ r in nhds s, (Jg r : E) = (J r : E) := by
    intro s hs
    filter_upwards [hrhoGerm s hs] with r hr
    change (J (rho r) : E) = (J r : E)
    exact congrArg (fun q : Real ↦ (J q : E)) (by
      simpa only [id_eq] using hr)
  have hWgGerm : ∀ s ∈ Icc (0 : Real) b,
      ∀ᶠ r in nhds s, (Wg r : E) = (W r : E) := by
    intro s hs
    filter_upwards [hrhoGerm s hs] with r hr
    change (W (rho r) : E) = (W r : E)
    exact congrArg (fun q : Real ↦ (W q : E)) (by
      simpa only [id_eq] using hr)
  have hQgGerm : ∀ s ∈ Icc (0 : Real) b,
      ∀ᶠ r in nhds s, (Qg r : E) = (Q r : E) := by
    intro s hs
    filter_upwards [hWgGerm s hs, hJgGerm s hs] with r hWr hJr
    change Wg r - Jg r = W r - J r
    rw [hWr, hJr]
    rfl
  have hGGerm : ∀ s ∈ Icc (0 : Real) b,
      gammaG =ᶠ[nhds s] gamma := by
    intro s hs
    exact (hGBGerm s hs).trans (hcenter s hs)
  have hJgSmooth' : ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun s : Real ↦
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (gammaG s) (Jg s) : TangentBundle I M)) := by
    simpa only [gammaG, Jg] using hJgSmooth
  have hrhoM : ContMDiff 𝓘(Real, Real) 𝓘(Real, Real) ∞ rho :=
    contMDiff_iff_contDiff.mpr hrho
  have hWg8 : ContMDiff 𝓘(Real, Real) I.tangent (8 : Nat)
      (fun s : Real ↦
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (gammaG s) (Wg s) : TangentBundle I M)) := by
    rw [← contMDiffOn_univ]
    change ContMDiffOn 𝓘(Real, Real) I.tangent 8
      ((fun s : Real ↦
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (alpha (A0, s)) (W s) : TangentBundle I M)) ∘ rho) univ
    exact hW.comp
      ((hrhoM.of_le (by decide :
        (8 : WithTop ENat) ≤ (↑(⊤ : ENat) : WithTop ENat))).contMDiffOn)
      (fun s _hs ↦ (hrhoRange s).2)
  have hJg8 := hJgSmooth'.of_le (by decide :
    (8 : WithTop ENat) ≤ (↑(⊤ : ENat) : WithTop ENat))
  have hQg8 : ContMDiff 𝓘(Real, Real) I.tangent (8 : Nat)
      (fun s : Real ↦
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (gammaG s) (Qg s) : TangentBundle I M)) := by
    have hneg := (contMDiff_const (c := (-1 : Real))).smul_bundle hJg8
    simpa only [Qg, Pi.sub_apply, neg_one_smul, sub_eq_add_neg] using
      hWg8.add_bundle hneg
  have hgeoG : IsLRegCurveOn S T gammaG (uIcc (0 : Real) b) x Z := by
    have h0Icc : (0 : Real) ∈ Icc (0 : Real) b := ⟨le_rfl, hb0.le⟩
    have h0germ := hGGerm 0 h0Icc
    refine ⟨(h0germ.self_of_nhds).trans hgeo.1, ?_, ?_⟩
    · have hvel : lVelocity (I := I) gammaG 0 =
          lVelocity (I := I) gamma 0 := by
        unfold lVelocity
        rw [h0germ.mfderiv_eq (I := 𝓘(Real, Real)) (I' := I)]
        rfl
      exact hvel.trans hgeo.2.1
    · intro s hs
      have hsIcc : s ∈ Icc (0 : Real) b := by
        simpa only [uIcc_of_le hb0.le] using hs
      exact lRegData_congr S T s (hGGerm s hsIcc) (hgeo.2.2 s hs)
  have hminG : ∀ delta : Real → M,
      ContMDiff 𝓘(Real, Real) I 1 delta →
      delta 0 = gammaG 0 → delta b = gammaG b →
      lRegAction S T gammaG 0 b ≤ lRegAction S T delta 0 b := by
    intro delta hdelta hd0 hdb
    have hG0 := (hGGerm 0 ⟨le_rfl, hb0.le⟩).self_of_nhds
    have hGb := (hGGerm b ⟨hb0.le, le_rfl⟩).self_of_nhds
    have hraw := hmin delta hdelta (hd0.trans hG0) (hdb.trans hGb)
    have haction : lRegAction S T gammaG 0 b =
        lRegAction S T gamma 0 b := by
      apply lRegAction_congr (I := I) S T
      intro s hs
      have hs' : s ∈ Ioo (0 : Real) b := by
        simpa only [uIoo_of_le hb0.le] using hs
      exact (hGGerm s ⟨hs'.1.le, hs'.2.le⟩).self_of_nhds
    rw [haction]
    exact hraw
  have h0Icc : (0 : Real) ∈ Icc (0 : Real) b := ⟨le_rfl, hb0.le⟩
  have haIcc : a ∈ Icc (0 : Real) b := ⟨ha0.le, hab.le⟩
  have hbIcc : b ∈ Icc (0 : Real) b := ⟨hb0.le, le_rfl⟩
  have hQga : Qg a = 0 := by
    rw [(hQgGerm a haIcc).self_of_nhds]
    exact hQa
  have hQgb : Qg b = 0 := by
    rw [(hQgGerm b hbIcc).self_of_nhds]
    exact hQb
  let Zg : Real → E := fun s ↦ (0 : Real) • Jg s
  have hZg8 : ContMDiff 𝓘(Real, Real) I.tangent (8 : Nat)
      (fun s : Real ↦
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (gammaG s) (Zg s) : TangentBundle I M)) := by
    have hz := (contMDiff_const (c := (0 : Real))).smul_bundle hJg8
    change ContMDiff 𝓘(Real, Real) (I.prod 𝓘(Real, E)) 8
      (fun s : Real ↦
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (gammaG s) ((0 : Real) • Jg s) : TangentBundle I M))
    exact hz
  have hnonneg := lIndex_sum_nonneg (E := E) (I := I) S hS T gammaG
    0 a b ha0 hab x Z hgeoG hminG Zg Qg hZg8 hQg8
    (by dsimp only [Zg]; change (0 : Real) • (Jg 0 : E) = 0; module)
    hQgb (by
      dsimp only [Zg]
      change (0 : Real) • (Jg a : E) = (Qg a : E)
      rw [zero_smul, hQga])
  have hZidx : lRegIndex S T gammaG Zg Zg 0 a = 0 := by
    simpa only [Zg, zero_mul] using
      (lRegIndex_smul (I := I) S T 0 gammaG Jg Zg 0 a)
  have hQgNonneg : 0 ≤ lRegIndex S T gammaG Qg Qg a b := by
    rw [hZidx, zero_add] at hnonneg
    exact hnonneg
  have hBetaGerm : ∀ s ∈ uIoo a b, beta =ᶠ[nhds s] gammaG := by
    intro s hs
    have hs' : s ∈ Ioo a b := by
      simpa only [uIoo_of_le hab.le] using hs
    exact (hGBGerm s ⟨ha0.le.trans hs'.1.le, hs'.2.le⟩).symm
  have hQGerm : ∀ s ∈ uIoo a b,
      ∀ᶠ r in nhds s, (Q r : E) = (Qg r : E) := by
    intro s hs
    have hs' : s ∈ Ioo a b := by
      simpa only [uIoo_of_le hab.le] using hs
    exact Filter.EventuallyEq.symm
      (hQgGerm s ⟨ha0.le.trans hs'.1.le, hs'.2.le⟩)
  have hQQeq : lRegIndex S T beta Q Q a b =
      lRegIndex S T gammaG Qg Qg a b := by
    apply lIndex_germ_congr (I := I) S T Q Q Qg Qg
    · exact hBetaGerm
    · exact hQGerm
    · exact hQGerm
  have hQQNonneg : 0 ≤ lRegIndex S T beta Q Q a b := by
    rw [hQQeq]
    exact hQgNonneg
  have htailInter : uIcc a b ⊆ K ∩ Omega := by
    intro s hs
    have hs' : s ∈ Icc a b := by
      simpa only [uIcc_of_le hab.le] using hs
    exact ⟨hsegK ⟨ha0.le.trans hs'.1, hs'.2⟩,
      hOmegaSeg ⟨ha0.le.trans hs'.1, hs'.2⟩⟩
  have hJg2 : ContMDiff 𝓘(Real, Real) I.tangent 2
      (fun s : Real ↦
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (gammaG s) (Jg s) : TangentBundle I M)) :=
    hJgSmooth'.of_le (by decide :
      (2 : WithTop ENat) ≤ (↑(⊤ : ENat) : WithTop ENat))
  have hQg2 : ContMDiff 𝓘(Real, Real) I.tangent 2
      (fun s : Real ↦
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (gammaG s) (Qg s) : TangentBundle I M)) :=
    hQg8.of_le (by norm_num)
  have hregTail : ∀ s ∈ uIcc a b, T - s ^ 2 ∈ D.regular := by
    intro s hs
    exact hreg (A0, s) ⟨hA0V, (htailInter hs).1⟩
  have hregGTail : ∀ s ∈ uIcc a b, T - s ^ 2 ∈ D.regular := by
    intro s hs
    have hs' : s ∈ Icc a b := by
      simpa only [uIcc_of_le hab.le] using hs
    have hs0b : s ∈ Icc (0 : Real) b :=
      ⟨ha0.le.trans hs'.1, hs'.2⟩
    have hs0b' : s ∈ uIcc (0 : Real) b := by
      rw [uIcc_of_le hb0.le]
      exact hs0b
    exact (hgeoG.2.2 s hs0b').1
  have hJJgInt := lRegIndex_int (I := I) S hS T a b gammaG Jg Jg
    hJg2 hJg2 hregGTail
  have hJQgInt := lRegIndex_int (I := I) S hS T a b gammaG Jg Qg
    hJg2 hQg2 hregGTail
  have hQQgInt := lRegIndex_int (I := I) S hS T a b gammaG Qg Qg
    hQg2 hQg2 hregGTail
  have hBetaIGerm : ∀ s ∈ Ioo a b, beta =ᶠ[nhds s] gammaG := by
    intro s hs
    exact hBetaGerm s (by simpa only [uIoo_of_le hab.le] using hs)
  have hJGerm : ∀ s ∈ Ioo a b,
      ∀ᶠ r in nhds s, (J r : E) = (Jg r : E) := by
    intro s hs
    exact Filter.EventuallyEq.symm
      (hJgGerm s ⟨ha0.le.trans hs.1.le, hs.2.le⟩)
  have hQIGerm : ∀ s ∈ Ioo a b,
      ∀ᶠ r in nhds s, (Q r : E) = (Qg r : E) := by
    intro s hs
    exact hQGerm s (by simpa only [uIoo_of_le hab.le] using hs)
  have hJJInt : IntervalIntegrable (lRegIndexInt S T beta J J)
      MeasureTheory.volume a b :=
    (lIndexInt_int_iff (I := I) S T J J Jg Jg a b hab.le
      hBetaIGerm hJGerm hJGerm).2 hJJgInt
  have hJQInt : IntervalIntegrable (lRegIndexInt S T beta J Q)
      MeasureTheory.volume a b :=
    (lIndexInt_int_iff (I := I) S T J Q Jg Qg a b hab.le
      hBetaIGerm hJGerm hQIGerm).2 hJQgInt
  have hQQInt : IntervalIntegrable (lRegIndexInt S T beta Q Q)
      MeasureTheory.volume a b :=
    (lIndexInt_int_iff (I := I) S T Q Q Qg Qg a b hab.le
      hBetaIGerm hQIGerm hQIGerm).2 hQQgInt
  have hbetaAt : ∀ s ∈ Icc a b,
      ContMDiffAt 𝓘(Real, Real) I ∞ beta s := by
    intro s hs
    have hsK := hsegK ⟨ha0.le.trans hs.1, hs.2⟩
    have hAlphaAt := (halpha (A0, s) ⟨hA0V, hsK⟩).contMDiffAt
      ((hVopen.prod hKopen).mem_nhds ⟨hA0V, hsK⟩)
    change ContMDiffAt 𝓘(Real, Real) I ∞
      (alpha ∘ fun r : Real ↦ (A0, r)) s
    exact hAlphaAt.comp s
      (contMDiff_const.prodMk contMDiff_id).contMDiffAt
  have hBetaMdiff : ∀ s ∈ uIcc a b, ∀ᶠ r in nhds s,
      MDifferentiableAt 𝓘(Real, Real) I beta r := by
    intro s hs
    have hs' : s ∈ Icc a b := by
      simpa only [uIcc_of_le hab.le] using hs
    have hsK := hsegK ⟨ha0.le.trans hs'.1, hs'.2⟩
    filter_upwards [hKopen.mem_nhds hsK] with r hr
    have hAlphaAt := (halpha (A0, r) ⟨hA0V, hr⟩).contMDiffAt
      ((hVopen.prod hKopen).mem_nhds ⟨hA0V, hr⟩)
    have hBetaAt : ContMDiffAt 𝓘(Real, Real) I ∞ beta r := by
      change ContMDiffAt 𝓘(Real, Real) I ∞
        (alpha ∘ fun s : Real ↦ (A0, s)) r
      exact hAlphaAt.comp r
        (contMDiff_const.prodMk contMDiff_id).contMDiffAt
    exact hBetaAt.mdifferentiableAt (by simp)
  have hA : ∀ s ∈ uIcc a b, DifferentiableAt Real
      (chartRepAt (I := I) beta
        (fun r ↦ lVelocity (I := I) beta r) s) s := by
    intro s hs
    have hs' : s ∈ Icc a b := by
      simpa only [uIcc_of_le hab.le] using hs
    simpa only [lVelocity] using
      velocity_rep_diffAt (I := I) beta s (hbetaAt s hs')
  have hJacTail : IsLRegJacobi S T beta J (uIcc a b) := by
    intro s hs
    exact hJacK s (htailInter hs).1
  have hJdiff : ∀ s ∈ uIcc a b,
      DifferentiableAt Real (chartRepAt (I := I) beta J s) s :=
    fun s hs ↦ (hJacTail s hs).2.1
  have hWdiff : ∀ s ∈ uIcc a b,
      DifferentiableAt Real (chartRepAt (I := I) beta W s) s := by
    intro s hs
    apply chartRep_diff_at (I := I)
    exact (hW.of_le (by norm_num)).contMDiffAt
      (hOmega.mem_nhds (htailInter hs).2)
  have hQdiff : ∀ s ∈ uIcc a b,
      DifferentiableAt Real (chartRepAt (I := I) beta Q s) s := by
    intro s hs
    have hrep : chartRepAt (I := I) beta Q s = fun r ↦
        chartRepAt (I := I) beta W s r -
          chartRepAt (I := I) beta J s r := by
      rw [show Q = fun r ↦ W r + (-1 : Real) • J r by
        funext r
        dsimp only [Q]
        module]
      rw [chartRepAt_add, chartRepAt_smul]
      funext r
      module
    rw [hrep]
    exact (hWdiff s hs).sub (hJdiff s hs)
  have hJQzero : lRegIndex S T beta J Q a b = 0 := by
    have hgreen := lRegIndex_jacobi (I := I) S hS T beta J Q a b
      hregTail hBetaMdiff hA hJacTail hQdiff hJQInt
    rw [hgreen, hQa, hQb]
    simp
  have hsquare := lIndex_sq_add (I := I) S T 1 beta J Q a b
    hJdiff hQdiff hJJInt hJQInt hQQInt
  have hfield : (fun s ↦ J s + (1 : Real) • Q s) = W := by
    funext s
    dsimp only [Q]
    module
  rw [hfield] at hsquare
  have hdecomp : lRegIndex S T beta W W a b =
      lRegIndex S T beta J J a b + lRegIndex S T beta Q Q a b := by
    rw [hsquare, hJQzero]
    ring
  have hJleW : lRegIndex S T beta J J a b ≤
      lRegIndex S T beta W W a b := by
    rw [hdecomp]
    linarith
  have hgreenJJ := lRegIndex_jacobi (I := I) S hS T beta J J a b
    hregTail hBetaMdiff hA hJacTail hJdiff hJJInt
  have hJJend : 2 * lRegIndex S T beta J J a b =
      g.inner y (covDerivAlong (I := I) g beta J b) Y := by
    rw [hgreenJJ, hJa, hJb]
    simp only [map_zero, sub_zero]
    ring
  let Jm : (s : Real) → TangentSpace I (beta s) := fun s ↦
    mfderiv 𝓘(Real, E) I (fun A : E ↦ alpha (A, s)) A0 B
  have hJmEq : Jm =ᶠ[nhds b] J := by
    filter_upwards [hKopen.mem_nhds hbK] with s hs
    have hAlphaAt := (halpha (A0, s) ⟨hA0V, hs⟩).contMDiffAt
      ((hVopen.prod hKopen).mem_nhds ⟨hA0V, hs⟩)
    change mfderiv 𝓘(Real, E) I
        (fun A : E ↦ alpha (A, s)) A0 B =
      lVelocity (I := I) (fun u : Real ↦ alpha (A0 + u • B, s)) 0
    exact (lTailLine_deriv (I := I) A0 B s hAlphaAt).symm
  have hcovEq : covDerivAlong (I := I) g beta Jm b =
      covDerivAlong (I := I) g beta J b :=
    covDerivAlong_congr_of_eventuallyEq (I := I) g beta hJmEq
  have hbranch : hessFun (I := I) g branch y Y Y =
      g.inner y (covDerivAlong (I := I) g beta J b) Y := by
    have hh := lTailBranch_hess S hS T a b hab hVopen hA0V hKopen
      hKconn haK hbK hstart halpha hreg
      (fun A hA s hs ↦ hEuler A hA s
        (hsegK ⟨ha0.le.trans hs.1, hs.2⟩)) hinj Y Y
    simpa only [g, branch, y, beta, hloc, B, Jm, hcovEq] using hh
  calc
    hessFun (I := I) (S.base.metric (T - b ^ 2))
        (fun q ↦ lRegAction S T
          (fun s ↦ alpha
            ((lTail_localDiffeo hVopen hA0V hbK halpha hinj).localInverse q, s))
          a b) (alpha (A0, b)) Y Y =
      hessFun (I := I) g branch y Y Y := rfl
    _ = g.inner y (covDerivAlong (I := I) g beta J b) Y := hbranch
    _ = 2 * lRegIndex S T beta J J a b := hJJend.symm
    _ ≤ 2 * lRegIndex S T beta W W a b :=
      mul_le_mul_of_nonneg_left hJleW (by norm_num)
    _ = 2 * lRegIndex S T (fun s ↦ alpha (A0, s)) W W a b := rfl

end DifferentialGeometry.PDE.RicciFlow.Perelman
