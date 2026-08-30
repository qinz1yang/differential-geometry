import DifferentialGeometry.Geometry.Metric.RicciSoliton.Models

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry

open Curvature Operator Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
  [FiniteDimensional Real F]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {G : Type*} [TopologicalSpace G]
variable {J : ModelWithCorners Real F G}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
variable [T2Space M] [I.Boundaryless] [T2Space N] [J.Boundaryless]

set_option backward.isDefEq.respectTransparency false in
theorem gradientRicciSoliton_prod_mixed_hessian
    [CompleteSpace E] [CompleteSpace F]
    {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric J N}
    {u : C^∞⟮I.prod J, M × N; Real⟯} {σ : Real}
    (hs : gradientRicciSoliton (I := I.prod J) (g.prod h) u σ)
    (x : M × N) (v : TangentSpace I x.1) (w : TangentSpace J x.2) :
    hessFun (I := I.prod J) (g.prod h) u x (v, 0) (0, w) = 0 := by
  have hs' := hs x (v, 0) (0, w)
  rw [Curvature.ricciTensor_prod, SmoothRiemannianMetric.prod_inner,
    mfderiv_fst, mfderiv_snd] at hs'
  change (Curvature.ricciTensor (I := I) g x.1 v 0 +
      Curvature.ricciTensor (I := J) h x.2 0 w) +
      hessFun (I := I.prod J) (g.prod h) u x (v, 0) (0, w) =
    (σ / 2) * (g.inner x.1 v 0 + h.inner x.2 0 w) at hs'
  simpa using hs'

set_option backward.isDefEq.respectTransparency false in
theorem gradientRicciSoliton_prod_fst_component
    [CompleteSpace E] [CompleteSpace F]
    {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric J N}
    {u : C^∞⟮I.prod J, M × N; Real⟯} {σ : Real}
    (hs : gradientRicciSoliton (I := I.prod J) (g.prod h) u σ)
    (x : M × N) (v w : TangentSpace I x.1) :
    Curvature.ricciTensor (I := I) g x.1 v w +
        hessFun (I := I.prod J) (g.prod h) u x (v, 0) (w, 0) =
      (σ / 2) * g.inner x.1 v w := by
  have hs' := hs x (v, 0) (w, 0)
  rw [Curvature.ricciTensor_prod, SmoothRiemannianMetric.prod_inner,
    mfderiv_fst, mfderiv_snd] at hs'
  change (Curvature.ricciTensor (I := I) g x.1 v w +
      Curvature.ricciTensor (I := J) h x.2 0 0) +
      hessFun (I := I.prod J) (g.prod h) u x (v, 0) (w, 0) =
    (σ / 2) * (g.inner x.1 v w + h.inner x.2 0 0) at hs'
  simpa only [map_zero, add_zero] using hs'

set_option backward.isDefEq.respectTransparency false in
theorem gradientRicciSoliton_prod_snd_component
    [CompleteSpace E] [CompleteSpace F]
    {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric J N}
    {u : C^∞⟮I.prod J, M × N; Real⟯} {σ : Real}
    (hs : gradientRicciSoliton (I := I.prod J) (g.prod h) u σ)
    (x : M × N) (v w : TangentSpace J x.2) :
    Curvature.ricciTensor (I := J) h x.2 v w +
        hessFun (I := I.prod J) (g.prod h) u x (0, v) (0, w) =
      (σ / 2) * h.inner x.2 v w := by
  have hs' := hs x (0, v) (0, w)
  rw [Curvature.ricciTensor_prod, SmoothRiemannianMetric.prod_inner,
    mfderiv_fst, mfderiv_snd] at hs'
  change (Curvature.ricciTensor (I := I) g x.1 0 0 +
      Curvature.ricciTensor (I := J) h x.2 v w) +
      hessFun (I := I.prod J) (g.prod h) u x (0, v) (0, w) =
    (σ / 2) * (g.inner x.1 0 0 + h.inner x.2 v w) at hs'
  simpa only [map_zero, zero_add] using hs'

set_option backward.isDefEq.respectTransparency false in
theorem gradientRicciSoliton_prod_real_line_hessian
    [CompleteSpace E]
    {g : SmoothRiemannianMetric I M}
    {u : C^∞⟮I.prod (modelWithCornersSelf Real Real), M × Real; Real⟯} {σ : Real}
    (hs : gradientRicciSoliton
      (I := I.prod (modelWithCornersSelf Real Real))
      (g.prod (euclideanMetric (E := Real))) u σ)
    (x : M × Real) (a b : Real) :
    hessFun (I := I.prod (modelWithCornersSelf Real Real))
        (g.prod (euclideanMetric (E := Real))) u x (0, a) (0, b) =
      (σ / 2) * (a * b) := by
  have h := gradientRicciSoliton_prod_snd_component
    (I := I) (J := modelWithCornersSelf Real Real) hs x a b
  rw [euclideanMetric_ricciTensor] at h
  have h' : hessFun (I := I.prod (modelWithCornersSelf Real Real))
        (g.prod (euclideanMetric (E := Real))) u x (0, a) (0, b) =
      (σ / 2) * (b * a) := by
    simpa [DifferentialGeometry.euclideanMetric_inner] using h
  calc
    _ = (σ / 2) * (b * a) := h'
    _ = _ := by ring

set_option backward.isDefEq.respectTransparency false in
private theorem lineUnit_parallel (s a : Real) :
    (Connection.LeviCivita (I := modelWithCornersSelf Real Real)
      (euclideanMetric (E := Real))).toFun
        (fun _ : Real => (1 : Real)) s a = 0 := by
  let U : (q : Real) → TangentSpace (modelWithCornersSelf Real Real) q :=
    fun _ => (1 : Real)
  have hU : MDiffAt (T% U) s := by
    have hU' : CMDiff ∞ (T% U) :=
      contMDiff_vectorSpace_iff_contDiff.mpr contDiff_const
    exact hU'.mdifferentiableAt (by simp)
  have hmc := (Connection.LeviCivita_isMetricCompatible
    (I := modelWithCornersSelf Real Real) (euclideanMetric (E := Real)))
    hU hU (Set.mem_univ s) a
  dsimp [U] at hmc ⊢
  let c : TangentSpace (modelWithCornersSelf Real Real) s :=
    (Connection.LeviCivita (I := modelWithCornersSelf Real Real)
      (euclideanMetric (E := Real))).toFun
        (fun _ : Real => (1 : Real)) s a
  have hfun : (fun b : Real =>
      (euclideanMetric (E := Real)).inner b (1 : Real) (1 : Real)) =
      fun _ : Real => (1 : Real) := by
    funext b
    rw [DifferentialGeometry.euclideanMetric_inner, Real.inner_apply]
    norm_num
  have hinnerLeft : (euclideanMetric (E := Real)).inner s c (1 : Real) =
      tangentSpaceModelContinuousLinearEquiv
        (I := modelWithCornersSelf Real Real) s c := by
    rw [DifferentialGeometry.euclideanMetric_inner, Real.inner_apply]
    rw [tangentSpaceModelContinuousLinearEquiv_apply]
    ring
  have hinnerRight : (euclideanMetric (E := Real)).inner s (1 : Real) c =
      tangentSpaceModelContinuousLinearEquiv
        (I := modelWithCornersSelf Real Real) s c := by
    rw [DifferentialGeometry.euclideanMetric_inner, Real.inner_apply]
    rw [tangentSpaceModelContinuousLinearEquiv_apply]
    ring
  rw [hfun, mfderiv_const, hinnerLeft, hinnerRight] at hmc
  change (0 : Real) =
    tangentSpaceModelContinuousLinearEquiv
        (I := modelWithCornersSelf Real Real) s c +
      tangentSpaceModelContinuousLinearEquiv
        (I := modelWithCornersSelf Real Real) s c at hmc
  have hc : tangentSpaceModelContinuousLinearEquiv
      (I := modelWithCornersSelf Real Real) s c = 0 := by
    linarith
  apply (tangentSpaceModelContinuousLinearEquiv
    (I := modelWithCornersSelf Real Real) s).injective
  simpa [c] using hc

private def verticalUnit (p : M × Real) :
    TangentSpace (I.prod (modelWithCornersSelf Real Real)) p :=
  ((0 : TangentSpace I p.1),
    (1 : TangentSpace (modelWithCornersSelf Real Real) p.2))

set_option backward.isDefEq.respectTransparency false in
omit [FiniteDimensional Real E] [T2Space M] [I.Boundaryless] in
private theorem verticalUnit_contMDiff :
    ContMDiff (I.prod (modelWithCornersSelf Real Real))
      ((I.prod (modelWithCornersSelf Real Real)).prod
        (modelWithCornersSelf Real (E × Real))) ∞
      (T% (verticalUnit (I := I) (M := M))) := by
  let W : (q : Real) → TangentSpace (modelWithCornersSelf Real Real) q :=
    fun _ => 1
  have hline : ContMDiff (modelWithCornersSelf Real Real)
      ((modelWithCornersSelf Real Real).prod
        (modelWithCornersSelf Real Real)) ∞
      (T% W) :=
    contMDiff_vectorSpace_iff_contDiff.mpr contDiff_const
  have hpair : ContMDiff (I.prod (modelWithCornersSelf Real Real))
      ((I.prod (modelWithCornersSelf Real E)).prod
        ((modelWithCornersSelf Real Real).prod
          (modelWithCornersSelf Real Real))) ∞
      (fun p : M × Real =>
        (TotalSpace.mk' E p.1 (0 : TangentSpace I p.1),
          TotalSpace.mk' Real p.2
            (W p.2))) := by
    exact ((contMDiff_zeroSection Real (TangentSpace I)).comp contMDiff_fst).prodMk
      (hline.comp contMDiff_snd)
  exact contMDiff_equivTangentBundleProd_symm.comp hpair

set_option backward.isDefEq.respectTransparency false in
omit [I.Boundaryless] in
private theorem verticalUnit_parallel
    [CompleteSpace E] (g : SmoothRiemannianMetric I M)
    (x : M × Real)
    (v : TangentSpace (I.prod (modelWithCornersSelf Real Real)) x) :
    (Connection.LeviCivita (I := I.prod (modelWithCornersSelf Real Real))
      (g.prod (euclideanMetric (E := Real)))).toFun
        (fun p : M × Real =>
          ((0 : TangentSpace I p.1),
            (1 : TangentSpace (modelWithCornersSelf Real Real) p.2))) x v = 0 := by
  let X := Curvature.smoothExtensionTangent (I := I) x.1 v.1
  let Y := Curvature.smoothExtensionTangent
    (I := modelWithCornersSelf Real Real) x.2 v.2
  let Z : (q : M) → TangentSpace I q := fun _ => 0
  let W : (q : Real) → TangentSpace (modelWithCornersSelf Real Real) q :=
    fun _ => 1
  have hX := Curvature.smoothExtensionTangent_contMDiff (I := I) x.1 v.1
  have hY := Curvature.smoothExtensionTangent_contMDiff
    (I := modelWithCornersSelf Real Real) x.2 v.2
  have hZ : ContMDiff I (I.prod (modelWithCornersSelf Real E)) ∞ (T% Z) := by
    exact contMDiff_zeroSection Real (TangentSpace I)
  have hW : ContMDiff (modelWithCornersSelf Real Real)
      ((modelWithCornersSelf Real Real).prod
        (modelWithCornersSelf Real Real)) ∞ (T% W) :=
    contMDiff_vectorSpace_iff_contDiff.mpr contDiff_const
  have hconn := Connection.leviCivita_prod
    (I := I) (J := modelWithCornersSelf Real Real)
    g (euclideanMetric (E := Real)) X Z Y W hX hZ hY hW x
  have hXx : X x.1 = v.1 :=
    Curvature.smoothExtensionTangent_eq x.1 v.1
  have hYx : Y x.2 = v.2 :=
    Curvature.smoothExtensionTangent_eq x.2 v.2
  have hv : (X x.1, Y x.2) = v := by
    rw [hXx, hYx]
    exact Prod.eta v
  have hzero : (Connection.LeviCivita (I := I) g).toFun Z x.1 (X x.1) = 0 := by
    change ((Connection.LeviCivita (I := I) g).toFun
      (0 : (q : M) → TangentSpace I q) x.1) (X x.1) = 0
    rw [CovariantDerivative.zero]
    rfl
  have hone : (Connection.LeviCivita (I := modelWithCornersSelf Real Real)
      (euclideanMetric (E := Real))).toFun W x.2 (Y x.2) = 0 := by
    exact lineUnit_parallel x.2 (Y x.2)
  rw [hv] at hconn
  have hconn' : (Connection.LeviCivita
      (I := I.prod (modelWithCornersSelf Real Real))
      (g.prod (euclideanMetric (E := Real)))).toFun
        (fun p : M × Real =>
          ((0 : TangentSpace I p.1),
            (1 : TangentSpace (modelWithCornersSelf Real Real) p.2))) x v =
      ((0 : TangentSpace I x.1),
        (0 : TangentSpace (modelWithCornersSelf Real Real) x.2)) := by
    simpa [Z, W, hzero, hone] using hconn
  exact hconn'

set_option backward.isDefEq.respectTransparency false in
omit [FiniteDimensional Real E] [IsManifold I ∞ M] [T2Space M]
    [I.Boundaryless] in
private theorem lineDerivative_eq_mvfderiv
    (u : C^∞⟮I.prod (modelWithCornersSelf Real Real), M × Real; Real⟯)
    (p : M × Real) :
    deriv (fun s : Real => u (p.1, s)) p.2 =
      mvfderiv (I := I.prod (modelWithCornersSelf Real Real)) u p
        (verticalUnit (I := I) (M := M) p) := by
  rcases p with ⟨y, s⟩
  have hu : MDiffAt u (y, s) :=
    u.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hemb : MDiffAt (fun t : Real => (y, t)) s :=
    mdifferentiableAt_const.prodMk mdifferentiableAt_id
  have hcomp := mfderiv_comp_apply s hu hemb (1 : Real)
  rw [mfderiv_prod_right] at hcomp
  have hvel : (ContinuousLinearMap.inr Real
      (TangentSpace I y)
      (TangentSpace (modelWithCornersSelf Real Real) s)) (1 : Real) =
      verticalUnit (I := I) (M := M) (y, s) := by
    apply Prod.ext <;> simp [verticalUnit]
  have hcomp' := hcomp.trans
    (congrArg (mfderiv (I.prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real Real) u (y, s)) hvel)
  have hcomp'' := congrArg
    (NormedSpace.fromTangentSpace (𝕜 := Real) (u (y, s))) hcomp'
  have hleft :
      (NormedSpace.fromTangentSpace (𝕜 := Real) (u (y, s)))
          ((fderiv Real (fun t : Real => u (y, t)) s) 1) =
        (fderiv Real (fun t : Real => u (y, t)) s) 1 := by
    rfl
  rw [mfderiv_eq_fderiv] at hcomp''
  change (NormedSpace.fromTangentSpace (𝕜 := Real) (u (y, s)))
      ((fderiv Real (fun t : Real => u (y, t)) s) 1) = _ at hcomp''
  rw [hleft] at hcomp''
  simpa only [deriv, DifferentialGeometry.mvfderiv_real_eq_mfderiv,
    mfderiv_eq_fderiv] using hcomp''

omit [FiniteDimensional Real E] [T2Space M] [I.Boundaryless] in
private theorem verticalDerivative_contMDiff
    (u : C^∞⟮I.prod 𝓘(Real, Real), M × Real; Real⟯) :
    ContMDiff (I.prod 𝓘(Real, Real))
      𝓘(Real, Real) ∞
      (fun p : M × Real => deriv (fun t : Real => u (p.1, t)) p.2) := by
  let uSwap : C^∞⟮𝓘(Real, Real).prod I, Real × M; Real⟯ :=
    ⟨fun p : Real × M => u (p.2, p.1),
      u.contMDiff.comp (contMDiff_snd.prodMk contMDiff_fst)⟩
  have h := DifferentialGeometry.contMDiff_partial_deriv_fst I uSwap
  have hcomp := h.comp (contMDiff_snd.prodMk contMDiff_fst)
  convert hcomp using 1
  · ext x y
    rfl
  · funext p
    rfl

set_option backward.isDefEq.respectTransparency false in
private theorem verticalDerivative_mvfderiv
    [CompleteSpace E] (g : SmoothRiemannianMetric I M)
    (u : C^∞⟮I.prod (modelWithCornersSelf Real Real), M × Real; Real⟯)
    (p : M × Real)
    (v : TangentSpace (I.prod (modelWithCornersSelf Real Real)) p) :
    mvfderiv (I := I.prod (modelWithCornersSelf Real Real))
        (fun q : M × Real => deriv (fun t : Real => u (q.1, t)) q.2) p v =
      hessFun (I := I.prod (modelWithCornersSelf Real Real))
        (g.prod (euclideanMetric (E := Real))) u p v
          (verticalUnit (I := I) (M := M) p) := by
  let K := I.prod (modelWithCornersSelf Real Real)
  let metric := g.prod (euclideanMetric (E := Real))
  let theta : (q : M × Real) → TangentSpace K q →L[Real] Real :=
    mvfderiv (I := K) u
  let Y : (q : M × Real) → TangentSpace K q :=
    verticalUnit (I := I) (M := M)
  have htheta : MDiffAtCotangent theta p := by
    have h := cotangentCov_mvfderiv_smooth (I := K) u.contMDiff
    exact (h p).mdifferentiableAt (by simp)
  have hY : MDiffAt (T% Y) p :=
    verticalUnit_contMDiff (I := I) (M := M) |>.contMDiffAt.mdifferentiableAt (by simp)
  have hpair := cotangentCov_dualPairing
    (Connection.LeviCivita (I := K) metric) htheta hY v
  have hparallel :
      (Connection.LeviCivita (I := K) metric).toFun Y p v = 0 := by
    exact verticalUnit_parallel (I := I) g p v
  rw [hparallel, map_zero, add_zero] at hpair
  have hpairing :
      (fun q : M × Real => theta q (Y q)) =
        fun q : M × Real => deriv (fun t : Real => u (q.1, t)) q.2 := by
    funext q
    exact (lineDerivative_eq_mvfderiv (I := I) u q).symm
  rw [hpairing] at hpair
  rw [Connection.hessFun_eq_abstract (I := K) metric u.contMDiff p v (Y p),
    Connection.abstractHessian_apply]
  exact hpair

set_option backward.isDefEq.respectTransparency false in
private theorem verticalDerivative_mvfderiv_eq
    [CompleteSpace E] (g : SmoothRiemannianMetric I M)
    (u : C^∞⟮I.prod (modelWithCornersSelf Real Real), M × Real; Real⟯)
    (sigma : Real)
    (hs : gradientRicciSoliton
      (I := I.prod (modelWithCornersSelf Real Real))
      (g.prod (euclideanMetric (E := Real))) u sigma)
    (p : M × Real)
    (v : TangentSpace (I.prod (modelWithCornersSelf Real Real)) p) :
    mvfderiv (I := I.prod (modelWithCornersSelf Real Real))
        (fun q : M × Real => deriv (fun t : Real => u (q.1, t)) q.2) p v =
      (sigma / 2) * v.2 := by
  rw [verticalDerivative_mvfderiv (I := I) g u p v]
  change hessFun (I := I.prod (modelWithCornersSelf Real Real))
      (g.prod (euclideanMetric (E := Real))) u p v (0, 1) = _
  have hv : v = (v.1, 0) + (0, v.2) := by
    calc
      v = (v.1, v.2) := (Prod.eta v).symm
      _ = (v.1, 0) + (0, v.2) := by simp
  let B := hessFun (I := I.prod (modelWithCornersSelf Real Real))
    (g.prod (euclideanMetric (E := Real))) u p
  calc
    B v (0, 1) = B ((v.1, 0) + (0, v.2)) (0, 1) := by rw [← hv]
    _ = (B (v.1, 0) + B (0, v.2)) (0, 1) := by rw [map_add]
    _ = B (v.1, 0) (0, 1) + B (0, v.2) (0, 1) := rfl
    _ = 0 + (sigma / 2) * (v.2 * 1) := by
      rw [gradientRicciSoliton_prod_mixed_hessian hs p v.1 1,
        gradientRicciSoliton_prod_real_line_hessian hs p v.2 1]
    _ = (sigma / 2) * v.2 := by ring

set_option backward.isDefEq.respectTransparency false in
private theorem adjustedVerticalDerivative_mfderiv_eq_zero
    [CompleteSpace E] (g : SmoothRiemannianMetric I M)
    (u : C^∞⟮I.prod (modelWithCornersSelf Real Real), M × Real; Real⟯)
    (sigma : Real)
    (hs : gradientRicciSoliton
      (I := I.prod (modelWithCornersSelf Real Real))
      (g.prod (euclideanMetric (E := Real))) u sigma)
    (p : M × Real) :
    mfderiv (I.prod (modelWithCornersSelf Real Real))
        (modelWithCornersSelf Real Real)
        (fun q : M × Real =>
          deriv (fun t : Real => u (q.1, t)) q.2 - (sigma / 2) * q.2) p = 0 := by
  let K := I.prod (modelWithCornersSelf Real Real)
  let q : M × Real → Real :=
    fun z => deriv (fun t : Real => u (z.1, t)) z.2
  let ell : M × Real → Real := fun z => (sigma / 2) * z.2
  have hqSmooth : ContMDiff K (modelWithCornersSelf Real Real) ∞ q := by
    exact verticalDerivative_contMDiff (I := I) u
  have hqDiff : MDiffAt q p :=
    hqSmooth.contMDiffAt.mdifferentiableAt (by simp)
  have hellSmooth : ContMDiff K (modelWithCornersSelf Real Real) ∞ ell := by
    exact contMDiff_const.mul contMDiff_snd
  have hellDiff : MDiffAt ell p :=
    hellSmooth.contMDiffAt.mdifferentiableAt (by simp)
  ext v
  apply (NormedSpace.fromTangentSpace (𝕜 := Real)
    (q p - ell p)).injective
  change mvfderiv (I := K) (q - ell) p v = 0
  rw [_root_.mvfderiv_sub hqDiff hellDiff]
  change mvfderiv (I := K) q p v - mvfderiv (I := K) ell p v = 0
  have hqv := verticalDerivative_mvfderiv_eq
    (I := I) g u sigma hs p v
  have hellv := DifferentialGeometry.mvfderiv_const_mul K
    (sigma / 2) (f := fun z : M × Real => z.2) (x := p)
      mdifferentiableAt_snd
  change mvfderiv (I := K) ell p = _ at hellv
  rw [hellv]
  change mvfderiv (I := K) q p v -
      (sigma / 2) * mvfderiv (I := K) (fun z : M × Real => z.2) p v = 0
  rw [hqv, DifferentialGeometry.mvfderiv_real_eq_mfderiv, mfderiv_snd]
  change (sigma / 2) * v.2 - (sigma / 2) * v.2 = 0
  ring

private theorem verticalDerivative_eq_affine
    [CompleteSpace E] [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M)
    (u : C^∞⟮I.prod (modelWithCornersSelf Real Real), M × Real; Real⟯)
    (sigma : Real)
    (hs : gradientRicciSoliton
      (I := I.prod (modelWithCornersSelf Real Real))
      (g.prod (euclideanMetric (E := Real))) u sigma) :
    ∃ a : Real, ∀ p : M × Real,
      deriv (fun t : Real => u (p.1, t)) p.2 = (sigma / 2) * p.2 + a := by
  let K := I.prod (modelWithCornersSelf Real Real)
  let q : M × Real → Real :=
    fun z => deriv (fun t : Real => u (z.1, t)) z.2
  let ell : M × Real → Real := fun z => (sigma / 2) * z.2
  let r : M × Real → Real := fun z => q z - ell z
  have hrSmooth : ContMDiff K (modelWithCornersSelf Real Real) ∞ r := by
    exact (verticalDerivative_contMDiff (I := I) u).sub
      (contMDiff_const.mul contMDiff_snd)
  have hzero : ∀ p : M × Real,
      mfderiv K (modelWithCornersSelf Real Real) r p = 0 := by
    intro p
    exact adjustedVerticalDerivative_mfderiv_eq_zero
      (I := I) g u sigma hs p
  have hlocal := DifferentialGeometry.isLocallyConstant_of_mfderiv_eq_zero
    (hrSmooth.mdifferentiable (by simp)) hzero
  obtain ⟨a, ha⟩ := hlocal.exists_eq_const
  refine ⟨a, fun p => ?_⟩
  have hp := congrFun ha p
  change q p - ell p = a at hp
  change q p = ell p + a
  linarith

omit [FiniteDimensional Real E] [IsManifold I ∞ M] [T2Space M]
    [I.Boundaryless] in
private theorem potential_eq_slice_add_quadratic
    (u : C^∞⟮I.prod (modelWithCornersSelf Real Real), M × Real; Real⟯)
    (sigma a : Real)
    (ha : ∀ p : M × Real,
      deriv (fun t : Real => u (p.1, t)) p.2 = (sigma / 2) * p.2 + a) :
    ∀ p : M × Real,
      u p = u (p.1, 0) + (sigma / 4) * p.2 ^ 2 + a * p.2 := by
  rintro ⟨y, s⟩
  let f : Real → Real := fun t => u (y, t)
  let P : Real → Real := fun t => (sigma / 4) * t ^ 2 + a * t
  have hfSmooth : ContDiff Real ∞ f := by
    exact (u.contMDiff.comp (contMDiff_const.prodMk contMDiff_id)).contDiff
  have hfDiff : Differentiable Real f :=
    hfSmooth.differentiable (by simp)
  have hPDiff : Differentiable Real P := by
    fun_prop
  have hzero : ∀ t : Real, deriv (f - P) t = 0 := by
    intro t
    have hfu : HasDerivAt f ((sigma / 2) * t + a) t := by
      have h := (hfDiff t).hasDerivAt
      rw [ha (y, t)] at h
      exact h
    have hP : HasDerivAt P ((sigma / 2) * t + a) t := by
      have hPderiv : deriv P t = (sigma / 2) * t + a := by
        change deriv (fun z : Real => (sigma / 4) * z ^ 2 + a * z) t = _
        rw [deriv_fun_add (by fun_prop) (by fun_prop),
          deriv_const_mul_field, deriv_pow_field, deriv_const_mul_id]
        ring
      have h := (hPDiff t).hasDerivAt
      rw [hPderiv] at h
      exact h
    have h := (hfu.sub hP).deriv
    rw [sub_self] at h
    exact h
  have hconst := is_const_of_deriv_eq_zero (hfDiff.sub hPDiff) hzero s 0
  change f s - P s = f 0 - P 0 at hconst
  dsimp only [f, P] at hconst ⊢
  ring_nf at hconst ⊢
  linarith

set_option backward.isDefEq.respectTransparency false in
theorem gradientRicciSoliton_prod_real_line_potential_splitting
    [CompleteSpace E] [ConnectedSpace M]
    {g : SmoothRiemannianMetric I M}
    {u : C^∞⟮I.prod (modelWithCornersSelf Real Real), M × Real; Real⟯}
    {sigma : Real}
    (hs : gradientRicciSoliton
      (I := I.prod (modelWithCornersSelf Real Real))
      (g.prod (euclideanMetric (E := Real))) u sigma)
    (hsigma : 0 < sigma) :
    ∃ s0 : Real, ∃ psi : C^∞⟮I, M; Real⟯,
      (∀ p : M × Real,
        u p = psi p.1 + (sigma / 4) * (p.2 - s0) ^ 2) ∧
      gradientRicciSoliton (I := I) g psi sigma := by
  obtain ⟨a, ha⟩ := verticalDerivative_eq_affine
    (I := I) g u sigma hs
  have hu := potential_eq_slice_add_quadratic (I := I) u sigma a ha
  let s0 : Real := -2 * a / sigma
  let psi : C^∞⟮I, M; Real⟯ :=
    ⟨fun y : M => u (y, 0) - a ^ 2 / sigma,
      (u.contMDiff.comp (contMDiff_id.prodMk contMDiff_const)).sub contMDiff_const⟩
  let phi : C^∞⟮modelWithCornersSelf Real Real, Real; Real⟯ :=
    ⟨fun s : Real => (sigma / 4) * (s - s0) ^ 2,
      by rw [contMDiff_iff_contDiff]; fun_prop⟩
  refine ⟨s0, psi, ?_, ?_⟩
  · intro p
    rw [hu p]
    change u (p.1, 0) + (sigma / 4) * p.2 ^ 2 + a * p.2 =
      (u (p.1, 0) - a ^ 2 / sigma) +
        (sigma / 4) * (p.2 - (-2 * a / sigma)) ^ 2
    field_simp [ne_of_gt hsigma]
    ring
  · intro y v w
    have hcomponent := gradientRicciSoliton_prod_fst_component
      (I := I) (J := modelWithCornersSelf Real Real) hs (y, 0) v w
    have hsplit : (u : M × Real → Real) =
        fun p : M × Real => psi p.1 + phi p.2 := by
      funext p
      rw [hu p]
      change u (p.1, 0) + (sigma / 4) * p.2 ^ 2 + a * p.2 =
        (u (p.1, 0) - a ^ 2 / sigma) +
          (sigma / 4) * (p.2 - (-2 * a / sigma)) ^ 2
      field_simp [ne_of_gt hsigma]
      ring
    have hhess :
        hessFun (I := I.prod (modelWithCornersSelf Real Real))
            (g.prod (euclideanMetric (E := Real))) u (y, 0) (v, 0) (w, 0) =
          hessFun (I := I) g psi y v w := by
      rw [hsplit]
      rw [Operator.hessFun_prod]
      simp only [map_zero, add_zero]
    rw [hhess] at hcomponent
    exact hcomponent

set_option backward.isDefEq.respectTransparency false in
theorem roundThreeCylinderShrinkerPotential_hessian
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real)
    (u v : TangentSpace ((𝓡 2).prod 𝓘(Real, Real)) x) :
    hessFun (I := (𝓡 2).prod 𝓘(Real, Real)) roundThreeCylinderShrinkerMetric
      roundThreeCylinderShrinkerPotential x u v =
      (1 / 2 : Real) * inner Real u.2 v.2 := by
  let : Fact (Module.finrank Real (EuclideanSpace Real (Fin 3)) = 2 + 1) :=
    ⟨by simp⟩
  have hprod := Operator.hessFun_prod
    (I := 𝓡 2) (J := 𝓘(Real, Real))
    roundTwoSphereShrinkerMetric (euclideanMetric (E := Real))
    roundTwoSphereShrinkerPotential (gaussianPotential (E := Real)) x u v
  have hsphere (y : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1)
      (a b : TangentSpace (𝓡 2) y) :
      hessFun (I := 𝓡 2) roundTwoSphereShrinkerMetric
        roundTwoSphereShrinkerPotential y a b = 0 := by
    let : Fact (Module.finrank Real (EuclideanSpace Real (Fin 3)) = 2 + 1) := ⟨by simp⟩
    simpa [roundTwoSphereShrinkerMetric, roundTwoSphereShrinkerPotential,
      roundSphereShrinkerPotential] using
      (roundSphereShrinkerPotential_hessian
        (A := EuclideanSpace Real (Fin 3)) (n := 2) (by decide) y a b)
  calc
    hessFun (I := (𝓡 2).prod 𝓘(Real, Real)) roundThreeCylinderShrinkerMetric
        roundThreeCylinderShrinkerPotential x u v =
      hessFun (I := (𝓡 2).prod 𝓘(Real, Real))
        (roundTwoSphereShrinkerMetric.prod (euclideanMetric (E := Real)))
        (fun q : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real =>
          roundTwoSphereShrinkerPotential q.1 + gaussianPotential q.2) x u v := by
            rfl
    _ = hessFun (I := 𝓡 2) roundTwoSphereShrinkerMetric
          roundTwoSphereShrinkerPotential x.1 u.1 v.1 +
        hessFun (I := 𝓘(Real, Real)) (euclideanMetric (E := Real))
          (gaussianPotential (E := Real)) x.2 u.2 v.2 := hprod
    _ = (1 / 2 : Real) * inner Real u.2 v.2 := by
      rw [hsphere, gaussianPotential_hessian]
      simp

set_option backward.isDefEq.respectTransparency false in
theorem roundThreeCylinderShrinkerPotential_tangential_hessian
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real)
    (u v : TangentSpace ((𝓡 2).prod 𝓘(Real, Real)) x)
    (hu : u.2 = 0) (hv : v.2 = 0) :
    hessFun (I := (𝓡 2).prod 𝓘(Real, Real)) roundThreeCylinderShrinkerMetric
      roundThreeCylinderShrinkerPotential x u v = 0 := by
  rw [roundThreeCylinderShrinkerPotential_hessian, hu, hv]
  simp

set_option backward.isDefEq.respectTransparency false in
theorem roundThreeCylinderShrinkerPotential_mixed_hessian
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real)
    (u v : TangentSpace ((𝓡 2).prod 𝓘(Real, Real)) x)
    (hu : u.2 = 0) :
    hessFun (I := (𝓡 2).prod 𝓘(Real, Real)) roundThreeCylinderShrinkerMetric
    roundThreeCylinderShrinkerPotential x u v = 0 := by
  simpa [hu] using
    (roundThreeCylinderShrinkerPotential_hessian x u v)

set_option backward.isDefEq.respectTransparency false in
theorem roundThreeCylinderShrinkerPotential_line_hessian
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real)
    (u v : TangentSpace ((𝓡 2).prod 𝓘(Real, Real)) x) :
    hessFun (I := (𝓡 2).prod 𝓘(Real, Real)) roundThreeCylinderShrinkerMetric
      roundThreeCylinderShrinkerPotential x u v =
      (1 / 2 : Real) * inner Real u.2 v.2 :=
  roundThreeCylinderShrinkerPotential_hessian x u v

theorem roundThreeCylinderShrinkerPotential_line_restriction
    (y : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1) :
    (fun t : Real => roundThreeCylinderShrinkerPotential (y, t)) =
      (fun t : Real => 1 + t ^ 2 / 4) := by
  funext t
  exact roundThreeCylinderShrinkerPotential_apply (y, t)

end DifferentialGeometry.Geometry
