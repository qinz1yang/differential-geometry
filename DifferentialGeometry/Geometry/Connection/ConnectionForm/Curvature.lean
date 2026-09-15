import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

noncomputable section

open Filter
open scoped Topology ContDiff

namespace DifferentialGeometry.Geometry.Connection

variable {V E W : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

def connectionFormCovDeriv (A : V → V →L[ℝ] E →L[ℝ] E)
    (s : V → E) (X : V) (x : V) : E :=
  fderiv ℝ s x X + A x X (s x)

def connectionFormCurvature (A : V → V →L[ℝ] E →L[ℝ] E)
    (x : V) (X Y : V) (u : E) : E :=
  fderiv ℝ A x X Y u - fderiv ℝ A x Y X u +
    A x X (A x Y u) - A x Y (A x X u)

private theorem fderiv_apply_const {F G : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {L : V → F →L[ℝ] G} {x : V} (hL : DifferentiableAt ℝ L x)
    (u : F) (X : V) :
    fderiv ℝ (fun y => L y u) x X = fderiv ℝ L x X u := by
  have h := (hL.hasFDerivAt.clm_apply (hasFDerivAt_const u x)).fderiv
  rw [h]
  simp

private theorem connectionFormCovDeriv_iterated
    {A : V → V →L[ℝ] E →L[ℝ] E} {s : V → E} {x : V}
    (hA : DifferentiableAt ℝ A x) (hs : ContDiffAt ℝ 2 s x) (X Y : V) :
    connectionFormCovDeriv A (connectionFormCovDeriv A s Y) X x =
      fderiv ℝ (fderiv ℝ s) x X Y +
        fderiv ℝ A x X Y (s x) + A x Y (fderiv ℝ s x X) +
        A x X (fderiv ℝ s x Y + A x Y (s x)) := by
  have hds : DifferentiableAt ℝ (fderiv ℝ s) x :=
    (hs.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hAs : DifferentiableAt ℝ (fun y => A y Y (s y)) x :=
    (hA.clm_apply (differentiableAt_const Y)).clm_apply
      (hs.differentiableAt (by norm_num))
  have hAderiv := ((hA.hasFDerivAt.clm_apply (hasFDerivAt_const Y x)).clm_apply
    (hs.differentiableAt (by norm_num)).hasFDerivAt).fderiv
  unfold connectionFormCovDeriv
  rw [fderiv_fun_add (hds.clm_apply (differentiableAt_const Y)) hAs,
    add_apply, fderiv_apply_const hds Y X, hAderiv]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, zero_apply, map_zero]
  abel_nf

theorem connectionFormCovDeriv_commutator
    {A : V → V →L[ℝ] E →L[ℝ] E} {s : V → E} {x : V}
    (hA : DifferentiableAt ℝ A x) (hs : ContDiffAt ℝ 2 s x) (X Y : V) :
    connectionFormCovDeriv A (connectionFormCovDeriv A s Y) X x -
      connectionFormCovDeriv A (connectionFormCovDeriv A s X) Y x =
        connectionFormCurvature A x X Y (s x) := by
  rw [connectionFormCovDeriv_iterated hA hs X Y,
    connectionFormCovDeriv_iterated hA hs Y X,
    (hs.isSymmSndFDerivAt (by norm_num)).eq X Y]
  simp only [connectionFormCurvature, map_add]
  abel_nf

end DifferentialGeometry.Geometry.Connection

namespace DifferentialGeometry.Geometry.Connection

variable {V E W : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

def bundleMapCovDeriv (A : V → V →L[ℝ] E →L[ℝ] E)
    (C : V → V →L[ℝ] W →L[ℝ] W) (J : V → E →L[ℝ] W)
    (x : V) (X : V) (u : E) : W :=
  fderiv ℝ J x X u + C x X (J x u) - J x (A x X u)

private theorem connectionFormCovDeriv_inner
    {C : V → V →L[ℝ] W →L[ℝ] W} {G : V → W →L[ℝ] W →L[ℝ] ℝ}
    {s t : V → W} {x : V} (hG : DifferentiableAt ℝ G x)
    (hs : DifferentiableAt ℝ s x) (ht : DifferentiableAt ℝ t x) (X : V)
    (hcompat : ∀ u v, fderiv ℝ G x X u v =
      G x (C x X u) v + G x u (C x X v)) :
    fderiv ℝ (fun y => G y (s y) (t y)) x X =
      G x (connectionFormCovDeriv C s X x) (t x) +
        G x (s x) (connectionFormCovDeriv C t X x) := by
  rw [((hG.hasFDerivAt.clm_apply hs.hasFDerivAt).clm_apply ht.hasFDerivAt).fderiv]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, hcompat, connectionFormCovDeriv, map_add]
  ring

theorem connectionFormCovDeriv_inner_eq_neg_of_orthogonal
    {C : V → V →L[ℝ] W →L[ℝ] W} {G : V → W →L[ℝ] W →L[ℝ] ℝ}
    {s t : V → W} {x : V} (hG : DifferentiableAt ℝ G x)
    (hs : DifferentiableAt ℝ s x) (ht : DifferentiableAt ℝ t x) (X : V)
    (hcompat : ∀ u v, fderiv ℝ G x X u v =
      G x (C x X u) v + G x u (C x X v))
    (horth : ∀ᶠ y in 𝓝 x, G y (s y) (t y) = 0) :
    G x (connectionFormCovDeriv C s X x) (t x) =
      -G x (s x) (connectionFormCovDeriv C t X x) := by
  have hd := connectionFormCovDeriv_inner hG hs ht X hcompat
  have hz : fderiv ℝ (fun y => G y (s y) (t y)) x = 0 :=
    (show (fun y => G y (s y) (t y)) =ᶠ[𝓝 x] (fun _ => 0) from horth).fderiv_eq.trans
      (fderiv_const_apply (0 : ℝ))
  rw [hz, zero_apply] at hd
  linarith only [hd]

private theorem bundleMapCovDeriv_differentiableAt
    {A : V → V →L[ℝ] E →L[ℝ] E} {C : V → V →L[ℝ] W →L[ℝ] W}
    {J : V → E →L[ℝ] W} {x : V}
    (hA : DifferentiableAt ℝ A x) (hC : DifferentiableAt ℝ C x)
    (hJ : ContDiffAt ℝ 2 J x) (X : V) (u : E) :
    DifferentiableAt ℝ (fun y => bundleMapCovDeriv A C J y X u) x := by
  have hJ' := hJ.differentiableAt (by norm_num)
  have hdJ := (hJ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  exact (((hdJ.clm_apply (differentiableAt_const X)).clm_apply
    (differentiableAt_const u)).add
    ((hC.clm_apply (differentiableAt_const X)).clm_apply
      (hJ'.clm_apply (differentiableAt_const u)))).sub
        (hJ'.clm_apply ((hA.clm_apply (differentiableAt_const X)).clm_apply
          (differentiableAt_const u)))

private theorem fderiv_bundleMapCovDeriv
    {A : V → V →L[ℝ] E →L[ℝ] E} {C : V → V →L[ℝ] W →L[ℝ] W}
    {J : V → E →L[ℝ] W} {x : V}
    (hA : DifferentiableAt ℝ A x) (hC : DifferentiableAt ℝ C x)
    (hJ : ContDiffAt ℝ 2 J x) (X Y : V) (u : E) :
    fderiv ℝ (fun y => bundleMapCovDeriv A C J y Y u) x X =
      fderiv ℝ (fderiv ℝ J) x X Y u +
        fderiv ℝ C x X Y (J x u) + C x Y (fderiv ℝ J x X u) -
        (fderiv ℝ J x X (A x Y u) + J x (fderiv ℝ A x X Y u)) := by
  have hJ' := hJ.differentiableAt (by norm_num)
  have hdJ := (hJ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hCJ := ((hC.hasFDerivAt.clm_apply (hasFDerivAt_const Y x)).clm_apply
    (hJ'.hasFDerivAt.clm_apply (hasFDerivAt_const u x)))
  have hJA := hJ'.hasFDerivAt.clm_apply
    ((hA.hasFDerivAt.clm_apply (hasFDerivAt_const Y x)).clm_apply
      (hasFDerivAt_const u x))
  have hdJJ := (hdJ.hasFDerivAt.clm_apply (hasFDerivAt_const Y x)).clm_apply
    (hasFDerivAt_const u x)
  rw [show (fun y => bundleMapCovDeriv A C J y Y u) =
    (fun y => fderiv ℝ J y Y u + C y Y (J y u) - J y (A y Y u)) from rfl,
    ((hdJJ.fun_add hCJ).fun_sub hJA).fderiv]
  simp only [sub_apply, add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    zero_apply, map_zero]
  abel_nf

private theorem bundleMapCovDeriv_curvature
    {A : V → V →L[ℝ] E →L[ℝ] E} {C : V → V →L[ℝ] W →L[ℝ] W}
    {J : V → E →L[ℝ] W} {x : V}
    (hA : DifferentiableAt ℝ A x) (hC : DifferentiableAt ℝ C x)
    (hJ : ContDiffAt ℝ 2 J x) (X Y : V) (u : E) :
    connectionFormCurvature C x X Y (J x u) =
      J x (connectionFormCurvature A x X Y u) +
        bundleMapCovDeriv A C J x X (A x Y u) -
        bundleMapCovDeriv A C J x Y (A x X u) +
        connectionFormCovDeriv C (fun y => bundleMapCovDeriv A C J y Y u) X x -
        connectionFormCovDeriv C (fun y => bundleMapCovDeriv A C J y X u) Y x := by
  simp only [connectionFormCovDeriv]
  rw [fderiv_bundleMapCovDeriv hA hC hJ X Y u, fderiv_bundleMapCovDeriv hA hC hJ Y X u]
  simp only [bundleMapCovDeriv, connectionFormCurvature, map_add, map_sub]
  rw [(hJ.isSymmSndFDerivAt (by norm_num)).eq X Y]
  abel_nf

theorem gauss_equation_connection_forms
    {A : V → V →L[ℝ] E →L[ℝ] E} {C : V → V →L[ℝ] W →L[ℝ] W}
    {J : V → E →L[ℝ] W} {G : V → W →L[ℝ] W →L[ℝ] ℝ} {x : V}
    (hA : DifferentiableAt ℝ A x) (hC : DifferentiableAt ℝ C x)
    (hJ : ContDiffAt ℝ 2 J x) (hG : DifferentiableAt ℝ G x)
    (hsymm : ∀ u v, G x u v = G x v u)
    (hcompat : ∀ X u v, fderiv ℝ G x X u v =
      G x (C x X u) v + G x u (C x X v))
    (horth : ∀ᶠ y in 𝓝 x, ∀ X u v,
      G y (bundleMapCovDeriv A C J y X u) (J y v) = 0)
    (X Y : V) (u v : E) :
    G x (J x (connectionFormCurvature A x X Y u)) (J x v) =
      G x (connectionFormCurvature C x X Y (J x u)) (J x v) +
        G x (bundleMapCovDeriv A C J x X v) (bundleMapCovDeriv A C J x Y u) -
        G x (bundleMapCovDeriv A C J x X u) (bundleMapCovDeriv A C J x Y v) := by
  have ho := horth.self_of_nhds
  have hJ' := hJ.differentiableAt (by norm_num)
  have hD (a b : V) :
      G x (connectionFormCovDeriv C (fun y => bundleMapCovDeriv A C J y b u) a x)
        (J x v) =
      -G x (bundleMapCovDeriv A C J x b u) (bundleMapCovDeriv A C J x a v) := by
    have hd := connectionFormCovDeriv_inner_eq_neg_of_orthogonal hG
      (bundleMapCovDeriv_differentiableAt hA hC hJ b u)
      (hJ'.clm_apply (differentiableAt_const v)) a (hcompat a)
      (horth.mono fun y hy => hy b u v)
    have hsplit : connectionFormCovDeriv C (fun y => J y v) a x =
        bundleMapCovDeriv A C J x a v + J x (A x a v) := by
      rw [connectionFormCovDeriv, fderiv_apply_const hJ' v a, bundleMapCovDeriv]
      abel_nf
    rw [hsplit, map_add, ho, add_zero] at hd
    exact hd
  have hc := congrArg (fun w => G x w (J x v))
    (bundleMapCovDeriv_curvature hA hC hJ X Y u)
  simp only [map_add, map_sub, add_apply,
    sub_apply, ho, add_zero, sub_zero, hD] at hc
  rw [hsymm (bundleMapCovDeriv A C J x Y u) (bundleMapCovDeriv A C J x X v)] at hc
  linarith only [hc]

end DifferentialGeometry.Geometry.Connection

namespace DifferentialGeometry.Geometry.Connection

variable {V E W : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

def pullbackConnectionForm (C : E → E →L[ℝ] W →L[ℝ] W) (F : V → E)
    (x : V) : V →L[ℝ] W →L[ℝ] W :=
  (C (F x)).comp (fderiv ℝ F x)

private theorem fderiv_pullbackConnectionForm
    {C : E → E →L[ℝ] W →L[ℝ] W} {F : V → E} {x : V}
    (hC : DifferentiableAt ℝ C (F x)) (hF : ContDiffAt ℝ 2 F x)
    (X Y : V) (u : W) :
    fderiv ℝ (pullbackConnectionForm C F) x X Y u =
      fderiv ℝ C (F x) (fderiv ℝ F x X) (fderiv ℝ F x Y) u +
        C (F x) (fderiv ℝ (fderiv ℝ F) x X Y) u := by
  have hF' := hF.differentiableAt (by norm_num)
  have hdF := (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hc := (hC.hasFDerivAt.comp x hF'.hasFDerivAt).clm_comp hdF.hasFDerivAt
  simp only [Function.comp_apply] at hc
  rw [show pullbackConnectionForm C F =
    (fun y => (C (F y)).comp (fderiv ℝ F y)) from rfl, hc.fderiv]
  simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.compL_apply]
  abel_nf

theorem connectionFormCurvature_pullback
    {C : E → E →L[ℝ] W →L[ℝ] W} {F : V → E} {x : V}
    (hC : DifferentiableAt ℝ C (F x)) (hF : ContDiffAt ℝ 2 F x)
    (X Y : V) (u : W) :
    connectionFormCurvature (pullbackConnectionForm C F) x X Y u =
      connectionFormCurvature C (F x) (fderiv ℝ F x X) (fderiv ℝ F x Y) u := by
  rw [connectionFormCurvature,
    fderiv_pullbackConnectionForm hC hF X Y u,
    fderiv_pullbackConnectionForm hC hF Y X u,
    (hF.isSymmSndFDerivAt (by norm_num)).eq X Y]
  simp only [pullbackConnectionForm, ContinuousLinearMap.comp_apply, connectionFormCurvature]
  abel_nf

end DifferentialGeometry.Geometry.Connection

namespace DifferentialGeometry.Geometry.Connection

variable {V W : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

private theorem bundleMapCovDeriv_pair_sum
    {A : V → V →L[ℝ] V →L[ℝ] V} {C : V → V →L[ℝ] W →L[ℝ] W}
    {J : V → V →L[ℝ] W} {G : V → W →L[ℝ] W →L[ℝ] ℝ}
    {H : V → V →L[ℝ] V →L[ℝ] ℝ} {x : V}
    (hJ : DifferentiableAt ℝ J x) (hG : DifferentiableAt ℝ G x)
    (hH : DifferentiableAt ℝ H x)
    (hcompatG : ∀ X u v, fderiv ℝ G x X u v =
      G x (C x X u) v + G x u (C x X v))
    (hcompatH : ∀ X Y Z, fderiv ℝ H x X Y Z =
      H x (A x X Y) Z + H x Y (A x X Z))
    (hmetric : ∀ᶠ y in 𝓝 x, ∀ u v, G y (J y u) (J y v) = H y u v)
    (X Y Z : V) :
    G x (bundleMapCovDeriv A C J x X Y) (J x Z) +
      G x (J x Y) (bundleMapCovDeriv A C J x X Z) = 0 := by
  have hdG := connectionFormCovDeriv_inner hG
    (hJ.clm_apply (differentiableAt_const Y))
    (hJ.clm_apply (differentiableAt_const Z)) X (hcompatG X)
  have he : (fun y => G y (J y Y) (J y Z)) =ᶠ[𝓝 x] (fun y => H y Y Z) :=
    hmetric.mono fun y hy => hy Y Z
  have hdH : fderiv ℝ (fun y => H y Y Z) x X = fderiv ℝ H x X Y Z := by
    rw [fderiv_apply_const (hH.clm_apply (differentiableAt_const Y)) Z X]
    rw [fderiv_apply_const hH Y X]
  have hsplit (u : V) : connectionFormCovDeriv C (fun y => J y u) X x =
      bundleMapCovDeriv A C J x X u + J x (A x X u) := by
    rw [connectionFormCovDeriv, fderiv_apply_const hJ u X, bundleMapCovDeriv]
    abel_nf
  rw [he.fderiv_eq, hdH, hcompatH, hsplit, hsplit] at hdG
  simp only [map_add, add_apply, hmetric.self_of_nhds] at hdG
  linarith only [hdG]

theorem bundleMapCovDeriv_orthogonal_of_symmetric
    {A : V → V →L[ℝ] V →L[ℝ] V} {C : V → V →L[ℝ] W →L[ℝ] W}
    {J : V → V →L[ℝ] W} {G : V → W →L[ℝ] W →L[ℝ] ℝ}
    {H : V → V →L[ℝ] V →L[ℝ] ℝ} {x : V}
    (hJ : DifferentiableAt ℝ J x) (hG : DifferentiableAt ℝ G x)
    (hH : DifferentiableAt ℝ H x)
    (hsymmG : ∀ u v, G x u v = G x v u)
    (hcompatG : ∀ X u v, fderiv ℝ G x X u v =
      G x (C x X u) v + G x u (C x X v))
    (hcompatH : ∀ X Y Z, fderiv ℝ H x X Y Z =
      H x (A x X Y) Z + H x Y (A x X Z))
    (hmetric : ∀ᶠ y in 𝓝 x, ∀ u v, G y (J y u) (J y v) = H y u v)
    (hsymm : ∀ X Y, bundleMapCovDeriv A C J x X Y = bundleMapCovDeriv A C J x Y X)
    (X Y Z : V) : G x (bundleMapCovDeriv A C J x X Y) (J x Z) = 0 := by
  have h1 := bundleMapCovDeriv_pair_sum hJ hG hH hcompatG hcompatH hmetric X Y Z
  have h2 := bundleMapCovDeriv_pair_sum hJ hG hH hcompatG hcompatH hmetric Y X Z
  have h3 := bundleMapCovDeriv_pair_sum hJ hG hH hcompatG hcompatH hmetric Z X Y
  rw [hsymmG (J x Y)] at h1
  rw [hsymm Y X, hsymmG (J x X)] at h2
  rw [hsymm Z X, hsymm Z Y, hsymmG (J x X)] at h3
  linarith only [h1, h2, h3]

theorem bundleMapCovDeriv_fderiv_symmetric
    {A : V → V →L[ℝ] V →L[ℝ] V} {C : W → W →L[ℝ] W →L[ℝ] W}
    {F : V → W} {x : V} (hF : ContDiffAt ℝ 2 F x)
    (hA : ∀ X Y, A x X Y = A x Y X)
    (hC : ∀ u v, C (F x) u v = C (F x) v u) (X Y : V) :
    bundleMapCovDeriv A (pullbackConnectionForm C F) (fderiv ℝ F) x X Y =
      bundleMapCovDeriv A (pullbackConnectionForm C F) (fderiv ℝ F) x Y X := by
  simp only [bundleMapCovDeriv, pullbackConnectionForm, ContinuousLinearMap.comp_apply]
  rw [(hF.isSymmSndFDerivAt (by norm_num)).eq X Y, hA X Y,
    hC (fderiv ℝ F x X) (fderiv ℝ F x Y)]

end DifferentialGeometry.Geometry.Connection
