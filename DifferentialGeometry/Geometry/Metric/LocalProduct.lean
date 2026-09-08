import DifferentialGeometry.Geometry.Metric.Pullback.Immersion
import DifferentialGeometry.Geometry.Metric.Product
import DifferentialGeometry.Geometry.Metric.Euclidean
import DifferentialGeometry.Geometry.Metric.LocalPullback

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry

open Set TopologicalSpace
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
variable {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
variable {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
private def opensProdDiffeomorph (U : Opens M) (V : Opens N) :
    Diffeomorph (I.prod J) (I.prod J) (U × V)
      (⟨(U : Set M) ×ˢ (V : Set N), U.isOpen.prod V.isOpen⟩ : Opens (M × N)) ∞ where
  toFun p := ⟨(p.1.1, p.2.1), p.1.2, p.2.2⟩
  invFun p := (⟨p.1.1, p.2.1⟩, ⟨p.1.2, p.2.2⟩)
  left_inv _ := rfl
  right_inv _ := rfl
  contMDiff_toFun := by
    intro x
    let W : Opens (M × N) := ⟨(U : Set M) ×ˢ (V : Set N), U.isOpen.prod V.isOpen⟩
    have h : ContMDiffAt (I.prod J) (I.prod J) ∞
        (fun p : U × V => (⟨(p.1.1, p.2.1), p.1.2, p.2.2⟩ : W)) x :=
      codRestr_contMDiffAt (V := W) (f := fun p : U × V => (p.1.1, p.2.1))
        (fun p : U × V => ⟨p.1.2, p.2.2⟩)
        (((contMDiff_subtype_val.comp contMDiff_fst).prodMk
          (contMDiff_subtype_val.comp contMDiff_snd)).contMDiffAt)
    exact h
  contMDiff_invFun := by
    let W : Opens (M × N) := ⟨(U : Set M) ×ˢ (V : Set N), U.isOpen.prod V.isOpen⟩
    have hfst : ContMDiff (I.prod J) I ∞ (fun x : W => (⟨x.1.1, x.2.1⟩ : U)) := by
      intro x
      exact codRestr_contMDiffAt (fun y : W => y.2.1)
        ((contMDiff_fst.comp contMDiff_subtype_val).contMDiffAt)
    have hsnd : ContMDiff (I.prod J) J ∞ (fun x : W => (⟨x.1.2, x.2.2⟩ : V)) := by
      intro x
      exact codRestr_contMDiffAt (fun y : W => y.2.2)
        ((contMDiff_snd.comp contMDiff_subtype_val).contMDiffAt)
    exact hfst.prodMk hsnd

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [IsManifold I ∞ M] [IsManifold J ∞ N] in
private theorem isLocalDiffeomorph_opens_prod_partialDiffeomorph
    (U : Opens M) (V : Opens N)
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
    {P : Type*} [TopologicalSpace P] [ChartedSpace H' P]
    (phi : PartialDiffeomorph (I.prod J) I' (M × N) P ∞)
    (hsource : (U : Set M) ×ˢ (V : Set N) ⊆ phi.source) :
    IsLocalDiffeomorph (I.prod J) I' ∞ (fun x : U × V => phi (x.1.1, x.2.1)) := by
  let W : Opens (M × N) := ⟨(U : Set M) ×ˢ (V : Set N), U.isOpen.prod V.isOpen⟩
  have hphi : IsLocalDiffeomorph (I.prod J) I' ∞ (fun x : W => phi x.1) := by
    apply isLocalDiffeomorph_restrict_open
    intro x
    exact phi.isLocalDiffeomorphAt _ _ _ (hsource x.2)
  have h := isLocalDiffeomorph_comp hphi
    (opensProdDiffeomorph (I := I) (J := J) U V).isLocalDiffeomorph
  exact h

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [IsManifold I ∞ M] [IsManifold J ∞ N] in
private theorem mfderiv_opens_prod_partialDiffeomorph
    (K : Opens N) (O : Opens ℝ)
    (phi : PartialDiffeomorph (J.prod 𝓘(ℝ, ℝ)) I (N × ℝ) M ∞)
    (hsource : (K : Set N) ×ˢ (O : Set ℝ) ⊆ phi.source) (x : K × O) :
    mfderiv (J.prod 𝓘(ℝ, ℝ)) I
        (fun y : K × O => phi (y.1.1, y.2.1)) x =
      mfderiv (J.prod 𝓘(ℝ, ℝ)) I phi (x.1.1, x.2.1) := by
  let inc := Prod.map (Subtype.val : K → N) (Subtype.val : O → ℝ)
  have hinc : MDifferentiableAt (J.prod 𝓘(ℝ, ℝ)) (J.prod 𝓘(ℝ, ℝ)) inc x :=
    ((contMDiff_subtype_val.comp contMDiff_fst).prodMk
      (contMDiff_subtype_val.comp contMDiff_snd)).contMDiffAt.mdifferentiableAt (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have hder := mfderiv_comp x (phi.mdifferentiableAt (by decide : (∞ : WithTop ℕ∞) ≠ 0) (hsource ⟨x.1.2, x.2.2⟩)) hinc
  have hincder : mfderiv (J.prod 𝓘(ℝ, ℝ)) (J.prod 𝓘(ℝ, ℝ)) inc x =
      ContinuousLinearMap.id ℝ (F × ℝ) := by
    rw [mfderiv_prodMap
      ((contMDiff_subtype_val (I := J) (U := K)).contMDiffAt.mdifferentiableAt (by decide : (∞ : WithTop ℕ∞) ≠ 0))
      ((contMDiff_subtype_val (I := 𝓘(ℝ, ℝ)) (U := O)).contMDiffAt.mdifferentiableAt (by decide : (∞ : WithTop ℕ∞) ≠ 0)),
      mfderiv_subtype_val, mfderiv_subtype_val]
    rfl
  rw [hincder] at hder
  exact hder

omit [FiniteDimensional ℝ E] in
theorem exists_metric_prod_eq_localPullMetric_of_partialDiffeomorph [T2Space N]
    (g : SmoothRiemannianMetric I M) (K : Opens N) (O : Opens ℝ) (hO : 0 ∈ O)
    (phi : PartialDiffeomorph (J.prod 𝓘(ℝ, ℝ)) I (N × ℝ) M ∞)
    (hsource : (K : Set N) ×ˢ (O : Set ℝ) ⊆ phi.source)
    (hproduct : ∀ k ∈ K, ∀ t ∈ O, ∀ (u v : TangentSpace J k) (r q : ℝ),
      g.inner (phi (k, t))
        (mfderiv (J.prod 𝓘(ℝ, ℝ)) I phi (k, t) (u, r))
        (mfderiv (J.prod 𝓘(ℝ, ℝ)) I phi (k, t) (v, q)) =
      g.inner (phi (k, 0))
        (mfderiv J I (fun y : N => phi (y, 0)) k u)
        (mfderiv J I (fun y : N => phi (y, 0)) k v) + r * q) :
    ∃ (hPhi : IsLocalDiffeomorph (J.prod 𝓘(ℝ, ℝ)) I ∞
        (fun x : K × O => phi (x.1.1, x.2.1)))
      (h : SmoothRiemannianMetric J K),
      (∀ (k : K) (u v : TangentSpace J k), h.inner k u v =
        g.inner (phi (k.1, 0))
          (mfderiv J I (fun y : N => phi (y, 0)) k.1 u)
          (mfderiv J I (fun y : N => phi (y, 0)) k.1 v)) ∧
      localPullMetric g (fun x : K × O => phi (x.1.1, x.2.1)) hPhi =
        h.prod ((euclideanMetric (E := ℝ)).restrictOpen O) := by
  have hPhi := isLocalDiffeomorph_opens_prod_partialDiffeomorph K O phi hsource
  let Y : K → M := fun k => phi (k.1, 0)
  have hY : ContMDiff J I ∞ Y := by
    exact hPhi.contMDiff.comp (contMDiff_id.prodMk (contMDiff_const (c := (⟨0, hO⟩ : O))))
  have hraw (k : K) : MDifferentiableAt J I (fun y : N => phi (y, 0)) k.1 :=
    (phi.mdifferentiableAt (by decide : (∞ : WithTop ℕ∞) ≠ 0) (hsource ⟨k.2, hO⟩)).comp k.1
      (mdifferentiableAt_id.prodMk mdifferentiableAt_const)
  have hYder (k : K) : mfderiv J I Y k =
      mfderiv J I (fun y : N => phi (y, 0)) k.1 := by
    have hh := mfderiv_comp k (hraw k)
      ((contMDiff_subtype_val (I := J) (U := K)).contMDiffAt.mdifferentiableAt (by decide : (∞ : WithTop ℕ∞) ≠ 0))
    rw [mfderiv_subtype_val] at hh
    exact hh
  have hrawder (k : K) : mfderiv J I (fun y : N => phi (y, 0)) k.1 =
      (mfderiv (J.prod 𝓘(ℝ, ℝ)) I phi (k.1, 0)).comp
        (ContinuousLinearMap.inl ℝ F ℝ) := by
    have hh := mfderiv_comp k.1 (phi.mdifferentiableAt (by decide : (∞ : WithTop ℕ∞) ≠ 0) (hsource ⟨k.2, hO⟩))
      (mdifferentiableAt_id.prodMk mdifferentiableAt_const)
    change mfderiv J I (fun y : N => phi (y, 0)) k.1 =
      (mfderiv (J.prod 𝓘(ℝ, ℝ)) I phi (k.1, 0)).comp
        (mfderiv J (J.prod 𝓘(ℝ, ℝ)) (fun y : N => (y, (0 : ℝ))) k.1) at hh
    rw [mfderiv_prod_left] at hh
    exact hh
  have himm : ∀ k, Function.Injective (mfderiv J I Y k) := by
    intro k u v huv
    rw [hYder, hrawder] at huv
    have hlocal : IsLocalDiffeomorphAt (J.prod 𝓘(ℝ, ℝ)) I ∞ phi (k.1, 0) :=
      phi.isLocalDiffeomorphAt _ _ _ (hsource ⟨k.2, hO⟩)
    have hinj : Function.Injective (mfderiv (J.prod 𝓘(ℝ, ℝ)) I phi (k.1, 0)) := by
      rw [← hlocal.mfderivToContinuousLinearEquiv_coe (by decide)]
      exact (hlocal.mfderivToContinuousLinearEquiv (by decide)).injective
    have hh := hinj huv
    exact congrArg Prod.fst hh
  let h : SmoothRiemannianMetric J K := g.pullback Y hY himm
  have hinner (k : K) (u v : TangentSpace J k) : h.inner k u v =
      g.inner (phi (k.1, 0))
        (mfderiv J I (fun y : N => phi (y, 0)) k.1 u)
        (mfderiv J I (fun y : N => phi (y, 0)) k.1 v) := by
    rw [SmoothRiemannianMetric.pullback_inner, hYder]
    rfl
  refine ⟨hPhi, h, hinner, ?_⟩
  apply SmoothRiemannianMetric.ext_inner
  intro x u v
  rw [localPullMetric_inner]
  have hd := mfderiv_opens_prod_partialDiffeomorph K O phi hsource x
  change (show F × ℝ →L[ℝ] TangentSpace I (phi (x.1.1, x.2.1)) from
    mfderiv (J.prod 𝓘(ℝ, ℝ)) I (fun y : K × O => phi (y.1.1, y.2.1)) x) =
      (show F × ℝ →L[ℝ] TangentSpace I (phi (x.1.1, x.2.1)) from
        mfderiv (J.prod 𝓘(ℝ, ℝ)) I phi (x.1.1, x.2.1)) at hd
  have hlhs : g.inner (phi (x.1.1, x.2.1))
      (mfderiv (J.prod 𝓘(ℝ, ℝ)) I (fun y : K × O => phi (y.1.1, y.2.1)) x u)
      (mfderiv (J.prod 𝓘(ℝ, ℝ)) I (fun y : K × O => phi (y.1.1, y.2.1)) x v) =
    g.inner (phi (x.1.1, x.2.1))
      (mfderiv (J.prod 𝓘(ℝ, ℝ)) I phi (x.1.1, x.2.1) (u.1, u.2))
      (mfderiv (J.prod 𝓘(ℝ, ℝ)) I phi (x.1.1, x.2.1) (v.1, v.2)) := by
    exact congrArg₂ (fun a b => g.inner (phi (x.1.1, x.2.1)) a b)
      (congrArg (fun L : F × ℝ →L[ℝ] TangentSpace I (phi (x.1.1, x.2.1)) => L u) hd)
      (congrArg (fun L : F × ℝ →L[ℝ] TangentSpace I (phi (x.1.1, x.2.1)) => L v) hd)
  rw [hlhs, hproduct x.1.1 x.1.2 x.2.1 x.2.2 u.1 v.1 u.2 v.2]
  rw [SmoothRiemannianMetric.prod_inner, mfderiv_fst, mfderiv_snd]
  have hreal : ((euclideanMetric (E := ℝ)).restrictOpen O).inner x.2 u.2 v.2 = u.2 * v.2 := by
    change inner ℝ (u.2 : ℝ) (v.2 : ℝ) = u.2 * v.2
    simp only [RCLike.inner_apply, conj_trivial]
    ring
  change _ = h.inner x.1 u.1 v.1 + ((euclideanMetric (E := ℝ)).restrictOpen O).inner x.2 u.2 v.2
  exact congrArg₂ (fun a b : ℝ => a + b) (hinner x.1 u.1 v.1).symm hreal.symm

end DifferentialGeometry
