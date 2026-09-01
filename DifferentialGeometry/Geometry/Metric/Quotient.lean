import DifferentialGeometry.Geometry.Metric.LocalPullback
import DifferentialGeometry.Geometry.Metric.SmoothMetricFromCoeff
import DifferentialGeometry.Geometry.Metric.BumpExtend
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorphOpens

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry

open Bundle Manifold Set TopologicalSpace
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
variable {N : Type*} [TopologicalSpace N] [ChartedSpace H N]
  [IsManifold I ∞ N]

private theorem infty_ne_zero : (∞ : WithTop ℕ∞) ≠ 0 := by decide

noncomputable def localPushInner
    (g : SmoothRiemannianMetric I M) (f : M → N)
    (hf : IsLocalDiffeomorph I I ∞ f) (x : M) :
    TangentSpace I (f x) →L[Real] TangentSpace I (f x) →L[Real] Real :=
  let D : TangentSpace I (f x) →L[Real] TangentSpace I x :=
    (hf.mfderivToContinuousLinearEquiv infty_ne_zero x).symm
  (ContinuousLinearMap.precomp Real D).comp ((g.inner x).comp D)

omit [FiniteDimensional Real E] [IsManifold I ∞ N] in
theorem localPushInner_apply
    (g : SmoothRiemannianMetric I M) (f : M → N)
    (hf : IsLocalDiffeomorph I I ∞ f) (x : M)
    (v w : TangentSpace I (f x)) :
    localPushInner g f hf x v w =
      g.inner x
        ((hf.mfderivToContinuousLinearEquiv infty_ne_zero x).symm v)
        ((hf.mfderivToContinuousLinearEquiv infty_ne_zero x).symm w) := by
  simp only [localPushInner, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.precomp_apply]
  rfl

omit [FiniteDimensional Real E] [IsManifold I ∞ N] in
private theorem cast_bilinear_symm
    {x y : N} (hxy : x = y)
    (b : TangentSpace I x →L[Real] TangentSpace I x →L[Real] Real)
    (hb : ∀ v w, b v w = b w v) (v w : TangentSpace I y) :
    (hxy ▸ b) v w = (hxy ▸ b) w v := by
  cases hxy
  exact hb v w

omit [FiniteDimensional Real E] [IsManifold I ∞ N] in
private theorem cast_bilinear_pos
    {x y : N} (hxy : x = y)
    (b : TangentSpace I x →L[Real] TangentSpace I x →L[Real] Real)
    (hb : ∀ v, v ≠ 0 → 0 < b v v) (v : TangentSpace I y) (hv : v ≠ 0) :
    0 < (hxy ▸ b) v v := by
  cases hxy
  exact hb v hv

omit [FiniteDimensional Real E] [IsManifold I ∞ N] in
private theorem cast_continuousLinearEquiv_apply
    {V : Type*} [TopologicalSpace V] [AddCommGroup V] [Module Real V]
    {x y : N} (hxy : x = y)
    (e : V ≃L[Real] TangentSpace I x) (v : V) :
    (hxy ▸ e) v = hxy ▸ e v := by
  cases hxy
  rfl

omit [FiniteDimensional Real E] [IsManifold I ∞ N] in
private theorem cast_tangent_eq_of_heq
    {x y : N} (hxy : x = y)
    (v : TangentSpace I x) (w : TangentSpace I y)
    (hvw : HEq v w) : hxy ▸ v = w := by
  cases hxy
  exact eq_of_heq hvw

def metricFiberCompatible
    (g : SmoothRiemannianMetric I M) (f : M → N)
    (hf : IsLocalDiffeomorph I I ∞ f) : Prop :=
  ∀ (x y : M) (hxy : f x = f y),
    hxy ▸ localPushInner g f hf x = localPushInner g f hf y

private noncomputable def chosenPreimage
    {f : M → N} (hsurj : Function.Surjective f) (y : N) : M :=
  Classical.choose (hsurj y)

omit [TopologicalSpace M] [TopologicalSpace N] in
private theorem chosenPreimage_spec
    {f : M → N} (hsurj : Function.Surjective f) (y : N) :
    f (chosenPreimage hsurj y) = y :=
  Classical.choose_spec (hsurj y)

private noncomputable def descendedInner
    (g : SmoothRiemannianMetric I M) (f : M → N)
    (hf : IsLocalDiffeomorph I I ∞ f)
    (hsurj : Function.Surjective f) (y : N) :
    TangentSpace I y →L[Real] TangentSpace I y →L[Real] Real :=
  chosenPreimage_spec hsurj y ▸
    localPushInner g f hf (chosenPreimage hsurj y)

omit [FiniteDimensional Real E] [IsManifold I ∞ N] in
private theorem descendedInner_eq_localPushInner
    (g : SmoothRiemannianMetric I M) (f : M → N)
    (hf : IsLocalDiffeomorph I I ∞ f)
    (hsurj : Function.Surjective f)
    (hcompat : metricFiberCompatible g f hf) (x : M) :
    descendedInner g f hf hsurj (f x) = localPushInner g f hf x := by
  exact hcompat (chosenPreimage hsurj (f x)) x
    (chosenPreimage_spec hsurj (f x))

omit [FiniteDimensional Real E] [IsManifold I ∞ N] in
private theorem descendedInner_eq_localPushInner_of_eq
    (g : SmoothRiemannianMetric I M) (f : M → N)
    (hf : IsLocalDiffeomorph I I ∞ f)
    (hsurj : Function.Surjective f)
    (hcompat : metricFiberCompatible g f hf)
    (x : M) (y : N) (hxy : f x = y) :
    descendedInner g f hf hsurj y = hxy ▸ localPushInner g f hf x := by
  cases hxy
  exact descendedInner_eq_localPushInner g f hf hsurj hcompat x

omit [FiniteDimensional Real E] [IsManifold I ∞ N] in
private theorem cast_localPushInner_apply
    (g : SmoothRiemannianMetric I M) (f : M → N)
    (hf : IsLocalDiffeomorph I I ∞ f)
    (x : M) (y : N) (hxy : f x = y)
    (v w : TangentSpace I y) :
    (hxy ▸ localPushInner g f hf x) v w =
      g.inner x
        ((hxy ▸ hf.mfderivToContinuousLinearEquiv infty_ne_zero x).symm v)
        ((hxy ▸ hf.mfderivToContinuousLinearEquiv infty_ne_zero x).symm w) := by
  cases hxy
  exact localPushInner_apply g f hf x v w

omit [IsManifold I ∞ N] in
theorem localPushInner_eq_of_fiber_preserving_isometry
    [T2Space M]
    (g : SmoothRiemannianMetric I M) (f : M → N)
    (hf : IsLocalDiffeomorph I I ∞ f)
    (Phi : M ≃ₘ⟮I, I⟯ M)
    (hcomp : f ∘ (Phi : M → M) = f)
    (hmetric : Diffeomorph.pullbackMetric g Phi = g)
    (x : M) :
    congrFun hcomp x ▸ localPushInner g f hf (Phi x) =
      localPushInner g f hf x := by
  let hmap : f (Phi x) = f x := congrFun hcomp x
  let A : TangentSpace I (Phi x) ≃L[Real] TangentSpace I (f x) :=
    hmap ▸ hf.mfderivToContinuousLinearEquiv infty_ne_zero (Phi x)
  let B : TangentSpace I x ≃L[Real] TangentSpace I (f x) :=
    hf.mfderivToContinuousLinearEquiv infty_ne_zero x
  let C : TangentSpace I x ≃L[Real] TangentSpace I (Phi x) :=
    Phi.mfderivToContinuousLinearEquiv infty_ne_zero x
  have hchain := mfderiv_comp x
    (hf.contMDiff.mdifferentiableAt infty_ne_zero)
    (Phi.contMDiff.mdifferentiableAt infty_ne_zero)
  rw [hcomp] at hchain
  have hAC (u : TangentSpace I x) : A (C u) = B u := by
    have hu := ContinuousLinearMap.ext_iff.mp hchain u
    change A (C u) = B u
    dsimp only [A, B, C]
    rw [cast_continuousLinearEquiv_apply]
    change hmap ▸ mfderiv I I f (Phi x) (mfderiv I I Phi x u) =
      mfderiv I I f x u
    exact cast_tangent_eq_of_heq hmap _ _ (heq_of_eq hu.symm)
  have hinv (v : TangentSpace I (f x)) : A.symm v = C (B.symm v) := by
    apply A.injective
    rw [A.apply_symm_apply, hAC, B.apply_symm_apply]
  have hisometry (u z : TangentSpace I x) :
      g.inner (Phi x) (C u) (C z) = g.inner x u z := by
    have h := Diffeomorph.pullbackMetric_inner g Phi x u z
    rw [hmetric] at h
    change g.inner (Phi x) (mfderiv I I Phi x u)
      (mfderiv I I Phi x z) = g.inner x u z
    exact h.symm
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  rw [cast_localPushInner_apply, localPushInner_apply]
  change g.inner (Phi x) (A.symm v) (A.symm w) =
    g.inner x (B.symm v) (B.symm w)
  rw [hinv, hinv]
  exact hisometry (B.symm v) (B.symm w)

omit [FiniteDimensional Real E] [IsManifold I ∞ N] in
private theorem descendedInner_symm
    (g : SmoothRiemannianMetric I M) (f : M → N)
    (hf : IsLocalDiffeomorph I I ∞ f)
    (hsurj : Function.Surjective f) (y : N)
    (v w : TangentSpace I y) :
    descendedInner g f hf hsurj y v w =
      descendedInner g f hf hsurj y w v := by
  let x := chosenPreimage hsurj y
  let hxy : f x = y := chosenPreimage_spec hsurj y
  change (hxy ▸ localPushInner g f hf x) v w =
    (hxy ▸ localPushInner g f hf x) w v
  apply cast_bilinear_symm hxy
  intro a b
  rw [localPushInner_apply, localPushInner_apply]
  exact g.symm x _ _

omit [FiniteDimensional Real E] [IsManifold I ∞ N] in
private theorem descendedInner_pos
    (g : SmoothRiemannianMetric I M) (f : M → N)
    (hf : IsLocalDiffeomorph I I ∞ f)
    (hsurj : Function.Surjective f) (y : N)
    (v : TangentSpace I y) (hv : v ≠ 0) :
    0 < descendedInner g f hf hsurj y v v := by
  let x := chosenPreimage hsurj y
  let hxy : f x = y := chosenPreimage_spec hsurj y
  change 0 < (hxy ▸ localPushInner g f hf x) v v
  apply cast_bilinear_pos hxy _ _ v hv
  intro a ha
  rw [localPushInner_apply]
  apply g.pos
  exact (hf.mfderivToContinuousLinearEquiv infty_ne_zero x).symm.map_ne_zero_iff.mpr ha

private noncomputable def tangentOpenEquiv
    (U : Opens N) (x : U) :
    TangentSpace I (x : N) ≃L[Real] TangentSpace I x :=
  (tangentSpaceModelContinuousLinearEquiv (I := I) (x : N)).trans
    (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm

omit [FiniteDimensional Real E] [IsManifold I ∞ N] in
private theorem mfderiv_subtype_val_tangentOpenEquiv
    (U : Opens N) (x : U) (v : TangentSpace I (x : N)) :
    mfderiv I I (Subtype.val : U → N) x (tangentOpenEquiv U x v) = v := by
  rw [mfderiv_subtype_val_apply]
  apply (tangentSpaceModelContinuousLinearEquiv (I := I) (x : N)).injective
  change tangentSpaceModelContinuousLinearEquiv (I := I) (x : N)
      ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm
        (tangentSpaceModelContinuousLinearEquiv (I := I) (x : N) v)) =
    tangentSpaceModelContinuousLinearEquiv (I := I) (x : N) v
  rw [tangentSpaceModelContinuousLinearEquiv_symm_apply]
  exact tangentSpaceModelContinuousLinearEquiv_apply (I := I) (x : N) v

private structure LocalSection
    (I : ModelWithCorners Real E H)
    (f : M → N) (y : N) where
  U : Opens N
  V : Opens M
  s : U ≃ₘ⟮I, I⟯ V
  mem : y ∈ U
  isSec : ∀ z : U, f ((s z : V) : M) = (z : N)

private noncomputable def LocalSection.ofLocal
    (f : M → N) (hf : IsLocalDiffeomorph I I ∞ f)
    (hsurj : Function.Surjective f) (y : N) : LocalSection I f y := by
  let x := chosenPreimage hsurj y
  have hxy : f x = y := chosenPreimage_spec hsurj y
  let Phi := Classical.choose (hf x)
  have hx : x ∈ Phi.source := (Classical.choose_spec (hf x)).1
  have hPhi : Set.EqOn f Phi Phi.source := (Classical.choose_spec (hf x)).2
  let V : Opens M := ⟨Phi.source, Phi.open_source⟩
  let U : Opens N :=
    ⟨(Phi : M → N) '' (V : Set M), image_opens_isOpen Phi Set.Subset.rfl⟩
  let e : V ≃ₘ⟮I, I⟯ U :=
    PartialDiffeomorph.toOpensDiffeoCross Phi Set.Subset.rfl
  refine
    { U := U
      V := V
      s := e.symm
      mem := ?_
      isSec := ?_ }
  · exact ⟨x, hx, (hPhi hx).symm.trans hxy⟩
  · intro z
    have hz : (((e.symm z : V) : M)) ∈ Phi.source := (e.symm z).2
    calc
      f ((e.symm z : V) : M) = Phi ((e.symm z : V) : M) := hPhi hz
      _ = (z : N) := congrArg Subtype.val (e.apply_symm_apply z)

namespace LocalSection

variable {f : M → N} {y : N} (S : LocalSection I f y)

private def toSource : S.U → M := fun z => ((S.s z : S.V) : M)

omit [FiniteDimensional Real E] [IsManifold I ∞ M] [IsManifold I ∞ N] in
private theorem toSource_contMDiff : ContMDiff I I ∞ S.toSource := by
  exact (contMDiff_subtype_val (I := I)).comp S.s.contMDiff

omit [FiniteDimensional Real E] [IsManifold I ∞ M] [IsManifold I ∞ N] in
private theorem mfderiv_toSource_apply
    (z : S.U) (v : TangentSpace I z) :
    mfderiv I I S.toSource z v = mfderiv I I S.s z v := by
  have hval : MDifferentiableAt I I
      (Subtype.val : S.V → M) (S.s z) :=
    (contMDiff_subtype_val (I := I)).mdifferentiableAt infty_ne_zero
  have hs : MDifferentiableAt I I (S.s : S.U → S.V) z :=
    S.s.contMDiff.mdifferentiableAt infty_ne_zero
  rw [show S.toSource = (Subtype.val : S.V → M) ∘ (S.s : S.U → S.V) from rfl,
    mfderiv_comp_apply z hval hs v, mfderiv_subtype_val_apply]

omit [FiniteDimensional Real E] [IsManifold I ∞ M] [IsManifold I ∞ N] in
private theorem dproj_sec
    (hf : IsLocalDiffeomorph I I ∞ f) (z : S.U) :
    (mfderiv I I f (S.toSource z)).comp (mfderiv I I S.toSource z) =
      mfderiv I I (Subtype.val : S.U → N) z := by
  have hcomp := mfderiv_comp z
    (hf.contMDiff.mdifferentiableAt infty_ne_zero)
    (S.toSource_contMDiff.mdifferentiableAt infty_ne_zero)
  have heq : f ∘ S.toSource = (Subtype.val : S.U → N) := by
    funext z'
    exact S.isSec z'
  rw [heq] at hcomp
  exact hcomp.symm

omit [FiniteDimensional Real E] [IsManifold I ∞ M] [IsManifold I ∞ N] in
private theorem inverse_mfderiv_eq
    (hf : IsLocalDiffeomorph I I ∞ f) (z : S.U)
    (hsec : f (S.toSource z) = (z : N))
    (v : TangentSpace I (z : N)) :
    (hsec ▸ hf.mfderivToContinuousLinearEquiv
        infty_ne_zero (S.toSource z)).symm v =
      mfderiv I I S.toSource z (tangentOpenEquiv S.U z v) := by
  have hright := ContinuousLinearMap.ext_iff.mp (S.dproj_sec hf z)
    (tangentOpenEquiv S.U z v)
  simp only [ContinuousLinearMap.comp_apply] at hright
  rw [hsec] at hright
  rw [mfderiv_subtype_val_tangentOpenEquiv] at hright
  let D : TangentSpace I (S.toSource z) ≃L[Real] TangentSpace I (z : N) :=
    hsec ▸ hf.mfderivToContinuousLinearEquiv infty_ne_zero (S.toSource z)
  change D.symm v = mfderiv I I S.toSource z (tangentOpenEquiv S.U z v)
  apply D.symm_apply_eq.mpr
  rw [show D (mfderiv I I S.toSource z (tangentOpenEquiv S.U z v)) =
      hsec ▸ (hf.mfderivToContinuousLinearEquiv
        infty_ne_zero (S.toSource z))
          (mfderiv I I S.toSource z (tangentOpenEquiv S.U z v)) by
        exact cast_continuousLinearEquiv_apply hsec _ _]
  have heq :
      (hf.mfderivToContinuousLinearEquiv infty_ne_zero (S.toSource z))
          (mfderiv I I S.toSource z (tangentOpenEquiv S.U z v)) =
        mfderiv I I f (S.toSource z)
          (mfderiv I I S.toSource z (tangentOpenEquiv S.U z v)) := by
    have hcoe := hf.mfderivToContinuousLinearEquiv_coe
      infty_ne_zero (S.toSource z)
    exact congrArg
      (fun L : TangentSpace I (S.toSource z) →L[Real]
          TangentSpace I (f (S.toSource z)) =>
        L (mfderiv I I S.toSource z (tangentOpenEquiv S.U z v))) hcoe
  rw [heq]
  exact (cast_tangent_eq_of_heq hsec _ _ (heq_of_eq hright)).symm

private theorem pullback_inner_eval
    [T2Space M] [T2Space N]
    (g : SmoothRiemannianMetric I M) (z : S.U)
    (v w : TangentSpace I z) :
    (Diffeomorph.pullbackMetricCross
        (g.restrictOpen (I := I) S.V) S.s).inner z v w =
      g.inner (S.toSource z)
        (mfderiv I I S.toSource z v)
        (mfderiv I I S.toSource z w) := by
  rw [Diffeomorph.pullbackMetricCross_inner,
    SmoothRiemannianMetric.restrictOpen_inner,
    S.mfderiv_toSource_apply, S.mfderiv_toSource_apply]
  rfl

private theorem descendedInner_locally_eq
    [T2Space M] [T2Space N]
    (g : SmoothRiemannianMetric I M)
    (hf : IsLocalDiffeomorph I I ∞ f)
    (hsurj : Function.Surjective f)
    (hcompat : metricFiberCompatible g f hf)
    (z : S.U) (v w : TangentSpace I (z : N)) :
    descendedInner g f hf hsurj (z : N) v w =
      (Diffeomorph.pullbackMetricCross
        (g.restrictOpen (I := I) S.V) S.s).inner z
          (tangentOpenEquiv S.U z v) (tangentOpenEquiv S.U z w) := by
  have hsec := S.isSec z
  change f (S.toSource z) = (z : N) at hsec
  rw [show descendedInner g f hf hsurj (z : N) =
      hsec ▸ localPushInner g f hf (S.toSource z) from
        descendedInner_eq_localPushInner_of_eq
          g f hf hsurj hcompat (S.toSource z) (z : N) hsec]
  rw [cast_localPushInner_apply, S.pullback_inner_eval]
  rw [S.inverse_mfderiv_eq hf z hsec,
    S.inverse_mfderiv_eq hf z hsec]

end LocalSection

private theorem descendedInner_coeff
    [T2Space M] [T2Space N]
    (g : SmoothRiemannianMetric I M) (f : M → N)
    (hf : IsLocalDiffeomorph I I ∞ f)
    (hsurj : Function.Surjective f)
    (hcompat : metricFiberCompatible g f hf)
    (x₀ : N) (i j : Fin (Module.finrank Real E)) :
    ContMDiffOn I (modelWithCornersSelf Real Real) ∞
      (fun x => descendedInner g f hf hsurj x
        (Geometry.frameVec (I := I) x₀ i x)
        (Geometry.frameVec (I := I) x₀ j x))
      (trivializationAt E (TangentSpace I) x₀).baseSet := by
  intro y hy
  let S := LocalSection.ofLocal f hf hsurj y
  apply ContMDiffAt.contMDiffWithinAt
  refine (contMDiffAt_subtype_iff (U := S.U)
    (x := ⟨y, S.mem⟩)).mp ?_
  have hfun :
      (fun z : S.U => descendedInner g f hf hsurj (z : N)
        (Geometry.frameVec (I := I) x₀ i (z : N))
        (Geometry.frameVec (I := I) x₀ j (z : N))) =
      fun z : S.U =>
        (Diffeomorph.pullbackMetricCross
          (g.restrictOpen (I := I) S.V) S.s).inner z
          (tangentOpenEquiv S.U z
            (Geometry.frameVec (I := I) x₀ i (z : N)))
          (tangentOpenEquiv S.U z
            (Geometry.frameVec (I := I) x₀ j (z : N))) := by
    funext z
    exact S.descendedInner_locally_eq g hf hsurj hcompat z _ _
  rw [hfun]
  exact CovariantDerivative.metric_inner_contMDiffAt
    (Diffeomorph.pullbackMetricCross
      (g.restrictOpen (I := I) S.V) S.s)
    (Geometry.frameVec_sub_cmdiffAt (I := I) S.U x₀ i hy S.mem)
    (Geometry.frameVec_sub_cmdiffAt (I := I) S.U x₀ j hy S.mem)
    (le_refl _)

noncomputable def descendedMetric
    [T2Space M] [T2Space N]
    (g : SmoothRiemannianMetric I M) (f : M → N)
    (hf : IsLocalDiffeomorph I I ∞ f)
    (hsurj : Function.Surjective f)
    (hcompat : metricFiberCompatible g f hf) :
    SmoothRiemannianMetric I N :=
  (Geometry.smoothMetric_of_localCoeff
    (descendedInner g f hf hsurj)
    (descendedInner_symm g f hf hsurj)
    (descendedInner_pos g f hf hsurj)
    (descendedInner_coeff g f hf hsurj hcompat)).choose

theorem descendedMetric_inner
    [T2Space M] [T2Space N]
    (g : SmoothRiemannianMetric I M) (f : M → N)
    (hf : IsLocalDiffeomorph I I ∞ f)
    (hsurj : Function.Surjective f)
    (hcompat : metricFiberCompatible g f hf)
    (y : N) (v w : TangentSpace I y) :
    (descendedMetric g f hf hsurj hcompat).inner y v w =
      descendedInner g f hf hsurj y v w :=
  (Geometry.smoothMetric_of_localCoeff
    (descendedInner g f hf hsurj)
    (descendedInner_symm g f hf hsurj)
    (descendedInner_pos g f hf hsurj)
    (descendedInner_coeff g f hf hsurj hcompat)).choose_spec y v w

theorem localPullMetric_descendedMetric
    [T2Space M] [T2Space N]
    (g : SmoothRiemannianMetric I M) (f : M → N)
    (hf : IsLocalDiffeomorph I I ∞ f)
    (hsurj : Function.Surjective f)
    (hcompat : metricFiberCompatible g f hf) :
    localPullMetric (descendedMetric g f hf hsurj hcompat) f hf = g := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [localPullMetric_inner, descendedMetric_inner,
    descendedInner_eq_localPushInner g f hf hsurj hcompat,
    localPushInner_apply]
  let D := hf.mfderivToContinuousLinearEquiv infty_ne_zero x
  change g.inner x (D.symm (mfderiv I I f x v))
      (D.symm (mfderiv I I f x w)) = g.inner x v w
  have hcoe : (D : TangentSpace I x →L[Real] TangentSpace I (f x)) =
      mfderiv I I f x := hf.mfderivToContinuousLinearEquiv_coe infty_ne_zero x
  rw [← hcoe]
  have hv : D.symm ((D : TangentSpace I x →L[Real]
      TangentSpace I (f x)) v) = v := D.symm_apply_apply v
  have hw : D.symm ((D : TangentSpace I x →L[Real]
      TangentSpace I (f x)) w) = w := D.symm_apply_apply w
  rw [hv, hw]

theorem localPullMetric_injective_of_surjective
    [T2Space M]
    (f : M → N) (hf : IsLocalDiffeomorph I I ∞ f)
    (hsurj : Function.Surjective f)
    {g h : SmoothRiemannianMetric I N}
    (heq : localPullMetric g f hf = localPullMetric h f hf) : g = h := by
  apply SmoothRiemannianMetric.ext_inner
  intro y v w
  obtain ⟨x, rfl⟩ := hsurj y
  let D := hf.mfderivToContinuousLinearEquiv infty_ne_zero x
  have hinner := congrArg
    (fun k : SmoothRiemannianMetric I M =>
      k.inner x (D.symm v) (D.symm w)) heq
  rw [localPullMetric_inner, localPullMetric_inner] at hinner
  have hcoe : (D : TangentSpace I x →L[Real] TangentSpace I (f x)) =
      mfderiv I I f x := hf.mfderivToContinuousLinearEquiv_coe infty_ne_zero x
  rw [← hcoe] at hinner
  have hv : (D : TangentSpace I x →L[Real]
      TangentSpace I (f x)) (D.symm v) = v := D.apply_symm_apply v
  have hw : (D : TangentSpace I x →L[Real]
      TangentSpace I (f x)) (D.symm w) = w := D.apply_symm_apply w
  rw [hv, hw] at hinner
  exact hinner

theorem exists_unique_metric_of_surjective_localDiffeomorph
    [T2Space M] [T2Space N]
    (g : SmoothRiemannianMetric I M) (f : M → N)
    (hf : IsLocalDiffeomorph I I ∞ f)
    (hsurj : Function.Surjective f)
    (hcompat : metricFiberCompatible g f hf) :
    ∃! h : SmoothRiemannianMetric I N, localPullMetric h f hf = g := by
  refine ⟨descendedMetric g f hf hsurj hcompat,
    localPullMetric_descendedMetric g f hf hsurj hcompat, ?_⟩
  intro h hh
  exact localPullMetric_injective_of_surjective f hf hsurj
    (hh.trans (localPullMetric_descendedMetric g f hf hsurj hcompat).symm)

end DifferentialGeometry
