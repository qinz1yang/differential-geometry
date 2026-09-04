import DifferentialGeometry.Geometry.Metric.Pullback.Cross
import Mathlib.Geometry.Manifold.Riemannian.PathELength

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
  [FiniteDimensional Real F]
variable {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners Real E H}
variable {G : Type*} [TopologicalSpace G]
  {J : ModelWithCorners Real F G}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
variable {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  [IsManifold J ∞ N]

private theorem infty_ne_zero : (∞ : WithTop ℕ∞) ≠ 0 := by decide

noncomputable def localPullInner
    (g : SmoothRiemannianMetric J N) (f : M → N) (x : M) :
    TangentSpace I x →L[Real] TangentSpace I x →L[Real] Real :=
  let D : TangentSpace I x →L[Real] TangentSpace J (f x) :=
    mfderiv I J f x
  (ContinuousLinearMap.precomp Real D).comp ((g.inner (f x)).comp D)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [IsManifold I ∞ M] in
theorem localPullInner_apply
    (g : SmoothRiemannianMetric J N) (f : M → N)
    (x : M) (v w : TangentSpace I x) :
    localPullInner (I := I) (J := J) g f x v w =
      g.inner (f x) (mfderiv I J f x v) (mfderiv I J f x w) := by
  simp only [localPullInner, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.precomp_apply]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [IsManifold I ∞ M] in
private theorem localPullInner_symm
    (g : SmoothRiemannianMetric J N) (f : M → N)
    (x : M) (v w : TangentSpace I x) :
    localPullInner (I := I) (J := J) g f x v w =
      localPullInner (I := I) (J := J) g f x w v := by
  rw [localPullInner_apply, localPullInner_apply]
  exact g.symm (f x) _ _

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [IsManifold I ∞ M] in
private theorem localPullInner_pos
    (g : SmoothRiemannianMetric J N) {f : M → N}
    (hf : IsLocalDiffeomorph I J ∞ f)
    (x : M) (v : TangentSpace I x) (hv : v ≠ 0) :
    0 < localPullInner (I := I) (J := J) g f x v v := by
  rw [localPullInner_apply]
  have hD :
      mfderiv I J f x v ≠ 0 := by
    have hv' :
        (hf.mfderivToContinuousLinearEquiv infty_ne_zero x) v ≠ 0 :=
      (hf.mfderivToContinuousLinearEquiv infty_ne_zero x).map_ne_zero_iff.mpr hv
    rw [← hf.mfderivToContinuousLinearEquiv_coe infty_ne_zero]
    exact hv'
  exact g.pos (f x) _ hD

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [IsManifold I ∞ M] in
private theorem localPullInner_bdd
    (g : SmoothRiemannianMetric J N) {f : M → N}
    (hf : IsLocalDiffeomorph I J ∞ f) :
    ∀ x : M, Bornology.IsVonNBounded Real
      {v : TangentSpace I x |
        localPullInner (I := I) (J := J) g f x v v < 1} := by
  intro x
  let e : TangentSpace I x ≃L[Real] TangentSpace J (f x) :=
    hf.mfderivToContinuousLinearEquiv infty_ne_zero x
  have himg :=
    (g.isVonNBounded (f x)).image
      (e.symm : TangentSpace J (f x) →L[Real] TangentSpace I x)
  have hset :
      {v : TangentSpace I x |
          localPullInner (I := I) (J := J) g f x v v < 1} =
        ((e.symm : TangentSpace J (f x) →L[Real] TangentSpace I x) : _ → _)
          '' {w : TangentSpace J (f x) | g.inner (f x) w w < 1} := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · intro hv
      refine ⟨e v, ?_, e.symm_apply_apply v⟩
      rw [localPullInner_apply] at hv
      rw [← hf.mfderivToContinuousLinearEquiv_coe infty_ne_zero] at hv
      exact hv
    · rintro ⟨w, hw, rfl⟩
      rw [localPullInner_apply]
      have hD :
          mfderiv I J f x
            ((e.symm : TangentSpace J (f x) →L[Real] TangentSpace I x) w) = w := by
        rw [← hf.mfderivToContinuousLinearEquiv_coe infty_ne_zero]
        exact e.apply_symm_apply w
      rw [hD]
      exact hw
  rw [hset]
  exact himg

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
private theorem push_smooth
    {f : M → N} (hf : ContMDiff I J ∞ f)
    (Y : ∀ x : M, TangentSpace I x)
    (hY : ContMDiff I (I.prod 𝓘(Real, E)) ∞
      (fun x : M => TotalSpace.mk' E
        (E := TangentSpace I) x (Y x))) :
    ContMDiff I (J.prod 𝓘(Real, F)) ∞
      (fun x : M => TotalSpace.mk' F
        (E := (TangentSpace J : N → Type _))
        (f x) (mfderiv I J f x (Y x))) := by
  exact (hf.contMDiff_tangentMap (le_refl _)).comp hY

noncomputable def localPullMetric
    [T2Space M]
    (g : SmoothRiemannianMetric J N) (f : M → N)
    (hf : IsLocalDiffeomorph I J ∞ f) :
    SmoothRiemannianMetric I M where
  inner x := localPullInner (I := I) (J := J) g f x
  symm x v w := localPullInner_symm (I := I) (J := J) g f x v w
  pos x v hv := localPullInner_pos (I := I) (J := J) g hf x v hv
  isVonNBounded := localPullInner_bdd (I := I) (J := J) g hf
  contMDiff := by
    classical
    apply contMDiff_continuousLinearMap_section_of_apply
      (V₂ := fun x : M => TangentSpace I x →L[Real] Real)
      (φ := fun x : M => localPullInner (I := I) (J := J) g f x)
    intro Y
    apply contMDiff_continuousLinearMap_section_of_apply
      (V₂ := fun _ : M => Real)
      (φ := fun x : M =>
        localPullInner (I := I) (J := J) g f x (Y x))
    intro W
    have hY := push_smooth (I := I) (J := J)
      hf.contMDiff (fun x => Y x) Y.contMDiff
    have hW := push_smooth (I := I) (J := J)
      hf.contMDiff (fun x => W x) W.contMDiff
    have hg :
        ContMDiff I (J.prod 𝓘(Real, F →L[Real] F →L[Real] Real)) ∞
          (fun x : M => TotalSpace.mk'
            (F →L[Real] F →L[Real] Real)
            (E := fun y : N =>
              TangentSpace J y →L[Real] TangentSpace J y →L[Real] Real)
            (f x) (g.inner (f x))) :=
      g.contMDiff.comp hf.contMDiff
    have htotal :
        ContMDiff I (J.prod 𝓘(Real, Real)) ∞
          (fun x : M => TotalSpace.mk' Real
            (E := Bundle.Trivial N Real) (f x)
            (g.inner (f x)
              (mfderiv I J f x (Y x))
              (mfderiv I J f x (W x)))) :=
      ContMDiff.clm_bundle_apply₂
        (E₁ := fun y : N => TangentSpace J y)
        (E₂ := fun y : N => TangentSpace J y)
        (E₃ := fun _ : N => Real)
        (b := f)
        (ψ := fun x => g.inner (f x))
        (v := fun x => mfderiv I J f x (Y x))
        (w := fun x => mfderiv I J f x (W x))
        hg hY hW
    have hscalar :
        ContMDiff I 𝓘(Real, Real) ∞
          (fun x : M =>
            g.inner (f x)
              (mfderiv I J f x (Y x))
              (mfderiv I J f x (W x))) := by
      intro x
      have hx := htotal x
      rw [contMDiffAt_totalSpace] at hx
      exact hx.2
    have hpull :
        ContMDiff I 𝓘(Real, Real) ∞
          (fun x : M =>
            localPullInner (I := I) (J := J) g f x (Y x) (W x)) := by
      simpa only [localPullInner_apply] using hscalar
    intro x
    rw [contMDiffAt_section]
    refine hpull.contMDiffAt.congr_of_eventuallyEq ?_
    filter_upwards with y
    rfl

omit [FiniteDimensional ℝ F] in
theorem localPullMetric_inner
    [T2Space M]
    (g : SmoothRiemannianMetric J N) (f : M → N)
    (hf : IsLocalDiffeomorph I J ∞ f)
    (x : M) (v w : TangentSpace I x) :
    (localPullMetric (I := I) (J := J) g f hf).inner x v w =
      g.inner (f x) (mfderiv I J f x v) (mfderiv I J f x w) :=
  localPullInner_apply (I := I) (J := J) g f x v w

omit [FiniteDimensional ℝ F] in
theorem localPull_enorm
    [T2Space M]
    [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
    (g : SmoothRiemannianMetric J N)
    (hEnorm : ∀ (y : N) (w : TangentSpace J y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (f : M → N)
    (hf : IsLocalDiffeomorph I J ∞ f)
    (x : M) (v : TangentSpace I x) :
    letI : RiemannianBundle
        (fun y : M ↦ TangentSpace I y) :=
      ⟨(localPullMetric (I := I) (J := J) g f hf).toRiemannianMetric⟩
    ‖mfderiv I J f x v‖ₑ = ‖v‖ₑ := by
  let : RiemannianBundle
      (fun y : M ↦ TangentSpace I y) :=
    ⟨(localPullMetric (I := I) (J := J) g f hf).toRiemannianMetric⟩
  rw [hEnorm, ← ofReal_norm, norm_eq_sqrt_real_inner]
  have hsrc :
      (inner Real v v : Real) =
        (localPullMetric (I := I) (J := J) g f hf).inner x v v :=
    rfl
  rw [hsrc, localPullMetric_inner]

omit [FiniteDimensional ℝ F] in
theorem localPull_pathLen
    [T2Space M]
    [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
    (g : SmoothRiemannianMetric J N)
    (hEnorm : ∀ (y : N) (w : TangentSpace J y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (f : M → N)
    (hf : IsLocalDiffeomorph I J ∞ f)
    {γ : Real → M} {a b : Real}
    (hγ : ContMDiffOn 𝓘(Real, Real) I 1 γ (Set.Icc a b)) :
    letI : RiemannianBundle
        (fun y : M ↦ TangentSpace I y) :=
      ⟨(localPullMetric (I := I) (J := J) g f hf).toRiemannianMetric⟩
    Manifold.pathELength J (f ∘ γ) a b =
      Manifold.pathELength I γ a b := by
  let : RiemannianBundle
      (fun y : M ↦ TangentSpace I y) :=
    ⟨(localPullMetric (I := I) (J := J) g f hf).toRiemannianMetric⟩
  rw [Manifold.pathELength_eq_lintegral_mfderiv_Ioo,
    Manifold.pathELength_eq_lintegral_mfderiv_Ioo]
  apply MeasureTheory.setLIntegral_congr_fun measurableSet_Ioo
  intro t ht
  have hγt : MDifferentiableAt 𝓘(Real, Real) I γ t :=
    ((hγ.mdifferentiableOn one_ne_zero) t
      ⟨ht.1.le, ht.2.le⟩).mdifferentiableAt
        (Icc_mem_nhds ht.1 ht.2)
  have hft : MDifferentiableAt I J f (γ t) :=
    hf.contMDiff.mdifferentiableAt (by decide)
  have hcomp :
      mfderiv 𝓘(Real, Real) J (f ∘ γ) t =
        (mfderiv I J f (γ t)).comp
          (mfderiv 𝓘(Real, Real) I γ t) :=
    mfderiv_comp t hft hγt
  change
    ‖mfderiv 𝓘(Real, Real) J (f ∘ γ) t 1‖ₑ =
      ‖mfderiv 𝓘(Real, Real) I γ t 1‖ₑ
  rw [hcomp]
  exact localPull_enorm (I := I) (J := J) g hEnorm f hf (γ t)
    (mfderiv 𝓘(Real, Real) I γ t 1)

end DifferentialGeometry
