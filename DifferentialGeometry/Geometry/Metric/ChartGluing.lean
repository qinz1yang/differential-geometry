import DifferentialGeometry.Geometry.Metric.FamilyGluing
import DifferentialGeometry.Geometry.Metric.Quotient
import DifferentialGeometry.Topology.Manifold.OpenEmbedding

section

set_option autoImplicit false
noncomputable section
open Set Bundle TopologicalSpace
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Metric

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {ι : Type*}

theorem exists_unique_metric_of_open_cover
    (U : ι → Opens M) (g : ∀ i, SmoothRiemannianMetric I (U i))
    (hcover : ∀ x : M, ∃ i, x ∈ U i)
    (heq : ∀ (i j : ι) (x : M) (hi : x ∈ U i) (hj : x ∈ U j) (v w : TangentSpace I x),
      (g i).inner ⟨x, hi⟩ v w = (g j).inner ⟨x, hj⟩ v w) :
    ∃! G : SmoothRiemannianMetric I M, ∀ i, G.restrictOpen (U i) = g i := by
  let V : Opens M := ⊤
  have hUV : ∀ i, U i ≤ V := fun _ => le_top
  have hcoverV : ∀ x : V, ∃ i, x.val ∈ U i := fun x => hcover x
  let gV := glueMetricFamilyOn U g V hUV hcoverV heq
  let hval := isLocalDiffeomorph_subtype_val (I := I) V
  have hsurj : Function.Surjective (Subtype.val : V → M) := fun x => ⟨⟨x, trivial⟩, rfl⟩
  have hcompat : metricFiberCompatible gV (Subtype.val : V → M) hval := by
    intro x y hxy
    have h : x = y := Subtype.ext hxy
    subst y
    rfl
  obtain ⟨G, hG, _⟩ := exists_unique_metric_of_surjective_localDiffeomorph
    gV (Subtype.val : V → M) hval hsurj hcompat
  have hGinner (x : V) (v w : TangentSpace I x) :
      G.inner (x : M) v w = gV.inner x v w := by
    have h := congrArg (fun g : SmoothRiemannianMetric I V => g.inner x v w) hG
    simpa only [localPullMetric_inner, mfderiv_subtype_val_apply] using h
  have hrestrict : ∀ i, G.restrictOpen (U i) = g i := by
    intro i
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    change G.inner (x : M) v w = (g i).inner x v w
    exact (hGinner (Opens.inclusion (hUV i) x) v w).trans
      (glueMetricFamilyOn_inner U g V hUV hcoverV heq i x v w)
  refine ⟨G, hrestrict, ?_⟩
  intro G' hG'
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  obtain ⟨i, hi⟩ := hcover x
  have h₁ := congrArg (fun k : SmoothRiemannianMetric I (U i) => k.inner ⟨x, hi⟩ v w) (hG' i)
  have h₂ := congrArg (fun k : SmoothRiemannianMetric I (U i) => k.inner ⟨x, hi⟩ v w) (hrestrict i)
  exact h₁.trans h₂.symm

end DifferentialGeometry.Geometry.Metric
end

end

section

set_option autoImplicit false
noncomputable section
open Set Bundle TopologicalSpace
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Metric

open DifferentialGeometry.Topology.Manifold

variable {E H P Q : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace P] [ChartedSpace H P] [IsManifold I ∞ P] [T2Space P]
  [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q] [T2Space Q]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ P] [T2Space P] [IsManifold I ∞ Q] [T2Space Q] in
private theorem mfderiv_diffeomorphOntoImage
    (f : P → Q) (hf : IsLocalDiffeomorph I I ∞ f) (hinj : Function.Injective f) (x : P) :
    mfderiv I I (diffeomorphOntoImage f hf hinj) x = mfderiv I I f x := by
  have hcomp : (Subtype.val : hf.image → Q) ∘ diffeomorphOntoImage f hf hinj = f := rfl
  have hchain := mfderiv_comp x
    (contMDiff_subtype_val.mdifferentiableAt (by decide : (∞ : WithTop ℕ∞) ≠ 0))
    ((diffeomorphOntoImage f hf hinj).contMDiff.mdifferentiableAt (by decide))
  rw [hcomp, mfderiv_subtype_val] at hchain
  exact hchain.symm

private def metricOnImage
    (g : SmoothRiemannianMetric I P) (f : P → Q)
    (hf : IsLocalDiffeomorph I I ∞ f) (hinj : Function.Injective f) :
    SmoothRiemannianMetric I hf.image :=
  Diffeomorph.pullbackMetricCross g (diffeomorphOntoImage f hf hinj).symm

private theorem metricOnImage_pullback
    (g : SmoothRiemannianMetric I P) (f : P → Q)
    (hf : IsLocalDiffeomorph I I ∞ f) (hinj : Function.Injective f) :
    Diffeomorph.pullbackMetricCross (metricOnImage g f hf hinj)
      (diffeomorphOntoImage f hf hinj) = g :=
  Diffeomorph.pullbackMetricCross_symm_eq_iff.mpr rfl

private theorem metricOnImage_inner
    (g : SmoothRiemannianMetric I P) (f : P → Q)
    (hf : IsLocalDiffeomorph I I ∞ f) (hinj : Function.Injective f)
    (x : P) (v w : TangentSpace I (f x)) :
    (metricOnImage g f hf hinj).inner (diffeomorphOntoImage f hf hinj x) v w =
      localPushInner g f hf x v w := by
  let A := hf.mfderivToContinuousLinearEquiv infty_ne_zero x
  have hcoe : (A : TangentSpace I x →L[ℝ] TangentSpace I (f x)) = mfderiv I I f x :=
    hf.mfderivToContinuousLinearEquiv_coe infty_ne_zero x
  have hpull := congrArg (fun k : SmoothRiemannianMetric I P => k.inner x (A.symm v) (A.symm w))
    (metricOnImage_pullback g f hf hinj)
  rw [Diffeomorph.pullbackMetricCross_inner, mfderiv_diffeomorphOntoImage, ← hcoe] at hpull
  change (metricOnImage g f hf hinj).inner (diffeomorphOntoImage f hf hinj x)
    (A (A.symm v)) (A (A.symm w)) = g.inner x (A.symm v) (A.symm w) at hpull
  simpa only [ContinuousLinearEquiv.apply_symm_apply, localPushInner_apply] using hpull

private theorem metricOnImage_inner_of_eq
    (g : SmoothRiemannianMetric I P) (f : P → Q)
    (hf : IsLocalDiffeomorph I I ∞ f) (hinj : Function.Injective f)
    (x : P) (y : Q) (hxy : f x = y) (v w : TangentSpace I y) :
    (metricOnImage g f hf hinj).inner ⟨y, ⟨x, hxy⟩⟩ v w =
      localPushInner g f hf x v w := by
  cases hxy
  exact metricOnImage_inner g f hf hinj x v w

omit [FiniteDimensional ℝ E] [IsManifold I ∞ Q] [T2Space Q] in
private theorem cast_bilinear_eq {x y : Q} (hxy : x = y)
    (b : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :
    (hxy ▸ b : TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) = b := by
  cases hxy
  rfl

end DifferentialGeometry.Geometry.Metric

namespace DifferentialGeometry.Geometry.Metric

open DifferentialGeometry.Topology.Manifold

variable {E H Q : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q] [T2Space Q]
  {ι : Type*} {P : ι → Type*}
  [∀ i, TopologicalSpace (P i)] [∀ i, ChartedSpace H (P i)]
  [∀ i, IsManifold I ∞ (P i)] [∀ i, T2Space (P i)]

theorem exists_unique_metric_of_localDiffeomorph_cover
    (f : ∀ i, P i → Q) (hf : ∀ i, IsLocalDiffeomorph I I ∞ (f i))
    (hinj : ∀ i, Function.Injective (f i)) (hcover : ∀ y, ∃ i x, f i x = y)
    (g : ∀ i, SmoothRiemannianMetric I (P i))
    (hcompat : ∀ (i j : ι) (x : P i) (y : P j) (hxy : f i x = f j y),
      hxy ▸ localPushInner (g i) (f i) (hf i) x = localPushInner (g j) (f j) (hf j) y) :
    ∃! G : SmoothRiemannianMetric I Q, ∀ i, localPullMetric G (f i) (hf i) = g i := by
  let U : ι → Opens Q := fun i => (hf i).image
  let gU : ∀ i, SmoothRiemannianMetric I (U i) := fun i => metricOnImage (g i) (f i) (hf i) (hinj i)
  have hcoverU : ∀ y : Q, ∃ i, y ∈ U i := by
    intro y
    obtain ⟨i, x, hx⟩ := hcover y
    exact ⟨i, x, hx⟩
  have heq : ∀ (i j : ι) (y : Q) (hi : y ∈ U i) (hj : y ∈ U j) (v w : TangentSpace I y),
      (gU i).inner ⟨y, hi⟩ v w = (gU j).inner ⟨y, hj⟩ v w := by
    intro i j y hi hj v w
    obtain ⟨xi, hxi⟩ := hi
    obtain ⟨xj, hxj⟩ := hj
    have hi : (gU i).inner ⟨y, ⟨xi, hxi⟩⟩ v w = localPushInner (g i) (f i) (hf i) xi v w :=
      metricOnImage_inner_of_eq (g i) (f i) (hf i) (hinj i) xi y hxi v w
    have hj : (gU j).inner ⟨y, ⟨xj, hxj⟩⟩ v w = localPushInner (g j) (f j) (hf j) xj v w :=
      metricOnImage_inner_of_eq (g j) (f j) (hf j) (hinj j) xj y hxj v w
    have hh : localPushInner (g i) (f i) (hf i) xi = localPushInner (g j) (f j) (hf j) xj := by
      exact (cast_bilinear_eq (hxi.trans hxj.symm) _).symm.trans
        (hcompat i j xi xj (hxi.trans hxj.symm))
    exact hi.trans ((congrArg (fun b => b v w) hh).trans hj.symm)
  obtain ⟨G, hG, _⟩ := exists_unique_metric_of_open_cover U gU hcoverU heq
  have hpull : ∀ i, localPullMetric G (f i) (hf i) = g i := by
    intro i
    have hi := congrArg (fun k : SmoothRiemannianMetric I (U i) =>
      Diffeomorph.pullbackMetricCross k (diffeomorphOntoImage (f i) (hf i) (hinj i))) (hG i)
    rw [metricOnImage_pullback] at hi
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    have he := congrArg (fun k : SmoothRiemannianMetric I (P i) => k.inner x v w) hi
    rw [Diffeomorph.pullbackMetricCross_inner, SmoothRiemannianMetric.restrictOpen_inner,
      mfderiv_diffeomorphOntoImage] at he
    exact he
  refine ⟨G, hpull, ?_⟩
  intro G' hG'
  apply SmoothRiemannianMetric.ext_inner
  intro y v w
  obtain ⟨i, x, rfl⟩ := hcover y
  let A := (hf i).mfderivToContinuousLinearEquiv infty_ne_zero x
  have hcoe : (A : TangentSpace I x →L[ℝ] TangentSpace I (f i x)) = mfderiv I I (f i) x :=
    (hf i).mfderivToContinuousLinearEquiv_coe infty_ne_zero x
  have he := congrArg (fun k : SmoothRiemannianMetric I (P i) => k.inner x (A.symm v) (A.symm w))
    ((hG' i).trans (hpull i).symm)
  rw [localPullMetric_inner, localPullMetric_inner, ← hcoe] at he
  change G'.inner (f i x) (A (A.symm v)) (A (A.symm w)) =
    G.inner (f i x) (A (A.symm v)) (A (A.symm w)) at he
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using he

end DifferentialGeometry.Geometry.Metric
end

end

section

set_option autoImplicit false
noncomputable section
open Bundle
open scoped Manifold ContDiff

namespace DifferentialGeometry

variable {E H M N Q : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ Q] in
theorem localPushInner_eq_of_derivative_factorization
    (gM : SmoothRiemannianMetric I M) (gN : SmoothRiemannianMetric I N)
    (f : M → Q) (g : N → Q)
    (hf : IsLocalDiffeomorph I I ∞ f) (hg : IsLocalDiffeomorph I I ∞ g)
    (x : M) (y : N) (hxy : f x = g y)
    (L : TangentSpace I x →L[ℝ] TangentSpace I y)
    (hD : mfderiv I I f x = (mfderiv I I g y).comp L)
    (hmetric : ∀ v w, gM.inner x v w = gN.inner y (L v) (L w)) :
    hxy ▸ localPushInner gM f hf x = localPushInner gN g hg y := by
  have hcast (q₁ q₂ : Q) (h : q₁ = q₂)
      (b : TangentSpace I q₁ →L[ℝ] TangentSpace I q₁ →L[ℝ] ℝ) :
      (h ▸ b : TangentSpace I q₂ →L[ℝ] TangentSpace I q₂ →L[ℝ] ℝ) = b := by
    cases h
    rfl
  rw [hcast]
  let A := hf.mfderivToContinuousLinearEquiv infty_ne_zero x
  let B := hg.mfderivToContinuousLinearEquiv infty_ne_zero y
  have hA : (A : TangentSpace I x →L[ℝ] TangentSpace I (f x)) = mfderiv I I f x :=
    hf.mfderivToContinuousLinearEquiv_coe infty_ne_zero x
  have hB : (B : TangentSpace I y →L[ℝ] TangentSpace I (g y)) = mfderiv I I g y :=
    hg.mfderivToContinuousLinearEquiv_coe infty_ne_zero y
  have hL (v : TangentSpace I (f x)) : L (A.symm v) = B.symm v := by
    apply B.injective
    have hv := congrArg (fun T : TangentSpace I x →L[ℝ] E => T (A.symm v)) hD
    rw [← hA, ← hB] at hv
    change A (A.symm v) = B (L (A.symm v)) at hv
    exact hv.symm.trans ((A.apply_symm_apply v).trans (B.apply_symm_apply v).symm)
  ext v w
  change gM.inner x (A.symm v) (A.symm w) = gN.inner y (B.symm v) (B.symm w)
  exact (hmetric _ _).trans (congrArg₂ (fun v w : TangentSpace I y => gN.inner y v w) (hL v) (hL w))

end DifferentialGeometry

end

end

