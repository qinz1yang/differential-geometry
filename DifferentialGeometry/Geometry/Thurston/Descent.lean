import DifferentialGeometry.Geometry.Thurston.Atlas
import DifferentialGeometry.Geometry.Thurston.ElementaryModels
import DifferentialGeometry.Geometry.Metric.Quotient
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Properties
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Algebra.Group.MinimalAxioms

/-!
# Descent of model geometries along coverings

If `π : M → N` is a surjective smooth covering and a local isometry onto `(N, gQ)`, a
`GeometricStructure` on `M` descends to one on `N` with the same `ThurstonModel`: charts compose
with `π` on its sheets (`ModelAtlas.descendAlong`, `HasThurstonAtlas.descend`) and completeness
descends by path lifting (`GeometricStructure.descend`; finite volume is an input only for
`.hyperbolic`, automatic in `descendOfCompact`). For a group acting freely, properly
discontinuously and smoothly by isometries, `quotientMetric` is the induced metric on the orbit
space, `HasThurstonAtlas.quotient` descends the atlas alone and `GeometricStructure.quotient`
the whole structure. Flat witnesses: `KleinBottleGroup` acts on `E³` by
`(x, y, z) ↦ (x + n / 2, (-1)ⁿ y + m, (-1)ⁿ z)`, its even-glide subgroup `torusTranslations`
by the lattice `ℤ e₀ ⊕ ℤ e₁`; `TwistedKleinBundle` (interior of the twisted I-bundle over the
Klein bottle) and `TorusTimesLine` (`T² × ℝ`) carry `.euclidean` geometric structures.
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry
open scoped Manifold ContDiff Topology RealInnerProductSpace
namespace GC.Geometry

section Atlas

variable {E F G H H' H'' M N P : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace H'']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  {K : ModelWithCorners ℝ G H''}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
  [TopologicalSpace P] [ChartedSpace H'' P] [IsManifold K ∞ P]

omit [FiniteDimensional ℝ F] [IsManifold K ∞ P] in
theorem exists_descended_chart [T2Space M] {g : SmoothRiemannianMetric I M}
    {gQ : SmoothRiemannianMetric J N} {π : M → N} (hπ : IsLocalDiffeomorph I J ∞ π)
    (hpull : localPullMetric gQ π hπ = g) (e : PartialDiffeomorph K I P M ∞) {y : M}
    (hy : y ∈ e.target) :
    ∃ d : PartialDiffeomorph K J P N ∞, π y ∈ d.target ∧ d.source ⊆ e.source ∧
      ∀ p ∈ d.source, ∀ v w : TangentSpace K p,
        gQ.inner (d p) (mfderiv K J d p v) (mfderiv K J d p w) =
          g.inner (e p) (mfderiv K I e p v) (mfderiv K I e p w) := by
  obtain ⟨Φ, hyΦ, hΦ⟩ := hπ y
  let d := e.trans Φ
  refine ⟨d, ?_, fun p hp => hp.1, ?_⟩
  · change π y ∈ Φ.target ∩ Φ.symm ⁻¹' e.target
    rw [hΦ hyΦ]
    refine ⟨Φ.map_source hyΦ, ?_⟩
    rw [Set.mem_preimage, PartialDiffeomorph.symm_toPartialEquiv,
      Φ.toPartialEquiv.left_inv hyΦ]
    exact hy
  · intro p hp v w
    have hpe : p ∈ e.source := hp.1
    have hpΦ : e p ∈ Φ.source := hp.2
    have hdp : d p = π (e p) := (hΦ hpΦ).symm
    have hloc : (d : P → N) =ᶠ[𝓝 p] π ∘ e := by
      filter_upwards [d.open_source.mem_nhds hp] with z hz
      exact (hΦ hz.2).symm
    have he : MDifferentiableAt K I e p := e.mdifferentiableAt (by decide) hpe
    have hπd : MDifferentiableAt I J π (e p) :=
      (hπ.contMDiff.mdifferentiableAt (by decide))
    have hder (u : TangentSpace K p) :
        mfderiv K J d p u = mfderiv I J π (e p) (mfderiv K I e p u) := by
      rw [hloc.mfderiv_eq]
      exact mfderiv_comp_apply p hπd he u
    rw [hder, hder, hdp, ← hpull, localPullMetric_inner]

omit [FiniteDimensional ℝ F] in
theorem ModelAtlas.descendAlong [T2Space M] {g : SmoothRiemannianMetric I M}
    {h : SmoothRiemannianMetric K P} (hg : ModelAtlas g h) {gQ : SmoothRiemannianMetric J N}
    {π : M → N} (hπ : IsLocalDiffeomorph I J ∞ π) (hsurj : Function.Surjective π)
    (hpull : localPullMetric gQ π hπ = g) : ModelAtlas gQ h := by
  intro x
  obtain ⟨y, rfl⟩ := hsurj x
  obtain ⟨e, hy, he⟩ := hg y
  obtain ⟨d, hd, hde, hdi⟩ := exists_descended_chart hπ hpull e hy
  exact ⟨d, hd, fun p hp v w => (hdi p hp v w).trans (he p (hde hp) v w)⟩

omit [FiniteDimensional ℝ F] in
theorem CoordinateModelAtlas.descend [T2Space M] {g : SmoothRiemannianMetric I M}
    {k : CoordinateModel} (hg : CoordinateModelAtlas g k) {gQ : SmoothRiemannianMetric J N}
    {π : M → N} (hπ : IsLocalDiffeomorph I J ∞ π) (hsurj : Function.Surjective π)
    (hpull : localPullMetric gQ π hπ = g) : CoordinateModelAtlas gQ k := by
  intro x
  obtain ⟨y, rfl⟩ := hsurj x
  obtain ⟨e, hy, he⟩ := hg y
  obtain ⟨d, hd, hde, hdi⟩ := exists_descended_chart hπ hpull e hy
  exact ⟨d, hd, fun p hp v w => (hdi p hp v w).trans (he p (hde hp) v w)⟩

omit [FiniteDimensional ℝ F] in
theorem HasThurstonAtlas.descend [T2Space M] {g : SmoothRiemannianMetric I M}
    {k : ThurstonModel} (hg : HasThurstonAtlas g k) {gQ : SmoothRiemannianMetric J N}
    {π : M → N} (hπ : IsLocalDiffeomorph I J ∞ π) (hsurj : Function.Surjective π)
    (hpull : localPullMetric gQ π hπ = g) : HasThurstonAtlas gQ k := by
  cases k <;> first
    | exact ModelAtlas.descendAlong hg hπ hsurj hpull
    | exact CoordinateModelAtlas.descend hg hπ hsurj hpull

variable [T2Space M] [SigmaCompactSpace M] [T2Space N] [SigmaCompactSpace N]

def GeometricStructure.descend (G : GeometricStructure I M) {π : M → N}
    (hπ : IsLocalDiffeomorph I J ∞ π) (hcover : IsCoveringMap π)
    (hsurj : Function.Surjective π) (gQ : SmoothRiemannianMetric J N)
    (hpull : localPullMetric gQ π hπ = G.metric)
    (hvol : G.model = .hyperbolic →
      Integral.Measure.riemannianVolumeMeasure J N gQ Set.univ < ⊤) :
    GeometricStructure J N where
  model := G.model
  metric := gQ
  complete := RiemannianMetricComplete.of_coveringMap_localPullMetric G.metric gQ hπ hcover
    hsurj hpull G.complete
  atlas := G.atlas.descend hπ hsurj hpull
  hyperbolic_finite_volume := hvol

def GeometricStructure.descendOfCompact [CompactSpace N] (G : GeometricStructure I M)
    {π : M → N} (hπ : IsLocalDiffeomorph I J ∞ π) (hcover : IsCoveringMap π)
    (hsurj : Function.Surjective π) (gQ : SmoothRiemannianMetric J N)
    (hpull : localPullMetric gQ π hπ = G.metric) : GeometricStructure J N :=
  G.descend hπ hcover hsurj gQ hpull fun _ => by
    have := Integral.Measure.riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := J) (M := N) gQ
    exact MeasureTheory.measure_lt_top _ _

end Atlas

section Covering

variable {E H M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T2Space N] [SigmaCompactSpace N]

def GeometricStructure.descendMetric (G : GeometricStructure I M) {π : M → N}
    (hπ : IsLocalDiffeomorph I I ∞ π) (hcover : IsCoveringMap π)
    (hsurj : Function.Surjective π) (hcompat : metricFiberCompatible G.metric π hπ)
    (hvol : G.model = .hyperbolic → Integral.Measure.riemannianVolumeMeasure I N
      (descendedMetric G.metric π hπ hsurj hcompat) Set.univ < ⊤) :
    GeometricStructure I N :=
  G.descend hπ hcover hsurj _ (localPullMetric_descendedMetric G.metric π hπ hsurj hcompat) hvol

theorem GeometricStructure.descendMetric_metric (G : GeometricStructure I M) {π : M → N}
    (hπ : IsLocalDiffeomorph I I ∞ π) (hcover : IsCoveringMap π)
    (hsurj : Function.Surjective π) (hcompat : metricFiberCompatible G.metric π hπ)
    (hvol : G.model = .hyperbolic → Integral.Measure.riemannianVolumeMeasure I N
      (descendedMetric G.metric π hπ hsurj hcompat) Set.univ < ⊤) :
    (G.descendMetric hπ hcover hsurj hcompat hvol).metric =
      descendedMetric G.metric π hπ hsurj hcompat :=
  rfl

theorem GeometricStructure.descendMetric_model (G : GeometricStructure I M) {π : M → N}
    (hπ : IsLocalDiffeomorph I I ∞ π) (hcover : IsCoveringMap π)
    (hsurj : Function.Surjective π) (hcompat : metricFiberCompatible G.metric π hπ)
    (hvol : G.model = .hyperbolic → Integral.Measure.riemannianVolumeMeasure I N
      (descendedMetric G.metric π hπ hsurj hcompat) Set.univ < ⊤) :
    (G.descendMetric hπ hcover hsurj hcompat hvol).model = G.model :=
  rfl

end Covering

section Quotient

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {Γ M : Type*}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [Group Γ] [MulAction Γ M] [ProperlyDiscontinuousSMul Γ M] [ContinuousConstSMul Γ M]
  [IsCancelSMul Γ M] [T2Space M] [LocallyCompactSpace M] [ContMDiffConstSMul I ∞ Γ M]

omit [FiniteDimensional ℝ E] in
variable (I Γ M) in
theorem isLocalDiffeomorph_orbitMk :
    IsLocalDiffeomorph I I ∞ (Quotient.mk'' : M → MulAction.orbitRel.Quotient Γ M) :=
  MulAction.isLocalDiffeomorph_quotientMk_of_properlyDiscontinuousSMul (n := ∞) I

variable (Γ M) in
theorem isCoveringMap_orbitMk :
    IsCoveringMap (Quotient.mk'' : M → MulAction.orbitRel.Quotient Γ M) :=
  isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul.isCoveringMap

variable (Γ) in
def quotientMetric (g : SmoothRiemannianMetric I M)
    (hinv : ∀ γ : Γ,
      Diffeomorph.pullbackMetric g (MulAction.smulDiffeomorph (n := ∞) I γ) = g) :
    SmoothRiemannianMetric I (MulAction.orbitRel.Quotient Γ M) :=
  descendedMetric g Quotient.mk'' (isLocalDiffeomorph_orbitMk I Γ M) Quotient.mk''_surjective
    (metricFiberCompatible_quotientMk_of_invariant g hinv)

theorem localPullMetric_quotientMetric (g : SmoothRiemannianMetric I M)
    (hinv : ∀ γ : Γ,
      Diffeomorph.pullbackMetric g (MulAction.smulDiffeomorph (n := ∞) I γ) = g) :
    localPullMetric (quotientMetric Γ g hinv) Quotient.mk''
      (isLocalDiffeomorph_orbitMk I Γ M) = g :=
  localPullMetric_descendedMetric g _ _ _ _

theorem HasThurstonAtlas.quotient {g : SmoothRiemannianMetric I M} {k : ThurstonModel}
    (hg : HasThurstonAtlas g k)
    (hinv : ∀ γ : Γ,
      Diffeomorph.pullbackMetric g (MulAction.smulDiffeomorph (n := ∞) I γ) = g) :
    HasThurstonAtlas (quotientMetric Γ g hinv) k :=
  hg.descend (isLocalDiffeomorph_orbitMk I Γ M) Quotient.mk''_surjective
    (localPullMetric_quotientMetric g hinv)

theorem RiemannianMetricComplete.quotient [SigmaCompactSpace M]
    {g : SmoothRiemannianMetric I M} (hg : RiemannianMetricComplete g)
    (hinv : ∀ γ : Γ,
      Diffeomorph.pullbackMetric g (MulAction.smulDiffeomorph (n := ∞) I γ) = g) :
    RiemannianMetricComplete (quotientMetric Γ g hinv) :=
  RiemannianMetricComplete.of_coveringMap_localPullMetric g _ (isLocalDiffeomorph_orbitMk I Γ M)
    (isCoveringMap_orbitMk Γ M) Quotient.mk''_surjective (localPullMetric_quotientMetric g hinv)
    hg

variable [SigmaCompactSpace M]

variable (Γ) in
def GeometricStructure.quotient (G : GeometricStructure I M)
    (hinv : ∀ γ : Γ,
      Diffeomorph.pullbackMetric G.metric (MulAction.smulDiffeomorph (n := ∞) I γ) = G.metric)
    (hvol : G.model = .hyperbolic → Integral.Measure.riemannianVolumeMeasure I
      (MulAction.orbitRel.Quotient Γ M) (quotientMetric Γ G.metric hinv) Set.univ < ⊤) :
    GeometricStructure I (MulAction.orbitRel.Quotient Γ M) :=
  G.descend (isLocalDiffeomorph_orbitMk I Γ M) (isCoveringMap_orbitMk Γ M)
    Quotient.mk''_surjective (quotientMetric Γ G.metric hinv)
    (localPullMetric_quotientMetric G.metric hinv) hvol

theorem GeometricStructure.quotient_model (G : GeometricStructure I M)
    (hinv : ∀ γ : Γ,
      Diffeomorph.pullbackMetric G.metric (MulAction.smulDiffeomorph (n := ∞) I γ) = G.metric)
    (hvol : G.model = .hyperbolic → Integral.Measure.riemannianVolumeMeasure I
      (MulAction.orbitRel.Quotient Γ M) (quotientMetric Γ G.metric hinv) Set.univ < ⊤) :
    (G.quotient Γ hinv hvol).model = G.model :=
  rfl

theorem GeometricStructure.quotient_metric (G : GeometricStructure I M)
    (hinv : ∀ γ : Γ,
      Diffeomorph.pullbackMetric G.metric (MulAction.smulDiffeomorph (n := ∞) I γ) = G.metric)
    (hvol : G.model = .hyperbolic → Integral.Measure.riemannianVolumeMeasure I
      (MulAction.orbitRel.Quotient Γ M) (quotientMetric Γ G.metric hinv) Set.univ < ⊤) :
    (G.quotient Γ hinv hvol).metric = quotientMetric Γ G.metric hinv :=
  rfl

variable (Γ) in
def GeometricStructure.quotientOfCompact [CompactSpace (MulAction.orbitRel.Quotient Γ M)]
    (G : GeometricStructure I M)
    (hinv : ∀ γ : Γ,
      Diffeomorph.pullbackMetric G.metric (MulAction.smulDiffeomorph (n := ∞) I γ) =
        G.metric) :
    GeometricStructure I (MulAction.orbitRel.Quotient Γ M) :=
  G.descendOfCompact (isLocalDiffeomorph_orbitMk I Γ M) (isCoveringMap_orbitMk Γ M)
    Quotient.mk''_surjective (quotientMetric Γ G.metric hinv)
    (localPullMetric_quotientMetric G.metric hinv)

end Quotient

section Flat

local notation "E3" => EuclideanSpace ℝ (Fin 3)

def euclideanGeometricStructure : GeometricStructure (𝓡 3) E3 where
  model := .euclidean
  metric := euclideanModelMetric
  complete := euclideanModel_complete
  atlas := ModelAtlas.refl _
  hyperbolic_finite_volume := fun h => by cases h

theorem euclideanModelMetric_pullback_affine (Φ : E3 ≃ₘ⟮𝓡 3, 𝓡 3⟯ E3) (A : E3 ≃ₗᵢ[ℝ] E3)
    (c : E3) (hΦ : ∀ x, Φ x = A x + c) :
    Diffeomorph.pullbackMetric euclideanModelMetric Φ = euclideanModelMetric := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  have hfun : (Φ : E3 → E3) = fun y => A y + c := funext hΦ
  have hder : mfderiv (𝓡 3) (𝓡 3) Φ x = (A : E3 →L[ℝ] E3) := by
    rw [mfderiv_eq_fderiv, hfun]
    exact (A.toContinuousLinearEquiv.hasFDerivAt.add_const c).fderiv
  rw [Diffeomorph.pullbackMetric_inner, hder]
  exact A.inner_map_map v w

theorem isCancelSMul_of_free {Γ X : Type*} [Group Γ] [MulAction Γ X]
    (hfree : ∀ (γ : Γ) (x : X), γ • x = x → γ = 1) : IsCancelSMul Γ X where
  right_cancel' a b x h := by
    have h1 : (b⁻¹ * a) • x = x := by rw [mul_smul, h, inv_smul_smul]
    rw [← mul_inv_cancel_left b a, hfree _ x h1, mul_one]

section Affine

variable {Γ : Type*} [Group Γ] [MulAction Γ E3]

theorem properlyDiscontinuousSMul_of_affine (A : Γ → E3 ≃ₗᵢ[ℝ] E3) (c : Γ → E3)
    (hact : ∀ γ x, γ • x = A γ x + c γ) (hfin : ∀ R : ℝ, {γ : Γ | ‖c γ‖ ≤ R}.Finite) :
    ProperlyDiscontinuousSMul Γ E3 := by
  refine ⟨fun {K L} hK hL => ?_⟩
  obtain ⟨R, hR⟩ := (hK.isBounded.union hL.isBounded).subset_closedBall (0 : E3)
  refine (hfin (R + R)).subset ?_
  rintro γ ⟨_, ⟨k, hk, rfl⟩, hl⟩
  have hk' : ‖k‖ ≤ R := mem_closedBall_zero_iff.mp (hR (Or.inl hk))
  have hl' : ‖A γ k + c γ‖ ≤ R := by
    rw [← hact]
    exact mem_closedBall_zero_iff.mp (hR (Or.inr hl))
  change ‖c γ‖ ≤ R + R
  calc ‖c γ‖ = ‖(A γ k + c γ) - A γ k‖ := by rw [add_sub_cancel_left]
    _ ≤ ‖A γ k + c γ‖ + ‖A γ k‖ := norm_sub_le _ _
    _ ≤ R + R := by rw [LinearIsometryEquiv.norm_map]; linarith

theorem continuousConstSMul_of_affine (A : Γ → E3 ≃ₗᵢ[ℝ] E3) (c : Γ → E3)
    (hact : ∀ γ x, γ • x = A γ x + c γ) : ContinuousConstSMul Γ E3 := by
  refine ⟨fun γ => ?_⟩
  rw [show (fun x : E3 => γ • x) = fun x => A γ x + c γ from funext (hact γ)]
  exact (A γ).continuous.add continuous_const

theorem contMDiffConstSMul_of_affine (A : Γ → E3 ≃ₗᵢ[ℝ] E3) (c : Γ → E3)
    (hact : ∀ γ x, γ • x = A γ x + c γ) : ContMDiffConstSMul (𝓡 3) ∞ Γ E3 := by
  refine ⟨fun γ => ?_⟩
  rw [show (fun x : E3 => γ • x) = fun x => A γ x + c γ from funext (hact γ)]
  exact contMDiff_iff_contDiff.mpr ((A γ).contDiff.add contDiff_const)

theorem euclideanModelMetric_invariant_of_affine [ContMDiffConstSMul (𝓡 3) ∞ Γ E3]
    (A : Γ → E3 ≃ₗᵢ[ℝ] E3) (c : Γ → E3) (hact : ∀ γ x, γ • x = A γ x + c γ) (γ : Γ) :
    Diffeomorph.pullbackMetric euclideanModelMetric
      (MulAction.smulDiffeomorph (n := ∞) (𝓡 3) γ) = euclideanModelMetric :=
  euclideanModelMetric_pullback_affine _ (A γ) (c γ) (hact γ)

end Affine

@[ext]
structure KleinBottleGroup where
  glide : ℤ
  shift : ℤ

namespace KleinBottleGroup

instance : Mul KleinBottleGroup :=
  ⟨fun a b => ⟨a.glide + b.glide, a.shift + (a.glide.negOnePow : ℤ) * b.shift⟩⟩

instance : One KleinBottleGroup := ⟨⟨0, 0⟩⟩

instance : Inv KleinBottleGroup := ⟨fun a => ⟨-a.glide, -((a.glide.negOnePow : ℤ) * a.shift)⟩⟩

@[simp] theorem mul_glide (a b : KleinBottleGroup) : (a * b).glide = a.glide + b.glide := rfl

@[simp] theorem mul_shift (a b : KleinBottleGroup) :
    (a * b).shift = a.shift + (a.glide.negOnePow : ℤ) * b.shift := rfl

@[simp] theorem one_glide : (1 : KleinBottleGroup).glide = 0 := rfl

@[simp] theorem one_shift : (1 : KleinBottleGroup).shift = 0 := rfl

@[simp] theorem inv_glide (a : KleinBottleGroup) : a⁻¹.glide = -a.glide := rfl

@[simp] theorem inv_shift (a : KleinBottleGroup) :
    a⁻¹.shift = -((a.glide.negOnePow : ℤ) * a.shift) := rfl

instance : Group KleinBottleGroup :=
  Group.ofLeftAxioms
    (fun a b c => by
      ext
      · simp only [mul_glide]; ring
      · simp only [mul_shift, mul_glide, Int.negOnePow_add, Units.val_mul]; ring)
    (fun a => by ext <;> simp)
    (fun a => by
      ext
      · simp
      · simp only [mul_shift, inv_shift, inv_glide, Int.negOnePow_neg, one_shift]; ring)

end KleinBottleGroup

def kleinAxis : E3 := EuclideanSpace.single 0 1

def kleinFibre : E3 := EuclideanSpace.single 1 1

theorem inner_kleinAxis_kleinAxis : ⟪kleinAxis, kleinAxis⟫ = 1 := by
  simp [kleinAxis]

theorem inner_kleinAxis_kleinFibre : ⟪kleinAxis, kleinFibre⟫ = 0 := by
  simp [kleinAxis, kleinFibre, EuclideanSpace.inner_single_left]

theorem inner_kleinFibre_kleinAxis : ⟪kleinFibre, kleinAxis⟫ = 0 := by
  simp [kleinAxis, kleinFibre, EuclideanSpace.inner_single_left]

theorem inner_kleinFibre_kleinFibre : ⟪kleinFibre, kleinFibre⟫ = 1 := by
  simp [kleinFibre]

theorem norm_kleinAxis : ‖kleinAxis‖ = 1 := by
  simp [kleinAxis]

theorem norm_kleinFibre : ‖kleinFibre‖ = 1 := by
  simp [kleinFibre]

def kleinFlip : E3 ≃ₗᵢ[ℝ] E3 := (ℝ ∙ kleinAxis).reflection

theorem kleinFlip_kleinAxis : kleinFlip kleinAxis = kleinAxis :=
  Submodule.reflection_mem_subspace_eq_self (Submodule.mem_span_singleton_self _)

theorem kleinFlip_kleinFibre : kleinFlip kleinFibre = -kleinFibre :=
  Submodule.reflection_mem_subspace_orthogonalComplement_eq_neg
    (Submodule.mem_orthogonal_singleton_iff_inner_right.mpr inner_kleinAxis_kleinFibre)

theorem kleinFlip_mul_self : kleinFlip * kleinFlip = 1 :=
  Submodule.reflection_mul_reflection _

theorem kleinFlip_inv : kleinFlip⁻¹ = kleinFlip :=
  Submodule.reflection_inv

theorem kleinFlip_zpow_kleinAxis (n : ℤ) : (kleinFlip ^ n) kleinAxis = kleinAxis := by
  induction n using Int.induction_on with
  | zero => simp
  | succ i hi =>
    rw [zpow_add_one, LinearIsometryEquiv.coe_mul, Function.comp_apply, kleinFlip_kleinAxis, hi]
  | pred i hi =>
    rw [zpow_sub_one, LinearIsometryEquiv.coe_mul, Function.comp_apply, kleinFlip_inv,
      kleinFlip_kleinAxis, hi]

theorem kleinFlip_zpow_kleinFibre (n : ℤ) :
    (kleinFlip ^ n) kleinFibre = ((n.negOnePow : ℤ) : ℝ) • kleinFibre := by
  induction n using Int.induction_on with
  | zero => simp
  | succ i hi =>
    rw [zpow_add_one, LinearIsometryEquiv.coe_mul, Function.comp_apply, kleinFlip_kleinFibre,
      map_neg, hi, Int.negOnePow_succ, Units.val_neg, Int.cast_neg, neg_smul]
  | pred i hi =>
    rw [zpow_sub_one, LinearIsometryEquiv.coe_mul, Function.comp_apply, kleinFlip_inv,
      kleinFlip_kleinFibre, map_neg, hi, Int.negOnePow_sub, Int.negOnePow_one, Units.val_mul,
      Units.val_neg, Units.val_one, Int.cast_mul, Int.cast_neg, Int.cast_one, mul_neg, mul_one,
      neg_smul]

namespace KleinBottleGroup

def linearPart (γ : KleinBottleGroup) : E3 ≃ₗᵢ[ℝ] E3 := kleinFlip ^ γ.glide

def translationPart (γ : KleinBottleGroup) : E3 :=
  ((γ.glide : ℝ) / 2) • kleinAxis + (γ.shift : ℝ) • kleinFibre

instance : MulAction KleinBottleGroup E3 where
  smul γ x := γ.linearPart x + γ.translationPart
  one_smul x := by
    change (kleinFlip ^ (0 : ℤ)) x +
      ((((0 : ℤ) : ℝ) / 2) • kleinAxis + ((0 : ℤ) : ℝ) • kleinFibre) = x
    simp
  mul_smul a b x := by
    change (kleinFlip ^ (a.glide + b.glide)) x +
        ((((a.glide + b.glide : ℤ) : ℝ) / 2) • kleinAxis +
        ((a.shift + (a.glide.negOnePow : ℤ) * b.shift : ℤ) : ℝ) • kleinFibre) =
      (kleinFlip ^ a.glide) ((kleinFlip ^ b.glide) x +
        (((b.glide : ℝ) / 2) • kleinAxis + (b.shift : ℝ) • kleinFibre)) +
        (((a.glide : ℝ) / 2) • kleinAxis + (a.shift : ℝ) • kleinFibre)
    rw [zpow_add, LinearIsometryEquiv.coe_mul, Function.comp_apply, map_add, map_add, map_smul,
      map_smul, kleinFlip_zpow_kleinAxis, kleinFlip_zpow_kleinFibre]
    push_cast
    module

theorem smul_def (γ : KleinBottleGroup) (x : E3) :
    γ • x = γ.linearPart x + γ.translationPart :=
  rfl

theorem inner_kleinAxis_linearPart (γ : KleinBottleGroup) (x : E3) :
    ⟪kleinAxis, γ.linearPart x⟫ = ⟪kleinAxis, x⟫ := by
  conv_lhs => rw [← kleinFlip_zpow_kleinAxis γ.glide]
  exact LinearIsometryEquiv.inner_map_map _ _ _

theorem inner_kleinAxis_translationPart (γ : KleinBottleGroup) :
    ⟪kleinAxis, γ.translationPart⟫ = (γ.glide : ℝ) / 2 := by
  simp [translationPart, inner_add_right, inner_smul_right, norm_kleinAxis,
    inner_kleinAxis_kleinFibre]

theorem inner_kleinFibre_translationPart (γ : KleinBottleGroup) :
    ⟪kleinFibre, γ.translationPart⟫ = γ.shift := by
  simp [translationPart, inner_add_right, inner_smul_right, inner_kleinFibre_kleinAxis,
    norm_kleinFibre]

theorem eq_one_of_smul_eq (γ : KleinBottleGroup) (x : E3) (h : γ • x = x) : γ = 1 := by
  have h0 := congrArg (fun y => ⟪kleinAxis, y⟫) h
  simp only [smul_def, inner_add_right, inner_kleinAxis_linearPart,
    inner_kleinAxis_translationPart, add_eq_left, div_eq_zero_iff, Int.cast_eq_zero] at h0
  have hg : γ.glide = 0 := h0.resolve_right two_ne_zero
  have hlin : γ.linearPart = 1 := by rw [linearPart, hg, zpow_zero]
  have h1 := congrArg (fun y => ⟪kleinFibre, y⟫) h
  simp only [smul_def, hlin, LinearIsometryEquiv.coe_one, id, inner_add_right,
    inner_kleinFibre_translationPart, add_eq_left, Int.cast_eq_zero] at h1
  exact KleinBottleGroup.ext hg h1

theorem finite_norm_translationPart_le (R : ℝ) :
    {γ : KleinBottleGroup | ‖γ.translationPart‖ ≤ R}.Finite := by
  let B : ℤ := ⌈2 * R⌉
  refine (((Set.finite_Icc (-B) B).prod (Set.finite_Icc (-B) B)).image
    (fun p : ℤ × ℤ => (⟨p.1, p.2⟩ : KleinBottleGroup))).subset ?_
  intro γ hγ
  have hR : ‖γ.translationPart‖ ≤ R := hγ
  have hB : 2 * R ≤ B := Int.le_ceil _
  have hax : |(γ.glide : ℝ) / 2| ≤ R := by
    rw [← inner_kleinAxis_translationPart]
    refine (abs_real_inner_le_norm _ _).trans ?_
    rw [norm_kleinAxis, one_mul]
    exact hR
  have hfi : |(γ.shift : ℝ)| ≤ R := by
    rw [← inner_kleinFibre_translationPart]
    refine (abs_real_inner_le_norm _ _).trans ?_
    rw [norm_kleinFibre, one_mul]
    exact hR
  rw [abs_div, abs_two, div_le_iff₀ two_pos] at hax
  have hR0 : 0 ≤ R := (abs_nonneg _).trans hfi
  obtain ⟨hg1, hg2⟩ := abs_le.mp hax
  obtain ⟨hs1, hs2⟩ := abs_le.mp hfi
  refine ⟨(γ.glide, γ.shift), ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, rfl⟩
  · have : ((-B : ℤ) : ℝ) ≤ γ.glide := by push_cast; linarith
    exact_mod_cast this
  · have : (γ.glide : ℝ) ≤ (B : ℝ) := by linarith
    exact_mod_cast this
  · have : ((-B : ℤ) : ℝ) ≤ γ.shift := by push_cast; linarith
    exact_mod_cast this
  · have : (γ.shift : ℝ) ≤ (B : ℝ) := by linarith
    exact_mod_cast this

end KleinBottleGroup

instance : ProperlyDiscontinuousSMul KleinBottleGroup E3 :=
  properlyDiscontinuousSMul_of_affine KleinBottleGroup.linearPart
    KleinBottleGroup.translationPart KleinBottleGroup.smul_def
    KleinBottleGroup.finite_norm_translationPart_le

instance : ContinuousConstSMul KleinBottleGroup E3 :=
  continuousConstSMul_of_affine KleinBottleGroup.linearPart
    KleinBottleGroup.translationPart KleinBottleGroup.smul_def

instance : ContMDiffConstSMul (𝓡 3) ∞ KleinBottleGroup E3 :=
  contMDiffConstSMul_of_affine KleinBottleGroup.linearPart
    KleinBottleGroup.translationPart KleinBottleGroup.smul_def

instance : IsCancelSMul KleinBottleGroup E3 :=
  isCancelSMul_of_free KleinBottleGroup.eq_one_of_smul_eq

def torusTranslations : Subgroup KleinBottleGroup where
  carrier := {γ | Even γ.glide}
  mul_mem' ha hb := ha.add hb
  one_mem' := ⟨0, rfl⟩
  inv_mem' ha := ha.neg

theorem mem_torusTranslations (γ : KleinBottleGroup) :
    γ ∈ torusTranslations ↔ Even γ.glide :=
  Iff.rfl

theorem torusTranslations_smul (γ : torusTranslations) (x : E3) :
    γ • x = x + (γ : KleinBottleGroup).translationPart := by
  obtain ⟨r, hr⟩ := γ.2
  change (kleinFlip ^ (γ : KleinBottleGroup).glide) x + _ = _
  rw [hr, ← two_mul, zpow_mul, zpow_two, kleinFlip_mul_self, one_zpow, LinearIsometryEquiv.coe_one,
    id]

instance : ProperlyDiscontinuousSMul torusTranslations E3 :=
  properlyDiscontinuousSMul_of_affine (fun γ => (γ : KleinBottleGroup).linearPart)
    (fun γ => (γ : KleinBottleGroup).translationPart) (fun γ x => KleinBottleGroup.smul_def γ x)
    (fun R => (KleinBottleGroup.finite_norm_translationPart_le R).preimage
      Subtype.val_injective.injOn)

instance : ContinuousConstSMul torusTranslations E3 :=
  continuousConstSMul_of_affine (fun γ => (γ : KleinBottleGroup).linearPart)
    (fun γ => (γ : KleinBottleGroup).translationPart) (fun γ x => KleinBottleGroup.smul_def γ x)

instance : ContMDiffConstSMul (𝓡 3) ∞ torusTranslations E3 :=
  contMDiffConstSMul_of_affine (fun γ => (γ : KleinBottleGroup).linearPart)
    (fun γ => (γ : KleinBottleGroup).translationPart) (fun γ x => KleinBottleGroup.smul_def γ x)

instance : IsCancelSMul torusTranslations E3 :=
  isCancelSMul_of_free fun γ x h =>
    Subtype.ext (KleinBottleGroup.eq_one_of_smul_eq (γ : KleinBottleGroup) x h)

abbrev TwistedKleinBundle := MulAction.orbitRel.Quotient KleinBottleGroup E3

abbrev TorusTimesLine := MulAction.orbitRel.Quotient torusTranslations E3

def twistedKleinBundleGeometry : GeometricStructure (𝓡 3) TwistedKleinBundle :=
  euclideanGeometricStructure.quotient KleinBottleGroup
    (euclideanModelMetric_invariant_of_affine KleinBottleGroup.linearPart
      KleinBottleGroup.translationPart KleinBottleGroup.smul_def)
    (fun h => by cases h)

theorem twistedKleinBundleGeometry_model : twistedKleinBundleGeometry.model = .euclidean :=
  rfl

def torusTimesLineGeometry : GeometricStructure (𝓡 3) TorusTimesLine :=
  euclideanGeometricStructure.quotient torusTranslations
    (euclideanModelMetric_invariant_of_affine
      (fun γ : torusTranslations => (γ : KleinBottleGroup).linearPart)
      (fun γ : torusTranslations => (γ : KleinBottleGroup).translationPart)
      (fun γ x => KleinBottleGroup.smul_def γ x))
    (fun h => by cases h)

theorem torusTimesLineGeometry_model : torusTimesLineGeometry.model = .euclidean :=
  rfl

end Flat

end GC.Geometry
