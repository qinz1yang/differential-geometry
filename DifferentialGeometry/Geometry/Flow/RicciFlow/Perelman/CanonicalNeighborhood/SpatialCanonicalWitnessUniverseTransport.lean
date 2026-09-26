import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialCanonicalWitnessTransport
import DifferentialGeometry.Topology.Manifold.ULift
import DifferentialGeometry.Geometry.Metric.Convergence.Naturality.CrossTensorPullback

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness (tensor02CovDerivNormWith)
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Measure
  (riemannianVolumeMeasure_image_eq_of_injective_local_isometry)
open DifferentialGeometry.Topology (uliftChartedSpace isManifold_ulift uliftDiffeomorph)
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions (pullbackTensor02FieldCross
  pullbackTensor02FieldCross_apply tensor02CovDerivNormWith_pullbackTensor02FieldCross)

universe u v

attribute [local instance] uliftChartedSpace

section IsometricBalls

open DifferentialGeometry.Geometry.Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} {N : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T2Space N]

private theorem image_riemannianClosedBall_eq_of_isometric_on_compact_ball_lift
    (h : SmoothRiemannianMetric I N) (g : SmoothRiemannianMetric I M)
    (F : PartialDiffeomorph I I N M ∞) (p : N)
    {R r : ℝ} (hr : 0 ≤ r) (hbuffer : r < R)
    (hcpt : IsCompact (riemannianClosedBallOf h p R))
    (hsource : riemannianClosedBallOf h p R ⊆ F.source)
    (hmetric : ∀ x ∈ riemannianClosedBallOf h p R, ∀ v : TangentSpace I x,
      g.inner (F x) (mfderiv I I (F : N → M) x v)
        (mfderiv I I (F : N → M) x v) = h.inner x v v) :
    (F : N → M) '' riemannianClosedBallOf h p r = riemannianClosedBallOf g (F p) r := by
  have hR : 0 < R := hr.trans_lt hbuffer
  have hlower : ∀ x ∈ riemannianClosedBallOf h p R, ∀ v : TangentSpace I x,
      h.inner x v v ≤ (1 : ℝ) ^ 2 *
        g.inner (F x) (mfderiv I I (F : N → M) x v)
          (mfderiv I I (F : N → M) x v) := by
    intro x hx v
    rw [one_pow, one_mul, hmetric x hx v]
  apply Set.Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    have hxR : riemannianEDistOf h p x < ENNReal.ofReal R :=
      lt_of_le_of_lt hx ((ENNReal.ofReal_lt_ofReal_iff hR).mpr hbuffer)
    have hle :=
      DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.edistOf_map_le_of_metric_upper_on_ball
        h g F p x hR (show (0 : ℝ) < 1 by norm_num) hsource
        (fun z hz v => by rw [one_pow, one_mul, hmetric z hz v]) hxR
    change riemannianEDistOf g (F p) (F x) ≤ ENNReal.ofReal r
    have hle' : riemannianEDistOf g (F p) (F x) ≤ riemannianEDistOf h p x := by
      simpa only [ENNReal.ofReal_one, one_mul] using hle
    exact hle'.trans hx
  · intro y hy
    obtain ⟨hyt, hx⟩ := DifferentialGeometry.PartialDiffeomorph.symm_mem_riemannianClosedBall_of_metric_lower h g F p hr
      (show (0 : ℝ) < 1 by norm_num) (by simpa using hbuffer) hcpt hsource hlower y hy
    exact ⟨F.symm y, by simpa only [one_mul] using hx, F.right_inv' hyt⟩

private theorem image_riemannianBall_eq_of_isometric_on_compact_ball_lift
    (h : SmoothRiemannianMetric I N) (g : SmoothRiemannianMetric I M)
    (F : PartialDiffeomorph I I N M ∞) (p : N)
    {R r : ℝ} (hr : 0 < r) (hbuffer : r < R)
    (hcpt : IsCompact (riemannianClosedBallOf h p R))
    (hsource : riemannianClosedBallOf h p R ⊆ F.source)
    (hmetric : ∀ x ∈ riemannianClosedBallOf h p R, ∀ v : TangentSpace I x,
      g.inner (F x) (mfderiv I I (F : N → M) x v)
        (mfderiv I I (F : N → M) x v) = h.inner x v v) :
    (F : N → M) '' riemannianBallOf h p r = riemannianBallOf g (F p) r := by
  have hR : 0 < R := hr.trans hbuffer
  apply Set.Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    have hxR := hx.trans ((ENNReal.ofReal_lt_ofReal_iff hR).mpr hbuffer)
    have hle :=
      DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.edistOf_map_le_of_metric_upper_on_ball
        h g F p x hR (show (0 : ℝ) < 1 by norm_num) hsource
        (fun z hz v => by rw [one_pow, one_mul, hmetric z hz v]) hxR
    exact lt_of_le_of_lt (by simpa only [ENNReal.ofReal_one, one_mul] using hle) hx
  · intro y hy
    have hfin : riemannianEDistOf g (F p) y ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top hy.le
    let d := (riemannianEDistOf g (F p) y).toReal
    have hd : 0 ≤ d := ENNReal.toReal_nonneg
    have hdr : d < r := (ENNReal.toReal_lt_of_lt_ofReal hy)
    have hdeq : ENNReal.ofReal d = riemannianEDistOf g (F p) y := ENNReal.ofReal_toReal hfin
    have hmem : y ∈ riemannianClosedBallOf g (F p) d := by
      change riemannianEDistOf g (F p) y ≤ ENNReal.ofReal d
      rw [hdeq]
    rw [← image_riemannianClosedBall_eq_of_isometric_on_compact_ball_lift h g F p
      hd (hdr.trans hbuffer) hcpt hsource hmetric] at hmem
    obtain ⟨x, hx, hxy⟩ := hmem
    refine ⟨x, ?_, hxy⟩
    exact hx.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hr).mpr hdr)

end IsometricBalls

section PartialDiffeomorphImages

variable {P Q : Type*} [TopologicalSpace P] [TopologicalSpace Q]
  [ChartedSpace ThreeSpace P] [ChartedSpace ThreeSpace Q]

private theorem partialDiffeomorph_injOn_of_subset_source_lift (F : PartialDiffeomorph I3 I3 P Q ∞)
    {s : Set P} (hs : s ⊆ F.source) : InjOn (F : P → Q) s := by
  intro x hx y hy hxy
  have h := congrArg F.invFun hxy
  rwa [F.left_inv' (hs hx), F.left_inv' (hs hy)] at h

private theorem partialDiffeomorph_image_inter_of_subset_source_lift
    (F : PartialDiffeomorph I3 I3 P Q ∞) {s t : Set P} (hs : s ⊆ F.source) (ht : t ⊆ F.source) :
    F '' (s ∩ t) = F '' s ∩ F '' t :=
  Set.image_inter_on fun _x hx _y hy hxy =>
    partialDiffeomorph_injOn_of_subset_source_lift F (Set.union_subset hs ht)
      (Or.inr hx) (Or.inl hy) hxy

private theorem partialDiffeomorph_image_interior_of_subset_source_lift
    (F : PartialDiffeomorph I3 I3 P Q ∞) {s : Set P} (hs : s ⊆ F.source) :
    F '' interior s = interior (F '' s) :=
  F.toOpenPartialHomeomorph.image_interior_of_subset_source hs

private theorem partialDiffeomorph_image_frontier_of_subset_source_lift
    (F : PartialDiffeomorph I3 I3 P Q ∞) {s : Set P} (hs : s ⊆ F.source) (hsc : IsClosed s)
    (htc : IsClosed (F '' s)) :
    F '' frontier s = frontier (F '' s) :=
  F.toOpenPartialHomeomorph.image_frontier_of_subset_source hs hsc htc

end PartialDiffeomorphImages

section ULiftModels

variable {Z : Type v} [TopologicalSpace Z] [ChartedSpace ThreeSpace Z] [IsManifold I3 ∞ Z]

omit [TopologicalSpace Z] [ChartedSpace ThreeSpace Z] [IsManifold I3 ∞ Z] in
private theorem down_image_compl_up_image (T : Set Z) :
    (ULift.down : ULift.{u} Z → Z) '' (ULift.up '' T)ᶜ = Tᶜ := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩ hz
    exact hy ⟨y.down, hz, rfl⟩
  · intro hz
    refine ⟨ULift.up z, ?_, rfl⟩
    rintro ⟨w, hw, hwz⟩
    exact hz (ULift.up_injective hwz ▸ hw)

private def projectivePresentationULift (pr : ProjectivePresentation Z) :
    ProjectivePresentation (ULift.{u} Z) where
  quotient a := ULift.up (pr.quotient a)
  smooth := (uliftDiffeomorph I3 Z : Z ≃ₘ⟮I3, I3⟯ ULift.{u} Z).contMDiff.comp pr.smooth
  onto y := by
    obtain ⟨a, ha⟩ := pr.onto y.down
    exact ⟨a, ULift.ext _ _ ha⟩
  fibers a b := by
    rw [ULift.up_inj]
    exact pr.fibers a b
  local_diffeo a := by
    have : IsManifold I3 ∞ (ULift.{u} Z) := isManifold_ulift I3 Z
    let Ψ : Z ≃ₘ⟮I3, I3⟯ ULift.{u} Z := uliftDiffeomorph I3 Z
    have hΨ : IsLocalDiffeomorph I3 I3 ∞ Ψ := Ψ.isLocalDiffeomorph
    have hU : MDifferentiableAt I3 I3 Ψ (pr.quotient a) :=
      Ψ.contMDiff.mdifferentiableAt (by decide)
    have hq : MDifferentiableAt (𝓡 3) I3 pr.quotient a := pr.smooth.mdifferentiableAt (by decide)
    have hc := mfderiv_comp a hU hq
    change Function.Bijective (mfderiv (𝓡 3) I3 (Ψ ∘ pr.quotient) a)
    rw [hc, ContinuousLinearMap.coe_comp]
    refine Function.Bijective.comp ?_ (pr.local_diffeo a)
    rw [← hΨ.mfderivToContinuousLinearEquiv_coe (by decide)]
    exact (hΨ.mfderivToContinuousLinearEquiv (by decide) (pr.quotient a)).bijective

private theorem capCore_transport_of_partialDiffeomorph_lift {P : Type v} {M : Type (max u v)}
    [TopologicalSpace P] [ChartedSpace ThreeSpace P]
    [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    {X : Set P} (c : CapCore (M := P) X) (e : PartialDiffeomorph I3 I3 P M ∞)
    (he : X ⊆ e.source) : Nonempty (CapCore (M := M) (e '' X)) := by
  cases c with
  | ball F h hx =>
    rw [← hx]
    exact ⟨CapCore.ball (PartialDiffeomorph.trans F e)
      (fun y hy => ⟨h hy, he (hx ▸ ⟨y, hy, rfl⟩)⟩)
      (by rw [partialDiffeomorph_image_trans])⟩
  | projective Z pr ball hb F hc hx =>
    have : IsManifold I3 ∞ (ULift.{u} Z) := isManifold_ulift I3 Z
    let Ψ : Z ≃ₘ⟮I3, I3⟯ ULift.{u} Z := uliftDiffeomorph I3 Z
    let Φ : ULift.{u} Z ≃ₘ⟮I3, I3⟯ Z := (uliftDiffeomorph I3 Z).symm
    have hball : (ball.trans Ψ.toPartialDiffeomorph) '' Metric.ball (0 : ThreeSpace) 1 =
        ULift.up '' (ball '' Metric.ball (0 : ThreeSpace) 1) :=
      partialDiffeomorph_image_trans _ _ _
    rw [← hx]
    refine ⟨CapCore.projective (ULift.{u} Z) (projectivePresentationULift pr)
      (ball.trans Ψ.toPartialDiffeomorph) (fun y hy => ⟨hb hy, trivial⟩)
      (Φ.toPartialDiffeomorph.trans (F.trans e)) ?_ ?_⟩
    · intro y hy
      rw [hball] at hy
      have hy' : y.down ∈ (ball '' Metric.ball (0 : ThreeSpace) 1)ᶜ :=
        down_image_compl_up_image _ ▸ ⟨y, hy, rfl⟩
      exact ⟨trivial, hc hy', he (hx ▸ ⟨y.down, hy', rfl⟩)⟩
    · rw [hball, partialDiffeomorph_image_trans, partialDiffeomorph_image_trans]
      change e '' (F '' ((ULift.down : ULift.{u} Z → Z) '' _)) = _
      rw [down_image_compl_up_image]

private theorem positiveComponent_transport_of_partialDiffeomorph_lift {P : Type v}
    {M : Type (max u v)}
    [TopologicalSpace P] [ChartedSpace ThreeSpace P]
    [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    {U : Set P} (c : PositiveComponent (M := P) U)
    (e : PartialDiffeomorph I3 I3 P M ∞) (he : U ⊆ e.source) :
    Nonempty (PositiveComponent (M := M) (e '' U)) := by
  cases c with
  | sphere F hsrc htgt =>
    rw [← htgt]
    refine ⟨PositiveComponent.sphere (PartialDiffeomorph.trans F e) ?_ ?_⟩
    · rw [partialDiffeomorph_trans_source, hsrc, univ_inter]
      exact Set.eq_univ_of_forall fun z =>
        he (htgt ▸ PartialEquiv.map_source F.toPartialEquiv (hsrc.symm ▸ Set.mem_univ z))
    · rw [partialDiffeomorph_trans_target, htgt]
      exact congrArg (fun s => ↑e.toPartialEquiv '' s) (Set.inter_eq_self_of_subset_right he)
  | projective Z pr F hsrc htgt =>
    have : IsManifold I3 ∞ (ULift.{u} Z) := isManifold_ulift I3 Z
    let Φ : ULift.{u} Z ≃ₘ⟮I3, I3⟯ Z := (uliftDiffeomorph I3 Z).symm
    have hG : (F.trans e).source = univ := by
      rw [partialDiffeomorph_trans_source, hsrc, univ_inter]
      exact Set.eq_univ_of_forall fun z =>
        he (htgt ▸ PartialEquiv.map_source F.toPartialEquiv (hsrc.symm ▸ Set.mem_univ z))
    refine ⟨PositiveComponent.projective (ULift.{u} Z) (projectivePresentationULift pr)
      (Φ.toPartialDiffeomorph.trans (F.trans e)) ?_ ?_⟩
    · rw [partialDiffeomorph_trans_source, hG]
      exact inter_univ _
    · have ht : (Φ.toPartialDiffeomorph).target = univ := rfl
      rw [partialDiffeomorph_trans_target, hG, univ_inter, ht, partialDiffeomorph_image_trans,
        ← hsrc, F.toPartialEquiv.image_source_eq_target, htgt]

end ULiftModels

section Precomposition

variable {Z' : Type*} [TopologicalSpace Z'] [ChartedSpace ThreeSpace Z'] [IsManifold I3 ∞ Z']
  [T2Space Z'] [SigmaCompactSpace Z']
  {Z : Type*} [TopologicalSpace Z] [ChartedSpace ThreeSpace Z] [IsManifold I3 ∞ Z]
  [T2Space Z] [SigmaCompactSpace Z]
  {P : Type*} [TopologicalSpace P] [ChartedSpace ThreeSpace P] [IsManifold I3 ∞ P]

private def MetricComparisonOn.precompDiffeomorph {k : SmoothRiemannianMetric I3 Z}
    {gP : ℝ → SmoothRiemannianMetric I3 P} {F : Z → P} {V : Set Z} {times : Set ℝ}
    {order : ℕ} {eps : ℝ} (C : MetricComparisonOn (fun _ => k) gP F V times order eps)
    (Φ : Z' ≃ₘ⟮I3, I3⟯ Z) {V' : Set Z'} (hV : ∀ y ∈ V', Φ y ∈ V)
    (hF : ∀ y ∈ V, MDifferentiableAt I3 I3 F y) :
    MetricComparisonOn (fun _ => DifferentialGeometry.Diffeomorph.pullbackMetricCross k Φ) gP
      (fun y => F (Φ y)) V' times order eps where
  pullback s := pullbackTensor02FieldCross Φ (C.pullback s)
  pullback_eq s y hy v := by
    have hc : mfderiv I3 I3 (fun y => F (Φ y)) y =
        (mfderiv I3 I3 F (Φ y)).comp (mfderiv I3 I3 Φ y) :=
      mfderiv_comp y (hF _ (hV y hy)) (Φ.contMDiff.mdifferentiableAt (by decide))
    rw [pullbackTensor02FieldCross_apply, C.pullback_eq s (Φ y) (hV y hy), hc]
    rfl
  jet b s := pullbackTensor02FieldCross Φ (C.jet b s)
  jet_zero s y v := by
    rw [pullbackTensor02FieldCross_apply, C.jet_zero, pullbackTensor02FieldCross_apply,
      DifferentialGeometry.Diffeomorph.pullbackMetricCross_inner]
  jet_succ b s hs y hy v := by
    have hfun : (fun a => pullbackTensor02FieldCross Φ (C.jet b a) y v) =
        fun a => C.jet b a (Φ y) (fun q => mfderiv I3 I3 Φ y (v q)) := by
      funext a
      exact pullbackTensor02FieldCross_apply Φ (C.jet b a) y v
    rw [pullbackTensor02FieldCross_apply, hfun]
    exact C.jet_succ b s hs (Φ y) (hV y hy) _
  equivalence s hs y hy v := by
    have h0 := C.equivalence s hs (Φ y) (hV y hy) (mfderiv I3 I3 Φ y v)
    rw [pullbackTensor02FieldCross_apply,
      DifferentialGeometry.Diffeomorph.pullbackMetricCross_inner]
    exact h0
  close a b hab s hs y hy := by
    rw [tensor02CovDerivNormWith_pullbackTensor02FieldCross k k Φ (C.jet b s) a y]
    exact C.close a b hab s hs (Φ y) (hV y hy)

end Precomposition

variable {M : Type (max u v)} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {g : SmoothRiemannianMetric I3 M} {eps C C1 C2 alpha : ℝ} {x : M} {U : Set M}

section Isometry

variable {N : Type v} [TopologicalSpace N] [ChartedSpace ThreeSpace N] [IsManifold I3 ∞ N]
  [T2Space N] [SigmaCompactSpace N] {h : SmoothRiemannianMetric I3 N}

private def isoSource (e : PartialDiffeomorph I3 I3 N M ∞) : TopologicalSpace.Opens N :=
  ⟨e.source, e.open_source⟩

omit [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M] [IsManifold I3 ∞ N] [T2Space N]
  [SigmaCompactSpace N] in
private theorem isLocalDiffeomorph_isoSource (e : PartialDiffeomorph I3 I3 N M ∞) :
    IsLocalDiffeomorph I3 I3 ∞ (fun p : isoSource e => e p) := fun p =>
  IsLocalDiffeomorphAt.comp (K := I3) (P := M) (isLocalDiffeomorph_subtype_val (isoSource e) p)
    (e.isLocalDiffeomorphAt I3 I3 ∞ p.2)

omit [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M] [IsManifold I3 ∞ N] [T2Space N]
  [SigmaCompactSpace N] in
private theorem mfderiv_isoSource (e : PartialDiffeomorph I3 I3 N M ∞) (p : isoSource e)
    (v : TangentSpace I3 p) :
    mfderiv I3 I3 (fun q : isoSource e => e q) p v = mfderiv I3 I3 e p v := by
  have he : MDifferentiableAt I3 I3 e (p : N) := e.mdifferentiableAt (by decide) p.2
  have hv : MDifferentiableAt I3 I3 (Subtype.val : isoSource e → N) p :=
    (isLocalDiffeomorph_subtype_val (isoSource e)).mdifferentiable (by decide) p
  have hc : mfderiv I3 I3 (fun q : isoSource e => e q) p =
      (mfderiv I3 I3 e p).comp (mfderiv I3 I3 (Subtype.val : isoSource e → N) p) :=
    mfderiv_comp p he hv
  rw [hc, ContinuousLinearMap.comp_apply, mfderiv_subtype_val_apply]

omit [T2Space M] [SigmaCompactSpace M] [SigmaCompactSpace N] in
private theorem localPull_isoSource_eq (e : PartialDiffeomorph I3 I3 N M ∞)
    (hiso : ∀ z ∈ e.source, ∀ v w : TangentSpace I3 z,
      g.inner (e z) (mfderiv I3 I3 e z v) (mfderiv I3 I3 e z w) = h.inner z v w) :
    localPullMetric h (Subtype.val : isoSource e → N) (isLocalDiffeomorph_subtype_val _) =
      localPullMetric g (fun q : isoSource e => e q) (isLocalDiffeomorph_isoSource e) := by
  apply SmoothRiemannianMetric.ext_inner
  intro p v w
  rw [localPullMetric_inner, localPullMetric_inner, mfderiv_isoSource, mfderiv_isoSource,
    mfderiv_subtype_val_apply, mfderiv_subtype_val_apply]
  exact (hiso p p.2 v w).symm

omit [SigmaCompactSpace M] [SigmaCompactSpace N] in
private theorem metricScalarAt_eq_of_isometryOn_lift (e : PartialDiffeomorph I3 I3 N M ∞)
    (hiso : ∀ z ∈ e.source, ∀ v w : TangentSpace I3 z,
      g.inner (e z) (mfderiv I3 I3 e z v) (mfderiv I3 I3 e z w) = h.inner z v w)
    {z : N} (hz : z ∈ e.source) : metricScalarAt g (e z) = metricScalarAt h z := by
  have h1 := metricScalarAt_localPull h (Subtype.val : isoSource e → N)
    (isLocalDiffeomorph_subtype_val _) ⟨z, hz⟩
  have h2 := metricScalarAt_localPull g (fun q : isoSource e => e q)
    (isLocalDiffeomorph_isoSource e) ⟨z, hz⟩
  rw [localPull_isoSource_eq e hiso] at h1
  exact h2.symm.trans h1

omit [SigmaCompactSpace M] [SigmaCompactSpace N] in
private theorem rmNormSq_eq_of_isometryOn_lift (e : PartialDiffeomorph I3 I3 N M ∞)
    (hiso : ∀ z ∈ e.source, ∀ v w : TangentSpace I3 z,
      g.inner (e z) (mfderiv I3 I3 e z v) (mfderiv I3 I3 e z w) = h.inner z v w)
    {z : N} (hz : z ∈ e.source) :
    normSq0S g (e z) 4 (metricRm04At g (e z)) = normSq0S h z 4 (metricRm04At h z) := by
  have h1 := normSq0S_metricRm04At_localPullMetric h (Subtype.val : isoSource e → N)
    (isLocalDiffeomorph_subtype_val _) ⟨z, hz⟩
  have h2 := normSq0S_metricRm04At_localPullMetric g (fun q : isoSource e => e q)
    (isLocalDiffeomorph_isoSource e) ⟨z, hz⟩
  rw [localPull_isoSource_eq e hiso] at h1
  exact h2.symm.trans h1

omit [SigmaCompactSpace M] [SigmaCompactSpace N] in
private theorem metricRm04At_eq_of_isometryOn_lift (e : PartialDiffeomorph I3 I3 N M ∞)
    (hiso : ∀ z ∈ e.source, ∀ v w : TangentSpace I3 z,
      g.inner (e z) (mfderiv I3 I3 e z v) (mfderiv I3 I3 e z w) = h.inner z v w)
    {z : N} (hz : z ∈ e.source) (u : Fin 4 → TangentSpace I3 z) :
    metricRm04At g (e z) (fun i => mfderiv I3 I3 e z (u i)) = metricRm04At h z u := by
  have h1 := DifferentialGeometry.Geometry.Tensor.metricRm04At_localPullMetric h
    (Subtype.val : isoSource e → N) (isLocalDiffeomorph_subtype_val _) ⟨z, hz⟩ u
  have h2 := DifferentialGeometry.Geometry.Tensor.metricRm04At_localPullMetric g
    (fun q : isoSource e => e q) (isLocalDiffeomorph_isoSource e) ⟨z, hz⟩ u
  rw [localPull_isoSource_eq e hiso] at h1
  calc metricRm04At g (e z) (fun i => mfderiv I3 I3 e z (u i))
      = metricRm04At g (e z) (fun i => mfderiv I3 I3 (fun q : isoSource e => e q)
          (⟨z, hz⟩ : isoSource e) (u i)) := by
        congr 1
        funext i
        exact (mfderiv_isoSource e ⟨z, hz⟩ (u i)).symm
    _ = metricRm04At h z (fun i => mfderiv I3 I3 (Subtype.val : isoSource e → N)
          (⟨z, hz⟩ : isoSource e) (u i)) := h2.symm.trans h1
    _ = metricRm04At h z u := by
        congr 1
        funext i
        exact mfderiv_subtype_val_apply (isoSource e) ⟨z, hz⟩ (u i)

omit [SigmaCompactSpace M] [SigmaCompactSpace N] in
private theorem mfderiv_metricScalarAt_eq_of_isometryOn_lift (e : PartialDiffeomorph I3 I3 N M ∞)
    (hiso : ∀ z ∈ e.source, ∀ v w : TangentSpace I3 z,
      g.inner (e z) (mfderiv I3 I3 e z v) (mfderiv I3 I3 e z w) = h.inner z v w)
    {z : N} (hz : z ∈ e.source) (v : TangentSpace I3 z) :
    (show ℝ from mfderiv I3 𝓘(ℝ, ℝ) (metricScalarAt g) (e z) (mfderiv I3 I3 e z v)) =
      mfderiv I3 𝓘(ℝ, ℝ) (metricScalarAt h) z v := by
  let p : isoSource e := ⟨z, hz⟩
  have hfun : (fun q : isoSource e => metricScalarAt h q) =
      fun q : isoSource e => metricScalarAt g (e q) :=
    funext fun q => (metricScalarAt_eq_of_isometryOn_lift e hiso q.2).symm
  have hh : MDifferentiableAt I3 𝓘(ℝ, ℝ) (metricScalarAt h) z :=
    (metricScalar_smooth h).mdifferentiableAt (by simp)
  have hg : MDifferentiableAt I3 𝓘(ℝ, ℝ) (metricScalarAt g) (e z) :=
    (metricScalar_smooth g).mdifferentiableAt (by simp)
  have hval : MDifferentiableAt I3 I3 (Subtype.val : isoSource e → N) p :=
    (isLocalDiffeomorph_subtype_val (isoSource e)).mdifferentiable (by decide) p
  have hphi : MDifferentiableAt I3 I3 (fun q : isoSource e => e q) p :=
    (isLocalDiffeomorph_isoSource e).mdifferentiable (by decide) p
  have h4 : mfderiv I3 I3 (Subtype.val : isoSource e → N) p v = v :=
    mfderiv_subtype_val_apply (I := I3) (isoSource e) p v
  have h5 : mfderiv I3 I3 (fun q : isoSource e => e q) p v = mfderiv I3 I3 e z v :=
    mfderiv_isoSource e p v
  have h0 : (show ℝ from mfderiv I3 𝓘(ℝ, ℝ) (fun q : isoSource e => metricScalarAt h q) p v) =
      (show ℝ from mfderiv I3 𝓘(ℝ, ℝ) (fun q : isoSource e => metricScalarAt g (e q)) p v) :=
    congrArg (fun f : isoSource e → ℝ => (show ℝ from mfderiv I3 𝓘(ℝ, ℝ) f p v)) hfun
  have hA : (show ℝ from mfderiv I3 𝓘(ℝ, ℝ) (fun q : isoSource e => metricScalarAt h q) p v) =
      (show ℝ from mfderiv I3 𝓘(ℝ, ℝ) (metricScalarAt h) z v) := by
    have hc := mfderiv_comp_apply p hh hval v
    rw [h4] at hc
    exact hc
  have hB : (show ℝ from
        mfderiv I3 𝓘(ℝ, ℝ) (fun q : isoSource e => metricScalarAt g (e q)) p v) =
      (show ℝ from mfderiv I3 𝓘(ℝ, ℝ) (metricScalarAt g) (e z) (mfderiv I3 I3 e z v)) := by
    have hc := mfderiv_comp_apply p hg hphi v
    rw [h5] at hc
    exact hc
  exact hB.symm.trans (h0.symm.trans hA)

omit [SigmaCompactSpace M] [SigmaCompactSpace N] in
private theorem secLower_image_of_isometryOn_lift (e : PartialDiffeomorph I3 I3 N M ∞)
    (hiso : ∀ z ∈ e.source, ∀ v w : TangentSpace I3 z,
      g.inner (e z) (mfderiv I3 I3 e z v) (mfderiv I3 I3 e z w) = h.inner z v w)
    {K : ℝ} {V : Set N} (hV : V ⊆ e.source) (hsec : SecLower h K V) :
    SecLower g K (e '' V) := by
  rintro _ ⟨y, hy, rfl⟩ v' w'
  let L := (e.isLocalDiffeomorphAt I3 I3 ∞ (hV hy)).mfderivToContinuousLinearEquiv (by simp)
  have hL : ∀ u, L u = mfderiv I3 I3 e y u := fun u => rfl
  obtain ⟨v, rfl⟩ := L.surjective v'
  obtain ⟨w, rfl⟩ := L.surjective w'
  rw [hL, hL, hiso y (hV hy), hiso y (hV hy), hiso y (hV hy)]
  have hrm := metricRm04At_eq_of_isometryOn_lift e hiso (hV hy) (fun i : Fin 4 => ![v, w, w, v] i)
  have hvec : (fun i : Fin 4 => mfderiv I3 I3 e y (![v, w, w, v] i)) =
      fun i : Fin 4 => ![mfderiv I3 I3 e y v, mfderiv I3 I3 e y w, mfderiv I3 I3 e y w,
        mfderiv I3 I3 e y v] i := by
    funext i
    fin_cases i <;> rfl
  rw [hvec] at hrm
  rw [hrm]
  exact hsec y hy v w

end Isometry


section Transport

variable {N : Type v} [TopologicalSpace N] [ChartedSpace ThreeSpace N] [IsManifold I3 ∞ N]
  [T2Space N] [SigmaCompactSpace N] {h : SmoothRiemannianMetric I3 N}

omit [T2Space M] [SigmaCompactSpace M] in
private def MetricComparisonOn.mapIsometryLift {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [FiniteDimensional ℝ E'] [CompleteSpace E'] {H' : Type*} [TopologicalSpace H']
    {J : ModelWithCorners ℝ E' H'} {Z : Type*} [TopologicalSpace Z] [ChartedSpace H' Z]
    [IsManifold J ∞ Z] [T2Space Z] [SigmaCompactSpace Z]
    {k : ℝ → SmoothRiemannianMetric J Z} {g₁ : ℝ → SmoothRiemannianMetric I3 N}
    {g₂ : ℝ → SmoothRiemannianMetric I3 M} {F : Z → N} {V : Set Z} {times : Set ℝ}
    {order : ℕ} {eps : ℝ} (C : MetricComparisonOn k g₁ F V times order eps)
    (e : PartialDiffeomorph I3 I3 N M ∞)
    (hiso : ∀ s, ∀ z ∈ e.source, ∀ v w : TangentSpace I3 z,
      (g₂ s).inner (e z) (mfderiv I3 I3 e z v) (mfderiv I3 I3 e z w) = (g₁ s).inner z v w)
    (hF : ∀ y ∈ V, MDifferentiableAt J I3 F y) (hV : ∀ y ∈ V, F y ∈ e.source) :
    MetricComparisonOn k g₂ (fun y => e (F y)) V times order eps where
  pullback := C.pullback
  pullback_eq s y hy v := by
    have hc : mfderiv J I3 (fun y => e (F y)) y =
        (mfderiv I3 I3 e (F y)).comp (mfderiv J I3 F y) :=
      mfderiv_comp y (e.mdifferentiableAt (by decide) (hV y hy)) (hF y hy)
    rw [C.pullback_eq s y hy v, hc, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.comp_apply, hiso s (F y) (hV y hy)]
  jet := C.jet
  jet_zero := C.jet_zero
  jet_succ := C.jet_succ
  equivalence := C.equivalence
  close := C.close

omit [SigmaCompactSpace M] [SigmaCompactSpace N] in
private theorem scaleMetric_isometryOn (e : PartialDiffeomorph I3 I3 N M ∞)
    (hiso : ∀ z ∈ e.source, ∀ v w : TangentSpace I3 z,
      g.inner (e z) (mfderiv I3 I3 e z v) (mfderiv I3 I3 e z w) = h.inner z v w)
    {p : N} (hp : p ∈ e.source) (hQ : 0 < metricScalarAt h p)
    (hQ' : 0 < metricScalarAt g (e p)) :
    ∀ (_ : ℝ), ∀ z ∈ e.source, ∀ v w : TangentSpace I3 z,
      (DifferentialGeometry.scaleMetric (metricScalarAt g (e p)) hQ' g).inner (e z)
          (mfderiv I3 I3 e z v) (mfderiv I3 I3 e z w) =
        (DifferentialGeometry.scaleMetric (metricScalarAt h p) hQ h).inner z v w := by
  intro _ z hz v w
  rw [scaleMetric_inner, scaleMetric_inner, metricScalarAt_eq_of_isometryOn_lift e hiso hp,
    hiso z hz v w]

omit [T2Space M] [SigmaCompactSpace M] [T2Space N] [SigmaCompactSpace N] in
private theorem center_mem_neckWindow {eps : ℝ} (heps : 0 < eps) (c : Sphere 2) :
    ((c, 0) : Cylinder) ∈ (univ ×ˢ Ioo (-eps⁻¹) eps⁻¹ : Set Cylinder) :=
  ⟨trivial, neg_neg_of_pos (inv_pos.mpr heps), inv_pos.mpr heps⟩

omit [SigmaCompactSpace M] [SigmaCompactSpace N] in
private def SpatialNeck.pushforwardLift {p : N} (nk : SpatialNeck h eps p) (e : PartialDiffeomorph I3 I3 N M ∞)
    (hiso : ∀ z ∈ e.source, ∀ v w : TangentSpace I3 z,
      g.inner (e z) (mfderiv I3 I3 e z v) (mfderiv I3 I3 e z w) = h.inner z v w)
    (hwin : ∀ z ∈ univ ×ˢ Ioo (-eps⁻¹) eps⁻¹, nk.map z ∈ e.source) :
    SpatialNeck g eps (e p) := by
  have hp : p ∈ e.source := by
    have h0 := hwin _ (center_mem_neckWindow nk.eps_pos nk.center)
    rwa [nk.center_eq] at h0
  have hQ : 0 < metricScalarAt g (e p) := by
    rw [metricScalarAt_eq_of_isometryOn_lift e hiso hp]
    exact nk.Q_pos
  exact {
    eps_pos := nk.eps_pos
    eps_small := nk.eps_small
    Q_pos := hQ
    cylinder := nk.cylinder
    map := nk.map.trans e
    center := nk.center
    center_eq := by rw [partialDiffeomorph_trans_apply, nk.center_eq]
    domain := fun z hz => ⟨nk.domain hz, hwin z hz⟩
    comparison := nk.comparison.mapIsometryLift e
      (scaleMetric_isometryOn e hiso hp nk.Q_pos hQ)
      (fun y hy => nk.map.mdifferentiableAt (by decide) (nk.domain hy)) hwin }

omit [SigmaCompactSpace M] [SigmaCompactSpace N] in
@[simp] private theorem SpatialNeck.pushforwardLift_map {p : N} (nk : SpatialNeck h eps p)
    (e : PartialDiffeomorph I3 I3 N M ∞)
    (hiso : ∀ z ∈ e.source, ∀ v w : TangentSpace I3 z,
      g.inner (e z) (mfderiv I3 I3 e z v) (mfderiv I3 I3 e z w) = h.inner z v w)
    (hwin : ∀ z ∈ univ ×ˢ Ioo (-eps⁻¹) eps⁻¹, nk.map z ∈ e.source) :
    (nk.pushforwardLift e hiso hwin).map = nk.map.trans e := rfl

omit [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M] [IsManifold I3 ∞ N] [T2Space N]
  [SigmaCompactSpace N] in
private theorem axial_fderiv_trans_eq (m₀ m₁ : PartialDiffeomorph IC I3 Cylinder N ∞)
    (e : PartialDiffeomorph I3 I3 N M ∞) {z : Cylinder} (hz : z ∈ m₀.source)
    (hzs : m₀ z ∈ e.source) :
    fderiv ℝ (fun a : ℝ => ((m₁.trans e).symm ((m₀.trans e) (z.1, a))).2) z.2 1 =
      fderiv ℝ (fun a : ℝ => (m₁.symm (m₀ (z.1, a))).2) z.2 1 := by
  have hev : (fun a : ℝ => ((m₁.trans e).symm ((m₀.trans e) (z.1, a))).2) =ᶠ[nhds z.2]
      fun a : ℝ => (m₁.symm (m₀ (z.1, a))).2 := by
    have hmem : {a : ℝ | (z.1, a) ∈ m₀.source ∧ m₀ (z.1, a) ∈ e.source} ∈ nhds z.2 := by
      have hc : ContinuousAt (fun a : ℝ => m₀ (z.1, a)) z.2 :=
        (m₀.contMDiffOn_toFun.continuousOn.continuousAt
          (m₀.open_source.mem_nhds hz)).comp
          (continuous_const.continuousAt.prodMk continuous_id.continuousAt)
      exact Filter.inter_mem
        ((m₀.open_source.preimage (continuous_const.prodMk continuous_id)).mem_nhds hz)
        (hc.preimage_mem_nhds (e.open_source.mem_nhds hzs))
    refine Filter.eventually_of_mem hmem ?_
    intro a ha
    simp only [partialDiffeomorph_trans_apply, PartialDiffeomorph.trans_symm_apply _ _ ha.2]
  rw [hev.fderiv_eq]

omit [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M] [IsManifold I3 ∞ N] [T2Space N]
  [SigmaCompactSpace N] in
private def SpatialOrderedNeckChain.transportLift {g' : SmoothRiemannianMetric I3 M} {eps' : ℝ} {V : Set N}
    (ch : SpatialOrderedNeckChain h eps V) (e : PartialDiffeomorph I3 I3 N M ∞)
    (hV : V ⊆ e.source) (necks : ∀ i, SpatialNeck g' eps' (e (ch.centers i)))
    (hmap : ∀ i, (necks i).map = (ch.necks i).map.trans e) :
    SpatialOrderedNeckChain g' eps' (e '' V) where
  count := ch.count
  count_pos := ch.count_pos
  centers i := e (ch.centers i)
  necks := necks
  lo := ch.lo
  hi := ch.hi
  lo_lt_hi := ch.lo_lt_hi
  inside := by
    intro i z hz
    have hVmem : (ch.necks i).map z ∈ V :=
      ch.swept_eq.ge (mem_iUnion.mpr ⟨i, z, hz, rfl⟩)
    rw [hmap i]
    exact ⟨ch.inside i hz, hV hVmem⟩
  swept_eq := by
    have h0 := congrArg (fun s => e '' s) ch.swept_eq
    simp only [image_iUnion] at h0
    rw [h0]
    simp only [hmap, partialDiffeomorph_image_trans]
  transition_increasing := by
    intro i j hij z hz hmem
    rw [hmap i, partialDiffeomorph_trans_source] at hz
    rw [hmap i, hmap j, partialDiffeomorph_trans_target] at hmem
    rw [hmap i, hmap j, axial_fderiv_trans_eq _ _ e hz.1 hz.2]
    apply ch.transition_increasing i j hij z hz.1
    obtain ⟨w, ⟨hw1, hw2⟩, hwe⟩ := hmem
    have hw : w = (ch.necks i).map z :=
      partialDiffeomorph_injOn_of_subset_source_lift e (subset_refl e.source) hw1 hz.2 hwe
    rwa [hw] at hw2

omit [SigmaCompactSpace M] [SigmaCompactSpace N] in
private def SpatialOrderedNeckChain.pushforwardLift {V : Set N} (ch : SpatialOrderedNeckChain h eps V)
    (e : PartialDiffeomorph I3 I3 N M ∞)
    (hiso : ∀ z ∈ e.source, ∀ v w : TangentSpace I3 z,
      g.inner (e z) (mfderiv I3 I3 e z v) (mfderiv I3 I3 e z w) = h.inner z v w)
    (hV : V ⊆ e.source)
    (hwin : ∀ i, ∀ z ∈ univ ×ˢ Ioo (-eps⁻¹) eps⁻¹, (ch.necks i).map z ∈ e.source) :
    SpatialOrderedNeckChain g eps (e '' V) :=
  ch.transportLift e hV (fun i => (ch.necks i).pushforwardLift e hiso (hwin i)) fun _ => rfl

omit [SigmaCompactSpace M] [SigmaCompactSpace N] in
private def SpatialLocalNeck.pushforwardLift {x : N} {V : Set N} (n : SpatialLocalNeck h eps x V)
    (e : PartialDiffeomorph I3 I3 N M ∞)
    (hiso : ∀ z ∈ e.source, ∀ v w : TangentSpace I3 z,
      g.inner (e z) (mfderiv I3 I3 e z v) (mfderiv I3 I3 e z w) = h.inner z v w)
    (hV : V ⊆ e.source) (hVc : IsCompact V)
    (hwin : ∀ z ∈ univ ×ˢ Ioo (-eps⁻¹) eps⁻¹, n.neck.map z ∈ e.source) :
    SpatialLocalNeck g eps (e x) (e '' V) where
  neck := n.neck.pushforwardLift e hiso hwin
  region_eq := by
    rw [SpatialNeck.pushforwardLift_map, partialDiffeomorph_image_trans]
    exact congrArg (fun s => e '' s) n.region_eq
  boundary_eq := by
    have hc : IsCompact (e '' V) :=
      hVc.image_of_continuousOn (e.contMDiffOn_toFun.continuousOn.mono hV)
    rw [← partialDiffeomorph_image_frontier_of_subset_source_lift e hV hVc.isClosed hc.isClosed,
      SpatialNeck.pushforwardLift_map, partialDiffeomorph_image_trans]
    exact congrArg (fun s => e '' s) n.boundary_eq

private def SpatialLocalCap.pushforwardLift {eps' : ℝ} {x : N} {V : Set N} (L : SpatialLocalCap h eps x V)
    (e : PartialDiffeomorph I3 I3 N M ∞) (hV : V ⊆ e.source) (hVc : IsCompact V)
    (chain : SpatialOrderedNeckChain g eps' (e '' L.tube)) :
    SpatialLocalCap g eps' (e x) (e '' V) := by
  have hcore : L.core.carrier ⊆ e.source :=
    (subset_union_left.trans L.union_eq.ge).trans hV
  have htube : L.tube ⊆ e.source := (subset_union_right.trans L.union_eq.ge).trans hV
  have hcoreC : IsClosed L.core.carrier := L.core.compact.isClosed
  have htubeC : IsClosed L.tube := L.isCompact_tube.isClosed
  have himg : ∀ {s : Set N}, s ⊆ e.source → IsCompact s → IsClosed (e '' s) := fun hs hsc =>
    (hsc.image_of_continuousOn (e.contMDiffOn_toFun.continuousOn.mono hs)).isClosed
  have hecore := himg hcore L.core.compact
  have hetube := himg htube L.isCompact_tube
  have heV := himg hV hVc
  refine {
    core := L.core.map e hcore
    core_inside := ?_
    center_inside := ?_
    coreModel := Classical.choice (capCore_transport_of_partialDiffeomorph_lift L.coreModel e hcore)
    tube := e '' L.tube
    tubeMap := L.tubeMap.trans e
    tube_domain := ?_
    tube_eq := ?_
    union_eq := ?_
    overlap_eq := ?_
    inner_boundary := ?_
    outer_boundary := ?_
    boundary_eq := ?_
    boundaries_disjoint := ?_
    chain := chain
    coreBoundaryMap := fun z => e (L.coreBoundaryMap z)
    core_boundary_eq := ?_ }
  · change e '' L.core.carrier ⊆ interior (e '' V)
    exact (image_mono L.core_inside).trans
      (le_of_eq (partialDiffeomorph_image_interior_of_subset_source_lift e hV))
  · change e x ∈ interior (e '' L.core.carrier)
    rw [← partialDiffeomorph_image_interior_of_subset_source_lift e hcore]
    exact ⟨x, L.center_inside, rfl⟩
  · intro z hz
    exact ⟨L.tube_domain hz, htube (L.tube_eq ▸ ⟨z, hz, rfl⟩)⟩
  · rw [partialDiffeomorph_image_trans, L.tube_eq]
  · change e '' V = e '' L.core.carrier ∪ e '' L.tube
    rw [← image_union]
    exact congrArg _ L.union_eq
  · change e '' L.core.carrier ∩ e '' L.tube = frontier (e '' L.core.carrier)
    rw [← partialDiffeomorph_image_inter_of_subset_source_lift e hcore htube, L.overlap_eq,
      partialDiffeomorph_image_frontier_of_subset_source_lift e hcore hcoreC hecore]
  · change (L.tubeMap.trans e) '' (univ ×ˢ ({0} : Set ℝ)) = frontier (e '' L.core.carrier)
    rw [partialDiffeomorph_image_trans, L.inner_boundary,
      partialDiffeomorph_image_frontier_of_subset_source_lift e hcore hcoreC hecore]
  · rw [partialDiffeomorph_image_trans, L.outer_boundary,
      partialDiffeomorph_image_frontier_of_subset_source_lift e hV hVc.isClosed heV]
  · change frontier (e '' L.tube) = frontier (e '' L.core.carrier) ∪ frontier (e '' V)
    rw [← partialDiffeomorph_image_frontier_of_subset_source_lift e htube htubeC hetube,
      L.boundary_eq, image_union,
      partialDiffeomorph_image_frontier_of_subset_source_lift e hcore hcoreC hecore,
      partialDiffeomorph_image_frontier_of_subset_source_lift e hV hVc.isClosed heV]
  · change Disjoint (frontier (e '' L.core.carrier)) (frontier (e '' V))
    rw [← partialDiffeomorph_image_frontier_of_subset_source_lift e hcore hcoreC hecore,
      ← partialDiffeomorph_image_frontier_of_subset_source_lift e hV hVc.isClosed heV]
    exact L.boundaries_disjoint.image
      (partialDiffeomorph_injOn_of_subset_source_lift e (subset_refl e.source))
      (hcoreC.frontier_subset.trans hcore) (hVc.isClosed.frontier_subset.trans hV)
  · intro z
    rw [partialDiffeomorph_trans_apply, L.core_boundary_eq]

omit [SigmaCompactSpace M] [SigmaCompactSpace N] in
private theorem SpatialLocalCap.pushforwardLift_tube {eps' : ℝ} {x : N} {V : Set N}
    (L : SpatialLocalCap h eps x V) (e : PartialDiffeomorph I3 I3 N M ∞) (hV : V ⊆ e.source)
    (hVc : IsCompact V) (chain : SpatialOrderedNeckChain g eps' (e '' L.tube)) :
    (L.pushforwardLift e hV hVc chain).tube = e '' L.tube := rfl

omit [SigmaCompactSpace M] [SigmaCompactSpace N] in
private theorem SpatialLocalCap.pushforwardLift_tubeMap {eps' : ℝ} {x : N} {V : Set N}
    (L : SpatialLocalCap h eps x V) (e : PartialDiffeomorph I3 I3 N M ∞) (hV : V ⊆ e.source)
    (hVc : IsCompact V) (chain : SpatialOrderedNeckChain g eps' (e '' L.tube)) :
    (L.pushforwardLift e hV hVc chain).tubeMap = L.tubeMap.trans e := rfl

omit [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M] [IsManifold I3 ∞ N] [T2Space N]
  [SigmaCompactSpace N] in
private theorem mfderiv_trans_apply {Z : Type*} [TopologicalSpace Z] [ChartedSpace ThreeSpace Z]
    (m : PartialDiffeomorph I3 I3 Z N ∞) (e : PartialDiffeomorph I3 I3 N M ∞) {z : Z}
    (hz : z ∈ m.source) (hez : m z ∈ e.source) (v : TangentSpace I3 z) :
    mfderiv I3 I3 (m.trans e) z v = mfderiv I3 I3 e (m z) (mfderiv I3 I3 m z v) :=
  mfderiv_comp_apply z (e.mdifferentiableAt (by decide) hez) (m.mdifferentiableAt (by decide) hz) v

omit [SigmaCompactSpace M] [SigmaCompactSpace N] in
private def SpatialRoundComponent.pushforwardLift {x : N} {V : Set N}
    (R : SpatialRoundComponent h eps x V) (e : PartialDiffeomorph I3 I3 N M ∞)
    (hiso : ∀ z ∈ e.source, ∀ v w : TangentSpace I3 z,
      g.inner (e z) (mfderiv I3 I3 e z v) (mfderiv I3 I3 e z w) = h.inner z v w)
    (hV : V ⊆ e.source) : SpatialRoundComponent g eps (e x) (e '' V) := by
  letI : TopologicalSpace R.Z := R.topology
  letI : ChartedSpace ThreeSpace R.Z := R.charted
  letI : IsManifold I3 ∞ R.Z := R.smooth
  letI : T2Space R.Z := R.t2
  letI : CompactSpace R.Z := R.compact
  letI : ConnectedSpace R.Z := R.connected
  letI : IsManifold I3 ∞ (ULift.{u} R.Z) := isManifold_ulift I3 R.Z
  letI : ConnectedSpace (ULift.{u} R.Z) :=
    ULift.up_surjective.connectedSpace continuous_uliftUp
  let Φ : ULift.{u} R.Z ≃ₘ⟮I3, I3⟯ R.Z := (uliftDiffeomorph I3 R.Z).symm
  have hsrc (y : R.Z) : y ∈ R.map.source := by rw [R.source_eq]; trivial
  have hmem (y : R.Z) : R.map y ∈ V := R.target_eq.subset (R.map.map_source (hsrc y))
  have hx : x ∈ e.source := by
    have h0 := hV (hmem R.p)
    rwa [R.center_eq] at h0
  have hR := metricScalarAt_eq_of_isometryOn_lift e hiso hx
  have hQ : 0 < metricScalarAt g (e x) := by
    rw [hR]
    exact R.Q_pos
  have hloc : DifferentialGeometry.Diffeomorph.pullbackMetricCross R.metric Φ =
      localPullMetric R.metric Φ Φ.isLocalDiffeomorph := by
    apply SmoothRiemannianMetric.ext_inner
    intro y v w
    rw [DifferentialGeometry.Diffeomorph.pullbackMetricCross_inner, localPullMetric_inner]
  have hd (y : R.Z) : MDifferentiableAt I3 I3 (fun z => e (R.map z)) y :=
    (e.mdifferentiableAt (by decide) (hV (hmem y))).comp y
      (R.map.mdifferentiableAt (by decide) (hsrc y))
  have hdΦ (y : ULift.{u} R.Z) : MDifferentiableAt I3 I3 Φ y :=
    Φ.contMDiff.mdifferentiableAt (by decide)
  let C0 := R.comparison.mapIsometryLift e (scaleMetric_isometryOn e hiso hx R.Q_pos hQ)
    (fun y _ => R.map.mdifferentiableAt (by decide) (hsrc y)) (fun y _ => hV (hmem y))
  exact {
    Z := ULift.{u} R.Z
    topology := inferInstance
    charted := uliftChartedSpace ThreeSpace R.Z
    smooth := isManifold_ulift I3 R.Z
    t2 := inferInstance
    compact := inferInstance
    connected := inferInstance
    metric := DifferentialGeometry.Diffeomorph.pullbackMetricCross R.metric Φ
    p := ULift.up R.p
    scalar_one := by
      intro z
      rw [hloc, metricScalarAt_localPull]
      exact R.scalar_one (Φ z)
    constant_curvature := by
      intro z v w
      rw [hloc, DifferentialGeometry.Geometry.Tensor.metricRm04At_localPullMetric,
        localPullMetric_inner, localPullMetric_inner, localPullMetric_inner]
      have hvec : (fun i : Fin 4 => mfderiv I3 I3 Φ z (![v, w, w, v] i)) =
          fun i : Fin 4 => ![mfderiv I3 I3 Φ z v, mfderiv I3 I3 Φ z w, mfderiv I3 I3 Φ z w,
            mfderiv I3 I3 Φ z v] i := by
        funext i
        fin_cases i <;> rfl
      rw [hvec]
      exact R.constant_curvature (Φ z) _ _
    map := Φ.toPartialDiffeomorph.trans (R.map.trans e)
    source_eq := by
      rw [partialDiffeomorph_trans_source, partialDiffeomorph_trans_source, R.source_eq,
        univ_inter]
      exact eq_univ_of_forall fun y => ⟨trivial, hV (hmem (Φ y))⟩
    target_eq := by
      have hs : (R.map.trans e).source = univ := by
        rw [partialDiffeomorph_trans_source, R.source_eq, univ_inter]
        exact eq_univ_of_forall fun y => hV (hmem y)
      have ht : (Φ.toPartialDiffeomorph).target = univ := rfl
      rw [partialDiffeomorph_trans_target, ht, inter_univ, hs, partialDiffeomorph_image_trans,
        ← R.source_eq, R.map.toPartialEquiv.image_source_eq_target, R.target_eq]
    center_eq := by
      change e (R.map R.p) = e x
      rw [R.center_eq]
    Q_pos := hQ
    comparison := C0.precompDiffeomorph Φ (fun _ _ => trivial) (fun y _ => hd y)
    metric_bounds := by
      intro z v
      have hc : mfderiv I3 I3 (Φ.toPartialDiffeomorph.trans (R.map.trans e)) z v =
          mfderiv I3 I3 e (R.map (Φ z)) (mfderiv I3 I3 R.map (Φ z) (mfderiv I3 I3 Φ z v)) := by
        have h1 := mfderiv_comp_apply z (hd (Φ z)) (hdΦ z) v
        have h2 := mfderiv_comp_apply (Φ z) (e.mdifferentiableAt (by decide) (hV (hmem (Φ z))))
          (R.map.mdifferentiableAt (by decide) (hsrc (Φ z))) (mfderiv I3 I3 Φ z v)
        exact h1.trans h2
      rw [hc, DifferentialGeometry.Diffeomorph.pullbackMetricCross_inner]
      change (1 / 2 : ℝ) * R.metric.inner (Φ z) (mfderiv I3 I3 Φ z v) (mfderiv I3 I3 Φ z v) ≤
          metricScalarAt g (e x) * g.inner (e (R.map (Φ z))) _ _ ∧
        metricScalarAt g (e x) * g.inner (e (R.map (Φ z))) _ _ ≤
          2 * R.metric.inner (Φ z) (mfderiv I3 I3 Φ z v) (mfderiv I3 I3 Φ z v)
      rw [hiso _ (hV (hmem (Φ z))), hR]
      exact R.metric_bounds (Φ z) (mfderiv I3 I3 Φ z v) }

omit [IsManifold I3 ∞ M] [SigmaCompactSpace M] [IsManifold I3 ∞ N] [T2Space N]
  [SigmaCompactSpace N] in
private theorem image_connectedComponent_eq (e : PartialDiffeomorph I3 I3 N M ∞) {x : N}
    (hK : IsCompact (connectedComponent x)) (hsrc : connectedComponent x ⊆ e.source) :
    e '' connectedComponent x = connectedComponent (e x) := by
  have : LocallyConnectedSpace N := ChartedSpace.locallyConnectedSpace ThreeSpace N
  have hopen : IsOpen (e '' connectedComponent x) :=
    e.toOpenPartialHomeomorph.isOpen_image_of_subset_source isOpen_connectedComponent hsrc
  have hclosed : IsClosed (e '' connectedComponent x) :=
    (hK.image_of_continuousOn (e.contMDiffOn_toFun.continuousOn.mono hsrc)).isClosed
  have hconn : IsPreconnected (e '' connectedComponent x) :=
    isPreconnected_connectedComponent.image _ (e.contMDiffOn_toFun.continuousOn.mono hsrc)
  exact subset_antisymm (hconn.subset_connectedComponent ⟨x, mem_connectedComponent, rfl⟩)
    ((IsClopen.connectedComponent_subset ⟨hclosed, hopen⟩ ⟨x, mem_connectedComponent, rfl⟩))

private def SpatialCanonicalAlternative.pushforwardLift {x : N} {V : Set N}
    (A : SpatialCanonicalAlternative h eps C x V) (e : PartialDiffeomorph I3 I3 N M ∞)
    (hiso : ∀ z ∈ e.source, ∀ v w : TangentSpace I3 z,
      g.inner (e z) (mfderiv I3 I3 e z v) (mfderiv I3 I3 e z w) = h.inner z v w)
    (hV : V ⊆ e.source) (hVc : IsCompact V)
    (hdist : ∀ y ∈ V, metricDistance h x y ≤ metricDistance g (e x) (e y))
    (hneck : ∀ n, A = .neck n → ∀ z ∈ univ ×ˢ Ioo (-eps⁻¹) eps⁻¹, n.neck.map z ∈ e.source)
    (hcap : ∀ c d, A = .cap c d →
      ∀ i, ∀ z ∈ univ ×ˢ Ioo (-eps⁻¹) eps⁻¹, (c.chain.necks i).map z ∈ e.source) :
    SpatialCanonicalAlternative g eps C (e x) (e '' V) := by
  have hx : x ∈ e.source := by
    cases A with
    | neck data =>
      have h0 := hneck data rfl _ (center_mem_neckWindow data.neck.eps_pos data.neck.center)
      rwa [data.neck.center_eq] at h0
    | cap data _ => exact hV (subset_union_left.trans data.union_eq.ge
        (interior_subset data.center_inside))
    | positive whole _ _ => exact hV (whole ▸ mem_connectedComponent)
    | round whole _ => exact hV (whole ▸ mem_connectedComponent)
  have hR := metricScalarAt_eq_of_isometryOn_lift e hiso hx
  cases A with
  | neck data => exact .neck (data.pushforwardLift e hiso hV hVc (hneck data rfl))
  | cap data deep =>
    have htube : data.tube ⊆ e.source := (subset_union_right.trans data.union_eq.ge).trans hV
    refine .cap (data.pushforwardLift e hV hVc
      (data.chain.pushforwardLift e hiso htube (hcap data deep rfl))) ?_
    rintro _ ⟨y, hy, rfl⟩
    rw [hR]
    exact (deep y hy).trans (hdist y (subset_union_right.trans data.union_eq.ge hy))
  | positive whole data sec =>
    have hwhole : e '' V = connectedComponent (e x) := by
      rw [whole] at hVc hV ⊢
      exact image_connectedComponent_eq e hVc hV
    refine .positive hwhole
      (Classical.choice (positiveComponent_transport_of_partialDiffeomorph_lift data e hV)) ?_
    rw [hR]
    exact secLower_image_of_isometryOn_lift e hiso hV sec
  | round whole data =>
    have hwhole : e '' V = connectedComponent (e x) := by
      rw [whole] at hVc hV ⊢
      exact image_connectedComponent_eq e hVc hV
    exact .round hwhole (data.pushforwardLift e hiso hV)

end Transport


section WitnessTransport

variable {N : Type v} [TopologicalSpace N] [ChartedSpace ThreeSpace N] [IsManifold I3 ∞ N]
  [T2Space N] [SigmaCompactSpace N] {h : SmoothRiemannianMetric I3 N}

omit [SigmaCompactSpace M] [SigmaCompactSpace N] in
private theorem metricDistance_le_of_isometryOn_lift (e : PartialDiffeomorph I3 I3 N M ∞)
    (hiso : ∀ z ∈ e.source, ∀ v w : TangentSpace I3 z,
      g.inner (e z) (mfderiv I3 I3 e z v) (mfderiv I3 I3 e z w) = h.inner z v w)
    {x : N} {R : ℝ} (hcpt : IsCompact (riemannianClosedBallOf h x R))
    (hsrc : riemannianClosedBallOf h x R ⊆ e.source) {y : N} (hy : y ∈ e.source)
    (hyR : e y ∈ riemannianBallOf g (e x) R) :
    metricDistance h x y ≤ metricDistance g (e x) (e y) := by
  have hlt : riemannianEDistOf g (e x) (e y) < ENNReal.ofReal R := hyR
  have hfin : riemannianEDistOf g (e x) (e y) ≠ ⊤ := ne_top_of_lt hlt
  have hd : 0 ≤ metricDistance g (e x) (e y) := ENNReal.toReal_nonneg
  have hdR : metricDistance g (e x) (e y) < R := ENNReal.toReal_lt_of_lt_ofReal hlt
  have hmem : e y ∈ riemannianClosedBallOf g (e x) (metricDistance g (e x) (e y)) := by
    change riemannianEDistOf g (e x) (e y) ≤ ENNReal.ofReal (metricDistance g (e x) (e y))
    rw [metricDistance, ENNReal.ofReal_toReal hfin]
  rw [← image_riemannianClosedBall_eq_of_isometric_on_compact_ball_lift
    h g e x hd hdR hcpt hsrc (fun z hz v => hiso z (hsrc hz) v v)] at hmem
  obtain ⟨y', hy', hyy⟩ := hmem
  have hy's : y' ∈ e.source := hsrc (riemannianClosedBallOf_mono h x hdR.le hy')
  have hyy' : y' = y :=
    partialDiffeomorph_injOn_of_subset_source_lift e (subset_refl e.source) hy's hy hyy
  subst hyy'
  exact ENNReal.toReal_le_of_le_ofReal hd hy'

omit [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M] [IsManifold I3 ∞ N] [T2Space N]
  [SigmaCompactSpace N] in
private theorem injective_isoSource (e : PartialDiffeomorph I3 I3 N M ∞) :
    Function.Injective (fun q : isoSource e => e q) := fun p q hpq =>
  Subtype.ext (partialDiffeomorph_injOn_of_subset_source_lift e (subset_refl e.source) p.2 q.2 hpq)

private theorem riemannianVolumeMeasure_image_eq_of_isometryOn_lift (e : PartialDiffeomorph I3 I3 N M ∞)
    (hiso : ∀ z ∈ e.source, ∀ v w : TangentSpace I3 z,
      g.inner (e z) (mfderiv I3 I3 e z v) (mfderiv I3 I3 e z w) = h.inner z v w)
    {A : Set N} (hA : A ⊆ e.source) (hAc : IsClosed A) :
    riemannianVolumeMeasure I3 M g (e '' A) = riemannianVolumeMeasure I3 N h A := by
  let S := isoSource e
  have : SigmaCompactSpace S := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I3 S.isOpen)
  let _ : MeasurableSpace S := borel S
  have : BorelSpace S := ⟨rfl⟩
  let B : Set S := Subtype.val ⁻¹' A
  have hB : MeasurableSet B := (hAc.preimage continuous_subtype_val).measurableSet
  have h1 := riemannianVolumeMeasure_image_eq_of_injective_local_isometry
    (localPullMetric h (Subtype.val : S → N) (isLocalDiffeomorph_subtype_val S)) h
    (Subtype.val : S → N) (isLocalDiffeomorph_subtype_val S) Subtype.val_injective
    (fun p v w => localPullMetric_inner h _ _ p v w) hB
  have h2 := riemannianVolumeMeasure_image_eq_of_injective_local_isometry
    (localPullMetric g (fun q : S => e q) (isLocalDiffeomorph_isoSource e)) g
    (fun q : S => e q) (isLocalDiffeomorph_isoSource e) (injective_isoSource e)
    (fun p v w => localPullMetric_inner g _ _ p v w) hB
  rw [localPull_isoSource_eq e hiso] at h1
  have hvalB : Subtype.val '' B = A := by
    ext y
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact hq
    · intro hy
      exact ⟨⟨y, hA hy⟩, hy, rfl⟩
  have heB : (fun q : S => e q) '' B = e '' A := by
    rw [← hvalB, image_image]
  rw [← heB, ← h2, h1, hvalB]

omit [SigmaCompactSpace M] [SigmaCompactSpace N] in
@[simp] private theorem SpatialCanonicalAlternative.pushforwardLift_requiresVolume {x : N} {V : Set N}
    (A : SpatialCanonicalAlternative h eps C x V) (e : PartialDiffeomorph I3 I3 N M ∞)
    (hiso : ∀ z ∈ e.source, ∀ v w : TangentSpace I3 z,
      g.inner (e z) (mfderiv I3 I3 e z v) (mfderiv I3 I3 e z w) = h.inner z v w)
    (hV : V ⊆ e.source) (hVc : IsCompact V)
    (hdist : ∀ y ∈ V, metricDistance h x y ≤ metricDistance g (e x) (e y))
    (hneck : ∀ n, A = .neck n → ∀ z ∈ univ ×ˢ Ioo (-eps⁻¹) eps⁻¹, n.neck.map z ∈ e.source)
    (hcap : ∀ c d, A = .cap c d →
      ∀ i, ∀ z ∈ univ ×ˢ Ioo (-eps⁻¹) eps⁻¹, (c.chain.necks i).map z ∈ e.source) :
    (A.pushforwardLift e hiso hV hVc hdist hneck hcap).requiresVolume = A.requiresVolume := by
  cases A <;> rfl

omit [SigmaCompactSpace M] [SigmaCompactSpace N] in
private theorem SpatialCanonicalAlternative.pushforwardLift_eq_cap {x : N} {V : Set N}
    {A : SpatialCanonicalAlternative h eps C x V} {e : PartialDiffeomorph I3 I3 N M ∞}
    {hiso : ∀ z ∈ e.source, ∀ v w : TangentSpace I3 z,
      g.inner (e z) (mfderiv I3 I3 e z v) (mfderiv I3 I3 e z w) = h.inner z v w}
    {hV : V ⊆ e.source} {hVc : IsCompact V}
    {hdist : ∀ y ∈ V, metricDistance h x y ≤ metricDistance g (e x) (e y)}
    {hneck : ∀ n, A = .neck n → ∀ z ∈ univ ×ˢ Ioo (-eps⁻¹) eps⁻¹, n.neck.map z ∈ e.source}
    {hcap : ∀ c d, A = .cap c d →
      ∀ i, ∀ z ∈ univ ×ˢ Ioo (-eps⁻¹) eps⁻¹, (c.chain.necks i).map z ∈ e.source}
    {cap : SpatialLocalCap g eps (e x) (e '' V)}
    {depth : ∀ y ∈ cap.tube, 10000 / Real.sqrt (metricScalarAt g (e x)) ≤
      metricDistance g (e x) y}
    (heq : A.pushforwardLift e hiso hV hVc hdist hneck hcap = .cap cap depth) :
    ∃ data deep, A = .cap data deep ∧ ∀ z, cap.tubeMap z = e (data.tubeMap z) := by
  cases A with
  | neck data => cases heq
  | cap data deep =>
    cases heq
    exact ⟨data, deep, rfl, fun _ => rfl⟩
  | positive whole data sec => cases heq
  | round whole data => cases heq

private theorem SpatialCanonicalWitness.domain_subset_of_ball_subset {x : N}
    (W : SpatialCanonicalWitness h eps C1 C2 x) {S : Set N} {R : ℝ} (hR : 2 * W.radius < R)
    (hsrc : riemannianClosedBallOf h x R ⊆ S) : W.domain.carrier ⊆ S := by
  have hr : 0 < W.radius :=
    (inv_pos.mpr (Real.sqrt_pos.mpr W.Q_pos)).trans_le W.radius_lower
  refine W.inside_ball.trans (fun y hy => hsrc ?_)
  exact le_of_lt (lt_trans hy ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr hR))

omit [SigmaCompactSpace M] in
private theorem SpatialCanonicalWitness.metricDistance_le_image {x : N}
    (W : SpatialCanonicalWitness h eps C1 C2 x) (e : PartialDiffeomorph I3 I3 N M ∞)
    (hiso : ∀ z ∈ e.source, ∀ v w : TangentSpace I3 z,
      g.inner (e z) (mfderiv I3 I3 e z v) (mfderiv I3 I3 e z w) = h.inner z v w)
    {R : ℝ} (hR : 2 * W.radius < R) (hcpt : IsCompact (riemannianClosedBallOf h x R))
    (hsrc : riemannianClosedBallOf h x R ⊆ e.source) :
    ∀ y ∈ W.domain.carrier, metricDistance h x y ≤ metricDistance g (e x) (e y) := by
  have hr : 0 < W.radius :=
    (inv_pos.mpr (Real.sqrt_pos.mpr W.Q_pos)).trans_le W.radius_lower
  have hdom := W.domain_subset_of_ball_subset hR hsrc
  have hB2 := image_riemannianBall_eq_of_isometric_on_compact_ball_lift
    h g e x (by linarith : 0 < 2 * W.radius) hR hcpt hsrc (fun z hz v => hiso z (hsrc hz) v v)
  intro y hy
  apply metricDistance_le_of_isometryOn_lift e hiso hcpt hsrc (hdom hy)
  have hy2 : e y ∈ riemannianBallOf g (e x) (2 * W.radius) := by
    rw [← hB2]
    exact ⟨y, W.inside_ball hy, rfl⟩
  exact lt_trans hy2 ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr hR)

private def SpatialCanonicalWitness.pushforwardLift {x : N} (W : SpatialCanonicalWitness h eps C1 C2 x)
    (e : PartialDiffeomorph I3 I3 N M ∞)
    (hiso : ∀ z ∈ e.source, ∀ v w : TangentSpace I3 z,
      g.inner (e z) (mfderiv I3 I3 e z v) (mfderiv I3 I3 e z w) = h.inner z v w)
    {R : ℝ} (hR : 2 * W.radius < R) (hcpt : IsCompact (riemannianClosedBallOf h x R))
    (hsrc : riemannianClosedBallOf h x R ⊆ e.source)
    (hneck : ∀ n, W.alternative = .neck n →
      ∀ z ∈ univ ×ˢ Ioo (-eps⁻¹) eps⁻¹, n.neck.map z ∈ e.source)
    (hcap : ∀ c d, W.alternative = .cap c d →
      ∀ i, ∀ z ∈ univ ×ˢ Ioo (-eps⁻¹) eps⁻¹, (c.chain.necks i).map z ∈ e.source) :
    SpatialCanonicalWitness g eps C1 C2 (e x) := by
  have hr : 0 < W.radius :=
    (inv_pos.mpr (Real.sqrt_pos.mpr W.Q_pos)).trans_le W.radius_lower
  have hdom : W.domain.carrier ⊆ e.source := W.domain_subset_of_ball_subset hR hsrc
  have hx : x ∈ e.source := hdom (interior_subset W.center_inside)
  have hRx := metricScalarAt_eq_of_isometryOn_lift e hiso hx
  have hquad : ∀ z ∈ riemannianClosedBallOf h x R, ∀ v : TangentSpace I3 z,
      g.inner (e z) (mfderiv I3 I3 e z v) (mfderiv I3 I3 e z v) = h.inner z v v :=
    fun z hz v => hiso z (hsrc hz) v v
  have hB1 := image_riemannianBall_eq_of_isometric_on_compact_ball_lift
    h g e x hr (by linarith) hcpt hsrc hquad
  have hB2 := image_riemannianBall_eq_of_isometric_on_compact_ball_lift
    h g e x (by linarith : 0 < 2 * W.radius) hR hcpt hsrc hquad
  have hdist := W.metricDistance_le_image e hiso hR hcpt hsrc
  refine {
    Q_pos := by rw [hRx]; exact W.Q_pos
    eps_pos := W.eps_pos
    eps_lt_one := W.eps_lt_one
    domain := W.domain.map e hdom
    center_inside := ?_
    radius := W.radius
    radius_lower := by rw [hRx]; exact W.radius_lower
    radius_upper := by rw [hRx]; exact W.radius_upper
    ball_inside := ?_
    inside_ball := ?_
    scalar_bounds := ?_
    rm_bound := ?_
    alternative := W.alternative.pushforwardLift e hiso hdom W.domain.compact hdist hneck hcap
    volume := ?_
    gradient := ?_ }
  · change e x ∈ interior (e '' W.domain.carrier)
    rw [← partialDiffeomorph_image_interior_of_subset_source_lift e hdom]
    exact ⟨x, W.center_inside, rfl⟩
  · change riemannianBallOf g (e x) W.radius ⊆ e '' W.domain.carrier
    rw [← hB1]
    exact image_mono W.ball_inside
  · change e '' W.domain.carrier ⊆ riemannianBallOf g (e x) (2 * W.radius)
    rw [← hB2]
    exact image_mono W.inside_ball
  · rintro _ ⟨y, hy, rfl⟩
    rw [hRx, metricScalarAt_eq_of_isometryOn_lift e hiso (hdom hy)]
    exact W.scalar_bounds y hy
  · rintro _ ⟨y, hy, rfl⟩
    have h0 := W.rm_bound y hy
    change Real.sqrt (normSq0S g (e y) 4 (metricRm04At g (e y))) ≤ _
    change Real.sqrt (normSq0S h y 4 (metricRm04At h y)) ≤ _ at h0
    rw [rmNormSq_eq_of_isometryOn_lift e hiso (hdom hy), hRx]
    exact h0
  · intro hv
    have hv' : W.alternative.requiresVolume :=
      (SpatialCanonicalAlternative.pushforwardLift_requiresVolume W.alternative e hiso hdom
        W.domain.compact hdist hneck hcap).mp hv
    change _ ≤ riemannianVolumeMeasure I3 M g (e '' W.domain.carrier)
    rw [riemannianVolumeMeasure_image_eq_of_isometryOn_lift e hiso hdom W.domain.compact.isClosed, hRx]
    exact W.volume hv'
  · intro v'
    let L := (e.isLocalDiffeomorphAt I3 I3 ∞ hx).mfderivToContinuousLinearEquiv (by simp)
    obtain ⟨v, rfl⟩ := L.surjective v'
    have hL : L v = mfderiv I3 I3 e x v := rfl
    rw [hL, mfderiv_metricScalarAt_eq_of_isometryOn_lift e hiso hx v, hiso x hx v v, hRx]
    exact W.gradient v

private theorem SpatialCanonicalWitness.capTubeHasNeckChart.pushforwardLift {x : N}
    {W : SpatialCanonicalWitness h eps C1 C2 x} (hW : W.capTubeHasNeckChart alpha)
    (e : PartialDiffeomorph I3 I3 N M ∞)
    (hiso : ∀ z ∈ e.source, ∀ v w : TangentSpace I3 z,
      g.inner (e z) (mfderiv I3 I3 e z v) (mfderiv I3 I3 e z w) = h.inner z v w)
    {R : ℝ} (hR : 2 * W.radius < R) (hcpt : IsCompact (riemannianClosedBallOf h x R))
    (hsrc : riemannianClosedBallOf h x R ⊆ e.source)
    (hneck : ∀ n, W.alternative = .neck n →
      ∀ z ∈ univ ×ˢ Ioo (-eps⁻¹) eps⁻¹, n.neck.map z ∈ e.source)
    (hcap : ∀ c d, W.alternative = .cap c d →
      ∀ i, ∀ z ∈ univ ×ˢ Ioo (-eps⁻¹) eps⁻¹, (c.chain.necks i).map z ∈ e.source)
    (hchart : ∀ c d, W.alternative = .cap c d → ∀ (v : N) (nk : SpatialNeck h alpha v),
      (∀ z, c.tubeMap z = nk.map z) →
        ∀ z ∈ univ ×ˢ Ioo (-alpha⁻¹) alpha⁻¹, nk.map z ∈ e.source) :
    (W.pushforwardLift e hiso hR hcpt hsrc hneck hcap).capTubeHasNeckChart alpha := by
  intro cap depth heq
  change W.alternative.pushforwardLift e hiso (W.domain_subset_of_ball_subset hR hsrc)
    W.domain.compact (W.metricDistance_le_image e hiso hR hcpt hsrc) hneck hcap = _ at heq
  obtain ⟨data, deep, hA, htube⟩ := SpatialCanonicalAlternative.pushforwardLift_eq_cap heq
  obtain ⟨v, nk, hnk⟩ := hW data deep hA
  refine ⟨e v, nk.pushforwardLift e hiso (hchart data deep hA v nk hnk), fun z => ?_⟩
  rw [htube z, hnk z]
  rfl

end WitnessTransport


section Corollaries

variable {N : Type v} [TopologicalSpace N] [ChartedSpace ThreeSpace N] [IsManifold I3 ∞ N]
  [T2Space N] [SigmaCompactSpace N]

omit [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M] [IsManifold I3 ∞ N] [T2Space N]
  [SigmaCompactSpace N] in
private theorem exists_partialDiffeomorph_of_injective {f : N → M}
    (hf : IsLocalDiffeomorph I3 I3 ∞ f) (hinj : Function.Injective f) (x : N) :
    ∃ e : PartialDiffeomorph I3 I3 N M ∞, e.source = univ ∧ (e : N → M) = f := by
  obtain ⟨e, hs, -, hf'⟩ := IsLocalDiffeomorphOn.exists_partialDiffeomorph_of_injOn
    (hf.isLocalDiffeomorphOn univ) isOpen_univ ⟨x, trivial⟩ hinj.injOn
  exact ⟨e, hs, hf'⟩

def SpatialCanonicalWitness.pushforwardOfInjectiveULift {f : N → M}
    (hf : IsLocalDiffeomorph I3 I3 ∞ f) (hinj : Function.Injective f) {x : N}
    (W : SpatialCanonicalWitness (localPullMetric g f hf) eps C1 C2 x) {R : ℝ}
    (hR : 2 * W.radius < R)
    (hcpt : IsCompact (riemannianClosedBallOf (localPullMetric g f hf) x R)) :
    SpatialCanonicalWitness g eps C1 C2 (f x) :=
  let e := Classical.choose (exists_partialDiffeomorph_of_injective hf hinj x)
  have hspec := Classical.choose_spec (exists_partialDiffeomorph_of_injective hf hinj x)
  have hiso : ∀ z ∈ e.source, ∀ v w : TangentSpace I3 z,
      g.inner (e z) (mfderiv I3 I3 e z v) (mfderiv I3 I3 e z w) =
        (localPullMetric g f hf).inner z v w := by
    intro z _ v w
    rw [hspec.2, localPullMetric_inner]
  have hmem : ∀ y : N, y ∈ e.source := fun y => hspec.1 ▸ mem_univ y
  congrFun hspec.2 x ▸ W.pushforwardLift e hiso hR hcpt (fun y _ => hmem y)
    (fun _ _ z _ => hmem _) (fun _ _ _ _ z _ => hmem _)

theorem SpatialCanonicalWitness.capTubeHasNeckChart.pushforwardOfInjectiveULift {f : N → M}
    (hf : IsLocalDiffeomorph I3 I3 ∞ f) (hinj : Function.Injective f) {x : N}
    {W : SpatialCanonicalWitness (localPullMetric g f hf) eps C1 C2 x}
    (hW : W.capTubeHasNeckChart alpha) {R : ℝ} (hR : 2 * W.radius < R)
    (hcpt : IsCompact (riemannianClosedBallOf (localPullMetric g f hf) x R)) :
    (W.pushforwardOfInjectiveULift hf hinj hR hcpt).capTubeHasNeckChart alpha := by
  have hspec := Classical.choose_spec (exists_partialDiffeomorph_of_injective hf hinj x)
  have hmem : ∀ y : N,
      y ∈ (Classical.choose (exists_partialDiffeomorph_of_injective hf hinj x)).source := by
    intro y
    rw [hspec.1]
    exact mem_univ y
  exact SpatialCanonicalWitness.capTubeHasNeckChart_cast _
    (hW.pushforwardLift _ _ hR hcpt (fun y _ => hmem y) _ _ fun _ _ _ _ _ _ z _ => hmem _)

end Corollaries

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
