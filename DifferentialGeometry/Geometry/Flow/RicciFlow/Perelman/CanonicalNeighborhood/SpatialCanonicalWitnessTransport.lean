import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialCanonicalWitness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.RoundModelCoveringBall
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ParabolicRescalingReduction
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Scaling
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CanonicalCapTransport
import DifferentialGeometry.Geometry.Metric.Comparison.IsometricBalls
import DifferentialGeometry.Geometry.Measure.LocalIsometry
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.LocalNorm
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.LocalIterCov

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PartialDiffeomorph (image_riemannianBall_eq_of_isometric_on_compact_ball
  image_riemannianClosedBall_eq_of_isometric_on_compact_ball)
open DifferentialGeometry.Geometry.Measure
  (riemannianVolumeMeasure_image_eq_of_injective_local_isometry)

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {g : SmoothRiemannianMetric I3 M} {eps C C1 C2 alpha : ℝ} {x : M} {U : Set M}

section Scaling

variable (c : ℝ) (hc : 0 < c)

private theorem div_sqrt_inv_mul_eq {c : ℝ} (hc : 0 < c) (a b : ℝ) :
    a / Real.sqrt (c⁻¹ * b) = Real.sqrt c * (a / Real.sqrt b) := by
  rw [Real.sqrt_mul (inv_nonneg.mpr hc.le), Real.sqrt_inv, mul_comm (Real.sqrt c)⁻¹, ← div_div,
    div_inv_eq_mul, mul_comm]

private theorem scaled_volume_factor {c : ℝ} (hc : 0 < c) (a b : ℝ) (hb : 0 < b) :
    a / (c⁻¹ * b * Real.sqrt (c⁻¹ * b)) = Real.sqrt c ^ 3 * (a / (b * Real.sqrt b)) := by
  obtain ⟨s, hs, rfl⟩ : ∃ s : ℝ, 0 < s ∧ s ^ 2 = c :=
    ⟨Real.sqrt c, Real.sqrt_pos.mpr hc, Real.sq_sqrt hc.le⟩
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  rw [Real.sqrt_sq hs.le, Real.sqrt_mul (inv_nonneg.mpr (sq_nonneg s)), Real.sqrt_inv,
    Real.sqrt_sq hs.le]
  field_simp

omit [T2Space M] [SigmaCompactSpace M] in
theorem metricScalarAt_scaleMetric_pos (hQ : 0 < metricScalarAt g x) :
    0 < metricScalarAt (DifferentialGeometry.scaleMetric c hc g) x := by
  rw [metricScalarAt_scaleMetric]
  exact mul_pos (inv_pos.mpr hc) hQ

omit [T2Space M] [SigmaCompactSpace M] in
theorem scaleMetric_normalized_eq (hQ : 0 < metricScalarAt g x) :
    DifferentialGeometry.scaleMetric (metricScalarAt (DifferentialGeometry.scaleMetric c hc g) x)
        (metricScalarAt_scaleMetric_pos c hc hQ) (DifferentialGeometry.scaleMetric c hc g) =
      DifferentialGeometry.scaleMetric (metricScalarAt g x) hQ g := by
  apply SmoothRiemannianMetric.ext_inner
  intro y v w
  rw [scaleMetric_inner, scaleMetric_inner, scaleMetric_inner, metricScalarAt_scaleMetric]
  field_simp

omit [T2Space M] [SigmaCompactSpace M] in
def SpatialOrderedNeckChain.scaleMetric (ch : SpatialOrderedNeckChain g eps U) :
    SpatialOrderedNeckChain (DifferentialGeometry.scaleMetric c hc g) eps U where
  count := ch.count
  count_pos := ch.count_pos
  centers := ch.centers
  necks i := (ch.necks i).scaleMetric c hc
  lo := ch.lo
  hi := ch.hi
  lo_lt_hi := ch.lo_lt_hi
  inside := ch.inside
  swept_eq := ch.swept_eq
  transition_increasing := ch.transition_increasing

omit [T2Space M] [SigmaCompactSpace M] in
def SpatialLocalNeck.scaleMetric (n : SpatialLocalNeck g eps x U) :
    SpatialLocalNeck (DifferentialGeometry.scaleMetric c hc g) eps x U where
  neck := n.neck.scaleMetric c hc
  region_eq := n.region_eq
  boundary_eq := n.boundary_eq

omit [T2Space M] [SigmaCompactSpace M] in
def SpatialLocalCap.scaleMetric (L : SpatialLocalCap g eps x U) :
    SpatialLocalCap (DifferentialGeometry.scaleMetric c hc g) eps x U where
  core := L.core
  core_inside := L.core_inside
  center_inside := L.center_inside
  coreModel := L.coreModel
  tube := L.tube
  tubeMap := L.tubeMap
  tube_domain := L.tube_domain
  tube_eq := L.tube_eq
  union_eq := L.union_eq
  overlap_eq := L.overlap_eq
  inner_boundary := L.inner_boundary
  outer_boundary := L.outer_boundary
  boundary_eq := L.boundary_eq
  boundaries_disjoint := L.boundaries_disjoint
  chain := L.chain.scaleMetric c hc
  coreBoundaryMap := L.coreBoundaryMap
  core_boundary_eq := L.core_boundary_eq

omit [T2Space M] [SigmaCompactSpace M] in
def SpatialRoundComponent.scaleMetric (R : SpatialRoundComponent g eps x U) :
    SpatialRoundComponent (DifferentialGeometry.scaleMetric c hc g) eps x U := by
  refine {
    Z := R.Z
    topology := R.topology
    charted := R.charted
    smooth := R.smooth
    t2 := R.t2
    compact := R.compact
    connected := R.connected
    metric := R.metric
    p := R.p
    scalar_one := R.scalar_one
    constant_curvature := R.constant_curvature
    map := R.map
    source_eq := R.source_eq
    target_eq := R.target_eq
    center_eq := R.center_eq
    Q_pos := metricScalarAt_scaleMetric_pos c hc R.Q_pos
    comparison := ?_
    metric_bounds := ?_ }
  · rw [scaleMetric_normalized_eq c hc R.Q_pos]
    exact R.comparison
  · intro z v
    have h := R.metric_bounds z v
    rw [scaleMetric_inner, metricScalarAt_scaleMetric]
    have he : ∀ a : ℝ, c⁻¹ * metricScalarAt g x * (c * a) = metricScalarAt g x * a := by
      intro a
      field_simp
    rw [he]
    exact h

omit [T2Space M] [SigmaCompactSpace M] in
theorem deep_scaleMetric {T : Set M}
    (deep : ∀ y ∈ T, 10000 / Real.sqrt (metricScalarAt g x) ≤ metricDistance g x y) :
    ∀ y ∈ T, 10000 / Real.sqrt (metricScalarAt (DifferentialGeometry.scaleMetric c hc g) x) ≤
      metricDistance (DifferentialGeometry.scaleMetric c hc g) x y := by
  intro y hy
  rw [metricScalarAt_scaleMetric, div_sqrt_inv_mul_eq hc, metricDistance_scaleMetric]
  exact mul_le_mul_of_nonneg_left (deep y hy) (Real.sqrt_nonneg c)

def SpatialCanonicalAlternative.scaleMetric :
    SpatialCanonicalAlternative g eps C x U →
      SpatialCanonicalAlternative (DifferentialGeometry.scaleMetric c hc g) eps C x U
  | .neck data => .neck (data.scaleMetric c hc)
  | .cap data deep => .cap (data.scaleMetric c hc) (deep_scaleMetric c hc deep)
  | .positive whole data sec => .positive whole data (by
      have : IsManifold I3 1 M := IsManifold.of_le (n := ∞) (by decide)
      refine (secLower_scaleMetric g c _ hc U).mpr ?_
      rw [metricScalarAt_scaleMetric]
      convert sec using 1
      field_simp)
  | .round whole data => .round whole (data.scaleMetric c hc)

omit [SigmaCompactSpace M] in
@[simp] theorem SpatialCanonicalAlternative.scaleMetric_requiresVolume
    (A : SpatialCanonicalAlternative g eps C x U) :
    (A.scaleMetric c hc).requiresVolume = A.requiresVolume := by
  cases A <;> rfl

def SpatialCanonicalWitness.scaleMetric (W : SpatialCanonicalWitness g eps C1 C2 x) :
    SpatialCanonicalWitness (DifferentialGeometry.scaleMetric c hc g) eps C1 C2 x := by
  have hci : 0 ≤ c⁻¹ := inv_nonneg.mpr hc.le
  have hsc : 0 ≤ Real.sqrt c := Real.sqrt_nonneg c
  refine {
    Q_pos := metricScalarAt_scaleMetric_pos c hc W.Q_pos
    eps_pos := W.eps_pos
    eps_lt_one := W.eps_lt_one
    domain := W.domain
    center_inside := W.center_inside
    radius := Real.sqrt c * W.radius
    radius_lower := ?_
    radius_upper := ?_
    ball_inside := ?_
    inside_ball := ?_
    scalar_bounds := ?_
    rm_bound := ?_
    alternative := W.alternative.scaleMetric c hc
    volume := ?_
    gradient := ?_ }
  · rw [metricScalarAt_scaleMetric, ← one_div, div_sqrt_inv_mul_eq hc, one_div]
    exact mul_le_mul_of_nonneg_left W.radius_lower hsc
  · rw [metricScalarAt_scaleMetric, div_sqrt_inv_mul_eq hc]
    exact mul_le_mul_of_nonneg_left W.radius_upper hsc
  · rw [riemannianBallOf_scaleMetric]
    exact W.ball_inside
  · rw [show 2 * (Real.sqrt c * W.radius) = Real.sqrt c * (2 * W.radius) by ring,
      riemannianBallOf_scaleMetric]
    exact W.inside_ball
  · intro y hy
    rw [metricScalarAt_scaleMetric, metricScalarAt_scaleMetric]
    have h := W.scalar_bounds y hy
    constructor
    · rw [mul_left_comm]
      exact mul_le_mul_of_nonneg_left h.1 hci
    · rw [mul_left_comm C2]
      exact mul_le_mul_of_nonneg_left h.2 hci
  · intro y hy
    have h := W.rm_bound y hy
    rw [metricRm_scale, normSq0S_scale, Real.sqrt_mul (pow_nonneg hci 4), sqrt_normSq0S_smul,
      abs_of_pos hc, metricScalarAt_scaleMetric]
    have h4 : Real.sqrt ((c⁻¹) ^ 4) = c⁻¹ * c⁻¹ := by
      rw [show (c⁻¹) ^ 4 = (c⁻¹ * c⁻¹) ^ 2 by ring, Real.sqrt_sq (mul_nonneg hci hci)]
    rw [h4]
    calc c⁻¹ * c⁻¹ * (c * Real.sqrt (normSq0S g y 4 (metricRm04 g y)))
        = c⁻¹ * Real.sqrt (normSq0S g y 4 (metricRm04 g y)) := by field_simp
      _ ≤ c⁻¹ * (C2 * metricScalarAt g x) := mul_le_mul_of_nonneg_left h hci
      _ = C2 * (c⁻¹ * metricScalarAt g x) := by ring
  · intro hv
    have hv' : W.alternative.requiresVolume := by
      simpa only [SpatialCanonicalAlternative.scaleMetric_requiresVolume] using hv
    have h := W.volume hv'
    rw [volume_scale_apply, metricScalarAt_scaleMetric, scaled_volume_factor hc _ _ W.Q_pos,
      ENNReal.ofReal_mul (pow_nonneg hsc 3), ENNReal.ofReal_pow hsc]
    have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
    rw [hdim]
    gcongr
  · intro v
    have hd : MDifferentiableAt I3 𝓘(ℝ, ℝ) (metricScalarAt g) x :=
      (metricScalar_smooth g).mdifferentiableAt (by simp)
    have hfun : metricScalarAt (DifferentialGeometry.scaleMetric c hc g) =
        c⁻¹ • metricScalarAt g := by
      funext y
      simp only [Pi.smul_apply, smul_eq_mul]
      exact metricScalarAt_scaleMetric c hc g y
    have hgrad := W.gradient v
    rw [hfun, const_smul_mfderiv hd]
    change |c⁻¹ * (show ℝ from mfderiv I3 𝓘(ℝ, ℝ) (metricScalarAt g) x v)| ≤
      C2 * (c⁻¹ • metricScalarAt g) x * Real.sqrt ((c⁻¹ • metricScalarAt g) x) *
        Real.sqrt ((DifferentialGeometry.scaleMetric c hc g).inner x v v)
    simp only [Pi.smul_apply, smul_eq_mul, scaleMetric_inner]
    refine (le_of_eq (abs_mul _ _)).trans ?_
    rw [abs_of_pos (inv_pos.mpr hc), Real.sqrt_mul hci, Real.sqrt_mul hc.le, Real.sqrt_inv]
    refine (mul_le_mul_of_nonneg_left hgrad hci).trans (le_of_eq ?_)
    have hs : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
    field_simp

@[simp] theorem SpatialCanonicalWitness.scaleMetric_domain
    (W : SpatialCanonicalWitness g eps C1 C2 x) :
    (W.scaleMetric c hc).domain = W.domain := rfl

@[simp] theorem SpatialCanonicalWitness.scaleMetric_radius
    (W : SpatialCanonicalWitness g eps C1 C2 x) :
    (W.scaleMetric c hc).radius = Real.sqrt c * W.radius := rfl

theorem SpatialCanonicalWitness.capTubeHasNeckChart.scaleMetric
    {W : SpatialCanonicalWitness g eps C1 C2 x} (h : W.capTubeHasNeckChart alpha) :
    (W.scaleMetric c hc).capTubeHasNeckChart alpha := by
  intro cap depth heq
  change W.alternative.scaleMetric c hc = SpatialCanonicalAlternative.cap cap depth at heq
  cases halt : W.alternative with
  | neck data =>
    rw [halt] at heq
    cases heq
  | cap data deep =>
    rw [halt] at heq
    change SpatialCanonicalAlternative.cap (data.scaleMetric c hc) _ = _ at heq
    cases heq
    obtain ⟨v, nk, hnk⟩ := h data deep halt
    exact ⟨v, nk.scaleMetric c hc, hnk⟩
  | positive whole data sec =>
    rw [halt] at heq
    cases heq
  | round whole data =>
    rw [halt] at heq
    cases heq

end Scaling

section Isometry

variable {N : Type u} [TopologicalSpace N] [ChartedSpace ThreeSpace N] [IsManifold I3 ∞ N]
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
theorem metricScalarAt_eq_of_isometryOn (e : PartialDiffeomorph I3 I3 N M ∞)
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
theorem rmNormSq_eq_of_isometryOn (e : PartialDiffeomorph I3 I3 N M ∞)
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
theorem metricRm04At_eq_of_isometryOn (e : PartialDiffeomorph I3 I3 N M ∞)
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
theorem mfderiv_metricScalarAt_eq_of_isometryOn (e : PartialDiffeomorph I3 I3 N M ∞)
    (hiso : ∀ z ∈ e.source, ∀ v w : TangentSpace I3 z,
      g.inner (e z) (mfderiv I3 I3 e z v) (mfderiv I3 I3 e z w) = h.inner z v w)
    {z : N} (hz : z ∈ e.source) (v : TangentSpace I3 z) :
    (show ℝ from mfderiv I3 𝓘(ℝ, ℝ) (metricScalarAt g) (e z) (mfderiv I3 I3 e z v)) =
      mfderiv I3 𝓘(ℝ, ℝ) (metricScalarAt h) z v := by
  let p : isoSource e := ⟨z, hz⟩
  have hfun : (fun q : isoSource e => metricScalarAt h q) =
      fun q : isoSource e => metricScalarAt g (e q) :=
    funext fun q => (metricScalarAt_eq_of_isometryOn e hiso q.2).symm
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
theorem secLower_image_of_isometryOn (e : PartialDiffeomorph I3 I3 N M ∞)
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
  have hrm := metricRm04At_eq_of_isometryOn e hiso (hV hy) (fun i : Fin 4 => ![v, w, w, v] i)
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

variable {N : Type u} [TopologicalSpace N] [ChartedSpace ThreeSpace N] [IsManifold I3 ∞ N]
  [T2Space N] [SigmaCompactSpace N] {h : SmoothRiemannianMetric I3 N}

omit [T2Space M] [SigmaCompactSpace M] in
def MetricComparisonOn.mapIsometry {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
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
  rw [scaleMetric_inner, scaleMetric_inner, metricScalarAt_eq_of_isometryOn e hiso hp,
    hiso z hz v w]

omit [T2Space M] [SigmaCompactSpace M] [T2Space N] [SigmaCompactSpace N] in
private theorem center_mem_neckWindow {eps : ℝ} (heps : 0 < eps) (c : Sphere 2) :
    ((c, 0) : Cylinder) ∈ (univ ×ˢ Ioo (-eps⁻¹) eps⁻¹ : Set Cylinder) :=
  ⟨trivial, neg_neg_of_pos (inv_pos.mpr heps), inv_pos.mpr heps⟩

omit [SigmaCompactSpace M] [SigmaCompactSpace N] in
def SpatialNeck.pushforward {p : N} (nk : SpatialNeck h eps p) (e : PartialDiffeomorph I3 I3 N M ∞)
    (hiso : ∀ z ∈ e.source, ∀ v w : TangentSpace I3 z,
      g.inner (e z) (mfderiv I3 I3 e z v) (mfderiv I3 I3 e z w) = h.inner z v w)
    (hwin : ∀ z ∈ univ ×ˢ Ioo (-eps⁻¹) eps⁻¹, nk.map z ∈ e.source) :
    SpatialNeck g eps (e p) := by
  have hp : p ∈ e.source := by
    have h0 := hwin _ (center_mem_neckWindow nk.eps_pos nk.center)
    rwa [nk.center_eq] at h0
  have hQ : 0 < metricScalarAt g (e p) := by
    rw [metricScalarAt_eq_of_isometryOn e hiso hp]
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
    comparison := nk.comparison.mapIsometry e
      (scaleMetric_isometryOn e hiso hp nk.Q_pos hQ)
      (fun y hy => nk.map.mdifferentiableAt (by decide) (nk.domain hy)) hwin }

omit [SigmaCompactSpace M] [SigmaCompactSpace N] in
@[simp] theorem SpatialNeck.pushforward_map {p : N} (nk : SpatialNeck h eps p)
    (e : PartialDiffeomorph I3 I3 N M ∞)
    (hiso : ∀ z ∈ e.source, ∀ v w : TangentSpace I3 z,
      g.inner (e z) (mfderiv I3 I3 e z v) (mfderiv I3 I3 e z w) = h.inner z v w)
    (hwin : ∀ z ∈ univ ×ˢ Ioo (-eps⁻¹) eps⁻¹, nk.map z ∈ e.source) :
    (nk.pushforward e hiso hwin).map = nk.map.trans e := rfl

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
def SpatialOrderedNeckChain.transport {g' : SmoothRiemannianMetric I3 M} {eps' : ℝ} {V : Set N}
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
      partialDiffeomorph_injOn_of_subset_source e (subset_refl e.source) hw1 hz.2 hwe
    rwa [hw] at hw2

omit [SigmaCompactSpace M] [SigmaCompactSpace N] in
def SpatialOrderedNeckChain.pushforward {V : Set N} (ch : SpatialOrderedNeckChain h eps V)
    (e : PartialDiffeomorph I3 I3 N M ∞)
    (hiso : ∀ z ∈ e.source, ∀ v w : TangentSpace I3 z,
      g.inner (e z) (mfderiv I3 I3 e z v) (mfderiv I3 I3 e z w) = h.inner z v w)
    (hV : V ⊆ e.source)
    (hwin : ∀ i, ∀ z ∈ univ ×ˢ Ioo (-eps⁻¹) eps⁻¹, (ch.necks i).map z ∈ e.source) :
    SpatialOrderedNeckChain g eps (e '' V) :=
  ch.transport e hV (fun i => (ch.necks i).pushforward e hiso (hwin i)) fun _ => rfl

omit [SigmaCompactSpace M] [SigmaCompactSpace N] in
def SpatialLocalNeck.pushforward {x : N} {V : Set N} (n : SpatialLocalNeck h eps x V)
    (e : PartialDiffeomorph I3 I3 N M ∞)
    (hiso : ∀ z ∈ e.source, ∀ v w : TangentSpace I3 z,
      g.inner (e z) (mfderiv I3 I3 e z v) (mfderiv I3 I3 e z w) = h.inner z v w)
    (hV : V ⊆ e.source) (hVc : IsCompact V)
    (hwin : ∀ z ∈ univ ×ˢ Ioo (-eps⁻¹) eps⁻¹, n.neck.map z ∈ e.source) :
    SpatialLocalNeck g eps (e x) (e '' V) where
  neck := n.neck.pushforward e hiso hwin
  region_eq := by
    rw [SpatialNeck.pushforward_map, partialDiffeomorph_image_trans]
    exact congrArg (fun s => e '' s) n.region_eq
  boundary_eq := by
    have hc : IsCompact (e '' V) :=
      hVc.image_of_continuousOn (e.contMDiffOn_toFun.continuousOn.mono hV)
    rw [← partialDiffeomorph_image_frontier_of_subset_source e hV hVc.isClosed hc.isClosed,
      SpatialNeck.pushforward_map, partialDiffeomorph_image_trans]
    exact congrArg (fun s => e '' s) n.boundary_eq

omit [SigmaCompactSpace M] [T2Space N] [SigmaCompactSpace N] in
theorem SpatialLocalCap.isCompact_tube {x : N} {V : Set N} (L : SpatialLocalCap h eps x V) :
    IsCompact L.tube := by
  rw [← L.tube_eq]
  exact (isCompact_univ.prod isCompact_Icc).image_of_continuousOn
    (L.tubeMap.contMDiffOn_toFun.continuousOn.mono L.tube_domain)

def SpatialLocalCap.pushforward {eps' : ℝ} {x : N} {V : Set N} (L : SpatialLocalCap h eps x V)
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
    coreModel := Classical.choice (capCore_transport_of_partialDiffeomorph L.coreModel e hcore)
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
      (le_of_eq (partialDiffeomorph_image_interior_of_subset_source e hV))
  · change e x ∈ interior (e '' L.core.carrier)
    rw [← partialDiffeomorph_image_interior_of_subset_source e hcore]
    exact ⟨x, L.center_inside, rfl⟩
  · intro z hz
    exact ⟨L.tube_domain hz, htube (L.tube_eq ▸ ⟨z, hz, rfl⟩)⟩
  · rw [partialDiffeomorph_image_trans, L.tube_eq]
  · change e '' V = e '' L.core.carrier ∪ e '' L.tube
    rw [← image_union]
    exact congrArg _ L.union_eq
  · change e '' L.core.carrier ∩ e '' L.tube = frontier (e '' L.core.carrier)
    rw [← partialDiffeomorph_image_inter_of_subset_source e hcore htube, L.overlap_eq,
      partialDiffeomorph_image_frontier_of_subset_source e hcore hcoreC hecore]
  · change (L.tubeMap.trans e) '' (univ ×ˢ ({0} : Set ℝ)) = frontier (e '' L.core.carrier)
    rw [partialDiffeomorph_image_trans, L.inner_boundary,
      partialDiffeomorph_image_frontier_of_subset_source e hcore hcoreC hecore]
  · rw [partialDiffeomorph_image_trans, L.outer_boundary,
      partialDiffeomorph_image_frontier_of_subset_source e hV hVc.isClosed heV]
  · change frontier (e '' L.tube) = frontier (e '' L.core.carrier) ∪ frontier (e '' V)
    rw [← partialDiffeomorph_image_frontier_of_subset_source e htube htubeC hetube,
      L.boundary_eq, image_union,
      partialDiffeomorph_image_frontier_of_subset_source e hcore hcoreC hecore,
      partialDiffeomorph_image_frontier_of_subset_source e hV hVc.isClosed heV]
  · change Disjoint (frontier (e '' L.core.carrier)) (frontier (e '' V))
    rw [← partialDiffeomorph_image_frontier_of_subset_source e hcore hcoreC hecore,
      ← partialDiffeomorph_image_frontier_of_subset_source e hV hVc.isClosed heV]
    exact L.boundaries_disjoint.image
      (partialDiffeomorph_injOn_of_subset_source e (subset_refl e.source))
      (hcoreC.frontier_subset.trans hcore) (hVc.isClosed.frontier_subset.trans hV)
  · intro z
    rw [partialDiffeomorph_trans_apply, L.core_boundary_eq]

omit [SigmaCompactSpace M] [SigmaCompactSpace N] in
theorem SpatialLocalCap.pushforward_tube {eps' : ℝ} {x : N} {V : Set N}
    (L : SpatialLocalCap h eps x V) (e : PartialDiffeomorph I3 I3 N M ∞) (hV : V ⊆ e.source)
    (hVc : IsCompact V) (chain : SpatialOrderedNeckChain g eps' (e '' L.tube)) :
    (L.pushforward e hV hVc chain).tube = e '' L.tube := rfl

omit [SigmaCompactSpace M] [SigmaCompactSpace N] in
theorem SpatialLocalCap.pushforward_tubeMap {eps' : ℝ} {x : N} {V : Set N}
    (L : SpatialLocalCap h eps x V) (e : PartialDiffeomorph I3 I3 N M ∞) (hV : V ⊆ e.source)
    (hVc : IsCompact V) (chain : SpatialOrderedNeckChain g eps' (e '' L.tube)) :
    (L.pushforward e hV hVc chain).tubeMap = L.tubeMap.trans e := rfl

omit [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M] [IsManifold I3 ∞ N] [T2Space N]
  [SigmaCompactSpace N] in
private theorem mfderiv_trans_apply {Z : Type*} [TopologicalSpace Z] [ChartedSpace ThreeSpace Z]
    (m : PartialDiffeomorph I3 I3 Z N ∞) (e : PartialDiffeomorph I3 I3 N M ∞) {z : Z}
    (hz : z ∈ m.source) (hez : m z ∈ e.source) (v : TangentSpace I3 z) :
    mfderiv I3 I3 (m.trans e) z v = mfderiv I3 I3 e (m z) (mfderiv I3 I3 m z v) :=
  mfderiv_comp_apply z (e.mdifferentiableAt (by decide) hez) (m.mdifferentiableAt (by decide) hz) v

omit [SigmaCompactSpace M] [SigmaCompactSpace N] in
def SpatialRoundComponent.pushforward {x : N} {V : Set N} (R : SpatialRoundComponent h eps x V)
    (e : PartialDiffeomorph I3 I3 N M ∞)
    (hiso : ∀ z ∈ e.source, ∀ v w : TangentSpace I3 z,
      g.inner (e z) (mfderiv I3 I3 e z v) (mfderiv I3 I3 e z w) = h.inner z v w)
    (hV : V ⊆ e.source) : SpatialRoundComponent g eps (e x) (e '' V) := by
  letI : TopologicalSpace R.Z := R.topology
  letI : ChartedSpace ThreeSpace R.Z := R.charted
  letI : IsManifold I3 ∞ R.Z := R.smooth
  letI : T2Space R.Z := R.t2
  letI : CompactSpace R.Z := R.compact
  have hsrc (y : R.Z) : y ∈ R.map.source := by rw [R.source_eq]; trivial
  have hmem (y : R.Z) : R.map y ∈ V := R.target_eq.subset (R.map.map_source (hsrc y))
  have hx : x ∈ e.source := by
    have h0 := hV (hmem R.p)
    rwa [R.center_eq] at h0
  have hR := metricScalarAt_eq_of_isometryOn e hiso hx
  have hQ : 0 < metricScalarAt g (e x) := by
    rw [hR]
    exact R.Q_pos
  exact {
    Z := R.Z
    topology := R.topology
    charted := R.charted
    smooth := R.smooth
    t2 := R.t2
    compact := R.compact
    connected := R.connected
    metric := R.metric
    p := R.p
    scalar_one := R.scalar_one
    constant_curvature := R.constant_curvature
    map := R.map.trans e
    source_eq := by
      rw [partialDiffeomorph_trans_source, R.source_eq, univ_inter]
      exact eq_univ_of_forall fun y => hV (hmem y)
    target_eq := by
      rw [partialDiffeomorph_trans_target, R.target_eq, inter_eq_self_of_subset_right hV]
    center_eq := by rw [partialDiffeomorph_trans_apply, R.center_eq]
    Q_pos := hQ
    comparison := R.comparison.mapIsometry e (scaleMetric_isometryOn e hiso hx R.Q_pos hQ)
      (fun y _ => R.map.mdifferentiableAt (by decide) (hsrc y)) (fun y _ => hV (hmem y))
    metric_bounds := by
      intro z v
      rw [mfderiv_trans_apply R.map e (hsrc z) (hV (hmem z)), partialDiffeomorph_trans_apply,
        hiso _ (hV (hmem z)), hR]
      exact R.metric_bounds z v }

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

def SpatialCanonicalAlternative.pushforward {x : N} {V : Set N}
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
  have hR := metricScalarAt_eq_of_isometryOn e hiso hx
  cases A with
  | neck data => exact .neck (data.pushforward e hiso hV hVc (hneck data rfl))
  | cap data deep =>
    have htube : data.tube ⊆ e.source := (subset_union_right.trans data.union_eq.ge).trans hV
    refine .cap (data.pushforward e hV hVc
      (data.chain.pushforward e hiso htube (hcap data deep rfl))) ?_
    rintro _ ⟨y, hy, rfl⟩
    rw [hR]
    exact (deep y hy).trans (hdist y (subset_union_right.trans data.union_eq.ge hy))
  | positive whole data sec =>
    have hwhole : e '' V = connectedComponent (e x) := by
      rw [whole] at hVc hV ⊢
      exact image_connectedComponent_eq e hVc hV
    refine .positive hwhole
      (Classical.choice (positiveComponent_transport_of_partialDiffeomorph data e hV)) ?_
    rw [hR]
    exact secLower_image_of_isometryOn e hiso hV sec
  | round whole data =>
    have hwhole : e '' V = connectedComponent (e x) := by
      rw [whole] at hVc hV ⊢
      exact image_connectedComponent_eq e hVc hV
    exact .round hwhole (data.pushforward e hiso hV)

end Transport


section WitnessTransport

variable {N : Type u} [TopologicalSpace N] [ChartedSpace ThreeSpace N] [IsManifold I3 ∞ N]
  [T2Space N] [SigmaCompactSpace N] {h : SmoothRiemannianMetric I3 N}

omit [SigmaCompactSpace M] [SigmaCompactSpace N] in
theorem metricDistance_le_of_isometryOn (e : PartialDiffeomorph I3 I3 N M ∞)
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
  rw [← image_riemannianClosedBall_eq_of_isometric_on_compact_ball
    h g e x hd hdR hcpt hsrc (fun z hz v => hiso z (hsrc hz) v v)] at hmem
  obtain ⟨y', hy', hyy⟩ := hmem
  have hy's : y' ∈ e.source := hsrc (riemannianClosedBallOf_mono h x hdR.le hy')
  have hyy' : y' = y :=
    partialDiffeomorph_injOn_of_subset_source e (subset_refl e.source) hy's hy hyy
  subst hyy'
  exact ENNReal.toReal_le_of_le_ofReal hd hy'

omit [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M] [IsManifold I3 ∞ N] [T2Space N]
  [SigmaCompactSpace N] in
private theorem injective_isoSource (e : PartialDiffeomorph I3 I3 N M ∞) :
    Function.Injective (fun q : isoSource e => e q) := fun p q hpq =>
  Subtype.ext (partialDiffeomorph_injOn_of_subset_source e (subset_refl e.source) p.2 q.2 hpq)

theorem riemannianVolumeMeasure_image_eq_of_isometryOn (e : PartialDiffeomorph I3 I3 N M ∞)
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
@[simp] theorem SpatialCanonicalAlternative.pushforward_requiresVolume {x : N} {V : Set N}
    (A : SpatialCanonicalAlternative h eps C x V) (e : PartialDiffeomorph I3 I3 N M ∞)
    (hiso : ∀ z ∈ e.source, ∀ v w : TangentSpace I3 z,
      g.inner (e z) (mfderiv I3 I3 e z v) (mfderiv I3 I3 e z w) = h.inner z v w)
    (hV : V ⊆ e.source) (hVc : IsCompact V)
    (hdist : ∀ y ∈ V, metricDistance h x y ≤ metricDistance g (e x) (e y))
    (hneck : ∀ n, A = .neck n → ∀ z ∈ univ ×ˢ Ioo (-eps⁻¹) eps⁻¹, n.neck.map z ∈ e.source)
    (hcap : ∀ c d, A = .cap c d →
      ∀ i, ∀ z ∈ univ ×ˢ Ioo (-eps⁻¹) eps⁻¹, (c.chain.necks i).map z ∈ e.source) :
    (A.pushforward e hiso hV hVc hdist hneck hcap).requiresVolume = A.requiresVolume := by
  cases A <;> rfl

omit [SigmaCompactSpace M] [SigmaCompactSpace N] in
theorem SpatialCanonicalAlternative.pushforward_eq_cap {x : N} {V : Set N}
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
    (heq : A.pushforward e hiso hV hVc hdist hneck hcap = .cap cap depth) :
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
  have hB2 := image_riemannianBall_eq_of_isometric_on_compact_ball
    h g e x (by linarith : 0 < 2 * W.radius) hR hcpt hsrc (fun z hz v => hiso z (hsrc hz) v v)
  intro y hy
  apply metricDistance_le_of_isometryOn e hiso hcpt hsrc (hdom hy)
  have hy2 : e y ∈ riemannianBallOf g (e x) (2 * W.radius) := by
    rw [← hB2]
    exact ⟨y, W.inside_ball hy, rfl⟩
  exact lt_trans hy2 ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr hR)

def SpatialCanonicalWitness.pushforward {x : N} (W : SpatialCanonicalWitness h eps C1 C2 x)
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
  have hRx := metricScalarAt_eq_of_isometryOn e hiso hx
  have hquad : ∀ z ∈ riemannianClosedBallOf h x R, ∀ v : TangentSpace I3 z,
      g.inner (e z) (mfderiv I3 I3 e z v) (mfderiv I3 I3 e z v) = h.inner z v v :=
    fun z hz v => hiso z (hsrc hz) v v
  have hB1 := image_riemannianBall_eq_of_isometric_on_compact_ball
    h g e x hr (by linarith) hcpt hsrc hquad
  have hB2 := image_riemannianBall_eq_of_isometric_on_compact_ball
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
    alternative := W.alternative.pushforward e hiso hdom W.domain.compact hdist hneck hcap
    volume := ?_
    gradient := ?_ }
  · change e x ∈ interior (e '' W.domain.carrier)
    rw [← partialDiffeomorph_image_interior_of_subset_source e hdom]
    exact ⟨x, W.center_inside, rfl⟩
  · change riemannianBallOf g (e x) W.radius ⊆ e '' W.domain.carrier
    rw [← hB1]
    exact image_mono W.ball_inside
  · change e '' W.domain.carrier ⊆ riemannianBallOf g (e x) (2 * W.radius)
    rw [← hB2]
    exact image_mono W.inside_ball
  · rintro _ ⟨y, hy, rfl⟩
    rw [hRx, metricScalarAt_eq_of_isometryOn e hiso (hdom hy)]
    exact W.scalar_bounds y hy
  · rintro _ ⟨y, hy, rfl⟩
    have h0 := W.rm_bound y hy
    change Real.sqrt (normSq0S g (e y) 4 (metricRm04At g (e y))) ≤ _
    change Real.sqrt (normSq0S h y 4 (metricRm04At h y)) ≤ _ at h0
    rw [rmNormSq_eq_of_isometryOn e hiso (hdom hy), hRx]
    exact h0
  · intro hv
    have hv' : W.alternative.requiresVolume :=
      (SpatialCanonicalAlternative.pushforward_requiresVolume W.alternative e hiso hdom
        W.domain.compact hdist hneck hcap).mp hv
    change _ ≤ riemannianVolumeMeasure I3 M g (e '' W.domain.carrier)
    rw [riemannianVolumeMeasure_image_eq_of_isometryOn e hiso hdom W.domain.compact.isClosed, hRx]
    exact W.volume hv'
  · intro v'
    let L := (e.isLocalDiffeomorphAt I3 I3 ∞ hx).mfderivToContinuousLinearEquiv (by simp)
    obtain ⟨v, rfl⟩ := L.surjective v'
    have hL : L v = mfderiv I3 I3 e x v := rfl
    rw [hL, mfderiv_metricScalarAt_eq_of_isometryOn e hiso hx v, hiso x hx v v, hRx]
    exact W.gradient v

theorem SpatialCanonicalWitness.capTubeHasNeckChart.pushforward {x : N}
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
    (W.pushforward e hiso hR hcpt hsrc hneck hcap).capTubeHasNeckChart alpha := by
  intro cap depth heq
  change W.alternative.pushforward e hiso (W.domain_subset_of_ball_subset hR hsrc)
    W.domain.compact (W.metricDistance_le_image e hiso hR hcpt hsrc) hneck hcap = _ at heq
  obtain ⟨data, deep, hA, htube⟩ := SpatialCanonicalAlternative.pushforward_eq_cap heq
  obtain ⟨v, nk, hnk⟩ := hW data deep hA
  refine ⟨e v, nk.pushforward e hiso (hchart data deep hA v nk hnk), fun z => ?_⟩
  rw [htube z, hnk z]
  rfl

end WitnessTransport


section Corollaries

theorem SpatialCanonicalWitness.capTubeHasNeckChart_cast {p q : M} (hpq : p = q)
    {W : SpatialCanonicalWitness g eps C1 C2 p} (hW : W.capTubeHasNeckChart alpha) :
    (hpq ▸ W).capTubeHasNeckChart alpha := by
  subst hpq
  exact hW

variable {N : Type u} [TopologicalSpace N] [ChartedSpace ThreeSpace N] [IsManifold I3 ∞ N]
  [T2Space N] [SigmaCompactSpace N]

omit [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M] [IsManifold I3 ∞ N] [T2Space N]
  [SigmaCompactSpace N] in
private theorem exists_partialDiffeomorph_of_injective {f : N → M}
    (hf : IsLocalDiffeomorph I3 I3 ∞ f) (hinj : Function.Injective f) (x : N) :
    ∃ e : PartialDiffeomorph I3 I3 N M ∞, e.source = univ ∧ (e : N → M) = f := by
  obtain ⟨e, hs, -, hf'⟩ := IsLocalDiffeomorphOn.exists_partialDiffeomorph_of_injOn
    (hf.isLocalDiffeomorphOn univ) isOpen_univ ⟨x, trivial⟩ hinj.injOn
  exact ⟨e, hs, hf'⟩

def SpatialCanonicalWitness.pushforwardOfInjective {f : N → M}
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
  congrFun hspec.2 x ▸ W.pushforward e hiso hR hcpt (fun y _ => hmem y)
    (fun _ _ z _ => hmem _) (fun _ _ _ _ z _ => hmem _)

theorem SpatialCanonicalWitness.capTubeHasNeckChart.pushforwardOfInjective {f : N → M}
    (hf : IsLocalDiffeomorph I3 I3 ∞ f) (hinj : Function.Injective f) {x : N}
    {W : SpatialCanonicalWitness (localPullMetric g f hf) eps C1 C2 x}
    (hW : W.capTubeHasNeckChart alpha) {R : ℝ} (hR : 2 * W.radius < R)
    (hcpt : IsCompact (riemannianClosedBallOf (localPullMetric g f hf) x R)) :
    (W.pushforwardOfInjective hf hinj hR hcpt).capTubeHasNeckChart alpha := by
  have hspec := Classical.choose_spec (exists_partialDiffeomorph_of_injective hf hinj x)
  have hmem : ∀ y : N,
      y ∈ (Classical.choose (exists_partialDiffeomorph_of_injective hf hinj x)).source := by
    intro y
    rw [hspec.1]
    exact mem_univ y
  exact SpatialCanonicalWitness.capTubeHasNeckChart_cast _
    (hW.pushforward _ _ hR hcpt (fun y _ => hmem y) _ _ fun _ _ _ _ _ _ z _ => hmem _)

omit [SigmaCompactSpace M] in
private theorem subtypeVal_symm_isometry (O : TopologicalSpace.Opens M)
    (i : PartialDiffeomorph I3 I3 O M ∞) (hi : ∀ q : O, i q = q) :
    ∀ z ∈ i.symm.source, ∀ v w : TangentSpace I3 z,
      (g.restrictOpen O).inner (i.symm z) (mfderiv I3 I3 i.symm z v) (mfderiv I3 I3 i.symm z w) =
        g.inner z v w := by
  intro z hz v w
  have hval : ((i.symm z : O) : M) = z := (hi _).symm.trans (i.right_inv' hz)
  have hd : ∀ u : TangentSpace I3 z, mfderiv I3 I3 i.symm z u = u := by
    intro u
    have hloc : (fun q => ((i.symm q : O) : M)) =ᶠ[nhds z] id :=
      Filter.eventuallyEq_of_mem (i.open_target.mem_nhds hz) fun q hq =>
        (hi _).symm.trans (i.right_inv' hq)
    have hcomp := mfderiv_comp z
      (hasMFDerivAt_subtype_val (I := I3) O (i.symm z)).mdifferentiableAt
      (i.symm.mdifferentiableAt (by decide) hz)
    rw [mfderiv_subtype_val] at hcomp
    have h1 : mfderiv I3 I3 (fun q => ((i.symm q : O) : M)) z u = mfderiv I3 I3 i.symm z u :=
      DFunLike.congr_fun hcomp u
    rw [hloc.mfderiv_eq, mfderiv_id] at h1
    exact h1.symm
  rw [SmoothRiemannianMetric.restrictOpen_inner, hd, hd]
  generalize ((i.symm z : O) : M) = a at hval ⊢
  subst hval
  rfl

def SpatialCanonicalWitness.restrictOpen {x : M} (W : SpatialCanonicalWitness g eps C1 C2 x)
    (O : TopologicalSpace.Opens M) [SigmaCompactSpace O] (hx : x ∈ O) {R : ℝ}
    (hR : 2 * W.radius < R) (hcpt : IsCompact (riemannianClosedBallOf g x R))
    (hsrc : riemannianClosedBallOf g x R ⊆ O)
    (hneck : ∀ n, W.alternative = .neck n →
      n.neck.map '' (univ ×ˢ Ioo (-eps⁻¹) eps⁻¹) ⊆ O)
    (hcap : ∀ c d, W.alternative = .cap c d →
      ∀ i, (c.chain.necks i).map '' (univ ×ˢ Ioo (-eps⁻¹) eps⁻¹) ⊆ O) :
    SpatialCanonicalWitness (g.restrictOpen O) eps C1 C2 ⟨x, hx⟩ :=
  let i := DifferentialGeometry.Topology.PartialDiffeomorph.subtypeVal (I := I3) O ⟨⟨x, hx⟩⟩
  have hsource : i.symm.source = (O : Set M) :=
    O.openPartialHomeomorphSubtypeCoe_target ⟨⟨x, hx⟩⟩
  have hix : i.symm x = ⟨x, hx⟩ := Subtype.ext (i.right_inv' (by
    change x ∈ i.symm.source
    rw [hsource]
    exact hx))
  hix ▸ W.pushforward i.symm (subtypeVal_symm_isometry O i fun _ => rfl) hR hcpt
    (hsource.symm ▸ hsrc)
    (fun n hn z hz => hsource.symm ▸ hneck n hn ⟨z, hz, rfl⟩)
    (fun c d hc k z hz => hsource.symm ▸ hcap c d hc k ⟨z, hz, rfl⟩)

theorem SpatialCanonicalWitness.capTubeHasNeckChart.restrictOpen {x : M}
    {W : SpatialCanonicalWitness g eps C1 C2 x} (hW : W.capTubeHasNeckChart alpha)
    (O : TopologicalSpace.Opens M) [SigmaCompactSpace O] (hx : x ∈ O) {R : ℝ}
    (hR : 2 * W.radius < R) (hcpt : IsCompact (riemannianClosedBallOf g x R))
    (hsrc : riemannianClosedBallOf g x R ⊆ O)
    (hneck : ∀ n, W.alternative = .neck n →
      n.neck.map '' (univ ×ˢ Ioo (-eps⁻¹) eps⁻¹) ⊆ O)
    (hcap : ∀ c d, W.alternative = .cap c d →
      ∀ i, (c.chain.necks i).map '' (univ ×ˢ Ioo (-eps⁻¹) eps⁻¹) ⊆ O)
    (hchart : ∀ c d, W.alternative = .cap c d → ∀ (v : M) (nk : SpatialNeck g alpha v),
      (∀ z, c.tubeMap z = nk.map z) → nk.map '' (univ ×ˢ Ioo (-alpha⁻¹) alpha⁻¹) ⊆ O) :
    (W.restrictOpen O hx hR hcpt hsrc hneck hcap).capTubeHasNeckChart alpha := by
  let i := DifferentialGeometry.Topology.PartialDiffeomorph.subtypeVal (I := I3) O ⟨⟨x, hx⟩⟩
  have hsource : i.symm.source = (O : Set M) :=
    O.openPartialHomeomorphSubtypeCoe_target ⟨⟨x, hx⟩⟩
  exact SpatialCanonicalWitness.capTubeHasNeckChart_cast _
    (hW.pushforward _ _ hR hcpt _ _ _ fun c d hc v nk hnk z hz =>
      hsource.symm ▸ hchart c d hc v nk hnk ⟨z, hz, rfl⟩)

end Corollaries


end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
