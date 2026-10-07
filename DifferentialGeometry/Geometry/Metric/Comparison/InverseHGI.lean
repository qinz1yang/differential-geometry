import DifferentialGeometry.Geometry.Metric.Comparison.PartialDiffeomorphDistance
import DifferentialGeometry.Geometry.Metric.Comparison.BallCaptureHGI

/-!
# Inverse comparison for two universes (S-HG-INTAKE, suffix `_HGI`)

Donor file `Geometry/Metric/Comparison/Inverse.lean` (467465bc6c) with its five theorems renamed
`_HGI`. The tracked file of the same path states them for `M N : Type u`; the donor for `M :
Type u`, `N : Type v`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open scoped _root_.Topology ContDiff Manifold ENNReal
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open CanonicalNeighborhood

universe u v

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

section Differential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type u} {N : Type v} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]

theorem inverse_metric_upper_of_metric_lower_HGI
    (h : SmoothRiemannianMetric I N) (g : SmoothRiemannianMetric I M)
    (F : PartialDiffeomorph I I N M (∞ : WithTop ℕ∞))
    (y : M) (hy : y ∈ F.target) (L : ℝ)
    (hlower : ∀ w : TangentSpace I (F.symm y),
      h.inner (F.symm y) w w ≤ L ^ 2 * g.inner (F (F.symm y))
        (mfderiv I I (F : N → M) (F.symm y) w)
        (mfderiv I I (F : N → M) (F.symm y) w))
    (v : TangentSpace I y) :
    h.inner (F.symm y) (mfderiv I I (F.symm : M → N) y v)
      (mfderiv I I (F.symm : M → N) y v) ≤ L ^ 2 * g.inner y v v := by
  have hF : MDifferentiableAt I I (F : N → M) (F.symm y) :=
    F.mdifferentiableAt (by simp : (∞ : WithTop ℕ∞) ≠ 0) (F.map_target' hy)
  have hInv : MDifferentiableAt I I (F.symm : M → N) y :=
    F.symm.mdifferentiableAt (by simp : (∞ : WithTop ℕ∞) ≠ 0) hy
  have htarget : ∀ᶠ z in 𝓝 y, z ∈ F.target := F.open_target.mem_nhds hy
  have heq : (F : N → M) ∘ (F.symm : M → N) =ᶠ[𝓝 y] id :=
    htarget.mono fun _ hz => F.right_inv' hz
  have hderiv : mfderiv I I (F : N → M) (F.symm y)
      (mfderiv I I (F.symm : M → N) y v) = v := by
    have hcomp := mfderiv_comp_apply y hF hInv v
    have hmaps : mfderiv I I ((F : N → M) ∘ (F.symm : M → N)) y =
        mfderiv I I (id : M → M) y := heq.mfderiv_eq
    have hid := DFunLike.congr_fun hmaps v
    rw [mfderiv_id] at hid
    exact hcomp.symm.trans hid
  have hbound := hlower (mfderiv I I (F.symm : M → N) y v)
  rw [hderiv] at hbound
  have hright : F (F.symm y) = y := F.right_inv' hy
  rw [hright] at hbound
  exact hbound

end Differential

section Capture

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type u} {N : Type v} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T2Space N]

theorem inverse_mem_closedBall_of_metric_lower_HGI
    (h : SmoothRiemannianMetric I N) (g : SmoothRiemannianMetric I M)
    (F : PartialDiffeomorph I I N M (∞ : WithTop ℕ∞)) (p : N)
    {R L r : ℝ} (hR : 0 < R) (hL : 0 < L) (hr : r < R / L)
    (hcpt : IsCompact (riemannianClosedBallOf (I := I) h p R))
    (hsource : riemannianClosedBallOf (I := I) h p R ⊆ F.source)
    (hlower : ∀ x ∈ riemannianClosedBallOf (I := I) h p R,
      ∀ v : TangentSpace I x, h.inner x v v ≤
        L ^ 2 * g.inner (F x) (mfderiv I I (F : N → M) x v)
          (mfderiv I I (F : N → M) x v))
    (y : M) (hy : y ∈ riemannianClosedBallOf (I := I) g (F p) r) :
    y ∈ F.target ∧ F.symm y ∈ riemannianClosedBallOf (I := I) h p R := by
  obtain ⟨x, hx, rfl⟩ :=
    CanonicalNeighborhood.closedBall_subset_image_of_metric_lower_HGI
      h g F p hR hL hr hcpt hsource hlower hy
  refine ⟨F.map_source' (hsource hx), ?_⟩
  have hleft : F.symm (F x) = x := F.left_inv' (hsource hx)
  rw [hleft]
  exact hx

theorem inverse_control_on_captured_ball_HGI
    (h : SmoothRiemannianMetric I N) (g : SmoothRiemannianMetric I M)
    (F : PartialDiffeomorph I I N M (∞ : WithTop ℕ∞)) (p : N)
    {R L r : ℝ} (hR : 0 < R) (hL : 0 < L) (hr : r < R / L)
    (hcpt : IsCompact (riemannianClosedBallOf (I := I) h p R))
    (hsource : riemannianClosedBallOf (I := I) h p R ⊆ F.source)
    (hlower : ∀ x ∈ riemannianClosedBallOf (I := I) h p R,
      ∀ v : TangentSpace I x, h.inner x v v ≤
        L ^ 2 * g.inner (F x) (mfderiv I I (F : N → M) x v)
          (mfderiv I I (F : N → M) x v)) :
    riemannianClosedBallOf (I := I) g (F p) r ⊆ F.symm.source ∧
      ∀ y ∈ riemannianClosedBallOf (I := I) g (F p) r,
        ∀ v : TangentSpace I y,
          h.inner (F.symm y) (mfderiv I I (F.symm : M → N) y v)
            (mfderiv I I (F.symm : M → N) y v) ≤ L ^ 2 * g.inner y v v := by
  have hcapture := inverse_mem_closedBall_of_metric_lower_HGI
    h g F p hR hL hr hcpt hsource hlower
  refine ⟨fun y hy => (hcapture y hy).1, ?_⟩
  intro y hy v
  exact inverse_metric_upper_of_metric_lower_HGI h g F y (hcapture y hy).1 L
    (hlower (F.symm y) (hcapture y hy).2) v

theorem edistOf_symm_le_of_metric_lower_on_compact_ball_HGI
    (h : SmoothRiemannianMetric I N) (g : SmoothRiemannianMetric I M)
    (F : PartialDiffeomorph I I N M (∞ : WithTop ℕ∞)) (p : N)
    {R L r : ℝ} (hR : 0 < R) (hL : 0 < L) (hr0 : 0 < r) (hr : r < R / L)
    (hcpt : IsCompact (riemannianClosedBallOf (I := I) h p R))
    (hsource : riemannianClosedBallOf (I := I) h p R ⊆ F.source)
    (hlower : ∀ x ∈ riemannianClosedBallOf (I := I) h p R,
      ∀ v : TangentSpace I x, h.inner x v v ≤
        L ^ 2 * g.inner (F x) (mfderiv I I (F : N → M) x v)
          (mfderiv I I (F : N → M) x v))
    (y : M) (hy : riemannianEDistOf (I := I) g (F p) y < ENNReal.ofReal r) :
    riemannianEDistOf (I := I) h p (F.symm y) ≤
      ENNReal.ofReal L * riemannianEDistOf (I := I) g (F p) y := by
  obtain ⟨hInvSource, hInvUpper⟩ := inverse_control_on_captured_ball_HGI
    h g F p hR hL hr hcpt hsource hlower
  have hpball : p ∈ riemannianClosedBallOf (I := I) h p R := by
    change riemannianEDistOf (I := I) h p p ≤ ENNReal.ofReal R
    rw [riemannianEDistOf_self]
    exact bot_le
  have hdist := edistOf_map_le_of_metric_upper_on_ball
    g h F.symm (F p) y hr0 hL hInvSource hInvUpper hy
  have hleft : F.symm (F p) = p := F.left_inv' (hsource hpball)
  simpa only [hleft] using hdist

theorem edistOf_symm_pair_le_of_metric_lower_on_compact_ball_HGI
    (h : SmoothRiemannianMetric I N) (g : SmoothRiemannianMetric I M)
    (F : PartialDiffeomorph I I N M (∞ : WithTop ℕ∞)) (p : N)
    {R L r rho : ℝ} (hR : 0 < R) (hL : 0 < L)
    (hrho : 0 ≤ rho) (hbuffer : 3 * rho < r) (hr : r < R / L)
    (hcpt : IsCompact (riemannianClosedBallOf (I := I) h p R))
    (hsource : riemannianClosedBallOf (I := I) h p R ⊆ F.source)
    (hlower : ∀ x ∈ riemannianClosedBallOf (I := I) h p R,
      ∀ v : TangentSpace I x, h.inner x v v ≤
        L ^ 2 * g.inner (F x) (mfderiv I I (F : N → M) x v)
          (mfderiv I I (F : N → M) x v))
    (y z : M)
    (hy : y ∈ riemannianClosedBallOf (I := I) g (F p) rho)
    (hz : z ∈ riemannianClosedBallOf (I := I) g (F p) rho) :
    riemannianEDistOf (I := I) h (F.symm y) (F.symm z) ≤
      ENNReal.ofReal L * riemannianEDistOf (I := I) g y z := by
  obtain ⟨hInvSource, hInvUpper⟩ := inverse_control_on_captured_ball_HGI
    h g F p hR hL hr hcpt hsource hlower
  exact edistOf_map_le_of_metric_upper_on_buffered_ball
    g h F.symm (F p) y z hrho hbuffer hL hInvSource hInvUpper hy hz

end Capture

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
