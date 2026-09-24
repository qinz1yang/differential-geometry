import DifferentialGeometry.Geometry.Comparison.BallCapture
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorphRange
import DifferentialGeometry.Topology.Manifold.OpenSubtypeDiffeomorph

set_option autoImplicit false
noncomputable section
open Set Manifold Function
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Metric

variable {E F H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] [T2Space N]

theorem ball_subset_image_of_metric_lower_on_opens
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (U : TopologicalSpace.Opens N) (f : U → M)
    (hf : IsLocalDiffeomorph J I ∞ f) (hinj : Injective f)
    (p : U) {R L : ℝ} (hR : 0 < R) (hL : 0 < L)
    (hcompact : IsCompact (riemannianClosedBallOf h p.val R))
    (hsource : riemannianClosedBallOf h p.val R ⊆ U)
    (hlower : ∀ x : U, x.val ∈ riemannianClosedBallOf h p.val R →
      ∀ v : TangentSpace J x, h.inner x.val v v ≤ L ^ 2 *
        g.inner (f x) (mfderiv J I f x v) (mfderiv J I f x v)) :
    riemannianBallOf g (f p) (R / L) ⊆
      f '' {x : U | x.val ∈ riemannianClosedBallOf h p.val R} := by
  let V := hf.image
  let e : Diffeomorph J I U V ∞ := Topology.diffeomorphRangeOfInjective hf hinj
  let iU := DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph J U ⟨p⟩
  let iV := DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph I V ⟨e p⟩
  let Φ := (iU.symm.trans e.toPartialDiffeomorph).trans iV
  have hsrc : Φ.source = (U : Set N) := by
    ext x
    change ((x ∈ iU.target ∧ iU.symm x ∈ (univ : Set U)) ∧
      e (iU.symm x) ∈ (univ : Set V)) ↔ x ∈ U
    simp only [mem_univ, and_true, iU,
      DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_target]
    rfl
  have hmap (x : U) : Φ x.val = f x := by
    change (e (iU.symm x.val) : M) = f x
    rw [show iU.symm x.val = x from
      DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_symm_apply J U ⟨p⟩ x.property]
    rfl
  have hder (x : U) : mfderiv J I f x = mfderiv J I (Φ : N → M) x.val := by
    have hfun : (fun x : U => Φ x.val) = f := funext hmap
    rw [← hfun]
    exact mfderiv_restrict_open (Φ : N → M) U x
  have hlow : ∀ x ∈ riemannianClosedBallOf h p.val R, ∀ v : TangentSpace J x,
      h.inner x v v ≤ L ^ 2 * g.inner (Φ x)
        (mfderiv J I (Φ : N → M) x v) (mfderiv J I (Φ : N → M) x v) := by
    intro x hx v
    let q : U := ⟨x, hsource hx⟩
    have hb := hlower q hx v
    rw [hder, ← hmap q] at hb
    exact hb
  have hcap := PartialDiffeomorph.ball_subset_image_closedBall_of_metric_lower
    h g Φ p.val hR hL hcompact (hsource.trans (by rw [hsrc])) hlow
  rw [hmap p] at hcap
  intro x hx
  obtain ⟨q, hq, hΦq⟩ := hcap hx
  exact ⟨⟨q, hsource hq⟩, hq, (hmap ⟨q, hsource hq⟩).symm.trans hΦq⟩

end DifferentialGeometry.Geometry.Metric
