import DifferentialGeometry.Geometry.Metric.Comparison.BallImage
import DifferentialGeometry.Geometry.Metric.Distance.Ball
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Basic

set_option autoImplicit false

open Bundle Manifold Set Filter
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry.PartialDiffeomorph

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem riemannianBallOf_subset_image_of_metric_lower
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RegularSpace M]
    {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
    [T3Space N]
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (Φ : PartialDiffeomorph I J M N ∞) {O x : M} {r R A C : ℝ} (hC : 0 ≤ C)
    (hcompact : IsCompact (riemannianClosedBallOf g O R))
    (hsub : riemannianClosedBallOf g O R ⊆ Φ.source)
    (hlower : ∀ z ∈ riemannianClosedBallOf g O R, ∀ v : TangentSpace I z,
      g.inner z v v ≤ C ^ 2 * h.inner (Φ z)
        (mfderiv I J (Φ : M → N) z v) (mfderiv I J (Φ : M → N) z v))
    (hx : x ∈ riemannianBallOf g O r) (hmargin : C * A + r < R) :
    riemannianBallOf h (Φ x) A ⊆ (Φ : M → N) '' riemannianClosedBallOf g O R := by
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : PseudoEMetricSpace M := .ofRiemannianMetric I M
  let : RiemannianBundle (TangentSpace J : N → Type _) := ⟨h.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle F (TangentSpace J : N → Type _) :=
    ⟨h.inner, h.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : PseudoEMetricSpace N := .ofRiemannianMetric J N
  have hgball : Metric.closedEBall O (ENNReal.ofReal R) = riemannianClosedBallOf g O R := by
    ext y
    change edist y O ≤ ENNReal.ofReal R ↔ edist O y ≤ ENNReal.ofReal R
    rw [edist_comm]
  have hhball : Metric.eball (Φ x) (ENNReal.ofReal A) = riemannianBallOf h (Φ x) A := by
    ext y
    change edist y (Φ x) < ENNReal.ofReal A ↔ edist (Φ x) y < ENNReal.ofReal A
    rw [edist_comm]
  rw [← hgball] at hcompact hsub
  rw [← hgball, ← hhball]
  refine eball_subset_image_closedEBall_of_enorm_mfderiv_symm_le
    (ofLE Φ (by decide)) (C := ⟨C, hC⟩) hcompact hsub ?_ ?_ hmargin
  · intro z hz w
    obtain ⟨y, hy, hyz⟩ := hz
    have hyS : y ∈ Φ.source := hsub hy
    have hzT : z ∈ Φ.target := hyz ▸ Φ.map_source' hyS
    have heq : (Φ : M → N) ∘ (Φ.symm : N → M) =ᶠ[𝓝 z] id := by
      filter_upwards [Φ.open_target.mem_nhds hzT] with q hq
      exact Φ.right_inv hq
    have hchain : mfderiv I J (Φ : M → N) (Φ.symm z)
        (mfderiv J I (Φ.symm : N → M) z w) = w := by
      have hh := (mfderiv_comp z
        (Φ.mdifferentiableAt (by simp) (Φ.map_target' hzT))
        (Φ.symm.mdifferentiableAt (by simp) hzT)).symm.trans heq.mfderiv_eq
      have hw := DFunLike.congr_fun hh w
      simp only [mfderiv_id] at hw
      exact hw
    have hinv : Φ.symm z = y := by rw [← hyz]; exact Φ.left_inv hyS
    have hquad := hlower (Φ.symm z) (by simpa only [hinv, ← hgball] using hy)
      (mfderiv J I (Φ.symm : N → M) z w)
    simp only [hchain] at hquad
    have hmetric : h.inner (Φ (Φ.symm z)) w w = h.inner z w w :=
      congrArg (fun q : N => h.inner q (show F from w) (show F from w)) (Φ.right_inv hzT)
    rw [hmetric] at hquad
    change ‖mfderiv J I (Φ.symm : N → M) z w‖ₑ ≤ ENNReal.ofReal C * ‖w‖ₑ
    rw [← ofReal_norm, ← ofReal_norm, norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner]
    change ENNReal.ofReal (Real.sqrt (g.inner (Φ.symm z)
      (mfderiv J I (Φ.symm : N → M) z w) (mfderiv J I (Φ.symm : N → M) z w))) ≤
        ENNReal.ofReal C * ENNReal.ofReal (Real.sqrt (h.inner z w w))
    calc
      _ ≤ ENNReal.ofReal (Real.sqrt (C ^ 2 * h.inner z w w)) :=
        ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt hquad)
      _ = _ := by rw [Real.sqrt_mul (sq_nonneg C), Real.sqrt_sq hC, ENNReal.ofReal_mul hC]
  · change edist x O < ENNReal.ofReal r
    rw [edist_comm]
    exact hx

end DifferentialGeometry.PartialDiffeomorph
