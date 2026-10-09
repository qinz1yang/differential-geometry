import DifferentialGeometry.Geometry.Metric.Comparison.BallImage

set_option autoImplicit false

open Bundle Manifold Set Filter
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry.PartialDiffeomorph


theorem ball_subset_image_closedBall_of_enorm_mfderiv_lower
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
    {M : Type*} [PseudoMetricSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
    {N : Type*} [PseudoMetricSpace N] [ChartedSpace G N] [T2Space N]
    [RiemannianBundle (fun x : N => TangentSpace J x)] [IsRiemannianManifold J N]
    (Φ : PartialDiffeomorph I J M N 1) {O x : M} {r R A : ℝ} {C : NNReal}
    (hcompact : IsCompact (Metric.closedBall O R))
    (hsub : Metric.closedBall O R ⊆ Φ.source)
    (hlower : ∀ y ∈ Metric.closedBall O R, ∀ v : TangentSpace I y,
      ‖v‖ₑ ≤ ENNReal.ofReal (C : ℝ) * ‖mfderiv I J (Φ : M → N) y v‖ₑ)
    (hx : x ∈ Metric.ball O r) (hmargin : (C : ℝ) * A + r < R) :
    Metric.ball ((Φ : M → N) x) A ⊆ (Φ : M → N) '' Metric.closedBall O R := by
  apply ball_subset_image_closedBall_of_enorm_mfderiv_symm_le Φ hcompact hsub ?_ hx hmargin
  intro z hz w
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
  have hinv : Φ.symm z = y := by
    rw [← hyz]
    exact Φ.left_inv hyS
  have hb := hlower (Φ.symm z) (by simpa only [hinv] using hy)
    (mfderiv J I (Φ.symm : N → M) z w)
  simp only [hchain] at hb
  have hnorm :
      ‖(show TangentSpace J (Φ (Φ.symm z)) from (show F from w))‖ₑ =
        ‖(show TangentSpace J z from (show F from w))‖ₑ :=
    congrArg (fun q : N => ‖(show TangentSpace J q from (show F from w))‖ₑ)
      (Φ.right_inv hzT)
  rw [hnorm] at hb
  exact hb

end DifferentialGeometry.PartialDiffeomorph
