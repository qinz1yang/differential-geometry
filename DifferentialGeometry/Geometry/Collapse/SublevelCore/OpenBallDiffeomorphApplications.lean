import DifferentialGeometry.Geometry.Collapse.SublevelCore.OpenBallDiffeomorph

/-!
# Consumer of LC60 (smooth open-distance-ball comparison)

`exists_open_distance_ball_diffeomorph_symm` reads LC60 from the side of the ball: the inverse
`J⁻¹ : B(p, ρ) → int {η ≤ ρ}` also moves points by less than `3e / (1 - ε)`, and it is the
identity on the smaller ball `B(p, ρ - 3e)`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function Bundle
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Operator

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

/-- **Consumer of LC60.** The inverse of the LC60 diffeomorphism, defined on the open distance
ball `B(p, ρ)`, has displacement `< 3e / (1 - ε)` and is the identity on `B(p, ρ - 3e)`. -/
theorem exists_open_distance_ball_diffeomorph_symm {m : ℕ} (hdim : Module.finrank ℝ E = m + 1)
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g) {p : M}
    {η : M → ℝ} {ε : ℝ≥0} {e : ℝ} (hε : (ε : ℝ) < 1 / 4) (he : e < 1 / 40)
    (hclose : ∀ x, |η x - dist p x| < e) (hlip : LipschitzWith ε (fun x => η x - dist p x))
    {W : Set M} (hW : IsOpen W) (hCW : ∀ x, 1 / 10 ≤ dist p x → dist p x ≤ 10 → x ∈ W)
    (hηW : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ η W)
    (hgrad : ∀ x, 1 / 10 ≤ dist p x → dist p x ≤ 10 →
      (1 - (ε : ℝ)) ^ 2 ≤ g.inner x (gradientFun (I := I) g η x) (gradientFun (I := I) g η x))
    {ρ : ℝ} (hρ : ρ ∈ Icc (1 / 5 : ℝ) 2) :
    ∃ J : PartialDiffeomorph I I M M ∞, J.source = interior {x | η x ≤ ρ} ∧
      J.target = Metric.ball p ρ ∧ (∀ y ∈ J.target, dist (J.symm y) y < 3 * e / (1 - ε)) ∧
      ∀ y, dist p y < ρ - 3 * e → y ∈ J.target ∧ J.symm y = y := by
  obtain ⟨J, hJs, hJt, hJid, hJd, -⟩ :=
    exists_open_distance_ball_diffeomorph hdim g hEnorm hε he hclose hlip hW hCW hηW hgrad hρ
  refine ⟨J, hJs, hJt, fun y hy => ?_, fun y hy => ?_⟩
  · have hx : J.symm y ∈ J.source := J.map_target' hy
    have hJx : J (J.symm y) = y := J.right_inv' hy
    have h := hJd _ hx
    rw [hJx, dist_comm] at h
    exact h
  · have h := abs_lt.mp (hclose y)
    have hηy : η y ≤ ρ - 2 * e := by linarith
    have hys : y ∈ J.source := by
      rw [hJs]
      have hU : IsOpen {x : M | η x < ρ} := isOpen_lt
        ((hlip.continuous.add (continuous_const.dist continuous_id)).congr
          (fun x => sub_add_cancel (η x) (dist p x))) continuous_const
      exact interior_maximal (fun x (hx : η x < ρ) => show η x ≤ ρ from le_of_lt hx) hU
        (show η y < ρ by linarith)
    have hJy : J y = y := hJid y hys hηy
    refine ⟨?_, ?_⟩
    · rw [← hJy]
      exact J.map_source' hys
    · have h2 : J.symm (J y) = y := J.left_inv' hys
      rwa [hJy] at h2

end DifferentialGeometry.Geometry.Collapse
