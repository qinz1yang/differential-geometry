import DifferentialGeometry.Geometry.Collapse.CircleFiberKernel
import DifferentialGeometry.Geometry.Collapse.DistanceSmoothing.LocalToGlobal
import DifferentialGeometry.Geometry.Comparison.Soul.SoulAngles

/-!
# LC83: the circle-fibre local model on a complete Riemannian manifold

Blueprint 207A, LC83 (`prop:collapse-two-stratum-local`, A:25167–25199), at a fixed scale (apply it to
the rescaled metric `ρ(p)⁻² g`).

* `joinedIn_of_lipschitz_two`: minimizing segments from `B(p, 2)` to `p` stay in `{‖η‖ < 4}`.
* `circleFiber_local_model` (LC83): `η : B(p, 200) → ℝ²` smooth of rank two, `2`-Lipschitz,
  `η(p) = 0`, `η⁻¹ B(0, 100) ⊆ B(p, 102)`, `η⁻¹(0) ⊆ B(p, 2)`; then `η` on `η⁻¹ B(0, 100)` is a smooth
  proper surjective submersion onto `B(0, 100)` with compact connected fibres, trivial over every
  `B(0, R)`, `R < 100`, with fibre the zero fibre.

Deviations from the row: the hypothesis "connected" and the dimension three are not used (for a
three-manifold the fibre is a compact connected boundaryless manifold modelled on `Fin 1 → ℝ`); the
identification of the fibre with `S¹` waits for the classification of compact connected 1-manifolds
(lane W4-FCb); triviality is proved over every `B(0, R)`, `R < 100` (the row's "in particular").
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle
open scoped ContDiff Manifold Topology NNReal

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Geometry.Topology

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

/-- On a complete Riemannian manifold, a `2`-Lipschitz map vanishing at `p` joins every point of
`B(p, 2)` to `p` inside `{‖η‖ < 4}` along a minimizing segment. -/
theorem joinedIn_of_lipschitz_two (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    {p : M} {η : M → ℝ²} (hlip : LipschitzOnWith 2 η (ball p 200)) (hp : η p = 0)
    {x : M} (hx : x ∈ ball p 2) :
    JoinedIn {y | y ∈ ball p 200 ∧ ‖η y‖ < 4} x p := by
  obtain ⟨c, hc, hc0, hc1, hcd⟩ := exists_riemannian_segment g hEnorm x p
  have hxp : dist x p < 2 := hx
  let γ : Path x p :=
    { toFun := fun t => c t
      continuous_toFun := hc.comp continuous_subtype_val
      source' := hc0
      target' := hc1 }
  refine ⟨γ, fun t => ?_⟩
  have ht0 : (0 : ℝ) ≤ t := t.2.1
  have ht1 : (t : ℝ) ≤ 1 := t.2.2
  have hdist : dist (c t) p < 2 := by
    have h := hcd t 1 ht1
    rw [hc1] at h
    have hmul : dist x p * (1 - t) ≤ dist x p := by
      have := dist_nonneg (x := x) (y := p)
      nlinarith
    linarith
  have hct : c t ∈ ball p 200 := mem_ball.mpr (by linarith)
  refine ⟨hct, ?_⟩
  have h := hlip.dist_le_mul (c t) hct p (mem_ball_self (by norm_num : (0 : ℝ) < 200))
  rw [hp, dist_zero_right] at h
  change ‖η (c t)‖ < 4
  push_cast at h
  linarith

/-- **LC83** (the circle-fibre local model), on a complete Riemannian manifold. Let
`η : B(p, 200) → ℝ²` be smooth with surjective differential, `2`-Lipschitz, `η(p) = 0`, with
`η⁻¹ B(0, 100) ⊆ B(p, 102)` and `η⁻¹(0) ⊆ B(p, 2)`. Then `η : η⁻¹ B(0, 100) → B(0, 100)` is a smooth
proper surjective submersion with compact connected fibres, trivial over every `B(0, R)`, `R < 100`,
with fibre the zero fibre. For a three-manifold that fibre is a compact connected boundaryless
manifold modelled on `Fin 1 → ℝ`. -/
theorem circleFiber_local_model (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    {p : M} {η : M → ℝ²} (hη : ContMDiffOn I 𝓘(ℝ, ℝ²) ∞ η (ball p 200))
    (hrank : ∀ x ∈ ball p 200, Surjective (mfderiv I 𝓘(ℝ, ℝ²) η x))
    (hlip : LipschitzOnWith 2 η (ball p 200)) (hp : η p = 0)
    (h102 : ∀ x ∈ ball p 200, ‖η x‖ < 100 → x ∈ ball p 102)
    (h2 : ∀ x ∈ ball p 200, η x = 0 → x ∈ ball p 2) :
    let f := diskPreimageMap (ball p 200) isOpen_ball η hη.continuousOn 100
    ContMDiff I 𝓘(ℝ, ℝ²) ∞ f ∧ (∀ x, Surjective (mfderiv I 𝓘(ℝ, ℝ²) f x)) ∧ IsProperMap f ∧
      Surjective f ∧ (∀ z, IsCompact (f ⁻¹' {z}) ∧ IsConnected (f ⁻¹' {z})) ∧
      ∀ R (hR : 0 < R) (hRr : R < 100),
        let y₀ : planeBallOpens 100 := ⟨0, zero_mem_planeBallOpens (hR.trans hRr)⟩
        let _ := regularFiberChartedSpace f y₀ (contMDiff_diskPreimageMap isOpen_ball hη 100)
          (fun x _ ↦ surjective_mfderiv_diskPreimageMap isOpen_ball hη hrank 100 x)
        let U : TopologicalSpace.Opens
            (diskPreimageOpens (ball p 200) isOpen_ball η hη.continuousOn 100) :=
          ⟨f ⁻¹' planeBallInner 100 R,
            (planeBallInner 100 R).isOpen.preimage (continuous_diskPreimageMap isOpen_ball _ 100)⟩
        ∃ (hy : y₀ ∈ planeBallInner 100 R) (Θ : Diffeomorph
            (𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ ℝ²) → ℝ).prod 𝓘(ℝ, ℝ²)) I
            ({x // f x = y₀} × planeBallInner 100 R) U ∞),
          (∀ q, f (Θ q).1 = q.2.1) ∧ (∀ x, (Θ (x, ⟨y₀, hy⟩)).1 = x.1) :=
  exists_trivial_proper_submersion_of_enclosure isOpen_ball hη hrank
    (soul_isCompact_closedBall g hEnorm p 102) (closedBall_subset_ball (by norm_num))
    (fun x hx hx100 => ball_subset_closedBall (h102 x hx hx100)) (mem_ball_self (by norm_num)) hp
    (by norm_num : (4 : ℝ) < 100)
    (fun x hx hx0 => joinedIn_of_lipschitz_two g hEnorm hlip hp (h2 x hx hx0))

end DifferentialGeometry.Geometry.Collapse
