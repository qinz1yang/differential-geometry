import DifferentialGeometry.Geometry.Collapse.CircleFiberLocalModel
import DifferentialGeometry.Topology.Manifold.OneManifold.CircleConsequences

/-!
# LC83: every fibre of the circle-fibre local model is a circle

Blueprint 207A, LC83 (`prop:collapse-two-stratum-local`, A:25167–25199), last clause. On a complete
Riemannian three-manifold, every fibre of `η : η⁻¹ B(0, 100) → B(0, 100)` from
`circleFiber_local_model` is diffeomorphic to the circle: it is a compact connected regular fibre of
codimension two, and the classification of compact connected 1-manifolds
(`OneManifold.nonempty_circle_diffeomorph_regularFiber`, lane N1) identifies it with `Circle`.
Together with `circleFiber_local_model` (properness, surjectivity, submersion, connected fibres,
triviality over every `B(0, R)`, `R < 100`) this gives `η⁻¹ B(0, R) ≅ S¹ × B(0, R)`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian

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

/-- **LC83, circle fibres.** Under the hypotheses of `circleFiber_local_model` on a three-manifold,
every fibre of `η : η⁻¹ B(0, 100) → B(0, 100)` (with its regular-fibre manifold structure) is
diffeomorphic to `Circle`. -/
theorem circleFiber_local_model_circle (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    (hdim : Module.finrank ℝ E = 3)
    {p : M} {η : M → ℝ²} (hη : ContMDiffOn I 𝓘(ℝ, ℝ²) ∞ η (ball p 200))
    (hrank : ∀ x ∈ ball p 200, Surjective (mfderiv I 𝓘(ℝ, ℝ²) η x))
    (hlip : LipschitzOnWith 2 η (ball p 200)) (hp : η p = 0)
    (h102 : ∀ x ∈ ball p 200, ‖η x‖ < 100 → x ∈ ball p 102)
    (h2 : ∀ x ∈ ball p 200, η x = 0 → x ∈ ball p 2) (z : planeBallOpens 100) :
    let f := diskPreimageMap (ball p 200) isOpen_ball η hη.continuousOn 100
    letI := regularFiberChartedSpace f z (contMDiff_diskPreimageMap isOpen_ball hη 100)
      (fun x _ ↦ surjective_mfderiv_diskPreimageMap isOpen_ball hη hrank 100 x)
    Nonempty (Circle ≃ₘ⟮𝓡 1, 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ ℝ²) → ℝ)⟯
      {x // f x = z}) := by
  intro f
  obtain ⟨hf, hsub, -, -, hfib, -⟩ :=
    circleFiber_local_model g hEnorm hη hrank hlip hp h102 h2
  have hdim' : Module.finrank ℝ E = Module.finrank ℝ ℝ² + 1 := by
    rw [hdim, finrank_euclideanSpace_fin]
  exact OneManifold.nonempty_circle_diffeomorph_regularFiber f z hf (fun x _ => hsub x) hdim'
    (hfib z).1 (hfib z).2

end DifferentialGeometry.Geometry.Collapse
