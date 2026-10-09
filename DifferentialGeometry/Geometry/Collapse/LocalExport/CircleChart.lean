import DifferentialGeometry.Geometry.Collapse.CircleFiberCircle

/-!
# LC83 circle charts as data (shared object for LC87)

Blueprint rows LC83 (`prop:collapse-two-stratum-local`) and LC87 item 2 (`def:collapse-local-export-
certificate`), master207A.  A `CircleChart I M` records one LC83 circle chart at normalized scale
(the metric of `M` is the rescaled `ρ(p)⁻² g`, as in LC83 itself): the centre `p`, the map
`η : B(p, 200) → ℝ²` with the producer obligations of LC83 (smooth, rank two, `2`-Lipschitz,
`η(p) = 0`, `η⁻¹ B(0, 100) ⊆ B(p, 102)`, `η⁻¹(0) ⊆ B(p, 2)`), and the output clauses of the proved
LC83 statement `circleFiber_local_model` for the restriction
`f = diskPreimageMap (B(p, 200)) η 100 : η⁻¹ B(0, 100) → B(0, 100)`: proper, surjective, compact
connected fibres, trivial over every `B(0, R)`, `0 < R < 100`, with fibre the zero fibre.

* `CircleChart.ofLocalModel`: the producer, from W4-F7a's `circleFiber_local_model` on a complete
  Riemannian manifold.
* `CircleChart.contMDiff_restrict`, `CircleChart.surjective_mfderiv_restrict`: smoothness and the
  submersion property of the restriction (from the recorded data).
* `CircleChart.nonempty_circle_diffeomorph`: in dimension three every fibre is diffeomorphic to the
  circle (the fibre type; from the recorded fields and the classification of compact connected
  1-manifolds, as in `circleFiber_local_model_circle`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

section Data

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
  (M : Type*) [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- An LC83 circle chart at normalized scale: the producer obligations of LC83 and the output
clauses of `circleFiber_local_model` for the restriction of `coord` to `coord⁻¹ B(0, 100)`. -/
structure CircleChart where
  /-- The centre `p`. -/
  center : M
  /-- The map `η`. -/
  coord : M → ℝ²
  contMDiffOn_coord : ContMDiffOn I 𝓘(ℝ, ℝ²) ∞ coord (ball center 200)
  rank : ∀ x ∈ ball center 200, Surjective (mfderiv I 𝓘(ℝ, ℝ²) coord x)
  lipschitz : LipschitzOnWith 2 coord (ball center 200)
  coord_center : coord center = 0
  enclosure : ∀ x ∈ ball center 200, ‖coord x‖ < 100 → x ∈ ball center 102
  zero_enclosure : ∀ x ∈ ball center 200, coord x = 0 → x ∈ ball center 2
  isProperMap : IsProperMap
    (diskPreimageMap (ball center 200) isOpen_ball coord contMDiffOn_coord.continuousOn 100)
  surjective : Surjective
    (diskPreimageMap (ball center 200) isOpen_ball coord contMDiffOn_coord.continuousOn 100)
  fibres : ∀ z,
    IsCompact (diskPreimageMap (ball center 200) isOpen_ball coord
      contMDiffOn_coord.continuousOn 100 ⁻¹' {z}) ∧
    IsConnected (diskPreimageMap (ball center 200) isOpen_ball coord
      contMDiffOn_coord.continuousOn 100 ⁻¹' {z})
  trivial : ∀ R (hR : 0 < R) (hRr : R < 100),
    let f := diskPreimageMap (ball center 200) isOpen_ball coord contMDiffOn_coord.continuousOn 100
    let y₀ : planeBallOpens 100 := ⟨0, zero_mem_planeBallOpens (hR.trans hRr)⟩
    let _ := regularFiberChartedSpace f y₀ (contMDiff_diskPreimageMap isOpen_ball contMDiffOn_coord 100)
      (fun x _ ↦ surjective_mfderiv_diskPreimageMap isOpen_ball contMDiffOn_coord rank 100 x)
    let U : TopologicalSpace.Opens
        (diskPreimageOpens (ball center 200) isOpen_ball coord contMDiffOn_coord.continuousOn 100) :=
      ⟨f ⁻¹' planeBallInner 100 R,
        (planeBallInner 100 R).isOpen.preimage (continuous_diskPreimageMap isOpen_ball _ 100)⟩
    ∃ (hy : y₀ ∈ planeBallInner 100 R) (Θ : Diffeomorph
        (𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ ℝ²) → ℝ).prod 𝓘(ℝ, ℝ²)) I
        ({x // f x = y₀} × planeBallInner 100 R) U ∞),
      (∀ q, f (Θ q).1 = q.2.1) ∧ (∀ x, (Θ (x, ⟨y₀, hy⟩)).1 = x.1)

variable {I M}

namespace CircleChart

/-- The restriction of a circle chart's map to its bundle domain is smooth. -/
theorem contMDiff_restrict (c : CircleChart I M) :
    ContMDiff I 𝓘(ℝ, ℝ²) ∞ (diskPreimageMap (ball c.center 200) isOpen_ball c.coord
      c.contMDiffOn_coord.continuousOn 100) :=
  contMDiff_diskPreimageMap isOpen_ball c.contMDiffOn_coord 100

/-- The restriction of a circle chart's map to its bundle domain is a submersion. -/
theorem surjective_mfderiv_restrict (c : CircleChart I M)
    (x : diskPreimageOpens (ball c.center 200) isOpen_ball c.coord
      c.contMDiffOn_coord.continuousOn 100) :
    Surjective (mfderiv I 𝓘(ℝ, ℝ²) (diskPreimageMap (ball c.center 200) isOpen_ball c.coord
      c.contMDiffOn_coord.continuousOn 100) x) :=
  surjective_mfderiv_diskPreimageMap isOpen_ball c.contMDiffOn_coord c.rank 100 x

/-- Fibre type: in dimension three every fibre of a circle chart is diffeomorphic to the circle. -/
theorem nonempty_circle_diffeomorph (c : CircleChart I M) (hdim : Module.finrank ℝ E = 3)
    (z : planeBallOpens 100) :
    let f := diskPreimageMap (ball c.center 200) isOpen_ball c.coord
      c.contMDiffOn_coord.continuousOn 100
    letI := regularFiberChartedSpace f z (contMDiff_diskPreimageMap isOpen_ball c.contMDiffOn_coord 100)
      (fun x _ ↦ surjective_mfderiv_diskPreimageMap isOpen_ball c.contMDiffOn_coord c.rank 100 x)
    Nonempty (Circle ≃ₘ⟮𝓡 1, 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ ℝ²) → ℝ)⟯
      {x // f x = z}) := by
  intro f
  have hdim' : Module.finrank ℝ E = Module.finrank ℝ ℝ² + 1 := by
    rw [hdim, finrank_euclideanSpace_fin]
  exact OneManifold.nonempty_circle_diffeomorph_regularFiber f z c.contMDiff_restrict
    (fun x _ => c.surjective_mfderiv_restrict x) hdim' (c.fibres z).1 (c.fibres z).2

end CircleChart

end Data

section Producer

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

/-- Producer of a circle chart from the hypotheses of LC83 (`circleFiber_local_model`) on a
complete Riemannian manifold. -/
def CircleChart.ofLocalModel (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    {p : M} {η : M → ℝ²} (hη : ContMDiffOn I 𝓘(ℝ, ℝ²) ∞ η (ball p 200))
    (hrank : ∀ x ∈ ball p 200, Surjective (mfderiv I 𝓘(ℝ, ℝ²) η x))
    (hlip : LipschitzOnWith 2 η (ball p 200)) (hp : η p = 0)
    (h102 : ∀ x ∈ ball p 200, ‖η x‖ < 100 → x ∈ ball p 102)
    (h2 : ∀ x ∈ ball p 200, η x = 0 → x ∈ ball p 2) : CircleChart I M where
  center := p
  coord := η
  contMDiffOn_coord := hη
  rank := hrank
  lipschitz := hlip
  coord_center := hp
  enclosure := h102
  zero_enclosure := h2
  isProperMap := (circleFiber_local_model g hEnorm hη hrank hlip hp h102 h2).2.2.1
  surjective := (circleFiber_local_model g hEnorm hη hrank hlip hp h102 h2).2.2.2.1
  fibres := (circleFiber_local_model g hEnorm hη hrank hlip hp h102 h2).2.2.2.2.1
  trivial := (circleFiber_local_model g hEnorm hη hrank hlip hp h102 h2).2.2.2.2.2

theorem CircleChart.ofLocalModel_center (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm g) {p : M} {η : M → ℝ²} (hη : ContMDiffOn I 𝓘(ℝ, ℝ²) ∞ η (ball p 200))
    (hrank : ∀ x ∈ ball p 200, Surjective (mfderiv I 𝓘(ℝ, ℝ²) η x))
    (hlip : LipschitzOnWith 2 η (ball p 200)) (hp : η p = 0)
    (h102 : ∀ x ∈ ball p 200, ‖η x‖ < 100 → x ∈ ball p 102)
    (h2 : ∀ x ∈ ball p 200, η x = 0 → x ∈ ball p 2) :
    (CircleChart.ofLocalModel g hEnorm hη hrank hlip hp h102 h2).center = p :=
  rfl

end Producer

end DifferentialGeometry.Geometry.Collapse
