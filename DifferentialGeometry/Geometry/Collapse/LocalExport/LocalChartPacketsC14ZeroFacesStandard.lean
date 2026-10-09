import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsC14ZeroFaces
import DifferentialGeometry.Geometry.Collapse.FiniteZeroCore.LPA05SublevelFaceStandardParam

/-!
# The original zero faces of the complete closed family: standard smooth parametrizations

Lane C14-ZSP35b, review 70 D70-5 (d). Strong form of `LocalChartPacketsC14Z.zero_face_type_ZSP35`
(homeomorphism types, kept): for every zero centre `c` and `a ∈ [1/5, 2]`, the original face
`{η_c = a}` is empty with `{η_c ≤ a} = univ` (compact model), or the exact image of a smooth
embedding of the standard `S² = ClosureSphere` (model `𝓡 2`), or of the standard
`T² = Circle × Circle` (model `torusModel`) — restricted from the family's own selected LFR54 core
model (`zero_sublevel_frontier_standard_param_ZSP35` on `zero_sublevel_types`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology NNReal
open DifferentialGeometry.Geometry.Riemannian
open GC.MetricGeometry GC.Endpoint

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "I3" => 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] LocalChartPackets.instMetricN LocalChartPackets.instChartedN
  LocalChartPackets.instMetricC

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3}

/-- **The standard smooth parametrization of an original zero face** (D70-5 (d)): for every zero
centre `c` and `a ∈ [1/5, 2]`, `{η_c = a}` is empty with `{η_c ≤ a} = univ`, or the exact image of a
smooth embedding `ClosureSphere.{0} → X` (model `𝓡 2`), or of a smooth embedding `Torus → X`
(model `torusModel`). -/
theorem LocalChartPacketsC14Z.zero_face_standard_param_ZSP35
    (P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM) {c : X} (hc : c ∈ P.zero.centres) {a : ℝ} (ha : a ∈ Icc (1 / 5 : ℝ) 2) :
    ({x | (P.zero.zero c hc).radial x ≤ a} = univ ∧ {x | (P.zero.zero c hc).radial x = a} = ∅) ∨
    (∃ e : GC.GraphManifold.ClosureSphere.{0} → X, IsSmoothEmbedding (𝓡 2) I3 ∞ e ∧
      range e = {x | (P.zero.zero c hc).radial x = a}) ∨
    (∃ e : Torus → X, IsSmoothEmbedding torusModel I3 ∞ e ∧
      range e = {x | (P.zero.zero c hc).radial x = a}) := by
  have hfr := (P.zero_sublevel_regular_FAMZ hc ha).1
  rcases zero_sublevel_frontier_standard_param_ZSP35 (P.isClosed_zero_sublevel_FAMZ hc a)
      (P.zero_sublevel_types c hc a ha) with ⟨hu, he⟩ | ⟨e, he, hr⟩ | ⟨e, he, hr⟩
  · exact Or.inl ⟨hu, hfr ▸ he⟩
  · exact Or.inr (Or.inl ⟨e, he, hr.trans hfr⟩)
  · exact Or.inr (Or.inr ⟨e, he, hr.trans hfr⟩)

end DifferentialGeometry.Geometry.Collapse
