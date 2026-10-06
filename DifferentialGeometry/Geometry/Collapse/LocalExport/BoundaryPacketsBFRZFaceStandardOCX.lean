import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPacketsBFRZ
import DifferentialGeometry.Geometry.Collapse.FiniteZeroCore.LPA05SublevelFaceStandardParam

/-!
# The zero faces of the complete final boundary family: regular level and standard smooth
parametrization (lane O-CROSS, G4)

The boundary analogue of `LocalChartPacketsC14Z.zero_sublevel_regular_FAMZ` /
`zero_face_standard_param_ZSP35` (closed family) for `LocalPacketsOnBFRZ` on any complete source
`X` (in the rows: the interior `W°` with its completed metric):

* `LocalPacketsOnBFRZ.frontier_zero_sublevel_OCX`: `frontier {η_c ≤ a} = {η_c = a}` for
  `a ∈ [1/5, 2]` (regular level, from the zero ball's `radial_spec`);
* `LocalPacketsOnBFRZ.zero_face_standard_param_OCX`: the source is compact (compact model), or
  `{η_c = a}` is the exact image of a smooth embedding `ClosureSphere.{0} → X` (model `𝓡 2`) or
  `Torus → X` (model `torusModel`) — `zero_sublevel_frontier_standard_param_ZSP35` on the family's
  own `zero_sublevel_types`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology NNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Operator
open GC.MetricGeometry GC.Endpoint

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "I3" => 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] LocalPacketsOn.instMetricN LocalPacketsOn.instChartedN
  LocalPacketsOn.instMetricC

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3}

/-- **The zero sublevels of the boundary family have a regular boundary**: for every zero centre
and `a ∈ [1/5, 2]`, `frontier {η_c ≤ a} = {η_c = a}`. -/
theorem LocalPacketsOnBFRZ.frontier_zero_sublevel_OCX
    (P : LocalPacketsOnBFRZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz U₁ U₂ Ue₁ Ue₂ oM) {c : X} (hc : c ∈ P.zero.centres) {a : ℝ}
    (ha : a ∈ Icc (1 / 5 : ℝ) 2) :
    frontier {x | (P.zero.zero c hc).radial x ≤ a} = {x | (P.zero.zero c hc).radial x = a} := by
  have hR := (P.zero.zero c hc).radius_pos
  obtain ⟨hlip, -, -, -, -, -, -, -, -, -, ⟨O', hO'o, hO'sub, hO'sm, hne⟩, -⟩ :=
    (P.zero.zero c hc).radial_spec
  have hηc : Continuous (P.zero.zero c hc).radial :=
    @LipschitzWith.continuous X ℝ (mX.rescale ((P.zero.zero c hc).radius)⁻¹
      (inv_pos.mpr hR)).toPseudoEMetricSpace _ _ _ hlip
  have hlevel : ∀ q, (P.zero.zero c hc).radial q = a → q ∈ O' := fun q hq =>
    hO'sub (show (P.zero.zero c hc).radial q ∈ Icc (1 / 5 : ℝ) 2 by rw [hq]; exact ha)
  exact frontier_sublevel_eq_level_of_regular (I := 𝓘(ℝ, E3)) hηc fun q hq =>
    ⟨((hO'sm.contMDiffAt (hO'o.mem_nhds (hlevel q hq))).of_le (by norm_num)),
      mfderiv_ne_zero_of_gradFun_ne_zero _ (hne q (hlevel q hq))⟩

/-- **The standard smooth parametrization of a zero face of the boundary family**: for every
zero centre and `a ∈ [1/5, 2]`, the source is compact (compact model), or `{η_c = a}` is the exact
image of a smooth embedding of `S² = ClosureSphere` (model `𝓡 2`) or of `T² = Torus` (model
`torusModel`). -/
theorem LocalPacketsOnBFRZ.zero_face_standard_param_OCX
    (P : LocalPacketsOnBFRZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz U₁ U₂ Ue₁ Ue₂ oM) {c : X} (hc : c ∈ P.zero.centres) {a : ℝ}
    (ha : a ∈ Icc (1 / 5 : ℝ) 2) :
    CompactSpace X ∨
    (∃ e : GC.GraphManifold.ClosureSphere.{0} → X, IsSmoothEmbedding (𝓡 2) I3 ∞ e ∧
      range e = {x | (P.zero.zero c hc).radial x = a}) ∨
    (∃ e : Torus → X, IsSmoothEmbedding torusModel I3 ∞ e ∧
      range e = {x | (P.zero.zero c hc).radial x = a}) := by
  have hfr := P.frontier_zero_sublevel_OCX hc ha
  have hA := P.isClosed_zero_sublevel_BFZD hc a
  rcases P.zero_sublevel_types c hc a ha with h | h | h | h | h
  · obtain ⟨-, hN, ⟨D⟩, -⟩ := h
    refine Or.inl ⟨?_⟩
    have h1 : IsCompact (range D.symm) := isCompact_range D.symm.continuous
    have h2 : range D.symm = univ := D.symm.toEquiv.surjective.range_eq
    rw [h2] at h1
    exact h1
  · obtain ⟨e, he, hr⟩ := h.frontier_standard_param_ZSP35 hA
    obtain ⟨he', hr'⟩ := closureSphere_param_of_sphere_ZSP35 he
    exact Or.inr (Or.inl ⟨_, he', (hr'.trans hr).trans hfr⟩)
  · obtain ⟨e, he, hr⟩ := h.frontier_standard_param_ZSP35 hA
    exact Or.inr (Or.inr ⟨e, he, hr.trans hfr⟩)
  · obtain ⟨e, he, hr⟩ := h.frontier_standard_param_ZSP35 hA
    obtain ⟨he', hr'⟩ := closureSphere_param_of_sphere_ZSP35 he
    exact Or.inr (Or.inl ⟨_, he', (hr'.trans hr).trans hfr⟩)
  · obtain ⟨e, he, hr⟩ := h.frontier_standard_param_ZSP35 hA
    exact Or.inr (Or.inr ⟨e, he, hr.trans hfr⟩)

end DifferentialGeometry.Geometry.Collapse
