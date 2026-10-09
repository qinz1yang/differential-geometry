import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsC14ZeroTypes
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.SelectedCoreOfSublevel74
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.SelectedCoreOfCompactModel74

/-!
# Draft 74, G32 (G27b): the LFR54 bridge on the final family `LocalChartPacketsC14Z`

Lane C14-REG-CHAIN (by S-REG-CHAIN3), G32. The zero sublevel clause `zero_sublevel_types` of the
final family (LPA05's LFR54 disjunction on the ACTUAL sublevel `{η_c ≤ a}`, `a ∈ [1/5, 2]`)
yields a `SelectedSmoothCore74` of that sublevel, whichever of the five branches holds:
`PointSoulCoreSublevel` / `CircleSoulCoreSublevel` / `ProjectiveSoulCoreSublevel` /
`KleinSoulCoreSublevel` (the disc-core branches) and `CompactModelSublevel` (the closed branch,
with the canonical `sec ≥ 0` metric of the compact type). This replaces the selected cores as
DATA of the zero row (`zeroDomains_exists_74`).
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] LocalChartPackets.instMetricN LocalChartPackets.instChartedN
  LocalChartPackets.instMetricC

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3}

/-- **The LFR54 bridge (G27b)**: every actual zero sublevel `{η_c ≤ a}`, `a ∈ [1/5, 2]`, of the
final family is a selected smooth core (of the branch given by `zero_sublevel_types`). -/
theorem LocalChartPacketsC14Z.nonempty_selectedCore74
    (P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM) {c : X} (hc : c ∈ P.zero.centres) {a : ℝ} (ha : a ∈ Icc (1 / 5 : ℝ) 2) :
    Nonempty (GC.GraphManifold.Assembly.SelectedSmoothCore74.{0, 0}
      {x | (P.zero.zero c hc).radial x ≤ a}) := by
  rcases P.zero_sublevel_types c hc a ha with h | h | h | h | h
  · exact GC.GraphManifold.Assembly.nonempty_selectedCore74_ofCompactModel h
  · exact GC.GraphManifold.Assembly.nonempty_selectedCore74_ofPointSoul h
  · exact GC.GraphManifold.Assembly.nonempty_selectedCore74_ofCircleSoul h
  · exact GC.GraphManifold.Assembly.nonempty_selectedCore74_ofProjectiveSoul h
  · exact GC.GraphManifold.Assembly.nonempty_selectedCore74_ofKleinSoul h

end DifferentialGeometry.Geometry.Collapse
