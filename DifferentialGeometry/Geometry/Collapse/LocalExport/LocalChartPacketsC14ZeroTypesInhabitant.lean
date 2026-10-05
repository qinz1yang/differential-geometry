import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsInhabitants
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsC14ZeroTypes

/-!
# Structural inhabitant of the complete closed family over the empty manifold (lane C14-FAM-Z)

Lead decision T48-4 (external review 48, item 5), applied to the last closed extension
`LocalChartPacketsC14Z` (`zero_sublevel_types`) and to `LocalChartPacketsC14D`
(`weak_edge_density`): over `X := PEmpty` every field is vacuous, for EVERY value of the real
parameters and every orientation of the source. This tests the field texts (no field forces a point,
no field is contradictory as stated); the geometric existence evidence is the producer
`eventually_nonempty_localChartPacketsC14Z_FAMZ`.

* `manifoldOrientationPEmpty_FAMZ`: the (vacuous) orientation of the empty three-manifold, so the
  orientation parameter of the certificate is inhabited.
* `nonempty_localChartPacketsC14Z_pempty_FAMZ`: an inhabitant of `LocalChartPacketsC14Z` for all
  parameters and every orientation (built on `nonempty_localChartPacketsC14_pempty_FAM`).
* `nonempty_localChartPacketsC14D_pempty_FAMZ`: the projection to `LocalChartPacketsC14D`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology NNReal
open DifferentialGeometry.Geometry.Riemannian
open GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- The metric on `PEmpty` (induced from `ℝ`), with the canonical topology of `PEmpty` (the same
term as the instance used by `metricPEmpty_FAM`). -/
local instance metricSpacePEmpty_FAMZ : MetricSpace PEmpty.{1} :=
  (MetricSpace.induced (PEmpty.elim : PEmpty.{1} → ℝ) (fun x => x.elim)
    inferInstance).replaceTopology (by ext s; simp only [Set.eq_empty_of_isEmpty s, isOpen_empty])

/-- The empty three-manifold (the same term as the instance used by `metricPEmpty_FAM`). -/
local instance chartedSpacePEmpty_FAMZ : ChartedSpace E3 PEmpty.{1} :=
  ChartedSpace.empty E3 PEmpty.{1}

/-- The (vacuous) orientation of the empty three-manifold. -/
def manifoldOrientationPEmpty_FAMZ : ManifoldOrientation 𝓘(ℝ, E3) PEmpty.{1} 3 where
  dimension_eq := finrank_euclideanSpace_fin
  orientation x := x.elim
  locally_constant p := p.elim

/-- **Structural inhabitant of the complete closed family** (T48-4): over the empty three-manifold,
for all values of the real parameters and every orientation `oM`, `LocalChartPacketsC14Z` is
inhabited (empty circle, slim, edge and zero families; `weak_edge_density` and
`zero_sublevel_types` are vacuous). -/
theorem nonempty_localChartPacketsC14Z_pempty_FAMZ
    (Λ : ℝ) (β : ℕ → ℝ) (Δ σs : ℝ) (K : ℕ)
    (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ)
    (oM : ManifoldOrientation 𝓘(ℝ, E3) PEmpty.{1} 3) :
    Nonempty (LocalChartPacketsC14Z PEmpty.{1} metricPEmpty_FAM (fun a => a.elim)
      (fun a => a.elim) (fun a => a.elim) Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
      vs ζ Λz oM) := by
  obtain ⟨P⟩ := nonempty_localChartPacketsC14_pempty_FAM Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax
    τ γ δ εr e T V vs ζ Λz
  exact ⟨{ toLocalChartPacketsC14 := P
           weak_edge_density := fun p => p.elim
           zero_sublevel_types := fun c => c.elim }⟩

/-- `LocalChartPacketsC14D` over the empty manifold (projection of the complete family at the
vacuous orientation). -/
theorem nonempty_localChartPacketsC14D_pempty_FAMZ
    (Λ : ℝ) (β : ℕ → ℝ) (Δ σs : ℝ) (K : ℕ)
    (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ) :
    Nonempty (LocalChartPacketsC14D PEmpty.{1} metricPEmpty_FAM (fun a => a.elim)
      (fun a => a.elim) (fun a => a.elim) Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
      vs ζ Λz) :=
  (nonempty_localChartPacketsC14Z_pempty_FAMZ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
    T V vs ζ Λz manifoldOrientationPEmpty_FAMZ).map LocalChartPacketsC14Z.toLocalChartPacketsC14D

end DifferentialGeometry.Geometry.Collapse
