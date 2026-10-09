import DifferentialGeometry.Geometry.Collapse.FixtureC1.TorusEmptyFamilies
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsC14ZeroTypes

/-!
# The closed family `LocalChartPacketsC14Z` on the flat torus (S-FIXTURE-C1b, F1, G5 file 2)

`torPacketsC14Z_FXC1 : LocalChartPacketsC14Z (Tor Λ) (torMetric Λ) … oM`: the flat torus
`T³ = ℝ³/(N R ℤ ⊕ N R ℤ ⊕ L₂ ℤ)` (`L₂ ≤ R β₂`, `8R/β₂ ≤ N R`) at the constant scale `ρ ≡ R`
with

* the NON-EMPTY circle family (`torCircleFamily_FXC1`: the `R`-spaced net, LC83 charts, formula
  cutoffs) and, at every centre, the circle adapted centre with the geodesic test
  (`torCircleAdapted_FXC1`) and the residual enclosure (`torCircle_residual_FXC1`);
* the slim, edge and zero families EMPTY (every point has rank exactly two: no one-stratum, no
  zero-stratum, no strong edge point), `sec = 0`;
* `oM` a PARAMETER (the zero family is empty, so `zero_sublevel_types` holds for every `oM`).

The projections `torPacketsC14_FXC1`, `torPacketsC14D_FXC1` are given for the weaker rows.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] torMS_FXC1

attribute [local instance] nezero_finrank_euclideanThree_LC87

section Packets

variable (Λ : TorusPeriods_FXC1) {R : ℝ} (hR : 0 < R) {β : ℕ → ℝ} (hβ2 : 0 < β 2)
  (hβ2s : β 2 ≤ 1 / 10 ^ 7) (hL2 : Λ.L 2 ≤ R * β 2) (hLp : 8 * R / β 2 ≤ planePeriod_FXC1 Λ)
  (N : ℕ) (hL0 : Λ.L 0 = N * R) (hL1 : Λ.L 1 = N * R) (hβ3 : β 3 ≤ 3 / 20)
  {Lam Δ σs : ℝ} {K : ℕ} {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  (hγ : 0 < γ) (hb : b ≤ 1 / 6) (hs : s ≤ 1 / 7) (hbs : b + s ≤ 1 / 100)

include hR hβ2 hβ2s hL2 hLp hβ3 hL0 hL1 hγ hb hs hbs in
/-- **`LocalChartPacketsC14` on the flat torus** (non-empty circle family, empty slim / edge / zero
families). -/
def torPacketsC14_FXC1 :
    LocalChartPacketsC14 (Tor_FXC1 Λ) (torMetric_FXC1 Λ) (torMS_hmetric_FXC1 Λ) (fun _ => R)
      (fun _ => hR) Lam β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz where
  toLocalChartFamilyE := torFamilyE_FXC1 Λ hR hβ2 hβ2s hL2 hLp hβ3 N hL0 hL1 hb hs hbs
  circleAdapted := fun j hj =>
    torCircleAdapted_FXC1 Λ hR hβ2 hβ2s hL2 hLp N hL0 hL1 hβ3 hγ j hj
  N := fun _ => Tor_FXC1 Λ
  C := fun _ => PUnit.{1}
  instMetricN := fun _ => torMS_FXC1 Λ
  instChartedN := fun _ => inferInstance
  instMetricC := fun _ => inferInstance
  o := fun _ => PUnit.unit
  zero := torZeroFamily_FXC1 Λ hR hβ2 hβ2s hL2 hLp hβ3
  edgeDisk := fun j hj => absurd hj (notMem_empty j)
  circle_residual := fun j _ => torCircle_residual_FXC1 Λ hR hβ2 hβ2s hL2 hLp j
  zero_local_comparison := fun c hc => absurd hc (notMem_empty c)
  slim_value := fun j hj => absurd hj (notMem_empty j)
  zero_shell_split := fun c hc => absurd hc (notMem_empty c)
  zero_adapted := fun c hc => absurd hc (notMem_empty c)
  zero_curvature := fun c hc => absurd hc (notMem_empty c)
  edge_section := fun j hj => absurd hj (notMem_empty j)

include hR hβ2 hβ2s hL2 hLp hβ3 hL0 hL1 hγ hb hs hbs in
/-- `LocalChartPacketsC14D` on the flat torus (`weak_edge_density` is vacuous: no one-stratum). -/
def torPacketsC14D_FXC1 :
    LocalChartPacketsC14D (Tor_FXC1 Λ) (torMetric_FXC1 Λ) (torMS_hmetric_FXC1 Λ) (fun _ => R)
      (fun _ => hR) Lam β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz where
  toLocalChartPacketsC14 :=
    torPacketsC14_FXC1 Λ hR hβ2 hβ2s hL2 hLp N hL0 hL1 hβ3 hγ hb hs hbs
  weak_edge_density := fun p hp => absurd hp
    (torNotMemStratum_FXC1 Λ hR hβ2 hβ2s hL2 hLp hβ3 (by decide) p)

variable (oM : ManifoldOrientation 𝓘(ℝ, E3) (Tor_FXC1 Λ) 3)

include hR hβ2 hβ2s hL2 hLp hβ3 hL0 hL1 hγ hb hs hbs in
/-- **The complete closed family `LocalChartPacketsC14Z` on the flat torus** (`oM` a parameter:
the zero family is empty). The circle family is NON-EMPTY: the stage clauses of the closed rows
have actual content on it. -/
def torPacketsC14Z_FXC1 :
    LocalChartPacketsC14Z (Tor_FXC1 Λ) (torMetric_FXC1 Λ) (torMS_hmetric_FXC1 Λ) (fun _ => R)
      (fun _ => hR) Lam β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz oM where
  toLocalChartPacketsC14D :=
    torPacketsC14D_FXC1 Λ hR hβ2 hβ2s hL2 hLp N hL0 hL1 hβ3 hγ hb hs hbs
  zero_sublevel_types := fun c hc => absurd hc (notMem_empty c)

end Packets

end DifferentialGeometry.Geometry.Collapse
