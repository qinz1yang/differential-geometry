import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartFamilyQuantitativeApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortGlobalBlockMapBridge
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryAffineHeight

/-!
# Boundary port (lane B-PORT-A): the slim / circle cutoff formulas at physical scale

GENERATED from `DifferentialGeometry/Geometry/Collapse/LocalExport/LocalChartFamilyQuantitativeApplications.lean` by `build-logs/scratch/B-PORT-A/gen_shared.py` (engine `portlib2.py`); do
not edit by hand, re-run the script. Closed family → boundary family (`LocalPacketsOnB` /
`LocalPacketsOnBF`, complete σ-compact carrier, regional `…On` families, ACTIVE edge `edgeB`); every
ported declaration `x` ↦ `x_BAUGP` (namespaced `T.m` ↦ `TOn.m_BAUGP`). Substitution table and
failure points: `build-logs/resume/state-B-PORT-A.md`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

universe u

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

namespace LocalPacketsOnB

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax : ℝ}
  {τ γ δ εr e T V vs ζ Λz : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}

/-- **The slim cutoff formula at physical scale.** -/
theorem slim_cutoff_apply_BAUGP
    (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs U₁ U₂ Ue₁ Ue₂)
    {j : X} (hj : j ∈ L.slim.centres) (x : X) :
    (L.slim.centre j hj).cutoff_BCNT x =
      if dist x j < 10 ^ 6 * Δ * ρ j then
        slimCutoffProfile_LC87 ((L.slim.centre j hj).coord_BCG2 x / (10 ^ 5 * Δ)) else 0 := by
  classical
  have hmem : dist x j < 10 ^ 6 * Δ * ρ j ↔ (ρ j)⁻¹ * dist x j < 10 ^ 6 * Δ := by
    rw [inv_mul_lt_iff₀ (hρ j)]
    constructor <;> intro h <;> linarith
  have h := L.slim_cutoff_eq j hj
  have h2 : (L.slim.centre j hj).cutoff_BCNT x = Set.indicator {y | (ρ j)⁻¹ * dist y j < 10 ^ 6 * Δ}
      (fun y => slimCutoffProfile_LC87 ((L.slim.centre j hj).coord_BCG2 y / (10 ^ 5 * Δ))) x :=
    congrFun h x
  rw [h2, indicator_apply]
  by_cases hx : (ρ j)⁻¹ * dist x j < 10 ^ 6 * Δ
  · have hx' := hmem.mpr hx
    simp only [Set.mem_ofPred_eq, hx, hx', ↓reduceIte]
  · have hx' : ¬ dist x j < 10 ^ 6 * Δ * ρ j := fun h => hx (hmem.mp h)
    simp only [Set.mem_ofPred_eq, hx, hx', ↓reduceIte]

/-- **The circle cutoff formula at physical scale.** -/
theorem circle_cutoff_apply_BAUGP
    (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs U₁ U₂ Ue₁ Ue₂)
    {j : X} (hj : j ∈ L.circle.centres) (x : X) :
    let c := L.circle.chart j hj
    let ζ := L.circle.cutoff j
    letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    ζ x = if @dist X mX.toDist x j < 200 * ρ j then circleCutoffBump_LC87 (c.coord x) else 0 := by
  classical
  have hcen := L.circle.chart_center j hj
  have h := L.circle_cutoff_eq j hj
  intro c ζ
  let mR : MetricSpace X := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  have hcen' : c.center = j := hcen
  have h' : ζ = c.formulaCutoff := h
  have hmem : x ∈ ball c.center 200 ↔ @dist X mX.toDist x j < 200 * ρ j := by
    rw [hcen']
    change (ρ j)⁻¹ * @dist X mX.toDist x j < 200 ↔ _
    rw [inv_mul_lt_iff₀ (hρ j)]
    constructor <;> intro h <;> linarith
  rw [h']
  change (ball c.center 200).indicator (fun y => circleCutoffBump_LC87 (c.coord y)) x = _
  rw [indicator_apply]
  by_cases hx : @dist X mX.toDist x j < 200 * ρ j
  · have hx' := hmem.mpr hx
    simp only [hx, hx', ↓reduceIte]
  · have hx' : x ∉ ball c.center 200 := fun h => hx (hmem.mp h)
    simp only [hx, hx', ↓reduceIte]

end LocalPacketsOnB


end DifferentialGeometry.Geometry.Collapse
