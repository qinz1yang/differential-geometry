import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartFamilyQuantitativeProducer
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartFamilyApplications

/-!
# Consumers of `LocalChartFamilyQ`: the cutoff formulas at physical scale

* `LocalChartFamilyQ.slim_cutoff_apply`: the slim cutoff at a centre `j` is
  `φ(η_j/(10⁵Δ))` on the PHYSICAL ball `B(j, 10⁶Δρ(j))` and zero outside it
  (`φ = slimCutoffProfile_LC87`, `η_j = SlimCentre.coord`).
* `LocalChartFamilyQ.circle_cutoff_apply`: the circle cutoff at `j` is `ψ_{8,9}(η_j)` on the physical
  ball `B(j, 200ρ(j))` and zero outside it (`ψ_{8,9} = circleCutoffBump_LC87`).
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

namespace LocalChartFamilyQ

variable {X : Type u} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax : ℝ}

/-- **The slim cutoff formula at physical scale.** -/
theorem slim_cutoff_apply
    (L : LocalChartFamilyQ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax)
    {j : X} (hj : j ∈ L.slim.centres) (x : X) :
    (L.slim.centre j hj).cutoff x =
      if dist x j < 10 ^ 6 * Δ * ρ j then
        slimCutoffProfile_LC87 ((L.slim.centre j hj).coord x / (10 ^ 5 * Δ)) else 0 := by
  classical
  have hmem : dist x j < 10 ^ 6 * Δ * ρ j ↔ (ρ j)⁻¹ * dist x j < 10 ^ 6 * Δ := by
    rw [inv_mul_lt_iff₀ (hρ j)]
    constructor <;> intro h <;> linarith
  have h := L.slim_cutoff_eq j hj
  have h2 : (L.slim.centre j hj).cutoff x = Set.indicator {y | (ρ j)⁻¹ * dist y j < 10 ^ 6 * Δ}
      (fun y => slimCutoffProfile_LC87 ((L.slim.centre j hj).coord y / (10 ^ 5 * Δ))) x :=
    congrFun h x
  rw [h2, indicator_apply]
  by_cases hx : (ρ j)⁻¹ * dist x j < 10 ^ 6 * Δ
  · have hx' := hmem.mpr hx
    simp only [Set.mem_ofPred_eq, hx, hx', ↓reduceIte]
  · have hx' : ¬ dist x j < 10 ^ 6 * Δ * ρ j := fun h => hx (hmem.mp h)
    simp only [Set.mem_ofPred_eq, hx, hx', ↓reduceIte]

/-- **The circle cutoff formula at physical scale.** -/
theorem circle_cutoff_apply
    (L : LocalChartFamilyQ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax)
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

end LocalChartFamilyQ

end DifferentialGeometry.Geometry.Collapse
