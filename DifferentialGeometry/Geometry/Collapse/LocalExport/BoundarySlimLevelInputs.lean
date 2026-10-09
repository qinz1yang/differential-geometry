import DifferentialGeometry.Geometry.Collapse.LocalExport.SlimFibreStandardType
import DifferentialGeometry.Geometry.Collapse.FiniteSurface.SlimModelOrientation
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryRegionalSlimValue
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryAugmentedInteriorKernels
import DifferentialGeometry.Geometry.Collapse.LocalExport.OriginalSlabCompactness
import DifferentialGeometry.Geometry.Fibration.ActualOriginalSlabs

/-!
# O-WF G3a: the original slim level of a REGIONAL slim centre — compact slab, standard type

Generic over a regional slim centre `c : SlimCentreOn X …` (complete σ-compact carrier, the
boundary route's family; closed twins on `SlimCentre`):

* `SlimCentreOn.isCompact_slab_OWF`: the closed slab `{x ∈ B(j, 10⁶Δρ_j) | |η_j x| ≤ a}` is
  compact for `a < 905·10³Δ` (LFR20's proper restriction, `SlimChart.isCompact_closedSlab_FPRE`);
* **`SlimCentreOn.standard_level_embedding_OWF`** (review 70 D70-2/D70-4 on the regional
  centre): for `K ≥ 5`, `Δ ≥ 1` and an orientation of `X`, EITHER every whole level
  `{x ∈ B(j, 10⁶Δρ_j) | η_j x = a}`, `|a| < 905·10³Δ`, is the image of a smooth embedding of the
  standard `ClosureSphere`, OR every one is the image of a smooth embedding of the standard `Torus`
  (`SlimChart.exists_standard_level_embedding_SSTD` on the stored packet and model, the surface
  factor from route β; closed twin `SlimCentre.fibre_standard_type_SSTD`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open GC.GraphManifold GC.Endpoint

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {β₁ Δ σs : ℝ} {K : ℕ} {j : X}

namespace SlimCentreOn

/-- **The closed slim slab is compact**: `{x ∈ B(j, 10⁶Δρ_j) | |η_j x| ≤ a}`, `a < 905·10³Δ`. -/
theorem isCompact_slab_OWF (c : SlimCentreOn X g hmetric ρ hρ β₁ Δ σs K j) {a : ℝ}
    (ha : a < 905 * 10 ^ 3 * Δ) :
    IsCompact {x | x ∈ ball j (10 ^ 6 * Δ * ρ j) ∧ |c.coord_BCG2 x| ≤ a} := by
  have hr := hρ j
  let P := c.packet
  let iZ := c.instZ
  let hMc : CompleteSpace X := ‹CompleteSpace X›
  let mR : MetricSpace X := mX.rescale (ρ j)⁻¹ (inv_pos.mpr hr)
  let bR := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr hr)
  let cR : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr hr)
  let iR : IsRiemannianManifold 𝓘(ℝ, E3) X :=
    radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr hr)
  let kR : CompleteSpace X := (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr hr)).mpr hMc
  have h1 := P.toSlimChart.isCompact_closedSlab_FPRE ha
  convert h1 using 1
  ext x
  exact and_congr_left' (mem_ball_rescale_iff_FPRE (m := mX) hr (k := 10 ^ 6 * Δ)).symm

/-- **The standard smooth type of the whole original slim levels** (see the module docstring). -/
theorem standard_level_embedding_OWF (c : SlimCentreOn X g hmetric ρ hρ β₁ Δ σs K j)
    (hK : 5 ≤ K) (hΔ : 1 ≤ Δ) (oM : DifferentialGeometry.ManifoldOrientation (𝓡 3) X 3) :
    (∀ a : ℝ, |a| < 905 * 10 ^ 3 * Δ → ∃ e : ClosureSphere.{0} → X,
      IsSmoothEmbedding (𝓡 2) 𝓘(ℝ, E3) ∞ e ∧
        range e = {x | x ∈ ball j (10 ^ 6 * Δ * ρ j) ∧ c.coord_BCG2 x = a}) ∨
    (∀ a : ℝ, |a| < 905 * 10 ^ 3 * Δ → ∃ e : Torus → X,
      IsSmoothEmbedding torusModel 𝓘(ℝ, E3) ∞ e ∧
        range e = {x | x ∈ ball j (10 ^ 6 * Δ * ρ j) ∧ c.coord_BCG2 x = a}) := by
  have hr := hρ j
  have hset : ∀ a : ℝ, {x | x ∈ @ball X (mX.rescale (ρ j)⁻¹ (inv_pos.mpr hr)).toPseudoMetricSpace
      j (10 ^ 6 * Δ) ∧ c.coord_BCG2 x = a} =
        {x | x ∈ ball j (10 ^ 6 * Δ * ρ j) ∧ c.coord_BCG2 x = a} := by
    intro a
    ext x
    exact and_congr_left' (mem_ball_rescale_iff_FPRE (m := mX) hr (k := 10 ^ 6 * Δ))
  let P := c.packet
  let PM := c.model
  let iZ := c.instZ
  let hMc : CompleteSpace X := ‹CompleteSpace X›
  let mR : MetricSpace X := mX.rescale (ρ j)⁻¹ (inv_pos.mpr hr)
  let bR := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr hr)
  let cR : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr hr)
  let iR : IsRiemannianManifold 𝓘(ℝ, E3) X :=
    radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr hr)
  let kR : CompleteSpace X := (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr hr)).mpr hMc
  obtain ⟨Q⟩ := SlimProductModel.nonempty_slimSurfaceFactor_of_oriented_source_SSTD hK hΔ PM oM
  rcases P.toSlimChart.exists_standard_level_embedding_SSTD.{0} hK hΔ PM Q with h | h
  · refine Or.inl fun a ha => ?_
    obtain ⟨e, he, hre⟩ := h a ha
    exact ⟨e, he, hre.trans (hset a)⟩
  · refine Or.inr fun a ha => ?_
    obtain ⟨e, he, hre⟩ := h a ha
    exact ⟨e, he, hre.trans (hset a)⟩

end SlimCentreOn

end DifferentialGeometry.Geometry.Collapse
