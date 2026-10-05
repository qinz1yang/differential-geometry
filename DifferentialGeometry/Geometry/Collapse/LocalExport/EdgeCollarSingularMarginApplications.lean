import DifferentialGeometry.Geometry.Collapse.LocalExport.EdgeCollarSingularMargin
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsC14

/-!
# The collar singular margin on the edge charts of the LC87 family

Lane C14-FAM, register R8 (design `build-logs/resume/design-C14-FAM.md` (e)).
`EdgeFamily.collar_singular_margin_FAM`: for the edge chart `c` of an LC87 edge family at a
centre `j` (normalized at `j`: metric `ρ(j)⁻² g`, scale `ρ/ρ(j)`, smoothing `F/ρ(j)`), at every
collar point `x` and every `y ∈ B(x, 100ρ(x)/ρ(j))`, the pair
`J = (η_j, (F/ρ(j))/(ρ/ρ(j))) = (η_j, F/ρ)` has least singular value `> 9/10` after the factor
`ρ(x)/ρ(j)` (TCP04, EDP03), as soon as the family's collar quality `γc ≤ 1/100` and plane-map
quality `βc ≤ 10⁻⁵` (both hold in the producers: `γc < 1/100`, `βc < γc/1000`). Applies to the
edge family of `LocalChartPacketsC14` (`P.edge`).
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

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {β : ℕ → ℝ} {Δ σc μ b s b' s' ε γc βc : ℝ}

/-- **The collar singular margin of an LC87 edge chart** (R8; TCP04, EDP03), normalized at the
centre `j`: at a collar point `x` and every `y ∈ B(x, 100ρ(x)/ρ(j))`, every unit `ξ ∈ ℝ²` has a
`ρ(j)⁻²g`-unit `W` with `⟨(ρ(x)/ρ(j)) DJ(y) W, ξ⟩ > 9/10`. -/
theorem EdgeFamily.collar_singular_margin_FAM
    (Fe : EdgeFamily X g hmetric ρ hρ β Δ σc μ b s b' s' ε γc βc) (hγc : 0 < γc)
    (hγc1 : γc ≤ 1 / 100) (hβc1 : βc ≤ 1 / 100000) {j : X} (hj : j ∈ Fe.centres) :
    let c := Fe.chart j hj
    let Fs := Fe.smoothing
    let hMc : CompleteSpace X := complete_of_compact
    letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    letI := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    letI : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
      radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    letI : IsRiemannianManifold 𝓘(ℝ, E3) X :=
      radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    letI : CompleteSpace X :=
      (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
    let gR : SmoothRiemannianMetric 𝓘(ℝ, E3) X :=
      scaleMetric ((ρ j)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (hρ j)) 2) g
    ∀ x ∈ ball j (100 * Δ), |c.coord x| ≤ 10 * Δ →
      Δ / 10 ≤ Fs x / ρ j / (ρ x / ρ j) → Fs x / ρ j / (ρ x / ρ j) ≤ 10 * Δ →
      ∀ y ∈ ball x (100 * (ρ x / ρ j)), ∀ ξ : EuclideanSpace ℝ (Fin 2), ‖ξ‖ = 1 →
        ∃ W : TangentSpace 𝓘(ℝ, E3) y, gR.inner y W W = 1 ∧
          9 / 10 < inner ℝ ((ρ x / ρ j) • mvfderiv (I := 𝓘(ℝ, E3))
            (edgeReferenceCoordinates ![c.coord, fun z => Fs z / ρ j / (ρ z / ρ j)]) y W) ξ := by
  have hcc0 := Fe.chart_center j hj
  intro c Fs hMc gR x hx hη hF1 hF2 y hy ξ hξ
  let _ := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let _ := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let _ : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let _ : IsRiemannianManifold 𝓘(ℝ, E3) X :=
    radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let _ : CompleteSpace X := (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
  have hcc : c.center = j := hcc0
  have hx' : x ∈ ball c.center (100 * Δ) := by
    rw [hcc]
    exact hx
  obtain ⟨W, hW, -, h⟩ := c.collar_singular_margin_FAM hγc hγc1 hβc1 hx' hη hF1 hF2 hy ξ hξ
  exact ⟨W, hW, h⟩

end DifferentialGeometry.Geometry.Collapse
