import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.SolidTorusRegionsSTR
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageOfBundlesCircle74

/-!
# S-SOLIDTORUS3 (suffix `_STR`), G4: the circle facts of the solid torus cut

`CircleCutFacts74` for the cut `D = cutChoice_STR ballZeroDomainsL_STR` over `circleBaseOpen = ⊤`:

* the local trivializations are the restrictions over `⊤` of the global trivialization of the X135
  circle bundle (S-JUNCTIONS2's kit `stageTrivialization_JN74`; the circle stage of this instance is
  `StageProj74.ofCircleBundle74 X135Radial.radialCircleBundle`);
* whole-circle properness is `CircleBundle.proj_proper_JN74`;
* `C₁ = {5/8 ≤ |q|² ≤ 15/16, Re q ≤ 4/5}` is compact (closed and bounded in the plane model);
* the saturation `M₃ = q₀⁻¹(C₁)` is the one rewriting `M3_eq_STR` against the planar description
  `circleRegion_eq_STR` of `q₀⁻¹(C₁)` (`q = z₂`, `|q|² = (1 - h)/2`, `Re q = u`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0.SolidTorusSTR

open GC.GraphManifold.Assembly.FC39P0.SolidTorusSTI GC.GraphManifold.Assembly.FC39P0

local instance carrierCharts_CircleFactsSTR : ChartedSpace (EuclideanHalfSpace 3) Wc.Carrier := by
  change ChartedSpace (EuclideanHalfSpace 3) solidTorusSet.{0}
  exact inferInstance

local instance carrierSmooth_CircleFactsSTR : IsManifold (𝓡∂ 3) ∞ Wc.Carrier := by
  change IsManifold (𝓡∂ 3) ∞ solidTorusSet.{0}
  exact inferInstance

/-! ## The planar region `C₁` is compact -/

/-- The region `C₁` in the plane model. -/
def circleC1Ambient_STR : Set (EuclideanSpace ℝ (Fin 2)) :=
  {z | 5 / 8 ≤ ‖modelPlaneComplex z‖ ^ 2 ∧ ‖modelPlaneComplex z‖ ^ 2 ≤ 15 / 16 ∧
    (modelPlaneComplex z).re ≤ 4 / 5}

theorem circleC1Ambient_compact_STR : IsCompact circleC1Ambient_STR := by
  have hc : IsClosed circleC1Ambient_STR :=
    ((isClosed_le continuous_const
      (modelPlaneComplex.continuous.norm.pow 2)).inter
      ((isClosed_le (modelPlaneComplex.continuous.norm.pow 2) continuous_const).inter
        (isClosed_le (Complex.continuous_re.comp modelPlaneComplex.continuous)
          continuous_const)))
  apply (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1).of_isClosed_subset hc
  intro z hz
  rw [Metric.mem_closedBall, dist_zero_right]
  have h1 : ‖modelPlaneComplex z‖ ^ 2 ≤ 15 / 16 := hz.2.1
  rw [modelPlaneComplex.norm_map] at h1
  nlinarith [norm_nonneg z]

theorem circleC1_image_STR :
    (fun b : circleStage_STR.Base => b.val.val) '' circleC1_STR = circleC1Ambient_STR := by
  ext z
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact hb
  · intro hz
    have h1 : 5 / 8 ≤ ‖modelPlaneComplex z‖ ^ 2 := hz.1
    have h2 : ‖modelPlaneComplex z‖ ^ 2 ≤ 15 / 16 := hz.2.1
    rw [modelPlaneComplex.norm_map] at h1 h2
    have hnorm : ‖z‖ < 1 := by nlinarith [norm_nonneg z]
    have hpos : (1 / 2 : ℝ) < ‖z‖ ^ 2 := by linarith
    exact ⟨⟨⟨z, hnorm⟩, hpos⟩, hz, rfl⟩

theorem circleC1_compact_STR : IsCompact circleC1_STR := by
  have he : Topology.IsEmbedding (fun b : circleStage_STR.Base => b.val.val) :=
    Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal
  apply he.isCompact_iff.mpr
  rw [circleC1_image_STR]
  exact circleC1Ambient_compact_STR

theorem circleCbase_compact_STR (Z : ZeroDomains Wc) :
    IsCompact (Subtype.val ⁻¹' (cutChoice_STR Z).C₁ : Set (cutChoice_STR Z).circleBaseOpen) :=
  isCompact_preimage_top_JN74 circleC1_compact_STR

/-! ## The circle region `q₀⁻¹(C₁)` in the coordinates `u`, `h` -/

theorem circleRegion_eq_STR (Z : ZeroDomains Wc) :
    (cutChoice_STR Z).circleRegion =
      {p | uW_STR p ≤ 4 / 5 ∧ -(7 / 8 : ℝ) ≤ X135Radial.height p ∧
        X135Radial.height p ≤ -(1 / 4 : ℝ)} := by
  ext x
  constructor
  · rintro ⟨hx, hc⟩
    have hq : modelPlaneComplex (X135Radial.radialCircleProjection ⟨x, hx⟩).val.val =
        sphereSecond x.val := X135Radial.radialCircleProjection_complex ⟨x, hx⟩
    obtain ⟨h1, h2, h3⟩ := hc
    have h1' : 5 / 8 ≤ ‖sphereSecond x.val‖ ^ 2 := by
      change 5 / 8 ≤ ‖modelPlaneComplex (X135Radial.radialCircleProjection ⟨x, hx⟩).val.val‖ ^ 2
        at h1
      rwa [hq] at h1
    have h2' : ‖sphereSecond x.val‖ ^ 2 ≤ 15 / 16 := by
      change ‖modelPlaneComplex (X135Radial.radialCircleProjection ⟨x, hx⟩).val.val‖ ^ 2 ≤ 15 / 16
        at h2
      rwa [hq] at h2
    have h3' : (sphereSecond x.val).re ≤ 4 / 5 := by
      change (modelPlaneComplex (X135Radial.radialCircleProjection ⟨x, hx⟩).val.val).re ≤ 4 / 5
        at h3
      rwa [hq] at h3
    have hn := norm_second_sq_STR x
    refine ⟨h3', ?_, ?_⟩ <;> linarith
  · rintro ⟨hu, hl, hh⟩
    have hx : x ∈ X135Radial.radialCircleDomain := by
      change -1 < X135Radial.height x ∧ X135Radial.height x < 0
      constructor <;> linarith
    refine ⟨hx, ?_⟩
    have hq : modelPlaneComplex (X135Radial.radialCircleProjection ⟨x, hx⟩).val.val =
        sphereSecond x.val := X135Radial.radialCircleProjection_complex ⟨x, hx⟩
    have hn := norm_second_sq_STR x
    change 5 / 8 ≤ ‖modelPlaneComplex (X135Radial.radialCircleProjection ⟨x, hx⟩).val.val‖ ^ 2 ∧
      ‖modelPlaneComplex (X135Radial.radialCircleProjection ⟨x, hx⟩).val.val‖ ^ 2 ≤ 15 / 16 ∧
      (modelPlaneComplex (X135Radial.radialCircleProjection ⟨x, hx⟩).val.val).re ≤ 4 / 5
    rw [hq]
    refine ⟨?_, ?_, hu⟩ <;> linarith

/-- **FDC03 saturation**: `M₃ = q₀⁻¹(C₁)` (one rewriting by `M3_eq_STR`). -/
theorem saturation_STR :
    (cutChoice_STR ballZeroDomainsL_STR).M₃ = (cutChoice_STR ballZeroDomainsL_STR).circleRegion :=
  M3_eq_STR.trans (circleRegion_eq_STR ballZeroDomainsL_STR).symm

/-! ## Whole-circle properness over `⊤` -/

theorem circleProper_STR (Z : ZeroDomains Wc) (K : Set (cutChoice_STR Z).circleBaseOpen)
    (hK : IsCompact K) :
    IsCompact (Subtype.val '' ((stageGeometry_STR Z).circle.restrictProj
      (cutChoice_STR Z).circleBaseOpen ⁻¹' K)) := by
  have hc : IsCompact (Subtype.val '' K : Set X135Radial.radialCircleBundle.Base) :=
    hK.image continuous_subtype_val
  have h := X135Radial.radialCircleBundle.proj_proper_JN74 hc
  have heq := image_restrictTop_JN74 circleStage_STR
    (fun y => X135Radial.radialCircleBundle.proj y ∈ Subtype.val '' K)
  have hset : Subtype.val '' ((stageGeometry_STR Z).circle.restrictProj
      (cutChoice_STR Z).circleBaseOpen ⁻¹' K) =
      Subtype.val '' {x : X135Radial.radialCircleBundle.domain |
        X135Radial.radialCircleBundle.proj x ∈ Subtype.val '' K} := by
    refine Eq.trans ?_ heq
    congr 1
    ext x
    change ((stageGeometry_STR Z).circle.restrictProj (cutChoice_STR Z).circleBaseOpen x) ∈ K ↔
      ((stageGeometry_STR Z).circle.restrictProj (cutChoice_STR Z).circleBaseOpen x).val ∈
        Subtype.val '' K
    exact (Subtype.val_injective.mem_set_image).symm
  rw [hset]
  exact h

/-! ## The circle facts -/

/-- **The circle facts of the solid torus cut** (`CircleCutFacts74`): trivializations restricted
from the X135 global one, properness, compact `C₁`, saturation by `M3_eq_STR`. -/
def circleFacts_STR : CircleCutFacts74 (stageGeometry_STR ballZeroDomainsL_STR)
    (cutChoice_STR ballZeroDomainsL_STR) where
  neighborhood c := X135Radial.radialCircleBundle.stageNeighborhood_JN74 ⊤ c
  mem_neighborhood c := X135Radial.radialCircleBundle.mem_stageNeighborhood_JN74 ⊤ c
  trivialization c := X135Radial.radialCircleBundle.stageTrivialization_JN74 ⊤ c
  projection_trivialization c x :=
    X135Radial.radialCircleBundle.stageProjection_trivialization_JN74 ⊤ c x
  proper := circleProper_STR ballZeroDomainsL_STR
  cbase_compact := circleCbase_compact_STR ballZeroDomainsL_STR
  saturation := saturation_STR

end GC.GraphManifold.Assembly.FC39P0.SolidTorusSTR
