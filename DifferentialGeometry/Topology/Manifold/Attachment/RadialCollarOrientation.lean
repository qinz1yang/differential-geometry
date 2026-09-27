import DifferentialGeometry.Topology.Manifold.SmoothOrientationComparison
import DifferentialGeometry.Topology.Manifold.SmoothOrientationPullback
import DifferentialGeometry.Topology.Manifold.ImmersionDifferential
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingFromOpen
import DifferentialGeometry.Topology.Manifold.Attachment.RadialEmbedding
import Mathlib.Analysis.Normed.Module.Connected

set_option autoImplicit false
noncomputable section
open Set Function Manifold
open DifferentialGeometry.Topology.Manifold DifferentialGeometry.Topology.Manifold.Attachment
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Topology.Manifold.Attachment
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev S2 := Metric.sphere (0 : E3) 1
private abbrev IR := (𝓡 2).prod (𝓡∂ 1)
private abbrev Collar (B : ℝ) := S2 × Ico (0 : ℝ) B
private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

def radialCollarOrientationMap (L B : ℝ) (q : Collar B) : E3 := (L + q.2.val) • q.1.val

theorem radialCollarOrientationMap_isSmoothEmbedding {L B : ℝ} (hL : 0 < L) (hB : 0 < B) :
    letI := halfClosedIntervalChartedSpace hB
    IsSmoothEmbedding IR (𝓡 3) ∞ (radialCollarOrientationMap L B) := by
  let := halfClosedIntervalChartedSpace hB
  exact isSmoothEmbedding_fromOpen IR (𝓡 3) _ (retainedRadialMap hL)
    (isSmoothEmbedding_retainedRadialMap hL hB)

theorem radialCollarOrientationMap_mfderiv_bijective {L B : ℝ} (hL : 0 < L) (hB : 0 < B)
    (q : Collar B) :
    letI := halfClosedIntervalChartedSpace hB
    Bijective (mfderiv IR (𝓡 3) (radialCollarOrientationMap L B) q) := by
  let := halfClosedIntervalChartedSpace hB
  exact bijective_mfderiv_of_isImmersionAt IR (𝓡 3) _ q
    ((radialCollarOrientationMap_isSmoothEmbedding hL hB).isImmersion.isImmersionAt q) (by simp)

def radialCollarSmoothOrientation {L B : ℝ} (hL : 0 < L) (hB : 0 < B)
    (o : Orientation ℝ E3 (Fin (Module.finrank ℝ E3))) :
    letI := halfClosedIntervalChartedSpace hB
    letI := halfClosedInterval_isManifold hB
    SmoothOrientation IR (Collar B) := by
  let := halfClosedIntervalChartedSpace hB
  let := halfClosedInterval_isManifold hB
  exact pullbackSmoothOrientation IR (𝓡 3) (radialCollarOrientationMap L B)
    (radialCollarOrientationMap_isSmoothEmbedding hL hB).contMDiff
    (radialCollarOrientationMap_mfderiv_bijective hL hB) (euclideanSmoothOrientation E3 o)

theorem radialCollarSmoothOrientation_neg_apply {L B : ℝ} (hL : 0 < L) (hB : 0 < B)
    (o : Orientation ℝ E3 (Fin (Module.finrank ℝ E3))) (q : Collar B) :
    letI := halfClosedIntervalChartedSpace hB
    letI := halfClosedInterval_isManifold hB
    (radialCollarSmoothOrientation hL hB (-o)).val q =
      -(radialCollarSmoothOrientation hL hB o).val q := by
  let := halfClosedIntervalChartedSpace hB
  let := halfClosedInterval_isManifold hB
  exact tangentOrientationEquiv_neg
    (differentialEquivOfBijective IR (𝓡 3) (radialCollarOrientationMap L B)
      (radialCollarOrientationMap_mfderiv_bijective hL hB) q).symm.toLinearEquiv o

theorem exists_radialCollarSmoothOrientation {L B : ℝ} (hL : 0 < L) (hB : 0 < B) :
    letI := halfClosedIntervalChartedSpace hB
    letI := halfClosedInterval_isManifold hB
    ∀ O : SmoothOrientation IR (Collar B),
      ∃ o : Orientation ℝ E3 (Fin (Module.finrank ℝ E3)),
        (o = (Module.finBasis ℝ E3).orientation ∨ o = -(Module.finBasis ℝ E3).orientation) ∧
        ∀ q : Collar B, (radialCollarSmoothOrientation hL hB o).val q = O.val q := by
  let := halfClosedIntervalChartedSpace hB
  let := halfClosedInterval_isManifold hB
  refine fun O => ?_
  let : ConnectedSpace S2 := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (by rw [← Module.finrank_eq_rank]; norm_num) (0 : E3) (by norm_num : (0 : ℝ) ≤ 1))
  let : PreconnectedSpace (Ico (0 : ℝ) B) := Subtype.preconnectedSpace isPreconnected_Ico
  let o₀ : Orientation ℝ E3 (Fin (Module.finrank ℝ E3)) := (Module.finBasis ℝ E3).orientation
  let y : S2 := Classical.choice (NormedSpace.sphere_nonempty_rclike ℝ (E := E3) (r := (1 : ℝ)) zero_le_one)
  let q₀ : Collar B := (y, ⟨0, le_rfl, hB⟩)
  rcases smoothOrientation_eq_or_eq_neg IR O (radialCollarSmoothOrientation hL hB o₀) q₀ with h | h
  · exact ⟨o₀, Or.inl rfl, fun q => (h q).symm⟩
  · refine ⟨-o₀, Or.inr rfl, ?_⟩
    intro q
    rw [radialCollarSmoothOrientation_neg_apply]
    exact (h q).symm
end DifferentialGeometry.Topology.Manifold.Attachment
