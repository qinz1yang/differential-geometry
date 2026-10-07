import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ScalarNonnegativeBranch_R2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.LargeTriggerTransfer_S21
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.BoundaryWiringG2_S16

set_option autoImplicit false

/-!
# CH12-R2 Q1(c).3: vanishing total volume implies T3

T2 puts the trigger ball inside the cut-piece boundary distance. Its volume
therefore transfers to the ambient normalized slice. The fixed lower bound
`w * b^3` contradicts vanishing ambient total volume.
-/

noncomputable section

open Set MeasureTheory DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.LongTime
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12

universe u

theorem LateCutFamily.hT3_of_volumeVanishes_R2
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (K : ℕ)
    (slices : ℕ → RegularSlice F.observation)
    (htimes : ∀ j : ℕ, (j : ℝ) < (slices j).time)
    (L : GC.LongTime.LateCutFamily F K slices)
    (hvol0 : NormalizedVolumeVanishes_R2 F) :
    ∀ w : ℝ, 0 < w → w < euclideanThreeUnitBallVolume →
    ∀ b : ℝ, 0 < b →
      ∃ N : ℕ, ∀ j, N ≤ j →
      ∀ c i, L.thin j c i →
      ∀ p : ((L.decomposition j c).component i).Carrier,
        ENNReal.ofReal 10 <
          distanceToBoundary ((L.decomposition j c).component i) (L.metric j c i) p →
      ∀ r : ℝ, 0 < r →
        ENNReal.ofReal r < curvatureRadius (L.metric j c i) p →
        ENNReal.ofReal (w * r ^ 3) ≤ ballVolume (L.metric j c i) p r →
        r < b := by
  intro w hw _ b hb
  obtain ⟨N₂, hN₂⟩ := LateCutFamily.eventually_interior_scale_core_T2 L
    (collarNegativePlane_S16 K)
  obtain ⟨T, hT⟩ := hvol0 (w * b ^ 3) (mul_pos hw (pow_pos hb _))
  refine ⟨max N₂ (Nat.ceil T), ?_⟩
  intro j hj c i hi p hp r hr hscale hvol
  have hD := (hN₂ j ((le_max_left _ _).trans hj) c i hi p hp).2.1
  have htransfer := (LateCutFamily.cutPiece_normalized_transfer_hd_S21 L j c i p r hr
    (hscale.trans hD)).2.1
  have htime : T ≤ (slices j).time :=
    (Nat.le_ceil T).trans ((by exact_mod_cast (le_max_right N₂ (Nat.ceil T)).trans hj :
      (Nat.ceil T : ℝ) ≤ (j : ℝ)).trans (htimes j).le)
  have hsmall := hT (slices j) htime
  have hball : ballVolume (slices j).normalizedMetric
      (cutPieceMap (L.decomposition j c) i p).val r ≤ normalizedTotalVolume_S13 (slices j) :=
    measure_mono (subset_univ _)
  by_contra hnot
  have hbr : b ≤ r := not_lt.mp hnot
  have hpoly : w * b ^ 3 ≤ w * r ^ 3 := by gcongr
  have hle : ENNReal.ofReal (w * b ^ 3) ≤ normalizedTotalVolume_S13 (slices j) := by
    calc _ ≤ ENNReal.ofReal (w * r ^ 3) := ENNReal.ofReal_le_ofReal hpoly
      _ ≤ ballVolume (L.metric j c i) p r := hvol
      _ = _ := htransfer
      _ ≤ _ := hball
  exact (not_lt_of_ge hle) hsmall

end GC.LongTime.Ch12
