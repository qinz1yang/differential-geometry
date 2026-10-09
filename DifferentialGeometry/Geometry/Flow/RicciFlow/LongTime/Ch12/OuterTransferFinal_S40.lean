import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.OuterTransferAssembly_S40
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.OuterCurvature_S41
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.OuterCurvatureLow_S41

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set
open Manifold GC.LongTime
open scoped Manifold ContDiff ENNReal
universe u
namespace GC.LongTime.Ch12

/-- **(G4)** `hTrans` discharged: the single inline hypothesis of `outerThin_ambient_v2_S35` is
supplied by `hTrans_of_curv_S40` from S41's `hUp_S41`, `hLow_S41` and S40's `hC0_S40`. -/
theorem hTrans_S40 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {K : ℕ} (B : BufferedPersistentCores F K) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ T₁ : ℝ, ∀ t (ht : B.start ≤ t), T₁ ≤ t →
      ∀ i : Fin B.count,
      ∀ y ∈ riemannianBallOf (B.model i).metric (B.model i).basepoint (B.accuracy t)⁻¹,
        (∀ q ∈ riemannianBallOf (scaleMetric t⁻¹ (inv_pos.mpr (B.start_pos.trans_le ht))
            (postMetric F.observation t)) (B.map i t ht y) c₀,
          SectionalBoundedBelowAt (scaleMetric t⁻¹ (inv_pos.mpr (B.start_pos.trans_le ht))
            (postMetric F.observation t)) q (-(c₀ ^ 2)⁻¹)) ∧
        ¬ SectionalBoundedBelowAt (scaleMetric t⁻¹ (inv_pos.mpr (B.start_pos.trans_le ht))
            (postMetric F.observation t)) (B.map i t ht y) (-(1 / 8 : ℝ)) ∧
        ∀ r : ℝ, 0 < r → r ^ 2 ≤ 8 →
          ballVolume (scaleMetric t⁻¹ (inv_pos.mpr (B.start_pos.trans_le ht))
            (postMetric F.observation t)) (B.map i t ht y) r ≤
          ENNReal.ofReal 2 * ballVolume (B.model i).metric y 4 :=
  hTrans_of_curv_S40 B (hUp_S41 B) (hLow_S41 B (hC0_S40 B))

/-- **(G4)** Outer thinness with NO transfer hypothesis left (only the buffered cores `B` and the
truncation `base`). -/
theorem outerThin_ambient_S40 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {K : ℕ} (B : BufferedPersistentCores F K)
    (base : ∀ i : Fin B.count, HyperbolicTruncation (B.model i)) :
    ∀ w : ℝ, 0 < w → ∃ T : ℝ, ∀ t (ht : B.start ≤ t), T ≤ t →
      ∀ trunc : (i : Fin B.count) → HyperbolicTruncation (B.model i),
        (∀ i, riemannianClosedBallOf (B.model i).metric (B.model i).basepoint
            ((B.accuracy t)⁻¹ / 2) ⊆ Set.range (trunc i).inclusion) →
        ∀ x : (postStage F.observation t).Carrier,
          x ∉ ⋃ i : Fin B.count, B.map i t ht '' Set.range (trunc i).inclusion →
          volumeCollapsedAtCurvatureScale
            (scaleMetric t⁻¹ (inv_pos.mpr (B.start_pos.trans_le ht))
              (postMetric F.observation t)) w x :=
  outerThin_ambient_v2_S35 B base (hTrans_S40 B)

end GC.LongTime.Ch12
