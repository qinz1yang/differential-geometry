import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SliceDefectQuad_S45
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.LTF03Uniform_S45

set_option autoImplicit false

/-!
# CH12-S45 / G1: LTF03 in the form consumed by the first-failure argument

For every late regular slice `s` carrying a macroscopic seed `(a, v)` at `p`, the physical metric
satisfies `|2 s Ric(V,V) + g(V,V)| ≤ ε g(V,V)` for every vector `V` at every point of the
normalized ball `B(p, L)`.  This is `ltf03_threshold_S45` composed with `slice_defect_quad_S45`.
-/

noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.LongTime Set
open scoped Manifold ContDiff
namespace GC.LongTime.Ch12
universe u

theorem ltf03_vector_threshold_S45 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} (Hp : AnalyticSurgeryProfile F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    (hneg : EventuallyNegativeScalar_S13 F)
    (hLTF03 : ∀ (S : LatePointSequence_S13 F) (a v L : ℝ),
      SeedHyperbolicOnFixedBallsSeq_S13 Hp hdec hneg S a v L)
    (a v L ε : ℝ) (ha : 0 < a) (hv : 0 < v) (hL : 0 < L) (hε : 0 < ε) :
    ∃ T : ℝ, ∀ s : RegularSlice F.observation, T ≤ s.time →
      ∀ p : s.stage.Carrier, HasNormalizedSeed_S13 s p a v →
        ∀ q ∈ riemannianBallOf s.normalizedMetric p L, ∀ V : TangentSpace ThreeModel q,
          |2 * s.time * ricciTensor s.metric q V V + s.metric.inner q V V| ≤
            ε * s.metric.inner q V V := by
  obtain ⟨T, hT⟩ := ltf03_threshold_S45 Hp hdec hneg hLTF03 a v L ε ha hv hL hε
  refine ⟨T, fun s hs p hp q hq V => ?_⟩
  exact (slice_defect_quad_S45 s q V).trans
    (mul_le_mul_of_nonneg_right (hT s hs p hp q hq).le (metric_inner_self_nonneg _ _ _))

end GC.LongTime.Ch12
