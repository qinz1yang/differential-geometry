import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SeedGeodesicConsumerCXSP
import DifferentialGeometry.Geometry.Metric.Restriction.Ball
import DifferentialGeometry.Topology.Manifold.ConnectedComponent

set_option autoImplicit false

/-!
# CX-SPINE G2：disconnected compact slice 的实际 minimizing segment

有限半径球内的两点属于同一 connected component。限制到该开闭紧分支，应用
Hopf–Rinow，再由 restrictOpen 的距离等式回到原 metric；不假设整个 stage connected。
-/

noncomputable section

open Set DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch11

universe u

/-- 紧流形的有限半径球中实际生产一条保持原 metric 距离的 smooth minimizing segment。 -/
theorem exists_seed_segment_of_compact_CXSP
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] [T2Space M] [CompactSpace M]
    (g : SmoothRiemannianMetric ThreeModel M) (p x : M) {ρ : ℝ}
    (hx : x ∈ riemannianBallOf g p ρ) (hpx : p ≠ x) :
    ∃ (L : ℝ) (γ : ℝ → M), 0 ≤ L ∧ L < ρ ∧ γ 0 = p ∧ γ L = x ∧
      ContMDiff 𝓘(ℝ, ℝ) ThreeModel ∞ γ ∧
      (∀ v, γ v ∈ connectedComponent p) ∧
      ∀ a ∈ Icc (0 : ℝ) L, ∀ b ∈ Icc (0 : ℝ) L,
        riemannianEDistOf g (γ a) (γ b) = ENNReal.ofReal |a - b| := by
  let U := connectedComponentOpen (I := ThreeModel) p
  let : ConnectedSpace U := connectedComponentOpen_connectedSpace p
  let : CompactSpace U := connectedComponentOpen_compactSpace p
  let pU : U := ⟨p, mem_connectedComponent⟩
  let xU : U := ⟨x, Geometry.Metric.edistOf_ball_subset_connCompOpen g p ρ hx⟩
  let gU := g.restrictOpen U
  have hdistU (z w : U) : riemannianEDistOf gU z w =
      riemannianEDistOf g (z : M) (w : M) :=
    riemannianEDistOf_restrictOpen_of_isClosed g U isClosed_connectedComponent z w
  let : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  obtain ⟨γU, hstart, hend, hsmooth, _, _, hdist⟩ :=
    DifferentialGeometry.Geometry.exists_unitSpeed_minimizing_geodesic_of_complete
      gU (DifferentialGeometry.RiemannianMetricComplete.of_compact gU) pU xU
      (fun h => hpx (congrArg Subtype.val h))
  let L := (riemannianEDistOf gU pU xU).toReal
  have hL : 0 ≤ L := ENNReal.toReal_nonneg
  have hfinite (z w : U) : ENNReal.ofReal (riemannianEDistOf gU z w).toReal =
      riemannianEDistOf gU z w := ENNReal.ofReal_toReal (riemannianEDistOf_ne_top gU z w)
  have hρ : 0 < ρ := ENNReal.ofReal_pos.mp (lt_of_le_of_lt bot_le hx)
  have hlen : L < ρ := by
    apply (ENNReal.ofReal_lt_ofReal_iff hρ).mp
    rw [hfinite pU xU, hdistU]
    exact hx
  refine ⟨L, fun v => (γU v : M), hL, hlen,
    congrArg Subtype.val hstart, congrArg Subtype.val hend,
    (contMDiff_subtype_val (I := ThreeModel) (U := U)).comp hsmooth,
    fun v => (γU v).property, ?_⟩
  intro a ha b hb
  rw [← hdistU, ← hfinite, hdist a ha b hb]

end GC.LongTime.Ch11
