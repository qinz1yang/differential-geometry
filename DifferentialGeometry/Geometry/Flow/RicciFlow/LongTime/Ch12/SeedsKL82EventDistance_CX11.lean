import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorFlow
import DifferentialGeometry.Geometry.Metric.RestrictionDistance
import DifferentialGeometry.Geometry.Metric.DistancePullback

set_option autoImplicit false

noncomputable section

open Set TopologicalSpace Manifold DifferentialGeometry
  DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Metric
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12

universe u

/-- Restricting to an open set containing a ball preserves distances from its centre
to every point of that ball. No connectedness or completeness assumption is needed. -/
theorem edist_restrict_eq_center_CX11
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] [T2Space M]
    (g : SmoothRiemannianMetric ThreeModel M) (U : Opens M)
    (x y : U) {ρ : ℝ} (hball : riemannianBallOf g x.val ρ ⊆ U)
    (hy : riemannianEDistOf g x.val y.val < ENNReal.ofReal ρ) :
    riemannianEDistOf (g.restrictOpen U) x y = riemannianEDistOf g x.val y.val := by
  apply le_antisymm
  · by_contra hn
    have hlt := lt_of_not_ge hn
    obtain ⟨c, hc, hcu⟩ := exists_between (lt_min hlt hy)
    have hcρ : c < ENNReal.ofReal ρ := hcu.trans_le (min_le_right _ _)
    have hcfin : c ≠ ⊤ := ne_top_of_lt hcρ
    have hcr : ENNReal.ofReal c.toReal = c := ENNReal.ofReal_toReal hcfin
    have hrρ : c.toReal ≤ ρ := by
      apply (ENNReal.ofReal_le_ofReal_iff ?_).mp
      · rw [hcr]
        exact hcρ.le
      · exact (ENNReal.ofReal_pos.mp (lt_of_le_of_lt bot_le hy)).le
    have hsub : riemannianBallOf g x.val c.toReal ⊆ U :=
      (riemannianBallOf_mono _ _ hrρ).trans hball
    have hh := riemannianEDistOf_restrictOpen_lt_of_riemannianBallOf_subset
      g U x y hsub (by rw [hcr]; exact hc)
    rw [hcr] at hh
    exact (not_lt_of_ge (hcu.trans_le (min_le_left _ _)).le) hh
  · exact riemannianEDistOf_le_restrictOpen g U x y

/-- At a surgery, an outgoing ball whose points all cross regularly has no shorter
incoming-terminal distance. This is the event step in KL 82.1's backward distance
argument; the codomain is the actual terminal regular open manifold. -/
theorem terminal_edist_le_output_of_survivor_ball_CX11
    (H : ObservedHistory.{u}) (i : Fin H.eventCount) {ρ : ℝ}
    (x y : H.backwardSurvivorDomain i.castSucc i.succ i.castSucc_lt_succ.le)
    (hball : riemannianBallOf (H.initialMetric i.succ) x.val ρ ⊆
      H.backwardSurvivorDomain i.castSucc i.succ i.castSucc_lt_succ.le)
    (hy : riemannianEDistOf (H.initialMetric i.succ) x.val y.val < ENNReal.ofReal ρ) :
    riemannianEDistOf (H.event i).terminal.metric
        (H.backwardSurvivorTerminalMap i.castSucc i.succ i.castSucc_lt_succ.le
          i le_rfl le_rfl x)
        (H.backwardSurvivorTerminalMap i.castSucc i.succ i.castSucc_lt_succ.le
          i le_rfl le_rfl y) ≤
      riemannianEDistOf (H.initialMetric i.succ) x.val y.val := by
  let U := H.backwardSurvivorDomain i.castSucc i.succ i.castSucc_lt_succ.le
  let f := H.backwardSurvivorTerminalMap i.castSucc i.succ i.castSucc_lt_succ.le
    i le_rfl le_rfl
  have hf := H.backwardSurvivorTerminalMap_isLocalDiffeomorph i.castSucc i.succ
    i.castSucc_lt_succ.le i le_rfl le_rfl
  have hm : H.backwardSurvivorMap i.castSucc i.succ i.castSucc_lt_succ.le
      i.succ i.castSucc_lt_succ.le le_rfl = Subtype.val :=
    funext (H.backwardSurvivorMap_last i.castSucc i.succ i.castSucc_lt_succ.le)
  have hinner (z : U) (v : TangentSpace ThreeModel z) :
      (H.event i).terminal.metric.inner (f z)
        (mfderiv ThreeModel ThreeModel f z v) (mfderiv ThreeModel ThreeModel f z v) =
      ((H.initialMetric i.succ).restrictOpen U).inner z v v := by
    have hh := H.backwardSurvivorMap_metric_crossing i.castSucc i.succ
      i.castSucc_lt_succ.le i le_rfl le_rfl z v v
    rw [hm, mfderiv_subtype_val_apply] at hh
    exact hh.symm
  have hh := edistOf_le_of_quad_of_localDiffeomorph
    ((H.initialMetric i.succ).restrictOpen U) (H.event i).terminal.metric f hf
    (c := 1) one_pos (fun z v => by rw [hinner, one_mul]) x y
  simp only [Real.sqrt_one, ENNReal.ofReal_one, one_mul] at hh
  exact hh.trans_eq (edist_restrict_eq_center_CX11 _ U x y hball hy)

end GC.LongTime.Ch12
