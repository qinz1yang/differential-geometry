import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.GoodPointBufferedCanonical
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NormalizedSourceRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventData

noncomputable section
open Set
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle

theorem exists_good_point_buffered_bounds_for_normalized_sequences
    {kappa alpha theta : ℝ} (ha : 0 < alpha)
    (haSmall : alpha < 1 / 44) (htheta : 0 < theta) :
    ∃ Lmin Lmax : ℝ, 0 < Lmin ∧ Lmin < Lmax ∧ ∀ H : ℝ, 0 < H →
      ∃ epsStar C : ℝ, 0 < epsStar ∧ epsStar < alpha ∧ 1 ≤ C ∧
        ∀ {sigma : ℝ} {Phi : ℝ → ℝ} (X : NormalizedSequence.{u} epsStar kappa sigma Phi)
          (i : ℕ) (t : ℝ), t ∈ Icc (-X.depth i) 0 → ∀ x : (X.term i).M,
          2 ≤ (X.term i).S.scalar t x →
          Nonempty (BufferedCanonical (X.term i).S alpha C H x t) ∧
          ∀ a b : MinimizingArm ((X.term i).S.base.metric t) x, ∀ s v : ℝ,
            s ∈ Set.Ioc 0 a.length → v ∈ Set.Ioc 0 b.length →
            Real.sqrt ((X.term i).S.scalar t x) * s ∈ Set.Icc Lmin Lmax →
            Real.sqrt ((X.term i).S.scalar t x) * v ∈ Set.Icc Lmin Lmax →
            theta ≤ Real.arccos ((s ^ 2 + v ^ 2 -
              metricDistance ((X.term i).S.base.metric t) (a.point s) (b.point v) ^ 2) / (2 * s * v)) →
            ∃ (neck : StrongNeck (X.term i).S (2 * alpha) x t)
              (path : TransversePath (a.point a.length) (b.point b.length)
                (neck.map '' (Set.univ ×ˢ ({0} : Set ℝ)))),
              (path.intersection = 1 ∨ path.intersection = -1) ∧
              (∀ w ∈ Set.Icc s a.length,
                a.point w ∉ neck.map '' (Set.univ ×ˢ ({0} : Set ℝ))) ∧
              (∀ w ∈ Set.Icc v b.length,
                b.point w ∉ neck.map '' (Set.univ ×ˢ ({0} : Set ℝ))) ∧
              (∀ y ∈ neck.map '' (Set.univ ×ˢ Set.Icc (-10) 10),
                ∀ z ∈ neck.map '' (Set.univ ×ˢ Set.Icc (-10) 10),
                  metricDistance ((X.term i).S.base.metric t) y z ≤ C / Real.sqrt ((X.term i).S.scalar t x)) := by
  obtain ⟨Lmin, Lmax, hLmin, hLmax, hmain⟩ :=
    good_point_buffered_canonical ha haSmall htheta
  refine ⟨Lmin, Lmax, hLmin, hLmax, ?_⟩
  intro H hH
  obtain ⟨epsStar, C, heps, hepsAlpha, hC, hbody⟩ := hmain H hH
  refine ⟨epsStar, C, heps, hepsAlpha, hC, ?_⟩
  intro sigma Phi X i t ht x hx
  have hw := X.higher_good i t ht x hx
  exact hbody (X.term i).M (X.interval i) (X.term i).S (X.orientation i) x t
    (X.term i).isSolution (X.regular_window_of_higher_good i ht hx hw.choose) hw

theorem exists_good_point_buffered_bounds_for_incoming_slabs
    {kappa alpha theta : ℝ} (ha : 0 < alpha)
    (haSmall : alpha < 1 / 44) (htheta : 0 < theta) :
    ∃ Lmin Lmax : ℝ, 0 < Lmin ∧ Lmin < Lmax ∧ ∀ H : ℝ, 0 < H →
      ∃ epsStar C : ℝ, 0 < epsStar ∧ epsStar < alpha ∧ 1 ≤ C ∧
        ∀ {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s)
          (o : TangentOrientationSection P.Carrier) (x : P.Carrier) (t : ℝ),
          OrientedWitness G.flow o epsStar kappa x t →
          Nonempty (BufferedCanonical G.flow alpha C H x t) ∧
          ∀ a b : MinimizingArm (G.flow.base.metric t) x, ∀ s v : ℝ,
            s ∈ Set.Ioc 0 a.length → v ∈ Set.Ioc 0 b.length →
            Real.sqrt (G.flow.scalar t x) * s ∈ Set.Icc Lmin Lmax →
            Real.sqrt (G.flow.scalar t x) * v ∈ Set.Icc Lmin Lmax →
            theta ≤ Real.arccos ((s ^ 2 + v ^ 2 -
              metricDistance (G.flow.base.metric t) (a.point s) (b.point v) ^ 2) / (2 * s * v)) →
            ∃ (neck : StrongNeck G.flow (2 * alpha) x t)
              (path : TransversePath (a.point a.length) (b.point b.length)
                (neck.map '' (Set.univ ×ˢ ({0} : Set ℝ)))),
              (path.intersection = 1 ∨ path.intersection = -1) ∧
              (∀ w ∈ Set.Icc s a.length,
                a.point w ∉ neck.map '' (Set.univ ×ˢ ({0} : Set ℝ))) ∧
              (∀ w ∈ Set.Icc v b.length,
                b.point w ∉ neck.map '' (Set.univ ×ˢ ({0} : Set ℝ))) ∧
              (∀ y ∈ neck.map '' (Set.univ ×ˢ Set.Icc (-10) 10),
                ∀ z ∈ neck.map '' (Set.univ ×ˢ Set.Icc (-10) 10),
                  metricDistance (G.flow.base.metric t) y z ≤ C / Real.sqrt (G.flow.scalar t x)) := by
  obtain ⟨Lmin, Lmax, hLmin, hLmax, hmain⟩ :=
    good_point_buffered_canonical ha haSmall htheta
  refine ⟨Lmin, Lmax, hLmin, hLmax, ?_⟩
  intro H hH
  obtain ⟨epsStar, C, heps, hepsAlpha, hC, hbody⟩ := hmain H hH
  refine ⟨epsStar, C, heps, hepsAlpha, hC, ?_⟩
  intro P a s G o x t hw
  have hreg : Ioo (t - (epsStar * G.flow.scalar t x)⁻¹) t ⊆
      (RealTimeInterval.closedOpen a s G.lt).regular := by
    simpa only [RealTimeInterval.closedOpen, interior_Icc, interior_Ico] using
      interior_mono hw.choose.window_mem
  exact hbody P.Carrier _ G.flow o x t G.equation hreg hw

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
