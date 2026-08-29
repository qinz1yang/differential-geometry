import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.ChartTimeH1
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.KineticChart
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ScalarCompact
import DifferentialGeometry.Topology.CurveChartCover

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle MeasureTheory Set
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Geometry.Curvature

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [UniformSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
variable {D : RealTimeInterval}

theorem lRegLag_int_c1
    (S : SolutionOn (I := I) (M := M) D)
    (hMet : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    (hSc : ScalarSTContOn (I := I) (M := M) S)
    (T a b : Real) (hab : a ≤ b) (alpha : Real → M)
    (halpha : ContMDiffOn (modelWithCornersSelf Real Real) I 1 alpha (Icc a b))
    (hreg : ∀ s ∈ Icc a b, T - s ^ 2 ∈ D.regular) :
    IntervalIntegrable (lRegLag S T alpha) volume a b := by
  classical
  obtain ⟨t, ht0, htmono, ⟨m, hm⟩, hchart⟩ :=
    DifferentialGeometry.Geometry.exists_chart_split (H := H) hab halpha.continuousOn
  have hseg (n : Nat) : (t n : Real) ≤ t (n + 1) :=
    htmono (Nat.le_succ n)
  have hkinPiece (n : Nat) : IntervalIntegrable
      (fun s ↦ (1 / 2 : Real) *
        (S.base.metric (T - s ^ 2)).inner (alpha s)
          (lVelocity (I := I) alpha s) (lVelocity (I := I) alpha s))
      volume (t n) (t (n + 1)) := by
    obtain ⟨p, hsrc⟩ := hchart n
    have hshift : MapsTo (fun r : Real ↦ (t n : Real) + r)
        (Icc (0 : Real) ((t (n + 1) : Real) - t n)) (Icc a b) := by
      intro r hr
      exact ⟨by linarith [(t n).property.1, hr.1],
        by linarith [hr.2, (t (n + 1)).property.2]⟩
    have hshiftPiece : MapsTo (fun r : Real ↦ (t n : Real) + r)
        (Icc (0 : Real) ((t (n + 1) : Real) - t n))
        (Icc (t n : Real) (t (n + 1) : Real)) := by
      intro r hr
      exact ⟨by linarith [hr.1], by linarith [hr.2]⟩
    have hlocalMD : ContMDiffOn (modelWithCornersSelf Real Real) I 1
        (fun r : Real ↦ alpha ((t n : Real) + r))
        (Icc (0 : Real) ((t (n + 1) : Real) - t n)) :=
      halpha.comp (contMDiff_const.add contMDiff_id).contMDiffOn hshift
    have hlocalSrc : MapsTo (fun r : Real ↦ alpha ((t n : Real) + r))
        (Icc (0 : Real) ((t (n + 1) : Real) - t n))
        (chartAt H p).source :=
      hsrc.comp hshiftPiece
    let us : timeH1 E ((t (n + 1) : Real) - t n) :=
      chartTimeH1 I (sub_nonneg.mpr (hseg n)) p
        (fun r : Real ↦ alpha ((t n : Real) + r)) hlocalMD hlocalSrc
    have hrep : EqOn us.toFun
        (fun r ↦ extChartAt I p (alpha ((t n : Real) + r)))
        (Icc (0 : Real) ((t (n + 1) : Real) - t n)) := by
      with_unfolding_all
        exact chartTimeH1_toFun I (sub_nonneg.mpr (hseg n)) p
          (fun r : Real ↦ alpha ((t n : Real) + r)) hlocalMD hlocalSrc
    have hdiff : ∀ᵐ r ∂timeMeasure ((t (n + 1) : Real) - t n),
        MDifferentiableAt (modelWithCornersSelf Real Real) I alpha ((t n : Real) + r) :=
      curve_mdiff_local I p alpha us (hseg n) hsrc hrep
    exact lKinetic_int_local S hMet T alpha p (t n) (t (n + 1))
      (hseg n) us hsrc hrep hdiff fun s hs ↦
        hreg s ⟨(t n).property.1.trans hs.1,
          hs.2.trans (t (n + 1)).property.2⟩
  have hkin : IntervalIntegrable
      (fun s ↦ (1 / 2 : Real) *
        (S.base.metric (T - s ^ 2)).inner (alpha s)
          (lVelocity (I := I) alpha s) (lVelocity (I := I) alpha s))
      volume a b := by
    have ht0' : (t 0 : Real) = a := by
      simpa only using congrArg Subtype.val ht0
    have htm' : (t m : Real) = b := by
      simpa only using congrArg Subtype.val (hm m le_rfl)
    have hchain := IntervalIntegrable.trans_iterate
      (n := m) fun k _hk ↦ hkinPiece k
    simpa only [ht0', htm'] using hchain
  have hcarrier : ∀ s ∈ uIcc a b, T - s ^ 2 ∈ D.carrier := by
    intro s hs
    exact D.regular_subset (hreg s (by simpa only [uIcc_of_le hab] using hs))
  have hpot : IntervalIntegrable
      (fun s ↦ 2 * s ^ 2 * S.scalar (T - s ^ 2) (alpha s))
      volume a b :=
    lScalar_int (I := I) S hSc T a b alpha hcarrier (by
      simpa only [uIcc_of_le hab] using halpha.continuousOn)
  with_unfolding_all exact hkin.add hpot

end DifferentialGeometry.PDE.RicciFlow.Perelman
