import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AscrFlowCompactness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AscrLimitGeometry
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TerminalNormalizedLine
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientSplitAvr
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedAsymptoticVolumeRatio
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientAscrAllTimes

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.BonnetMyers
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Tensor0SBundle
open CanonicalNeighborhood
open scoped Manifold ContDiff _root_.Topology ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

section Terminal

variable (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance ancientAvrTerminalTopology : TopologicalSpace F.M := F.topology
local instance ancientAvrTerminalCharted : ChartedSpace H F.M := F.charted
local instance ancientAvrTerminalSmooth : IsManifold I ∞ F.M := F.smooth
local instance ancientAvrTerminalT2 : T2Space F.M := F.t2
local instance ancientAvrTerminalSigma : SigmaCompactSpace F.M := F.sigmaCompact
local instance ancientAvrTerminalTangentT2 : T2Space (TangentBundle I F.M) :=
  F.t2TangentBundle

theorem ancientKappaThree_terminal_avr_eq_zero {kappa : ℝ}
    (hF : IsAncientKappaSolution (I := I) kappa F) (hdim : Module.finrank ℝ E = 3)
    (hnoncompact : NoncompactSpace F.M) (p : F.M) :
    asymptoticVolumeRatio (I := I) (F.S.base.metric 0) p = 0 := by
  let _ : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  let _ : ConnectedSpace F.M := hF.connected
  let hK : KLim kappa F := ancientKappaThree_toKLim F hF hdim
  have hcompleteSource : RiemannianMetricComplete (I := I) (F.S.base.metric 0) :=
    ⟨hF.complete 0 (by simp)⟩
  have hoperator (z : F.M) :
      metricAlgebraicCurvatureTensorAt (I := I) (F.S.base.metric 0) z ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := F.M) := by
    apply mem_algebraicCurvatureOperatorNonnegativeCone.mpr
    intro n c v w
    have h := hF.nonnegativeCurvatureOperator 0 (by simp) z n c v w
    simpa only [algebraicCurvatureOperatorQuadraticEval,
      metricAlgebraicCurvatureTensorAt, tensor04StandardAt, SolutionFamily.rm04,
      metricRm04_apply] using h
  have hRicSource : RicciBoundedBelow (I := I) (F.S.base.metric 0) 0 := by
    intro z v
    rw [zero_mul, ← metricRicciAt_apply_eq_ricciTensor]
    exact metricRicciAt_nonnegative_of_curvatureOperator_nonnegative
      (F.S.base.metric 0) z (hoperator z) v
  obtain ⟨x, r, eps, hQ, _hr, heps, _hanti, _hepsLimit, _hdisjoint,
      hescape, _hQr, _hratio, hexpand, hscaled, _hlarge, hlocal,
      _hterms, _hbase, _hRm, L, phi, hphi, Phi,
      hconnected, hcomplete, hconv⟩ :=
    ancientKappaThree_exists_ascr_ancient_limit F hF hdim hnoncompact p hfrontier
  have hlocal4 (i : ℕ) (z : F.M)
      (hz : (riemannianEDistOf (I := I) (F.S.base.metric 0) z (x i)).toReal < r i) :
      F.S.scalar 0 z ≤ 4 * F.S.scalar 0 (x i) := by
    exact (hlocal i z hz).trans (mul_le_mul_of_nonneg_right
      (by linarith [(heps i).2]) (hQ i).le)
  have hconvCanonical : ∀ t ≤ (0 : ℝ),
      ∃ C : MetricConvergenceData (I := I)
          (Phi.atTime (X := terminalCurvatureNormalizedFlowSeq F hK x hQ)
            (L := L) (phi := phi) t),
        ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData
          (I := I) (Phi.atTime (X := terminalCurvatureNormalizedFlowSeq F hK x hQ)
            (L := L) (phi := phi) t) k := by
    intro t ht
    obtain ⟨C, hcanonical, _hreference⟩ := hconv t ht
    exact ⟨C, hcanonical⟩
  have hlimit := terminalCurvatureNormalizedFlowSeq_ancient_limit_geometry
    F hF hK hdim x r hQ hlocal4 hexpand L phi hphi Phi
      hconnected hcomplete hconvCanonical
  let _ : TopologicalSpace L.M := L.topology
  let _ : ChartedSpace H L.M := L.charted
  let _ : IsManifold I ∞ L.M := L.smooth
  let _ : T2Space L.M := L.t2
  let _ : SigmaCompactSpace L.M := L.sigmaCompact
  obtain ⟨C, hcanonical, hreference⟩ := hconv 0 le_rfl
  obtain ⟨a, b, hplane, hnull⟩ :=
    exists_null_plane_of_terminalCurvatureNormalizedFlowSeq_limit
      F hK (by omega) p x hQ hescape hscaled hphi
        (Phi.atTime (X := terminalCurvatureNormalizedFlowSeq F hK x hQ)
          (L := L) (phi := phi) 0) C hcanonical hreference
        (hcomplete 0 le_rfl) hconnected L.basepoint
  have hnullFlow : L.S.base.rm04 0 L.basepoint (vec4 (I := I) a b b a) = 0 := by
    change metricRm04At (I := I) (L.S.base.metric 0) L.basepoint
      (vec4 (I := I) a b b a) = 0
    exact (metricRm04StandardAt_apply (I := I) (L.S.base.metric 0)
      L.basepoint a b b a).symm.trans hnull
  have hzero : asymptoticVolumeRatio (I := I) (L.S.base.metric 0) L.basepoint = 0 :=
    ancientKappa_null_plane_asymptoticVolumeRatio_eq_zero L hlimit.1 hdim
      0 le_rfl L.basepoint a b hplane hnullFlow 0 le_rfl L.basepoint
  let v := asymptoticVolumeRatio (I := I) (F.S.base.metric 0) p
  have hsource (i : ℕ) : v ≤
      @asymptoticVolumeRatio E _ _ _ H _ I F.M F.topology F.charted F.smooth
        F.t2 F.sigmaCompact
      (((terminalCurvatureNormalizedFlowSeq F hK x hQ).atZero (I := I)).obj i).metric
        (x i) := by
    rw [terminalCurvatureNormalizedFlowSeq_metric, asymptoticVolumeRatio_scaleMetric]
    exact (asymptoticVolumeRatio_basepoint_eq (F.S.base.metric 0)
      hcompleteSource hRicSource p (x i)).le
  have hlower := asymptoticVolumeRatio_lower_of_pointed_metric_convergence
    C hreference (hcomplete 0 le_rfl) v hsource
  change v ≤ asymptoticVolumeRatio (I := I) (L.S.base.metric 0) L.basepoint at hlower
  rw [hzero] at hlower
  exact le_antisymm hlower bot_le

end Terminal

section AllTimes

variable {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)

local instance ancientAvrAllTimesTopology : TopologicalSpace F.M := F.topology
local instance ancientAvrAllTimesCharted : ChartedSpace H F.M := F.charted
local instance ancientAvrAllTimesSmooth : IsManifold I ∞ F.M := F.smooth
local instance ancientAvrAllTimesC1 : IsManifold I 1 F.M :=
  IsManifold.of_le (n := ∞) (by decide)
local instance ancientAvrAllTimesT2 : T2Space F.M := F.t2
local instance ancientAvrAllTimesSigma : SigmaCompactSpace F.M := F.sigmaCompact

theorem ancientKappaThree_avr_eq_zero {kappa : ℝ}
    (hF : IsAncientKappaSolution (I := I) kappa F) (hdim : Module.finrank ℝ E = 3)
    (hnoncompact : NoncompactSpace F.M) (t0 : ℝ) (ht0 : t0 ∈ D.carrier) (p : F.M)
    (hfrontier : NoncompactShrinkerCylinderClassificationTheorem.{uE, uH, u}) :
    asymptoticVolumeRatio (I := I) (F.S.base.metric t0) p = 0 := by
  have ht0le : t0 ≤ 0 := by
    simpa only [hF.carrier_eq, Set.mem_Iic] using ht0
  obtain ⟨hQ, hdata⟩ :=
    ancientKappa_exists_curvatureNormalization_ascr F hdim hF t0 ht0le p
  let G := curvatureNormalizedFlow F hF.carrier_eq hF.regular_eq
    t0 (F.S.scalar t0 p) hQ ht0 p
  have hG : IsAncientKappaSolution (I := I) kappa G := hdata.1
  have hnoncompactG : @NoncompactSpace G.M G.topology := by
    change @NoncompactSpace F.M F.topology
    exact hnoncompact
  have havr :
      @asymptoticVolumeRatio E _ _ _ H _ I F.M F.topology F.charted F.smooth
        F.t2 F.sigmaCompact (G.S.base.metric 0) p =
      asymptoticVolumeRatio (F.S.base.metric t0) p := by
    change asymptoticVolumeRatio (I := I) (M := F.M)
      (scaleMetric (F.S.scalar t0 p) hQ
        (F.S.base.metric (parabolicTime t0 (F.S.scalar t0 p) 0))) p = _
    rw [parabolicTime_zero, asymptoticVolumeRatio_scaleMetric]
  exact havr.symm.trans
    (ancientKappaThree_terminal_avr_eq_zero G hG hdim hnoncompactG p)

theorem ancientKappaThree_ascr_eq_top_and_avr_eq_zero {kappa : ℝ}
    (hF : IsAncientKappaSolution (I := I) kappa F) (hdim : Module.finrank ℝ E = 3)
    (hnoncompact : NoncompactSpace F.M) (t0 : ℝ) (ht0 : t0 ∈ D.carrier) (p : F.M)
    (hfrontier : NoncompactShrinkerCylinderClassificationTheorem.{uE, uH, u}) :
    asymptoticScalarCurvatureRatio (I := I) (F.S.base.metric t0) p = ⊤ ∧
      asymptoticVolumeRatio (I := I) (F.S.base.metric t0) p = 0 :=
  ⟨ancientKappaThree_ascr_eq_top F hF hdim hnoncompact t0 ht0 p hfrontier,
    ancientKappaThree_avr_eq_zero F hF hdim hnoncompact t0 ht0 p hfrontier⟩

end AllTimes

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
