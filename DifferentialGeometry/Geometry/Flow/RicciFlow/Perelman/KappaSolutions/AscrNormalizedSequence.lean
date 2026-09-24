import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientAscrInfinite
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AscrPointSelection
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.HarnackPointSelection

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Tensor0SBundle
open CanonicalNeighborhood
open scoped _root_.Manifold ContDiff _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance ascrNormalizedTopology : TopologicalSpace F.M := F.topology
local instance ascrNormalizedCharted : ChartedSpace H F.M := F.charted
local instance ascrNormalizedSmooth : IsManifold I ∞ F.M := F.smooth
local instance ascrNormalizedT2 : T2Space F.M := F.t2
local instance ascrNormalizedSigma : SigmaCompactSpace F.M := F.sigmaCompact

theorem ancientKappaThree_exists_ascr_normalized_sequence {kappa : ℝ}
    (hF : IsAncientKappaSolution kappa F) (hdim : Module.finrank ℝ E = 3)
    (hnoncompact : NoncompactSpace F.M) (p : F.M) :
    let hK := ancientKappaThree_toKLim F hF hdim
    let d := fun y z : F.M =>
      (riemannianEDistOf (I := I) (F.S.base.metric 0) y z).toReal
    ∃ (x : ℕ → F.M) (r eps : ℕ → ℝ) (hQ : ∀ i, 0 < F.S.scalar 0 (x i)),
      (∀ i, 0 < r i ∧ r i ≤ d p (x i) / 6) ∧
      (∀ i, 0 < eps i ∧ eps i < 1) ∧ StrictAnti eps ∧
      Tendsto eps atTop (𝓝 0) ∧
      Pairwise (fun i j =>
        Disjoint
          {z : F.M | riemannianEDistOf (I := I) (F.S.base.metric 0) z (x i) <
            ENNReal.ofReal (r i)}
          {z : F.M | riemannianEDistOf (I := I) (F.S.base.metric 0) z (x j) <
            ENNReal.ofReal (r j)}) ∧
      Tendsto (fun i => d p (x i)) atTop atTop ∧
      Tendsto (fun i => F.S.scalar 0 (x i) * r i ^ 2) atTop atTop ∧
      Tendsto (fun i => d p (x i) / r i) atTop atTop ∧
      Tendsto (fun i => r i * Real.sqrt (F.S.scalar 0 (x i))) atTop atTop ∧
      Tendsto (fun i => Real.sqrt (F.S.scalar 0 (x i)) * d p (x i)) atTop atTop ∧
      (∀ i z, d z (x i) < r i →
        F.S.scalar 0 z ≤ (1 + eps i) * F.S.scalar 0 (x i)) ∧
      let Y := terminalCurvatureNormalizedFlowSeq F hK x hQ
      (∀ i, IsAncientKappaSolution (I := I) kappa (Y.term i)) ∧
      FlowMetricComplete (I := I) Y ∧
      (∀ i, @ConnectedSpace (Y.term i).M (Y.term i).topology) ∧
      (∀ i, PointedFlowNoncollapsedAllScales (I := I) (Y.term i) kappa) ∧
      (∀ i s, s ≤ 0 → PointedFlowNonnegativeCurvatureOperator (I := I) (Y.term i) s) ∧
      (∀ i, PointedFlowScalarAtBase (I := I) (Y.term i) 1) ∧
      (∀ i s, s ≤ 0 → ∀ z : F.M,
        (@riemannianEDistOf E _ _ H _ I F.M F.topology F.charted F.smooth
          ((Y.atZero (I := I)).obj i).metric z (x i)).toReal <
            r i * Real.sqrt (F.S.scalar 0 (x i)) →
        0 ≤ (Y.term i).S.scalar s z ∧ (Y.term i).S.scalar s z ≤ 4) ∧
      (∀ A : ℝ, ∀ᶠ i in atTop, ∀ s ≤ 0, ∀ z : F.M,
        (@riemannianEDistOf E _ _ H _ I F.M F.topology F.charted F.smooth
          ((Y.atZero (I := I)).obj i).metric z (x i)).toReal ≤ A →
        0 ≤ (Y.term i).S.scalar s z ∧ (Y.term i).S.scalar s z ≤ 4) := by
  let hK : KLim kappa F := ancientKappaThree_toKLim F hF hdim
  let _ : ConnectedSpace F.M := hF.connected
  have hcomplete : RiemannianMetricComplete (I := I) (F.S.base.metric 0) :=
    ⟨hF.complete 0 (by simp)⟩
  have hASCR := ancientKappaThree_terminal_ascr_eq_top F hF hdim hnoncompact p
  obtain ⟨x, r, eps, hr, heps, hanti, hepsLimit, hdisjoint, hescape, hQr, hratio, hcontrol⟩ :=
    exists_scalarAscrPointSelection (I := I) (F.S.base.metric 0) hcomplete p hASCR
  obtain ⟨N, hN⟩ := ((tendsto_order.1 hepsLimit).2 1 zero_lt_one).exists_forall_of_atTop
  let shift : ℕ → ℕ := fun i => N + i
  have hshift : StrictMono shift := by
    intro i j hij
    exact Nat.add_lt_add_left hij N
  let x' : ℕ → F.M := x ∘ shift
  let r' : ℕ → ℝ := r ∘ shift
  let eps' : ℕ → ℝ := eps ∘ shift
  let hQ : ∀ i, 0 < F.S.scalar 0 (x' i) := fun i => (hr (shift i)).2.2
  have hr' (i : ℕ) : 0 < r' i ∧
      r' i ≤ (riemannianEDistOf (I := I) (F.S.base.metric 0) p (x' i)).toReal / 6 :=
    ⟨(hr (shift i)).1, (hr (shift i)).2.1⟩
  have heps' (i : ℕ) : 0 < eps' i ∧ eps' i < 1 := by
    refine ⟨heps (shift i), hN (shift i) ?_⟩
    exact Nat.le_add_right N i
  have hQr' : Tendsto (fun i => F.S.scalar 0 (x' i) * r' i ^ 2) atTop atTop :=
    hQr.comp hshift.tendsto_atTop
  have hexpand : Tendsto (fun i => r' i * Real.sqrt (F.S.scalar 0 (x' i)))
      atTop atTop := by
    have hsqrt : Tendsto (fun i => Real.sqrt (F.S.scalar 0 (x' i) * r' i ^ 2))
        atTop atTop := Real.tendsto_sqrt_atTop.comp hQr'
    have heq : (fun i => Real.sqrt (F.S.scalar 0 (x' i) * r' i ^ 2)) =
        (fun i => r' i * Real.sqrt (F.S.scalar 0 (x' i))) := by
      funext i
      rw [Real.sqrt_mul (hQ i).le, Real.sqrt_sq (hr' i).1.le, mul_comm]
    rw [heq] at hsqrt
    exact hsqrt
  have hscaledEscape : Tendsto (fun i => Real.sqrt (F.S.scalar 0 (x' i)) *
      (riemannianEDistOf (I := I) (F.S.base.metric 0) p (x' i)).toReal)
      atTop atTop := by
    apply tendsto_atTop_mono (f := fun i => r' i * Real.sqrt (F.S.scalar 0 (x' i)))
      ?_ hexpand
    intro i
    have hrd : r' i ≤
        (riemannianEDistOf (I := I) (F.S.base.metric 0) p (x' i)).toReal := by
      have hp := (hr' i).1
      have hb := (hr' i).2
      linarith
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_right hrd (Real.sqrt_nonneg (F.S.scalar 0 (x' i)))
  have hlocal (i : ℕ) (z : F.M)
      (hz : (riemannianEDistOf (I := I) (F.S.base.metric 0) z (x' i)).toReal < r' i) :
      F.S.scalar 0 z ≤ (1 + eps' i) * F.S.scalar 0 (x' i) :=
    hcontrol (shift i) z hz
  have hlocal4 (i : ℕ) (z : F.M)
      (hz : (riemannianEDistOf (I := I) (F.S.base.metric 0) z (x' i)).toReal < r' i) :
      F.S.scalar 0 z ≤ 4 * F.S.scalar 0 (x' i) := by
    exact (hlocal i z hz).trans (mul_le_mul_of_nonneg_right
      (by linarith [(heps' i).2]) (hQ i).le)
  have hbackward : ∀ i s, s ≤ 0 → ∀ z : F.M,
      (@riemannianEDistOf E _ _ H _ I F.M F.topology F.charted F.smooth
        (((terminalCurvatureNormalizedFlowSeq F hK x' hQ).atZero (I := I)).obj i).metric
        z (x' i)).toReal < r' i * Real.sqrt (F.S.scalar 0 (x' i)) →
      0 ≤ ((terminalCurvatureNormalizedFlowSeq F hK x' hQ).term i).S.scalar s z ∧
        ((terminalCurvatureNormalizedFlowSeq F hK x' hQ).term i).S.scalar s z ≤ 4 := by
    intro i s hs z hz
    exact terminalCurvatureNormalizedFlowSeq_scalar_bound F hK x' hQ i (r' i)
      (hlocal4 i) hs z hz
  refine ⟨x', r', eps', hQ, hr', heps', hanti.comp_strictMono hshift,
    hepsLimit.comp hshift.tendsto_atTop, ?_, hescape.comp hshift.tendsto_atTop,
    hQr', hratio.comp hshift.tendsto_atTop, hexpand, hscaledEscape, hlocal, ?_⟩
  · intro i j hij
    exact hdisjoint (fun h => hij (hshift.injective h))
  · refine ⟨?_, terminalCurvatureNormalizedFlowSeq_complete F hK x' hQ,
      terminalCurvatureNormalizedFlowSeq_connected F hK x' hQ,
      terminalCurvatureNormalizedFlowSeq_noncollapsed F hK x' hQ,
      (fun i s hs =>
        terminalCurvatureNormalizedFlowSeq_nonnegativeCurvatureOperator F hK x' hQ i hs),
      terminalCurvatureNormalizedFlowSeq_scalar_base F hK x' hQ, hbackward, ?_⟩
    · intro i
      exact isAncientKappaSolution_curvatureNormalizedFlow F hF
        0 (F.S.scalar 0 (x' i)) (hQ i) (by simp) (x' i) rfl
    · intro A
      filter_upwards [hexpand (eventually_gt_atTop A)] with i hi
      intro s hs z hz
      exact hbackward i s hs z (hz.trans_lt hi)

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
