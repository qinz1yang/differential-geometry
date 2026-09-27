import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SelectedCountersequenceAdapter
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.RecenteredSourceInputs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Foundations.WindowRestriction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Foundations.ParabolicRescaling

noncomputable section
open Filter Set
open scoped Topology Manifold ContDiff ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle



private abbrev normalizedTerminalCurvatureRescale
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ} (X : FlowSequence.{u})
    (depth scale : ℕ → ℝ) (hdepth : ∀ i, 0 < depth i) (hscale : ∀ i, 0 < scale i)
    (hcarrier : ∀ i, (X.interval i).carrier = Icc (-(2 * depth i)) 0)
    (hregular : ∀ i, (X.interval i).regular = Ioo (-(2 * depth i)) 0)
    (hconnected : ∀ i, ConnectedSpace (X.term i).M)
    (orientation : ∀ i, TangentOrientationSection (X.term i).M)
    (hcomplete : ∀ i t, t ∈ (X.interval i).carrier → MetricComplete ((X.term i).atTime t))
    (hsource : ∀ i, ∃ C : ℝ, PointedFlowRmNormSqBounded (X.term i) C)
    (hnoncollapse : ∀ i, ParabolicallyKappaNoncollapsedBelowScale (X.term i).S
      (modelNoncollapseFactor * kappa) (Real.sqrt (scale i) * sigma))
    (hpinching : ∀ i, PhiAlmostNonnegative (X.term i).S (X.interval i).carrier
      (rescalePinchingFunction (scale i) Phi))
    (hgood : ∀ i t, t ∈ Icc (-depth i) 0 → ∀ x,
      2 ≤ (X.term i).S.scalar t x → OrientedWitness (X.term i).S (orientation i) eps kappa x t)
    (x : ∀ i, (X.term i).M) (hQ : ∀ i, 1 ≤ (X.term i).S.scalar 0 (x i))
    (hbuffer : ∀ i, modelDepth eps ≤ (X.term i).S.scalar 0 (x i) * depth i)
    (hdepthlim : Tendsto (fun i => (X.term i).S.scalar 0 (x i) * depth i) atTop atTop)
    (hscalelim : Tendsto (fun i => (X.term i).S.scalar 0 (x i) * scale i) atTop atTop) :
    NormalizedSequence.{u} eps kappa sigma Phi := by
  have hzero (i) : (0 : ℝ) ∈ (X.interval i).carrier := by
    rw [hcarrier]
    exact ⟨by linarith [hdepth i], le_rfl⟩
  exact {
  toFlowSequence := X.terminalCurvatureRescale x
    (fun i => lt_of_lt_of_le zero_lt_one (hQ i)) hzero
  depth i := (X.term i).S.scalar 0 (x i) * depth i
  scale i := (X.term i).S.scalar 0 (x i) * scale i
  depth_pos i := mul_pos (lt_of_lt_of_le zero_lt_one (hQ i)) (hdepth i)
  depth_buffer := hbuffer
  scale_pos i := mul_pos (lt_of_lt_of_le zero_lt_one (hQ i)) (hscale i)
  depth_tendsto := hdepthlim
  scale_tendsto := hscalelim
  carrier_eq i := by
    ext s
    simp only [FlowSequence.terminalCurvatureRescale, parabolicInterval_carrier, mem_ofPred_eq, hcarrier, mem_Icc,
      parabolicTime, zero_add]
    have hp := lt_of_lt_of_le zero_lt_one (hQ i)
    rw [le_div_iff₀ hp, div_le_iff₀ hp]
    ring_nf
  regular_eq i := by
    ext s
    simp only [FlowSequence.terminalCurvatureRescale, parabolicInterval_regular, mem_ofPred_eq, hregular, mem_Ioo,
      parabolicTime, zero_add]
    have hp := lt_of_lt_of_le zero_lt_one (hQ i)
    rw [lt_div_iff₀ hp, div_lt_iff₀ hp]
    ring_nf
  connected i := hconnected i
  orientation i := orientation i
  complete i s hs := by
    have hc : RiemannianMetricComplete ((X.term i).S.base.metric
        (parabolicTime 0 ((X.term i).S.scalar 0 (x i)) s)) := ⟨hcomplete i _ hs⟩
    exact (hc.of_lower (lt_of_lt_of_le zero_lt_one (hQ i)) (fun _ _ => le_rfl)).complete
  source_bound i := by
    obtain ⟨C, hC⟩ := hsource i
    refine ⟨((X.term i).S.scalar 0 (x i))⁻¹ ^ 2 * C, fun s hs y => ?_⟩
    exact (parabolicRmNormSq (X.term i).S 0 ((X.term i).S.scalar 0 (x i))
      (lt_of_lt_of_le zero_lt_one (hQ i)) (hzero i) s y).le.trans
      (mul_le_mul_of_nonneg_left (hC _ hs y) (sq_nonneg _))
  base_one i := by
    change (parabolicSolution (X.term i).S 0 ((X.term i).S.scalar 0 (x i))
      (lt_of_lt_of_le zero_lt_one (hQ i)) (hzero i)).scalar 0 (x i) = 1
    simp only [parabolicSolution_scalar, parabolicTime_zero,
      inv_mul_cancel₀ (ne_of_gt (lt_of_lt_of_le zero_lt_one (hQ i)))]
  noncollapse i := by
    rw [← recentered_noncollapse_scale (lt_of_lt_of_le zero_lt_one (hQ i)).le]
    exact parabolicallyKappaNoncollapsedBelowScale_parabolicSolution (X.term i).S 0
      ((X.term i).S.scalar 0 (x i)) (lt_of_lt_of_le zero_lt_one (hQ i)) (hzero i) _
      (Real.sqrt (scale i) * sigma) (hnoncollapse i)
  pinching i := by
    rw [← rescalePinchingFunction_rescale]
    exact phiAlmostNonnegative_paraSolution (X.term i).S
      (lt_of_lt_of_le zero_lt_one (hQ i)) (hzero i) (hpinching i)
  higher_good i s hs y hy := by
    have hp := lt_of_lt_of_le zero_lt_one (hQ i)
    apply (orientedWitness_paraSolution_iff (X.term i).S (orientation i)
      hp (hzero i) s y eps kappa).mpr
    apply hgood i
    · change -depth i ≤ 0 + s / _ ∧ 0 + s / _ ≤ 0
      simp only [zero_add]
      rw [le_div_iff₀ hp, div_le_iff₀ hp]
      constructor <;> nlinarith [hs.1, hs.2]
    · change 2 ≤ (parabolicSolution (X.term i).S 0 ((X.term i).S.scalar 0 (x i))
        hp (hzero i)).scalar s y at hy
      simp only [parabolicSolution_scalar] at hy
      rw [← div_eq_inv_mul, le_div_iff₀ hp] at hy
      exact (by linarith [hQ i] : 2 ≤ 2 * (X.term i).S.scalar 0 (x i)).trans hy
 }

theorem FlowSequence.exists_normalized_terminalCurvatureRescale_of_pos_lower_bounds
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ} (X : FlowSequence.{u})
    (depth scale : ℕ → ℝ) {H0 S0 : ℝ} (hH0 : 0 < H0) (hS0 : 0 < S0)
    (hdepth : ∀ i, H0 ≤ depth i) (hscale : ∀ i, S0 ≤ scale i)
    (hcarrier : ∀ i, (X.interval i).carrier = Icc (-(2 * depth i)) 0)
    (hregular : ∀ i, (X.interval i).regular = Ioo (-(2 * depth i)) 0)
    (hconnected : ∀ i, ConnectedSpace (X.term i).M)
    (orientation : ∀ i, TangentOrientationSection (X.term i).M)
    (hcomplete : ∀ i t, t ∈ (X.interval i).carrier → MetricComplete ((X.term i).atTime t))
    (hsource : ∀ i, ∃ C : ℝ, PointedFlowRmNormSqBounded (X.term i) C)
    (hnoncollapse : ∀ i, ParabolicallyKappaNoncollapsedBelowScale (X.term i).S
      (modelNoncollapseFactor * kappa) (Real.sqrt (scale i) * sigma))
    (hpinching : ∀ i, PhiAlmostNonnegative (X.term i).S (X.interval i).carrier
      (rescalePinchingFunction (scale i) Phi))
    (hgood : ∀ i t, t ∈ Icc (-depth i) 0 → ∀ x,
      2 ≤ (X.term i).S.scalar t x → OrientedWitness (X.term i).S (orientation i) eps kappa x t)
    (x : ∀ i, (X.term i).M)
    (hQ : Tendsto (fun i => (X.term i).S.scalar 0 (x i)) atTop atTop) :
    ∃ k : ℕ → ℕ, StrictMono k ∧
      ∃ (hpos : ∀ i, 0 < (X.term (k i)).S.scalar 0 (x (k i)))
        (hzero : ∀ i, (0 : ℝ) ∈ (X.interval (k i)).carrier),
      ∃ Y : NormalizedSequence.{u} eps kappa sigma Phi,
        Y.toFlowSequence = (X.reindex k).terminalCurvatureRescale (fun i => x (k i)) hpos hzero ∧
        (∀ i, Y.depth i = (X.term (k i)).S.scalar 0 (x (k i)) * depth (k i)) ∧
        (∀ i, Y.scale i = (X.term (k i)).S.scalar 0 (x (k i)) * scale (k i)) := by
  have hlarge : ∀ᶠ i in atTop, 1 ≤ (X.term i).S.scalar 0 (x i) ∧
      modelDepth eps ≤ (X.term i).S.scalar 0 (x i) * depth i := by
    filter_upwards [hQ.eventually_ge_atTop 1,
      (hQ.atTop_mul_const hH0).eventually_ge_atTop (modelDepth eps)] with i hi hd
    exact ⟨hi, hd.trans (mul_le_mul_of_nonneg_left (hdepth i) (zero_lt_one.trans_le hi).le)⟩
  obtain ⟨N, hN⟩ := eventually_atTop.mp hlarge
  let k : ℕ → ℕ := fun i => i + N
  have hk : StrictMono k := fun _ _ hij => Nat.add_lt_add_right hij N
  have hkN (i) : N ≤ k i := Nat.le_add_left N i
  have hQ1 (i) : 1 ≤ (X.term (k i)).S.scalar 0 (x (k i)) := (hN (k i) (hkN i)).1
  have hpos (i) : 0 < (X.term (k i)).S.scalar 0 (x (k i)) := zero_lt_one.trans_le (hQ1 i)
  have hzero (i) : (0 : ℝ) ∈ (X.interval (k i)).carrier := by
    rw [hcarrier]
    exact ⟨by linarith [hdepth (k i)], le_rfl⟩
  have hdepthlim : Tendsto (fun i => (X.term (k i)).S.scalar 0 (x (k i)) * depth (k i))
      atTop atTop := by
    apply tendsto_atTop_mono _ ((hQ.comp hk.tendsto_atTop).atTop_mul_const hH0)
    intro i
    exact mul_le_mul_of_nonneg_left (hdepth (k i)) (hpos i).le
  have hscalelim : Tendsto (fun i => (X.term (k i)).S.scalar 0 (x (k i)) * scale (k i))
      atTop atTop := by
    apply tendsto_atTop_mono _ ((hQ.comp hk.tendsto_atTop).atTop_mul_const hS0)
    intro i
    exact mul_le_mul_of_nonneg_left (hscale (k i)) (hpos i).le
  let Y := normalizedTerminalCurvatureRescale (X.reindex k)
    (depth ∘ k) (scale ∘ k) (fun i => hH0.trans_le (hdepth (k i)))
    (fun i => hS0.trans_le (hscale (k i))) (fun i => hcarrier (k i))
    (fun i => hregular (k i)) (fun i => hconnected (k i)) (fun i => orientation (k i))
    (fun i => hcomplete (k i)) (fun i => hsource (k i)) (fun i => hnoncollapse (k i))
    (fun i => hpinching (k i)) (fun i => hgood (k i)) (fun i => x (k i)) hQ1
    (fun i => (hN (k i) (hkN i)).2) hdepthlim hscalelim
  exact ⟨k, hk, hpos, hzero, Y, rfl, fun _ => rfl, fun _ => rfl⟩

namespace NormalizedSequence
variable {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}

def terminalCurvatureRescale (X : NormalizedSequence.{u} eps kappa sigma Phi)
    (x : ∀ i, (X.term i).M) (hQ : ∀ i, 1 ≤ (X.term i).S.scalar 0 (x i)) :
    NormalizedSequence.{u} eps kappa sigma Phi :=
  normalizedTerminalCurvatureRescale X.toFlowSequence X.depth X.scale X.depth_pos X.scale_pos
    X.carrier_eq X.regular_eq X.connected X.orientation X.complete X.source_bound
    X.noncollapse X.pinching X.higher_good x hQ
    (fun i => (X.depth_buffer i).trans (le_mul_of_one_le_left (X.depth_pos i).le (hQ i)))
    (tendsto_atTop_mono (fun i => le_mul_of_one_le_left (X.depth_pos i).le (hQ i)) X.depth_tendsto)
    (tendsto_atTop_mono (fun i => le_mul_of_one_le_left (X.scale_pos i).le (hQ i)) X.scale_tendsto)

@[simp] theorem terminalCurvatureRescale_toFlowSequence
    (X : NormalizedSequence.{u} eps kappa sigma Phi)
    (x : ∀ i, (X.term i).M) (hQ : ∀ i, 1 ≤ (X.term i).S.scalar 0 (x i)) :
    (X.terminalCurvatureRescale x hQ).toFlowSequence =
      X.toFlowSequence.terminalCurvatureRescale x
        (fun i => zero_lt_one.trans_le (hQ i))
        (fun i => by rw [X.carrier_eq]; exact ⟨by linarith [X.depth_pos i], le_rfl⟩) := rfl

end NormalizedSequence
end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
