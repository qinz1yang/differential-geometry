import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ParabolicComparisonStability
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.LocalNeckTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WitnessTimeRegularity

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {P : Type u} [TopologicalSpace P] [ChartedSpace ThreeSpace P]
  [IsManifold I3 ∞ P] [T2Space P] [SigmaCompactSpace P]

private local instance neckScaleStabilityC1 : IsManifold I3 1 P :=
  IsManifold.of_le (n := ∞) (by decide)

theorem StrongNeck.exists_rescaled_transport_tolerances_of_ancient
    {Sm : SolutionOn (I := I3) (M := P) ancientTimeInterval} (hSm : IsSolutionOn Sm)
    {alpha : ℝ} {p : P} (nk : StrongNeck Sm (neckModelTolerance alpha) p 0)
    (ha : 0 < alpha) (hsmall : 2 * alpha < 1 / 11)
    (U : TopologicalSpace.Opens P) (hUcompact : IsCompact (closure (U : Set P)))
    {K : Set P} (hK : IsCompact K) (hKU : K ⊆ U)
    (houter : ∀ y ∈ univ ×ˢ Ioo (-alpha⁻¹) alpha⁻¹, nk.map y ∈ K) :
    ∃ eta beta : ℝ, 0 < eta ∧ 0 < beta ∧
      ∀ c : ℝ, ∀ hc : 0 < c, |c - Sm.scalar 0 p| < eta →
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M],
      ∀ {D : RealTimeInterval} (S : SolutionOn (I := I3) (M := M) D), IsSolutionOn S →
      ∀ {x : M} {t : ℝ} (hQ : 0 < S.scalar t x) {b : ℝ}, b < -1 →
      MapsTo (parabolicTime t (S.scalar t x)) (Icc b 0) D.carrier →
      MapsTo (parabolicTime t (S.scalar t x)) (Ioo b 0) D.regular →
      ∀ F : PartialDiffeomorph I3 I3 P M ∞, (U : Set P) ⊆ F.source → F p = x →
      MetricComparisonOn (rescaledMetric Sm 0 c hc) (rescaledMetric S t (S.scalar t x) hQ)
        F U (Icc (-1 : ℝ) 0) ⌈(2 * alpha)⁻¹⌉₊ beta →
      ∃ nk' : StrongNeck S (2 * alpha) x t,
        nk'.map = partialDiffeomorphTransMixed nk.map F := by
  have htarget : 0 < neckSourceTolerance alpha := neckSourceTolerance_pos ha
  obtain ⟨eta, beta, heta, hbeta, htransfer⟩ :=
    exists_rescaledMetric_comparison_tolerance_on_compact Sm hSm
      (a := -(Sm.scalar 0 p)⁻¹ - 1) (t := 0) (depth := 1) (Q := Sm.scalar 0 p)
      zero_lt_one nk.Q_pos (by simp only [zero_sub, one_div]; linarith)
      (fun _ hs => hs.2) (fun _ hs => hs.2) U hUcompact hK hKU
      ⌈(2 * alpha)⁻¹⌉₊ htarget
  refine ⟨eta, beta, heta, hbeta, ?_⟩
  intro c hc hnear M _ _ _ _ _ D S hS x t hQ b hb hdomain hregular F hF hbase C
  have ht : t ∈ D.carrier := by
    have hh := hdomain (show (0 : ℝ) ∈ Icc b 0 from ⟨by linarith, le_rfl⟩)
    simpa only [parabolicTime_zero] using hh
  let T := parabolicSolution S t (S.scalar t x) hQ ht
  have hT : IsSolutionOn T := parabolicSolution_isSolutionOn S hS t (S.scalar t x) hQ ht
  obtain ⟨cmp⟩ := htransfer c hc hnear M T hT hb hdomain hregular F hF C
  have htime : Icc (t - (S.scalar t x)⁻¹) t ⊆ D.carrier := by
    intro r hr
    let s := (r - t) * S.scalar t x
    have hs : s ∈ Icc b 0 := by
      have hlo := mul_le_mul_of_nonneg_right hr.1 hQ.le
      have hi : (S.scalar t x)⁻¹ * S.scalar t x = 1 := inv_mul_cancel₀ hQ.ne'
      dsimp only [s]
      constructor
      · nlinarith
      · exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hr.2) hQ.le
    have hh := hdomain hs
    have heq : parabolicTime t (S.scalar t x) s = r := by
      dsimp only [parabolicTime, s]
      rw [mul_div_cancel_right₀ _ hQ.ne']
      ring
    rwa [heq] at hh
  apply nk.exists_transport_of_local_comparisons hQ F cmp ha hsmall htarget.le le_rfl
    le_rfl hbase houter (hKU.trans hF) htime
  · intro q s hs z hz v
    obtain ⟨y, hy, rfl⟩ := hz
    have hzero : (0 : ℝ) ∈ ancientTimeInterval.carrier := by
      change (0 : ℝ) ≤ 0
      exact le_rfl
    let R := parabolicSolution Sm 0 (Sm.scalar 0 p) nk.Q_pos hzero
    have hR : IsSolutionOn R := parabolicSolution_isSolutionOn Sm hSm 0 (Sm.scalar 0 p)
      nk.Q_pos hzero
    have hRdomain : Icc (-2 : ℝ) 0 ⊆
        (parabolicInterval ancientTimeInterval 0 (Sm.scalar 0 p) hzero).carrier := by
      intro r hr
      change 0 + r / Sm.scalar 0 p ≤ 0
      simpa only [zero_add] using div_nonpos_of_nonpos_of_nonneg hr.2 nk.Q_pos.le
    have hRregular : Ioo (-2 : ℝ) 0 ⊆
        (parabolicInterval ancientTimeInterval 0 (Sm.scalar 0 p) hzero).regular := by
      intro r hr
      change 0 + r / Sm.scalar 0 p < 0
      simpa only [zero_add] using div_neg_of_neg_of_pos hr.2 nk.Q_pos
    exact (cmp.jet_contDiffOn_of_solutions R hR T hT (by norm_num : (-2 : ℝ) < -1) hb
      (by norm_num : (-1 : ℝ) < 0) hRdomain hRregular hdomain hregular
      q (nk.map y) (houter y hy) v s hs).differentiableWithinAt (by simp)
  · intro q s hs _hu y hy v
    have hsub := neck_window_subset_of_le (neckModelTolerance_pos ha) (neckModelTolerance_le alpha)
    exact (nk.hasDerivWithinAt_comparison_jet_of_ancient hSm q hs y
      (hsub hy) v).differentiableWithinAt

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
