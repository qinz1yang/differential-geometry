import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TerminalPoleCenters
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientReducedLengthRetiming
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.RegularPoleRescalings

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Filter Set CanonicalNeighborhood
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

private local instance : TopologicalSpace F.M := F.topology
private local instance : ChartedSpace H F.M := F.charted
private local instance : IsManifold I ∞ F.M := F.smooth
private local instance : T2Space F.M := F.t2
private local instance : SigmaCompactSpace F.M := F.sigmaCompact

theorem exists_poleRescaledFlowSeq_tail_of_terminal_redLength_bound
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p : F.M) (tau : ℕ → ℝ) (hescape : Tendsto tau atTop atTop)
    (q : ℕ → F.M) {A : ℝ} (hA : 0 ≤ A)
    (hterminal : ∀ᶠ i in atTop, redLength F.S 0 p (q i) (tau i) ≤ A) :
    ∃ (b : ℝ) (_hb : b < 0) (hbmem : b ∈ ancientTimeInterval.carrier)
      (N : ℕ) (hsigma : ∀ i, 0 < tau (i + N) + b) (C : ℝ),
      let S := poleRescaledFlowSeq F hF.carrier_eq hF.regular_eq b hbmem
        (fun j => tau (j + N)) (fun j => q (j + N)) hsigma
      0 < C ∧
      StrictMono (fun i : ℕ => i + N) ∧
      Tendsto (fun i : ℕ => i + N) atTop atTop ∧
      Tendsto (fun i : ℕ => tau (i + N)) atTop atTop ∧
      Tendsto (fun i : ℕ => tau (i + N) + b) atTop atTop ∧
      (∀ i, redLength F.S b p (q (i + N)) (tau (i + N) + b) ≤ C) ∧
      (∀ i, (S.term i).basepoint = q (i + N)) ∧
      (∀ i, IsAncientKappaSolution kappa (S.term i)) ∧
      ∀ i, (S.term i).S.base.metric (-1) =
        scaleMetric (tau (i + N) + b)⁻¹ (inv_pos.mpr (hsigma i))
          (F.S.base.metric (-tau (i + N))) := by
  obtain ⟨b, hb, x, hx⟩ := exists_neg_time_rmNormSq_ne_zero_of_ancient F hF
  have hbmem : b ∈ ancientTimeInterval.carrier := hb.le
  obtain ⟨C, hC, hbound⟩ := exists_ancientKappa_eventually_redLength_shift_le
    F hF hb hA p hescape q hterminal
  obtain ⟨N, hN⟩ := eventually_atTop.mp hbound
  have hpos (i : ℕ) : 0 < tau (i + N) + b :=
    (hN (i + N) (Nat.le_add_left N i)).1
  have heta : Tendsto (fun i : ℕ => i + N) atTop atTop := tendsto_add_atTop_nat N
  have htau : Tendsto (fun i : ℕ => tau (i + N)) atTop atTop := hescape.comp heta
  have hsigma : Tendsto (fun i : ℕ => tau (i + N) + b) atTop atTop := by
    apply tendsto_atTop.mpr
    intro R
    filter_upwards [htau.eventually_ge_atTop (R - b)] with i hi
    linarith
  refine ⟨b, hb, hbmem, N, hpos, C * (A + 1), ?_,
    (fun _ _ hij => Nat.add_lt_add_right hij N), heta, htau, hsigma, ?_, ?_, ?_, ?_⟩
  · exact mul_pos hC (by linarith)
  · intro i
    apply (hN (i + N) (Nat.le_add_left N i)).2.trans
    exact mul_le_mul_of_nonneg_left (by linarith) hC.le
  · intro i
    exact poleRescaledFlowSeq_basepoint F hF.carrier_eq hF.regular_eq b hbmem
      (fun j => tau (j + N)) (fun j => q (j + N)) hpos i
  · intro i
    exact isAncientKappaSolution_curvatureNormalizedFlow_of_rmNormSq_ne_zero
      F hF b (tau (i + N) + b)⁻¹ (inv_pos.mpr (hpos i)) hbmem
      (q (i + N)) le_rfl x hx
  · intro i
    exact poleRescaledFlowSeq_metric_neg_one F hF.carrier_eq hF.regular_eq b hbmem
      (fun j => tau (j + N)) (fun j => q (j + N)) hpos i

theorem exists_poleRescaledFlowSeq_tail_with_terminal_redLength_bound
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p : F.M) (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i)
    (hescape : Tendsto tau atTop atTop) :
    ∃ q : ℕ → F.M,
      (∀ i, redLength F.S 0 p (q i) (tau i) ≤ (Module.finrank ℝ E : ℝ) / 2) ∧
      ∃ (b : ℝ) (_hb : b < 0) (hbmem : b ∈ ancientTimeInterval.carrier)
        (N : ℕ) (hsigma : ∀ i, 0 < tau (i + N) + b) (C : ℝ),
        let S := poleRescaledFlowSeq F hF.carrier_eq hF.regular_eq b hbmem
          (fun j => tau (j + N)) (fun j => q (j + N)) hsigma
        0 < C ∧
        StrictMono (fun i : ℕ => i + N) ∧
        Tendsto (fun i : ℕ => i + N) atTop atTop ∧
        Tendsto (fun i : ℕ => tau (i + N)) atTop atTop ∧
        Tendsto (fun i : ℕ => tau (i + N) + b) atTop atTop ∧
        (∀ i, redLength F.S b p (q (i + N)) (tau (i + N) + b) ≤ C) ∧
        (∀ i, (S.term i).basepoint = q (i + N)) ∧
        (∀ i, IsAncientKappaSolution kappa (S.term i)) ∧
        ∀ i, (S.term i).S.base.metric (-1) =
          scaleMetric (tau (i + N) + b)⁻¹ (inv_pos.mpr (hsigma i))
            (F.S.base.metric (-tau (i + N))) := by
  classical
  choose q hq using fun i => exists_redLength_le_half_finrank_of_ancient F hF p (htau i)
  refine ⟨q, hq, ?_⟩
  exact exists_poleRescaledFlowSeq_tail_of_terminal_redLength_bound
    F hF p tau hescape q (by positivity) (Eventually.of_forall hq)

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
