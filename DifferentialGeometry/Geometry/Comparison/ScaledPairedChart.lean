import DifferentialGeometry.Geometry.Comparison.VariablePairedRank
import DifferentialGeometry.Geometry.Comparison.PairedChartQuality
import DifferentialGeometry.Geometry.Comparison.PairedPacketLocalization

set_option autoImplicit false

open Set Metric Real
open scoped Topology NNReal ENNReal

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

variable {X : Type*} [MetricSpace X] [Nontrivial X]

theorem exists_distance_chart_of_scaled_quality_in_open_set
    (hcurves : ∀ x y : X, ∀ η : ℝ, 0 < η →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = x ∧ c 1 = y ∧
        eVariationOn c univ < ENNReal.ofReal (dist x y + η))
    {Ω O : Set X} (hcomp : fourPointComparison 1 Ω) (hOΩ : O ⊆ Ω)
    (hO : IsOpen O) (hOne : O.Nonempty)
    (hcomplete : ∀ z ∈ Ω, ∃ R : ℝ, 0 < R ∧ IsComplete (closedBall z R))
    {n : ℕ} (hn : 1 ≤ n) (hdim : dimH Ω ≤ n)
    {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    ∃ m : ℕ, 1 ≤ m ∧ m ≤ n ∧ ∃ q ∈ O, ∃ a b : Fin m → X,
      PairedComparisonPacket (c * pairedChartQuality n m) {q} a b ∧
      range a ∪ range b ⊆ Ω ∧
      ∃ r : ℝ, 0 < r ∧ ball q r ⊆ O ∧
      ∃ U : Set (PiLp 2 (fun _ : Fin m => ℝ)), IsOpen U ∧
      ∃ e : ball q r ≃ₜ U,
        (∀ z, (e z : PiLp 2 (fun _ : Fin m => ℝ)) = distanceCoordinates 2 a (z : X)) ∧
        (∀ x y, ((c * pairedChartQuality n (m + 1)) / (100 * Real.pi)) ^ 2 * dist x y ≤ dist (e x) (e y)) ∧
        LipschitzWith (NNReal.sqrt m) e := by
  let σ : ℕ → ℝ := fun k => c * pairedChartQuality n k
  have hσpos (k : ℕ) (_hk : 1 ≤ k) (_hkn : k ≤ n + 1) : 0 < σ k :=
    mul_pos hc (pairedChartQuality_pos n k)
  have hσbound (k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n + 1) :
      σ k ≤ 1 / (200 * (k : ℝ)) := by
    exact (mul_le_of_le_one_left (pairedChartQuality_pos n k).le hc1).trans
      (pairedChartQuality_le_rank_bound n (by omega) hkn)
  obtain ⟨m, hm1, hmn, q, hq, a, b, hp, hab, hno⟩ :=
    exists_maximal_paired_rank_of_quality hcurves hcomp hOΩ hO hOne hcomplete hn hdim
      σ hσpos hσbound
  let : NeZero m := ⟨by omega⟩
  let δ := 2 * σ m
  let β := σ (m + 1)
  have hδ : 0 < δ := mul_pos (by norm_num) (hσpos m hm1 (by omega))
  have hβ : 0 < β := hσpos (m + 1) (by omega) (by omega)
  have hδβ : δ = β / 100 := by
    dsimp [δ, β, σ]
    rw [pairedChartQuality_succ]
    ring
  have hβm : β ≤ 1 / (200 * ((m : ℝ) + 1)) := by
    simpa only [β, Nat.cast_succ] using
      hσbound (m + 1) (by omega) (Nat.succ_le_succ hmn)
  have hp' : PairedComparisonPacket (δ / 2) {q} a b := by
    simpa only [δ, mul_div_cancel_left₀ _ (two_ne_zero : (2 : ℝ) ≠ 0)] using hp
  have hsmall : δ / 2 < Real.pi / 2 := by
    have hden : 0 < 200 * ((m : ℝ) + 1) := by positivity
    have hβ1 : β ≤ 1 := hβm.trans ((div_le_one hden).mpr (by nlinarith [Nat.cast_nonneg (α := ℝ) m]))
    rw [hδβ]
    linarith [Real.two_le_pi]
  obtain ⟨V, hVo, hqV, hVO, hpacket, a₀, A, ha₀, _, hbounds⟩ :=
    hp'.exists_uniform_nhds hδ (hp'.not_mem_anchors (mem_singleton _) hsmall) (hO.mem_nhds hq)
  obtain ⟨R, hR, hRV⟩ := Metric.isOpen_iff.mp hVo q hqV
  let ε : ℝ := (β / (100 * Real.pi)) ^ 2
  let K : ℝ := 4 * cosh (A + 1) / sinh a₀
  let r : ℝ := min (R / 4) (min (1 / 4) (min (a₀ / 8) (ε / (4 * K))))
  have hK : 0 < K := div_pos (by positivity) (sinh_pos_iff.mpr ha₀)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hr : 0 < r := lt_min (by positivity) (lt_min (by norm_num)
    (lt_min (by positivity) (div_pos hε (by positivity))))
  have hrR : r ≤ R / 4 := min_le_left _ _
  have hr1 : r ≤ 1 / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hra : r ≤ a₀ / 8 := ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hrε : r ≤ ε / (4 * K) := ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)
  have hrK : 2 * r ≤ ε / K := by
    have h := (le_div_iff₀ (show 0 < 4 * K by positivity)).mp hrε
    apply (le_div_iff₀ hK).mpr
    nlinarith [mul_pos hK hr]
  obtain ⟨U, hU, e, he, hlo, hLip, _⟩ := hpacket.exists_chart_of_rank_exclusion
    hcurves hcomp (hVO.trans hOΩ) hab ha₀ hβ (by simpa using hβm) hδ
    hδβ.le hbounds (fun z hz => hcomplete z (hOΩ (hVO hz)))
    (fun z hz c d hcd => hno z (hVO hz) c d hcd) hr
    ((ball_subset_ball (show 3 * r ≤ R by linarith)).trans hRV)
    (by linarith) (by linarith) hrK
  refine ⟨m, hm1, hmn, q, hq, a, b, hp, hab, r, hr,
    ((ball_subset_ball (show r ≤ R by linarith)).trans hRV).trans hVO, U, hU, e, he, hlo, ?_⟩
  simpa only [Fintype.card_fin] using hLip

end DifferentialGeometry.Geometry.Comparison.Toponogov
