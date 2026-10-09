import DifferentialGeometry.Geometry.Comparison.RankOnePacket
import DifferentialGeometry.Geometry.Comparison.PairedChartQuality
import DifferentialGeometry.Geometry.Comparison.PairedPacketReindex
import DifferentialGeometry.Geometry.Comparison.PairedPacketDimension
import Mathlib.Data.Nat.Find

set_option autoImplicit false

open Set Metric
open scoped Topology ENNReal

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

variable {X : Type*} [MetricSpace X] [Nontrivial X]

theorem exists_maximal_paired_rank
    (hcurves : ∀ x y : X, ∀ η : ℝ, 0 < η →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = x ∧ c 1 = y ∧
        eVariationOn c univ < ENNReal.ofReal (dist x y + η))
    {Ω O : Set X} (hcomp : fourPointComparison 1 Ω) (hOΩ : O ⊆ Ω)
    (hO : IsOpen O) (hOne : O.Nonempty)
    (hcomplete : ∀ z ∈ Ω, ∃ R : ℝ, 0 < R ∧ IsComplete (closedBall z R))
    {n : ℕ} (hn : 1 ≤ n) (hdim : dimH Ω ≤ n) :
    ∃ m : ℕ, 1 ≤ m ∧ m ≤ n ∧ ∃ q ∈ O, ∃ a b : Fin m → X,
      PairedComparisonPacket (pairedChartQuality n m) {q} a b ∧ range a ∪ range b ⊆ Ω ∧
      ∀ z ∈ O, ∀ c d : Option (Fin m) → X, range c ∪ range d ⊆ Ω →
        ¬ PairedComparisonPacket (pairedChartQuality n (m + 1)) {z} c d := by
  classical
  let P : ℕ → Prop := fun k => 1 ≤ k ∧ ∃ q ∈ O, ∃ a b : Fin k → X,
    PairedComparisonPacket (pairedChartQuality n k) {q} a b ∧ range a ∪ range b ⊆ Ω
  have h1top : 1 ≤ n + 1 := Nat.le_succ_of_le hn
  have hquality1 : pairedChartQuality n 1 ≤ 1 := by
    have h := pairedChartQuality_le_rank_bound n (by omega : 0 < 1) h1top
    norm_num at h
    linarith
  obtain ⟨x, hx, y, hy, z, hz, _, hp⟩ := exists_rank_one_packet_in_open_set
    hcurves hO hOne (pairedChartQuality_pos n 1) hquality1
  have hP1 : P 1 := by
    refine ⟨le_rfl, z, hz, _, _, hp, ?_⟩
    rintro w (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact hOΩ hx
    · exact hOΩ hy
  have hceil (k : ℕ) (hk : k ≤ n + 1) (hp : P k) : k ≤ n := by
    have hk0 : 0 < k := by omega
    let : NeZero k := ⟨Nat.ne_zero_of_lt hk0⟩
    obtain ⟨_, q, hq, a, b, hpacket, hanchors⟩ := hp
    have hd := hpacket.card_le_dimH hcurves hcomp
      (Filter.mem_of_superset (hO.mem_nhds hq) hOΩ) hanchors (pairedChartQuality_pos n k)
      (by simpa only [Fintype.card_fin] using pairedChartQuality_le_rank_bound n hk0 hk) hcomplete
    have hh := hd.trans hdim
    simpa only [Fintype.card_fin, Nat.cast_le] using hh
  let m := Nat.findGreatest P (n + 1)
  have hmP : P m := Nat.findGreatest_spec h1top hP1
  have hmtop : m ≤ n + 1 := Nat.findGreatest_le _
  have hmn : m ≤ n := hceil m hmtop hmP
  obtain ⟨hm1, q, hq, a, b, hpacket, hanchors⟩ := hmP
  refine ⟨m, hm1, hmn, q, hq, a, b, hpacket, hanchors, ?_⟩
  intro z hz c d hcd hp
  let e : Fin (m + 1) ≃ Option (Fin m) := Fintype.equivOfCardEq (by simp)
  have hnext : P (m + 1) := by
    refine ⟨by omega, z, hz, c ∘ e, d ∘ e, hp.reindex e, ?_⟩
    rintro w (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact hcd (Or.inl ⟨e i, rfl⟩)
    · exact hcd (Or.inr ⟨e i, rfl⟩)
  have hle := Nat.le_findGreatest (Nat.succ_le_succ hmn) hnext
  exact Nat.not_succ_le_self m hle

end DifferentialGeometry.Geometry.Comparison.Toponogov
