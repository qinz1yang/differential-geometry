import DifferentialGeometry.Geometry.Comparison.ScaledPairedChart
import DifferentialGeometry.Geometry.Comparison.GlobalIntegerDimension

set_option autoImplicit false

open Set Metric Real
open scoped NNReal ENNReal Topology

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem exists_global_rank_paired_packets_of_local_comparison_and_dimH
    {X : Type*} [MetricSpace X] [CompleteSpace X] [Nontrivial X]
    (hcurves : ∀ x y : X, ∀ η : ℝ, 0 < η →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = x ∧ c 1 = y ∧
        eVariationOn c univ < ENNReal.ofReal (dist x y + η))
    {n : ℕ} (hdim : dimH (univ : Set X) ≤ n)
    (hlocal : ∀ p : X, ∃ Ω : Set X, IsOpen Ω ∧ fourPointComparison 1 Ω ∧ p ∈ Ω) :
    ∃ m : ℕ, m ≤ n ∧ dimH (univ : Set X) = m ∧
      (∀ V : Set X, IsOpen V → V.Nonempty → dimH V = m) ∧
      ∀ ε : ℝ, 0 < ε → ∀ O : Set X, IsOpen O → O.Nonempty →
        ∃ q ∈ O, ∃ Ω : Set X, IsOpen Ω ∧ fourPointComparison 1 Ω ∧ q ∈ Ω ∧
          ∃ a b : Fin m → X, range a ∪ range b ⊆ Ω ∧
            PairedComparisonPacket ε {q} a b := by
  obtain ⟨m, hmn, hglobal, hopen⟩ :=
    exists_global_integer_dimH_of_local_comparison_and_dimH hcurves hdim hlocal
  refine ⟨m, hmn, hglobal, hopen, ?_⟩
  intro ε hε O hO hOne
  obtain ⟨p, hp⟩ := hOne
  obtain ⟨Ω, hΩ, hcomp, hpΩ⟩ := hlocal p
  let V := Ω ∩ O
  have hV : IsOpen V := hΩ.inter hO
  have hpV : p ∈ V := ⟨hpΩ, hp⟩
  have hdimΩ : dimH Ω ≤ (n + 1 : ℕ) := by
    exact ((dimH_mono (subset_univ Ω)).trans hdim).trans (by exact_mod_cast Nat.le_succ n)
  let c : ℝ := min 1 ε
  have hc : 0 < c := lt_min zero_lt_one hε
  have hc1 : c ≤ 1 := min_le_left _ _
  obtain ⟨k, hk1, hkn, q, hq, a, b, hpacket, hab, r, hr, hBr, U, hU, e, he, hlo, hhi⟩ :=
    exists_distance_chart_of_scaled_quality_in_open_set hcurves hcomp inter_subset_left hV
      ⟨p, hpV⟩ (fun z _ => ⟨1, zero_lt_one, isClosed_closedBall.isComplete⟩)
      (by omega : 1 ≤ n + 1) hdimΩ hc hc1
  let F : ball q r → PiLp 2 (fun _ : Fin k => ℝ) := fun z => (e z).val
  let L : ℝ := ((c * pairedChartQuality (n + 1) (k + 1)) / (100 * Real.pi)) ^ 2
  have hL : 0 < L := by
    dsimp [L]
    exact sq_pos_of_pos (div_pos (mul_pos hc (pairedChartQuality_pos _ _)) (by positivity))
  let D : ℝ≥0 := ⟨L⁻¹, (inv_pos.mpr hL).le⟩
  have hLip : LipschitzWith (NNReal.sqrt k) F := by
    simpa only [F, Function.comp_def, one_mul] using isometry_subtype_coe.lipschitzWith.comp hhi
  have hAnti : AntilipschitzWith D F := by
    apply AntilipschitzWith.of_le_mul_dist
    intro x y
    change dist x y ≤ L⁻¹ * dist (e x) (e y)
    have hh := mul_le_mul_of_nonneg_left (hlo x y) (inv_pos.mpr hL).le
    simpa only [L, ← mul_assoc, inv_mul_cancel₀ hL.ne', one_mul] using hh
  have himage : F '' (univ : Set (ball q r)) = U := by
    rw [image_univ]
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact (e x).property
    · intro hz
      obtain ⟨x, hx⟩ := e.surjective ⟨z, hz⟩
      exact ⟨x, congrArg Subtype.val hx⟩
  have hsource : dimH (univ : Set (ball q r)) = dimH (ball q r) := by
    simpa only [image_univ, Subtype.range_coe] using
      (isometry_subtype_coe.dimH_image (univ : Set (ball q r))).symm
  have heq : dimH (ball q r) = dimH U := by
    apply le_antisymm
    · simpa only [himage, hsource] using hAnti.le_dimH_image (univ : Set (ball q r))
    · simpa only [himage, hsource] using hLip.dimH_image_le (univ : Set (ball q r))
  have hchart : dimH (ball q r) = k := by
    apply heq.trans
    have hdU := Real.dimH_of_mem_nhds (hU.mem_nhds (e ⟨q, mem_ball_self hr⟩).property)
    simpa using hdU
  have hkm : k = m := by
    exact_mod_cast hchart.symm.trans (hopen _ isOpen_ball ⟨q, mem_ball_self hr⟩)
  subst k
  have hquality : pairedChartQuality (n + 1) m ≤ 1 := by
    have hh := pairedChartQuality_le (n + 1) (show m ≤ (n + 1) + 1 by omega)
    apply hh.trans
    apply (div_le_one (by positivity)).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) (n + 1)]
  have hsmall : c * pairedChartQuality (n + 1) m ≤ ε :=
    (mul_le_of_le_one_right hc.le hquality).trans (min_le_right 1 ε)
  exact ⟨q, hq.2, Ω, hΩ, hcomp, hq.1, a, b, hab, hpacket.weaken hsmall⟩

end DifferentialGeometry.Geometry.Comparison.Toponogov
