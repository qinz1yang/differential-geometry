import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

noncomputable section

open Filter MeasureTheory Set
open scoped Topology ENNReal

namespace DifferentialGeometry.Analysis.Integration

theorem intervalIntegral_le_of_forall_lt {f : ℝ → ℝ} {s T C : ℝ} (hsT : s ≤ T) (hC : 0 ≤ C)
    (hint : IntegrableOn f (Icc s T))
    (h : ∀ u : ℝ, s ≤ u → u < T → (∫ v in s..u, f v) ≤ C) :
    (∫ v in s..T, f v) ≤ C := by
  rcases lt_or_eq_of_le hsT with hsT' | rfl
  · have hcont : ContinuousOn (fun u : ℝ => ∫ v in s..u, f v) (Icc s T) := by
      have h := intervalIntegral.continuousOn_primitive_interval
        (show IntegrableOn f (uIcc s T) volume by rwa [uIcc_of_le hsT])
      rwa [uIcc_of_le hsT] at h
    have hmem : Ioo s T ∈ 𝓝[<] T :=
      mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
        ⟨Ioo s (T + 1), isOpen_Ioo.mem_nhds ⟨hsT', lt_add_one T⟩,
          fun u hu => ⟨hu.1.1, hu.2⟩⟩
    have hmemIcc : Icc s T ∈ 𝓝[<] T :=
      Filter.mem_of_superset hmem fun u hu => ⟨hu.1.le, hu.2.le⟩
    have hlim : Tendsto (fun u : ℝ => ∫ v in s..u, f v) (𝓝[<] T) (𝓝 (∫ v in s..T, f v)) :=
      (hcont.continuousWithinAt (right_mem_Icc.mpr hsT)).mono_of_mem_nhdsWithin hmemIcc
    have hev : ∀ᶠ u in 𝓝[<] T, (∫ v in s..u, f v) ≤ C :=
      Filter.mem_of_superset hmem fun u hu => h u hu.1.le hu.2
    exact le_of_tendsto hlim hev
  · simpa only [intervalIntegral.integral_same] using hC

theorem volume_lt_le_of_forall_lt {f : ℝ → ℝ} {s T B : ℝ} {C : ℝ≥0∞}
    (h : ∀ u : ℝ, s < u → u < T → volume {v : ℝ | v ∈ Icc s u ∧ B < f v} ≤ C) :
    volume {v : ℝ | v ∈ Icc s T ∧ B < f v} ≤ C := by
  rcases lt_or_ge s T with hsT | hTs
  · set u : ℕ → ℝ := (fun n => T - (T - s) / ((n : ℝ) + 2)) with hu
    have hu_gt : ∀ n : ℕ, s < u n := by
      intro n
      have h1 : (T - s) / ((n : ℝ) + 2) < T - s := by
        rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 2)]
        have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        nlinarith
      simp only [hu]
      linarith
    have hu_lt : ∀ n : ℕ, u n < T := by
      intro n
      have hp : 0 < (T - s) / ((n : ℝ) + 2) := div_pos (by linarith) (by positivity)
      simp only [hu]
      linarith
    have hmono : Monotone u := by
      intro m n hmn
      have hmn' : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
      have h2 : (T - s) / ((n : ℝ) + 2) ≤ (T - s) / ((m : ℝ) + 2) :=
        div_le_div_of_nonneg_left (by linarith) (by positivity) (by linarith)
      simp only [hu]
      linarith
    have hsetmono : Monotone fun n : ℕ => {v : ℝ | v ∈ Icc s (u n) ∧ B < f v} :=
      fun m n hmn v hv => ⟨⟨hv.1.1, hv.1.2.trans (hmono hmn)⟩, hv.2⟩
    have hcover : {v : ℝ | v ∈ Icc s T ∧ B < f v} ⊆
        (⋃ n : ℕ, {v : ℝ | v ∈ Icc s (u n) ∧ B < f v}) ∪ {T} := by
      rintro v ⟨hv, hBv⟩
      rcases lt_or_eq_of_le hv.2 with hlt | heq
      · left
        have hε : 0 < (T - v) / (T - s) := div_pos (by linarith) (by linarith)
        obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
        refine mem_iUnion.mpr ⟨m + 1, ⟨hv.1, ?_⟩, hBv⟩
        have hm' : (T - s) / ((m : ℝ) + 1) < T - v := by
          have hrew : (T - s) * (1 / ((m : ℝ) + 1)) = (T - s) / ((m : ℝ) + 1) := by ring
          rw [← hrew]
          calc (T - s) * (1 / ((m : ℝ) + 1))
              < (T - s) * ((T - v) / (T - s)) := mul_lt_mul_of_pos_left hm (by linarith)
            _ = T - v := by field_simp
        have h3 : (T - s) / (((m : ℝ) + 1) + 2) < (T - s) / ((m : ℝ) + 1) :=
          div_lt_div_of_pos_left (by linarith) (by positivity) (by linarith)
        simp only [hu]
        push_cast
        linarith
      · right
        simp only [mem_singleton_iff]
        exact heq
    calc volume {v : ℝ | v ∈ Icc s T ∧ B < f v}
        ≤ volume ((⋃ n : ℕ, {v : ℝ | v ∈ Icc s (u n) ∧ B < f v}) ∪ {T}) :=
          measure_mono hcover
      _ ≤ volume (⋃ n : ℕ, {v : ℝ | v ∈ Icc s (u n) ∧ B < f v}) + volume {T} :=
          measure_union_le _ _
      _ = volume (⋃ n : ℕ, {v : ℝ | v ∈ Icc s (u n) ∧ B < f v}) := by
          rw [Real.volume_singleton, add_zero]
      _ = ⨆ n : ℕ, volume {v : ℝ | v ∈ Icc s (u n) ∧ B < f v} := hsetmono.measure_iUnion
      _ ≤ C := ciSup_le fun n => h (u n) (hu_gt n) (hu_lt n)
  · have hsub : {v : ℝ | v ∈ Icc s T ∧ B < f v} ⊆ {T} := by
      rintro v ⟨hv, -⟩
      simp only [mem_singleton_iff]
      exact le_antisymm hv.2 (hTs.trans hv.1)
    exact ((measure_mono hsub).trans_eq Real.volume_singleton).trans (by simp)

end DifferentialGeometry.Analysis.Integration
