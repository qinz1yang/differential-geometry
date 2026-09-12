import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.Flow
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.LocalRegularity
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic



noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Families

open CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
    [SigmaCompactSpace Q] [hT2 : T2Space Q] [hCompact : CompactSpace Q]
    [hConnected : ConnectedSpace Q] [hBoundary : I.Boundaryless]
    {D : RealTimeInterval} {a b : ℝ}

include hT2 hCompact hConnected hBoundary

theorem rfs_ramp_small_angle (g : SmoothRiemannianMetric I Q)
    (c : ProductCurve Q) (lambda t ell K : ℝ) (hlambda : 0 < lambda)
    (hell : 0 < ell) (hK : 0 < K) (hdegree : c.degree = 1)
    (hsmooth : c.SmoothOn (I := I) {t})
    (hramp : c.IsRampOn (fun _ => g) lambda {t})
    (hlength : ell ≤ c.length (fun _ => g) lambda t)
    (hcurvature : ∀ x, c.curvature (fun _ => g) lambda x t ≤ K) :
    ∀ x, c.angle (fun _ => g) lambda x t ≤ 2 * lambda / ell + 2 * Real.sqrt (K * lambda) := by
  sorry


def localRegularityDelta (B : RicciBackground (I := I) (M := Q) D a b) (L₀ Theta₀ : ℝ)
    (K : CurveShorteningRegularityInput B L₀ Theta₀) : ℝ :=
  K.delta

def localRegularityRadius (B : RicciBackground (I := I) (M := Q) D a b) (L₀ Theta₀ : ℝ)
    (K : CurveShorteningRegularityInput B L₀ Theta₀) : ℝ :=
  K.radius

def localRegularityCoefficient (B : RicciBackground (I := I) (M := Q) D a b) (L₀ Theta₀ : ℝ)
    (K : CurveShorteningRegularityInput B L₀ Theta₀) : ℕ → ℝ :=
  K.coefficient


def goodWindowUnion (starts : Finset ℝ) (d : ℝ) : Set ℝ :=
  {t | ∃ w ∈ starts, t ∈ Icc (w + 5 * d / 8) (w + 7 * d / 8)}

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [TopologicalSpace H] [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
  hT2 hCompact hConnected hBoundary in
theorem volume_lt_le_of_integral_le {f : ℝ → ℝ} {s t B C : ℝ}
    (hst : s ≤ t) (hB : 0 < B)
    (hint : IntervalIntegrable f volume s t)
    (hnn : ∀ v ∈ Icc s t, 0 ≤ f v)
    (hE : (∫ v in s..t, f v) ≤ C) :
    volume {v : ℝ | v ∈ Icc s t ∧ B < f v} ≤ ENNReal.ofReal (C / B) := by
  have hintI : IntegrableOn f (Icc s t) volume :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hst).mp hint
  have hnn' : 0 ≤ᵐ[volume.restrict (Icc s t)] f :=
    (ae_restrict_iff' measurableSet_Icc).mpr (Filter.Eventually.of_forall hnn)
  have hmeas : AEMeasurable f (volume.restrict (Icc s t)) := hintI.aestronglyMeasurable.aemeasurable
  have hmeas' : AEMeasurable (fun v => ENNReal.ofReal (f v)) (volume.restrict (Icc s t)) :=
    hmeas.ennreal_ofReal
  have hmark := MeasureTheory.meas_ge_le_lintegral_div (μ := volume.restrict (Icc s t)) hmeas'
    (ε := ENNReal.ofReal B) (by rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hB)
    ENNReal.ofReal_ne_top
  have hsub : {v : ℝ | v ∈ Icc s t ∧ B < f v} ⊆
      Icc s t ∩ {v : ℝ | ENNReal.ofReal B ≤ ENNReal.ofReal (f v)} := fun v hv =>
    ⟨hv.1, ENNReal.ofReal_le_ofReal hv.2.le⟩
  have hnull : NullMeasurableSet {v : ℝ | ENNReal.ofReal B ≤ ENNReal.ofReal (f v)}
      (volume.restrict (Icc s t)) := hmeas'.nullMeasurableSet_preimage measurableSet_Ici
  have hres : (volume.restrict (Icc s t)) {v : ℝ | ENNReal.ofReal B ≤ ENNReal.ofReal (f v)} =
      volume (Icc s t ∩ {v : ℝ | ENNReal.ofReal B ≤ ENNReal.ofReal (f v)}) := by
    rw [Measure.restrict_apply₀ hnull, Set.inter_comm]
  have hIcc : (∫ x, f x ∂(volume.restrict (Icc s t))) = ∫ v in s..t, f v :=
    integral_Icc_eq_integral_Ioc.trans (intervalIntegral.integral_of_le hst).symm
  have hlint : (∫⁻ v, ENNReal.ofReal (f v) ∂(volume.restrict (Icc s t))) =
      ENNReal.ofReal (∫ v in s..t, f v) := by
    rw [← hIcc, ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hintI hnn']
  calc volume {v : ℝ | v ∈ Icc s t ∧ B < f v}
      ≤ volume (Icc s t ∩ {v : ℝ | ENNReal.ofReal B ≤ ENNReal.ofReal (f v)}) :=
        measure_mono hsub
    _ = (volume.restrict (Icc s t)) {v : ℝ | ENNReal.ofReal B ≤ ENNReal.ofReal (f v)} := hres.symm
    _ ≤ (∫⁻ v, ENNReal.ofReal (f v) ∂(volume.restrict (Icc s t))) / ENNReal.ofReal B := hmark
    _ = ENNReal.ofReal (∫ v in s..t, f v) / ENNReal.ofReal B := by rw [hlint]
    _ ≤ ENNReal.ofReal C / ENNReal.ofReal B :=
        ENNReal.div_le_div_right (ENNReal.ofReal_le_ofReal hE) _
    _ = ENNReal.ofReal (C / B) := (ENNReal.ofReal_div_of_pos hB).symm

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [TopologicalSpace H] [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
  hT2 hCompact hConnected hBoundary in
theorem volume_image_add_right (c : ℝ) (B : Set ℝ) :
    volume ((fun v : ℝ => v + c) '' B) = volume B := by
  have hfun : (fun v : ℝ => v + c) '' B = (fun v : ℝ => v + (-c)) ⁻¹' B := by
    ext v; constructor
    · rintro ⟨u, hu, rfl⟩
      simpa only [Set.mem_preimage, add_assoc, add_neg_cancel, add_zero] using hu
    · intro hv
      exact ⟨v + -c, hv, by ring⟩
  rw [hfun]
  exact measure_preimage_add_right volume (-c) B


omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [TopologicalSpace H] [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
  hT2 hCompact hConnected hBoundary in
theorem exists_goodWindow_finset_of_energy_bound {a b d C threshold : ℝ} (hd : 0 < d) (hab : a ≤ b)
    {f : ℝ → ℝ} (hfint : IntervalIntegrable f volume a b)
    (hfnn : ∀ t ∈ Icc a b, 0 ≤ f t) (hfb : (∫ t in a..b, f t) ≤ C)
    (hth : 0 < threshold) :
    ∃ starts : Finset ℝ,
      (∀ w ∈ starts, w ∈ Icc a (b - d) ∧ f w ≤ threshold) ∧
      goodWindowUnion starts d ⊆ Ioo a b ∧
      volume (Icc a b \ goodWindowUnion starts d) ≤ ENNReal.ofReal (d + C / threshold) ∧
      ∀ w ∈ starts, Icc (w + 5 * d / 8) (w + 7 * d / 8) ⊆ Ioo (w + d / 2) (w + d) := by
  classical
  have hCnn : 0 ≤ C := le_trans (intervalIntegral.integral_nonneg hab hfnn) hfb
  have hCdiv : 0 ≤ C / threshold := div_nonneg hCnn hth.le
  have hof : ENNReal.ofReal (d + C / threshold) =
      ENNReal.ofReal d + ENNReal.ofReal (C / threshold) :=
    ENNReal.ofReal_add (le_of_lt hd) hCdiv
  have hMarkov : volume {v : ℝ | v ∈ Icc a b ∧ threshold < f v} ≤
      ENNReal.ofReal (C / threshold) :=
    volume_lt_le_of_integral_le hab hth hfint hfnn hfb
  by_cases hsmall : b - a ≤ d
  · refine ⟨∅, ?_, ?_, ?_, ?_⟩
    · intro w hw; simp at hw
    · intro t ht
      simp only [goodWindowUnion, Set.mem_ofPred_eq] at ht
      obtain ⟨w, hw, -⟩ := ht
      simp at hw
    · have hset : Icc a b \ goodWindowUnion (∅ : Finset ℝ) d = Icc a b := by
        ext t
        simp only [goodWindowUnion, Set.mem_ofPred_eq, mem_sdiff, mem_Icc]
        constructor
        · rintro ⟨h, -⟩; exact h
        · intro h; exact ⟨h, fun hcon => by obtain ⟨w, hw, -⟩ := hcon; simp at hw⟩
      rw [hset, Real.volume_Icc, hof]
      exact le_trans (ENNReal.ofReal_le_ofReal hsmall) (le_add_of_nonneg_right bot_le)
    · intro w hw; simp at hw
  · have hgt : d < b - a := lt_of_not_ge hsmall
    set h : ℝ := d / 8 with hh
    have hhpos : 0 < h := by rw [hh]; positivity
    have hdh : 8 * h = d := by rw [hh]; ring
    have h5 : (5 : ℝ) * d / 8 = 5 * h := by rw [hh]; ring
    have h7 : (7 : ℝ) * d / 8 = 7 * h := by rw [hh]; ring
    have hbann : 0 ≤ b - a := by linarith
    set m : ℕ := ⌊(b - a) / h⌋₊ with hm
    have hmge : 8 ≤ m := by
      have h1 : (8 : ℝ) ≤ (b - a) / h := by
        rw [le_div_iff₀ hhpos]; linarith [hdh, hgt]
      simpa [hm] using Nat.le_floor h1
    set K : ℕ := m - 8 with hK
    set r : ℝ := b - a - (m : ℝ) * h with hr
    have hKr : (K : ℝ) = (m : ℝ) - 8 := by rw [hK]; exact Nat.cast_sub hmge
    have hm0 : 0 ≤ (b - a) / h := div_nonneg hbann hhpos.le
    have hmh_le : (m : ℝ) * h ≤ b - a := by
      have h1 : ((m : ℝ)) ≤ (b - a) / h := by simpa [hm] using Nat.floor_le hm0
      have h2 : ((m : ℝ)) * h ≤ ((b - a) / h) * h := mul_le_mul_of_nonneg_right h1 hhpos.le
      rwa [div_mul_cancel₀ _ (ne_of_gt hhpos)] at h2
    have hmh_lt : b - a < ((m : ℝ) + 1) * h := by
      have h1 : ((b - a) / h) < ((m : ℝ) + 1) := by
        simpa [hm] using Nat.lt_floor_add_one ((b - a) / h)
      have h2 : ((b - a) / h) * h < ((m : ℝ) + 1) * h := mul_lt_mul_of_pos_right h1 hhpos
      rwa [div_mul_cancel₀ _ (ne_of_gt hhpos)] at h2
    have hrnn : 0 ≤ r := by rw [hr]; linarith
    have hrlt : r < h := by
      have h3 : b - a < (m : ℝ) * h + h := by linarith [hmh_lt]
      rw [hr]; linarith
    set p : ℕ → ℝ := fun j => a + (j : ℝ) * h with hp
    have hp_apply : ∀ j : ℕ, p j = a + (j : ℝ) * h := fun j => rfl
    have hp_add : ∀ j k : ℕ, p (j + k) = p j + (k : ℝ) * h := by
      intro j k; rw [hp_apply, hp_apply]; push_cast; ring
    have hp_succ : ∀ j, p (j + 1) = p j + h := by intro j; simpa using hp_add j 1
    have hpa : ∀ j, a ≤ p j := by
      intro j; rw [hp_apply]
      exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg j) hhpos.le)
    have hp_mono : Monotone p := by
      intro i j hij
      rw [hp_apply, hp_apply]
      have h1 : (i : ℝ) ≤ (j : ℝ) := Nat.cast_le.mpr hij
      nlinarith [hhpos]
    have hpK_le : p K ≤ b - d := by
      rw [hp_apply, hKr, ← hdh]; nlinarith [hmh_le]
    have hbd : b - d = p K + r := by
      rw [hp_apply, hr, hKr, ← hdh]; ring
    set cell : ℕ → Set ℝ := fun j => if j < K then Icc (p j) (p (j + 1)) else Icc (p K) (b - d)
      with hcell
    have hcell_lt : ∀ j, j < K → cell j = Icc (p j) (p (j + 1)) := by
      intro j hj; simp only [hcell, if_pos hj]
    have hcell_ge : ∀ j, K ≤ j → cell j = Icc (p K) (b - d) := by
      intro j hj; simp only [hcell, if_neg (not_lt.mpr hj)]
    have hcell_sub : ∀ j, cell j ⊆ Icc a (b - d) := by
      intro j
      rcases lt_or_ge j K with hlt | hge
      · rw [hcell_lt j hlt]
        exact Icc_subset_Icc (hpa j) (le_trans (hp_mono (by omega)) hpK_le)
      · rw [hcell_ge j hge]; exact Icc_subset_Icc (hpa K) le_rfl
    have hcell_ab : ∀ j, cell j ⊆ Icc a b := by
      intro j
      exact Subset.trans (hcell_sub j) (Icc_subset_Icc le_rfl (by linarith [hd, hdh]))
    set good : ℕ → Prop := fun j => ∃ x : ℝ, x ∈ cell j ∧ f x ≤ threshold with hgood
    set wfun : ℕ → ℝ := fun j => if hj : good j then Classical.choose hj else a with hwfun
    have hwfun_spec : ∀ j, good j → wfun j ∈ cell j ∧ f (wfun j) ≤ threshold := by
      intro j hj
      have h1 : wfun j = Classical.choose hj := by rw [hwfun]; simp only [dif_pos hj]
      rw [h1]; exact Classical.choose_spec hj
    have hxlo : ∀ j ≤ K, ∀ x ∈ cell j, p j ≤ x := by
      intro j hj x hx
      rcases lt_or_eq_of_le hj with hlt | heq
      · rw [hcell_lt j hlt] at hx; exact hx.1
      · subst heq; rw [hcell_ge K le_rfl] at hx; exact hx.1
    have hxhi_lt : ∀ j, j < K → ∀ x ∈ cell j, x ≤ p j + h := by
      intro j hj x hx
      rw [hcell_lt j hj, hp_succ j] at hx
      exact hx.2
    have hxhi_K : ∀ x ∈ cell K, x ≤ p K + r := by
      intro x hx
      rw [hcell_ge K le_rfl, hbd] at hx
      exact hx.2
    have hcover : ∀ j ≤ K, ∀ x ∈ cell j,
        Icc (p (j + 6)) (p (j + 7)) ⊆ Icc (x + 5 * h) (x + 7 * h) := by
      intro j hj x hx
      rcases lt_or_eq_of_le hj with hlt | heq
      · have h1 : x + 5 * h ≤ p (j + 6) := by
          have hA := hxhi_lt j hlt x hx
          have hB : p (j + 6) = p j + 6 * h := hp_add j 6
          linarith
        have h2 : p (j + 7) ≤ x + 7 * h := by
          have hA := hxlo j hj x hx
          have hB : p (j + 7) = p j + 7 * h := hp_add j 7
          linarith
        exact Icc_subset_Icc h1 h2
      · subst heq
        have h1 : x + 5 * h ≤ p (K + 6) := by
          have hA := hxhi_K x hx
          have hB : p (K + 6) = p K + 6 * h := hp_add K 6
          linarith
        have h2 : p (K + 7) ≤ x + 7 * h := by
          have hA := hxlo K le_rfl x hx
          have hB : p (K + 7) = p K + 7 * h := hp_add K 7
          linarith
        exact Icc_subset_Icc h1 h2
    set starts : Finset ℝ := ((Finset.range (K + 1)).filter good).image wfun with hstarts
    have hmem : ∀ w ∈ starts, w ∈ Icc a (b - d) ∧ f w ≤ threshold := by
      intro w hw
      rw [hstarts] at hw
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hw
      obtain ⟨hjr, hjg⟩ := Finset.mem_filter.mp hj
      have hjle : j ≤ K := Nat.lt_succ_iff.mp (Finset.mem_range.mp hjr)
      exact ⟨hcell_sub j (hwfun_spec j hjg).1, (hwfun_spec j hjg).2⟩
    refine ⟨starts, hmem, ?_, ?_, ?_⟩
    · rintro t ⟨w, hw, ht⟩
      obtain ⟨hwd, -⟩ := hmem w hw
      have h1 : a < t := by
        have h2 : a + 5 * d / 8 ≤ t := by linarith [ht.1, hwd.1]
        linarith [hd]
      have h2 : t < b := by
        have h3 : w + 7 * d / 8 ≤ b - d + 7 * d / 8 := by linarith [hwd.2]
        linarith [ht.2, h3, hd]
      exact ⟨h1, h2⟩
    · have hbad : ∀ j, ¬ good j → cell j ⊆ {v : ℝ | v ∈ Icc a b ∧ threshold < f v} := by
        intro j hnj x hx
        exact ⟨hcell_ab j hx, lt_of_not_ge (fun hle => hnj ⟨x, hx, hle⟩)⟩
      set X : Set ℝ := Icc a (p 6) with hX
      set Y : Set ℝ := Icc (p (K + 7)) b with hY
      set D : Set ℝ := Icc (p (K + 6) + r) (p (K + 7)) with hD
      set Btr : Set ℝ := (fun v : ℝ => v + 6 * h) ''
        {v : ℝ | v ∈ Icc a b ∧ threshold < f v} with hBtr
      have hvX : volume X = ENNReal.ofReal (6 * h) := by
        rw [hX, Real.volume_Icc]; congr 1
        rw [hp_apply]; push_cast; ring
      have hvY : volume Y = ENNReal.ofReal (h + r) := by
        rw [hY, Real.volume_Icc]; congr 1
        have hA : p (K + 7) = a + ((m : ℝ) - 1) * h := by
          rw [hp_add K 7, hp_apply, hKr]; push_cast; ring
        rw [hA, hr]; ring
      have hvD : volume D = ENNReal.ofReal (h - r) := by
        rw [hD, Real.volume_Icc]; congr 1
        have hA : p (K + 7) = p (K + 6) + h := by rw [hp_add K 7, hp_add K 6]; ring
        rw [hA]; ring
      have hvB : volume Btr ≤ ENNReal.ofReal (C / threshold) := by
        rw [hBtr, volume_image_add_right]; exact hMarkov
      have hfind : ∀ t : ℝ, p 6 ≤ t → t < p (K + 7) →
          ∃ j ≤ K, t ∈ Icc (p (j + 6)) (p (j + 7)) := by
        intro t ht6 htK7
        have hpa6 : a ≤ t := le_trans (hpa 6) ht6
        have hx0 : 0 ≤ (t - a) / h := div_nonneg (by linarith) hhpos.le
        set n : ℕ := ⌊(t - a) / h⌋₊ with hn
        have hgrid : t ∈ Icc (p n) (p (n + 1)) := by
          have hn_le : (n : ℝ) ≤ (t - a) / h := by
            have h := Nat.floor_le hx0; simpa [hn] using h
          have hn_lt : (t - a) / h < (n : ℝ) + 1 := by
            have h := Nat.lt_floor_add_one ((t - a) / h); simpa [hn] using h
          rw [mem_Icc, hp_apply, hp_apply]; push_cast
          constructor
          · have hA := mul_le_mul_of_nonneg_right hn_le hhpos.le
            rw [div_mul_cancel₀ _ (ne_of_gt hhpos)] at hA
            linarith
          · have hA := mul_lt_mul_of_pos_right hn_lt hhpos
            rw [div_mul_cancel₀ _ (ne_of_gt hhpos)] at hA
            linarith
        have hn6 : 6 ≤ n := by
          have hA : (6 : ℝ) ≤ (t - a) / h := by
            rw [le_div_iff₀ hhpos]
            have hB : p 6 = a + 6 * h := by rw [hp_apply]; push_cast; ring
            linarith
          simpa [hn] using Nat.le_floor hA
        have hnK : n ≤ K + 6 := by
          by_contra hcon
          have hKn : K + 7 ≤ n := by omega
          have hA : p (K + 7) ≤ p n := hp_mono hKn
          linarith [hgrid.1]
        refine ⟨n - 6, by omega, ?_⟩
        have hna : n - 6 + 6 = n := Nat.sub_add_cancel hn6
        have hnb : n - 6 + 7 = n + 1 := by omega
        rw [hna, hnb]
        exact hgrid
      have hcov : Icc a b \ goodWindowUnion starts d ⊆ (X ∪ Y ∪ D) ∪ Btr := by
        intro t ht
        obtain ⟨htab, htU⟩ := ht
        by_cases h1t : t ≤ p 6
        · exact Or.inl (Or.inl (Or.inl ⟨htab.1, h1t⟩))
        · have h1t' : p 6 < t := lt_of_not_ge h1t
          by_cases h2t : p (K + 7) ≤ t
          · exact Or.inl (Or.inl (Or.inr ⟨h2t, htab.2⟩))
          · have h2t' : t < p (K + 7) := lt_of_not_ge h2t
            obtain ⟨j, hjle, hjt⟩ := hfind t h1t'.le h2t'
            have hnj : ¬ good j := by
              intro hg
              have hspec := hwfun_spec j hg
              have hwmem : wfun j ∈ starts := by
                rw [hstarts]
                exact Finset.mem_image.mpr ⟨j,
                  Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hjle), hg⟩, rfl⟩
              have hwin : t ∈ Icc (wfun j + 5 * h) (wfun j + 7 * h) :=
                hcover j hjle (wfun j) hspec.1 hjt
              have hwin' : t ∈ Icc (wfun j + 5 * d / 8) (wfun j + 7 * d / 8) := by
                rw [h5, h7]; exact hwin
              exact htU ⟨wfun j, hwmem, hwin'⟩
            have hbj := hbad j hnj
            rcases lt_or_eq_of_le hjle with hlt | heq
            · refine Or.inr ?_
              rw [hBtr]
              have hmemcell : t - 6 * h ∈ cell j := by
                rw [hcell_lt j hlt, hp_succ j]
                rw [hp_add j 6, hp_add j 7] at hjt
                push_cast at hjt
                exact ⟨by linarith [hjt.1], by linarith [hjt.2]⟩
              exact ⟨t - 6 * h, hbj hmemcell, by ring⟩
            · subst heq
              rw [hp_add K 6, hp_add K 7] at hjt
              push_cast at hjt
              by_cases ht4 : t ≤ p K + r + 6 * h
              · refine Or.inr ?_
                rw [hBtr]
                have hmemcell : t - 6 * h ∈ cell K := by
                  rw [hcell_ge K le_rfl, hbd]
                  exact ⟨by linarith [hjt.1], by linarith [ht4]⟩
                exact ⟨t - 6 * h, hbj hmemcell, by ring⟩
              · have ht4' : p K + r + 6 * h < t := lt_of_not_ge ht4
                refine Or.inl (Or.inr ⟨?_, ?_⟩)
                · rw [hp_add K 6]; push_cast; linarith [ht4']
                · rw [hp_add K 7]; exact hjt.2
      have e1 : ENNReal.ofReal (6 * h) + ENNReal.ofReal (h + r) + ENNReal.ofReal (h - r)
          = ENNReal.ofReal d := by
        have h1 : ENNReal.ofReal (6 * h) + ENNReal.ofReal (h + r) =
            ENNReal.ofReal (6 * h + (h + r)) :=
          (ENNReal.ofReal_add (by positivity) (by linarith)).symm
        have h2 : ENNReal.ofReal (6 * h + (h + r)) + ENNReal.ofReal (h - r) =
            ENNReal.ofReal ((6 * h + (h + r)) + (h - r)) :=
          (ENNReal.ofReal_add (by linarith) (by linarith)).symm
        rw [h1, h2]
        have h3 : (6 * h + (h + r)) + (h - r) = d := by rw [← hdh]; ring
        rw [h3]
      calc volume (Icc a b \ goodWindowUnion starts d)
          ≤ volume ((X ∪ Y ∪ D) ∪ Btr) := measure_mono hcov
        _ ≤ volume (X ∪ Y ∪ D) + volume Btr := measure_union_le _ _
        _ ≤ (volume (X ∪ Y) + volume D) + volume Btr :=
            add_le_add (measure_union_le (X ∪ Y) D) le_rfl
        _ ≤ ((volume X + volume Y) + volume D) + volume Btr :=
            add_le_add (add_le_add (measure_union_le X Y) le_rfl) le_rfl
        _ ≤ ((ENNReal.ofReal (6 * h) + ENNReal.ofReal (h + r)) +
              ENNReal.ofReal (h - r)) + ENNReal.ofReal (C / threshold) := by
            refine add_le_add (add_le_add (add_le_add ?_ ?_) ?_) ?_
            · rw [hvX]
            · rw [hvY]
            · rw [hvD]
            · exact hvB
        _ = ENNReal.ofReal d + ENNReal.ofReal (C / threshold) := by rw [e1]
        _ = ENNReal.ofReal (d + C / threshold) := hof.symm
    · intro w hw t ht
      exact ⟨by linarith [hd, ht.1], by linarith [hd, ht.2]⟩

theorem rfs_finite_good_windows (B : RicciBackground (I := I) (M := Q) D a b)
    (L₀ Theta₀ : ℝ) (K : CurveShorteningRegularityInput B L₀ Theta₀) :
    let delta := localRegularityDelta B L₀ Theta₀ K
    let r₀ := localRegularityRadius B L₀ Theta₀ K
    let areg := localRegularityCoefficient B L₀ Theta₀ K 0
    let C_E := Real.exp (B.B₀ * (b - a)) * L₀
    ∀ ell threshold : ℝ, 0 < ell → 0 < threshold →
      let r := min r₀ (min (ell / 2) (delta ^ 2 / threshold))
      let d := delta * r ^ 2
      d < b - a →
      ∀ lambda : ℝ, 0 < lambda → lambda ≤ 1 → ∀ c : ProductCurve Q,
        c.IsSolutionOn B.family.metric lambda (Icc a b) →
        c.IsRampOn B.family.metric lambda (Icc a b) → c.degree = 1 →
        c.length B.family.metric lambda a ≤ L₀ →
        c.totalCurvature B.family.metric lambda a ≤ Theta₀ →
        (∀ t ∈ Icc a b, ell ≤ c.length B.family.metric lambda t) →
        ∃ starts : Finset ℝ,
          (∀ w ∈ starts, w ∈ Icc a (b - d) ∧ c.energy B.family.metric lambda w ≤ threshold) ∧
          goodWindowUnion starts d ⊆ Ioo a b ∧
          volume (Icc a b \ goodWindowUnion starts d) ≤ ENNReal.ofReal (d + C_E / threshold) ∧
          (∀ x t, t ∈ goodWindowUnion starts d →
            c.curvature B.family.metric lambda x t ≤ Real.sqrt (2 * areg / d)) ∧
          ∀ w ∈ starts, Icc (w + 5 * d / 8) (w + 7 * d / 8) ⊆ Ioo (w + d / 2) (w + d) := by
  sorry

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [TopologicalSpace H] [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
  hT2 hCompact hConnected hBoundary in
theorem le_of_lipschitz_integral_bound {u : ℝ → ℝ} {L K lam : ℝ} (hL : 0 < L) (hK : 0 < K)
    (hcont : ContinuousOn u (Icc (0 : ℝ) L))
    (hnonneg : ∀ s ∈ Icc (0 : ℝ) L, 0 ≤ u s)
    (hlip : ∀ s ∈ Icc (0 : ℝ) L, u 0 - K * s ≤ u s)
    (hint : (∫ s in (0 : ℝ)..L, u s) = lam) :
    u 0 ≤ 2 * lam / L + 2 * Real.sqrt (K * lam) := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) L := ⟨le_rfl, hL.le⟩
  have hlam : 0 ≤ lam := by
    rw [← hint]
    exact intervalIntegral.integral_nonneg hL.le fun s hs => hnonneg s hs
  have ha : 0 ≤ u 0 := hnonneg 0 h0
  have hUi : IntervalIntegrable u volume (0 : ℝ) L := hcont.intervalIntegrable_of_Icc hL.le
  have hsqrt : 0 ≤ Real.sqrt (K * lam) := Real.sqrt_nonneg _
  rcases eq_or_lt_of_le ha with hzero | hapos
  · have hdiv : 0 ≤ 2 * lam / L := div_nonneg (by linarith) hL.le
    rw [← hzero]
    linarith
  rcases lt_or_ge (K * L) (u 0) with hcase | hcase
  · have hcalc : (∫ s in (0 : ℝ)..L, (u 0 - K * s)) = u 0 * L - K * (L ^ 2 / 2) := by
      have h1 : (∫ s in (0 : ℝ)..L, (u 0 : ℝ)) = u 0 * L := by
        rw [intervalIntegral.integral_const]
        simp only [sub_zero, smul_eq_mul]
        ring
      have h2 : (∫ s in (0 : ℝ)..L, K * s) = K * (L ^ 2 / 2) := by
        rw [intervalIntegral.integral_const_mul, integral_id]
        ring
      rw [intervalIntegral.integral_sub (f := fun _ : ℝ => u 0) (g := fun s : ℝ => K * s)
          intervalIntegrable_const ((continuous_const.mul continuous_id).intervalIntegrable _ _),
        h1, h2]
    have hlow : u 0 * L - K * (L ^ 2 / 2) ≤ lam := by
      rw [← hcalc, ← hint]
      exact intervalIntegral.integral_mono_on hL.le
        ((continuous_const.sub (continuous_const.mul continuous_id)).intervalIntegrable _ _)
        hUi fun s hs => hlip s hs
    have hkey : u 0 ≤ lam / L + K * L / 2 := by
      have hsplit : lam / L + K * L / 2 = (lam + K * (L ^ 2 / 2)) / L := by
        field_simp
      rw [hsplit, le_div_iff₀ hL]
      linarith
    have hbig : K * L / 2 < lam / L := by
      rw [lt_div_iff₀ hL]
      nlinarith [hlow, hcase]
    have hterm : u 0 ≤ 2 * lam / L := by
      have htwo : lam / L + lam / L = 2 * lam / L := by ring
      linarith
    linarith [hterm, hsqrt]
  · set s₀ : ℝ := u 0 / K with hs₀def
    have hs₀pos : 0 < s₀ := by
      rw [hs₀def]
      exact div_pos hapos hK
    have hs₀le : s₀ ≤ L := by
      rw [hs₀def, div_le_iff₀ hK]
      linarith
    have hcont' : ContinuousOn u (Icc (0 : ℝ) s₀) := hcont.mono (Icc_subset_Icc le_rfl hs₀le)
    have hcalc : (∫ s in (0 : ℝ)..s₀, (u 0 - K * s)) = u 0 ^ 2 / (2 * K) := by
      have h1 : (∫ s in (0 : ℝ)..s₀, (u 0 : ℝ)) = u 0 * s₀ := by
        rw [intervalIntegral.integral_const]
        simp only [sub_zero, smul_eq_mul]
        ring
      have h2 : (∫ s in (0 : ℝ)..s₀, K * s) = K * (s₀ ^ 2 / 2) := by
        rw [intervalIntegral.integral_const_mul, integral_id]
        ring
      rw [intervalIntegral.integral_sub (f := fun _ : ℝ => u 0) (g := fun s : ℝ => K * s)
          intervalIntegrable_const ((continuous_const.mul continuous_id).intervalIntegrable _ _),
        h1, h2, hs₀def]
      field_simp
      ring
    have hle1 : (∫ s in (0 : ℝ)..s₀, (u 0 - K * s)) ≤ ∫ s in (0 : ℝ)..s₀, u s :=
      intervalIntegral.integral_mono_on hs₀pos.le
        ((continuous_const.sub (continuous_const.mul continuous_id)).intervalIntegrable _ _)
        (hcont'.intervalIntegrable_of_Icc hs₀pos.le)
        fun s hs => hlip s ⟨hs.1, hs.2.trans hs₀le⟩
    have hle2 : (∫ s in (0 : ℝ)..s₀, u s) ≤ ∫ s in (0 : ℝ)..L, u s := by
      have hsplit : (∫ s in (0 : ℝ)..s₀, u s) + (∫ s in s₀..L, u s) =
          ∫ s in (0 : ℝ)..L, u s :=
        intervalIntegral.integral_add_adjacent_intervals
          (hcont'.intervalIntegrable_of_Icc hs₀pos.le)
          ((hcont.mono (Icc_subset_Icc hs₀pos.le le_rfl)).intervalIntegrable_of_Icc hs₀le)
      have hnn : 0 ≤ ∫ s in s₀..L, u s :=
        intervalIntegral.integral_nonneg hs₀le fun s hs => hnonneg s ⟨hs₀pos.le.trans hs.1, hs.2⟩
      linarith
    have hkey : u 0 ^ 2 ≤ 2 * K * lam := by
      have h := hle1.trans hle2
      rw [hint, hcalc] at h
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < 2 * K)] at h
      linarith
    have hstep : u 0 ≤ Real.sqrt (2 * K * lam) :=
      (Real.le_sqrt (by linarith) (by positivity)).mpr hkey
    have hmono : Real.sqrt (2 * K * lam) ≤ Real.sqrt (4 * (K * lam)) := by
      apply Real.sqrt_le_sqrt
      nlinarith [hK, hlam]
    have hfour : Real.sqrt (4 * (K * lam)) = 2 * Real.sqrt (K * lam) := by
      have hsq : (4 : ℝ) = 2 ^ 2 := by norm_num
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), hsq,
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
    have hterm : 0 ≤ 2 * lam / L := div_nonneg (by linarith) hL.le
    linarith [hstep, hmono, hfour.le, hterm]

end DifferentialGeometry.PDE.RicciFlow.Extinction.Families
