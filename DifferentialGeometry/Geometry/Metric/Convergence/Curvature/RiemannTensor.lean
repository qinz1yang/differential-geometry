import DifferentialGeometry.Geometry.Metric.Convergence.Curvature.CoordinateBounds
import DifferentialGeometry.Topology.UniformConvergence

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature

open scoped Manifold ContDiff Topology BigOperators Matrix

open CheegerGromovCompactness Geometry.Operator Tensor.Coordinates Filter
open Geometry.Connection (chartChristoffelBracket chartChristoffelBracketDeriv)
open Analysis.Calculus Analysis.Spectral.DeTurckCoefficients
open Integral.DivergenceTheorem Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]

private lemma chartGram_partial_bound_riem
    (gRef : SmoothRiemannianMetric I M) (α : M)
    {K : Set M} (hK : IsCompact K)
    (hKchart : K ⊆ (chartAt H α).source)
    (B : Real) :
    ∃ Q : Real, 0 ≤ Q ∧ ∀ w : SmoothRiemannianMetric I M,
      (∀ y ∈ K, ∀ a : ℕ, a ≤ 2 →
        metricCovDerivNorm (I := I) a w gRef y ≤ B) →
      ∀ y ∈ K,
        (∀ m a b : Fin (Module.finrank Real E),
          |partialDeriv (E := E) m (chartGramOnE (I := I) w α a b)
            (extChartAt I α y)| ≤ Q) ∧
        (∀ d m a b : Fin (Module.finrank Real E),
          |partialDeriv (E := E) d
            (partialDeriv (E := E) m (chartGramOnE (I := I) w α a b))
              (extChartAt I α y)| ≤ Q) := by
  classical
  let 𝓖 := {w : SmoothRiemannianMetric I M //
    ∀ y ∈ K, ∀ a : ℕ, a ≤ 2 → metricCovDerivNorm (I := I) a w gRef y ≤ B}
  let gFam : 𝓖 → SmoothRiemannianMetric I M := fun w => w.1
  have hbdd : ∀ q : ℕ, q ≤ 2 → ∃ C : Real, ∀ k : 𝓖, ∀ y ∈ K,
      metricCovDerivNorm (I := I) q (gFam k) gRef y ≤ C := by
    intro q hq
    exact ⟨B, fun k y hy => k.2 y hy q hq⟩
  obtain ⟨Q1, hQ10, hQ1⟩ := chartGram_iter_le (I := I) gRef gFam α hK hKchart 1
    (fun q hq => hbdd q (by omega))
  obtain ⟨Q2, hQ20, hQ2⟩ := chartGram_iter_le (I := I) gRef gFam α hK hKchart 2 hbdd
  set V : Real := ∑ a : Fin (Module.finrank Real E), ‖(chartModelBasis E) a‖ with hV
  have hV0 : 0 ≤ V := Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine ⟨max (Q1 * V) (Q2 * V ^ 2),
    le_max_of_le_left (mul_nonneg hQ10 hV0), ?_⟩
  intro w hw y hy
  let k : 𝓖 := ⟨w, hw⟩
  constructor
  · intro m a b
    let f : E → Real := chartGramOnE (I := I) w α a b
    have happ := (iteratedFDeriv ℝ 1 f (extChartAt I α y)).le_opNorm_mul_pow_of_le
        (b := V) (m := fun i : Fin 1 => (chartModelBasis E) (![m] i))
        ((pi_norm_le_iff_of_nonneg hV0).mpr fun i =>
          Finset.single_le_sum (fun a _ => norm_nonneg ((chartModelBasis E) a))
            (Finset.mem_univ (![m] i)))
    rw [Real.norm_eq_abs] at happ
    have heval : iteratedFDeriv Real 1 f (extChartAt I α y)
          ![(chartModelBasis E) m] = partialDeriv (E := E) m f (extChartAt I α y) := by
      rw [partialDeriv_eq_iteratedFDeriv_one]
    have hargs : (fun i : Fin 1 => (chartModelBasis E) (![m] i)) =
        ![(chartModelBasis E) m] := by
      funext i
      fin_cases i
      rfl
    rw [hargs, heval, pow_one] at happ
    exact happ.trans <| (mul_le_mul_of_nonneg_right (hQ1 k y hy a b) hV0).trans <|
      le_max_left _ _
  · intro d m a b
    let f : E → Real := chartGramOnE (I := I) w α a b
    have hyint : extChartAt I α y ∈ interior (extChartAt I α).target := by
      rw [(isOpen_extChartAt_target (I := I) α).interior_eq]
      exact (extChartAt I α).map_source (by rw [extChartAt_source]; exact hKchart hy)
    have hf : ContDiffAt Real ∞ f (extChartAt I α y) :=
      ((chartGramOnE_contDiffOn (I := I) w α a b).mono interior_subset).contDiffAt
        (isOpen_interior.mem_nhds hyint)
    have happ := (iteratedFDeriv ℝ 2 f (extChartAt I α y)).le_opNorm_mul_pow_of_le
        (b := V) (m := fun i : Fin 2 => (chartModelBasis E) (![d, m] i))
        ((pi_norm_le_iff_of_nonneg hV0).mpr fun i =>
          Finset.single_le_sum (fun a _ => norm_nonneg ((chartModelBasis E) a))
            (Finset.mem_univ (![d, m] i)))
    rw [Real.norm_eq_abs] at happ
    have heval : iteratedFDeriv Real 2 f (extChartAt I α y)
          ![(chartModelBasis E) d, (chartModelBasis E) m] =
        partialDeriv (E := E) d (partialDeriv (E := E) m f) (extChartAt I α y) := by
      rw [partialDeriv_partialDeriv_eq_iteratedFDeriv_two f hf d m]
    have hargs : (fun i : Fin 2 => (chartModelBasis E) (![d, m] i)) =
        ![(chartModelBasis E) d, (chartModelBasis E) m] := by
      funext i
      fin_cases i <;> rfl
    rw [hargs, heval] at happ
    exact happ.trans <| (mul_le_mul_of_nonneg_right (hQ2 k y hy a b) (sq_nonneg V)).trans <|
      le_max_right _ _

theorem exists_abs_chartRiemannTensor_sub_le
    (gRef : SmoothRiemannianMetric I M) (α : M)
    {K : Set M} (hK : IsCompact K)
    (hKchart : K ⊆ (chartAt H α).source)
    (lam B : Real) (hlam : 0 < lam) :
    ∃ C : Real, 0 < C ∧ ∀ u u' : SmoothRiemannianMetric I M,
      (∀ y ∈ K, ∀ ξ : TangentSpace I y,
        lam * gRef.inner y ξ ξ ≤ u.inner y ξ ξ) →
      (∀ y ∈ K, ∀ ξ : TangentSpace I y,
        lam * gRef.inner y ξ ξ ≤ u'.inner y ξ ξ) →
      (∀ y ∈ K, ∀ a : ℕ, a ≤ 2 →
        metricCovDerivNorm (I := I) a u gRef y ≤ B) →
      (∀ y ∈ K, ∀ a : ℕ, a ≤ 2 →
        metricCovDerivNorm (I := I) a u' gRef y ≤ B) →
      ∀ y ∈ K, ∀ i j k l : Fin (Module.finrank Real E),
        |chartRiemannTensor (I := I) u α i j k l (extChartAt I α y) -
          chartRiemannTensor (I := I) u' α i j k l (extChartAt I α y)| ≤
        C * ∑ q ∈ Finset.range 3, metricDerivNorm (I := I) q u u' gRef y := by
  classical
  obtain ⟨Q, hQ0, hQ⟩ := chartGram_partial_bound_riem (I := I) gRef α hK hKchart B
  obtain ⟨Mb, hMb0, hMb⟩ := exists_abs_chartInvGramMatrix_le_of_lower_bound (I := I) gRef α hK
    (by rwa [trivializationAt_baseSet_eq_chartAt_source]) lam hlam
  obtain ⟨CJ, hCJ0, hCJ⟩ := exists_chartMetricJet2DiffSup_le (I := I) gRef α hK hKchart
  set nR : Real := (Module.finrank Real E : Real) with hnR
  have hnR0 : 0 ≤ nR := Nat.cast_nonneg _
  set P : Real := 3 * Q with hP
  have hP0 : 0 ≤ P := by rw [hP]; positivity
  set R : Real := 3 * Q with hR
  have hR0 : 0 ≤ R := by rw [hR]; positivity
  set Cinv : Real := nR ^ 2 * Mb ^ 2 with hCinv
  have hCinv0 : 0 ≤ Cinv := by rw [hCinv]; positivity
  set D : Real := nR ^ 2 * Mb ^ 2 * Q with hD
  have hD0 : 0 ≤ D := by rw [hD]; positivity
  set Cd : Real := nR ^ 2 * (2 * Cinv * Mb * Q + Mb ^ 2) with hCd
  have hCd0 : 0 ≤ Cd := by rw [hCd]; positivity
  set Clip : Real := (1 / 2) * nR * (Cinv * P + 3 * Mb) with hClip
  have hClip0 : 0 ≤ Clip := by rw [hClip]; positivity
  set Cdiff : Real := (1 / 2) * nR * (Cd * P + 3 * D + Cinv * R + 3 * Mb) with hCdiff
  have hCdiff0 : 0 ≤ Cdiff := by rw [hCdiff]; positivity
  set Mg : Real := (1 / 2) * nR * Mb * P with hMg
  have hMg0 : 0 ≤ Mg := by rw [hMg]; positivity
  set Cr : Real := 2 * Cdiff + 4 * nR * Clip * Mg with hCr
  have hCr0 : 0 ≤ Cr := by rw [hCr]; positivity
  refine ⟨Cr * CJ + 1, by positivity, ?_⟩
  intro u u' hlowu hlowu' hcovu hcovu' y hy i j k l
  set z : E := extChartAt I α y with hz
  have hψ : (extChartAt I α).symm z = y := by
    rw [hz]
    exact (extChartAt I α).left_inv (by rw [extChartAt_source]; exact hKchart hy)
  have hybase : y ∈ (trivializationAt E (TangentSpace I : M → Type _) α).baseSet := by
    rw [DifferentialGeometry.Integral.Measure.trivializationAt_baseSet_eq_chartAt_source]
    exact hKchart hy
  have hzint : z ∈ interior (extChartAt I α).target := by
    rw [(isOpen_extChartAt_target (I := I) α).interior_eq, hz]
    exact (extChartAt I α).map_source (by rw [extChartAt_source]; exact hKchart hy)
  have hQu := (hQ u hcovu y hy).1
  have hQu' := (hQ u' hcovu' y hy).1
  have hQQu := (hQ u hcovu y hy).2
  have hMbu : ∀ a b : Fin (Module.finrank Real E),
      |chartInvGramOnE (I := I) u α a b z| ≤ Mb := by
    intro a b
    rw [chartInvGramOnE_def, hψ]
    exact hMb y hy u (hlowu y hy) a b
  have hMbu' : ∀ a b : Fin (Module.finrank Real E),
      |chartInvGramOnE (I := I) u' α a b z| ≤ Mb := by
    intro a b
    rw [chartInvGramOnE_def, hψ]
    exact hMb y hy u' (hlowu' y hy) a b
  have hCinv' : ∀ a b : Fin (Module.finrank Real E),
      |chartInvGramOnE (I := I) u α a b z - chartInvGramOnE (I := I) u' α a b z| ≤
        Cinv * chartGramDiffSup (I := I) (M := M) u u' α ((extChartAt I α).symm z) := by
    intro a b
    rw [chartInvGramOnE_def, chartInvGramOnE_def, hψ]
    have h := chartInvGramMatrix_entry_sub_abs_le_gramDiffSup (I := I) (M := M)
      u u' α hybase
      (fun p q => hMb y hy u (hlowu y hy) p q)
      (fun p q => hMb y hy u' (hlowu' y hy) p q) a b
    rw [hCinv, hnR]
    exact h
  have hPu : ∀ a b c : Fin (Module.finrank Real E),
      |chartChristoffelBracket (I := I) u α a b c z| ≤ P := by
    intro a b c
    rw [hP]
    exact chartChristoffelBracket_abs_le (I := I) (M := M) u α z hQu a b c
  have hPu' : ∀ a b c : Fin (Module.finrank Real E),
      |chartChristoffelBracket (I := I) u' α a b c z| ≤ P := by
    intro a b c
    rw [hP]
    exact chartChristoffelBracket_abs_le (I := I) (M := M) u' α z hQu' a b c
  have hRu : ∀ d a b c : Fin (Module.finrank Real E),
      |chartChristoffelBracketDeriv (I := I) u α d a b c z| ≤ R := by
    intro d a b c
    rw [hR]
    exact chartChristoffelBracketDeriv_abs_le (I := I) (M := M) u α z hQQu d a b c
  have hDu' : ∀ d a b : Fin (Module.finrank Real E),
      |partialDeriv (E := E) d (chartInvGramOnE (I := I) u' α a b) z| ≤ D := by
    intro d a b
    have h := invGramD_abs_le (I := I) (M := M) u' α hzint hMb0 hMbu' hQu' d a b
    rw [hD, hnR]
    exact h
  have hCd' : ∀ d a b : Fin (Module.finrank Real E),
      |partialDeriv (E := E) d (chartInvGramOnE (I := I) u α a b) z -
        partialDeriv (E := E) d (chartInvGramOnE (I := I) u' α a b) z| ≤
        Cd * chartMetricJet1DiffSup (I := I) (M := M) u u' α z := by
    intro d a b
    have h := partialDeriv_chartInvGramOnE_sub_abs_le (I := I) (M := M)
      u u' α hzint hMb0 hQ0 hCinv0 hMbu hMbu' hQu hCinv' d a b
    rw [hCd, hCinv, hnR]
    exact h
  have hClip' : ∀ a b c : Fin (Module.finrank Real E),
      |chartChristoffel (I := I) u α a b c z -
        chartChristoffel (I := I) u' α a b c z| ≤
        Clip * chartMetricJet1DiffSup (I := I) (M := M) u u' α z := by
    intro a b c
    have h := chartChristoffel_sub_abs_le (I := I) (M := M)
      u u' α hP0 hMb0 hMbu' hPu hCinv' hCinv0 a b c
    rw [hClip, hnR]
    exact h
  have hCdiff' : ∀ d a b c : Fin (Module.finrank Real E),
      |partialDeriv (E := E) d (chartChristoffel (I := I) u α a b c) z -
        partialDeriv (E := E) d (chartChristoffel (I := I) u' α a b c) z| ≤
        Cdiff * chartMetricJet2DiffSup (I := I) (M := M) u u' α z := by
    intro d a b c
    have h := partialDeriv_chartChristoffel_sub_abs_le (I := I) (M := M)
      u u' α hzint hCd0 hCinv0 hMb0 hP0 hD0 hR0 d a b c
      (fun p q => hCd' d p q) hMbu' hPu (fun p q => hDu' d p q)
      (fun p q r => hRu d p q r) hCinv'
    rw [hCdiff, hCd, hCinv, hD, hR, hnR]
    exact h
  have hMgu : ∀ a b c : Fin (Module.finrank Real E),
      |chartChristoffel (I := I) u α a b c z| ≤ Mg := by
    intro a b c
    have h := christoffel_abs_le (I := I) (M := M) u α z a b c hMb0
      (fun l => hMbu c l) (fun l => hPu a b l)
    rw [hMg, hnR]
    exact h
  have hMgu' : ∀ a b c : Fin (Module.finrank Real E),
      |chartChristoffel (I := I) u' α a b c z| ≤ Mg := by
    intro a b c
    have h := christoffel_abs_le (I := I) (M := M) u' α z a b c hMb0
      (fun l => hMbu' c l) (fun l => hPu' a b l)
    rw [hMg, hnR]
    exact h
  have hD1 := hCdiff' j i k l
  have hD2 := hCdiff' k i j l
  set jet2 : Real := chartMetricJet2DiffSup (I := I) (M := M) u u' α z with hjet
  have hjet0 : 0 ≤ jet2 := chartMetricJet2DiffSup_nonneg _ _ _ _
  have hjet1 : chartMetricJet1DiffSup (I := I) (M := M) u u' α z ≤ jet2 :=
    chartMetricJet1DiffSup_le_jet2 (I := I) (M := M) u u' α z
  have hjet10 : 0 ≤ chartMetricJet1DiffSup (I := I) (M := M) u u' α z :=
    chartMetricJet1DiffSup_nonneg _ _ _ _
  have hsum : ∀ m : Fin (Module.finrank Real E),
      |chartChristoffel (I := I) u α j m l z * chartChristoffel (I := I) u α i k m z -
          chartChristoffel (I := I) u' α j m l z * chartChristoffel (I := I) u' α i k m z| +
        |chartChristoffel (I := I) u α k m l z * chartChristoffel (I := I) u α i j m z -
          chartChristoffel (I := I) u' α k m l z * chartChristoffel (I := I) u' α i j m z|
        ≤ (4 * Clip * Mg) * jet2 := by
    intro m
    have hb1 : |chartChristoffel (I := I) u α j m l z -
          chartChristoffel (I := I) u' α j m l z| ≤ Clip * jet2 :=
      (hClip' j m l).trans (mul_le_mul_of_nonneg_left hjet1 hClip0)
    have hb2 : |chartChristoffel (I := I) u α i k m z -
          chartChristoffel (I := I) u' α i k m z| ≤ Clip * jet2 :=
      (hClip' i k m).trans (mul_le_mul_of_nonneg_left hjet1 hClip0)
    have hb3 : |chartChristoffel (I := I) u α k m l z -
          chartChristoffel (I := I) u' α k m l z| ≤ Clip * jet2 :=
      (hClip' k m l).trans (mul_le_mul_of_nonneg_left hjet1 hClip0)
    have hb4 : |chartChristoffel (I := I) u α i j m z -
          chartChristoffel (I := I) u' α i j m z| ≤ Clip * jet2 :=
      (hClip' i j m).trans (mul_le_mul_of_nonneg_left hjet1 hClip0)
    have ht1 : |chartChristoffel (I := I) u α j m l z * chartChristoffel (I := I) u α i k m z -
          chartChristoffel (I := I) u' α j m l z * chartChristoffel (I := I) u' α i k m z|
        ≤ Clip * jet2 * Mg + Mg * (Clip * jet2) := by
      have hsplit :
          chartChristoffel (I := I) u α j m l z * chartChristoffel (I := I) u α i k m z -
            chartChristoffel (I := I) u' α j m l z * chartChristoffel (I := I) u' α i k m z =
          (chartChristoffel (I := I) u α j m l z - chartChristoffel (I := I) u' α j m l z) *
              chartChristoffel (I := I) u α i k m z +
            chartChristoffel (I := I) u' α j m l z *
              (chartChristoffel (I := I) u α i k m z - chartChristoffel (I := I) u' α i k m z) := by
        ring
      rw [hsplit]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul]
      exact add_le_add
        (mul_le_mul hb1 (hMgu i k m) (abs_nonneg _) (mul_nonneg hClip0 hjet0))
        (mul_le_mul (hMgu' j m l) hb2 (abs_nonneg _) hMg0)
    have ht2 : |chartChristoffel (I := I) u α k m l z * chartChristoffel (I := I) u α i j m z -
          chartChristoffel (I := I) u' α k m l z * chartChristoffel (I := I) u' α i j m z|
        ≤ Clip * jet2 * Mg + Mg * (Clip * jet2) := by
      have hsplit :
          chartChristoffel (I := I) u α k m l z * chartChristoffel (I := I) u α i j m z -
            chartChristoffel (I := I) u' α k m l z * chartChristoffel (I := I) u' α i j m z =
          (chartChristoffel (I := I) u α k m l z - chartChristoffel (I := I) u' α k m l z) *
              chartChristoffel (I := I) u α i j m z +
            chartChristoffel (I := I) u' α k m l z *
              (chartChristoffel (I := I) u α i j m z - chartChristoffel (I := I) u' α i j m z) := by
        ring
      rw [hsplit]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul]
      exact add_le_add
        (mul_le_mul hb3 (hMgu i j m) (abs_nonneg _) (mul_nonneg hClip0 hjet0))
        (mul_le_mul (hMgu' k m l) hb4 (abs_nonneg _) hMg0)
    have hCM : Clip * jet2 * Mg + Mg * (Clip * jet2) = (2 * Clip * Mg) * jet2 := by ring
    linarith [ht1, ht2, hCM]
  have hRm : |chartRiemannTensor (I := I) u α i j k l z -
      chartRiemannTensor (I := I) u' α i j k l z| ≤ Cr * jet2 := by
    rw [chartRiemannTensor_def, chartRiemannTensor_def]
    set Au : ℝ := partialDeriv (E := E) j (chartChristoffel (I := I) u α i k l) z with hAu
    set Bu : ℝ := partialDeriv (E := E) k (chartChristoffel (I := I) u α i j l) z with hBu
    set Su : ℝ := ∑ m : Fin (Module.finrank Real E),
      (chartChristoffel (I := I) u α j m l z * chartChristoffel (I := I) u α i k m z -
        chartChristoffel (I := I) u α k m l z * chartChristoffel (I := I) u α i j m z) with hSu
    set Au' : ℝ := partialDeriv (E := E) j (chartChristoffel (I := I) u' α i k l) z with hAu'
    set Bu' : ℝ := partialDeriv (E := E) k (chartChristoffel (I := I) u' α i j l) z with hBu'
    set Su' : ℝ := ∑ m : Fin (Module.finrank Real E),
      (chartChristoffel (I := I) u' α j m l z * chartChristoffel (I := I) u' α i k m z -
        chartChristoffel (I := I) u' α k m l z * chartChristoffel (I := I) u' α i j m z) with hSu'
    have hD1' : |Au - Au'| ≤ Cdiff * jet2 := by rw [hAu, hAu']; exact hD1
    have hD2' : |Bu - Bu'| ≤ Cdiff * jet2 := by rw [hBu, hBu']; exact hD2
    have hSub : |Su - Su'| ≤ (4 * nR * Clip * Mg) * jet2 := by
      rw [hSu, hSu']
      rw [← Finset.sum_sub_distrib]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have hstep : ∀ m ∈ (Finset.univ : Finset (Fin (Module.finrank Real E))),
          |(chartChristoffel (I := I) u α j m l z * chartChristoffel (I := I) u α i k m z -
                chartChristoffel (I := I) u α k m l z * chartChristoffel (I := I) u α i j m z) -
              (chartChristoffel (I := I) u' α j m l z * chartChristoffel (I := I) u' α i k m z -
                chartChristoffel (I := I) u' α k m l z * chartChristoffel (I := I) u' α i j m z)|
            ≤ (4 * Clip * Mg) * jet2 := by
        intro m _
        set aa : ℝ := chartChristoffel (I := I) u α j m l z *
          chartChristoffel (I := I) u α i k m z with haa
        set bb : ℝ := chartChristoffel (I := I) u α k m l z *
          chartChristoffel (I := I) u α i j m z with hbb
        set cc : ℝ := chartChristoffel (I := I) u' α j m l z *
          chartChristoffel (I := I) u' α i k m z with hcc
        set dd : ℝ := chartChristoffel (I := I) u' α k m l z *
          chartChristoffel (I := I) u' α i j m z with hdd
        have hsplit : (aa - bb) - (cc - dd) = (aa - cc) - (bb - dd) := by ring
        have hneg : (aa - cc) - (bb - dd) = (aa - cc) + -(bb - dd) := by ring
        rw [hsplit, hneg]
        exact ((abs_add_le (aa - cc) (-(bb - dd))).trans_eq (by rw [abs_neg])).trans (hsum m)
      refine (Finset.sum_le_sum hstep).trans ?_
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hc : ((Module.finrank Real E : ℝ)) * ((4 * Clip * Mg) * jet2) =
          (4 * nR * Clip * Mg) * jet2 := by rw [hnR]; ring
      linarith [hc.le]
    have hEq : (Au - Bu + Su) - (Au' - Bu' + Su') =
        (Au - Au') - (Bu - Bu') + (Su - Su') := by ring
    rw [hEq]
    calc |(Au - Au') - (Bu - Bu') + (Su - Su')|
        ≤ |(Au - Au') - (Bu - Bu')| + |Su - Su'| := abs_add_le _ _
      _ ≤ (|Au - Au'| + |Bu - Bu'|) + |Su - Su'| := by
          have h : |(Au - Au') - (Bu - Bu')| ≤ |Au - Au'| + |Bu - Bu'| := by
            have hneg : (Au - Au') - (Bu - Bu') = (Au - Au') + -(Bu - Bu') := by ring
            rw [hneg]
            exact (abs_add_le (Au - Au') (-(Bu - Bu'))).trans_eq (by rw [abs_neg])
          linarith
      _ ≤ (Cdiff * jet2 + Cdiff * jet2) + (4 * nR * Clip * Mg) * jet2 := by
          linarith [hD1', hD2', hSub]
      _ = Cr * jet2 := by rw [hCr]; ring
  set S : Real := ∑ q ∈ Finset.range 3, metricDerivNorm (I := I) q u u' gRef y with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _
  have hjet_le : jet2 ≤ CJ * S := by
    rw [hjet, hz]
    exact hCJ u u' y hy
  calc
    |chartRiemannTensor (I := I) u α i j k l (extChartAt I α y) -
        chartRiemannTensor (I := I) u' α i j k l (extChartAt I α y)|
        = |chartRiemannTensor (I := I) u α i j k l z -
            chartRiemannTensor (I := I) u' α i j k l z| := by rw [hz]
    _ ≤ Cr * jet2 := hRm
    _ ≤ Cr * (CJ * S) := mul_le_mul_of_nonneg_left hjet_le hCr0
    _ ≤ (Cr * CJ + 1) * S := by nlinarith

omit [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private theorem chartRiemannTensor_abs_le
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j k l : Fin (Module.finrank Real E)) {z : E}
    {Mg Md : Real} (hMg0 : 0 ≤ Mg)
    (hMg : ∀ a b c : Fin (Module.finrank Real E),
      |chartChristoffel (I := I) g α a b c z| ≤ Mg)
    (hMd : ∀ d a b c : Fin (Module.finrank Real E),
      |partialDeriv (E := E) d (chartChristoffel (I := I) g α a b c) z| ≤ Md) :
    |chartRiemannTensor (I := I) g α i j k l z| ≤
      2 * Md + 2 * (Module.finrank Real E : Real) * Mg ^ 2 := by
  classical
  rw [chartRiemannTensor_def]
  have h1 : |partialDeriv (E := E) j (chartChristoffel (I := I) g α i k l) z -
      partialDeriv (E := E) k (chartChristoffel (I := I) g α i j l) z| ≤ Md + Md := by
    have hneg : partialDeriv (E := E) j (chartChristoffel (I := I) g α i k l) z -
        partialDeriv (E := E) k (chartChristoffel (I := I) g α i j l) z =
        partialDeriv (E := E) j (chartChristoffel (I := I) g α i k l) z +
          -(partialDeriv (E := E) k (chartChristoffel (I := I) g α i j l) z) := by ring
    rw [hneg]
    exact (abs_add_le _ _).trans (add_le_add (hMd j i k l) (by rw [abs_neg]; exact hMd k i j l))
  have h2 : |∑ m : Fin (Module.finrank Real E),
      (chartChristoffel (I := I) g α j m l z * chartChristoffel (I := I) g α i k m z -
        chartChristoffel (I := I) g α k m l z * chartChristoffel (I := I) g α i j m z)| ≤
      (Module.finrank Real E : Real) * (2 * Mg * Mg) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ m ∈ (Finset.univ : Finset (Fin (Module.finrank Real E))),
        |chartChristoffel (I := I) g α j m l z * chartChristoffel (I := I) g α i k m z -
          chartChristoffel (I := I) g α k m l z * chartChristoffel (I := I) g α i j m z| ≤
          2 * Mg * Mg := by
      intro m _
      have hneg : chartChristoffel (I := I) g α j m l z * chartChristoffel (I := I) g α i k m z -
          chartChristoffel (I := I) g α k m l z * chartChristoffel (I := I) g α i j m z =
          chartChristoffel (I := I) g α j m l z * chartChristoffel (I := I) g α i k m z +
            -(chartChristoffel (I := I) g α k m l z *
              chartChristoffel (I := I) g α i j m z) := by
        ring
      rw [hneg]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_neg, abs_mul]
      exact (add_le_add
        (mul_le_mul (hMg j m l) (hMg i k m) (abs_nonneg _) hMg0)
        (mul_le_mul (hMg k m l) (hMg i j m) (abs_nonneg _) hMg0)).trans (le_of_eq (by ring))
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hmain := (abs_add_le _ _).trans (add_le_add h1 h2)
  have hb : Md + Md ≤ 2 * Md := by linarith
  have hc : (Module.finrank Real E : Real) * (2 * Mg * Mg) =
      2 * (Module.finrank Real E : Real) * Mg ^ 2 := by
    ring
  linarith [hmain, hb, hc.le, hc.ge]

theorem exists_abs_chartRiemannTensor_le
    (gRef : SmoothRiemannianMetric I M) (α : M)
    {K : Set M} (hK : IsCompact K)
    (hKchart : K ⊆ (chartAt H α).source)
    (lam B : Real) (hlam : 0 < lam) :
    ∃ C : Real, 0 ≤ C ∧ ∀ u : SmoothRiemannianMetric I M,
      (∀ y ∈ K, ∀ ξ : TangentSpace I y,
        lam * gRef.inner y ξ ξ ≤ u.inner y ξ ξ) →
      (∀ y ∈ K, ∀ a : ℕ, a ≤ 2 →
        metricCovDerivNorm (I := I) a u gRef y ≤ B) →
      ∀ y ∈ K, ∀ i j k l : Fin (Module.finrank Real E),
        |chartRiemannTensor (I := I) u α i j k l (extChartAt I α y)| ≤ C := by
  classical
  obtain ⟨Q, hQ0, hQ⟩ := chartGram_partial_bound_riem (I := I) gRef α hK hKchart B
  obtain ⟨Mb, hMb0, hMb⟩ := exists_abs_chartInvGramMatrix_le_of_lower_bound (I := I) gRef α hK
    (by rwa [trivializationAt_baseSet_eq_chartAt_source]) lam hlam
  set nR : Real := (Module.finrank Real E : Real) with hnR
  have hnR0 : 0 ≤ nR := Nat.cast_nonneg _
  set P : Real := 3 * Q with hP
  have hP0 : 0 ≤ P := by rw [hP]; positivity
  set R : Real := 3 * Q with hR
  have hR0 : 0 ≤ R := by rw [hR]; positivity
  set D : Real := nR ^ 2 * Mb ^ 2 * Q with hD
  have hD0 : 0 ≤ D := by rw [hD]; positivity
  set Mg : Real := (1 / 2) * nR * Mb * P with hMg
  have hMg0 : 0 ≤ Mg := by rw [hMg]; positivity
  set Md : Real := (1 / 2) * nR * (D * P + Mb * R) with hMd
  have hMd0 : 0 ≤ Md := by rw [hMd]; positivity
  set C : Real := 2 * Md + 2 * nR * Mg ^ 2 with hC
  have hC0 : 0 ≤ C := by rw [hC]; positivity
  refine ⟨C, hC0, ?_⟩
  intro u hlow hcov y hy i j k l
  set z : E := extChartAt I α y with hz
  have hψ : (extChartAt I α).symm z = y := by
    rw [hz]
    exact (extChartAt I α).left_inv (by rw [extChartAt_source]; exact hKchart hy)
  have hzint : z ∈ interior (extChartAt I α).target := by
    rw [(isOpen_extChartAt_target (I := I) α).interior_eq, hz]
    exact (extChartAt I α).map_source (by rw [extChartAt_source]; exact hKchart hy)
  have hQu := (hQ u hcov y hy).1
  have hQQu := (hQ u hcov y hy).2
  have hMbu : ∀ a b : Fin (Module.finrank Real E),
      |chartInvGramOnE (I := I) u α a b z| ≤ Mb := by
    intro a b
    rw [chartInvGramOnE_def, hψ]
    exact hMb y hy u (hlow y hy) a b
  have hPu : ∀ a b c : Fin (Module.finrank Real E),
      |chartChristoffelBracket (I := I) u α a b c z| ≤ P := by
    intro a b c
    rw [hP]
    exact chartChristoffelBracket_abs_le (I := I) (M := M) u α z hQu a b c
  have hRu : ∀ d a b c : Fin (Module.finrank Real E),
      |chartChristoffelBracketDeriv (I := I) u α d a b c z| ≤ R := by
    intro d a b c
    rw [hR]
    exact chartChristoffelBracketDeriv_abs_le (I := I) (M := M) u α z hQQu d a b c
  have hDu : ∀ d a b : Fin (Module.finrank Real E),
      |partialDeriv (E := E) d (chartInvGramOnE (I := I) u α a b) z| ≤ D := by
    intro d a b
    have h := invGramD_abs_le (I := I) (M := M) u α hzint hMb0 hMbu hQu d a b
    rw [hD, hnR]
    exact h
  have hMgu : ∀ a b c : Fin (Module.finrank Real E),
      |chartChristoffel (I := I) u α a b c z| ≤ Mg := by
    intro a b c
    have h := christoffel_abs_le (I := I) (M := M) u α z a b c hMb0
      (fun lhp => hMbu c lhp) (fun lhp => hPu a b lhp)
    rw [hMg, hnR]
    exact h
  have hMdu : ∀ d a b c : Fin (Module.finrank Real E),
      |partialDeriv (E := E) d (chartChristoffel (I := I) u α a b c) z| ≤ Md := by
    intro d a b c
    have h := christoffelD_abs_le (I := I) (M := M) u α hzint d a b c
      hMb0 hD0 (fun lhp => hMbu c lhp) (fun lhp => hDu d c lhp)
      (fun lhp => hPu a b lhp) (fun lhp => hRu d a b lhp)
    rw [hMd, hnR]
    exact h
  have h := chartRiemannTensor_abs_le (I := I) u α i j k l hMg0 hMgu hMdu
  rw [hC, hnR]
  exact h

omit [I.Boundaryless] [SigmaCompactSpace M] in
private theorem scale_sum_le_three
    {K : Set M} (hK : IsCompact K) (gk gInf gRef : SmoothRiemannianMetric I M)
    {x : M} (hx : x ∈ K) :
    (∑ q ∈ Finset.range 3, metricDerivNorm (I := I) q gk gInf gRef x) ≤
      3 * metricDerivNormSupOn (I := I) K 2 gk gInf gRef := by
  calc
    (∑ q ∈ Finset.range 3, metricDerivNorm (I := I) q gk gInf gRef x)
        ≤ ∑ _q ∈ Finset.range 3, metricDerivNormSupOn (I := I) K 2 gk gInf gRef :=
          Finset.sum_le_sum fun q hq =>
            derivNorm_le_sup (I := I) hK
              (Nat.le_of_lt_succ (Finset.mem_range.1 hq)) gk gInf gRef hx
    _ = 3 * metricDerivNormSupOn (I := I) K 2 gk gInf gRef := by norm_num

private theorem scale_three_mul_lt
    {C rho eps : ℝ} (hC0 : 0 ≤ C) (heps : 0 < eps) (h : rho < eps / (3 * C + 1)) :
    C * (3 * rho) < eps := by
  have hpos : 0 < 3 * C + 1 := by linarith
  by_cases hr : 0 ≤ rho
  · have h' : rho * (3 * C + 1) < eps := by
      rw [lt_div_iff₀ hpos] at h
      linarith [h]
    nlinarith [h', hr, heps, hC0]
  · have hle : C * (3 * rho) ≤ 0 := by nlinarith [hr, hC0]
    linarith

theorem chartRicciLim_contOn
    (gRef : SmoothRiemannianMetric I M) (α : M)
    {K : Set M} (hK : IsCompact K)
    (hKchart : K ⊆ (chartAt H α).source)
    (gSeq : ℕ → ℝ → SmoothRiemannianMetric I M) (gInf : ℝ → SmoothRiemannianMetric I M)
    (β ψ lam B : ℝ) (hlam : 0 < lam)
    (hlowSeq : ∀ (k : ℕ) (t : ℝ), t ∈ Set.Icc β ψ → ∀ y ∈ K, ∀ ξ : TangentSpace I y,
      lam * gRef.inner y ξ ξ ≤ (gSeq k t).inner y ξ ξ)
    (hlowInf : ∀ (t : ℝ), t ∈ Set.Icc β ψ → ∀ y ∈ K, ∀ ξ : TangentSpace I y,
      lam * gRef.inner y ξ ξ ≤ (gInf t).inner y ξ ξ)
    (hbddSeq : ∀ (k : ℕ) (t : ℝ), t ∈ Set.Icc β ψ → ∀ y ∈ K, ∀ a : ℕ, a ≤ 2 →
      metricCovDerivNorm (I := I) a (gSeq k t) gRef y ≤ B)
    (hbddInf : ∀ (t : ℝ), t ∈ Set.Icc β ψ → ∀ y ∈ K, ∀ a : ℕ, a ≤ 2 →
      metricCovDerivNorm (I := I) a (gInf t) gRef y ≤ B)
    (hconv : ∀ ε : ℝ, 0 < ε → ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k → ∀ t ∈ Set.Icc β ψ,
      metricDerivNormSupOn (I := I) K 2 (gSeq k t) (gInf t) gRef < ε)
    (i j : Fin (Module.finrank Real E))
    (hkcont : ∀ k : ℕ, ContinuousOn
      (fun p : ℝ × M => chartRicciTensor (I := I) (gSeq k p.1) α i j (extChartAt I α p.2))
      (Set.Icc β ψ ×ˢ K)) :
    ContinuousOn
      (fun p : ℝ × M => chartRicciTensor (I := I) (gInf p.1) α i j (extChartAt I α p.2))
      (Set.Icc β ψ ×ˢ K) := by
  classical
  obtain ⟨C, hC0, hC⟩ := exists_abs_chartRicciTensor_sub_le (I := I) gRef α hK hKchart lam B hlam
  have htu : TendstoUniformlyOn
      (fun (k : ℕ) (p : ℝ × M) =>
        chartRicciTensor (I := I) (gSeq k p.1) α i j (extChartAt I α p.2))
      (fun p : ℝ × M =>
        chartRicciTensor (I := I) (gInf p.1) α i j (extChartAt I α p.2))
      atTop (Set.Icc β ψ ×ˢ K) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro eps heps
    obtain ⟨k0, hk0⟩ := hconv (eps / (3 * C + 1)) (by positivity)
    filter_upwards [eventually_ge_atTop k0] with k hk
    rintro ⟨t, x⟩ ⟨ht, hx⟩
    have hdiff := hC (gSeq k t) (gInf t)
      (fun y hy ξ => hlowSeq k t ht y hy ξ)
      (fun y hy ξ => hlowInf t ht y hy ξ)
      (fun y hy a ha => hbddSeq k t ht y hy a ha)
      (fun y hy a ha => hbddInf t ht y hy a ha) x hx i j
    have hsum := scale_sum_le_three hK (gSeq k t) (gInf t) gRef hx
    have h1 : dist (chartRicciTensor (I := I) (gInf t) α i j (extChartAt I α x))
        (chartRicciTensor (I := I) (gSeq k t) α i j (extChartAt I α x)) ≤
        C * ∑ q ∈ Finset.range 3,
          metricDerivNorm (I := I) q (gSeq k t) (gInf t) gRef x := by
      rw [Real.dist_eq, abs_sub_comm]
      exact hdiff
    have h2 : C * ∑ q ∈ Finset.range 3,
          metricDerivNorm (I := I) q (gSeq k t) (gInf t) gRef x ≤
        C * (3 * metricDerivNormSupOn (I := I) K 2 (gSeq k t) (gInf t) gRef) :=
      mul_le_mul_of_nonneg_left hsum hC0.le
    have h3 := scale_three_mul_lt hC0.le heps (hk0 k hk t ht)
    linarith [h1, h2, h3]
  exact htu.continuousOn (Filter.Eventually.of_forall hkcont).frequently

theorem chartRiemannLim_contOn
    (gRef : SmoothRiemannianMetric I M) (α : M)
    {K : Set M} (hK : IsCompact K)
    (hKchart : K ⊆ (chartAt H α).source)
    (gSeq : ℕ → ℝ → SmoothRiemannianMetric I M) (gInf : ℝ → SmoothRiemannianMetric I M)
    (β ψ lam B : ℝ) (hlam : 0 < lam)
    (hlowSeq : ∀ (k : ℕ) (t : ℝ), t ∈ Set.Icc β ψ → ∀ y ∈ K, ∀ ξ : TangentSpace I y,
      lam * gRef.inner y ξ ξ ≤ (gSeq k t).inner y ξ ξ)
    (hlowInf : ∀ (t : ℝ), t ∈ Set.Icc β ψ → ∀ y ∈ K, ∀ ξ : TangentSpace I y,
      lam * gRef.inner y ξ ξ ≤ (gInf t).inner y ξ ξ)
    (hbddSeq : ∀ (k : ℕ) (t : ℝ), t ∈ Set.Icc β ψ → ∀ y ∈ K, ∀ a : ℕ, a ≤ 2 →
      metricCovDerivNorm (I := I) a (gSeq k t) gRef y ≤ B)
    (hbddInf : ∀ (t : ℝ), t ∈ Set.Icc β ψ → ∀ y ∈ K, ∀ a : ℕ, a ≤ 2 →
      metricCovDerivNorm (I := I) a (gInf t) gRef y ≤ B)
    (hconv : ∀ ε : ℝ, 0 < ε → ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k → ∀ t ∈ Set.Icc β ψ,
      metricDerivNormSupOn (I := I) K 2 (gSeq k t) (gInf t) gRef < ε)
    (i j k' l : Fin (Module.finrank Real E))
    (hkcont : ∀ k : ℕ, ContinuousOn
      (fun p : ℝ × M =>
        chartRiemannTensor (I := I) (gSeq k p.1) α i j k' l (extChartAt I α p.2))
      (Set.Icc β ψ ×ˢ K)) :
    ContinuousOn
      (fun p : ℝ × M =>
        chartRiemannTensor (I := I) (gInf p.1) α i j k' l (extChartAt I α p.2))
      (Set.Icc β ψ ×ˢ K) := by
  classical
  obtain ⟨C, hC0, hC⟩ := exists_abs_chartRiemannTensor_sub_le (I := I) gRef α hK hKchart lam B hlam
  have htu : TendstoUniformlyOn
      (fun (k : ℕ) (p : ℝ × M) =>
        chartRiemannTensor (I := I) (gSeq k p.1) α i j k' l (extChartAt I α p.2))
      (fun p : ℝ × M =>
        chartRiemannTensor (I := I) (gInf p.1) α i j k' l (extChartAt I α p.2))
      atTop (Set.Icc β ψ ×ˢ K) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro eps heps
    obtain ⟨k0, hk0⟩ := hconv (eps / (3 * C + 1)) (by positivity)
    filter_upwards [eventually_ge_atTop k0] with k hk
    rintro ⟨t, x⟩ ⟨ht, hx⟩
    have hdiff := hC (gSeq k t) (gInf t)
      (fun y hy ξ => hlowSeq k t ht y hy ξ)
      (fun y hy ξ => hlowInf t ht y hy ξ)
      (fun y hy a ha => hbddSeq k t ht y hy a ha)
      (fun y hy a ha => hbddInf t ht y hy a ha) x hx i j k' l
    have hsum := scale_sum_le_three hK (gSeq k t) (gInf t) gRef hx
    have h1 : dist (chartRiemannTensor (I := I) (gInf t) α i j k' l (extChartAt I α x))
        (chartRiemannTensor (I := I) (gSeq k t) α i j k' l (extChartAt I α x)) ≤
        C * ∑ q ∈ Finset.range 3,
          metricDerivNorm (I := I) q (gSeq k t) (gInf t) gRef x := by
      rw [Real.dist_eq, abs_sub_comm]
      exact hdiff
    have h2 : C * ∑ q ∈ Finset.range 3,
          metricDerivNorm (I := I) q (gSeq k t) (gInf t) gRef x ≤
        C * (3 * metricDerivNormSupOn (I := I) K 2 (gSeq k t) (gInf t) gRef) :=
      mul_le_mul_of_nonneg_left hsum hC0.le
    have h3 := scale_three_mul_lt hC0.le heps (hk0 k hk t ht)
    linarith [h1, h2, h3]
  exact htu.continuousOn (Filter.Eventually.of_forall hkcont).frequently

end DifferentialGeometry.Geometry.Curvature
