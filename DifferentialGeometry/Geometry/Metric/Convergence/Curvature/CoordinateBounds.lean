import DifferentialGeometry.Geometry.Metric.Convergence.Coordinates.JetBounds
import DifferentialGeometry.Geometry.Metric.Convergence.Coordinates.InverseGram
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.Ricci.AffineDifference
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.RHS.AbsoluteBound

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature

open scoped Manifold ContDiff Topology BigOperators Matrix

open CheegerGromovCompactness Geometry.Operator Tensor.Coordinates
open Geometry.Connection (chartChristoffelBracket chartChristoffelBracketDeriv)
open Analysis.Calculus Analysis.Spectral.DeTurckCoefficients
open Integral.DivergenceTheorem Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]

private lemma chartGram_partial_bound
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
    rw [show chartGramOnE (I := I) w α a b = f from rfl]
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
    rw [show chartGramOnE (I := I) w α a b = f from rfl]
    exact happ.trans <| (mul_le_mul_of_nonneg_right (hQ2 k y hy a b) (sq_nonneg V)).trans <|
      le_max_right _ _

theorem exists_abs_chartRicciTensor_sub_le
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
      ∀ y ∈ K, ∀ i k : Fin (Module.finrank Real E),
        |chartRicciTensor (I := I) u α i k (extChartAt I α y) -
          chartRicciTensor (I := I) u' α i k (extChartAt I α y)| ≤
        C * ∑ q ∈ Finset.range 3, metricDerivNorm (I := I) q u u' gRef y := by
  classical
  obtain ⟨Q, hQ0, hQ⟩ := chartGram_partial_bound (I := I) gRef α hK hKchart B
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
  set Cr : Real := 2 * nR * Cdiff + 4 * nR ^ 2 * Clip * Mg with hCr
  have hCr0 : 0 ≤ Cr := by rw [hCr]; positivity
  refine ⟨Cr * CJ + 1, by positivity, ?_⟩
  intro u u' hlowu hlowu' hcovu hcovu' y hy i k
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
  have h2nd := chartRicciSecondOrderTerm_sub_abs_le (I := I) (M := M)
    u u' α hCdiff' i k
  have h1st := chartRicciFirstOrderTerm_sub_abs_le (I := I) (M := M)
    u u' α hClip0 hMg0 hClip' hMgu hMgu' i k
  set jet2 : Real := chartMetricJet2DiffSup (I := I) (M := M) u u' α z with hjet
  have hjet0 : 0 ≤ jet2 := chartMetricJet2DiffSup_nonneg _ _ _ _
  have hjet1 : chartMetricJet1DiffSup (I := I) (M := M) u u' α z ≤ jet2 :=
    chartMetricJet1DiffSup_le_jet2 (I := I) (M := M) u u' α z
  have hricJet : |chartRicciTensor (I := I) u α i k z -
      chartRicciTensor (I := I) u' α i k z| ≤ Cr * jet2 := by
    rw [chartRicciTensor_eq_secondOrder_add_firstOrder (I := I) u α i k z,
      chartRicciTensor_eq_secondOrder_add_firstOrder (I := I) u' α i k z]
    rw [show
      (chartRicciSecondOrderTerm (I := I) u α i k z +
          chartRicciFirstOrderTerm (I := I) u α i k z) -
        (chartRicciSecondOrderTerm (I := I) u' α i k z +
          chartRicciFirstOrderTerm (I := I) u' α i k z) =
        (chartRicciSecondOrderTerm (I := I) u α i k z -
          chartRicciSecondOrderTerm (I := I) u' α i k z) +
        (chartRicciFirstOrderTerm (I := I) u α i k z -
          chartRicciFirstOrderTerm (I := I) u' α i k z) by ring]
    refine (abs_add_le _ _).trans ?_
    have h1st' : |chartRicciFirstOrderTerm (I := I) u α i k z -
        chartRicciFirstOrderTerm (I := I) u' α i k z| ≤
        4 * nR ^ 2 * Clip * Mg * jet2 := by
      refine h1st.trans ?_
      rw [hnR]
      exact mul_le_mul_of_nonneg_left hjet1 (by positivity)
    calc
      |chartRicciSecondOrderTerm (I := I) u α i k z -
          chartRicciSecondOrderTerm (I := I) u' α i k z| +
          |chartRicciFirstOrderTerm (I := I) u α i k z -
            chartRicciFirstOrderTerm (I := I) u' α i k z|
          ≤ 2 * nR * Cdiff * jet2 + 4 * nR ^ 2 * Clip * Mg * jet2 := by
            rw [hnR]
            exact add_le_add h2nd h1st'
      _ = Cr * jet2 := by rw [hCr]; ring
  set S : Real := ∑ q ∈ Finset.range 3, metricDerivNorm (I := I) q u u' gRef y with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _
  have hjet_le : jet2 ≤ CJ * S := by
    rw [hjet, hz]
    exact hCJ u u' y hy
  calc
    |chartRicciTensor (I := I) u α i k (extChartAt I α y) -
        chartRicciTensor (I := I) u' α i k (extChartAt I α y)|
        = |chartRicciTensor (I := I) u α i k z -
            chartRicciTensor (I := I) u' α i k z| := by rw [hz]
    _ ≤ Cr * jet2 := hricJet
    _ ≤ Cr * (CJ * S) := mul_le_mul_of_nonneg_left hjet_le hCr0
    _ ≤ (Cr * CJ + 1) * S := by nlinarith

theorem exists_abs_chartRicciTensor_le
    (gRef : SmoothRiemannianMetric I M) (α : M)
    {K : Set M} (hK : IsCompact K)
    (hKchart : K ⊆ (chartAt H α).source)
    (lam B : Real) (hlam : 0 < lam) :
    ∃ C : Real, 0 ≤ C ∧ ∀ u : SmoothRiemannianMetric I M,
      (∀ y ∈ K, ∀ ξ : TangentSpace I y,
        lam * gRef.inner y ξ ξ ≤ u.inner y ξ ξ) →
      (∀ y ∈ K, ∀ a : ℕ, a ≤ 2 →
        metricCovDerivNorm (I := I) a u gRef y ≤ B) →
      ∀ y ∈ K, ∀ i k : Fin (Module.finrank Real E),
        |chartRicciTensor (I := I) u α i k (extChartAt I α y)| ≤ C := by
  classical
  obtain ⟨Q, hQ0, hQ⟩ := chartGram_partial_bound (I := I) gRef α hK hKchart B
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
  set C : Real := 2 * nR * Md + 2 * nR ^ 2 * Mg ^ 2 with hC
  have hC0 : 0 ≤ C := by rw [hC]; positivity
  refine ⟨C, hC0, ?_⟩
  intro u hlow hcov y hy i k
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
      (fun l => hMbu c l) (fun l => hPu a b l)
    rw [hMg, hnR]
    exact h
  have hMdu : ∀ d a b c : Fin (Module.finrank Real E),
      |partialDeriv (E := E) d (chartChristoffel (I := I) u α a b c) z| ≤ Md := by
    intro d a b c
    have h := christoffelD_abs_le (I := I) (M := M) u α hzint d a b c
      hMb0 hD0 (fun l => hMbu c l) (fun l => hDu d c l)
      (fun l => hPu a b l) (fun l => hRu d a b l)
    rw [hMd, hnR]
    exact h
  have h := chartRicci_abs_le (I := I) u α i k z hMg0 hMgu hMdu
  rw [hC, hnR]
  convert h using 1
  ring


end DifferentialGeometry.Geometry.Curvature
