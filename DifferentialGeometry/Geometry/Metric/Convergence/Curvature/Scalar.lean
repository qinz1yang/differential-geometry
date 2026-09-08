import DifferentialGeometry.Geometry.Metric.Convergence.Curvature.CoordinateBounds
import DifferentialGeometry.Geometry.Connection.ChartBridge.Curvature.BasisIdentityOffCenter
import DifferentialGeometry.Geometry.Curvature.Coordinates.ScalarTrace
import Mathlib.Topology.Compactness.LocallyFinite

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature

open scoped Manifold ContDiff Topology BigOperators Matrix

open CheegerGromovCompactness Geometry.Operator Geometry.Connection Tensor.Coordinates
open Analysis.Spectral.DeTurckCoefficients
open Integral.DivergenceTheorem Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]

private theorem abs_metricScalarAt_sub_bound_on_chart
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
      ∀ y ∈ K,
        |metricScalarAt (I := I) u y - metricScalarAt (I := I) u' y| ≤
          C * ∑ q ∈ Finset.range 3, metricDerivNorm (I := I) q u u' gRef y := by
  classical
  obtain ⟨Cric, hCric0, hCric⟩ :=
    exists_abs_chartRicciTensor_sub_le (I := I) gRef α hK hKchart lam B hlam
  obtain ⟨Cari, hCari0, hCari⟩ :=
    exists_abs_chartRicciTensor_le (I := I) gRef α hK hKchart lam B hlam
  obtain ⟨Minv, hMinv0, hMinv⟩ :=
    exists_abs_chartInvGramMatrix_le_of_lower_bound (I := I) gRef α hK
      (by rwa [trivializationAt_baseSet_eq_chartAt_source]) lam hlam
  obtain ⟨CJ, hCJ0, hCJ⟩ := exists_chartMetricJet2DiffSup_le (I := I) gRef α hK hKchart
  set nR : Real := (Module.finrank Real E : Real) with hnR
  have hnR0 : 0 ≤ nR := Nat.cast_nonneg _
  set Cinv : Real := nR ^ 2 * Minv ^ 2 with hCinv
  have hCinv0 : 0 ≤ Cinv := by rw [hCinv]; positivity
  set Ci : Real := Cinv * CJ with hCi
  have hCi0 : 0 ≤ Ci := by rw [hCi]; positivity
  set Ct : Real := Ci * Cari + Minv * Cric with hCt
  have hCt0 : 0 ≤ Ct := by rw [hCt]; positivity
  refine ⟨nR ^ 2 * Ct + 1, by positivity, ?_⟩
  intro u u' hlowu hlowu' hcovu hcovu' y hy
  set z : E := extChartAt I α y with hz
  set S : Real := ∑ q ∈ Finset.range 3, metricDerivNorm (I := I) q u u' gRef y with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _
  have hψ : (extChartAt I α).symm z = y := by
    rw [hz]
    exact (extChartAt I α).left_inv (by rw [extChartAt_source]; exact hKchart hy)
  have hybase : y ∈ (trivializationAt E (TangentSpace I : M → Type _) α).baseSet := by
    rw [DifferentialGeometry.Integral.Measure.trivializationAt_baseSet_eq_chartAt_source]
    exact hKchart hy
  have hyg : y ∈ chartLeviCivitaGoodSet (I := I) α := by
    rw [chartLeviCivitaGoodSet_eq_extChartAt_source (I := I) α, extChartAt_source]
    exact hKchart hy
  have hMinvu' : ∀ i j : Fin (Module.finrank Real E),
      |chartInvGramOnE (I := I) u' α i j z| ≤ Minv := by
    intro i j
    rw [chartInvGramOnE_def, hψ]
    exact hMinv y hy u' (hlowu' y hy) i j
  have hInv : ∀ i j : Fin (Module.finrank Real E),
      |chartInvGramOnE (I := I) u α i j z - chartInvGramOnE (I := I) u' α i j z| ≤
        Ci * S := by
    intro i j
    have hmatrix := chartInvGramMatrix_entry_sub_abs_le_gramDiffSup (I := I) (M := M)
      u u' α hybase
      (fun p q => hMinv y hy u (hlowu y hy) p q)
      (fun p q => hMinv y hy u' (hlowu' y hy) p q) i j
    have hgram : chartGramDiffSup (I := I) (M := M) u u' α y ≤
        chartMetricJet2DiffSup (I := I) (M := M) u u' α z := by
      rw [← hψ]
      exact (chartGramDiffSup_le_jet1 (I := I) (M := M) u u' α z).trans
        (chartMetricJet1DiffSup_le_jet2 (I := I) (M := M) u u' α z)
    have hjet : chartMetricJet2DiffSup (I := I) (M := M) u u' α z ≤ CJ * S := by
      rw [hz, hS]
      exact hCJ u u' y hy
    rw [chartInvGramOnE_def, chartInvGramOnE_def, hψ]
    calc
      |chartInvGramMatrix (I := I) u α y i j - chartInvGramMatrix (I := I) u' α y i j|
          ≤ Cinv * chartGramDiffSup (I := I) (M := M) u u' α y := by
            rw [hCinv, hnR]
            exact hmatrix
      _ ≤ Cinv * chartMetricJet2DiffSup (I := I) (M := M) u u' α z :=
        mul_le_mul_of_nonneg_left hgram hCinv0
      _ ≤ Cinv * (CJ * S) := mul_le_mul_of_nonneg_left hjet hCinv0
      _ = Ci * S := by rw [hCi]; ring
  have hscalar (w : SmoothRiemannianMetric I M) :
      metricScalarAt (I := I) w y =
        ∑ i : Fin (Module.finrank Real E), ∑ j : Fin (Module.finrank Real E),
          chartInvGramOnE (I := I) w α i j z * chartRicciTensor (I := I) w α i j z := by
    rw [DifferentialGeometry.PDE.RicciFlow.metricScalar_chartTrace_eq (I := I) w α hyg]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [ricciTensor_chartBasisVec_alpha_eq (I := I) w α i j hyg, hz]
  rw [hscalar u, hscalar u']
  have hdiff :
      (∑ i : Fin (Module.finrank Real E), ∑ j : Fin (Module.finrank Real E),
          chartInvGramOnE (I := I) u α i j z * chartRicciTensor (I := I) u α i j z) -
        (∑ i : Fin (Module.finrank Real E), ∑ j : Fin (Module.finrank Real E),
          chartInvGramOnE (I := I) u' α i j z * chartRicciTensor (I := I) u' α i j z) =
      ∑ i : Fin (Module.finrank Real E), ∑ j : Fin (Module.finrank Real E),
        ((chartInvGramOnE (I := I) u α i j z - chartInvGramOnE (I := I) u' α i j z) *
            chartRicciTensor (I := I) u α i j z +
          chartInvGramOnE (I := I) u' α i j z *
            (chartRicciTensor (I := I) u α i j z - chartRicciTensor (I := I) u' α i j z)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hdiff]
  have hterm : ∀ i j : Fin (Module.finrank Real E),
      |(chartInvGramOnE (I := I) u α i j z - chartInvGramOnE (I := I) u' α i j z) *
          chartRicciTensor (I := I) u α i j z +
        chartInvGramOnE (I := I) u' α i j z *
          (chartRicciTensor (I := I) u α i j z - chartRicciTensor (I := I) u' α i j z)| ≤
        Ct * S := by
    intro i j
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    have hA := hCari u hlowu hcovu y hy i j
    have hR := hCric u u' hlowu hlowu' hcovu hcovu' y hy i j
    have h1 := mul_le_mul (hInv i j) hA (abs_nonneg _) (mul_nonneg hCi0 hS0)
    have h2 := mul_le_mul (hMinvu' i j) hR (abs_nonneg _) hMinv0
    rw [hCt]
    nlinarith
  calc
    |∑ i : Fin (Module.finrank Real E), ∑ j : Fin (Module.finrank Real E),
        ((chartInvGramOnE (I := I) u α i j z - chartInvGramOnE (I := I) u' α i j z) *
            chartRicciTensor (I := I) u α i j z +
          chartInvGramOnE (I := I) u' α i j z *
            (chartRicciTensor (I := I) u α i j z - chartRicciTensor (I := I) u' α i j z))|
        ≤ ∑ i : Fin (Module.finrank Real E), ∑ j : Fin (Module.finrank Real E), Ct * S := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
          refine Finset.sum_le_sum fun i _ => (Finset.abs_sum_le_sum_abs _ _).trans ?_
          exact Finset.sum_le_sum fun j _ => hterm i j
    _ = nR ^ 2 * Ct * S := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [hnR]
      ring
    _ ≤ (nR ^ 2 * Ct + 1) * S := by nlinarith


theorem exists_abs_metricScalarAt_sub_le
    (gRef : SmoothRiemannianMetric I M)
    {K : Set M} (hK : IsCompact K)
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
      ∀ y ∈ K,
        |metricScalarAt (I := I) u y - metricScalarAt (I := I) u' y| ≤
          C * ∑ q ∈ Finset.range 3, metricDerivNorm (I := I) q u u' gRef y := by
  classical
  let ρ := chartAtlasPOU I M
  have hKα : ∀ α : M, IsCompact
      (K ∩ tsupport (fun y : M => (ρ α : M → Real) y)) := fun α =>
    hK.inter_right (isClosed_tsupport (fun y : M => (ρ α : M → Real) y))
  have hKchart : ∀ α : M,
      K ∩ tsupport (fun y : M => (ρ α : M → Real) y) ⊆ (chartAt H α).source := by
    intro α y hy
    exact (chartAtlasPOU_isSubordinate I M) α hy.2
  choose Cα hCα0 hCα using fun α : M =>
    abs_metricScalarAt_sub_bound_on_chart (I := I) gRef α (hKα α) (hKchart α) lam B hlam
  let A : Set M := {α : M | (Function.support (fun y : M => (ρ α : M → Real) y) ∩ K).Nonempty}
  have hA : A.Finite := by
    dsimp [A]
    exact ρ.locallyFinite.finite_nonempty_inter_compact hK
  let active : Finset M := hA.toFinset
  have hactive (α : M) : α ∈ active ↔
      (Function.support (fun y : M => (ρ α : M → Real) y) ∩ K).Nonempty := by
    change α ∈ hA.toFinset ↔
      (Function.support (fun y : M => (ρ α : M → Real) y) ∩ K).Nonempty
    rw [Set.Finite.mem_toFinset]
    rfl
  have hsum0 : 0 ≤ ∑ α ∈ active, Cα α :=
    Finset.sum_nonneg fun α _ => (hCα0 α).le
  refine ⟨(∑ α ∈ active, Cα α) + 1, by linarith, ?_⟩
  intro u u' hlowu hlowu' hcovu hcovu' y hy
  obtain ⟨α, hαpos⟩ := ρ.exists_pos_of_mem (Set.mem_univ y)
  have hysupp : y ∈ Function.support (fun z : M => (ρ α : M → Real) z) := ne_of_gt hαpos
  have hαS : α ∈ active := hactive α |>.2 ⟨y, hysupp, hy⟩
  have hyKα : y ∈ K ∩ tsupport (fun z : M => (ρ α : M → Real) z) :=
    ⟨hy, subset_closure hysupp⟩
  have hloc := hCα α u u'
    (fun z hz ξ => hlowu z hz.1 ξ)
    (fun z hz ξ => hlowu' z hz.1 ξ)
    (fun z hz a ha => hcovu z hz.1 a ha)
    (fun z hz a ha => hcovu' z hz.1 a ha)
    y hyKα
  have hCαle : Cα α ≤ ∑ β ∈ active, Cα β :=
    Finset.single_le_sum (fun β _ => (hCα0 β).le) hαS
  have hD0 : 0 ≤ ∑ q ∈ Finset.range 3,
      metricDerivNorm (I := I) q u u' gRef y :=
    Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _
  exact hloc.trans <| mul_le_mul_of_nonneg_right
    (hCαle.trans (le_add_of_nonneg_right zero_le_one)) hD0


end DifferentialGeometry.Geometry.Curvature
