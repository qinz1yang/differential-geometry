import DifferentialGeometry.Analysis.Integration.Measure.ParamEvaluation
import Mathlib.Analysis.Matrix.Normed

noncomputable section

open Manifold Set
open scoped ContDiff Matrix.Norms.Elementwise

namespace DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private theorem contDiffOn_paramGramMatrix_of_chart
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1)
    {n : ℕ∞} {s : Set E} (hs : IsOpen s) (hs_source : s ⊆ Ψ.source)
    (hs_chart : ∀ w ∈ s, Ψ w ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (hΨ : ContMDiffOn 𝓘(ℝ, E) I ((n : ℕ∞ω) + 1) Ψ s) :
    ContDiffOn ℝ n (paramGramMatrix g Ψ) s := by
  have hT : ContDiffOn ℝ ((n : ℕ∞ω) + 1) (paramChartMap (I := I) x₀ Ψ) s := by
    apply contMDiffOn_iff_contDiffOn.mp
    exact ((contMDiffOn_extChartAt (I := I) (x := x₀) (n := ∞)).of_le
      (by simp only [← WithTop.coe_add, ← WithTop.coe_one, WithTop.coe_le_coe]; exact le_top)).comp hΨ (fun w hw => by
      simpa [trivializationAt_baseSet_eq_chartAt_source (I := I)] using hs_chart w hw)
  have hfderiv : ContDiffOn ℝ n (fderiv ℝ (paramChartMap (I := I) x₀ Ψ)) s :=
    hT.fderiv_of_isOpen hs le_rfl
  have hJ : ∀ k i, ContDiffOn ℝ n
      (fun w => paramJacobianMatrix (I := I) x₀ Ψ w k i) s := by
    intro k i
    have hcoord := ((chartModelBasis E).coord k).toContinuousLinearMap.contDiff (n := n)
    exact (hcoord.comp_contDiffOn (hfderiv.clm_apply (contDiffOn_const (c := chartModelBasis E i)))).congr
      (fun w _ => paramJacobianMatrix_apply (I := I) x₀ Ψ w k i)
  have hG : ∀ k l, ContDiffOn ℝ n
      (fun w => chartGramMatrix g x₀ (Ψ w) k l) s := by
    intro k l
    apply contMDiffOn_iff_contDiffOn.mp
    exact ((chartGramMatrix_entry_contMDiffOn g x₀ k l).of_le
      (show (n : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)).comp
        (hΨ.of_le (le_add_of_nonneg_right zero_le_one)) hs_chart
  refine contDiffOn_pi.mpr fun i => contDiffOn_pi.mpr fun j => ?_
  have hsum : ContDiffOn ℝ n
      (fun w => ∑ k, ∑ l,
        paramJacobianMatrix (I := I) x₀ Ψ w k i *
        paramJacobianMatrix (I := I) x₀ Ψ w l j *
        chartGramMatrix g x₀ (Ψ w) k l) s := by
    refine ContDiffOn.sum fun k _ => ContDiffOn.sum fun l _ => ?_
    exact ((hJ k i).mul (hJ l j)).mul (hG k l)
  exact hsum.congr fun w hw =>
    paramGramMatrix_pullback_eq_sum g x₀ Ψ (hs_source hw) (hs_chart w hw) i j

theorem contDiffOn_paramGramMatrix
    (g : SmoothRiemannianMetric I M)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1)
    {n : ℕ∞} {s : Set E} (hs : IsOpen s) (hs_source : s ⊆ Ψ.source)
    (hΨ : ContMDiffOn 𝓘(ℝ, E) I ((n : ℕ∞ω) + 1) Ψ s) :
    ContDiffOn ℝ n (paramGramMatrix g Ψ) s := by
  intro w hw
  let U : Set E := s ∩ Ψ ⁻¹' (chartAt H (Ψ w)).source
  have hU : IsOpen U :=
    hΨ.continuousOn.isOpen_inter_preimage hs (chartAt H (Ψ w)).open_source
  have hwU : w ∈ U := ⟨hw, mem_chart_source H (Ψ w)⟩
  have hGram : ContDiffOn ℝ n (paramGramMatrix g Ψ) U := by
    apply contDiffOn_paramGramMatrix_of_chart g (Ψ w) Ψ hU
      (fun z hz => hs_source hz.1) _ (hΨ.mono inter_subset_left)
    intro z hz
    simpa [trivializationAt_baseSet_eq_chartAt_source (I := I)] using hz.2
  exact (hGram.contDiffAt (hU.mem_nhds hwU)).contDiffWithinAt

theorem contDiffOn_paramDensity
    (g : SmoothRiemannianMetric I M)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1)
    {n : ℕ∞} {s : Set E} (hs : IsOpen s) (hs_source : s ⊆ Ψ.source)
    (hΨ : ContMDiffOn 𝓘(ℝ, E) I ((n : ℕ∞ω) + 1) Ψ s) :
    ContDiffOn ℝ n (paramDensity g Ψ) s := by
  classical
  have hGram := contDiffOn_paramGramMatrix g Ψ hs hs_source hΨ
  have hdet : ContDiffOn ℝ n (fun w => (paramGramMatrix g Ψ w).det) s := by
    simp_rw [Matrix.det_apply']
    refine ContDiffOn.sum fun σ _ => ?_
    exact contDiffOn_const.mul (contDiffOn_prod fun i _ =>
      contDiffOn_pi.mp (contDiffOn_pi.mp hGram (σ i)) i)
  exact hdet.sqrt fun w hw => ne_of_gt (paramGramMatrix_det_pos g Ψ (hs_source hw))

end DifferentialGeometry.Integral.Measure
