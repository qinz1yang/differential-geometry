import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.TimeDifference
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.Endpoint.CovariantContinuity
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Scaling
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.Solution.TimeRegularity

noncomputable section
open Set DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem metricDerivNorm_le_add_of_ricci_difference_bound
    {D D' : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (T : SolutionOn (I := I) (M := M) D') (hS : IsSolutionOn S) (hT : IsSolutionOn T)
    (R : SmoothRiemannianMetric I M) (q : ℕ) (x : M) {a b L : ℝ}
    (hreg : Icc a b ⊆ D.regular) (hreg' : Icc a b ⊆ D'.regular)
    (hbound : ∀ r ∈ Icc a b,
      Real.sqrt (normSq0S R x (q + 2)
        ((covDerivOfField R (solutionRicField S r) q) x -
          (covDerivOfField R (solutionRicField T r) q) x)) ≤ L)
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    metricDerivNorm q (S.base.metric s) (T.base.metric s) R x ≤
      metricDerivNorm q (S.base.metric t) (T.base.metric t) R x + 2 * L * |s - t| := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let A := fun r => metricCovDeriv (S.base.metric r) R q x -
    metricCovDeriv (T.base.metric r) R q x
  let B := fun r => (-2 : ℝ) •
    ((covDerivOfField R (solutionRicField S r) q) x -
      (covDerivOfField R (solutionRicField T r) q) x)
  have hS' (r : ℝ) (hr : r ∈ Icc a b) (v : Fin (q + 2) → TangentSpace I x) :=
    solutionTower_hasDerivAt R S hS q
      (solutionTowerSwap_regularity R S hS q (fun {_r} h => D.regular_isOpen.mem_nhds h))
      q le_rfl r (hreg hr) x v
  have hT' (r : ℝ) (hr : r ∈ Icc a b) (v : Fin (q + 2) → TangentSpace I x) :=
    solutionTower_hasDerivAt R T hT q
      (solutionTowerSwap_regularity R T hT q (fun {_r} h => D'.regular_isOpen.mem_nhds h))
      q le_rfl r (hreg' hr) x v
  have hderiv : ∀ r ∈ Icc a b, ∀ v : Fin (q + 2) → TangentSpace I x,
      HasDerivWithinAt (fun r => A r v) (B r v) (Icc a b) r := by
    intro r hr v
    have hh := ((hS' r hr v).sub (hT' r hr v)).hasDerivWithinAt (s := Icc a b)
    convert hh using 1 <;>
      first | rfl | (simp only [B,
        solutionEvolutionField, covDerivOfField_smul, ContMDiffSection.coe_smul,
        Pi.smul_apply, Tensor0SSpace.sub_apply,
        Tensor0SSpace.smul_apply, smul_sub])
  have hB : ∀ r ∈ Icc a b, Real.sqrt (normSq0S R x (q + 2) (B r)) ≤ 2 * L := by
    intro r hr
    dsimp only [B]
    rw [sqrt_normSq0S_smul]
    norm_num only [abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact mul_le_mul_of_nonneg_left (hbound r hr) (by norm_num)
  have hdiff := sqrt_normSq0S_sub_le_of_hasDerivWithinAt R x (q + 2) A B hderiv hB hs ht
  have htriangle := _root_.Tensor0SBundle.sqrt_normSq0S_add_le R x (q + 2)
    (A t) (A s - A t)
  rw [add_sub_cancel] at htriangle
  exact htriangle.trans (add_le_add_right hdiff _)

end DifferentialGeometry.PDE.RicciFlow

section

open Filter
namespace DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [SigmaCompactSpace M] [BoundarylessManifold I M]

theorem metricDerivNorm_le_terminal_add_of_ricci_difference_bound
    {D D' : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (T : SolutionOn (I := I) (M := M) D') (hS : IsSolutionOn S) (hT : IsSolutionOn T)
    (R : SmoothRiemannianMetric I M) (q : ℕ) (x : M) {a b L : ℝ}
    (hab : a < b) (hcar : Icc a b ⊆ D.carrier) (hcar' : Icc a b ⊆ D'.carrier)
    (hreg : Ioo a b ⊆ D.regular) (hreg' : Ioo a b ⊆ D'.regular)
    (hbound : ∀ r ∈ Ioo a b,
      Real.sqrt (normSq0S R x (q + 2)
        ((covDerivOfField R (solutionRicField S r) q) x -
          (covDerivOfField R (solutionRicField T r) q) x)) ≤ L)
    {s : ℝ} (hs : s ∈ Ioc a b) :
    metricDerivNorm q (S.base.metric s) (T.base.metric s) R x ≤
      metricDerivNorm q (S.base.metric b) (T.base.metric b) R x + 2 * L * (b - s) := by
  classical
  have hterminal : ContinuousWithinAt
      (fun t => metricDerivNorm q (S.base.metric t) (T.base.metric t) R x) (Iic b) b := by
    obtain ⟨basis, horth⟩ := exists_orthonormal_basis R x
    have hinv := metricInverseInBasis_of_orthonormal R basis horth
    have hnorm (t : ℝ) : metricDerivNorm q (S.base.metric t) (T.base.metric t) R x =
        Real.sqrt (∑ slots, (component0S basis (metricCovDeriv (S.base.metric t) R q x) slots -
          component0S basis (metricCovDeriv (T.base.metric t) R q x) slots) ^ 2) := by
      rw [metricDerivNorm, metricDiffCovDerivAt,
        normSq0S_identity_eq_sum_sq R x (q + 2) basis hinv]
      rfl
    simp only [hnorm]
    apply ContinuousWithinAt.sqrt
    apply tendsto_finsetSum
    intro slots _
    exact ((solution_metricCovDeriv_component_continuousWithinAt_terminal S hS hab hcar
      hreg R q x basis slots).sub
        (solution_metricCovDeriv_component_continuousWithinAt_terminal T hT hab hcar'
          hreg' R q x basis slots)).pow 2
  rcases hs.2.lt_or_eq with hsb | rfl
  · have he : Tendsto
        (fun t => metricDerivNorm q (S.base.metric t) (T.base.metric t) R x + 2 * L * |s - t|)
        (𝓝[<] b) (𝓝 (metricDerivNorm q (S.base.metric b) (T.base.metric b) R x + 2 * L * |s - b|)) :=
      (hterminal.mono Iio_subset_Iic_self).add
        ((continuousAt_const.mul (continuousAt_const.sub continuousAt_id).abs).tendsto.mono_left
          nhdsWithin_le_nhds)
    have htime : |s - b| = b - s := abs_sub_comm s b ▸ abs_of_pos (sub_pos.mpr hsb)
    rw [htime] at he
    apply ge_of_tendsto he
    filter_upwards [Ioo_mem_nhdsLT hsb] with t ht
    exact metricDerivNorm_le_add_of_ricci_difference_bound S T hS hT R q x
      (fun r hr => hreg ⟨hs.1.trans_le hr.1,hr.2.trans_lt ht.2⟩)
      (fun r hr => hreg' ⟨hs.1.trans_le hr.1,hr.2.trans_lt ht.2⟩)
      (fun r hr => hbound r ⟨hs.1.trans_le hr.1,hr.2.trans_lt ht.2⟩)
      ⟨le_rfl,ht.1.le⟩ ⟨ht.1.le,le_rfl⟩
  · simp only [sub_self, mul_zero, add_zero, le_refl]

end DifferentialGeometry.PDE.RicciFlow
end
