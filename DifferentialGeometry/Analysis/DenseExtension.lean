import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Algebra.LinearMapCompletion
import Mathlib.Topology.UniformSpace.CompleteSeparated
import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Integral.Bochner.Basic

noncomputable section

open Filter Set
open MeasureTheory
open scoped NNReal Topology

namespace DifferentialGeometry.Analysis

theorem ContinuousLinearMap.norm_fromCompletion
    {X Y : Type*} [SeminormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (f : X →L[ℝ] Y) : ‖f.fromCompletion‖ = ‖f‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg f)
    intro x
    refine UniformSpace.Completion.induction_on x
      (isClosed_le f.fromCompletion.continuous.norm
        (continuous_const.mul continuous_norm)) ?_
    intro y
    simpa using f.le_opNorm y
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg f.fromCompletion)
    intro x
    simpa using f.fromCompletion.le_opNorm
      (x : UniformSpace.Completion X)

noncomputable def bilinearFromCompletion
    {X Y : Type*} [SeminormedAddCommGroup X] [NormedSpace ℝ X]
    [SeminormedAddCommGroup Y] [NormedSpace ℝ Y]
    (F : X →L[ℝ] Y →L[ℝ] ℝ) :
    UniformSpace.Completion X →L[ℝ] UniformSpace.Completion Y →L[ℝ] ℝ :=
  F.fromCompletion.flip.fromCompletion.flip

@[simp] theorem bilinearFromCompletion_apply_coe
    {X Y : Type*} [SeminormedAddCommGroup X] [NormedSpace ℝ X]
    [SeminormedAddCommGroup Y] [NormedSpace ℝ Y]
    (F : X →L[ℝ] Y →L[ℝ] ℝ) (x : X) (y : Y) :
    bilinearFromCompletion F (x : UniformSpace.Completion X)
        (y : UniformSpace.Completion Y) = F x y := by
  simp [bilinearFromCompletion]

theorem norm_bilinearFromCompletion_le
    {X Y : Type*} [SeminormedAddCommGroup X] [NormedSpace ℝ X]
    [SeminormedAddCommGroup Y] [NormedSpace ℝ Y]
    (F : X →L[ℝ] Y →L[ℝ] ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hF : ∀ x y, ‖F x y‖ ≤ C * ‖x‖ * ‖y‖) :
    ‖bilinearFromCompletion F‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound₂ _ hC
  intro x y
  induction x, y using UniformSpace.Completion.induction_on₂ with
  | hp =>
      exact isClosed_le
        (bilinearFromCompletion F).continuous₂.norm
        ((continuous_const.mul (continuous_norm.comp continuous_fst)).mul
          (continuous_norm.comp continuous_snd))
  | ih x y => simpa [bilinearFromCompletion] using hF x y
theorem cont_of_lipBalls {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {D : Set X} (F : D → Y) (x₀ : X)
    (hball : ∀ R : ℝ, ∃ K : ℝ≥0,
      LipschitzOnWith K F {x : D | dist (x : X) x₀ ≤ R}) :
    Continuous F := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨K, hK⟩ := hball (dist (x : X) x₀ + 1)
  refine hK.continuousOn.continuousAt ?_
  have hmem : Metric.closedBall x₀ (dist (x : X) x₀ + 1) ∈ 𝓝 (x : X) :=
    Metric.closedBall_mem_nhds_of_mem
      (by simpa only [Metric.mem_ball] using lt_add_one (dist (x : X) x₀))
  exact continuous_subtype_val.continuousAt.preimage_mem_nhds hmem

theorem cont_extend_lip {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    [CompleteSpace Y] [T0Space Y] {D : Set X} (hD : Dense D) (F : D → Y) (x₀ : X)
    (hball : ∀ R : ℝ, ∃ K : ℝ≥0,
      LipschitzOnWith K F {x : D | dist (x : X) x₀ ≤ R}) :
    Continuous (Dense.extend hD F) := by
  apply hD.isDenseInducing_val.continuous_extend_of_cauchy
  intro x
  let l : Filter D := comap ((↑) : D → X) (𝓝 x)
  have hl : Cauchy l :=
    cauchy_nhds.comap'
      (le_of_eq isUniformEmbedding_subtype_val.isUniformInducing.comap_uniformity)
      (hD.comap_val_nhds_neBot x)
  let R : ℝ := dist x x₀ + 1
  let S : Set D := {d | dist (d : X) x₀ ≤ R}
  obtain ⟨K, hK⟩ := hball R
  have hclosed : Metric.closedBall x₀ R ∈ 𝓝 x :=
    Metric.closedBall_mem_nhds_of_mem
      (by simpa only [Metric.mem_ball, R] using lt_add_one (dist x x₀))
  have hlS : l ≤ 𝓟 S := by
    rw [le_principal_iff]
    have hpre : ((↑) : D → X) ⁻¹' Metric.closedBall x₀ R ∈ l :=
      preimage_mem_comap hclosed
    change ((↑) : D → X) ⁻¹' Metric.closedBall x₀ R ∈ l
    exact hpre
  exact hl.map_of_le hK.uniformContinuousOn hlS

theorem eq_of_lipPair {ι X Y : Type*} [SeminormedAddCommGroup X]
    [NormedAddCommGroup Y] {j : ι → X} {f : ι → Y}
    (hpair : ∀ R : ℝ, ∃ K : ℝ, ∀ v w : ι, ‖j v‖ ≤ R → ‖j w‖ ≤ R →
      ‖f v - f w‖ ≤ K * ‖j v - j w‖)
    {v w : ι} (h : j v = j w) : f v = f w := by
  obtain ⟨K, hK⟩ := hpair ‖j v‖
  have hle := hK v w le_rfl (by rw [← h])
  rw [h, sub_self, norm_zero, mul_zero] at hle
  exact sub_eq_zero.mp (norm_le_zero_iff.mp hle)

private theorem lipBalls_of_pair {ι X Y : Type*} [SeminormedAddCommGroup X]
    [NormedAddCommGroup Y] {j : ι → X} (F : ↥(Set.range j) → Y) (f : ι → Y)
    (hval : ∀ v : ι, F ⟨j v, ⟨v, rfl⟩⟩ = f v)
    (hpair : ∀ R : ℝ, ∃ K : ℝ, ∀ v w : ι, ‖j v‖ ≤ R → ‖j w‖ ≤ R →
      ‖f v - f w‖ ≤ K * ‖j v - j w‖) :
    ∀ R : ℝ, ∃ K : ℝ≥0,
      LipschitzOnWith K F {x : ↥(Set.range j) | dist (x : X) 0 ≤ R} := by
  intro R
  obtain ⟨K, hK⟩ := hpair R
  let K' : ℝ≥0 := ⟨max K 0, le_max_right _ _⟩
  refine ⟨K', ?_⟩
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro x hx y hy
  obtain ⟨v, hv⟩ := x.2
  obtain ⟨w, hw⟩ := y.2
  have hvR : ‖j v‖ ≤ R := by
    have hx' : dist (x : X) 0 ≤ R := hx
    rwa [dist_zero_right, ← hv] at hx'
  have hwR : ‖j w‖ ≤ R := by
    have hy' : dist (y : X) 0 ≤ R := hy
    rwa [dist_zero_right, ← hw] at hy'
  have hxv : x = ⟨j v, ⟨v, rfl⟩⟩ := Subtype.ext hv.symm
  have hyw : y = ⟨j w, ⟨w, rfl⟩⟩ := Subtype.ext hw.symm
  rw [hxv, hyw, hval, hval]
  simp only [Subtype.dist_eq, dist_eq_norm]
  change ‖f v - f w‖ ≤ max K 0 * ‖j v - j w‖
  exact (hK v w hvR hwR).trans
    (mul_le_mul_of_nonneg_right (le_max_left K 0) (norm_nonneg _))

theorem cont_extend_pair {ι X Y : Type*} [SeminormedAddCommGroup X]
    [NormedAddCommGroup Y] [CompleteSpace Y] {j : ι → X} (hj : DenseRange j)
    (F : ↥(Set.range j) → Y) (f : ι → Y)
    (hval : ∀ v : ι, F ⟨j v, ⟨v, rfl⟩⟩ = f v)
    (hpair : ∀ R : ℝ, ∃ K : ℝ, ∀ v w : ι, ‖j v‖ ≤ R → ‖j w‖ ≤ R →
      ‖f v - f w‖ ≤ K * ‖j v - j w‖) :
    Continuous (Dense.extend hj F) :=
  cont_extend_lip hj F 0 (lipBalls_of_pair F f hval hpair)

theorem extend_pair_apply {ι X Y : Type*} [SeminormedAddCommGroup X]
    [NormedAddCommGroup Y] {j : ι → X} (hj : DenseRange j)
    (F : ↥(Set.range j) → Y) (f : ι → Y)
    (hval : ∀ v : ι, F ⟨j v, ⟨v, rfl⟩⟩ = f v)
    (hpair : ∀ R : ℝ, ∃ K : ℝ, ∀ v w : ι, ‖j v‖ ≤ R → ‖j w‖ ≤ R →
      ‖f v - f w‖ ≤ K * ‖j v - j w‖)
    (v : ι) : Dense.extend hj F (j v) = f v :=
  (Dense.extend_eq hj (cont_of_lipBalls F 0 (lipBalls_of_pair F f hval hpair))
    ⟨j v, ⟨v, rfl⟩⟩).trans (hval v)

theorem exists_extend_pair {ι X Y : Type*} [SeminormedAddCommGroup X]
    [NormedAddCommGroup Y] [CompleteSpace Y] {j : ι → X} (hj : DenseRange j)
    (f : ι → Y)
    (hpair : ∀ R : ℝ, ∃ K : ℝ, ∀ v w : ι, ‖j v‖ ≤ R → ‖j w‖ ≤ R →
      ‖f v - f w‖ ≤ K * ‖j v - j w‖) :
    ∃ F : X → Y, Continuous F ∧ ∀ v : ι, F (j v) = f v := by
  classical
  have hval : ∀ v : ι, (f ∘ Set.rangeSplitting j) ⟨j v, ⟨v, rfl⟩⟩ = f v := by
    intro v
    exact eq_of_lipPair hpair (Set.apply_rangeSplitting j ⟨j v, ⟨v, rfl⟩⟩)
  exact ⟨Dense.extend hj (f ∘ Set.rangeSplitting j),
    cont_extend_pair hj _ f hval hpair,
    fun v => extend_pair_apply hj _ f hval hpair v⟩

theorem norm_extend_le {ι X Y : Type*} [SeminormedAddCommGroup X]
    [SeminormedAddCommGroup Y] {j : ι → X} (hj : DenseRange j) {f : ι → Y}
    {F : X → Y} {Φ : ℝ → ℝ} (hF : Continuous F) (hΦ : Continuous Φ)
    (hval : ∀ v : ι, F (j v) = f v) (hbd : ∀ v : ι, ‖f v‖ ≤ Φ ‖j v‖) (x : X) :
    ‖F x‖ ≤ Φ ‖x‖ := by
  refine hj.induction_on x (isClosed_le hF.norm (hΦ.comp continuous_norm)) ?_
  intro v
  rw [hval v]
  exact hbd v

theorem exists_extend_le {ι X Y : Type*} [SeminormedAddCommGroup X]
    [NormedAddCommGroup Y] [CompleteSpace Y] {j : ι → X} (hj : DenseRange j)
    (f : ι → Y) {Φ : ℝ → ℝ} (hΦ : Continuous Φ)
    (hpair : ∀ R : ℝ, ∃ K : ℝ, ∀ v w : ι, ‖j v‖ ≤ R → ‖j w‖ ≤ R →
      ‖f v - f w‖ ≤ K * ‖j v - j w‖)
    (hbd : ∀ v : ι, ‖f v‖ ≤ Φ ‖j v‖) :
    ∃ F : X → Y, Continuous F ∧ (∀ v : ι, F (j v) = f v) ∧
      ∀ x : X, ‖F x‖ ≤ Φ ‖x‖ := by
  obtain ⟨F, hFc, hFv⟩ := exists_extend_pair hj f hpair
  exact ⟨F, hFc, hFv, fun x => norm_extend_le hj hFc hΦ hFv hbd x⟩

theorem ContinuousOn.clm_apply_of_denseRange
    {𝕜 ι P X Y : Type*} [NontriviallyNormedField 𝕜]
    [SeminormedAddCommGroup X] [NormedSpace 𝕜 X]
    [SeminormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    [TopologicalSpace P] {j : ι → X} (hj : DenseRange j)
    {F : P → X →L[𝕜] Y} {K : Set P}
    (hFj : ∀ i, ContinuousOn (fun p => F p (j i)) K)
    {C : ℝ} (hbound : ∀ p ∈ K, ‖F p‖ ≤ C)
    (x : X) :
    ContinuousOn (fun p => F p x) K := by
  apply continuousOn_of_uniform_approx_of_continuousOn
  intro u hu
  obtain ⟨ε, hε, hεu⟩ := Metric.uniformity_basis_dist.mem_iff.mp hu
  let D : ℝ := max C 0
  have hD : 0 < D + 1 :=
    add_pos_of_nonneg_of_pos (le_max_right C 0) zero_lt_one
  obtain ⟨i, hi⟩ := hj.exists_dist_lt x (div_pos hε hD)
  refine ⟨fun p => F p (j i), hFj i, ?_⟩
  intro p hp
  apply hεu
  calc
    dist (F p x) (F p (j i)) ≤ ‖F p‖ * dist x (j i) :=
      (F p).dist_le_opNorm x (j i)
    _ ≤ D * dist x (j i) :=
      mul_le_mul_of_nonneg_right ((hbound p hp).trans (le_max_left C 0)) dist_nonneg
    _ ≤ (D + 1) * dist x (j i) :=
      mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) dist_nonneg
    _ < (D + 1) * (ε / (D + 1)) := mul_lt_mul_of_pos_left hi hD
    _ = ε := by field_simp

theorem AEStronglyMeasurable.clm_apply_of_denseRange
    {𝕜 ι P X Y : Type*} [NontriviallyNormedField 𝕜]
    [SeminormedAddCommGroup X] [NormedSpace 𝕜 X]
    [SeminormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    [MeasurableSpace P] {j : ι → X} (hj : DenseRange j)
    {F : P → X →L[𝕜] Y} {μ : Measure P}
    (hFj : ∀ i, AEStronglyMeasurable (fun p => F p (j i)) μ)
    (x : X) :
    AEStronglyMeasurable (fun p => F p x) μ := by
  obtain ⟨u, hu, hux⟩ := mem_closure_iff_seq_limit.mp (hj x)
  choose i hi using hu
  have hji : Tendsto (fun m => j (i m)) atTop (nhds x) := by
    convert hux using 1
    funext m
    exact hi m
  exact aestronglyMeasurable_of_tendsto_ae atTop (fun m => hFj (i m))
    (Eventually.of_forall fun p => (F p).continuous.continuousAt.tendsto.comp hji)

theorem AEStronglyMeasurable.clm_apply₂_of_denseRange
    {𝕜 ι κ P X Y Z : Type*} [NontriviallyNormedField 𝕜]
    [SeminormedAddCommGroup X] [NormedSpace 𝕜 X]
    [SeminormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    [SeminormedAddCommGroup Z] [NormedSpace 𝕜 Z]
    [MeasurableSpace P] {j : ι → X} {k : κ → Z}
    (hj : DenseRange j) (hk : DenseRange k)
    {F : P → X →L[𝕜] Z →L[𝕜] Y} {μ : Measure P}
    (hFj : ∀ i l, AEStronglyMeasurable (fun p ↦ F p (j i) (k l)) μ)
    (x : X) (z : Z) :
    AEStronglyMeasurable (fun p ↦ F p x z) μ := by
  have hleft (i : ι) :
      AEStronglyMeasurable (fun p ↦ F p (j i) z) μ :=
    AEStronglyMeasurable.clm_apply_of_denseRange hk (hFj i) z
  have hright :
      AEStronglyMeasurable (fun p ↦ (F p).flip z x) μ :=
    AEStronglyMeasurable.clm_apply_of_denseRange hj hleft x
  simpa only [ContinuousLinearMap.flip_apply] using hright

end DifferentialGeometry.Analysis

end
