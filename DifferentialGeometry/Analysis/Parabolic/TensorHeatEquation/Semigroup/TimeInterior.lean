import DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.Semigroup.WeakIdentification

noncomputable section
open MeasureTheory Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear

open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
  {g : SmoothRiemannianMetric I M} {r s : ℕ} {a T : ℝ}

theorem strongPair_toFun_eq_heatSemigroup_sub
    (u : timeH1 (TensorHs g r s a) T)
    (U : timeL2 (TensorHs g r s (a + 2)) T)
    (hU : timeL2Inclusion (g := g) (r := r) (s := s)
      (show a ≤ a + 2 by linarith) U = timeH1.toTimeL2 _ T u)
    (heq : timeH1.timeDeriv _ T u = timeScaleLaplacian a U)
    {t z : ℝ} (hz : z ∈ Icc (0 : ℝ) t) (ht : t ≤ T) :
    u.toFun t = tensorHeatSemigroupHsExt g r s a (t - z) (u.toFun z) := by
  rw [strongPair_toFun_eq_heatSemigroup u U hU heq ⟨hz.1.trans hz.2, ht⟩,
    strongPair_toFun_eq_heatSemigroup u U hU heq ⟨hz.1, hz.2.trans ht⟩]
  have h := tensorHeatSemigroupHsExt_add (g := g) (r := r) (s := s) (σ := a)
    (sub_nonneg.mpr hz.2) hz.1
  rw [sub_add_cancel] at h
  exact congrArg (fun L => L u.initial) h

theorem strongPair_norm_toFun_le (u : timeH1 (TensorHs g r s a) T)
    (U : timeL2 (TensorHs g r s (a + 2)) T)
    (hU : timeL2Inclusion (g := g) (r := r) (s := s)
      (show a ≤ a + 2 by linarith) U = timeH1.toTimeL2 _ T u)
    (heq : timeH1.timeDeriv _ T u = timeScaleLaplacian a U)
    {t z : ℝ} (hz : z ∈ Icc (0 : ℝ) t) (ht : t ≤ T) :
    ‖u.toFun t‖ ≤ ‖u.toFun z‖ := by
  rw [strongPair_toFun_eq_heatSemigroup_sub u U hU heq hz ht]
  exact ((tensorHeatSemigroupHsExt g r s a (t - z)).le_opNorm _).trans
    ((mul_le_mul_of_nonneg_right
      (tensorHeatSemigroupHsExt_opNorm_le_one (sub_nonneg.mpr hz.2))
      (norm_nonneg _)).trans_eq (one_mul _))

theorem strongPair_norm_toFun_sq_le_timeL2
    (u : timeH1 (TensorHs g r s a) T)
    (U : timeL2 (TensorHs g r s (a + 2)) T)
    (hU : timeL2Inclusion (g := g) (r := r) (s := s)
      (show a ≤ a + 2 by linarith) U = timeH1.toTimeL2 _ T u)
    (heq : timeH1.timeDeriv _ T u = timeScaleLaplacian a U)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ T) :
    ‖u.toFun t‖ ^ 2 ≤ ‖u.toFunL2‖ ^ 2 / t := by
  have hmeasure : timeMeasure t ≤ timeMeasure T :=
    Measure.restrict_mono (Icc_subset_Icc le_rfl htT) le_rfl
  have hrep := (TimeSobolev.coeFn_ofContinuousOn u.continuousOn_toFun).filter_mono
    (ae_mono hmeasure)
  have hi : Integrable (fun z ↦ ‖u.toFunL2 z‖ ^ 2) (timeMeasure T) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable u.toFunL2)).mp
      (Lp.memLp u.toFunL2)
  have hb : ∀ᵐ z ∂timeMeasure t, ‖u.toFun t‖ ^ 2 ≤ ‖u.toFunL2 z‖ ^ 2 := by
    filter_upwards [hrep, ae_restrict_mem measurableSet_Icc] with z hz hmem
    change u.toFunL2 z = u.toFun z at hz
    rw [hz]
    exact pow_le_pow_left₀ (norm_nonneg _) (strongPair_norm_toFun_le u U hU heq hmem htT) 2
  have hbound := integral_mono_ae (integrable_const (‖u.toFun t‖ ^ 2))
    (hi.mono_measure hmeasure) hb
  have hmono := integral_mono_measure hmeasure
    (Filter.Eventually.of_forall fun z => sq_nonneg ‖u.toFunL2 z‖) hi
  rw [integral_const, timeMeasure_real_univ ht.le] at hbound
  have hnorm : (∫ z, ‖u.toFunL2 z‖ ^ 2 ∂timeMeasure T) = ‖u.toFunL2‖ ^ 2 :=
    (TimeSobolev.norm_sq_eq_integral u.toFunL2).symm
  rw [hnorm] at hmono
  apply (le_div_iff₀ ht).mpr
  simpa only [smul_eq_mul, mul_comm] using hbound.trans hmono

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear
end

noncomputable section
open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear

open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
  {g : SmoothRiemannianMetric I M} {r s : ℕ} {a T : ℝ}

theorem strongPair_norm_toFun_le_timeL2
    (u : timeH1 (TensorHs g r s a) T)
    (U : timeL2 (TensorHs g r s (a + 2)) T)
    (hU : timeL2Inclusion (g := g) (r := r) (s := s)
      (show a ≤ a + 2 by linarith) U = timeH1.toTimeL2 _ T u)
    (heq : timeH1.timeDeriv _ T u = timeScaleLaplacian a U)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ T) :
    ‖u.toFun t‖ ≤ ‖u.toFunL2‖ / Real.sqrt t := by
  have h := strongPair_norm_toFun_sq_le_timeL2 u U hU heq ht htT
  have hsq : (‖u.toFunL2‖ / Real.sqrt t) ^ 2 = ‖u.toFunL2‖ ^ 2 / t := by
    rw [div_pow, Real.sq_sqrt ht.le]
  have hnon := div_nonneg (norm_nonneg u.toFunL2) (Real.sqrt_nonneg t)
  nlinarith [sq_nonneg (‖u.toFun t‖ + ‖u.toFunL2‖ / Real.sqrt t)]

theorem strongPair_sobolev_norm_le_timeL2
    (u : timeH1 (TensorHs g r s a) T)
    (U : timeL2 (TensorHs g r s (a + 2)) T)
    (hU : timeL2Inclusion (g := g) (r := r) (s := s)
      (show a ≤ a + 2 by linarith) U = timeH1.toTimeL2 _ T u)
    (heq : timeH1.timeDeriv _ T u = timeScaleLaplacian a U)
    {b t : ℝ} (hab : a ≤ b) (ht : 0 < t) (htT : t ≤ T) (ht2 : t ≤ 2) :
    ‖tensorHeatSemigroupHs (g := g) (r := r) (s := s) ht
      (a := a) (b := b) u.initial‖ ≤
      (Real.sqrt (tensorSmoothingConst (b - a)) *
        (t / 2) ^ (-((b - a) / 2))) * (‖u.toFunL2‖ / Real.sqrt (t / 2)) := by
  have hhalf : 0 < t / 2 := half_pos ht
  have hsplit : tensorHeatSemigroupHs (g := g) (r := r) (s := s) ht
      (a := a) (b := b) u.initial =
      tensorHeatSemigroupHs hhalf (a := a) (b := b) (u.toFun (t / 2)) := by
    rw [strongPair_toFun_eq_heatSemigroup u U hU heq ⟨hhalf.le, by linarith⟩,
      tensorHeatSemigroupHsExt_of_pos hhalf]
    have h := tensorHeatSemigroupHs_add (g := g) (r := r) (s := s)
      hhalf hhalf (a := a) (b := b) (c := a) u.initial
    have htime : t / 2 + t / 2 = t := by ring
    simpa only [htime] using h
  rw [hsplit]
  have hb := (tensorHeatSemigroupHs hhalf (a := a) (b := b)).le_opNorm (u.toFun (t / 2))
  have hs := tensorHeatSemigroupHs_opNorm_le (g := g) (r := r) (s := s)
    hab hhalf (by linarith : t / 2 ≤ 1)
  have hu := strongPair_norm_toFun_le_timeL2 u U hU heq hhalf (by linarith)
  exact hb.trans (mul_le_mul hs hu (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hhalf.le _)))

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear
end
