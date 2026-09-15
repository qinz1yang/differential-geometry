import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Solution.PointwiseSpectralCoordinates
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Duhamel.FiniteProduct
import DifferentialGeometry.Analysis.Parabolic.TensorHeat.Duhamel.MildSolution

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology ENNReal

namespace DifferentialGeometry.Analysis.Parabolic

open TensorSpectral TimeSobolev MaximalRegularity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

namespace TensorHeatEquation

private theorem tensorHeatMildSolutionHs_coeff
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (a : ℝ)
    (u₀ : TensorHs (I := I) (M := M) g r s a)
    {F : ℝ → TensorHs (I := I) (M := M) g r s a}
    (hF : Continuous F) {t : ℝ} (ht : 0 ≤ t)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    (tensorHeatMildSolutionHs (I := I) (M := M) g r s a u₀ F t).coeff i =
      Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) * u₀.coeff i +
        perModeConvolution (TensorEigenIdx.lambda (I := I) (M := M) i)
          (fun q => (F q).coeff i) t := by
  rw [tensorHeatMildSolutionHs_apply, TensorHs.add_coeff]
  dsimp only
  rw [tensorHeatSemigroupHsExt_coeff ht]
  congr 1
  change (QuasiLinear.coeffCLM (I := I) (M := M) (g := g) (r := r) (s := s) (σ := a) i)
    (∫ q in (0 : ℝ)..t, tensorHeatSemigroupHsExt (I := I) (M := M) g r s a (t - q) (F q)) = _
  rw [← (QuasiLinear.coeffCLM (I := I) (M := M)
    (g := g) (r := r) (s := s) (σ := a) i).intervalIntegral_comp_comm
    (tensorHeatMildSolutionHs_integrable (I := I) (M := M) g r s a hF ht)]
  unfold perModeConvolution
  apply intervalIntegral.integral_congr
  intro q hq
  rw [Set.uIcc_of_le ht] at hq
  change (tensorHeatSemigroupHsExt (I := I) (M := M) g r s a (t - q) (F q)).coeff i = _
  rw [tensorHeatSemigroupHsExt_coeff (sub_nonneg.mpr hq.2), neg_mul]

private theorem tensorHeatMildSolutionHs_coeff_of_continuousOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (a : ℝ)
    (u₀ : TensorHs (I := I) (M := M) g r s a)
    {F : ℝ → TensorHs (I := I) (M := M) g r s a}
    {T t : ℝ} (hF : ContinuousOn F (Icc 0 T)) (ht : t ∈ Icc 0 T)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    (tensorHeatMildSolutionHs (I := I) (M := M) g r s a u₀ F t).coeff i =
      Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) * u₀.coeff i +
        perModeConvolution (TensorEigenIdx.lambda (I := I) (M := M) i)
          (fun q => (F q).coeff i) t := by
  let hT : 0 ≤ T := ht.1.trans ht.2
  let Fext : ℝ → TensorHs (I := I) (M := M) g r s a :=
    Set.IccExtend hT (fun q : Icc (0 : ℝ) T => F q)
  have hFext : Continuous Fext := Continuous.Icc_extend' hF.domRestrict
  have hext : ∀ q ∈ Icc (0 : ℝ) T, Fext q = F q := by
    intro q hq
    exact Set.IccExtend_of_mem hT _ hq
  have hmild : tensorHeatMildSolutionHs (I := I) (M := M) g r s a u₀ F t =
      tensorHeatMildSolutionHs (I := I) (M := M) g r s a u₀ Fext t := by
    rw [tensorHeatMildSolutionHs_apply, tensorHeatMildSolutionHs_apply]
    congr 1
    apply intervalIntegral.integral_congr
    intro q hq
    rw [Set.uIcc_of_le ht.1] at hq
    change tensorHeatSemigroupHsExt (I := I) (M := M) g r s a (t - q) (F q) =
      tensorHeatSemigroupHsExt (I := I) (M := M) g r s a (t - q) (Fext q)
    rw [hext q ⟨hq.1, hq.2.trans ht.2⟩]
  rw [hmild, tensorHeatMildSolutionHs_coeff g r s a u₀ hFext ht.1]
  congr 1
  unfold perModeConvolution
  apply intervalIntegral.integral_congr
  intro q hq
  rw [Set.uIcc_of_le ht.1] at hq
  dsimp only
  rw [hext q ⟨hq.1, hq.2.trans ht.2⟩]

end TensorHeatEquation

namespace QuasiLinear

open TensorHeatEquation

variable {g : SmoothRiemannianMetric I M} {r s : ℕ} {a T d : ℝ}

theorem maximalRegularityDuhamelMap_toFun_eq_tensorHeatMildSolutionHs
    (hT : 0 < T) (hdT : d ≤ T)
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (force : timeL2 (TensorHs (I := I) (M := M) g r s a) T)
    {F : ℝ → TensorHs (I := I) (M := M) g r s a}
    (hF : ContinuousOn F (Icc 0 d))
    (hrep : ⇑force =ᵐ[volume.restrict (Icc (0 : ℝ) d)] F)
    {t : ℝ} (ht : t ∈ Icc 0 d) :
    (maximalRegularityDuhamelMap (I := I) (M := M) a hT 0 force).toFun t =
      tensorHeatMildSolutionHs (I := I) (M := M) g r s a 0 F t := by
  have hd : 0 ≤ d := ht.1.trans ht.2
  rcases eq_or_lt_of_le hd with rfl | hd
  · have ht0 : t = 0 := le_antisymm ht.2 ht.1
    rw [ht0, timeH1.toFun_zero, maximalRegularityDuhamelMap_initial,
      map_zero, tensorHeatMildSolutionHs_zero]
  apply TensorHs.ext
  funext i
  have hcoord : ∀ j : TensorEigenIdx (I := I) (M := M) g r s,
      ContinuousOn (fun q => (F q).coeff j) (Icc (0 : ℝ) d) := by
    intro j
    exact (coeffCLM (I := I) (M := M)
      (g := g) (r := r) (s := s) (σ := a) j).continuous.comp_continuousOn hF
  rw [carrier_toFun_coeff_eq_perModeConvolution_IccExtend_restrict hT hd hdT h_compact
    force hcoord hrep i ht,
    tensorHeatMildSolutionHs_coeff_of_continuousOn g r s a 0 hF ht i,
    TensorHs.zero_coeff, mul_zero, zero_add]
  unfold perModeConvolution
  apply intervalIntegral.integral_congr
  intro q hq
  rw [Set.uIcc_of_le ht.1] at hq
  dsimp only
  rw [Set.IccExtend_of_mem hd.le _ ⟨hq.1, hq.2.trans ht.2⟩]

variable {ι : Type*} [Fintype ι]

theorem maximalRegularityDuhamelVectorMap_toFun_eq_tensorHeatMildSolutionHs
    (hT : 0 < T) (hdT : d ≤ T)
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (force : timeL2 (PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s a)) T)
    {F : ℝ → PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s a)}
    (hF : ContinuousOn F (Icc 0 d))
    (hrep : ⇑force =ᵐ[volume.restrict (Icc (0 : ℝ) d)] F)
    {t : ℝ} (ht : t ∈ Icc 0 d) :
    (maximalRegularityDuhamelVectorMap (I := I) (M := M) hT 0 force).toFun t =
      WithLp.toLp 2 (fun i : ι => tensorHeatMildSolutionHs (I := I) (M := M)
        g r s a 0 (fun q => F q i) t) := by
  rw [maximalRegularityDuhamelVectorMap,
    timeH1.piLpEquiv_symm_toFun _ (show t ∈ Icc (0 : ℝ) T from ⟨ht.1, ht.2.trans hdT⟩)]
  apply PiLp.ext
  intro i
  change (maximalRegularityDuhamelMap (I := I) (M := M) a hT 0
    (Lp.piLpEquiv (𝕜 := ℝ) (timeMeasure T) force i)).toFun t = _
  refine maximalRegularityDuhamelMap_toFun_eq_tensorHeatMildSolutionHs
    hT hdT h_compact _
    ((PiLp.proj (p := (2 : ℝ≥0∞)) (𝕜 := ℝ) _ i).continuous.comp_continuousOn hF) ?_ ht
  have hproj := Lp.piLpEquiv_apply (𝕜 := ℝ) (timeMeasure T) force i
  have hproj' := ae_restrict_of_ae_restrict_of_subset (μ := volume)
    (Icc_subset_Icc le_rfl hdT) hproj
  filter_upwards [hproj', hrep] with q hq hqF
  rw [hq, hqF]
  rfl

end QuasiLinear

end DifferentialGeometry.Analysis.Parabolic
