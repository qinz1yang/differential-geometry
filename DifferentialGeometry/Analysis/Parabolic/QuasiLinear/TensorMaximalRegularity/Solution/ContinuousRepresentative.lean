import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.CrossScaleParabolicTraceContinuity
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Duhamel.FiniteProduct

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff ENNReal

namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear

open TensorHeatEquation TensorSpectral TimeSobolev

variable {ι : Type*} [Fintype ι]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
variable {g : SmoothRiemannianMetric I M} {r s : ℕ} {a T : ℝ}

theorem exists_continuousOn_intermediate_representative
    (hT : 0 < T)
    (u : timeH1 (PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s a)) T)
    (v : timeL2 (PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 2))) T)
    (hlink : ∀ᵐ t ∂timeMeasure T,
      ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
        tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
          (show a ≤ a + 2 by linarith)) (v t) = u.toFun t) :
    ∃ w : ℝ → PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 1)),
      ContinuousOn w (Icc 0 T) ∧
      (∀ t ∈ Icc 0 T, ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
        tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
          (show a ≤ a + 1 by linarith)) (w t) = u.toFun t) ∧
      w =ᵐ[timeMeasure T] fun t => ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
        tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
          (show a + 1 ≤ a + 2 by linarith)) (v t) := by
  let U : ι → CrossScaleField (I := I) (M := M) g r s a T := fun i =>
    { highRegularity := Lp.piLpEquiv (𝕜 := ℝ) (timeMeasure T) v i
      lowRegularity := timeH1.piLpEquiv u i
      link := by
        filter_upwards [hlink, Lp.piLpEquiv_apply (𝕜 := ℝ) (timeMeasure T) v i,
          ae_restrict_mem (μ := volume) measurableSet_Icc] with t htu htv ht
        rw [htv, timeH1.piLpEquiv_toFun u i ht]
        exact congrArg (fun p => p i) htu }
  let w : ℝ → PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 1)) :=
    fun t => WithLp.toLp 2 (fun i => (U i).repr t)
  refine ⟨w, ?_, ?_, ?_⟩
  · exact (PiLp.continuous_toLp 2 _).comp_continuousOn
      (continuousOn_pi.mpr fun i => (U i).continuousOn_repr)
  · intro t ht
    apply PiLp.ext
    intro i
    change tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
      (show a ≤ a + 1 by linarith) ((U i).repr t) = u.toFun t i
    apply TensorHs.ext
    funext j
    rw [tensorHsInclusion_coeff_apply, (U i).repr_coeff hT ht]
    change ((timeH1.piLpEquiv u i).toFun t).coeff j = (u.toFun t i).coeff j
    rw [timeH1.piLpEquiv_toFun u i ht]
  · have hcoeff : ∀ᵐ t ∂timeMeasure T, ∀ i : ι, ∀ j,
        (U i).coeffFun j t = ((U i).highRegularity t).coeff j :=
      ae_all_iff.mpr fun i => (U i).ae_coeffFun_eq_hiL2
    have hproj : ∀ᵐ t ∂timeMeasure T, ∀ i : ι,
        (Lp.piLpEquiv (𝕜 := ℝ) (timeMeasure T) v i) t = v t i :=
      ae_all_iff.mpr fun i => Lp.piLpEquiv_apply (𝕜 := ℝ) (timeMeasure T) v i
    filter_upwards [hcoeff, hproj, ae_restrict_mem (μ := volume) measurableSet_Icc]
      with t htc htp ht
    apply PiLp.ext
    intro i
    apply TensorHs.ext
    funext j
    change ((U i).repr t).coeff j =
      (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        (show a + 1 ≤ a + 2 by linarith) (v t i)).coeff j
    rw [(U i).repr_coeff hT ht, tensorHsInclusion_coeff_apply, htc i j]
    change ((Lp.piLpEquiv (𝕜 := ℝ) (timeMeasure T) v i) t).coeff j = (v t i).coeff j
    rw [htp i]

theorem maximalRegularityDuhamelVectorMap_exists_continuousOn_representative
    (hT : 0 < T)
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (u₀ : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 2)))
    (F : timeL2 (PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s a)) T) :
    ∃ w : ℝ → PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 1)),
      ContinuousOn w (Icc 0 T) ∧
      (∀ t ∈ Icc 0 T, ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
        tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
          (show a ≤ a + 1 by linarith)) (w t) =
            (maximalRegularityDuhamelVectorMap hT u₀ F).toFun t) ∧
      w =ᵐ[timeMeasure T] fun t => ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
        tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
          (show a + 1 ≤ a + 2 by linarith))
          (maximalRegularityDuhamelVectorField hT u₀ F t) := by
  apply exists_continuousOn_intermediate_representative hT
    (maximalRegularityDuhamelVectorMap hT u₀ F)
    (maximalRegularityDuhamelVectorField hT u₀ F)
  let L := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
    tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
      (show a ≤ a + 2 by linarith))
  have hpin := maximalRegularityDuhamelVectorField_toFunL2 hT h_compact u₀ F
  have ha := L.coeFn_compLpL (p := 2) (μ := timeMeasure T)
    (maximalRegularityDuhamelVectorField hT u₀ F)
  have hb := coeFn_ofContinuousOn (maximalRegularityDuhamelVectorMap hT u₀ F).continuousOn_toFun
  filter_upwards [ha, hb] with t hta htb
  change (L.compLpL 2 (timeMeasure T) (maximalRegularityDuhamelVectorField hT u₀ F)) t = _ at hta
  change (maximalRegularityDuhamelVectorMap hT u₀ F).toFunL2 t = _ at htb
  rw [show L.compLpL 2 (timeMeasure T) (maximalRegularityDuhamelVectorField hT u₀ F) =
    (maximalRegularityDuhamelVectorMap hT u₀ F).toFunL2 from hpin] at hta
  exact hta.symm.trans htb

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear
