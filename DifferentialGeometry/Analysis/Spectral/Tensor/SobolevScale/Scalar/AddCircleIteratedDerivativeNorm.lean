import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.AddCircleIteratedDerivativeLift
import DifferentialGeometry.Analysis.FunctionalAnalysis.ContinuousLinearMap.ClosedRange

noncomputable section

open scoped Manifold ContDiff

namespace AddCircle

open DifferentialGeometry DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private abbrev HsPi (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (ι : Type*) (n : ℕ) := PiLp 2 (fun _ : ι => TensorHs g 0 0 (n : ℝ))

private def inclusionPi
    {ι : Type*} (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {n m : ℕ} (h : n ≤ m) : HsPi g ι m →L[ℝ] HsPi g ι n :=
  ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
    tensorHsInclusion (g := g) (r := 0) (s := 0) (by exact_mod_cast h))

private def derivativePi
    {ι : Type*} (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (n m : ℕ) : HsPi g ι (n + m) →L[ℝ] HsPi g ι n :=
  ContinuousLinearMap.piLpMap 2 (fun _ : ι => iteratedParameterDerivativeHs g n m)

private theorem inclusionPi_injective
    {ι : Type*} (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {n m : ℕ} (h : n ≤ m) : Function.Injective (inclusionPi (ι := ι) g h) := by
  intro x y hxy
  apply PiLp.ext
  intro i
  exact tensorHsInclusion_injective (by exact_mod_cast h) (congrArg (fun z => z i) hxy)

private theorem derivativePi_comp_inclusionPi
    {ι : Type*} (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (n m : ℕ) :
    (derivativePi (ι := ι) g (n + 1) m).comp
        (inclusionPi g (show n + 1 + m ≤ n + 2 + m by omega)) =
      (inclusionPi g (show n + 1 ≤ n + 2 by omega)).comp
        (derivativePi g (n + 2) m) := by
  apply ContinuousLinearMap.ext
  intro x
  apply PiLp.ext
  intro i
  exact iteratedParameterDerivativeHs_tensorHsInclusion g
    (show n + 1 ≤ n + 2 by omega) m (x i)

private theorem exists_derivativePi_lift
    {ι : Type*} [Finite ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n m : ℕ)
    (y : HsPi g ι (n + 1 + m)) (z : HsPi g ι (n + 2))
    (hyz : derivativePi g (n + 1) m y =
      inclusionPi g (show n + 1 ≤ n + 2 by omega) z) :
    ∃ x : HsPi g ι (n + 2 + m),
      inclusionPi g (show n + 1 + m ≤ n + 2 + m by omega) x = y ∧
        derivativePi g (n + 2) m x = z := by
  obtain ⟨w, _, hw⟩ :=
    exists_continuousOn_tensorHsInclusion_eq_of_iteratedParameterDerivative_lift
      (X := Unit) g n m (s := Set.univ) (σ := ((n + 1 : ℕ) : ℝ)) le_rfl
      (fun _ => y) (fun _ => z) continuousOn_const continuousOn_const (by
        intro t ht i
        simpa only [derivativePi, inclusionPi, ContinuousLinearMap.piLpMap_apply,
          tensorHsInclusion_refl_apply] using congrArg (fun v => v i) hyz)
  have hwJ : inclusionPi g (show n + 1 + m ≤ n + 2 + m by omega) (w ()) = y :=
    hw () (Set.mem_univ ())
  refine ⟨w (), hwJ, ?_⟩
  apply inclusionPi_injective g (show n + 1 ≤ n + 2 by omega)
  have hcomm := DFunLike.congr_fun (derivativePi_comp_inclusionPi g n m) (w ())
  change derivativePi g (n + 1) m
      (inclusionPi g (show n + 1 + m ≤ n + 2 + m by omega) (w ())) =
    inclusionPi g (show n + 1 ≤ n + 2 by omega) (derivativePi g (n + 2) m (w ()))
      at hcomm
  rw [hwJ] at hcomm
  exact hcomm.symm.trans hyz

theorem exists_norm_piLp_le_max_of_iteratedParameterDerivativeHs
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n m : ℕ) :
    ∃ C ≥ (0 : ℝ), ∀ x : PiLp 2 (fun _ : ι =>
        TensorHs g 0 0 ((n + 2 + m : ℕ) : ℝ)),
      ‖x‖ ≤ C * max
        ‖ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
          tensorHsInclusion (g := g) (r := 0) (s := 0)
            (by exact_mod_cast (show n + 1 + m ≤ n + 2 + m by omega) :
              ((n + 1 + m : ℕ) : ℝ) ≤ ((n + 2 + m : ℕ) : ℝ))) x‖
        ‖ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
          iteratedParameterDerivativeHs g (n + 2) m) x‖ := by
  exact ContinuousLinearMap.exists_norm_le_max_of_lifting
    (inclusionPi (ι := ι) g (show n + 1 + m ≤ n + 2 + m by omega))
    (derivativePi g (n + 2) m) (derivativePi g (n + 1) m)
    (inclusionPi g (show n + 1 ≤ n + 2 by omega))
    (inclusionPi_injective g _) (derivativePi_comp_inclusionPi g n m)
    (exists_derivativePi_lift g n m)

open MeasureTheory Filter
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev

private theorem inclusionPi_compLpL_injective
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {n m : ℕ} (h : n ≤ m) (T : ℝ) :
    Function.Injective ((inclusionPi (ι := ι) g h).compLpL 2 (timeMeasure T)) := by
  let J := inclusionPi (ι := ι) g h
  intro x y hxy
  apply Lp.ext
  have hx := J.coeFn_compLpL (p := 2) (μ := timeMeasure T) x
  have hy := J.coeFn_compLpL (p := 2) (μ := timeMeasure T) y
  rw [hxy] at hx
  filter_upwards [hx, hy] with t ht ht'
  exact inclusionPi_injective g h (ht.symm.trans ht')

private theorem derivativePi_compLpL_inclusionPi
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n m : ℕ) (T : ℝ) :
    ((derivativePi (ι := ι) g (n + 1) m).compLpL 2 (timeMeasure T)).comp
        ((inclusionPi g (show n + 1 + m ≤ n + 2 + m by omega)).compLpL
          2 (timeMeasure T)) =
      ((inclusionPi g (show n + 1 ≤ n + 2 by omega)).compLpL 2 (timeMeasure T)).comp
        ((derivativePi g (n + 2) m).compLpL 2 (timeMeasure T)) := by
  let J := inclusionPi (ι := ι) g (show n + 1 + m ≤ n + 2 + m by omega)
  let K := inclusionPi (ι := ι) g (show n + 1 ≤ n + 2 by omega)
  let QH := derivativePi (ι := ι) g (n + 2) m
  let QL := derivativePi (ι := ι) g (n + 1) m
  apply ContinuousLinearMap.ext
  intro x
  apply Lp.ext
  filter_upwards [QL.coeFn_compLpL (J.compLpL 2 (timeMeasure T) x),
    J.coeFn_compLpL x, K.coeFn_compLpL (QH.compLpL 2 (timeMeasure T) x),
    QH.coeFn_compLpL x] with t hQL hJ hK hQH
  change (QL.compLpL 2 (timeMeasure T) (J.compLpL 2 (timeMeasure T) x)) t =
    (K.compLpL 2 (timeMeasure T) (QH.compLpL 2 (timeMeasure T) x)) t
  rw [hQL, hJ, hK, hQH]
  exact DFunLike.congr_fun (derivativePi_comp_inclusionPi g n m) (x t)

private theorem exists_derivativePi_timeL2_lift
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n m : ℕ) (T : ℝ)
    (y : timeL2 (HsPi g ι (n + 1 + m)) T) (z : timeL2 (HsPi g ι (n + 2)) T)
    (hyz : (derivativePi g (n + 1) m).compLpL 2 (timeMeasure T) y =
      (inclusionPi g (show n + 1 ≤ n + 2 by omega)).compLpL 2 (timeMeasure T) z) :
    ∃ x : timeL2 (HsPi g ι (n + 2 + m)) T,
      (inclusionPi g (show n + 1 + m ≤ n + 2 + m by omega)).compLpL
          2 (timeMeasure T) x = y ∧
        (derivativePi g (n + 2) m).compLpL 2 (timeMeasure T) x = z := by
  let QL := derivativePi (ι := ι) g (n + 1) m
  let K := inclusionPi (ι := ι) g (show n + 1 ≤ n + 2 by omega)
  have hcompat : ∀ᵐ t ∂timeMeasure T, ∀ i : ι,
      tensorHsInclusion (le_refl (((n + 1 : ℕ) : ℝ)))
          (iteratedParameterDerivativeHs g (n + 1) m (y t i)) =
        tensorHsInclusion
          (by exact_mod_cast (show n + 1 ≤ n + 2 by omega) :
            ((n + 1 : ℕ) : ℝ) ≤ ((n + 2 : ℕ) : ℝ)) (z t i) := by
    have hQL := QL.coeFn_compLpL y
    have hK := K.coeFn_compLpL z
    change QL.compLpL 2 (timeMeasure T) y = K.compLpL 2 (timeMeasure T) z at hyz
    rw [hyz] at hQL
    filter_upwards [hQL, hK] with t hQt hKt
    intro i
    simpa only [QL, K, derivativePi, inclusionPi, ContinuousLinearMap.piLpMap_apply,
      tensorHsInclusion_refl_apply] using congrArg (fun v => v i) (hQt.symm.trans hKt)
  obtain ⟨x, hx⟩ := exists_timeL2_tensorHsInclusion_eq_of_iteratedParameterDerivative_lift
    g n m (σ := ((n + 1 : ℕ) : ℝ)) le_rfl y z hcompat
  have hxJ : (inclusionPi g (show n + 1 + m ≤ n + 2 + m by omega)).compLpL
      2 (timeMeasure T) x = y := hx
  refine ⟨x, hxJ, ?_⟩
  apply inclusionPi_compLpL_injective g (show n + 1 ≤ n + 2 by omega) T
  have hcomm := DFunLike.congr_fun (derivativePi_compLpL_inclusionPi g n m T) x
  change (derivativePi g (n + 1) m).compLpL 2 (timeMeasure T)
      ((inclusionPi g (show n + 1 + m ≤ n + 2 + m by omega)).compLpL
        2 (timeMeasure T) x) =
    (inclusionPi g (show n + 1 ≤ n + 2 by omega)).compLpL 2 (timeMeasure T)
      ((derivativePi g (n + 2) m).compLpL 2 (timeMeasure T) x) at hcomm
  rw [hxJ] at hcomm
  exact hcomm.symm.trans hyz

theorem exists_norm_timeL2_le_max_of_iteratedParameterDerivativeHs
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n m : ℕ) (T : ℝ) :
    ∃ C ≥ (0 : ℝ), ∀ x : timeL2 (PiLp 2 (fun _ : ι =>
        TensorHs g 0 0 ((n + 2 + m : ℕ) : ℝ))) T,
      ‖x‖ ≤ C * max
        ‖(ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
          tensorHsInclusion (g := g) (r := 0) (s := 0)
            (by exact_mod_cast (show n + 1 + m ≤ n + 2 + m by omega) :
              ((n + 1 + m : ℕ) : ℝ) ≤ ((n + 2 + m : ℕ) : ℝ)))).compLpL
                2 (timeMeasure T) x‖
        ‖(ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
          iteratedParameterDerivativeHs g (n + 2) m)).compLpL 2 (timeMeasure T) x‖ := by
  let J := (inclusionPi (ι := ι) g (show n + 1 + m ≤ n + 2 + m by omega)).compLpL
    2 (timeMeasure T)
  let QH := (derivativePi (ι := ι) g (n + 2) m).compLpL 2 (timeMeasure T)
  let QL := (derivativePi (ι := ι) g (n + 1) m).compLpL 2 (timeMeasure T)
  let K := (inclusionPi (ι := ι) g (show n + 1 ≤ n + 2 by omega)).compLpL
    2 (timeMeasure T)
  change ∃ C ≥ (0 : ℝ), ∀ x : timeL2 (HsPi g ι (n + 2 + m)) T,
    ‖x‖ ≤ C * max ‖J x‖ ‖QH x‖
  exact ContinuousLinearMap.exists_norm_le_max_of_lifting J QH QL K
    (inclusionPi_compLpL_injective g _ T) (derivativePi_compLpL_inclusionPi g n m T)
    (exists_derivativePi_timeL2_lift g n m T)

end AddCircle

end
