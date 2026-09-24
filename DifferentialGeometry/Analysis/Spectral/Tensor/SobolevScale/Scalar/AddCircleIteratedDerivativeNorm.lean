import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.AddCircleIteratedDerivativeLift
import DifferentialGeometry.Analysis.FunctionalAnalysis.ContinuousLinearMap.ClosedRange
import DifferentialGeometry.Analysis.FunctionalAnalysis.ContinuousLinearMap.Perturbation
import Mathlib.Topology.MetricSpace.Pseudo.Basic

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
open scoped Topology

private theorem tendsto_of_fixed_graph_estimate
    {X Y Z P : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {l : Filter P} (J : X →L[ℝ] Y) (D : X →L[ℝ] Z)
    (x₀ : X) (x : P → X) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ v, ‖v‖ ≤ C * max ‖J v‖ ‖D v‖)
    (hJ : Tendsto (fun p => J (x p)) l (𝓝 (J x₀)))
    (hD : Tendsto (fun p => D (x p)) l (𝓝 (D x₀))) : Tendsto x l (𝓝 x₀) :=
  ContinuousLinearMap.tendsto_of_tendsto_apply_of_norm_le_max
    J D (fun _ : P => D) x₀ x hC hb tendsto_const_nhds hJ hD

theorem tendsto_timeL2_of_tensorHsInclusion_of_iteratedParameterDerivativeHs
    {ι P : Type*} [Fintype ι] {l : Filter P}
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n m : ℕ) (T : ℝ)
    (W₀ : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((n + 2 + m : ℕ) : ℝ))) T)
    (W : P → timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((n + 2 + m : ℕ) : ℝ))) T) :
    let J := (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by exact_mod_cast (show n + 1 + m ≤ n + 2 + m by omega) :
          ((n + 1 + m : ℕ) : ℝ) ≤ ((n + 2 + m : ℕ) : ℝ)))).compLpL 2 (timeMeasure T)
    let D := (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      iteratedParameterDerivativeHs g (n + 2) m)).compLpL 2 (timeMeasure T)
    Tendsto (fun p => J (W p)) l (𝓝 (J W₀)) →
    Tendsto (fun p => D (W p)) l (𝓝 (D W₀)) →
    Tendsto W l (𝓝 W₀) := by
  intro J D hJ hD
  obtain ⟨C, hC, hbound⟩ :=
    exists_norm_timeL2_le_max_of_iteratedParameterDerivativeHs (ι := ι) g n m T
  change ∀ x, ‖x‖ ≤ C * max ‖J x‖ ‖D x‖ at hbound
  exact tendsto_of_fixed_graph_estimate J D W₀ W hC hbound hJ hD

theorem tendstoUniformlyOn_of_tensorHsInclusion_of_iteratedParameterDerivativeHs
    {ι P X : Type*} [Finite ι] {l : Filter P} {s : Set X}
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n m : ℕ)
    (W₀ : X → PiLp 2 (fun _ : ι => TensorHs g 0 0 ((n + 2 + m : ℕ) : ℝ)))
    (W : P → X → PiLp 2 (fun _ : ι => TensorHs g 0 0 ((n + 2 + m : ℕ) : ℝ)))
    (hJ : TendstoUniformlyOn (fun p x =>
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
        tensorHsInclusion (g := g) (r := 0) (s := 0)
          (by exact_mod_cast (show n + 1 + m ≤ n + 2 + m by omega) :
            ((n + 1 + m : ℕ) : ℝ) ≤ ((n + 2 + m : ℕ) : ℝ)))) (W p x))
      (fun x => (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
        tensorHsInclusion (g := g) (r := 0) (s := 0)
          (by exact_mod_cast (show n + 1 + m ≤ n + 2 + m by omega) :
            ((n + 1 + m : ℕ) : ℝ) ≤ ((n + 2 + m : ℕ) : ℝ)))) (W₀ x)) l s)
    (hD : TendstoUniformlyOn (fun p x =>
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
        iteratedParameterDerivativeHs g (n + 2) m)) (W p x))
      (fun x => (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
        iteratedParameterDerivativeHs g (n + 2) m)) (W₀ x)) l s) :
    TendstoUniformlyOn W W₀ l s := by
  let _ := Fintype.ofFinite ι
  let J := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
    tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by exact_mod_cast (show n + 1 + m ≤ n + 2 + m by omega) :
        ((n + 1 + m : ℕ) : ℝ) ≤ ((n + 2 + m : ℕ) : ℝ)))
  let D := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
    iteratedParameterDerivativeHs g (n + 2) m)
  obtain ⟨C, hC, hbound⟩ :=
    exists_norm_piLp_le_max_of_iteratedParameterDerivativeHs (ι := ι) g n m
  change TendstoUniformlyOn (fun p x => J (W p x)) (fun x => J (W₀ x)) l s at hJ
  change TendstoUniformlyOn (fun p x => D (W p x)) (fun x => D (W₀ x)) l s at hD
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have hC1 : 0 < C + 1 := by linarith
  have hδ : 0 < ε / (C + 1) := div_pos hε hC1
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hJ _ hδ,
    Metric.tendstoUniformlyOn_iff.mp hD _ hδ] with p hp hq
  intro x hx
  have hj : ‖J (W₀ x - W p x)‖ < ε / (C + 1) := by
    simpa only [map_sub, dist_eq_norm] using hp x hx
  have hd : ‖D (W₀ x - W p x)‖ < ε / (C + 1) := by
    simpa only [map_sub, dist_eq_norm] using hq x hx
  have hmax : max ‖J (W₀ x - W p x)‖ ‖D (W₀ x - W p x)‖ < ε / (C + 1) :=
    max_lt hj hd
  have hnonneg : 0 ≤ max ‖J (W₀ x - W p x)‖ ‖D (W₀ x - W p x)‖ :=
    le_trans (norm_nonneg _) (le_max_left _ _)
  have hsmall :
      (C + 1) * max ‖J (W₀ x - W p x)‖ ‖D (W₀ x - W p x)‖ < ε := by
    calc
      _ < (C + 1) * (ε / (C + 1)) := mul_lt_mul_of_pos_left hmax hC1
      _ = ε := mul_div_cancel₀ ε hC1.ne'
  rw [dist_eq_norm]
  exact (hbound (W₀ x - W p x)).trans_lt
    ((mul_le_mul_of_nonneg_right (by linarith : C ≤ C + 1) hnonneg).trans_lt hsmall)


end AddCircle

end
