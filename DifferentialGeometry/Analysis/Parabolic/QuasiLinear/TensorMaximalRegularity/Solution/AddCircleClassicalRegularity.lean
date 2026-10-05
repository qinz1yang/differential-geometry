import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Solution.AddCircleDerivativeContinuity
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.AddCircleFiniteRegularity
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.Multiplication

noncomputable section

open MeasureTheory Filter Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear

open TensorHeatEquation TensorSpectral TimeSobolev
open DifferentialGeometry.Analysis.Spectral

variable {ι : Type*} [Fintype ι]

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

theorem contDiff_and_continuousOn_iteratedDeriv_of_parameterDerivative_forcing_lift
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n : ℕ)
    {T : ℝ} (hT : 0 < T)
    (f₀ : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((n + 1 : ℕ) : ℝ) + 2)))
    (F FH : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((n + 1 : ℕ) : ℝ))) T)
    (hlift : parameterDerivativeDuhamelForcing g n hT F =
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
        tensorHsInclusion (g := g) (r := 0) (s := 0)
          (by exact_mod_cast Nat.le_succ n : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ)))).compLpL
            2 (timeMeasure T) FH) :
    let P := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by exact_mod_cast (show 1 ≤ (n + 1) + 2 by omega) :
          (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) + 2))
    let S := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by exact_mod_cast (show 1 ≤ n + 1 by omega) :
          (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ)))
    let u := maximalRegularityDuhamelVectorMap (g := g) (r := 0) (s := 0)
      (a := ((n + 1 : ℕ) : ℝ)) hT 0 F
    let f := fun t (x : ℝ) => scalarH1PiToContinuous g (P f₀ + S (u.toFun t))
      (x : AddCircle (1 : ℝ))
    (∀ t ∈ Icc 0 T, ContDiff ℝ (n + 2) (f t)) ∧
      ContinuousOn (fun p : ℝ × ℝ => iteratedDeriv (n + 2) (f p.1) p.2)
        (Icc 0 T ×ˢ univ) := by
  intro P S u f
  obtain ⟨W, hW, hWlo, _⟩ :=
    exists_continuousOn_representative_of_parameterDerivative_forcing_lift g n hT F FH hlift
  let K := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
    tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by push_cast; linarith : ((n + 2 : ℕ) : ℝ) + 1 ≤ ((n + 1 : ℕ) : ℝ) + 2))
  have h := AddCircle.contDiff_and_continuousOn_iteratedDeriv_scalarH1PiToContinuous
    g (n + 2) (fun t => P f₀ + S (u.toFun t)) (fun t => K (f₀ + W t))
    (K.continuous.comp_continuousOn (continuousOn_const.add hW)) (fun t ht => by
      apply PiLp.ext
      intro i
      simp only [K, ContinuousLinearMap.piLpMap_apply, PiLp.add_apply,
        ← tensorHsInclusion_trans_apply, map_add]
      change _ = (P f₀) i + (S (u.toFun t)) i
      congr 1
      have hWi := congrArg (fun z => z i) (hWlo t ht)
      have hWi' := congrArg (tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by exact_mod_cast (show 1 ≤ n + 1 by omega) :
          (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ))) hWi
      simpa only [S, ContinuousLinearMap.piLpMap_apply,
        ← tensorHsInclusion_trans_apply] using hWi')
  exact h

theorem hasDerivWithinAt_maximalRegularityDuhamelVectorMap_of_continuousOn_rhs
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {T : ℝ} (hT : 0 < T)
    (F : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ))) T)
    (f₀ : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 2)))
    (W : ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 2)))
    (alpha : ℝ → TensorHs g 0 0 ((1 : ℕ) : ℝ))
    (reaction : ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ)))
    (hWfield : W =ᵐ[timeMeasure T]
      maximalRegularityDuhamelVectorField (g := g) (r := 0) (s := 0)
        (a := ((1 : ℕ) : ℝ)) hT 0 F) :
    let u := maximalRegularityDuhamelVectorMap (g := g) (r := 0) (s := 0)
      (a := ((1 : ℕ) : ℝ)) hT 0 F
    let L := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.tensorScaleLaplacian
        (g := g) (r := 0) (s := 0) ((1 : ℕ) : ℝ))
    let Q := AddCircle.parameterSecondDerivativeHsPi (ι := ι) g 1
    let field := maximalRegularityDuhamelVectorField (g := g) (r := 0) (s := 0)
      (a := ((1 : ℕ) : ℝ)) hT 0 F
    let rhs := fun t =>
      ContinuousLinearMap.piLpMap 2 (fun _ : ι => scalarHsMul g 1 (by norm_num) (alpha t))
        (Q (f₀ + W t)) + reaction t
    ContinuousOn rhs (Icc 0 T) →
    (∀ᵐ t ∂timeMeasure T, L (field t) + F t =
      ContinuousLinearMap.piLpMap 2 (fun _ : ι => scalarHsMul g 1 (by norm_num) (alpha t))
        (Q (f₀ + field t)) + reaction t) →
    ∀ t ∈ Icc 0 T, HasDerivWithinAt u.toFun (rhs t) (Icc 0 T) t := by
  intro u L Q field rhs hRHS hweak
  have hder : u.deriv = L.compLpL 2 (timeMeasure T) field + F :=
    maximalRegularityDuhamelVectorMap_timeDeriv_eq hT
      (tensorResolventL2_isCompactOperator
        (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ)) g 0 0) 0 F
  have hrep : u.deriv =ᵐ[timeMeasure T] rhs := by
    rw [hder]
    filter_upwards [Lp.coeFn_add (L.compLpL 2 (timeMeasure T) field) F,
      L.coeFn_compLpL field, hweak, hWfield] with t hadd hL htEq htW
    rw [hadd, Pi.add_apply, hL, htEq, ← htW]
  intro t htt
  exact u.hasDerivWithinAt_toFun_of_continuousOn hRHS hrep htt

theorem hasDerivAt_maximalRegularityDuhamelVectorMap_of_continuousOn_rhs
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {T : ℝ} (hT : 0 < T)
    (F : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ))) T)
    (f₀ : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 2)))
    (W : ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 2)))
    (alpha : ℝ → TensorHs g 0 0 ((1 : ℕ) : ℝ))
    (reaction : ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ)))
    (hWfield : W =ᵐ[timeMeasure T]
      maximalRegularityDuhamelVectorField (g := g) (r := 0) (s := 0)
        (a := ((1 : ℕ) : ℝ)) hT 0 F) :
    let u := maximalRegularityDuhamelVectorMap (g := g) (r := 0) (s := 0)
      (a := ((1 : ℕ) : ℝ)) hT 0 F
    let L := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.tensorScaleLaplacian
        (g := g) (r := 0) (s := 0) ((1 : ℕ) : ℝ))
    let Q := AddCircle.parameterSecondDerivativeHsPi (ι := ι) g 1
    let field := maximalRegularityDuhamelVectorField (g := g) (r := 0) (s := 0)
      (a := ((1 : ℕ) : ℝ)) hT 0 F
    let rhs := fun t =>
      ContinuousLinearMap.piLpMap 2 (fun _ : ι => scalarHsMul g 1 (by norm_num) (alpha t))
        (Q (f₀ + W t)) + reaction t
    ContinuousOn rhs (Icc 0 T) →
    (∀ᵐ t ∂timeMeasure T, L (field t) + F t =
      ContinuousLinearMap.piLpMap 2 (fun _ : ι => scalarHsMul g 1 (by norm_num) (alpha t))
        (Q (f₀ + field t)) + reaction t) →
    ∀ t ∈ Ioo 0 T, HasDerivAt u.toFun (rhs t) t := by
  intro u L Q field rhs hRHS hweak t htt
  exact (hasDerivWithinAt_maximalRegularityDuhamelVectorMap_of_continuousOn_rhs
    g hT F f₀ W alpha reaction hWfield hRHS hweak t ⟨htt.1.le, htt.2.le⟩).hasDerivAt
      (Icc_mem_nhds htt.1 htt.2)

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear

end
