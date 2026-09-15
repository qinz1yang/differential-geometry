import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.AddCircleClassicalDerivative
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.ContinuousMultiplication
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.H1.Basic
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.Multiplication

noncomputable section

open MeasureTheory Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear

open TensorHeatEquation TensorSpectral TimeSobolev
open DifferentialGeometry.Analysis.Spectral

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

variable {ι : Type*} [Fintype ι]

private theorem ae_spatial_time_derivative
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) {T : ℝ}
    (u : timeH1 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ))) T)
    (v : ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 2)))
    (f₀ : PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ)))
    (hlink : ∀ᵐ t ∂timeMeasure T,
      ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
        (g := g) (r := 0) (s := 0)
          (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 2)) (v t) = f₀ + u.toFun t) :
    let C := ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
      (g := g) (r := 0) (s := 0) (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)))
    let f := fun t (x : ℝ) => scalarH1PiToContinuous g (C (f₀ + u.toFun t))
      (x : AddCircle (1 : ℝ))
    ∀ᵐ t ∂timeMeasure T, ContDiff ℝ 2 (f t) ∧ ∀ x : ℝ,
      HasDerivAt (fun s => f s x)
        (scalarH1PiToContinuous g (C (u.deriv t)) (x : AddCircle (1 : ℝ))) t ∧
      deriv (deriv (f t)) x = scalarH1PiToContinuous g
        (C (AddCircle.parameterSecondDerivativeHsPi g 1 (v t)))
        (x : AddCircle (1 : ℝ)) := by
  intro C f
  have hmem : ∀ᵐ t ∂timeMeasure T, t ∈ Ioo (0 : ℝ) T := by
    unfold timeMeasure
    rw [← restrict_Ioo_eq_restrict_Icc]
    exact ae_restrict_mem measurableSet_Ioo
  filter_upwards [hlink, u.ae_hasDerivWithinAt_toFun, hmem] with t ht hdt hmem
  have hlo : ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
      (g := g) (r := 0) (s := 0)
        (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2)) (v t) = C (f₀ + u.toFun t) := by
    rw [← ht]
    apply PiLp.ext
    intro i
    exact tensorHsInclusion_trans_apply (by norm_num) (by norm_num) (v t i)
  let V := ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
    (g := g) (r := 0) (s := 0)
      (by norm_num : ((2 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)) (v t)
  have hV : ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
      (g := g) (r := 0) (s := 0)
        (by norm_num : (1 : ℝ) ≤ ((2 : ℕ) : ℝ) + 1)) V = C (f₀ + u.toFun t) := by
    rw [← hlo]
    apply PiLp.ext
    intro i
    exact (tensorHsInclusion_trans_apply (by norm_num) (by norm_num) (v t i)).symm
  constructor
  · have h := AddCircle.contDiff_two_scalarH1PiToContinuous g V
    rw [hV] at h
    exact h
  · intro x
    constructor
    · let L := (ContinuousMap.evalCLM ℝ (x : AddCircle (1 : ℝ))).comp
        ((scalarH1PiToContinuous (ι := ι) g).comp C)
      exact L.hasFDerivAt.comp_hasDerivAt t
        ((hdt.hasDerivAt (Icc_mem_nhds hmem.1 hmem.2)).const_add f₀)
    · have h := AddCircle.deriv_deriv_scalarH1PiToContinuous g (v t) x
      rw [hlo] at h
      exact h

theorem ae_hasDerivAt_of_circle_sobolev_equation
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) {T : ℝ}
    (u : timeH1 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ))) T)
    (v : ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 2)))
    (f₀ : PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ)))
    (a : ℝ → TensorHs g 0 0 ((1 : ℕ) : ℝ))
    (b : ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ)))
    (hlink : ∀ᵐ t ∂timeMeasure T,
      ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
        (g := g) (r := 0) (s := 0)
          (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 2)) (v t) = f₀ + u.toFun t)
    (hpde : ∀ᵐ t ∂timeMeasure T, u.deriv t =
      ContinuousLinearMap.piLpMap 2 (fun _ : ι => scalarHsMul g 1 (by norm_num) (a t))
        (AddCircle.parameterSecondDerivativeHsPi g 1 (v t)) + b t) :
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ))
    let C := ContinuousLinearMap.piLpMap 2 (fun _ : ι => J)
    let f := fun t (x : ℝ) => scalarH1PiToContinuous g (C (f₀ + u.toFun t))
      (x : AddCircle (1 : ℝ))
    ∀ᵐ t ∂timeMeasure T, ContDiff ℝ 2 (f t) ∧ ∀ x : ℝ,
      HasDerivAt (fun s => f s x)
        (scalarH1ToContinuous g (J (a t)) (x : AddCircle (1 : ℝ)) •
          deriv (deriv (f t)) x + scalarH1PiToContinuous g (C (b t))
            (x : AddCircle (1 : ℝ))) t := by
  intro J C f
  have hrep := ae_spatial_time_derivative g u v f₀ hlink
  filter_upwards [hrep, hpde] with t ht hpde
  refine ⟨ht.1, fun x => ?_⟩
  have hder := (ht.2 x).1
  have hsecond := (ht.2 x).2
  have heq : scalarH1PiToContinuous g (C (u.deriv t)) (x : AddCircle (1 : ℝ)) =
      scalarH1ToContinuous g (J (a t)) (x : AddCircle (1 : ℝ)) •
        deriv (deriv (f t)) x + scalarH1PiToContinuous g (C (b t))
          (x : AddCircle (1 : ℝ)) := by
    rw [hpde, hsecond]
    ext i
    change scalarH1ToContinuous g (J (_ + b t i)) _ = _
    rw [map_add, map_add]
    change scalarH1ToContinuous g (J (scalarHsMul g 1 (by norm_num) (a t)
      (AddCircle.parameterSecondDerivativeHsPi g 1 (v t) i))) _ +
        scalarH1ToContinuous g (J (b t i)) _ = _
    rw [scalarH1ToContinuous_scalarHsMul]
    rfl
  rw [heq] at hder
  exact hder

theorem ae_hasDerivAt_of_circle_sobolev_evolution
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) {T : ℝ}
    (u : timeH1 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ))) T)
    (field : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 2))) T)
    (f₀ : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 2)))
    (force : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ))) T)
    (L : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 2)) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ)))
    (a : ℝ → TensorHs g 0 0 ((1 : ℕ) : ℝ))
    (b : ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ)))
    (hlink : u.toFunL2 =
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
        (g := g) (r := 0) (s := 0)
          (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 2))).compLpL
            2 (timeMeasure T) field)
    (hderiv : u.deriv = L.compLpL 2 (timeMeasure T) field + force)
    (hpde : ∀ᵐ t ∂timeMeasure T, L (field t) + force t =
      ContinuousLinearMap.piLpMap 2 (fun _ : ι => scalarHsMul g 1 (by norm_num) (a t))
        (AddCircle.parameterSecondDerivativeHsPi g 1 (f₀ + field t)) + b t) :
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ))
    let C := ContinuousLinearMap.piLpMap 2 (fun _ : ι => J)
    let K := ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
      (g := g) (r := 0) (s := 0)
        (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 2))
    let f := fun t (x : ℝ) => scalarH1PiToContinuous g (C (K f₀ + u.toFun t))
      (x : AddCircle (1 : ℝ))
    ∀ᵐ t ∂timeMeasure T, ContDiff ℝ 2 (f t) ∧ ∀ x : ℝ,
      HasDerivAt (fun s => f s x)
        (scalarH1ToContinuous g (J (a t)) (x : AddCircle (1 : ℝ)) •
          deriv (deriv (f t)) x + scalarH1PiToContinuous g (C (b t))
            (x : AddCircle (1 : ℝ))) t := by
  intro J C K f
  apply ae_hasDerivAt_of_circle_sobolev_equation g u
    (fun t => f₀ + field t) (K f₀) a b
  · have hcoe := K.coeFn_compLpL (p := 2) (μ := timeMeasure T) field
    have hu := coeFn_ofContinuousOn u.continuousOn_toFun
    filter_upwards [hcoe, hu] with t ht hut
    change u.toFunL2 t = u.toFun t at hut
    rw [hlink] at hut
    change K (f₀ + field t) = K f₀ + u.toFun t
    rw [map_add, ← ht, hut]
  · have hcoe := L.coeFn_compLpL (p := 2) (μ := timeMeasure T) field
    have hadd := Lp.coeFn_add (L.compLpL 2 (timeMeasure T) field) force
    filter_upwards [hcoe, hadd, hpde] with t ht hsum hpdet
    rw [hderiv, hsum, Pi.add_apply, ht]
    exact hpdet

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear
