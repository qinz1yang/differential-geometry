import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Existence.LinearTimeDependent
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Solution.HeatEvolutionInclusion

noncomputable section
open MeasureTheory Filter
open scoped Manifold ContDiff NNReal

namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Spectral

variable {ι : Type*} [Fintype ι]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
variable {g : SmoothRiemannianMetric I M} {r s : ℕ} {a b T : ℝ}

private abbrev HsPi (q : ℝ) := PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s q)

theorem exists_unique_heat_vector_forcing_lift_of_l2_coefficients
    (hab : a ≤ b) (hT : 0 < T)
    (u₀H : HsPi (b + 1)) (u₀L : HsPi (a + 1))
    (hu₀ : u₀L = (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
      (g := g) (r := r) (s := s) (show a + 1 ≤ b + 1 by linarith))) u₀H)
    (A2h : ℝ → HsPi (b + 2) →L[ℝ] HsPi b)
    (hA2h : AEStronglyMeasurable A2h (timeMeasure T))
    (C2h : ℝ≥0) (hC2h : ∀ᵐ t ∂timeMeasure T, ‖A2h t‖ ≤ C2h)
    (A1h : ℝ → HsPi (b + 1) →L[ℝ] HsPi b)
    (hA1h : MemLp A1h 2 (timeMeasure T))
    (f0h : timeL2 (HsPi b) T)
    (hsmallh : (C2h : ℝ) * (1 + T) + Real.sqrt (1 + T) * ‖hA1h.toLp A1h‖ < 1)
    (A2l : ℝ → HsPi (a + 2) →L[ℝ] HsPi a)
    (hA2l : AEStronglyMeasurable A2l (timeMeasure T))
    (C2l : ℝ≥0) (hC2l : ∀ᵐ t ∂timeMeasure T, ‖A2l t‖ ≤ C2l)
    (A1l : ℝ → HsPi (a + 1) →L[ℝ] HsPi a)
    (hA1l : MemLp A1l 2 (timeMeasure T))
    (f0l : timeL2 (HsPi a) T)
    (hsmalll : (C2l : ℝ) * (1 + T) + Real.sqrt (1 + T) * ‖hA1l.toLp A1l‖ < 1)
    (hA2 : ∀ᵐ t ∂timeMeasure T, ∀ x,
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
        (g := g) (r := r) (s := s) hab)) (A2h t x) =
      A2l t ((ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
        (g := g) (r := r) (s := s)
          (show a + 2 ≤ b + 2 by linarith))) x))
    (hA1 : ∀ᵐ t ∂timeMeasure T, ∀ x,
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
        (g := g) (r := r) (s := s) hab)) (A1h t x) =
      A1l t ((ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
        (g := g) (r := r) (s := s)
          (show a + 1 ≤ b + 1 by linarith))) x))
    (hf0 : f0l =
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
        (g := g) (r := r) (s := s)
          hab)).compLpL 2 (timeMeasure T) f0h)
    (fL : timeL2 (HsPi a) T)
    (hfLeq : ∀ᵐ t ∂timeMeasure T,
      fL t = A2l t (heatDuhamelVectorField hT u₀L fL t) +
        A1l t ((ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
          (g := g) (r := r) (s := s)
            (show a + 1 ≤ a + 2 by linarith)))
          (heatDuhamelVectorField hT u₀L fL t)) + f0l t) :
    ∃! fH : timeL2 (HsPi b) T,
      (∀ᵐ t ∂timeMeasure T,
        fH t = A2h t (heatDuhamelVectorField hT u₀H fH t) +
          A1h t ((ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
            (g := g) (r := r) (s := s)
              (show b + 1 ≤ b + 2 by linarith)))
            (heatDuhamelVectorField hT u₀H fH t)) + f0h t) ∧
      fL = (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
        (g := g) (r := r) (s := s) hab)).compLpL 2 (timeMeasure T) fH := by
  obtain ⟨fH, hfH, huniqH⟩ := exists_unique_heat_vector_forcing_of_l2_coefficients
    (g := g) (r := r) (s := s) hT u₀H A2h hA2h C2h hC2h A1h hA1h f0h hsmallh
  obtain ⟨funiqL, _, huniqL⟩ := exists_unique_heat_vector_forcing_of_l2_coefficients
    (g := g) (r := r) (s := s) hT u₀L A2l hA2l C2l hC2l A1l hA1l f0l hsmalll
  let J0 := ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
    (g := g) (r := r) (s := s) hab)
  let J2 : HsPi (b + 2) →L[ℝ] HsPi (a + 2) :=
    ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
      (g := g) (r := r) (s := s) (show a + 2 ≤ b + 2 by linarith))
  let J1 : HsPi (b + 1) →L[ℝ] HsPi (a + 1) :=
    ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
      (g := g) (r := r) (s := s) (show a + 1 ≤ b + 1 by linarith))
  let K1h : HsPi (b + 2) →L[ℝ] HsPi (b + 1) :=
    ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
      (g := g) (r := r) (s := s) (show b + 1 ≤ b + 2 by linarith))
  let K1l : HsPi (a + 2) →L[ℝ] HsPi (a + 1) :=
    ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
      (g := g) (r := r) (s := s) (show a + 1 ≤ a + 2 by linarith))
  let fdown := J0.compLpL 2 (timeMeasure T) fH
  have hD : J2.compLpL 2 (timeMeasure T)
      (heatDuhamelVectorField hT u₀H fH) =
      heatDuhamelVectorField hT u₀L fdown := by
    rw [hu₀]
    exact heatDuhamelVectorField_compLpL_tensorHsInclusion
      (g := g) (r := r) (s := s) (a := a) (b := b) hab hT
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s) u₀H fH
  have hDae : ∀ᵐ t ∂timeMeasure T,
      J2 (heatDuhamelVectorField hT u₀H fH t) =
      heatDuhamelVectorField hT u₀L fdown t := by
    have h := J2.coeFn_compLpL (p := 2) (μ := timeMeasure T)
      (heatDuhamelVectorField hT u₀H fH)
    rw [hD] at h
    exact h.symm
  have hfdown : ∀ᵐ t ∂timeMeasure T, fdown t = J0 (fH t) :=
    J0.coeFn_compLpL (p := 2) (μ := timeMeasure T) fH
  have hf0ae : ∀ᵐ t ∂timeMeasure T, f0l t = J0 (f0h t) := by
    rw [hf0]
    exact J0.coeFn_compLpL (p := 2) (μ := timeMeasure T) f0h
  have hJK (x : HsPi (b + 2)) : J1 (K1h x) = K1l (J2 x) := by
    apply PiLp.ext
    intro i
    apply TensorHs.ext
    rfl
  have hprojected : ∀ᵐ t ∂timeMeasure T,
      fdown t = A2l t (heatDuhamelVectorField hT u₀L fdown t) +
        A1l t (K1l (heatDuhamelVectorField hT u₀L fdown t)) + f0l t := by
    filter_upwards [hfH, hDae, hfdown, hf0ae, hA2, hA1]
      with t he hdt hft h0t ha2 ha1
    rw [hft, he, map_add, map_add, h0t]
    change J0 (A2h t (heatDuhamelVectorField hT u₀H fH t)) +
        J0 (A1h t (K1h (heatDuhamelVectorField hT u₀H fH t))) + J0 (f0h t) =
      A2l t (heatDuhamelVectorField hT u₀L fdown t) +
        A1l t (K1l (heatDuhamelVectorField hT u₀L fdown t)) + J0 (f0h t)
    rw [ha2, ha1]
    change A2l t (J2 (heatDuhamelVectorField hT u₀H fH t)) +
        A1l t (J1 (K1h (heatDuhamelVectorField hT u₀H fH t))) + J0 (f0h t) = _
    rw [hJK, hdt]
  refine ⟨fH, ⟨hfH, (huniqL fL hfLeq).trans (huniqL _ hprojected).symm⟩, ?_⟩
  intro fH' h'
  exact huniqH fH' h'.1

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear
