import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Existence.HeatTraceLift

noncomputable section

open MeasureTheory Set Filter
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear

open TensorHeatEquation TensorSpectral TimeSobolev MaximalRegularity

variable {ι : Type*} [Fintype ι]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
variable {g : SmoothRiemannianMetric I M} {r s : ℕ} {a b T : ℝ}

private abbrev HsPi (q : ℝ) := PiLp 2 (fun _ : ι => TensorHs g r s q)

omit [NeZero (Module.finrank ℝ E)] in
theorem heat_vector_forcing_equation_of_tensorHsInclusion
    (hab : a ≤ b) (hT : 0 < T)
    (hc : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (u₀H : HsPi (b + 1)) (u₀L : HsPi (a + 1))
    (hu₀ : u₀L = (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
      (g := g) (r := r) (s := s) (show a + 1 ≤ b + 1 by linarith))) u₀H)
    (A2h : ℝ → HsPi (b + 2) →L[ℝ] HsPi b)
    (A1h : ℝ → HsPi (b + 1) →L[ℝ] HsPi b) (f0h : timeL2 (HsPi b) T)
    (A2l : ℝ → HsPi (a + 2) →L[ℝ] HsPi a)
    (A1l : ℝ → HsPi (a + 1) →L[ℝ] HsPi a) (f0l : timeL2 (HsPi a) T)
    (hA2 : ∀ᵐ t ∂timeMeasure T, ∀ x,
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
        (g := g) (r := r) (s := s) hab)) (A2h t x) =
        A2l t ((ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
          (g := g) (r := r) (s := s) (show a + 2 ≤ b + 2 by linarith))) x))
    (hA1 : ∀ᵐ t ∂timeMeasure T, ∀ x,
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
        (g := g) (r := r) (s := s) hab)) (A1h t x) =
        A1l t ((ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
          (g := g) (r := r) (s := s) (show a + 1 ≤ b + 1 by linarith))) x))
    (hf0 : f0l = (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
      (g := g) (r := r) (s := s) hab)).compLpL 2 (timeMeasure T) f0h)
    (FH : timeL2 (HsPi b) T) (FL : timeL2 (HsPi a) T)
    (hF : FL = (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
      (g := g) (r := r) (s := s) hab)).compLpL 2 (timeMeasure T) FH)
    (hfLeq : ∀ᵐ t ∂timeMeasure T,
      FL t = A2l t (heatDuhamelVectorField hT u₀L FL t) +
        A1l t ((ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
          (g := g) (r := r) (s := s) (show a + 1 ≤ a + 2 by linarith)))
          (heatDuhamelVectorField hT u₀L FL t)) + f0l t) :
    ∀ᵐ t ∂timeMeasure T,
      FH t = A2h t (heatDuhamelVectorField hT u₀H FH t) +
        A1h t ((ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
          (g := g) (r := r) (s := s) (show b + 1 ≤ b + 2 by linarith)))
          (heatDuhamelVectorField hT u₀H FH t)) + f0h t := by
  let J0 : HsPi b →L[ℝ] HsPi a :=
    ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
      (g := g) (r := r) (s := s) hab)
  let J1 : HsPi (b + 1) →L[ℝ] HsPi (a + 1) :=
    ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
      (g := g) (r := r) (s := s) (show a + 1 ≤ b + 1 by linarith))
  let J2 : HsPi (b + 2) →L[ℝ] HsPi (a + 2) :=
    ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
      (g := g) (r := r) (s := s) (show a + 2 ≤ b + 2 by linarith))
  let K1h : HsPi (b + 2) →L[ℝ] HsPi (b + 1) :=
    ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
      (g := g) (r := r) (s := s) (show b + 1 ≤ b + 2 by linarith))
  let K1l : HsPi (a + 2) →L[ℝ] HsPi (a + 1) :=
    ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
      (g := g) (r := r) (s := s) (show a + 1 ≤ a + 2 by linarith))
  have hJ : Function.Injective J0 := by
    intro x y hxy
    apply PiLp.ext
    intro i
    apply tensorHsInclusion_injective hab
    exact congrArg (fun v => v i) hxy
  have hfield : J2.compLpL 2 (timeMeasure T) (heatDuhamelVectorField hT u₀H FH) =
      heatDuhamelVectorField hT u₀L FL := by
    rw [hu₀, hF]
    exact heatDuhamelVectorField_compLpL_tensorHsInclusion hab hT hc u₀H FH
  have hfieldAE : ∀ᵐ t ∂timeMeasure T,
      J2 (heatDuhamelVectorField hT u₀H FH t) = heatDuhamelVectorField hT u₀L FL t := by
    have h := J2.coeFn_compLpL (p := 2) (μ := timeMeasure T)
      (heatDuhamelVectorField hT u₀H FH)
    rw [hfield] at h
    exact h.symm
  have hFAE : ∀ᵐ t ∂timeMeasure T, FL t = J0 (FH t) := by
    rw [hF]
    exact J0.coeFn_compLpL (p := 2) (μ := timeMeasure T) FH
  have hf0AE : ∀ᵐ t ∂timeMeasure T, f0l t = J0 (f0h t) := by
    rw [hf0]
    exact J0.coeFn_compLpL (p := 2) (μ := timeMeasure T) f0h
  have hJK (x : HsPi (b + 2)) : J1 (K1h x) = K1l (J2 x) := by
    apply PiLp.ext
    intro i
    apply TensorHs.ext
    rfl
  filter_upwards [hfLeq, hfieldAE, hFAE, hf0AE, hA2, hA1]
    with t he hdt hFt h0t ha2 ha1
  apply hJ
  change J0 (FH t) = J0 (A2h t (heatDuhamelVectorField hT u₀H FH t) +
    A1h t (K1h (heatDuhamelVectorField hT u₀H FH t)) + f0h t)
  rw [map_add, map_add, ha2, ha1]
  change J0 (FH t) = A2l t (J2 (heatDuhamelVectorField hT u₀H FH t)) +
    A1l t (J1 (K1h (heatDuhamelVectorField hT u₀H FH t))) + J0 (f0h t)
  rw [hJK, hdt, ← h0t, ← hFt]
  exact he

theorem exists_unique_heat_vector_forcing_lift_of_principal_norm_lt_one
    (hab : a ≤ b) (hT : 0 < T)
    (hc : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (u₀L : HsPi (a + 1)) (FL : timeL2 (HsPi a) T)
    (A2h : ℝ → HsPi (b + 2) →L[ℝ] HsPi b)
    (hA2h : AEStronglyMeasurable A2h (timeMeasure T))
    (C2h : ℝ≥0) (hC2h : ∀ᵐ t ∂timeMeasure T, ‖A2h t‖ ≤ C2h)
    (A1h : ℝ → HsPi (b + 1) →L[ℝ] HsPi b)
    (hA1h : MemLp A1h 2 (timeMeasure T)) (f0h : timeL2 (HsPi b) T)
    (A2l : ℝ → HsPi (a + 2) →L[ℝ] HsPi a)
    (hA2l : AEStronglyMeasurable A2l (timeMeasure T))
    (C2l : ℝ≥0) (hC2l : ∀ᵐ t ∂timeMeasure T, ‖A2l t‖ ≤ C2l)
    (A1l : ℝ → HsPi (a + 1) →L[ℝ] HsPi a)
    (hA1l : MemLp A1l 2 (timeMeasure T)) (f0l : timeL2 (HsPi a) T)
    (hA2 : ∀ᵐ t ∂timeMeasure T, ∀ x,
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
        (g := g) (r := r) (s := s) hab)) (A2h t x) =
        A2l t ((ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
          (g := g) (r := r) (s := s) (show a + 2 ≤ b + 2 by linarith))) x))
    (hA1 : ∀ᵐ t ∂timeMeasure T, ∀ x,
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
        (g := g) (r := r) (s := s) hab)) (A1h t x) =
        A1l t ((ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
          (g := g) (r := r) (s := s) (show a + 1 ≤ b + 1 by linarith))) x))
    (hf0 : f0l = (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
      (g := g) (r := r) (s := s) hab)).compLpL 2 (timeMeasure T) f0h)
    (hfLeq : ∀ᵐ t ∂timeMeasure T,
      FL t = A2l t (heatDuhamelVectorField hT u₀L FL t) +
        A1l t ((ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
          (g := g) (r := r) (s := s) (show a + 1 ≤ a + 2 by linarith)))
          (heatDuhamelVectorField hT u₀L FL t)) + f0l t)
    (hC2h_lt : (C2h : ℝ) < 1) (hC2l_lt : (C2l : ℝ) < 1)
    (u₀H : HsPi (b + 1))
    (hu₀ : u₀L = (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
      (g := g) (r := r) (s := s) (show a + 1 ≤ b + 1 by linarith))) u₀H) :
    ∃! FH : timeL2 (HsPi b) T,
      (∀ᵐ t ∂timeMeasure T,
        FH t = A2h t (heatDuhamelVectorField hT u₀H FH t) +
          A1h t ((ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
            (g := g) (r := r) (s := s) (show b + 1 ≤ b + 2 by linarith)))
            (heatDuhamelVectorField hT u₀H FH t)) + f0h t) ∧
      FL = (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
        (g := g) (r := r) (s := s) hab)).compLpL 2 (timeMeasure T) FH := by
  obtain ⟨FH, hFH⟩ := exists_heat_vector_forcing_lift_of_l2_coefficients
    hab hT hc u₀L FL A2h hA2h C2h hC2h A1h hA1h f0h
    A2l hA2l C2l hC2l A1l hA1l f0l hA2 hA1 hf0 hfLeq hC2h_lt hC2l_lt u₀H hu₀
  have heq := heat_vector_forcing_equation_of_tensorHsInclusion hab hT hc u₀H u₀L hu₀
    A2h A1h f0h A2l A1l f0l hA2 hA1 hf0 FH FL hFH hfLeq
  refine ⟨FH, ⟨heq, hFH⟩, ?_⟩
  intro FH' hFH'
  let J : HsPi b →L[ℝ] HsPi a :=
    ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
      (g := g) (r := r) (s := s) hab)
  have hJ : Function.Injective J := by
    intro x y hxy
    apply PiLp.ext
    intro i
    apply tensorHsInclusion_injective hab
    exact congrArg (fun v => v i) hxy
  have hproj : J.compLpL 2 (timeMeasure T) FH' = J.compLpL 2 (timeMeasure T) FH :=
    hFH'.2.symm.trans hFH
  have hleft := J.coeFn_compLpL (p := 2) (μ := timeMeasure T) FH'
  rw [hproj] at hleft
  have hright := J.coeFn_compLpL (p := 2) (μ := timeMeasure T) FH
  apply Lp.ext
  filter_upwards [hleft, hright] with t hl hr
  exact hJ (hl.symm.trans hr)

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear

end
