import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Existence.LinearTimeDependentInclusion
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Solution.HeatEvolutionRestart
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Bochner.LocalSmallness
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.H1.Approximation.Slice
import DifferentialGeometry.Topology.Order.IntervalContinuation
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Bochner.FiniteCover
import Mathlib.Topology.UnitInterval

noncomputable section

open MeasureTheory Set Filter
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

private theorem memLp_operator_add_timeMeasure
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {T c d : ℝ}
    (A : ℝ → X →L[ℝ] Y) (hA : MemLp A 2 (timeMeasure T))
    (hc : 0 ≤ c) (hd : d ≤ T) :
    MemLp (fun t => A (t + c)) 2 (timeMeasure (d - c)) :=
  MemLp.ae_eq ((timeL2.slice_coe (hA.toLp A) c d hc hd).trans
    (ae_add_right_timeMeasure hc hd hA.coeFn_toLp))
    (Lp.memLp (timeL2.slice (hA.toLp A) c d hc hd))

private theorem toLp_operator_add_eq_slice
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {T c d : ℝ}
    (A : ℝ → X →L[ℝ] Y) (hA : MemLp A 2 (timeMeasure T))
    (hc : 0 ≤ c) (hd : d ≤ T)
    (hshift : MemLp (fun t => A (t + c)) 2 (timeMeasure (d - c))) :
    hshift.toLp (fun t => A (t + c)) = timeL2.slice (hA.toLp A) c d hc hd := by
  apply Lp.ext
  exact hshift.coeFn_toLp.trans
    (((timeL2.slice_coe (hA.toLp A) c d hc hd).trans
      (ae_add_right_timeMeasure hc hd hA.coeFn_toLp)).symm)

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev

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
private theorem heat_vector_forcing_equation_slice
    (hT : 0 < T)
    (hc : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (u₀L : HsPi (a + 1)) (FL : timeL2 (HsPi a) T)
    (A2l : ℝ → HsPi (a + 2) →L[ℝ] HsPi a)
    (A1l : ℝ → HsPi (a + 1) →L[ℝ] HsPi a) (f0l : timeL2 (HsPi a) T)
    (hfLeq : ∀ᵐ t ∂timeMeasure T,
      FL t = A2l t (heatDuhamelVectorField hT u₀L FL t) +
        A1l t ((ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
          (g := g) (r := r) (s := s) (show a + 1 ≤ a + 2 by linarith)))
          (heatDuhamelVectorField hT u₀L FL t)) + f0l t)
    {c d : ℝ} (hc0 : 0 ≤ c) (hcd : c < d) (hdT : d ≤ T) :
    let vL := heatDuhamelVectorTrace hT hc u₀L FL c
    let Fs := timeL2.slice FL c d hc0 hdT
    let Us := heatDuhamelVectorField (sub_pos.mpr hcd) vL Fs
    ∀ᵐ t ∂timeMeasure (d - c),
      Fs t = A2l (t + c) (Us t) +
        A1l (t + c) ((ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
          (g := g) (r := r) (s := s) (show a + 1 ≤ a + 2 by linarith))) (Us t)) +
        timeL2.slice f0l c d hc0 hdT t := by
  intro vL Fs Us
  have hUs : timeL2.slice (heatDuhamelVectorField hT u₀L FL) c d hc0 hdT = Us :=
    (heatDuhamelVectorEvolution_slice hT hc u₀L FL hc0 hcd hdT).1
  have hUseq : Us =ᵐ[timeMeasure (d - c)]
      fun t => heatDuhamelVectorField hT u₀L FL (t + c) := by
    rw [← hUs]
    exact timeL2.slice_coe _ c d hc0 hdT
  filter_upwards [ae_add_right_timeMeasure hc0 hdT hfLeq,
    timeL2.slice_coe FL c d hc0 hdT, timeL2.slice_coe f0l c d hc0 hdT,
    hUseq] with t he hF hf hU
  change Fs t = FL (t + c) at hF
  rw [hF, hU, hf]
  exact he

omit [NeZero (Module.finrank ℝ E)] in
private theorem heat_vector_trace_eq_on_Icc_of_lift
    (hab : a ≤ b) (hT : 0 < T)
    (hc : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (u₀L : HsPi (a + 1)) (FL : timeL2 (HsPi a) T)
    {c d : ℝ} (hc0 : 0 ≤ c) (hcd : c < d) (hdT : d ≤ T)
    (vH : HsPi (b + 1))
    (hvH : heatDuhamelVectorTrace hT hc u₀L FL c =
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
        (g := g) (r := r) (s := s) (show a + 1 ≤ b + 1 by linarith))) vH)
    (FH : timeL2 (HsPi b) (d - c))
    (hFH : timeL2.slice FL c d hc0 hdT =
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
        (g := g) (r := r) (s := s) hab)).compLpL 2 (timeMeasure (d - c)) FH) :
    ∀ t ∈ Icc c d,
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
        (g := g) (r := r) (s := s) (show a + 1 ≤ b + 1 by linarith)))
        (heatDuhamelVectorTrace (sub_pos.mpr hcd) hc vH FH (t - c)) =
        heatDuhamelVectorTrace hT hc u₀L FL t := by
  intro t ht
  have ht' : t - c ∈ Icc (0 : ℝ) (d - c) := by
    constructor <;> linarith [ht.1, ht.2]
  have htrace := heatDuhamelVectorTrace_tensorHsInclusion hab (sub_pos.mpr hcd)
    hc vH FH ht'
  rw [← hvH, ← hFH] at htrace
  have hrestart := heatDuhamelVectorTrace_toFun_add hT hc u₀L FL hc0 hcd hdT ht'
  have hct : c + (t - c) = t := by ring
  simpa only [hct] using htrace.trans hrestart.symm

theorem exists_heat_vector_trace_lift_on_Icc
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
    {c d : ℝ} (hc0 : 0 ≤ c) (hcd : c < d) (hdT : d ≤ T)
    (vH : HsPi (b + 1))
    (hvH : heatDuhamelVectorTrace hT hc u₀L FL c =
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
        (g := g) (r := r) (s := s) (show a + 1 ≤ b + 1 by linarith))) vH)
    (hsmallh : (C2h : ℝ) * (1 + (d - c)) + Real.sqrt (1 + (d - c)) *
      ‖timeL2.slice (hA1h.toLp A1h) c d hc0 hdT‖ < 1)
    (hsmalll : (C2l : ℝ) * (1 + (d - c)) + Real.sqrt (1 + (d - c)) *
      ‖timeL2.slice (hA1l.toLp A1l) c d hc0 hdT‖ < 1) :
    ∃ FH : timeL2 (HsPi b) (d - c),
      (∀ᵐ t ∂timeMeasure (d - c),
        FH t = A2h (t + c) (heatDuhamelVectorField (sub_pos.mpr hcd) vH FH t) +
          A1h (t + c) ((ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
            (g := g) (r := r) (s := s) (show b + 1 ≤ b + 2 by linarith)))
            (heatDuhamelVectorField (sub_pos.mpr hcd) vH FH t)) +
          timeL2.slice f0h c d hc0 hdT t) ∧
      timeL2.slice FL c d hc0 hdT =
        (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
          (g := g) (r := r) (s := s) hab)).compLpL 2 (timeMeasure (d - c)) FH ∧
      ∀ t ∈ Icc c d,
        (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
          (g := g) (r := r) (s := s) (show a + 1 ≤ b + 1 by linarith)))
          (heatDuhamelVectorTrace (sub_pos.mpr hcd) hc vH FH (t - c)) =
          heatDuhamelVectorTrace hT hc u₀L FL t := by
  let vL := heatDuhamelVectorTrace hT hc u₀L FL c
  let Fs := timeL2.slice FL c d hc0 hdT
  have hFsEq := heat_vector_forcing_equation_slice hT hc u₀L FL A2l A1l f0l
    hfLeq hc0 hcd hdT
  have hf0s : timeL2.slice f0l c d hc0 hdT =
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
        (g := g) (r := r) (s := s) hab)).compLpL 2 (timeMeasure (d - c))
          (timeL2.slice f0h c d hc0 hdT) := by
    rw [hf0, timeL2.slice_compLpL]
  have hshifth : MemLp (fun t => A1h (t + c)) 2 (timeMeasure (d - c)) :=
    memLp_operator_add_timeMeasure A1h hA1h hc0 hdT
  have hshiftl : MemLp (fun t => A1l (t + c)) 2 (timeMeasure (d - c)) :=
    memLp_operator_add_timeMeasure A1l hA1l hc0 hdT
  have hsmallh' : (C2h : ℝ) * (1 + (d - c)) + Real.sqrt (1 + (d - c)) *
      ‖hshifth.toLp (fun t => A1h (t + c))‖ < 1 := by
    rw [toLp_operator_add_eq_slice A1h hA1h hc0 hdT hshifth]
    exact hsmallh
  have hsmalll' : (C2l : ℝ) * (1 + (d - c)) + Real.sqrt (1 + (d - c)) *
      ‖hshiftl.toLp (fun t => A1l (t + c))‖ < 1 := by
    rw [toLp_operator_add_eq_slice A1l hA1l hc0 hdT hshiftl]
    exact hsmalll
  obtain ⟨FH, hFH, _⟩ := exists_unique_heat_vector_forcing_lift_of_l2_coefficients
    (ι := ι) (E := E) (H := H) (I := I) (M := M) (g := g)
    (r := r) (s := s) (a := a) (b := b) (T := d - c)
    hab (sub_pos.mpr hcd) vH vL hvH
    (fun t => A2h (t + c))
    (aestronglyMeasurable_add_timeMeasure (X := HsPi (b + 2) →L[ℝ] HsPi b) hA2h hc0 hdT)
    C2h (ae_add_right_timeMeasure hc0 hdT hC2h)
    (fun t => A1h (t + c)) hshifth (timeL2.slice f0h c d hc0 hdT) hsmallh'
    (fun t => A2l (t + c))
    (aestronglyMeasurable_add_timeMeasure (X := HsPi (a + 2) →L[ℝ] HsPi a) hA2l hc0 hdT)
    C2l (ae_add_right_timeMeasure hc0 hdT hC2l)
    (fun t => A1l (t + c)) hshiftl (timeL2.slice f0l c d hc0 hdT) hsmalll'
    (ae_add_right_timeMeasure hc0 hdT hA2) (ae_add_right_timeMeasure hc0 hdT hA1)
    hf0s Fs hFsEq
  exact ⟨FH, hFH.1, hFH.2,
    heat_vector_trace_eq_on_Icc_of_lift hab hT hc u₀L FL hc0 hcd hdT vH hvH FH hFH.2⟩

theorem exists_heat_vector_trace_lift_of_l2_coefficients
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
    ∀ t ∈ Icc (0 : ℝ) T, ∃ vH : HsPi (b + 1),
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
        (g := g) (r := r) (s := s) (show a + 1 ≤ b + 1 by linarith))) vH =
        heatDuhamelVectorTrace hT hc u₀L FL t := by
  obtain ⟨δh, hδh, _, hwindowh⟩ :=
    exists_pos_l2_slice_contraction_lt hT (hA1h.toLp A1h) C2h hC2h_lt
  obtain ⟨δl, hδl, _, hwindowl⟩ :=
    exists_pos_l2_slice_contraction_lt hT (hA1l.toLp A1l) C2l hC2l_lt
  let δ := min δh δl
  have hδ : 0 < δ := lt_min hδh hδl
  refine Set.forall_mem_Icc_of_uniform_forward_propagation (a := 0) (b := T) (δ := δ)
    (P := fun t => ∃ vH : HsPi (b + 1),
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
        (g := g) (r := r) (s := s) (show a + 1 ≤ b + 1 by linarith))) vH =
        heatDuhamelVectorTrace hT hc u₀L FL t) hδ ?_ ?_
  · refine ⟨u₀H, ?_⟩
    rw [heatDuhamelVectorTrace_initial]
    exact hu₀.symm
  · intro c hcI hPc t ht
    by_cases hcT : c < T
    · obtain ⟨vH, hvH⟩ := hPc
      let d := min (c + δ) T
      have hcd : c < d := lt_min (lt_add_of_pos_right c hδ) hcT
      have hdT : d ≤ T := min_le_right _ _
      have hDc : 0 ≤ d - c := sub_nonneg.mpr hcd.le
      have hDδ : d - c ≤ δ := by
        have h := min_le_left (c + δ) T
        dsimp only [d]
        linarith
      have hsmallh := hwindowh c d hcI.1 hdT hDc (hDδ.trans (min_le_left _ _))
      have hsmalll := hwindowl c d hcI.1 hdT hDc (hDδ.trans (min_le_right _ _))
      obtain ⟨FH, _, _, htrace⟩ := exists_heat_vector_trace_lift_on_Icc
        hab hT hc u₀L FL A2h hA2h C2h hC2h A1h hA1h f0h
        A2l hA2l C2l hC2l A1l hA1l f0l hA2 hA1 hf0 hfLeq
        hcI.1 hcd hdT vH hvH.symm hsmallh hsmalll
      exact ⟨heatDuhamelVectorTrace (sub_pos.mpr hcd) hc vH FH (t - c), htrace t ht⟩
    · have hcT' : c = T := le_antisymm hcI.2 (le_of_not_gt hcT)
      have htc : t = c := le_antisymm
        (ht.2.trans ((min_le_right _ _).trans hcT'.ge)) ht.1
      simpa only [htc] using hPc

theorem exists_heat_vector_forcing_lift_of_l2_coefficients
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
    ∃ FH : timeL2 (HsPi b) T,
      FL = (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
        (g := g) (r := r) (s := s) hab)).compLpL 2 (timeMeasure T) FH := by
  classical
  have hpoint := exists_heat_vector_trace_lift_of_l2_coefficients
    hab hT hc u₀L FL A2h hA2h C2h hC2h A1h hA1h f0h
    A2l hA2l C2l hC2l A1l hA1l f0l hA2 hA1 hf0 hfLeq hC2h_lt hC2l_lt u₀H hu₀
  obtain ⟨δh, hδh, _, hwindowh⟩ :=
    exists_pos_l2_slice_contraction_lt hT (hA1h.toLp A1h) C2h hC2h_lt
  obtain ⟨δl, hδl, _, hwindowl⟩ :=
    exists_pos_l2_slice_contraction_lt hT (hA1l.toLp A1l) C2l hC2l_lt
  let δ := min δh δl
  have hδ : 0 < δ := lt_min hδh hδl
  let grid (i : ℕ) : ℝ := Set.Icc.addNSMul hT.le δ i
  have hgrid0 : grid 0 = 0 := Set.Icc.addNSMul_zero hT.le
  have hmono : Monotone grid := Set.Icc.monotone_addNSMul hT.le hδ.le
  obtain ⟨n, hn⟩ := Set.Icc.addNSMul_eq_right hT.le hδ
  have hgridN : grid (n + 1) = T := hn _ (Nat.le_succ n)
  let c (i : Fin (n + 1)) := grid i.val
  let d (i : Fin (n + 1)) := grid (i.val + 1)
  have hc0 (i : Fin (n + 1)) : 0 ≤ c i := (Set.Icc.addNSMul hT.le δ i.val).property.1
  have hdT (i : Fin (n + 1)) : d i ≤ T :=
    (Set.Icc.addNSMul hT.le δ (i.val + 1)).property.2
  have hcd (i : Fin (n + 1)) : c i ≤ d i := hmono (Nat.le_succ i.val)
  have hlength (i : Fin (n + 1)) : d i - c i ≤ δ := by
    have h := Set.Icc.abs_sub_addNSMul_le hT.le hδ.le
      (t := Set.Icc.addNSMul hT.le δ (i.val + 1)) i.val
      ⟨hmono (Nat.le_succ i.val), le_rfl⟩
    exact (le_abs_self (d i - c i)).trans h
  let J : HsPi b →L[ℝ] HsPi a :=
    ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
      (g := g) (r := r) (s := s) hab)
  have hJ : Function.Injective J := by
    intro x y hxy
    apply PiLp.ext
    intro i
    apply tensorHsInclusion_injective hab
    exact congrArg (fun v => v i) hxy
  have hlocal (i : Fin (n + 1)) : ∃ v : timeL2 (HsPi b) (d i - c i),
      J.compLpL 2 (timeMeasure (d i - c i)) v =
        timeL2.slice FL (c i) (d i) (hc0 i) (hdT i) := by
    by_cases hpos : c i < d i
    · obtain ⟨vH, hvH⟩ := hpoint (c i) ⟨hc0 i, (hcd i).trans (hdT i)⟩
      have hsmallh := hwindowh (c i) (d i) (hc0 i) (hdT i)
        (sub_nonneg.mpr (hcd i)) ((hlength i).trans (min_le_left _ _))
      have hsmalll := hwindowl (c i) (d i) (hc0 i) (hdT i)
        (sub_nonneg.mpr (hcd i)) ((hlength i).trans (min_le_right _ _))
      obtain ⟨FH, _, hFH, _⟩ := exists_heat_vector_trace_lift_on_Icc
        hab hT hc u₀L FL A2h hA2h C2h hC2h A1h hA1h f0h
        A2l hA2l C2l hC2l A1l hA1l f0l hA2 hA1 hf0 hfLeq
        (hc0 i) hpos (hdT i) vH hvH.symm hsmallh hsmalll
      exact ⟨FH, hFH.symm⟩
    · have heq : d i = c i := le_antisymm (le_of_not_gt hpos) (hcd i)
      refine ⟨0, ?_⟩
      rw [map_zero]
      apply Lp.ext
      simp [timeMeasure, heq, Filter.EventuallyEq]
  choose v hv using hlocal
  have hcover : ∀ᵐ t ∂timeMeasure T,
      t ∈ ⋃ i : Fin (n + 1), Icc (c i) (d i) := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc] with t ht
    have ht' : t ∈ Icc (grid 0) (grid (n + 1)) := by
      simpa only [hgrid0, hgridN] using ht
    obtain ⟨i, hi, hti⟩ :=
      (Set.mem_Icc_iff_exists_mem_Icc_adjacent hmono (Nat.succ_pos n)).mp ht'
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, hti⟩
  obtain ⟨FH, hFH, _⟩ := timeL2.exists_lift_of_finite_slices
    J hJ FL c d hc0 hdT hcover v hv
  exact ⟨FH, hFH.symm⟩

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear

end
