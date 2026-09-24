import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Solution.HeatEvolutionFinite
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.H1.Approximation.Slice

import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Solution.HeatEvolutionInclusion
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.CrossScaleParabolicTraceContinuity
import Mathlib.MeasureTheory.Measure.OpenPos

noncomputable section

open MeasureTheory Set Filter
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear

open TensorHeatEquation TensorSpectral TimeSobolev MaximalRegularity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
variable {g : SmoothRiemannianMetric I M} {r s : ℕ} {a T : ℝ}

theorem strongPair_eq_heatDuhamelEvolution (hT : 0 < T)
    (hc : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (u₀ : TensorHs g r s (a + 1)) (F : timeL2 (TensorHs g r s a) T)
    (u : timeH1 (TensorHs g r s a) T)
    (field : timeL2 (TensorHs g r s (a + 2)) T)
    (htrace : timeH1.trace0 _ T u =
      tensorHsInclusion (g := g) (r := r) (s := s) (show a ≤ a + 1 by linarith) u₀)
    (hlink : timeL2Inclusion (g := g) (r := r) (s := s)
      (show a ≤ a + 2 by linarith) field = timeH1.toTimeL2 _ T u)
    (heq : timeH1.timeDeriv _ T u = timeScaleLaplacian a field + F) :
    field = heatDuhamelEvolutionField a hT u₀ F ∧
      u = heatDuhamelEvolution a hT u₀ F := by
  let ud := heatDuhamelEvolution a hT u₀ F
  let fd := heatDuhamelEvolutionField a hT u₀ F
  have hzeroTrace : timeH1.trace0 _ T (u - ud) = 0 := by
    rw [map_sub, htrace, heatDuhamelEvolution_trace0, sub_self]
  have hzeroLink : timeL2Inclusion (g := g) (r := r) (s := s)
      (show a ≤ a + 2 by linarith) (field - fd) =
        timeH1.toTimeL2 _ T (u - ud) := by
    rw [map_sub, map_sub, hlink, heatDuhamelEvolutionField_toTimeL2 hT hc]
  have hzeroEq : timeH1.timeDeriv _ T (u - ud) =
      timeScaleLaplacian a (field - fd) := by
    rw [map_sub, map_sub, heq, heatDuhamelEvolution_timeDeriv hT hc]
    abel
  obtain ⟨hu, hf⟩ := strongPair_zero hT (u - ud) (field - fd)
    hzeroTrace hzeroLink hzeroEq
  exact ⟨sub_eq_zero.mp hf, sub_eq_zero.mp hu⟩

variable {ι : Type*} [Fintype ι]

theorem strongPair_eq_heatDuhamelVectorEvolution (hT : 0 < T)
    (hc : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (u₀ : PiLp 2 (fun _ : ι => TensorHs g r s (a + 1)))
    (F : timeL2 (PiLp 2 (fun _ : ι => TensorHs g r s a)) T)
    (u : timeH1 (PiLp 2 (fun _ : ι => TensorHs g r s a)) T)
    (field : timeL2 (PiLp 2 (fun _ : ι => TensorHs g r s (a + 2))) T)
    (htrace : timeH1.trace0 _ T u =
      ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
        (g := g) (r := r) (s := s) (show a ≤ a + 1 by linarith)) u₀)
    (hlink : (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
        (g := g) (r := r) (s := s) (show a ≤ a + 2 by linarith))).compLpL
          2 (timeMeasure T) field = u.toFunL2)
    (heq : timeH1.timeDeriv _ T u =
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorScaleLaplacian
        (g := g) (r := r) (s := s) a)).compLpL 2 (timeMeasure T) field + F) :
    field = heatDuhamelVectorField hT u₀ F ∧
      u = heatDuhamelVectorEvolution hT u₀ F := by
  have hparts (i : ι) :
      Lp.piLpEquiv (𝕜 := ℝ) (timeMeasure T) field i =
        heatDuhamelEvolutionField a hT (u₀ i)
          (Lp.piLpEquiv (𝕜 := ℝ) (timeMeasure T) F i) ∧
      timeH1.piLpEquiv u i = heatDuhamelEvolution a hT (u₀ i)
        (Lp.piLpEquiv (𝕜 := ℝ) (timeMeasure T) F i) := by
    apply strongPair_eq_heatDuhamelEvolution hT hc
    · exact congrArg (fun x => x i) htrace
    · have h := congrArg (fun x => Lp.piLpEquiv (𝕜 := ℝ) (timeMeasure T) x i) hlink
      rw [Lp.piLpEquiv_compLpL] at h
      simpa only [ContinuousLinearMap.piLpMap_apply, timeH1.toTimeL2_apply,
        timeH1.piLpEquiv_toFunL2, timeL2Inclusion] using h
    · have h := congrArg (fun x => Lp.piLpEquiv (𝕜 := ℝ) (timeMeasure T) x i) heq
      rw [map_add, Lp.piLpEquiv_compLpL] at h
      exact h
  constructor
  · apply (Lp.piLpEquiv (𝕜 := ℝ) (timeMeasure T)).injective
    change _ = (Lp.piLpEquiv (𝕜 := ℝ) (timeMeasure T))
      ((Lp.piLpEquiv (𝕜 := ℝ) (timeMeasure T)).symm _)
    rw [LinearIsometryEquiv.apply_symm_apply]
    exact PiLp.ext fun i => (hparts i).1
  · apply timeH1.piLpEquiv.injective
    change _ = timeH1.piLpEquiv (timeH1.piLpEquiv.symm _)
    rw [LinearIsometryEquiv.apply_symm_apply]
    exact PiLp.ext fun i => (hparts i).2

def heatDuhamelVectorTrace (hT : 0 < T)
    (hc : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (u₀ : PiLp 2 (fun _ : ι => TensorHs g r s (a + 1)))
    (F : timeL2 (PiLp 2 (fun _ : ι => TensorHs g r s a)) T)
    (t : ℝ) : PiLp 2 (fun _ : ι => TensorHs g r s (a + 1)) :=
  WithLp.toLp 2 (fun i =>
    (strongCross (heatDuhamelEvolutionField a hT (u₀ i)
      (Lp.piLpEquiv (𝕜 := ℝ) (timeMeasure T) F i))
      (heatDuhamelEvolution a hT (u₀ i)
        (Lp.piLpEquiv (𝕜 := ℝ) (timeMeasure T) F i))
      (heatDuhamelEvolutionField_toTimeL2 hT hc (u₀ i)
        (Lp.piLpEquiv (𝕜 := ℝ) (timeMeasure T) F i))).repr t)

theorem heatDuhamelVectorTrace_inclusion (hT : 0 < T)
    (hc : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (u₀ : PiLp 2 (fun _ : ι => TensorHs g r s (a + 1)))
    (F : timeL2 (PiLp 2 (fun _ : ι => TensorHs g r s a)) T)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
      (g := g) (r := r) (s := s) (show a ≤ a + 1 by linarith))
      (heatDuhamelVectorTrace hT hc u₀ F t) = (heatDuhamelVectorEvolution hT u₀ F).toFun t := by
  rw [heatDuhamelVectorEvolution, timeH1.piLpEquiv_symm_toFun _ ht]
  apply PiLp.ext
  intro i
  apply TensorHs.ext
  funext j
  change (tensorHsInclusion (g := g) (r := r) (s := s) (show a ≤ a + 1 by linarith)
    ((strongCross _ _ _).repr t)).coeff j = _
  rw [tensorHsInclusion_coeff_apply, CrossScaleField.repr_coeff _ hT ht]
  rfl

theorem heatDuhamelVectorEvolution_slice (hT : 0 < T)
    (hc : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (u₀ : PiLp 2 (fun _ : ι => TensorHs g r s (a + 1)))
    (F : timeL2 (PiLp 2 (fun _ : ι => TensorHs g r s a)) T)
    {c d : ℝ} (hc0 : 0 ≤ c) (hcd : c < d) (hdT : d ≤ T) :
    timeL2.slice (heatDuhamelVectorField hT u₀ F) c d hc0 hdT =
        heatDuhamelVectorField (sub_pos.mpr hcd) (heatDuhamelVectorTrace hT hc u₀ F c)
          (timeL2.slice F c d hc0 hdT) ∧
      timeH1.slice (heatDuhamelVectorEvolution hT u₀ F) c d hc0 hdT =
        heatDuhamelVectorEvolution (sub_pos.mpr hcd) (heatDuhamelVectorTrace hT hc u₀ F c)
          (timeL2.slice F c d hc0 hdT) := by
  apply strongPair_eq_heatDuhamelVectorEvolution (sub_pos.mpr hcd) hc
  · change (heatDuhamelVectorEvolution hT u₀ F).toFun c = _
    exact (heatDuhamelVectorTrace_inclusion hT hc u₀ F ⟨hc0, hcd.le.trans hdT⟩).symm
  · rw [timeH1.slice_toFunL2, ← timeL2.slice_compLpL,
      heatDuhamelVectorField_toFunL2 hT hc]
  · change timeL2.slice (heatDuhamelVectorEvolution hT u₀ F).deriv c d hc0 hdT = _
    rw [show (heatDuhamelVectorEvolution hT u₀ F).deriv =
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorScaleLaplacian
        (g := g) (r := r) (s := s) a)).compLpL 2 (timeMeasure T)
          (heatDuhamelVectorField hT u₀ F) + F from
        heatDuhamelVectorEvolution_timeDeriv hT hc u₀ F,
      timeL2.slice_add, timeL2.slice_compLpL]

theorem heatDuhamelVectorEvolution_toFun_add (hT : 0 < T)
    (hc : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (u₀ : PiLp 2 (fun _ : ι => TensorHs g r s (a + 1)))
    (F : timeL2 (PiLp 2 (fun _ : ι => TensorHs g r s a)) T)
    {c d t : ℝ} (hc0 : 0 ≤ c) (hcd : c < d) (hdT : d ≤ T)
    (ht : t ∈ Icc (0 : ℝ) (d - c)) :
    (heatDuhamelVectorEvolution hT u₀ F).toFun (c + t) =
      (heatDuhamelVectorEvolution (sub_pos.mpr hcd) (heatDuhamelVectorTrace hT hc u₀ F c)
        (timeL2.slice F c d hc0 hdT)).toFun t := by
  rw [← (heatDuhamelVectorEvolution_slice hT hc u₀ F hc0 hcd hdT).2]
  exact (timeH1.slice_toFun _ c d hc0 hdT ht).symm

theorem heatDuhamelVectorTrace_continuousOn (hT : 0 < T)
    (hc : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (u₀ : PiLp 2 (fun _ : ι => TensorHs g r s (a + 1)))
    (F : timeL2 (PiLp 2 (fun _ : ι => TensorHs g r s a)) T) :
    ContinuousOn (heatDuhamelVectorTrace hT hc u₀ F) (Icc (0 : ℝ) T) :=
  (PiLp.continuous_toLp 2 _).comp_continuousOn
    (continuousOn_pi.mpr fun i =>
      (strongCross (heatDuhamelEvolutionField a hT (u₀ i)
        (Lp.piLpEquiv (𝕜 := ℝ) (timeMeasure T) F i))
        (heatDuhamelEvolution a hT (u₀ i)
          (Lp.piLpEquiv (𝕜 := ℝ) (timeMeasure T) F i))
        (heatDuhamelEvolutionField_toTimeL2 hT hc (u₀ i)
          (Lp.piLpEquiv (𝕜 := ℝ) (timeMeasure T) F i))).continuousOn_repr)

theorem heatDuhamelVectorTrace_initial (hT : 0 < T)
    (hc : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (u₀ : PiLp 2 (fun _ : ι => TensorHs g r s (a + 1)))
    (F : timeL2 (PiLp 2 (fun _ : ι => TensorHs g r s a)) T) :
    heatDuhamelVectorTrace hT hc u₀ F 0 = u₀ := by
  have htrace := heatDuhamelVectorTrace_inclusion hT hc u₀ F ⟨le_rfl, hT.le⟩
  have hinitial : (heatDuhamelVectorEvolution hT u₀ F).toFun 0 =
      ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
        (g := g) (r := r) (s := s) (show a ≤ a + 1 by linarith)) u₀ := by
    rw [timeH1.toFun_zero]
    exact heatDuhamelVectorEvolution_trace0 hT u₀ F
  apply PiLp.ext
  intro i
  apply tensorHsInclusion_injective (show a ≤ a + 1 by linarith)
  exact congrArg (fun v => v i) (htrace.trans hinitial)

theorem heatDuhamelVectorTrace_toFun_add (hT : 0 < T)
    (hc : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (u₀ : PiLp 2 (fun _ : ι => TensorHs g r s (a + 1)))
    (F : timeL2 (PiLp 2 (fun _ : ι => TensorHs g r s a)) T)
    {c d t : ℝ} (hc0 : 0 ≤ c) (hcd : c < d) (hdT : d ≤ T)
    (ht : t ∈ Icc (0 : ℝ) (d - c)) :
    heatDuhamelVectorTrace hT hc u₀ F (c + t) =
      heatDuhamelVectorTrace (sub_pos.mpr hcd) hc (heatDuhamelVectorTrace hT hc u₀ F c)
        (timeL2.slice F c d hc0 hdT) t := by
  have hct : c + t ∈ Icc (0 : ℝ) T := by
    constructor <;> linarith [ht.1, ht.2]
  have hold := heatDuhamelVectorTrace_inclusion hT hc u₀ F hct
  have hnew := heatDuhamelVectorTrace_inclusion (sub_pos.mpr hcd) hc
    (heatDuhamelVectorTrace hT hc u₀ F c) (timeL2.slice F c d hc0 hdT) ht
  have hfun := heatDuhamelVectorEvolution_toFun_add hT hc u₀ F hc0 hcd hdT ht
  apply PiLp.ext
  intro i
  apply tensorHsInclusion_injective (show a ≤ a + 1 by linarith)
  exact congrArg (fun v => v i) (hold.trans (hfun.trans hnew.symm))


variable {b : ℝ}

theorem heatDuhamelVectorEvolution_toFun_tensorHsInclusion
    (hab : a ≤ b) (hT : 0 < T)
    (hc : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (u₀ : PiLp 2 (fun _ : ι => TensorHs g r s (b + 1)))
    (F : timeL2 (PiLp 2 (fun _ : ι => TensorHs g r s b)) T)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
      (g := g) (r := r) (s := s) hab)
      ((heatDuhamelVectorEvolution hT u₀ F).toFun t) =
      (heatDuhamelVectorEvolution hT
        (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
          (g := g) (r := r) (s := s) (show a + 1 ≤ b + 1 by linarith)) u₀)
        ((ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
          (g := g) (r := r) (s := s) hab)).compLpL 2 (timeMeasure T) F)).toFun t := by
  let J₀ := ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
    (g := g) (r := r) (s := s) hab)
  let J₁ := ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
    (g := g) (r := r) (s := s) (show a + 1 ≤ b + 1 by linarith))
  let J₂ := ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
    (g := g) (r := r) (s := s) (show a + 2 ≤ b + 2 by linarith))
  let Ka := ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
    (g := g) (r := r) (s := s) (show a ≤ a + 2 by linarith))
  let Kb := ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
    (g := g) (r := r) (s := s) (show b ≤ b + 2 by linarith))
  let FH := F
  let FL := J₀.compLpL 2 (timeMeasure T) FH
  let UH := heatDuhamelVectorField hT u₀ FH
  let UL := heatDuhamelVectorField hT (J₁ u₀) FL
  let uH := heatDuhamelVectorEvolution hT u₀ FH
  let uL := heatDuhamelVectorEvolution hT (J₁ u₀) FL
  have hfield : J₂.compLpL 2 (timeMeasure T) UH = UL :=
    heatDuhamelVectorField_compLpL_tensorHsInclusion hab hT hc u₀ F
  have hhigh : Kb.compLpL 2 (timeMeasure T) UH = uH.toFunL2 :=
    heatDuhamelVectorField_toFunL2 hT hc u₀ FH
  have hlow : Ka.compLpL 2 (timeMeasure T) UL = uL.toFunL2 :=
    heatDuhamelVectorField_toFunL2 hT hc (J₁ u₀) FL
  have hfieldAe : UL =ᵐ[timeMeasure T] fun q => J₂ (UH q) := by
    rw [← hfield]
    exact J₂.coeFn_compLpL (p := 2) (μ := timeMeasure T) UH
  have hhighAe : uH.toFun =ᵐ[timeMeasure T] fun q => Kb (UH q) := by
    have hrep : uH.toFunL2 =ᵐ[timeMeasure T] uH.toFun :=
      coeFn_ofContinuousOn uH.continuousOn_toFun
    rw [← hhigh] at hrep
    exact hrep.symm.trans (Kb.coeFn_compLpL (p := 2) (μ := timeMeasure T) UH)
  have hlowAe : uL.toFun =ᵐ[timeMeasure T] fun q => Ka (UL q) := by
    have hrep : uL.toFunL2 =ᵐ[timeMeasure T] uL.toFun :=
      coeFn_ofContinuousOn uL.continuousOn_toFun
    rw [← hlow] at hrep
    exact hrep.symm.trans (Ka.coeFn_compLpL (p := 2) (μ := timeMeasure T) UL)
  have hae : (fun q => J₀ (uH.toFun q)) =ᵐ[timeMeasure T] uL.toFun := by
    filter_upwards [hfieldAe, hhighAe, hlowAe] with q hf hh hl
    rw [hh, hl, hf]
    apply PiLp.ext
    intro i
    apply TensorHs.ext
    rfl
  exact Measure.eqOn_Icc_of_ae_eq (μ := (volume : Measure ℝ)) (ne_of_lt hT) hae
    (J₀.continuous.comp_continuousOn uH.continuousOn_toFun) uL.continuousOn_toFun ht

theorem heatDuhamelVectorTrace_tensorHsInclusion
    (hab : a ≤ b) (hT : 0 < T)
    (hc : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (u₀ : PiLp 2 (fun _ : ι => TensorHs g r s (b + 1)))
    (F : timeL2 (PiLp 2 (fun _ : ι => TensorHs g r s b)) T)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
      (g := g) (r := r) (s := s) (show a + 1 ≤ b + 1 by linarith))
      (heatDuhamelVectorTrace hT hc u₀ F t) =
      heatDuhamelVectorTrace hT hc
        (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
          (g := g) (r := r) (s := s) (show a + 1 ≤ b + 1 by linarith)) u₀)
        ((ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
          (g := g) (r := r) (s := s) hab)).compLpL 2 (timeMeasure T) F) t := by
  let J₀ := ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
    (g := g) (r := r) (s := s) hab)
  let J₁ := ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
    (g := g) (r := r) (s := s) (show a + 1 ≤ b + 1 by linarith))
  let FL := J₀.compLpL 2 (timeMeasure T) F
  have hh := heatDuhamelVectorTrace_inclusion hT hc u₀ F ht
  have hl := heatDuhamelVectorTrace_inclusion hT hc (J₁ u₀) FL ht
  have hf := heatDuhamelVectorEvolution_toFun_tensorHsInclusion hab hT hc u₀ F ht
  have heq := (congrArg J₀ hh).trans (hf.trans hl.symm)
  apply PiLp.ext
  intro i
  apply tensorHsInclusion_injective (g := g) (r := r) (s := s)
    (show a ≤ a + 1 by linarith)
  apply TensorHs.ext
  funext j
  exact congrArg (fun v => (v i).coeff j) heq


end DifferentialGeometry.Analysis.Parabolic.QuasiLinear

end
