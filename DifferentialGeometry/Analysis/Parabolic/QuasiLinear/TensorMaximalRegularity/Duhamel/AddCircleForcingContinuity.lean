import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Duhamel.AddCircleForcing
import DifferentialGeometry.Analysis.FunctionalAnalysis.PiLpOperators
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

noncomputable section

open Filter MeasureTheory Set
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace AddCircle

open DifferentialGeometry
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private local instance vectorTensorHsNormedSpace {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (s : ℝ) :
    NormedSpace ℝ (PiLp 2 (fun _ : ι => TensorHs g 0 0 s)) := inferInstance

theorem tendsto_timeL2_parabolic_forcing
    {P ι : Type*} [Fintype ι] {l : Filter P}
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {m : ℕ} (hm : 1 ≤ m) {T : ℝ}
    (f : P → PiLp 2 (fun _ : ι => TensorHs g 0 0 ((m : ℝ) + 2)))
    (f₀ : PiLp 2 (fun _ : ι => TensorHs g 0 0 ((m : ℝ) + 2)))
    (V : P → timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((m : ℝ) + 2))) T)
    (V₀ : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((m : ℝ) + 2))) T)
    (a : P → Lp (TensorHs g 0 0 (m : ℝ)) ∞ (timeMeasure T))
    (a₀ : Lp (TensorHs g 0 0 (m : ℝ)) ∞ (timeMeasure T))
    (b F : P → timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (m : ℝ))) T)
    (b₀ F₀ : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (m : ℝ))) T)
    (hf : Tendsto f l (𝓝 f₀)) (hV : Tendsto V l (𝓝 V₀))
    (ha : Tendsto a l (𝓝 a₀)) (hb : Tendsto b l (𝓝 b₀))
    (hF : ∀ p, ∀ᵐ t ∂timeMeasure T, ∀ i,
      tensorScaleLaplacian (g := g) (r := 0) (s := 0) (m : ℝ) (V p t i) + F p t i =
        scalarHsMul g m (by simpa using hm) (a p t)
          (parameterSecondDerivativeHs g m (f p i + V p t i)) + b p t i)
    (hF₀ : ∀ᵐ t ∂timeMeasure T, ∀ i,
      tensorScaleLaplacian (g := g) (r := 0) (s := 0) (m : ℝ) (V₀ t i) + F₀ t i =
        scalarHsMul g m (by simpa using hm) (a₀ t)
          (parameterSecondDerivativeHs g m (f₀ i + V₀ t i)) + b₀ t i) :
    Tendsto F l (𝓝 F₀) := by
  let H := PiLp 2 (fun _ : ι => TensorHs g 0 0 (m : ℝ))
  let H₂ := PiLp 2 (fun _ : ι => TensorHs g 0 0 ((m : ℝ) + 2))
  let M : TensorHs g 0 0 (m : ℝ) →L[ℝ] H →L[ℝ] H :=
    (ContinuousLinearMap.piLpMapL 2).comp
      (ContinuousLinearMap.pi fun _ : ι => scalarHsMul g m (by simpa using hm))
  let ML := M.holderL (timeMeasure T) ∞ 2 2
  let Q : H₂ →L[ℝ] H := ContinuousLinearMap.piLpMap 2
    (fun _ : ι => parameterSecondDerivativeHs g m)
  let L : H₂ →L[ℝ] H := ContinuousLinearMap.piLpMap 2
    (fun _ : ι => tensorScaleLaplacian (g := g) (r := 0) (s := 0) (m : ℝ))
  let C : H₂ →L[ℝ] timeL2 H₂ T := Lp.constL 2 (timeMeasure T) ℝ
  let source := fun (f' : H₂) (V' : timeL2 H₂ T)
      (a' : Lp (TensorHs g 0 0 (m : ℝ)) ∞ (timeMeasure T)) (b' : timeL2 H T) =>
    ML a' (Q.compLpL 2 (timeMeasure T) (C f' + V')) + b' -
      L.compLpL 2 (timeMeasure T) V'
  have hsource (f' : H₂) (V' : timeL2 H₂ T)
      (a' : Lp (TensorHs g 0 0 (m : ℝ)) ∞ (timeMeasure T)) (b' F' : timeL2 H T)
      (heq : ∀ᵐ t ∂timeMeasure T, ∀ i,
        tensorScaleLaplacian (g := g) (r := 0) (s := 0) (m : ℝ) (V' t i) + F' t i =
          scalarHsMul g m (by simpa using hm) (a' t)
            (parameterSecondDerivativeHs g m (f' i + V' t i)) + b' t i) :
      F' = source f' V' a' b' := by
    apply Lp.ext
    filter_upwards [heq,
      Lp.coeFn_sub
        (ML a' (Q.compLpL 2 (timeMeasure T) (C f' + V')) + b')
        (L.compLpL 2 (timeMeasure T) V'),
      Lp.coeFn_add (ML a' (Q.compLpL 2 (timeMeasure T) (C f' + V'))) b',
      M.coeFn_holder (r := 2) a' (Q.compLpL 2 (timeMeasure T) (C f' + V')),
      Q.coeFn_compLpL (C f' + V'), Lp.coeFn_add (C f') V',
      Lp.coeFn_const (p := 2) (μ := timeMeasure T) f', L.coeFn_compLpL V']
      with t ht hsub hadd hop hQ hsum hconst hL
    change F' t =
      (ML a' (Q.compLpL 2 (timeMeasure T) (C f' + V')) + b' -
        L.compLpL 2 (timeMeasure T) V') t
    change ML a' (Q.compLpL 2 (timeMeasure T) (C f' + V')) t =
      M (a' t) (Q.compLpL 2 (timeMeasure T) (C f' + V') t) at hop
    rw [hsub, Pi.sub_apply, hadd, Pi.add_apply, hop, hQ, hsum, Pi.add_apply, hL]
    change C f' t = f' at hconst
    rw [hconst]
    apply PiLp.ext
    intro i
    change F' t i = scalarHsMul g m (by simpa using hm) (a' t)
      (parameterSecondDerivativeHs g m (f' i + V' t i)) + b' t i -
        tensorScaleLaplacian (g := g) (r := 0) (s := 0) (m : ℝ) (V' t i)
    exact eq_sub_of_add_eq' (ht i)
  have hC : Tendsto (fun p => C (f p) + V p) l (𝓝 (C f₀ + V₀)) :=
    ((C.continuous.tendsto f₀).comp hf).add hV
  have hQ : Tendsto (fun p => Q.compLpL 2 (timeMeasure T) (C (f p) + V p)) l
      (𝓝 (Q.compLpL 2 (timeMeasure T) (C f₀ + V₀))) :=
    ((Q.compLpL 2 (timeMeasure T)).continuous.tendsto (C f₀ + V₀)).comp hC
  have hM : Tendsto (fun p => ML (a p)) l (𝓝 (ML a₀)) :=
    (ML.continuous.tendsto a₀).comp ha
  have hL : Tendsto (fun p => L.compLpL 2 (timeMeasure T) (V p)) l
      (𝓝 (L.compLpL 2 (timeMeasure T) V₀)) :=
    ((L.compLpL 2 (timeMeasure T)).continuous.tendsto V₀).comp hV
  have hMQ := isBoundedBilinearMap_apply.continuous.tendsto
    (ML a₀, Q.compLpL 2 (timeMeasure T) (C f₀ + V₀)) |>.comp (hM.prodMk_nhds hQ)
  have hs := (hMQ.add hb).sub hL
  change Tendsto (fun p => source (f p) (V p) (a p) (b p)) l
    (𝓝 (source f₀ V₀ a₀ b₀)) at hs
  have heq (p : P) := hsource (f p) (V p) (a p) (b p) (F p) (hF p)
  have heq₀ := hsource f₀ V₀ a₀ b₀ F₀ hF₀
  simpa only [← heq, ← heq₀] using hs

end AddCircle

end
