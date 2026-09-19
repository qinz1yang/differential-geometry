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

section

open DifferentialGeometry.Analysis.Parabolic.QuasiLinear

private theorem exists_tendsto_timeL2_parabolic_forcing_lift
    {P ι : Type*} [Fintype ι] {l : Filter P}
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {n m : ℕ} (hn : 1 ≤ n) (hnm : n ≤ m) {T : ℝ} (hT : 0 < T) (p₀ : P)
    (f : P → PiLp 2 (fun _ : ι => TensorHs g 0 0 ((m : ℝ) + 2)))
    (V : P → timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((m : ℝ) + 2))) T)
    (F : P → timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (n : ℝ))) T)
    (a : P → Lp (TensorHs g 0 0 (m : ℝ)) ∞ (timeMeasure T))
    (b : P → timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (m : ℝ))) T)
    (hf : Tendsto f l (𝓝 (f p₀))) (hVlim : Tendsto V l (𝓝 (V p₀)))
    (ha : Tendsto a l (𝓝 (a p₀))) (hb : Tendsto b l (𝓝 (b p₀))) :
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (show (n : ℝ) ≤ (m : ℝ) by exact_mod_cast hnm)
    let K := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (show (n : ℝ) + 2 ≤ (m : ℝ) + 2 by exact_mod_cast Nat.add_le_add_right hnm 2)
    (∀ p, (ContinuousLinearMap.piLpMap 2 (fun _ : ι => K)).compLpL
      2 (timeMeasure T) (V p) = maximalRegularityDuhamelVectorField hT 0 (F p)) →
    (∀ p, ∀ᵐ t ∂timeMeasure T, ∀ i,
      tensorScaleLaplacian (g := g) (r := 0) (s := 0) (n : ℝ) (K (V p t i)) +
        F p t i = scalarHsMul g n (by simpa using hn) (J (a p t))
          (parameterSecondDerivativeHs g n (K (f p i + V p t i))) + J (b p t i)) →
    ∃ FH : P → timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (m : ℝ))) T,
      (∀ p, (ContinuousLinearMap.piLpMap 2 (fun _ : ι => J)).compLpL
        2 (timeMeasure T) (FH p) = F p) ∧
      (∀ p, V p = maximalRegularityDuhamelVectorField hT 0 (FH p)) ∧
      (∀ p, ∀ᵐ t ∂timeMeasure T, ∀ i,
        tensorScaleLaplacian (g := g) (r := 0) (s := 0) (m : ℝ) (V p t i) +
          FH p t i = scalarHsMul g m (by simpa using hn.trans hnm) (a p t)
            (parameterSecondDerivativeHs g m (f p i + V p t i)) + b p t i) ∧
      Tendsto FH l (𝓝 (FH p₀)) := by
  intro J K hV hPDE
  classical
  have hex (p : P) := exists_timeL2_parabolic_forcing_lift g hn hnm (f p) (V p)
    (F p) (fun t => a p t) (Lp.memLp (a p)).aestronglyMeasurable
    (ae_le_lpNorm_exponent_top (Lp.memLp (a p))) (b p) (hPDE p)
  choose FH hFH hhigh using hex
  have hduhamel (p : P) : V p = maximalRegularityDuhamelVectorField hT 0 (FH p) := by
    apply eq_maximalRegularityDuhamelVectorField_of_tensorHsInclusion_eq
      (show (n : ℝ) ≤ (m : ℝ) by exact_mod_cast hnm) hT
      (tensorResolventL2_isCompactOperator g 0 0) 0 (F p) (FH p) (V p) (hFH p)
    simpa only [map_zero] using hV p
  refine ⟨FH, hFH, hduhamel, hhigh, ?_⟩
  exact tendsto_timeL2_parabolic_forcing g (hn.trans hnm)
    f (f p₀) V (V p₀) a (a p₀) b FH (b p₀) (FH p₀)
    hf hVlim ha hb hhigh (hhigh p₀)

end

end AddCircle

end

noncomputable section

open Filter MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology ENNReal NNReal

namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear

open DifferentialGeometry.Analysis.Spectral
open TensorHeatEquation TensorSpectral TimeSobolev MaximalRegularity
open _root_.AddCircle

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩
attribute [local instance] _root_.AddCircle.vectorTensorHsNormedSpace

private theorem exists_tendsto_forcing_lift_of_duhamel_equation
    {X ι : Type*} [Fintype ι] {l : Filter X}
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {n m : ℕ} (hn : 1 ≤ n) (hnm : n ≤ m) {T : ℝ} (hT : 0 < T) (x₀ : X)
    (f : X → PiLp 2 (fun _ : ι => TensorHs g 0 0 ((m : ℝ) + 2)))
    (V : X → timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((m : ℝ) + 2))) T)
    (F : X → timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (n : ℝ))) T)
    (a : X → timeL2 (TensorHs g 0 0 (m : ℝ)) T)
    (aTop : X → Lp (TensorHs g 0 0 (m : ℝ)) ∞ (timeMeasure T))
    (b : X → timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (m : ℝ))) T)
    (hf : Tendsto f l (𝓝 (f x₀))) (hVlim : Tendsto V l (𝓝 (V x₀)))
    (haToplim : Tendsto aTop l (𝓝 (aTop x₀))) (hb : Tendsto b l (𝓝 (b x₀)))
    (haTop : ∀ x, aTop x =ᵐ[timeMeasure T] a x) :
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (show (n : ℝ) ≤ (m : ℝ) by exact_mod_cast hnm)
    let K := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (show (n : ℝ) + 2 ≤ (m : ℝ) + 2 by exact_mod_cast Nat.add_le_add_right hnm 2)
    let U := fun x => maximalRegularityDuhamelVectorField hT 0 (F x)
    (∀ x, (ContinuousLinearMap.piLpMap 2 (fun _ : ι => K)).compLpL
      2 (timeMeasure T) (V x) = U x) →
    (∀ x, ∀ᵐ t ∂timeMeasure T, ∀ i,
      tensorScaleLaplacian (g := g) (r := 0) (s := 0) (n : ℝ) (U x t i) + F x t i =
        scalarHsMul g n (by simpa using hn) (J (a x t))
          (parameterSecondDerivativeHs g n (K (f x i) + U x t i)) + J (b x t i)) →
    ∃ FH : X → timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (m : ℝ))) T,
      (∀ x, (ContinuousLinearMap.piLpMap 2 (fun _ : ι => J)).compLpL
        2 (timeMeasure T) (FH x) = F x) ∧
      (∀ x, V x = maximalRegularityDuhamelVectorField hT 0 (FH x)) ∧
      (∀ x, ∀ᵐ t ∂timeMeasure T, ∀ i,
        tensorScaleLaplacian (g := g) (r := 0) (s := 0) (m : ℝ) (V x t i) +
          FH x t i = scalarHsMul g m (by simpa using hn.trans hnm) (aTop x t)
            (parameterSecondDerivativeHs g m (f x i + V x t i)) + b x t i) ∧
      Tendsto FH l (𝓝 (FH x₀)) := by
  intro J K U hV hPDE
  apply exists_tendsto_timeL2_parabolic_forcing_lift g hn hnm hT x₀ f V F aTop b
    hf hVlim haToplim hb hV
  intro x
  have hVae := (ContinuousLinearMap.piLpMap 2 (fun _ : ι => K)).coeFn_compLpL
    (p := 2) (μ := timeMeasure T) (V x)
  rw [hV x] at hVae
  filter_upwards [hPDE x, haTop x, hVae] with t ht hat hvt
  intro i
  have hUi := congrArg (fun z => z i) hvt
  change U x t i = K (V x t i) at hUi
  rw [K.map_add, ← hUi, hat]
  exact ht i

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear

end
