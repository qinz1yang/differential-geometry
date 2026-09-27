import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.H1.Classical
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Duhamel.FiniteProduct
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Embedding.ScalarContinuousInjective

open MeasureTheory Filter Set
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear

open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

theorem exists_strongPair_of_classical_scalar_equation
    {M : Type*} [TopologicalSpace M] [ChartedSpace ℝ M]
    [IsManifold 𝓘(ℝ, ℝ) ∞ M] [CompactSpace M] [T2Space M]
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) M)
    {T : ℝ} (hT : 0 < T)
    (W : ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℝ) + 2)))
    (V : ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 (1 : ℝ)))
    (hW : ContinuousOn W (Icc 0 T)) (hV : ContinuousOn V (Icc 0 T))
    (heq : ∀ z : M, ∀ t ∈ Icc 0 T,
      HasDerivWithinAt
        (fun s => scalarH1PiToContinuous g
          (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
            (g := g) (r := 0) (s := 0) (by norm_num : (1 : ℝ) ≤ 1 + 2)) (W s)) z)
        (scalarH1PiToContinuous g (V t) z) (Icc 0 T) t) :
    let P := ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
      (g := g) (r := 0) (s := 0) (by norm_num : (1 : ℝ) ≤ 1 + 2))
    let L := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorScaleLaplacian (g := g) (r := 0) (s := 0) (1 : ℝ))
    ∃ (u : timeH1 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (1 : ℝ))) T)
      (field : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℝ) + 2))) T)
      (force : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (1 : ℝ))) T),
      timeH1.trace0 _ T u = P (W 0) ∧
        EqOn u.toFun (fun t => P (W t)) (Icc 0 T) ∧
        field =ᵐ[timeMeasure T] W ∧
        force =ᵐ[timeMeasure T] (fun t => V t - L (W t)) ∧
        P.compLpL 2 (timeMeasure T) field = u.toFunL2 ∧
        timeH1.timeDeriv _ T u = L.compLpL 2 (timeMeasure T) field + force := by
  intro P L
  let J (z : M) := (ContinuousMap.evalCLM ℝ z).comp
    (scalarH1PiToContinuous (ι := ι) g)
  have hJ : Function.Injective
      (fun x : PiLp 2 (fun _ : ι => TensorHs g 0 0 (1 : ℝ)) => fun z => J z x) := by
    intro x y hxy
    apply scalarH1PiToContinuous_injective g
    apply ContinuousMap.ext
    exact fun z => congrFun hxy z
  exact exists_timeH1_lift_of_hasDerivWithinAt_separating
    P L J hJ hT W V hW hV heq

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear
