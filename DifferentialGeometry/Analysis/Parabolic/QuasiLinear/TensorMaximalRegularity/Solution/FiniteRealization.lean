import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Solution.Inclusion
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.AddCircleFiniteRegularity
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Solution.ContinuousRepresentative

noncomputable section
open MeasureTheory Set Filter
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open TensorHeatEquation TensorSpectral TimeSobolev
open DifferentialGeometry.Analysis.Spectral
variable {ι : Type*} [Fintype ι]
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

theorem contDiff_and_continuousOn_iteratedDeriv_duhamel_realization
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {n : ℕ} (hn : 1 ≤ n) {T : ℝ} (hT : 0 < T)
    (f₀ : PiLp 2 (fun _ : ι => TensorHs g 0 0 ((n : ℝ) + 1)))
    (F : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (n : ℝ))) T) :
    let J := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g) (r := 0) (s := 0) (by exact_mod_cast hn))
    let P := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : (1 : ℝ) ≤ (n : ℝ) + 1))
    let u := maximalRegularityDuhamelVectorMap hT
      (0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℝ) + 2)))
      (J.compLpL 2 (timeMeasure T) F)
    let f := fun t (x : ℝ) => scalarH1PiToContinuous g (P f₀ + u.toFun t)
      (x : AddCircle (1 : ℝ))
    (∀ t ∈ Icc 0 T, ContDiff ℝ n (f t)) ∧
      ContinuousOn (fun p : ℝ × ℝ => iteratedDeriv n (f p.1) p.2)
        (Icc 0 T ×ˢ univ) := by
  intro J P u f
  have hc := tensorResolventL2_isCompactOperator
    (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ)) g 0 0
  obtain ⟨w, hw, hwlo, _⟩ := maximalRegularityDuhamelVectorMap_exists_continuousOn_representative
    hT hc (0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 ((n : ℝ) + 2))) F
  have hlow (t : ℝ) (ht : t ∈ Icc 0 T) : P (w t) = u.toFun t := by
    have h := maximalRegularityDuhamelVectorMap_toFun_tensorHsInclusion
      (show (1 : ℝ) ≤ (n : ℝ) by exact_mod_cast hn) hT hc
      (0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 ((n : ℝ) + 2))) F ht
    rw [map_zero] at h
    have hcomp : P (w t) = J
        (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
          tensorHsInclusion (g := g) (r := 0) (s := 0)
            (show (n : ℝ) ≤ (n : ℝ) + 1 by linarith)) (w t)) := by
      apply PiLp.ext
      intro i
      exact tensorHsInclusion_trans_apply (by exact_mod_cast hn) (by linarith) (w t i)
    rw [hcomp, hwlo t ht]
    exact h
  have hf (t : ℝ) (ht : t ∈ Icc 0 T) : f t = fun x : ℝ =>
      scalarH1PiToContinuous g (P (f₀ + w t)) (x : AddCircle (1 : ℝ)) := by
    funext x
    simp only [f, map_add, hlow t ht]
  constructor
  · intro t ht
    rw [hf t ht]
    exact AddCircle.contDiff_scalarH1PiToContinuous g n (f₀ + w t)
  · have hW : ContinuousOn (fun p : ℝ × ℝ => (f₀ + w p.1, p.2))
        (Icc 0 T ×ˢ univ) :=
      (continuousOn_const.add (hw.comp continuousOn_fst (fun _ h => h.1))).prodMk continuousOn_snd
    have h := (AddCircle.continuous_iteratedDeriv_scalarH1PiToContinuous g n).comp_continuousOn hW
    apply h.congr
    intro p hp
    dsimp only [Function.comp_apply]
    rw [hf p.1 hp.1]

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear
