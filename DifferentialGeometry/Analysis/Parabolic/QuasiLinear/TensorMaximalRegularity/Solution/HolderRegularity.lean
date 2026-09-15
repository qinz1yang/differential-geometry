import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Basic.Interpolation
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Solution.ContinuousRepresentative
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.H1.Compactness.Basic
import Mathlib.Topology.MetricSpace.Holder

noncomputable section

open Set MeasureTheory
open scoped ContDiff NNReal ENNReal

namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear

open TensorHeatEquation TensorSpectral TimeSobolev

variable {ι : Type*} [Fintype ι]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
variable {g : SmoothRiemannianMetric I M} {r s : ℕ} {a b T : ℝ}

theorem holderOnWith_inclusion_of_timeH1 (hab : a ≤ b)
    (u : timeH1 (PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s a)) T)
    (w : ℝ → PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s b))
    {K : Set ℝ} (hK : K ⊆ Icc 0 T)
    (hlow : ∀ t ∈ K, ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        hab) (w t) = u.toFun t)
    {R : ℝ≥0} (hhigh : ∀ t ∈ K, ‖w t‖ ≤ R)
    {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    HolderOnWith (‖u.deriv‖₊ ^ (1 - θ) * (2 * R) ^ θ)
      (⟨(1 - θ) / 2, by linarith⟩ : ℝ≥0)
      (fun t => ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
        tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
          (show (1 - θ) * a + θ * b ≤ b by nlinarith)) (w t)) K := by
  intro t ht z hz
  rw [edist_nndist, edist_nndist]
  change (nndist _ _ : ℝ≥0∞) ≤
    ((‖u.deriv‖₊ ^ (1 - θ) * (2 * R) ^ θ : ℝ≥0) : ℝ≥0∞) *
      (nndist t z : ℝ≥0∞) ^ ((1 - θ) / 2)
  rw [← ENNReal.coe_rpow_of_nonneg _ (show 0 ≤ (1 - θ) / 2 by linarith),
    ← ENNReal.coe_mul, ENNReal.coe_le_coe]
  change (nndist _ _ : ℝ) ≤ (_ : ℝ≥0)
  simp only [coe_nndist, NNReal.coe_mul, NNReal.coe_rpow,
    NNReal.coe_ofNat, coe_nnnorm, dist_eq_norm, Real.norm_eq_abs]
  rw [← map_sub]
  have hinterp :
      ‖ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
        tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
          (show (1 - θ) * a + θ * b ≤ b by nlinarith)) (w t - w z)‖ ≤
      ‖ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
        tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
          hab) (w t - w z)‖ ^ (1 - θ) *
        ‖w t - w z‖ ^ θ := by
    exact TensorHs.norm_piLpMap_inclusion_interpolation hab hθ hθ1 (w t - w z)
  rw [(ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
    tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s) hab)).map_sub,
    hlow t ht, hlow z hz] at hinterp
  have hlo := u.toFun_sub_le (hK hz) (hK ht)
  have hhi : ‖w t - w z‖ ≤ 2 * (R : ℝ) :=
    (norm_sub_le _ _).trans (by linarith [hhigh t ht, hhigh z hz])
  calc
    _ ≤ ‖u.toFun t - u.toFun z‖ ^ (1 - θ) * ‖w t - w z‖ ^ θ := hinterp
    _ ≤ (Real.sqrt |t - z| * ‖u.deriv‖) ^ (1 - θ) * (2 * (R : ℝ)) ^ θ := by
      gcongr
    _ = _ := by
      rw [Real.mul_rpow (Real.sqrt_nonneg _) (norm_nonneg _), Real.sqrt_eq_rpow,
        ← Real.rpow_mul (abs_nonneg _)]
      rw [show (1 / 2 : ℝ) * (1 - θ) = (1 - θ) / 2 by ring]
      ring

theorem exists_holderOnWith_intermediate_representative (hT : 0 < T)
    (u : timeH1 (PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s a)) T)
    (v : timeL2 (PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 2))) T)
    (hlink : ∀ᵐ t ∂timeMeasure T, ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        (show a ≤ a + 2 by linarith)) (v t) = u.toFun t) :
    ∃ w : ℝ → PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 1)),
      ContinuousOn w (Icc 0 T) ∧
      (∀ t ∈ Icc 0 T, ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
        tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
          (show a ≤ a + 1 by linarith)) (w t) = u.toFun t) ∧
      w =ᵐ[timeMeasure T] (fun t => ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
        tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
          (show a + 1 ≤ a + 2 by linarith)) (v t)) ∧
      ∃ R : ℝ≥0, ∀ θ : ℝ, 0 ≤ θ → ∀ hθ1 : θ ≤ 1,
        HolderOnWith (‖u.deriv‖₊ ^ (1 - θ) * (2 * R) ^ θ)
          (⟨(1 - θ) / 2, by linarith⟩ : ℝ≥0)
          (fun t => ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
            tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
              (show (1 - θ) * a + θ * (a + 1) ≤ a + 1 by nlinarith)) (w t))
          (Icc 0 T) := by
  obtain ⟨w, hw, hlo, hhi⟩ := exists_continuousOn_intermediate_representative hT u v hlink
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hw
  have hR : ∀ t ∈ Icc 0 T, ‖w t‖ ≤ Real.toNNReal C := by
    intro t ht
    exact (hC t ht).trans (Real.le_coe_toNNReal C)
  refine ⟨w, hw, hlo, hhi, Real.toNNReal C, ?_⟩
  intro θ hθ hθ1
  exact holderOnWith_inclusion_of_timeH1 (show a ≤ a + 1 by linarith)
    u w (fun _ h => h) hlo hR hθ hθ1

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear
