import DifferentialGeometry.Geometry.Comparison.Volume.BishopGromov
import DifferentialGeometry.Geometry.Comparison.Volume.LocalDoubling

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  [T2Space (TangentBundle I M)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
  [ConnectedSpace M] [CompleteSpace M]

theorem ballVolume_mul_scale_le_model_ratio
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (p : M) {q r s R : ℝ} (hq : 0 ≤ q) (hr : 0 < r)
    (hs : 0 < s) (hsR : s ≤ R)
    (hRic : ricciBoundedBelowOn (I := I) g
      {y : M | riemannianEDist I p y < ENNReal.ofReal (R * r)}
      (((Module.finrank ℝ E - 1 : ℕ) : ℝ) * (-((q / r) ^ 2)))) :
    ballVolume g p (R * r) ≤
      ENNReal.ofReal (modelVolume (-(q ^ 2)) (Module.finrank ℝ E) R /
        modelVolume (-(q ^ 2)) (Module.finrank ℝ E) s) * ballVolume g p (s * r) := by
  let n := Module.finrank ℝ E
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
  have hR : 0 < R := hs.trans_le hsR
  let R₀ : Set.Ioi (0 : ℝ≥0∞) := ⟨ENNReal.ofReal (R * r), ENNReal.ofReal_pos.mpr (mul_pos hR hr)⟩
  have hc := localBishopGromov_cross g hEnorm p (-((q / r) ^ 2)) R₀ hRic
    (mul_pos hs hr) (mul_le_mul_of_nonneg_right hsR hr.le)
    (by rw [bishopGromovRadius_of_nonpos (neg_nonpos.mpr (sq_nonneg _))])
  have hpos : 0 < modelVolume (-((q / r) ^ 2)) n (s * r) :=
    modelVolume_pos hn (mul_pos hs hr)
      ⟨(mul_pos hs hr).le, fun h => (not_lt_of_ge (neg_nonpos.mpr (sq_nonneg _)) h).elim⟩
  have hd := (ENNReal.le_div_iff_mul_le
    (Or.inl (ENNReal.ofReal_pos.mpr hpos).ne') (Or.inl ENNReal.ofReal_ne_top)).mpr hc
  rw [ENNReal.mul_div_right_comm, ← ENNReal.ofReal_div_of_pos hpos] at hd
  have heq : modelVolume (-((q / r) ^ 2)) n (R * r) /
      modelVolume (-((q / r) ^ 2)) n (s * r) =
      modelVolume (-(q ^ 2)) n R / modelVolume (-(q ^ 2)) n s := by
    rw [modelVolume_doubling_scale q r R n hq hr hn,
      modelVolume_doubling_scale q r s n hq hr hn]
    exact mul_div_mul_left _ _ (pow_ne_zero n hr.ne')
  rw [heq] at hd
  exact hd

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
