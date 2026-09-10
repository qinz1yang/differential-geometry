import DifferentialGeometry.Geometry.Comparison.Volume.BishopGromovLocal
import DifferentialGeometry.Geometry.Comparison.Volume.SmallRadius

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open DifferentialGeometry
open DifferentialGeometry.Geometry.Riemannian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  [T2Space (TangentBundle I M)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
variable [PseudoEMetricSpace M] [IsRiemannianManifold I M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

def bishopGromovRadius (K : ℝ) (R₀ : ℝ≥0∞) : ℝ≥0∞ :=
  if 0 < K then min R₀ (ENNReal.ofReal (Real.pi / Real.sqrt K)) else R₀

@[simp] theorem bishopGromovRadius_of_nonpos {K : ℝ} (hK : K ≤ 0)
    (R₀ : ℝ≥0∞) : bishopGromovRadius K R₀ = R₀ := by
  simp [bishopGromovRadius, not_lt.mpr hK]

@[simp] theorem bishopGromovRadius_of_pos {K : ℝ} (hK : 0 < K)
    (R₀ : ℝ≥0∞) :
    bishopGromovRadius K R₀ =
      min R₀ (ENNReal.ofReal (Real.pi / Real.sqrt K)) := by
  simp [bishopGromovRadius, hK]

theorem bishopGromovRadius_le_source (K : ℝ) (R₀ : ℝ≥0∞) :
    bishopGromovRadius K R₀ ≤ R₀ := by
  by_cases hK : 0 < K
  · simp [bishopGromovRadius, hK]
  · simp [bishopGromovRadius, hK]

theorem ofReal_le_conjugateRadius_of_le_bishopGromovRadius
    {K R : ℝ} {R₀ : ℝ≥0∞} (hK : 0 < K)
    (hR : ENNReal.ofReal R ≤ bishopGromovRadius K R₀) :
    R ≤ Real.pi / Real.sqrt K := by
  have hq : 0 < Real.pi / Real.sqrt K :=
    div_pos Real.pi_pos (Real.sqrt_pos.2 hK)
  have hof : ENNReal.ofReal R ≤
      ENNReal.ofReal (Real.pi / Real.sqrt K) := by
    exact hR.trans (by simp [bishopGromovRadius, hK])
  exact (ENNReal.ofReal_le_ofReal_iff hq.le).mp hof

theorem localBishopGromov_cross [ConnectedSpace M] [CompleteSpace M]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (K : ℝ) (R₀ : Set.Ioi (0 : ℝ≥0∞))
    (hRic : ricciBoundedBelowOn (I := I) g
      {y : M | riemannianEDist I p y < R₀.1}
      (((Module.finrank ℝ E - 1 : ℕ) : ℝ) * K))
    {s R : ℝ} (hs : 0 < s) (hsR : s ≤ R)
    (hR : ENNReal.ofReal R ≤ bishopGromovRadius K R₀.1) :
    ballVolume g p R *
        ENNReal.ofReal (modelVolume K (Module.finrank ℝ E) s) ≤
      ENNReal.ofReal (modelVolume K (Module.finrank ℝ E) R) *
        ballVolume g p s := by
  have hRsource : ENNReal.ofReal R ≤ R₀.1 :=
    hR.trans (bishopGromovRadius_le_source K R₀.1)
  have hsubset :
      {y : M | riemannianEDist I p y < ENNReal.ofReal R} ⊆
        {y : M | riemannianEDist I p y < R₀.1} := by
    intro y hy
    exact hy.trans_le hRsource
  have hRicR : ricciBoundedBelowOn (I := I) g
      {y : M | riemannianEDist I p y < ENNReal.ofReal R}
      (((Module.finrank ℝ E - 1 : ℕ) : ℝ) * K) :=
    ricciBoundedBelowOn_mono hsubset hRic
  have hconj : 0 < K → R ≤ Real.pi / Real.sqrt K := fun hK =>
    ofReal_le_conjugateRadius_of_le_bishopGromovRadius hK hR
  simpa only [ballVolume] using
    modelVolume_cross_endpoint_of_ricciBoundedBelowOn
      (I := I) g hEnorm p hs hsR hconj hRicR


theorem localBishopGromov_ratio [ConnectedSpace M] [CompleteSpace M]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (K : ℝ) (R₀ : Set.Ioi (0 : ℝ≥0∞))
    (hRic : ricciBoundedBelowOn (I := I) g
      {y : M | riemannianEDist I p y < R₀.1}
      (((Module.finrank ℝ E - 1 : ℕ) : ℝ) * K))
    {s R : ℝ} (hs : 0 < s) (hsR : s ≤ R)
    (hR : ENNReal.ofReal R ≤ bishopGromovRadius K R₀.1) :
    ballVolume g p R /
        ENNReal.ofReal (modelVolume K (Module.finrank ℝ E) R) ≤
      ballVolume g p s /
        ENNReal.ofReal (modelVolume K (Module.finrank ℝ E) s) := by
  let n : ℕ := Module.finrank ℝ E
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.2 (NeZero.ne n)
  have hRpos : 0 < R := hs.trans_le hsR
  have hRmodel : modelVolumeAdmissible K R :=
    ⟨hRpos.le, fun hK =>
      ofReal_le_conjugateRadius_of_le_bishopGromovRadius hK hR⟩
  have hsmodel : modelVolumeAdmissible K s :=
    ⟨hs.le, fun hK => hsR.trans
      (ofReal_le_conjugateRadius_of_le_bishopGromovRadius hK hR)⟩
  have hmR : 0 < ENNReal.ofReal (modelVolume K n R) :=
    ENNReal.ofReal_pos.2 (modelVolume_pos hn hRpos hRmodel)
  have hms : 0 < ENNReal.ofReal (modelVolume K n s) :=
    ENNReal.ofReal_pos.2 (modelVolume_pos hn hs hsmodel)
  have hcross := localBishopGromov_cross
    (I := I) g hEnorm p K R₀ hRic hs hsR hR
  apply (ENNReal.div_le_iff hmR.ne' ENNReal.ofReal_ne_top).2
  rw [← ENNReal.mul_div_right_comm]
  apply (ENNReal.le_div_iff_mul_le (Or.inl hms.ne')
    (Or.inl ENNReal.ofReal_ne_top)).2
  simpa only [n, mul_comm] using hcross

theorem localBishopGromov_absolute_upper [ConnectedSpace M] [CompleteSpace M]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (K : ℝ) (R₀ : Set.Ioi (0 : ℝ≥0∞))
    (hRic : ricciBoundedBelowOn (I := I) g
      {y : M | riemannianEDist I p y < R₀.1}
      (((Module.finrank ℝ E - 1 : ℕ) : ℝ) * K))
    {R : ℝ} (hRpos : 0 < R)
    (hR : ENNReal.ofReal R ≤ bishopGromovRadius K R₀.1) :
    ballVolume g p R ≤
      ENNReal.ofReal (modelVolume K (Module.finrank ℝ E) R) := by
  let n : ℕ := Module.finrank ℝ E
  let c : ℝ≥0∞ := ballVolume g p R /
    ENNReal.ofReal (modelVolume K n R)
  have hRmodel : modelVolumeAdmissible K R :=
    ⟨hRpos.le, fun hK =>
      ofReal_le_conjugateRadius_of_le_bishopGromovRadius hK hR⟩
  have hmR : 0 < ENNReal.ofReal (modelVolume K n R) := by
    exact ENNReal.ofReal_pos.2
      (modelVolume_pos (Nat.one_le_iff_ne_zero.2 (NeZero.ne n)) hRpos hRmodel)
  have hsmall : Tendsto (fun s : ℝ => ballVolume g p s /
      ENNReal.ofReal (modelVolume K n s)) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    simpa only [n] using tendsto_ballVolume_div_modelVolume
      (I := I) g hEnorm p K
  have hle : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      c ≤ ballVolume g p s /
        ENNReal.ofReal (modelVolume K n s) := by
    have heventR : ∀ᶠ s in 𝓝[>] (0 : ℝ), s ≤ R :=
      (show 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ) from inf_le_left)
        (Iic_mem_nhds hRpos)
    filter_upwards [self_mem_nhdsWithin, heventR] with s hs hsR
    simpa only [c, n] using
      localBishopGromov_ratio (I := I) g hEnorm p K R₀ hRic hs hsR hR
  have hc : c ≤ 1 := ge_of_tendsto hsmall hle
  have hraw := (ENNReal.div_le_iff hmR.ne' ENNReal.ofReal_ne_top).1
    (show ballVolume g p R / ENNReal.ofReal (modelVolume K n R) ≤ 1 by
      simpa only [c] using hc)
  simpa only [n, one_mul] using hraw

theorem localBishopGromovVolumeComparison [ConnectedSpace M] [CompleteSpace M]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (_hn : 2 ≤ Module.finrank ℝ E)
    (p : M) (K : ℝ) (R₀ : Set.Ioi (0 : ℝ≥0∞))
    (hRic : ricciBoundedBelowOn (I := I) g
      {y : M | riemannianEDist I p y < R₀.1}
      (((Module.finrank ℝ E - 1 : ℕ) : ℝ) * K)) :
    (∀ {s R : ℝ}, 0 < s → s ≤ R →
        ENNReal.ofReal R ≤ bishopGromovRadius K R₀.1 →
        ballVolume g p R /
            ENNReal.ofReal (modelVolume K (Module.finrank ℝ E) R) ≤
          ballVolume g p s /
            ENNReal.ofReal (modelVolume K (Module.finrank ℝ E) s)) ∧
      Tendsto (fun r : ℝ => ballVolume g p r /
          ENNReal.ofReal (modelVolume K (Module.finrank ℝ E) r))
        (𝓝[>] (0 : ℝ)) (𝓝 1) ∧
      (∀ {R : ℝ}, 0 < R →
        ENNReal.ofReal R ≤ bishopGromovRadius K R₀.1 →
        ballVolume g p R ≤
          ENNReal.ofReal (modelVolume K (Module.finrank ℝ E) R)) := by
  refine ⟨?_, tendsto_ballVolume_div_modelVolume (I := I) g hEnorm p K, ?_⟩
  · intro s R hs hsR hR
    exact localBishopGromov_ratio (I := I) g hEnorm p K R₀ hRic hs hsR hR
  · intro R hRpos hR
    exact localBishopGromov_absolute_upper
      (I := I) g hEnorm p K R₀ hRic hRpos hR

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
