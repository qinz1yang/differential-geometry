import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientReducedLengthTimeComparison

set_option autoImplicit false
noncomputable section
namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open Set Filter
open DifferentialGeometry.CheegerGromovCompactness CanonicalNeighborhood
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff _root_.Topology
universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type uH} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

theorem continuousOn_redLength_space_time_of_ancient
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (p : F.M) :
    ContinuousOn (fun z : ℝ × F.M => redLength F.S 0 p z.2 z.1) (Ioi 0 ×ˢ univ) := by
  rintro ⟨tau, q⟩ htau
  apply ContinuousAt.continuousWithinAt
  let a := tau / 2
  have ha : 0 < a := half_pos htau.1
  have heq : tau / a = 2 := (div_eq_iff ha.ne').mpr (by dsimp only [a]; ring)
  let A := redLength F.S 0 p q a + 1
  obtain ⟨K, hK⟩ := exists_lipschitzOnWith_redLength_rescaled_time F hF p
    (A := A) (T := 3) (by norm_num)
  have hbaseC : Continuous (fun z : ℝ × F.M => redLength F.S 0 p z.2 a) :=
    (continuous_redLength_of_ancient F hF p ha).comp continuous_snd
  have hbase : ∀ᶠ z : ℝ × F.M in 𝓝 (tau, q), redLength F.S 0 p z.2 a ≤ A :=
    (hbaseC.continuousAt.eventually (Iio_mem_nhds (by dsimp [A]; linarith))).mono
      fun _ hz => hz.le
  have hband : ∀ᶠ z : ℝ × F.M in 𝓝 (tau, q), z.1 / a ∈ Icc (1 : ℝ) 3 :=
    (continuous_fst.div_const a).continuousAt.preimage_mem_nhds (by
      rw [heq]
      exact Icc_mem_nhds (by norm_num) (by norm_num))
  have hspaceC : Continuous (fun z : ℝ × F.M => redLength F.S 0 p z.2 tau) :=
    (continuous_redLength_of_ancient F hF p htau.1).comp continuous_snd
  let B : ℝ × F.M → ℝ := fun z =>
    (K : ℝ) * |z.1 / a - tau / a| +
      |redLength F.S 0 p z.2 tau - redLength F.S 0 p q tau|
  have hBC : Continuous B :=
    (continuous_const.mul ((continuous_fst.div_const a).sub continuous_const).abs).add
      (hspaceC.sub continuous_const).abs
  have hBzero : B (tau, q) = 0 := by simp only [B, sub_self, abs_zero, mul_zero, add_zero]
  change Tendsto _ (𝓝 (tau, q)) _
  rw [Metric.tendsto_nhds]
  intro epsilon hepsilon
  have hsmall : ∀ᶠ z in 𝓝 (tau, q), B z < epsilon :=
    hBC.continuousAt.eventually (Iio_mem_nhds (hBzero ▸ hepsilon))
  filter_upwards [hbase, hband, hsmall] with z hz hb hs
  have hh := (hK a ha z.2 hz).dist_le_mul (z.1 / a) hb (tau / a)
    (by rw [heq]; norm_num)
  simp only [mul_div_cancel₀ _ ha.ne', Real.dist_eq] at hh
  rw [Real.dist_eq]
  calc
    _ ≤ |redLength F.S 0 p z.2 z.1 - redLength F.S 0 p z.2 tau| +
          |redLength F.S 0 p z.2 tau - redLength F.S 0 p q tau| := abs_sub_le _ _ _
    _ ≤ B z := add_le_add hh le_rfl
    _ < epsilon := hs

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
