import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume.Covering
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume.UpperBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.BackwardSliceMass
import DifferentialGeometry.Topology.Covering.Fiber.FiniteCardinality
import DifferentialGeometry.Topology.Manifold.LocallyPathConnected

set_option autoImplicit false
noncomputable section

section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure

variable {E H M N : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [CompactSpace M] [ConnectedSpace M]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T2Space N]
  [CompactSpace N] [ConnectedSpace N] {D : RealTimeInterval}

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩
private local instance : MeasurableSpace N := borel N
private local instance : BorelSpace N := ⟨rfl⟩

variable [NeZero (Module.finrank ℝ E)]

private theorem redVolume_le_one_of_compact
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : ℝ) (x : M) {tau : ℝ} (htau : 0 < tau)
    (hreg : Icc (T - tau) T ⊆ D.regular) : redVolume S T x tau ≤ 1 := by
  apply redVolume_le_one_of_rm S hS T (RiemannianMetricComplete.of_compact _) x ?_ htau hreg
  intro sigma _ hslab
  obtain ⟨K, _, hK⟩ := exists_curvature_bound_on_closed_interval_of_isSolutionOn S hS hslab
  exact ⟨K, hK⟩

theorem natCast_mul_asymptoticReducedVolume_le_one_of_compact_covering
    (S : SolutionOn (I := I) (M := N) D) (hS : IsSolutionOn S)
    (p : M → N) (hp : IsLocalDiffeomorph I I ∞ p) (hcover : IsCoveringMap p)
    (k : ℕ) (hcard : ∀ y : N, {x : M | p x = y}.encard = (k : ℕ∞))
    (T : ℝ) (hregular : Iic T ⊆ D.regular)
    (hscalar : ∀ t ≤ T, ∀ y : N, 0 ≤ S.scalar t y) (x : M) :
    (k : ℝ≥0∞) * KappaSolutions.asymptoticReducedVolume S T (p x) ≤ 1 := by
  obtain ⟨C, _, hbound⟩ := exists_redVolume_covering_lower_bound_of_compact
    S hS p hp hcover k hcard T hregular hscalar x
  have hforall (tau : ℝ) (htau : 1 < tau) :
      ENNReal.ofReal (Real.exp (-C / (2 * Real.sqrt tau))) *
        ((k : ℝ≥0∞) * KappaSolutions.asymptoticReducedVolume S T (p x)) ≤ 1 := by
    have hle : KappaSolutions.asymptoticReducedVolume S T (p x) ≤ redVolume S T (p x) tau :=
      iInf_le (fun t : Ioi (0 : ℝ) => KappaSolutions.intrinsicReducedVolume S T (p x) t)
        ⟨tau, zero_lt_one.trans htau⟩
    apply (mul_le_mul' le_rfl (mul_le_mul' le_rfl hle)).trans
    exact (hbound tau htau).trans (redVolume_le_one_of_compact
      (S.localPullback p hp) (hS.localPullback p hp) T x (zero_lt_one.trans htau)
      (fun _ ht => hregular ht.2))
  have hratio : Tendsto (fun r : ℝ => -C / (2 * r)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_id.const_mul_atTop (by norm_num))
  have hfactor : Tendsto (fun r : ℝ => ENNReal.ofReal (Real.exp (-C / (2 * r))))
      atTop (𝓝 1) := by
    simpa only [Real.exp_zero, ENNReal.ofReal_one, Function.comp_def] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        (Real.continuous_exp.continuousAt.tendsto.comp hratio)
  have hlim := ENNReal.Tendsto.mul_const
    (b := (k : ℝ≥0∞) * KappaSolutions.asymptoticReducedVolume S T (p x))
    hfactor (Or.inl one_ne_zero)
  rw [one_mul] at hlim
  apply le_of_tendsto hlim
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with r hr
  have hr0 : 0 ≤ r := zero_le_one.trans hr.le
  have hr2 : 1 < r ^ 2 := by nlinarith
  simpa only [Real.sqrt_sq hr0] using hforall (r ^ 2) hr2

end DifferentialGeometry.PDE.RicciFlow.Perelman

end

section

open Set
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open DifferentialGeometry.Geometry.Curvature

variable {E H M N : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [CompactSpace M] [ConnectedSpace M]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T2Space N]
  [CompactSpace N] [ConnectedSpace N] {D : RealTimeInterval}

theorem covering_injective_of_one_half_lt_asymptoticReducedVolume
    (S : SolutionOn (I := I) (M := N) D) (hS : IsSolutionOn S)
    (p : M → N) (hp : IsLocalDiffeomorph I I ∞ p) (hcover : IsCoveringMap p)
    (T : ℝ) (hregular : Iic T ⊆ D.regular)
    (hscalar : ∀ t ≤ T, ∀ y : N, 0 ≤ S.scalar t y) (x : M)
    (hmass : (1 / 2 : ℝ≥0∞) < KappaSolutions.asymptoticReducedVolume S T (p x)) :
    Function.Injective p := by
  let : LocallyPathConnectedSpace N :=
    Topology.Manifold.locallyPathConnectedSpace_of_modelWithCorners I
  let : PathConnectedSpace N := pathConnectedSpace_iff_connectedSpace.mpr inferInstance
  obtain ⟨k, hcard⟩ := Topology.Covering.exists_encard_fiber_eq_natCast_of_compact hcover
  have hbound := natCast_mul_asymptoticReducedVolume_le_one_of_compact_covering
    S hS p hp hcover k hcard T hregular hscalar x
  have hk : k ≤ 1 := by
    by_contra hnot
    have hk2 : 2 ≤ k := by omega
    have hk2' : (2 : ℝ≥0∞) ≤ k := by exact_mod_cast hk2
    have hlt := ENNReal.mul_lt_mul_right (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) hmass
    have htwo : (2 : ℝ≥0∞) * (1 / 2) = 1 := by
      simpa only [one_div] using ENNReal.mul_inv_cancel (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
    rw [htwo] at hlt
    exact (not_lt_of_ge hbound) (hlt.trans_le (mul_le_mul' hk2' le_rfl))
  intro y z hyz
  have hsmall : {w : M | p w = p y}.encard ≤ 1 := by
    rw [hcard]
    exact_mod_cast hk
  exact Set.encard_le_one_iff.mp hsmall y z rfl hyz.symm

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
