import DifferentialGeometry.Geometry.Metric.Distance.Ball
import DifferentialGeometry.Geometry.Exponential.MinimizingGeodesic
import DifferentialGeometry.Topology.FiberBundle.Separation

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry

open scoped Manifold ContDiff ENNReal Topology Bundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem closure_riemannianBallOf
    (g : SmoothRiemannianMetric I M) (hg : RiemannianMetricComplete g)
    (x : M) {r : ℝ} (hr : 0 < r) :
    closure (riemannianBallOf g x r) = riemannianClosedBallOf g x r := by
  let _ : IsManifold I 1 M := IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)
  let _ : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let _ : Bundle.RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let _ : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let _ : CompleteSpace M := hg.complete
  have hEnorm : Geometry.Riemannian.IsMetricNorm (I := I) g :=
    fun y v => Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) g y v
  apply Set.Subset.antisymm
  · apply closure_minimal (t := riemannianClosedBallOf g x r)
      (fun _ hy => (show Manifold.riemannianEDist I _ _ < ENNReal.ofReal r from hy).le)
    change IsClosed {y : M | edist x y ≤ ENNReal.ofReal r}
    exact isClosed_le (continuous_const.edist continuous_id) continuous_const
  intro y hy
  have hfin : Manifold.riemannianEDist I x y ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hy
  obtain ⟨v, hv, hnorm⟩ := Geometry.Riemannian.Exponential.minExp_of_ne_top
    g hEnorm x y hfin
  let γ : ℝ → M := Geometry.Riemannian.Exponential.intrinsicGeodesic g hEnorm x v
  have hγ : Continuous γ :=
    Geometry.Riemannian.Exponential.intrinsicGeodesic_continuous g hEnorm x v
  have hγone : γ 1 = y := hv
  have hbound : Real.sqrt (g.inner x v v) ≤ r := by
    rw [hnorm]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hy).trans_eq
      (ENNReal.toReal_ofReal hr.le)
  have hmaps : Set.MapsTo γ (Set.Ico (0 : ℝ) 1) (riemannianBallOf g x r) := by
    intro t ht
    have hd := Geometry.Riemannian.Exponential.intrinsicGeodesic_riemannianEDist_le
      g hEnorm x v ht.1
    rw [Geometry.Riemannian.Exponential.intrinsicGeodesic_zero, sub_zero] at hd
    have hlt : Real.sqrt (g.inner x v v) * t < r :=
      (mul_le_mul_of_nonneg_right hbound ht.1).trans_lt (by nlinarith [ht.2])
    exact hd.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hr).mpr hlt)
  rw [← hγone]
  apply hγ.continuousAt.continuousWithinAt.mem_closure _ hmaps
  rw [closure_Ico (by norm_num : (0 : ℝ) ≠ 1)]
  exact ⟨zero_le_one, le_rfl⟩

end DifferentialGeometry
