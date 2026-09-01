import DifferentialGeometry.Geometry.Compactness.CheegerGromov.CenterOfMass.Average.TwoParameterConvergence
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.CenterOfMass.Average.Weights.Bump

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Bundle
open scoped Manifold ContDiff Topology

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

section Diagonal

open DifferentialGeometry.Geometry.Riemannian

variable {M' : Type u} [TopologicalSpace M'] [ChartedSpace H M'] [IsManifold I ∞ M']
  [T2Space M'] [T2Space (TangentBundle I M')] [SigmaCompactSpace M']
  [ConnectedSpace M'] [T3Space M']

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [Module.Finite ℝ E] [CompleteSpace E] in
theorem centerOfMass_diag
    [Module.Finite ℝ E]
    (g : SmoothRiemannianMetric I M') {ι : Type} [Fintype ι]
    (μ : ι → ℝ) (pts : ι → M') (join : M' → M' → ℝ → M') (p : M') (r : ℝ)
    (h : CenterInput (I := I) g μ pts join p r) (q : M') (hall : ∀ i, pts i = q) :
    centerOfMass (I := I) g μ pts join p r h = q := by
  let : RiemannianBundle (fun x : M' => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M' => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : MetricSpace M' := HopfRinow.riemMetricSpace (I := I) (M := M')
  have hnear : ∀ i : ι, dist q (pts i) ≤ (0 : ℝ) := fun i => by rw [hall i, dist_self]
  have hd := centerOfMass.dist_le (I := I) (g := g) (μ := μ) (pts := pts) (join := join)
    (p := p) (r := r) h le_rfl hnear
  rw [mul_zero] at hd
  exact dist_le_zero.mp hd

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [Module.Finite ℝ E] in
theorem chartCm_diag
    [Module.Finite ℝ E]
    (g : SmoothRiemannianMetric I M') {ι : Type} [Fintype ι]
    (μ : ι → ℝ) (join : M' → M' → ℝ → M') (p : M') (r : ℝ) (z : E)
    (hz : z ∈ (NormalCoordinates.normalChartAt (I := I) g p).target)
    (h : CenterInput (I := I) g μ
      (fun _ : ι => (NormalCoordinates.normalChartAt (I := I) g p).symm z) join p r) :
    NormalCoordinates.normalChartAt (I := I) g p
      (centerOfMass (I := I) g μ
        (fun _ : ι => (NormalCoordinates.normalChartAt (I := I) g p).symm z) join p r h) = z := by
  rw [centerOfMass_diag (I := I) g μ _ join p r h
    ((NormalCoordinates.normalChartAt (I := I) g p).symm z) (fun _ => rfl)]
  exact NormalCoordinates.normalChartAt_right_inv (I := I) g p hz

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [Module.Finite ℝ E] [CompleteSpace E] in
theorem centerOfMass_delta
    [Module.Finite ℝ E]
    (g : SmoothRiemannianMetric I M') {ι : Type} [Fintype ι]
    (μ : ι → ℝ) (pts : ι → M') (join : M' → M' → ℝ → M') (p : M') (r : ℝ)
    (h : CenterInput (I := I) g μ pts join p r) (i0 : ι)
    (hdead : ∀ i, i ≠ i0 → μ i = 0) :
    centerOfMass (I := I) g μ pts join p r h = pts i0 := by
  let : RiemannianBundle (fun x : M' => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M' => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : MetricSpace M' := HopfRinow.riemMetricSpace (I := I) (M := M')
  have hzero : CenterOfMass.centerEnergy (I := I) g μ pts (pts i0) = 0 := by
    simp only [CenterOfMass.centerEnergy]
    rw [Finset.sum_eq_zero, mul_zero]
    intro i _
    rcases eq_or_ne i i0 with rfl | hne
    · rw [Manifold.riemannianEDist_self]
      simp
    · rw [hdead i hne, zero_mul]
  have hmin : ∀ z : M', CenterOfMass.centerEnergy (I := I) g μ pts (pts i0)
      ≤ CenterOfMass.centerEnergy (I := I) g μ pts z := by
    intro z
    rw [hzero]
    simp only [CenterOfMass.centerEnergy]
    refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ => ?_)
    exact mul_nonneg (h.μ_nonneg i) (by positivity)
  exact ((centerOfMass.unique (I := I) (g := g) (μ := μ) (pts := pts) (join := join)
    (p := p) (r := r) h) (pts i0) hmin).symm

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [Module.Finite ℝ E] in
theorem diagEventuallyEqId
    [Module.Finite ℝ E]
    (g : SmoothRiemannianMetric I M') {ι : Type} [Fintype ι]
    (μfun : E → ι → ℝ) (join : M' → M' → ℝ → M') (p : M') (r : ℝ)
    {x : E} {V : Set E} (hV : IsOpen V) (hxV : x ∈ V)
    (hVtgt : V ⊆ (NormalCoordinates.normalChartAt (I := I) g p).target)
    (H : ∀ z ∈ V, CenterInput (I := I) g (μfun z)
      (fun _ : ι => (NormalCoordinates.normalChartAt (I := I) g p).symm z) join p r)
    {G : E → E}
    (hagree : ∀ z, ∀ hz : z ∈ V,
      G z = NormalCoordinates.normalChartAt (I := I) g p
        (centerOfMass (I := I) g (μfun z)
          (fun _ : ι => (NormalCoordinates.normalChartAt (I := I) g p).symm z) join p r
          (H z hz))) :
    G =ᶠ[nhds x] fun y => y := by
  filter_upwards [hV.mem_nhds hxV] with z hz
  rw [hagree z hz, chartCm_diag (I := I) g (μfun z) join p r z (hVtgt hz) (H z hz)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [Module.Finite ℝ E] in
omit [CompleteSpace E] in
theorem cmDeltaOfBump
    [Module.Finite ℝ E]
    {ι : Type} [DecidableEq ι] [Fintype ι] [HasContDiffBump E]
    (g : SmoothRiemannianMetric I M') {χ : E → ℝ} (f : ι → ContDiffBump (0 : E))
    {J : ι → E → E} {i0 : ι} {x₀ : E}
    (pts : ι → M') (join : M' → M' → ℝ → M') (p : M') (r : ℝ)
    (hfar : ∀ j, j ≠ i0 → (f j).rOut ≤ ‖J j x₀‖)
    (hmem0 : ‖J i0 x₀‖ ≤ (f i0).rIn)
    (H : CenterInput (I := I) g
      (fun i => normWeights (bumpNum χ (fun i' => ⇑(f i')) J i0) i x₀) pts join p r) :
    centerOfMass (I := I) g
      (fun i => normWeights (bumpNum χ (fun i' => ⇑(f i')) J i0) i x₀) pts join p r H
      = pts i0 := by
  obtain ⟨hkill, hbase⟩ := bumpNumDeltaOfNorm (χ := χ) f (J := J) hfar
  have hone : f i0 (J i0 x₀) = 1 :=
    (f i0).one_of_mem_closedBall
      (by rw [Metric.mem_closedBall, dist_zero_right]; exact hmem0)
  have hne : bumpNum χ (fun i' => ⇑(f i')) J i0 i0 x₀ ≠ 0 := by
    rw [hbase, hone]; exact one_ne_zero
  obtain ⟨hw1, hw0⟩ := normWeights_delta (num := bumpNum χ (fun i' => ⇑(f i')) J i0)
    (z := x₀) i0 hkill hne
  exact centerOfMass_delta (I := I) g _ pts join p r H i0 (fun j hj => hw0 j hj)

end Diagonal

end HCGCompactness
end DifferentialGeometry
