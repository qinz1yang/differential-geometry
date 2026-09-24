import DifferentialGeometry.Geometry.Compactness.CheegerGromov.CenterOfMass.NormalCoordinates.Hessian
import DifferentialGeometry.Geometry.Exponential.DiagonalExponential.FiberComparison
import DifferentialGeometry.Geometry.Exponential.NormalBall.TangentCoordinates
import DifferentialGeometry.Geometry.Exponential.NormalBall.DiagonalInverseBranch

noncomputable section
open scoped BigOperators ContDiff Manifold

namespace DifferentialGeometry.CheegerGromovCompactness

variable {E G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [AddCommGroup G] [Module ℝ G] {ι : Type*} [Fintype ι]

theorem invVelocitySum_eq_zero_of_linearMap_eq
    (e e' : OpenPartialHomeomorph (E × E) (E × E))
    (μ : ι → ℝ) (ξ ξ' : ι → E) (z z' : E)
    (L L' : E →ₗ[ℝ] G) (hL : Function.Injective L)
    (htransport : ∀ i, μ i ≠ 0 →
      L (e.symm (z, ξ i)).2 = L' (e'.symm (z', ξ' i)).2)
    (hroot : invVelocitySum e' μ ξ' z' = 0) :
    invVelocitySum e μ ξ z = 0 := by
  apply hL
  rw [map_zero]
  have hsum : L (invVelocitySum e μ ξ z) = L' (invVelocitySum e' μ ξ' z') := by
    simp only [invVelocitySum, map_sum, map_smul]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : μ i = 0
    · simp only [hi, zero_smul]
    · rw [htransport i hi]
  rw [hsum, hroot, map_zero]

end DifferentialGeometry.CheegerGromovCompactness
end

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Exponential

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
variable [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

theorem invVelocitySum_eq_zero_of_fiber_ball_subset
    {g : SmoothRiemannianMetric I M}
    {hEnorm : IsMetricNorm (I := I) (M := M) g}
    {p₁ p₂ y : M}
    (B₁ : DiagonalInverseBranch (I := I) g hEnorm p₁)
    (B₂ : DiagonalInverseBranch (I := I) g hEnorm p₂)
    (e₁ e₂ : OpenPartialHomeomorph (E × E) (E × E))
    {ι : Type*} [Fintype ι] (μ : ι → ℝ) (points : ι → M)
    (ξ₁ ξ₂ : ι → E) (z₁ z₂ : E)
    (L₁ L₂ : E →ₗ[ℝ] TangentSpace I y) (hL₁ : Function.Injective L₁)
    {r : ℝ}
    (hd : ∀ i, μ i ≠ 0 → riemannianEDist I y (points i) < ENNReal.ofReal r)
    (hsource₁ : ∀ v : TangentSpace I y, Real.sqrt (g.inner y v v) < r →
      (⟨y, v⟩ : TangentBundle I M) ∈ B₁.hom.source)
    (hsource₂ : ∀ v : TangentSpace I y, Real.sqrt (g.inner y v v) < r →
      (⟨y, v⟩ : TangentBundle I M) ∈ B₂.hom.source)
    (hcoords₁ : ∀ i, μ i ≠ 0 →
      B₁.inv (y, points i) = (⟨y, L₁ (e₁.symm (z₁, ξ₁ i)).2⟩ : TangentBundle I M))
    (hcoords₂ : ∀ i, μ i ≠ 0 →
      B₂.inv (y, points i) = (⟨y, L₂ (e₂.symm (z₂, ξ₂ i)).2⟩ : TangentBundle I M))
    (hroot : CheegerGromovCompactness.invVelocitySum e₂ μ ξ₂ z₂ = 0) :
    CheegerGromovCompactness.invVelocitySum e₁ μ ξ₁ z₁ = 0 := by
  apply CheegerGromovCompactness.invVelocitySum_eq_zero_of_linearMap_eq
    e₁ e₂ μ ξ₁ ξ₂ z₁ z₂ L₁ L₂ hL₁ _ hroot
  intro i hi
  have heq := B₁.inv_eq_of_fiber_ball_subset B₂ (hd i hi) hsource₁ hsource₂
  rw [hcoords₁ i hi, hcoords₂ i hi] at heq
  exact congrArg (fun t : TangentBundle I M => (t.snd : E)) heq

end Exponential
end Riemannian
end Geometry
end DifferentialGeometry
end

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Exponential

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
variable [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

theorem source_eq_of_invVelocity_root_of_fiber_ball_subset
    {g : SmoothRiemannianMetric I M}
    {hEnorm : IsMetricNorm (I := I) (M := M) g}
    {p₁ p₂ : M}
    (B₁ : DiagonalInverseBranch (I := I) g hEnorm p₁)
    (B₂ : DiagonalInverseBranch (I := I) g hEnorm p₂)
    (c : NormalCoordinates.NormalBallChart (I := I) p₁)
    (d : NormalCoordinates.NormalBallChart (I := I) p₂)
    (e₁ e₂ : OpenPartialHomeomorph (E × E) (E × E))
    {ι : Type*} [Fintype ι] (μ : ι → ℝ) (points : ι → M)
    (ξ₁ ξ₂ : ι → E) {u v z : E} {r rTube : ℝ}
    (hy : d.hom v ∈ c.restrictBall.target)
    (hclose : dist (c.inv (d.hom v)) z < rTube)
    (hunique : ∀ w, dist w z < rTube →
      CheegerGromovCompactness.invVelocitySum e₁ μ ξ₁ w = 0 → w = u)
    (hd : ∀ i, μ i ≠ 0 → riemannianEDist I (d.hom v) (points i) < ENNReal.ofReal r)
    (hsource₁ : ∀ w : TangentSpace I (d.hom v),
      Real.sqrt (g.inner (d.hom v) w w) < r →
      (⟨d.hom v, w⟩ : TangentBundle I M) ∈ B₁.hom.source)
    (hsource₂ : ∀ w : TangentSpace I (d.hom v),
      Real.sqrt (g.inner (d.hom v) w w) < r →
      (⟨d.hom v, w⟩ : TangentBundle I M) ∈ B₂.hom.source)
    (hcoords₁ : ∀ i, μ i ≠ 0 →
      B₁.inv (d.hom v, points i) = (⟨d.hom v,
        (mfderiv 𝓘(ℝ, E) I (fun w : E => c.hom w) (c.inv (d.hom v)))
          (e₁.symm (c.inv (d.hom v), ξ₁ i)).2⟩ : TangentBundle I M))
    (hcoords₂ : ∀ i, μ i ≠ 0 →
      B₂.inv (d.hom v, points i) = (⟨d.hom v,
        (mfderiv 𝓘(ℝ, E) I (fun w : E => d.hom w) v)
          (e₂.symm (v, ξ₂ i)).2⟩ : TangentBundle I M))
    (hroot : CheegerGromovCompactness.invVelocitySum e₂ μ ξ₂ v = 0) :
    c.hom u = d.hom v := by
  have hzero := invVelocitySum_eq_zero_of_fiber_ball_subset (y := d.hom v) B₁ B₂ e₁ e₂ μ points
    ξ₁ ξ₂ (c.inv (d.hom v)) v
    (mfderiv 𝓘(ℝ, E) I (fun w : E => c.hom w) (c.inv (d.hom v))).toLinearMap
    (mfderiv 𝓘(ℝ, E) I (fun w : E => d.hom w) v).toLinearMap
    (NormalCoordinates.NormalBallChart.mfderiv_injective c hy)
    hd hsource₁ hsource₂ hcoords₁ hcoords₂ hroot
  have heq := hunique (c.inv (d.hom v)) hclose hzero
  rw [← heq]
  exact c.restrictBall.right_inv hy

end Exponential
end Riemannian
end Geometry
end DifferentialGeometry
end

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Exponential

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
variable [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

theorem source_eq_of_chart_invVelocity_roots
    {g : SmoothRiemannianMetric I M}
    {hEnorm : IsMetricNorm (I := I) (M := M) g}
    {p₁ p₂ : M} (c : NormalCoordinates.NormalBallChart (I := I) p₁)
    (d : NormalCoordinates.NormalBallChart (I := I) p₂)
    (e₁ e₂ : OpenPartialHomeomorph (E × E) (E × E))
    {q₁ q₂ : ℝ} (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (hsource₁ : e₁.source = Metric.ball (0 : E × E) q₁)
    (hsource₂ : e₂.source = Metric.ball (0 : E × E) q₂)
    (hzero₁ : e₁ 0 = 0) (hzero₂ : e₂ 0 = 0)
    (hinv₁ : ContDiffOn ℝ ∞ (e₁.symm : E × E → E × E) e₁.target)
    (hinv₂ : ContDiffOn ℝ ∞ (e₂.symm : E × E → E × E) e₂.target)
    (hdiag₁ : ∀ z ∈ e₁.source, c.pair (e₁ z) = diagExp g hEnorm (c.tangent z))
    (hdiag₂ : ∀ z ∈ e₂.source, d.pair (e₂ z) = diagExp g hEnorm (d.tangent z))
    (hfence₁ : ∀ z ∈ e₁.source,
      z.1 ∈ Metric.ball (0 : E) c.radius ∧
      (e₁ z).1 ∈ Metric.ball (0 : E) c.radius ∧ (e₁ z).2 ∈ Metric.ball (0 : E) c.radius)
    (hfence₂ : ∀ z ∈ e₂.source,
      z.1 ∈ Metric.ball (0 : E) d.radius ∧
      (e₂ z).1 ∈ Metric.ball (0 : E) d.radius ∧ (e₂ z).2 ∈ Metric.ball (0 : E) d.radius)
    {ι : Type*} [Fintype ι] (mu : ι → ℝ) (points : ι → M)
    (xi₁ xi₂ : ι → E) {u v z : E} {rTube : ℝ}
    (hv : v ∈ Metric.ball (0 : E) d.radius)
    (hy : d.hom v ∈ c.restrictBall.target)
    (hyq₁ : ‖c.inv (d.hom v)‖ < q₁) (hyq₂ : ‖v‖ < q₂)
    (hlower₁ : ∀ w : E,
      (1 / 2 : ℝ) * ‖w‖ ^ 2 ≤ c.metric g (c.inv (d.hom v)) w w)
    (hlower₂ : ∀ w : E, (1 / 2 : ℝ) * ‖w‖ ^ 2 ≤ d.metric g v w w)
    (hclose : dist (c.inv (d.hom v)) z < rTube)
    (hunique : ∀ w, dist w z < rTube →
      CheegerGromovCompactness.invVelocitySum e₁ mu xi₁ w = 0 → w = u)
    (hdist : ∀ i, mu i ≠ 0 →
      riemannianEDist I (d.hom v) (points i) < ENNReal.ofReal (min q₁ q₂ / 2))
    (hatoms₁ : ∀ i, mu i ≠ 0 → xi₁ i ∈ Metric.ball (0 : E) c.radius ∧ c.hom (xi₁ i) = points i)
    (hatoms₂ : ∀ i, mu i ≠ 0 → xi₂ i ∈ Metric.ball (0 : E) d.radius ∧ d.hom (xi₂ i) = points i)
    (hpairs₁ : ∀ i, mu i ≠ 0 → (c.inv (d.hom v), xi₁ i) ∈ e₁.target)
    (hpairs₂ : ∀ i, mu i ≠ 0 → (v, xi₂ i) ∈ e₂.target)
    (hroot : CheegerGromovCompactness.invVelocitySum e₂ mu xi₂ v = 0) :
    c.hom u = d.hom v := by
  have hz₁ : (0 : E × E) ∈ e₁.source := by
    rw [hsource₁]
    exact Metric.mem_ball_self hq₁
  have hz₂ : (0 : E × E) ∈ e₂.source := by
    rw [hsource₂]
    exact Metric.mem_ball_self hq₂
  let B₁ := c.diagonalInverseBranch e₁ hz₁ hzero₁ hinv₁ hdiag₁
  let B₂ := d.diagonalInverseBranch e₂ hz₂ hzero₂ hinv₂ hdiag₂
  have hf₁ : MapsTo e₁ (Metric.ball (0 : E × E) q₁) c.pairHome.source := by
    intro w hw
    rw [c.pairHome_source]
    exact (hfence₁ w (hsource₁ ▸ hw)).2
  have hf₂ : MapsTo e₂ (Metric.ball (0 : E × E) q₂) d.pairHome.source := by
    intro w hw
    rw [d.pairHome_source]
    exact (hfence₂ w (hsource₂ ▸ hw)).2
  have hdy : d.hom v ∈ d.restrictBall.target := d.restrictBall.map_source hv
  have hdinv : d.inv (d.hom v) = v := d.restrictBall.left_inv hv
  have hcy : c.inv (d.hom v) ∈ Metric.ball (0 : E) c.radius := c.restrictBall.map_target hy
  have hcyEq : c.hom (c.inv (d.hom v)) = d.hom v := c.restrictBall.right_inv hy
  have hball₁ := c.diagonalInverseBranch_fiber_ball_subset_of_metric_lower_bound e₁
    hz₁ hzero₁ hinv₁ hdiag₁ (hsource₁ ▸ Set.Subset.rfl) hf₁ hy hyq₁ hlower₁
  have hball₂ := d.diagonalInverseBranch_fiber_ball_subset_of_metric_lower_bound e₂
    hz₂ hzero₂ hinv₂ hdiag₂ (hsource₂ ▸ Set.Subset.rfl) hf₂ hdy
    (by simpa only [hdinv] using hyq₂) (by simpa only [hdinv] using hlower₂)
  apply source_eq_of_invVelocity_root_of_fiber_ball_subset B₁ B₂ c d e₁ e₂ mu points
    xi₁ xi₂ hy hclose hunique hdist
    (fun w hw => hball₁ w (hw.trans_le (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num))))
    (fun w hw => hball₂ w (hw.trans_le (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num))))
    _ _ hroot
  · intro i hi
    have hc := c.diagonalInverseBranch_inv_apply e₁ hdiag₁ hfence₁ hz₁ hzero₁ hinv₁
      hcy (hatoms₁ i hi).1 (hpairs₁ i hi)
    rw [hcyEq, (hatoms₁ i hi).2] at hc
    exact hc
  · intro i hi
    have hc := d.diagonalInverseBranch_inv_apply e₂ hdiag₂ hfence₂ hz₂ hzero₂ hinv₂
      hv (hatoms₂ i hi).1 (hpairs₂ i hi)
    rw [(hatoms₂ i hi).2] at hc
    exact hc

end Exponential
end Riemannian
end Geometry
end DifferentialGeometry
end

noncomputable section

open Bundle Filter Manifold Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Geometry.Riemannian.Exponential

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {κ P : Type*} {M : κ → Type*}
  [∀ k, TopologicalSpace (M k)] [∀ k, ChartedSpace H (M k)]
  [∀ k, IsManifold I ∞ (M k)] [∀ k, T2Space (M k)] [∀ k, SigmaCompactSpace (M k)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [∀ k, RiemannianBundle (fun x : M k ↦ TangentSpace I x)]
  [∀ k, PseudoEMetricSpace (M k)] [∀ k, IsRiemannianManifold I (M k)]
  [∀ k, CompleteSpace (M k)]
  [∀ k, IsContinuousRiemannianBundle E (fun x : M k ↦ TangentSpace I x)]

theorem eventually_eqOn_of_chart_invVelocity_roots
    (g : ∀ k, SmoothRiemannianMetric I (M k))
    (hEnorm : ∀ k, IsMetricNorm (I := I) (M := M k) (g k))
    {p₁ p₂ : ∀ k, M k}
    (c : ∀ k, NormalCoordinates.NormalBallChart (I := I) (p₁ k))
    (d : ∀ k, NormalCoordinates.NormalBallChart (I := I) (p₂ k))
    (e₁ e₂ : κ → OpenPartialHomeomorph (E × E) (E × E))
    {l : Filter κ} {q₁ q₂ : κ → ℝ}
    (hsource₁ : ∀ᶠ k in l, (e₁ k).source = Metric.ball (0 : E × E) (q₁ k))
    (hsource₂ : ∀ᶠ k in l, (e₂ k).source = Metric.ball (0 : E × E) (q₂ k))
    (hzero₁ : ∀ᶠ k in l, e₁ k 0 = 0) (hzero₂ : ∀ᶠ k in l, e₂ k 0 = 0)
    (hinv₁ : ∀ᶠ k in l,
      ContDiffOn ℝ ∞ ((e₁ k).symm : E × E → E × E) (e₁ k).target)
    (hinv₂ : ∀ᶠ k in l,
      ContDiffOn ℝ ∞ ((e₂ k).symm : E × E → E × E) (e₂ k).target)
    (hdiag₁ : ∀ᶠ k in l, ∀ w ∈ (e₁ k).source,
      (c k).pair (e₁ k w) = diagExp (g k) (hEnorm k) ((c k).tangent w))
    (hdiag₂ : ∀ᶠ k in l, ∀ w ∈ (e₂ k).source,
      (d k).pair (e₂ k w) = diagExp (g k) (hEnorm k) ((d k).tangent w))
    (hfence₁ : ∀ᶠ k in l, ∀ w ∈ (e₁ k).source,
      w.1 ∈ Metric.ball (0 : E) (c k).radius ∧
      (e₁ k w).1 ∈ Metric.ball (0 : E) (c k).radius ∧
      (e₁ k w).2 ∈ Metric.ball (0 : E) (c k).radius)
    (hfence₂ : ∀ᶠ k in l, ∀ w ∈ (e₂ k).source,
      w.1 ∈ Metric.ball (0 : E) (d k).radius ∧
      (e₂ k w).1 ∈ Metric.ball (0 : E) (d k).radius ∧
      (e₂ k w).2 ∈ Metric.ball (0 : E) (d k).radius)
    {ι : Type*} [Fintype ι] {K : Set P}
    (mu : κ → P → ι → ℝ) (points : ∀ k, P → ι → M k)
    (xi₁ xi₂ : κ → P → ι → E) {u v z : κ → P → E} {rTube : κ → P → ℝ}
    (hy : ∀ᶠ k in l, ∀ x ∈ K, (d k).hom (v k x) ∈ (c k).restrictBall.target)
    (hyq₁ : ∀ᶠ k in l, ∀ x ∈ K, ‖(c k).inv ((d k).hom (v k x))‖ < q₁ k)
    (hyq₂ : ∀ᶠ k in l, ∀ x ∈ K, ‖v k x‖ < q₂ k)
    (hlower₁ : ∀ᶠ k in l, ∀ x ∈ K, ∀ w : E,
      (1 / 2 : ℝ) * ‖w‖ ^ 2 ≤ (c k).metric (g k) ((c k).inv ((d k).hom (v k x))) w w)
    (hlower₂ : ∀ᶠ k in l, ∀ x ∈ K, ∀ w : E,
      (1 / 2 : ℝ) * ‖w‖ ^ 2 ≤ (d k).metric (g k) (v k x) w w)
    (hclose : ∀ᶠ k in l, ∀ x ∈ K,
      dist ((c k).inv ((d k).hom (v k x))) (z k x) < rTube k x)
    (hunique : ∀ᶠ k in l, ∀ x ∈ K, ∀ w, dist w (z k x) < rTube k x →
      CheegerGromovCompactness.invVelocitySum (e₁ k) (mu k x) (xi₁ k x) w = 0 → w = u k x)
    (hdist : ∀ i, ∀ᶠ k in l, ∀ x ∈ K, mu k x i ≠ 0 →
      riemannianEDist I ((d k).hom (v k x)) (points k x i) <
        ENNReal.ofReal (min (q₁ k) (q₂ k) / 2))
    (hatoms₁ : ∀ i, ∀ᶠ k in l, ∀ x ∈ K, mu k x i ≠ 0 →
      (c k).hom (xi₁ k x i) = points k x i)
    (hatoms₂ : ∀ i, ∀ᶠ k in l, ∀ x ∈ K, mu k x i ≠ 0 →
      (d k).hom (xi₂ k x i) = points k x i)
    (hpairs₁ : ∀ i, ∀ᶠ k in l, ∀ x ∈ K, mu k x i ≠ 0 →
      ((c k).inv ((d k).hom (v k x)), xi₁ k x i) ∈ (e₁ k).target)
    (hpairs₂ : ∀ i, ∀ᶠ k in l, ∀ x ∈ K, mu k x i ≠ 0 →
      (v k x, xi₂ k x i) ∈ (e₂ k).target)
    (hroot : ∀ᶠ k in l, ∀ x ∈ K,
      CheegerGromovCompactness.invVelocitySum (e₂ k) (mu k x) (xi₂ k x) (v k x) = 0) :
    ∀ᶠ k in l, EqOn (fun x => (c k).hom (u k x)) (fun x => (d k).hom (v k x)) K := by
  filter_upwards [hsource₁, hsource₂, hzero₁, hzero₂, hinv₁, hinv₂, hdiag₁, hdiag₂,
    hfence₁, hfence₂, hy, hyq₁, hyq₂, hlower₁, hlower₂, hclose, hunique,
    eventually_all.mpr hdist, eventually_all.mpr hatoms₁, eventually_all.mpr hatoms₂,
    eventually_all.mpr hpairs₁, eventually_all.mpr hpairs₂, hroot]
      with k hs₁ hs₂ hz₁ hz₂ hi₁ hi₂ hd₁ hd₂ hf₁ hf₂ hyt hy₁ hy₂ hl₁ hl₂ hc hu hdt ha₁ ha₂
        hp₁ hp₂ hr x hx
  have hq₁ : 0 < q₁ k := (norm_nonneg _).trans_lt (hy₁ x hx)
  have hq₂ : 0 < q₂ k := (norm_nonneg _).trans_lt (hy₂ x hx)
  have hv : v k x ∈ Metric.ball (0 : E) (d k).radius := by
    apply (hf₂ (v k x, 0) ?_).1
    rw [hs₂]
    simpa only [Metric.mem_ball, dist_zero_right, Prod.norm_def, norm_zero, max_lt_iff]
      using And.intro (hy₂ x hx) hq₂
  apply source_eq_of_chart_invVelocity_roots (c k) (d k) (e₁ k) (e₂ k) hq₁ hq₂
    hs₁ hs₂ hz₁ hz₂ hi₁ hi₂ hd₁ hd₂ hf₁ hf₂ (mu k x) (points k x) (xi₁ k x) (xi₂ k x)
    hv (hyt x hx) (hy₁ x hx) (hy₂ x hx) (hl₁ x hx) (hl₂ x hx) (hc x hx) (hu x hx)
    (fun i => hdt i x hx) _ _ (fun i => hp₁ i x hx) (fun i => hp₂ i x hx) (hr x hx)
  · intro i hi
    refine ⟨?_, ha₁ i x hx hi⟩
    have ht := hp₁ i x hx hi
    have hf := (hf₁ _ ((e₁ k).map_target ht)).2.2
    simpa only [(e₁ k).right_inv ht] using hf
  · intro i hi
    refine ⟨?_, ha₂ i x hx hi⟩
    have ht := hp₂ i x hx hi
    have hf := (hf₂ _ ((e₂ k).map_target ht)).2.2
    simpa only [(e₂ k).right_inv ht] using hf

end DifferentialGeometry.Geometry.Riemannian.Exponential
end
