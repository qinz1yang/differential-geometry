import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Estimates.Curvature
import DifferentialGeometry.Topology.FirstExit

noncomputable section
open Set MeasureTheory
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {D : RealTimeInterval}

theorem lRegularizedAction_ge_of_scalar_lower_on_interior
    (S : SolutionOn (I := I) (M := M) D) (T : ℝ) (α : ℝ → M)
    {a b v B : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hbv : b ≤ v) (hB : 0 ≤ B)
    (hscalar : ∀ s ∈ Ioo a b, -B ≤ S.scalar (T - s ^ 2) (α s))
    (hLag : IntervalIntegrable (lRegularizedLagrangian S T α) volume a b) :
    -(2 * B * v ^ 2) * (b - a) ≤ lRegularizedAction S T α a b := by
  let C := -(2 * B * v ^ 2)
  have hh := intervalIntegral.integral_mono_on_of_le_Ioo hab
    (intervalIntegrable_const (c := C)) hLag (fun s hs => ?_)
  · simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm, lRegularizedAction, C] using hh
  have hs2 : s ^ 2 ≤ v ^ 2 :=
    (sq_le_sq₀ (ha.trans hs.1.le) (ha.trans (hab.trans hbv))).mpr (hs.2.le.trans hbv)
  have hsc := mul_le_mul_of_nonneg_left (hscalar s hs) (by positivity : 0 ≤ 2 * s ^ 2)
  have hsq := mul_le_mul_of_nonneg_left hs2 (by positivity : 0 ≤ 2 * B)
  have hkin := metric_inner_self_nonneg (S.base.metric (T - s ^ 2)) (α s) (lVelocity α s)
  dsimp only [C, lRegularizedLagrangian]
  nlinarith

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem lRegularizedAction_ge_of_subinterval_separation
    (S : SolutionOn (I := I) (M := M) D) (T : ℝ) (α : ℝ → M)
    {a b c d v μ B r : ℝ} (ha : 0 ≤ a) (hac : a ≤ c) (hcd : c < d)
    (hdb : d ≤ b) (hbv : b ≤ v) (hμ : 0 ≤ μ) (hB : 0 ≤ B) (hr : 0 ≤ r)
    (g : SmoothRiemannianMetric I M)
    (hα : ContMDiffOn 𝓘(ℝ, ℝ) I 1 α (Icc a b))
    (hmetric : ∀ s ∈ Ioo c d,
      μ * g.inner (α s) (lVelocity (I := I) α s) (lVelocity (I := I) α s) ≤
        (S.base.metric (T - s ^ 2)).inner (α s)
          (lVelocity (I := I) α s) (lVelocity (I := I) α s))
    (hscalar : ∀ s ∈ Ioo a b, -B ≤ S.scalar (T - s ^ 2) (α s))
    (hLag : IntervalIntegrable (lRegularizedLagrangian S T α) volume a b)
    (hseparation : ENNReal.ofReal r ≤ riemannianEDistOf g (α c) (α d)) :
    μ * r ^ 2 / (2 * (b - a)) - 2 * B * v ^ 2 * (b - a) ≤
      lRegularizedAction S T α a b := by
  have hab : a < b := lt_of_le_of_lt hac (hcd.trans_le hdb)
  have hcb : c ≤ b := hcd.le.trans hdb
  have had : a ≤ d := hac.trans hcd.le
  have hi (s t : ℝ) (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) :
      IntervalIntegrable (lRegularizedLagrangian S T α) volume s t :=
    hLag.mono_set (by simpa only [uIcc_of_le hst, uIcc_of_le hab.le] using Icc_subset_Icc has htb)
  have hleft := lRegularizedAction_ge_of_scalar_lower_on_interior S T α ha hac
    (hcb.trans hbv) hB (fun s hs => hscalar s ⟨hs.1, hs.2.trans_le hcb⟩)
    (hi a c le_rfl hac hcb)
  have hmiddle := lRegularizedAction_ge_of_endpoint_separation_of_interior_bounds S T α
    (ha.trans hac) hcd (hdb.trans hbv) hμ hB hr g (hα.mono (Icc_subset_Icc hac hdb))
    hmetric (fun s hs => hscalar s ⟨lt_of_le_of_lt hac hs.1, hs.2.trans_le hdb⟩)
    (hi c d hac hcd.le hdb) hseparation
  have hright := lRegularizedAction_ge_of_scalar_lower_on_interior S T α (ha.trans had)
    hdb hbv hB (fun s hs => hscalar s ⟨lt_of_le_of_lt had hs.1, hs.2⟩)
    (hi d b had hdb le_rfl)
  have hadd₁ := lRegularizedAction_add S T α a c d
    (hi a c le_rfl hac hcb) (hi c d hac hcd.le hdb)
  have hadd₂ := lRegularizedAction_add S T α a d b
    (hi a d le_rfl had hdb) (hi d b had hdb le_rfl)
  have hratio : μ * r ^ 2 / (2 * (b - a)) ≤ μ * r ^ 2 / (2 * (d - c)) :=
    div_le_div_of_nonneg_left (mul_nonneg hμ (sq_nonneg r))
      (by linarith) (by linarith)
  nlinarith

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem lRegularizedAction_ge_of_leaves_closed_set
    (S : SolutionOn (I := I) (M := M) D) (T : ℝ) (α : ℝ → M)
    {a b v μ B r : ℝ} (ha : 0 ≤ a) (hbv : b ≤ v)
    (hμ : 0 ≤ μ) (hB : 0 ≤ B) (hr : 0 ≤ r)
    (g : SmoothRiemannianMetric I M) {K : Set M} (hK : IsClosed K)
    (hα : ContMDiffOn 𝓘(ℝ, ℝ) I 1 α (Icc a b))
    (hstart : α a ∈ interior K)
    (hmetric : ∀ s ∈ Ioo a b, α s ∈ K →
      μ * g.inner (α s) (lVelocity (I := I) α s) (lVelocity (I := I) α s) ≤
        (S.base.metric (T - s ^ 2)).inner (α s)
          (lVelocity (I := I) α s) (lVelocity (I := I) α s))
    (hscalar : ∀ s ∈ Ioo a b, -B ≤ S.scalar (T - s ^ 2) (α s))
    (hLag : IntervalIntegrable (lRegularizedLagrangian S T α) volume a b)
    (hfront : ∀ y ∈ frontier K, ENNReal.ofReal r ≤ riemannianEDistOf g (α a) y)
    (hexit : ¬ MapsTo α (Icc a b) K) :
    μ * r ^ 2 / (2 * (b - a)) - 2 * B * v ^ 2 * (b - a) ≤
      lRegularizedAction S T α a b := by
  obtain ⟨t, ht, hstay, htfront⟩ :=
    exists_first_exit_frontier_Icc_of_not_mapsTo hK hα.continuousOn hstart hexit
  apply lRegularizedAction_ge_of_subinterval_separation S T α ha le_rfl ht.1 ht.2.le
    hbv hμ hB hr g hα ?_ hscalar hLag (hfront _ htfront)
  intro s hs
  exact hmetric s ⟨hs.1, hs.2.trans_le ht.2.le⟩ (hstay ⟨hs.1.le, hs.2.le⟩)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem lRegularizedAction_ge_of_enters_closed_set
    (S : SolutionOn (I := I) (M := M) D) (T : ℝ) (α : ℝ → M)
    {a b v μ B r : ℝ} (ha : 0 ≤ a) (hbv : b ≤ v)
    (hμ : 0 ≤ μ) (hB : 0 ≤ B) (hr : 0 ≤ r)
    (g : SmoothRiemannianMetric I M) {K : Set M} (hK : IsClosed K)
    (hα : ContMDiffOn 𝓘(ℝ, ℝ) I 1 α (Icc a b))
    (hend : α b ∈ interior K)
    (hmetric : ∀ s ∈ Ioo a b, α s ∈ K →
      μ * g.inner (α s) (lVelocity (I := I) α s) (lVelocity (I := I) α s) ≤
        (S.base.metric (T - s ^ 2)).inner (α s)
          (lVelocity (I := I) α s) (lVelocity (I := I) α s))
    (hscalar : ∀ s ∈ Ioo a b, -B ≤ S.scalar (T - s ^ 2) (α s))
    (hLag : IntervalIntegrable (lRegularizedLagrangian S T α) volume a b)
    (hfront : ∀ y ∈ frontier K, ENNReal.ofReal r ≤ riemannianEDistOf g y (α b))
    (hexit : ¬ MapsTo α (Icc a b) K) :
    μ * r ^ 2 / (2 * (b - a)) - 2 * B * v ^ 2 * (b - a) ≤
      lRegularizedAction S T α a b := by
  obtain ⟨t, ht, hstay, htfront⟩ :=
    exists_last_entry_frontier_Icc_of_not_mapsTo hK hα.continuousOn hend hexit
  apply lRegularizedAction_ge_of_subinterval_separation S T α ha ht.1.le ht.2 le_rfl
    hbv hμ hB hr g hα ?_ hscalar hLag (hfront _ htfront)
  intro s hs
  exact hmetric s ⟨lt_of_le_of_lt ht.1.le hs.1, hs.2⟩ (hstay ⟨hs.1.le, hs.2.le⟩)

end DifferentialGeometry.PDE.RicciFlow.Perelman
