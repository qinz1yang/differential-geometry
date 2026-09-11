import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedIntrinsicTimeJets
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedZeroComparison


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter Set DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff _root_.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

private local instance mixedComparisonC1 {D : RealTimeInterval}
    (F : PointedFlowData.{u, 0, 0} (I := I3) D) : IsManifold I3 1 F.M :=
  IsManifold.of_le (I := I3) (M := F.M) (n := ∞) (by decide)

private theorem tensor02_covariant_norm_zero
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold I3 ∞ M] [T2Space M]
    (g : SmoothRiemannianMetric I3 M) (a : ℕ) (x : M) :
    tensor02CovDerivNormWith (I := I3) a 0 g g x = 0 := by
  rw [tensor02CovDerivNormWith, tensor02_cov_deriv_eq_cov_deriv_of_field, covDerivOfField_zero_tensor]
  simp only [ContMDiffSection.coe_zero, Pi.zero_apply, normSq0S, inner0S,
    MetricFiberData.inner, map_zero, Real.sqrt_zero]


theorem eventually_pointed_mixed_comparison
    {X : PointedFlowSeq.{u, 0, 0} (I := I3)}
    {L : PointedFlowData.{u, 0, 0} (I := I3) X.D} {phi : ℕ → ℕ}
    (Phi : PointedCGHMaps (I := I3) X (L.atTime (I := I3) 0) phi)
    {κ : ℝ} (hsource : ∀ i, KLim (I := I3) κ (X.term i))
    (hnormalized : ∀ i, (X.term i).S.scalar 0 (X.term i).basepoint = 1)
    (hlimit : KLim (I := I3) κ L)
    (hconv : ∀ t : ℝ, t ≤ 0 →
      ∃ C : MetricConvergenceData (I := I3) (Phi.atTime (L := L) t),
        ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData
          (I := I3) (Phi.atTime (L := L) t) k)
    {a b : ℝ} (hab : a ≤ b) (hb : b ≤ 0) (K : Set L.M) (hK : IsCompact K)
    (order : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ i in atTop, Nonempty (MetricComparisonOn
      (fun s => L.S.base.metric s) (fun s => (X.term (phi i)).S.base.metric s)
      (Phi.map i) K (Icc a b) order ε) := by
  classical
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  obtain ⟨G, J, hJzero, hJderiv, hG, hbound⟩ :=
    exists_pointed_uniform_error_jets hdim Phi hsource hnormalized hlimit hconv
  let c : ℝ := min a (-1)
  have hc : c < 0 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have htimes : Icc a b ⊆ Icc c 0 := fun _ ht =>
    ⟨(min_le_left _ _).trans ht.1, ht.2.trans hb⟩
  have hclose : ∀ᶠ i in atTop, ∀ p q : Fin (order + 1), ∀ t ∈ Icc c 0, ∀ x ∈ K,
      tensor02CovDerivNormWith (I := I3) (p : ℕ) (J i (q : ℕ) t)
        (L.S.base.metric t) (L.S.base.metric t) x ≤ ε := by
    rw [Filter.eventually_all]
    intro p
    rw [Filter.eventually_all]
    intro q
    exact eventually_atTop.2 (hbound c hc K hK p q ε hε)
  filter_upwards [hclose, pointed_metric_quadratic_uniform_on_closed_time Phi hsource
    (hab.trans hb) K hK (fun t ht => hconv t ht.2) ε hε, hG K hK] with i hi hmetric hGi
  obtain ⟨U, _hU, hKU, _hUsource, hpair⟩ := hGi
  have hquadratic (t : ℝ) (ht : t ∈ Icc a b) (x : L.M) (hx : x ∈ K)
      (v : TangentSpace I3 x) :
      |(G i t).inner x v v - (L.S.base.metric t).inner x v v| ≤
        ε * (L.S.base.metric t).inner x v v := by
    rw [hpair t x (hKU hx) v v]
    exact (hmetric.2 t ⟨ht.1, ht.2.trans hb⟩ x hx v).trans
      (mul_le_mul_of_nonneg_left (hlimit.metric_inner_le (ht.2.trans hb) le_rfl x v) hε.le)
  let jet : ℕ → ℝ → Tensor0SField (I := I3) (M := L.M) (n := ∞) 2 :=
    fun q t => if a = b ∧ q ≠ 0 then 0 else J i q t
  have hjzero (t : ℝ) : jet 0 t = J i 0 t := by
    simp only [jet, ne_eq, not_true_eq_false, and_false, ↓reduceIte]
  refine ⟨{
    pullback := fun t => metricTensorField (G i t)
    pullback_eq := ?_
    jet := jet
    jet_zero := ?_
    jet_succ := ?_
    equivalence := ?_
    close := ?_ }⟩
  · intro t x hx v
    exact (metricTensorField_apply (G i t) x v).trans
      (hpair t x (hKU hx) (v 0) (v 1))
  · intro t x v
    rw [hjzero t, hJzero i t]
    rfl
  · intro q t ht x _hx v
    by_cases heq : a = b
    · have htEq : t = a := by rw [← heq] at ht; exact le_antisymm ht.2 ht.1
      subst t
      have hz : jet (q + 1) a x v = 0 := by
        have htest : a = b ∧ q + 1 ≠ 0 := ⟨heq, Nat.add_one_ne_zero q⟩
        simp only [jet, if_pos htest]
        rfl
      rw [hz]
      symm
      apply derivWithin_zero_of_not_accPt
      rw [← heq, Icc_self, accPt_iff_clusterPt, inf_principal]
      simp [ClusterPt]
    · have hab' : a < b := lt_of_le_of_ne hab heq
      have hjet (r : ℕ) (s : ℝ) : jet r s = J i r s := by
        simp only [jet, heq, false_and, ↓reduceIte]
      simp only [hjet]
      exact tensor_time_tower_derivWithin_Icc (J i) (hJderiv i) hab' hb q t ht x v
  · intro t ht x hx v
    have h := abs_le.mp (hquadratic t ht x hx v)
    change (1 - ε) * (L.S.base.metric t).inner x v v ≤ (G i t).inner x v v ∧
      (G i t).inner x v v ≤ (1 + ε) * (L.S.base.metric t).inner x v v
    constructor <;> nlinarith
  · intro p q hpq t ht x hx
    by_cases htest : a = b ∧ q ≠ 0
    · simp only [jet, if_pos htest, tensor02_covariant_norm_zero]
      exact hε.le
    · simp only [jet, if_neg htest]
      exact hi ⟨p, by omega⟩ ⟨q, by omega⟩ t (htimes ht) x hx

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
