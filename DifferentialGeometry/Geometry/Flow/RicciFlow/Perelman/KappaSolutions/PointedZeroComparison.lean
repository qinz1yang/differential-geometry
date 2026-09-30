import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedMetricErrorJets
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedUniformMetricTime
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornGeometry


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter Set DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open scoped _root_.Manifold ContDiff _root_.Topology BigOperators

section Quadratic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M]

private local instance zeroComparisonC1 : IsManifold I 1 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)


theorem metric_error_norm_le_of_quadratic_control
    (g h : SmoothRiemannianMetric I M) (x : M) {δ : ℝ} (hδ : 0 ≤ δ)
    (hquad : ∀ v : TangentSpace I x,
      |g.inner x v v - h.inner x v v| ≤ δ * h.inner x v v) :
    tensor02CovDerivNormWith (I := I) 0 (metricTensorField g - metricTensorField h) h h x ≤
      4 * (Module.finrank ℝ (TangentSpace I x) : ℝ) * δ := by
  classical
  obtain ⟨basis, hON⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis (I := I) h x
  have hinv : MetricInverseInBasis (I := I) h x basis
      (identityInvMetric (Idx := Fin (Module.finrank ℝ (TangentSpace I x)))) := by
    have hi := metricInverseInBasis_of_orthonormal (I := I) h basis hON
    intro i j
    simpa [identityInvMetric, diagonalInvMetric] using hi i j
  let T : Tensor0SSpace 2 I x := metricTensorField g x - metricTensorField h x
  have hcomp (slots : Fin 2 → Fin (Module.finrank ℝ (TangentSpace I x))) :
      |component0S (I := I) basis T slots| ≤ 4 * δ := by
    have h := metricDifference_comp_le g h (C := δ + 1) (by linarith) x basis hON
      (fun v => by simpa only [add_sub_cancel_right] using hquad v) (slots 0) (slots 1)
    simpa only [T, component0S_apply, Tensor0SSpace.sub_apply, metricTensorField_apply,
      add_sub_cancel_right] using h
  have hbound := normSq0S_le_card_of_component_bound (I := I) h x 2 basis hinv T
    (4 * δ) (by positivity) hcomp
  have hcard : (Fintype.card (Fin 2 → Fin (Module.finrank ℝ (TangentSpace I x))) : ℝ) =
      (Module.finrank ℝ (TangentSpace I x) : ℝ) ^ 2 := by simp
  rw [hcard] at hbound
  change Real.sqrt (normSq0S (I := I) h x 2 T) ≤ _
  calc
    Real.sqrt (normSq0S (I := I) h x 2 T) ≤
        Real.sqrt ((Module.finrank ℝ (TangentSpace I x) : ℝ) ^ 2 * (4 * δ) ^ 2) :=
      Real.sqrt_le_sqrt hbound
    _ = 4 * (Module.finrank ℝ (TangentSpace I x) : ℝ) * δ := by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Nat.cast_nonneg _),
        Real.sqrt_sq (by positivity : 0 ≤ 4 * δ)]
      ring

end Quadratic

section Pointed

open CanonicalNeighborhood CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

private local instance zeroComparisonFlowC1 {D : RealTimeInterval}
    (F : PointedFlowData.{u, 0, 0} (I := I3) D) : IsManifold I3 1 F.M :=
  IsManifold.of_le (I := I3) (M := F.M) (n := ∞) (by decide)


theorem eventually_pointed_zero_order_comparison
    {X : PointedFlowSeq.{u, 0, 0} (I := I3)}
    {L : PointedFlowData.{u, 0, 0} (I := I3) X.D} {phi : ℕ → ℕ}
    (Phi : PointedCGHMaps (I := I3) X (L.atTime (I := I3) 0) phi)
    {kappa : ℝ} (hsource : ∀ i, KLim (I := I3) kappa (X.term i))
    (hlimit : KLim (I := I3) kappa L)
    {a b : ℝ} (hab : a ≤ b) (hb : b ≤ 0) (K : Set L.M) (hK : IsCompact K)
    (hconv : ∀ t ∈ Icc a 0,
      ∃ C : MetricConvergenceData (I := I3) (Phi.atTime (L := L) t),
        ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData
          (I := I3) (Phi.atTime (L := L) t) k)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ i in atTop, Nonempty (MetricComparisonOn
      (fun s => L.S.base.metric s) (fun s => (X.term (phi i)).S.base.metric s)
      (Phi.map i) K (Icc a b) 0 ε) := by
  classical
  obtain ⟨G, J, hJzero, hJderiv, hG⟩ := exists_pointed_metric_error_time_jets
    Phi hlimit.carrier_eq hlimit.regular_eq
  let δ : ℝ := ε / 13
  have hδ : 0 < δ := div_pos hε (by norm_num)
  have hδε : δ ≤ ε := by dsimp only [δ]; linarith
  have hsmall : 12 * δ ≤ ε := by dsimp only [δ]; linarith
  filter_upwards [pointed_metric_quadratic_uniform_on_closed_time Phi hsource
    (hab.trans hb) K hK hconv δ hδ, hG K hK] with i hi hGi
  obtain ⟨U, _hU, hKU, _hUsource, hpair⟩ := hGi
  have hquadratic (t : ℝ) (ht : t ∈ Icc a b) (x : L.M) (hx : x ∈ K)
      (v : TangentSpace I3 x) :
      |(G i t).inner x v v - (L.S.base.metric t).inner x v v| ≤
        δ * (L.S.base.metric t).inner x v v := by
    rw [hpair t x (hKU hx) v v]
    exact (hi.2 t ⟨ht.1, ht.2.trans hb⟩ x hx v).trans
      (mul_le_mul_of_nonneg_left (hlimit.metric_inner_le (ht.2.trans hb) le_rfl x v) hδ.le)
  have hzeroBound (t : ℝ) (ht : t ∈ Icc a b) (x : L.M) (hx : x ∈ K) :
      tensor02CovDerivNormWith (I := I3) 0 (J i 0 t)
        (L.S.base.metric t) (L.S.base.metric t) x ≤ ε := by
    rw [hJzero i t]
    have h := metric_error_norm_le_of_quadratic_control (G i t) (L.S.base.metric t) x
      hδ.le (hquadratic t ht x hx)
    have hdim : Module.finrank ℝ (TangentSpace I3 x) = 3 := by
      change Module.finrank ℝ ThreeSpace = 3
      simp [ThreeSpace]
    rw [hdim] at h
    norm_num only [Nat.cast_ofNat] at h
    exact h.trans hsmall
  let jet : ℕ → ℝ → Tensor0SField (I := I3) (M := L.M) (n := ∞) 2 :=
    fun q t => if a = b ∧ q ≠ 0 then 0 else J i q t
  have hjzero (t : ℝ) : jet 0 t = J i 0 t := by simp only [jet, ne_eq, not_true_eq_false,
    and_false, ↓reduceIte]
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
        simp only [jet, ite_eq_left htest]
        rfl
      rw [hz]
      symm
      apply derivWithin_zero_of_not_accPt
      rw [← heq, Icc_self, accPt_iff_clusterPt, inf_principal]
      simp [ClusterPt]
    · have hab' : a < b := lt_of_le_of_ne hab heq
      have hjet (r : ℕ) (s : ℝ) : jet r s = J i r s := by simp only [jet, heq,
        false_and, ↓reduceIte]
      simp only [hjet]
      exact tensor_time_tower_derivWithin_Icc (J i) (hJderiv i) hab' hb q t ht x v
  · intro t ht x hx v
    have h := abs_le.mp (hquadratic t ht x hx v)
    have hnn : 0 ≤ (L.S.base.metric t).inner x v v := by
      by_cases hv : v = 0
      · subst v; simp
      · exact ((L.S.base.metric t).pos x v hv).le
    change (1 - ε) * (L.S.base.metric t).inner x v v ≤ (G i t).inner x v v ∧
      (G i t).inner x v v ≤ (1 + ε) * (L.S.base.metric t).inner x v v
    constructor <;> nlinarith [mul_le_mul_of_nonneg_right hδε hnn]
  · intro p q hpq t ht x hx
    have hp : p = 0 := by omega
    have hq : q = 0 := by omega
    subst p
    subst q
    rw [hjzero t]
    exact hzeroBound t ht x hx

end Pointed

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
