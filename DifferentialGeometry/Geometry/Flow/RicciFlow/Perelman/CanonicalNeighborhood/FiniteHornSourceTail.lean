import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornStructure
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalParabolicScalarComparison
import DifferentialGeometry.Geometry.Geodesic.Ray
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas


open Set

set_option autoImplicit false

private theorem exists_last_eq_of_continuousOn
    {f : ℝ → ℝ} {a b q : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn f (Icc a b))
    (haq : f a ≤ q) (hqb : q ≤ f b) :
    ∃ c ∈ Icc a b, f c = q ∧ ∀ s ∈ Icc c b, q ≤ f s := by
  obtain ⟨c₀, hc₀, hfc₀⟩ := (intermediate_value_Icc hab hcont) ⟨haq, hqb⟩
  let A : Set ℝ := Icc a b ∩ f ⁻¹' ({q} : Set ℝ)
  have hAne : A.Nonempty := by
    refine ⟨c₀, ?_⟩
    exact ⟨hc₀, Set.mem_singleton_iff.mpr hfc₀⟩
  have hAcl : IsClosed A := by
    simpa only [A] using
      hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hAcomp : IsCompact A :=
    IsCompact.of_isClosed_subset isCompact_Icc hAcl inter_subset_left
  obtain ⟨c, hcA, hmax⟩ := hAcomp.exists_isMaxOn hAne continuousOn_id
  have hfc : f c = q := Set.mem_singleton_iff.mp hcA.2
  refine ⟨c, ?_, hfc, ?_⟩
  · exact hcA.1
  intro s hs
  by_contra hnot
  have hfs : f s < q := lt_of_not_ge hnot
  have hsub : Icc s b ⊆ Icc a b := by
    intro x hx
    exact ⟨le_trans hcA.1.1 (le_trans hs.1 hx.1), hx.2⟩
  have hqmem : q ∈ Icc (f s) (f b) := ⟨hfs.le, hqb⟩
  obtain ⟨t, ht, hft⟩ := (intermediate_value_Icc hs.2 (hcont.mono hsub)) hqmem
  have htA : t ∈ A := by
    exact ⟨hsub ht, Set.mem_singleton_iff.mpr hft⟩
  have htc : t ≤ c := isMaxOn_iff.mp hmax t htA
  have hts : s ≤ t := ht.1
  have hts' : t ≤ s := htc.trans hs.1
  have hEq : t = s := le_antisymm hts' hts
  subst t
  exact hfs.ne hft

set_option autoImplicit false

noncomputable section

open Filter Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open Geometry.Curvature
open CheegerGromovCompactness
open Geometry.Riemannian.HopfRinow
open Bundle
open Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_source_metric_segment
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) (i : ℕ)
    (q : (X.term i).M) (hq : (X.term i).basepoint ≠ q) :
    let g := (X.term i).S.base.metric 0
    let L := metricDistance g (X.term i).basepoint q
    ∃ gamma : ℝ → (X.term i).M,
      gamma 0 = (X.term i).basepoint ∧ gamma L = q ∧
      ContinuousOn gamma (Icc 0 L) ∧
      ∀ s ∈ Icc 0 L, ∀ t ∈ Icc 0 L,
        metricDistance g (gamma s) (gamma t) = |s - t| := by
  let g := (X.term i).S.base.metric 0
  let Y := (X.term i).atTime 0
  let rb : Bundle.RiemannianBundle (fun x : (X.term i).M => TangentSpace I3 x) := Y.riemBundle
  let rc : IsContinuousRiemannianBundle ThreeSpace (fun x : (X.term i).M => TangentSpace I3 x) := Y.riemBundle_cont
  let : TopologicalSpace.MetrizableSpace (X.term i).M := Manifold.metrizableSpace I3 (X.term i).M
  let : T3Space (X.term i).M := inferInstance
  let : ConnectedSpace (X.term i).M := X.connected i
  let : RiemannianBundle (fun x : (X.term i).M => TangentSpace I3 x) := rb
  let : IsContinuousRiemannianBundle ThreeSpace (fun x : (X.term i).M => TangentSpace I3 x) := rc
  let : EMetricSpace (X.term i).M := Y.emetricSpace
  let : CompleteSpace (X.term i).M := by
    have htime : (0 : ℝ) ∈ (X.interval i).carrier := by
      rw [X.carrier_eq]
      exact ⟨by linarith [X.depth_pos i], le_rfl⟩
    exact X.complete i 0 htime
  let : MetricSpace (X.term i).M := riemMetricSpace (I := I3)
  have hEnorm : Geometry.Riemannian.IsMetricNorm (I := I3) g :=
    Geometry.Riemannian.isMetricNorm_of_riemannianBundle g
  have hdist (x y : (X.term i).M) : dist x y = metricDistance g x y := by
    change dist x y = (riemannianEDistOf (I := I3) g x y).toReal
    rw [DifferentialGeometry.riemannianEDistOf_eq_riemannianEDist g hEnorm]
    exact riemMetric_dist_eq (I := I3) x y
  have : IsRiemannianManifold I3 (X.term i).M := by
    refine ⟨fun x y => ?_⟩
    rfl
  obtain ⟨gamma, hisom, hzero, hend, _, _⟩ :=
    Geometry.exists_unitSpeed_minimizing_riemannian_geodesic g hEnorm (X.term i).basepoint q hq
  dsimp only
  refine ⟨gamma, hzero, ?_, ?_, ?_⟩
  · simpa only [hdist] using hend
  · have hc := continuousOn_iff_continuous_domRestrict.mpr hisom.continuous
    simpa only [hdist] using hc
  · intro s hs t ht
    have hs' : s ∈ Icc 0 (dist (X.term i).basepoint q) := by simpa only [hdist] using hs
    have ht' : t ∈ Icc 0 (dist (X.term i).basepoint q) := by simpa only [hdist] using ht
    have h := hisom.dist_eq (⟨s, hs'⟩ : Icc 0 (dist (X.term i).basepoint q)) ⟨t, ht'⟩
    simpa only [hdist, Subtype.dist_eq, Real.dist_eq] using h

theorem exists_source_high_scalar_segment
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) (i : ℕ)
    (q : (X.term i).M) (hq : 2 < (X.term i).S.scalar 0 q) :
    let g := (X.term i).S.base.metric 0
    let L := metricDistance g (X.term i).basepoint q
    ∃ (gamma : ℝ → (X.term i).M) (a : ℝ),
      gamma 0 = (X.term i).basepoint ∧ gamma L = q ∧
      ContinuousOn gamma (Icc 0 L) ∧
      (∀ s ∈ Icc 0 L, ∀ t ∈ Icc 0 L,
        metricDistance g (gamma s) (gamma t) = |s - t|) ∧
      a ∈ Icc 0 L ∧ (X.term i).S.scalar 0 (gamma a) = 2 ∧
      ∀ s ∈ Icc a L, 2 ≤ (X.term i).S.scalar 0 (gamma s) := by
  have hbase : (X.term i).S.scalar 0 (X.term i).basepoint = 1 := X.base_one i
  have hne : (X.term i).basepoint ≠ q := by
    intro heq
    rw [heq] at hbase
    linarith
  obtain ⟨gamma, hzero, hend, hcont, hdist⟩ := exists_source_metric_segment X i q hne
  let g := (X.term i).S.base.metric 0
  let L := metricDistance g (X.term i).basepoint q
  have hL : 0 ≤ L := ENNReal.toReal_nonneg
  have hc : ContinuousOn (fun s => (X.term i).S.scalar 0 (gamma s)) (Icc 0 L) := by
    have hscalar : Continuous (fun x => (X.term i).S.scalar 0 x) := (metricScalar_smooth g).continuous
    exact hscalar.comp_continuousOn hcont
  obtain ⟨a, ha, heq, hhigh⟩ := exists_last_eq_of_continuousOn hL hc
    (show (X.term i).S.scalar 0 (gamma 0) ≤ 2 by rw [hzero, hbase]; norm_num)
    (show 2 ≤ (X.term i).S.scalar 0 (gamma L) by rw [hend]; exact hq.le)
  exact ⟨gamma, a, hzero, hend, hcont, hdist, ha, heq, hhigh⟩


end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

set_option autoImplicit false

noncomputable section

open Filter Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open Geometry.Curvature
open CheegerGromovCompactness
open Surgery.Topology
open Bundle

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_source_tail_endpoint_distance_lower
    {kappa : ℝ} (hmod : ModelCurvatureBoundNearBase.{u, 0, 0} I3 kappa) :
    ∃ epsStar D : ℝ, 0 < epsStar ∧ 0 < D ∧
      ∀ eps : ℝ, 0 < eps → eps ≤ epsStar → ∀ sigma : ℝ, 0 < sigma →
        ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
          ∀ X : NormalizedSequence.{u} eps kappa sigma Phi, ∀ i : ℕ,
          ∀ p q : (X.term i).M,
          (X.term i).S.scalar 0 p = 2 →
          2 * D < (X.term i).S.scalar 0 q →
          1 / Real.sqrt 2 < metricDistance ((X.term i).S.base.metric 0) p q := by
  obtain ⟨epsStar, D, hepsStar, hD, hcmp⟩ :=
    exists_scalar_le_mul_scalar_of_modelCurvatureBound hmod
  refine ⟨epsStar, D, hepsStar, hD, ?_⟩
  intro eps heps hsmall sigma hsigma Phi hPhi X i p q hp hq
  let Y := (X.term i).atTime 0
  let rb : Bundle.RiemannianBundle (fun x : (X.term i).M => TangentSpace I3 x) := Y.riemBundle
  let rc : IsContinuousRiemannianBundle ThreeSpace (fun x : (X.term i).M => TangentSpace I3 x) := Y.riemBundle_cont
  let : RiemannianBundle (fun x : (X.term i).M => TangentSpace I3 x) := rb
  let : IsContinuousRiemannianBundle ThreeSpace (fun x : (X.term i).M => TangentSpace I3 x) := rc
  have htime : (0 : ℝ) ∈ Set.Icc (-X.depth i) 0 :=
    ⟨neg_nonpos.mpr (X.depth_pos i).le, le_rfl⟩
  let _ : ConnectedSpace (X.term i).M := X.connected i
  by_contra hnot
  have hdist : riemannianEDistOf (I := I3) ((X.term i).S.base.metric 0) p q ≤
      ENNReal.ofReal (1 / Real.sqrt ((X.term i).S.scalar 0 p)) := by
    apply (ENNReal.le_ofReal_iff_toReal_le
      (riemannianEDistOf_ne_top (I := I3) ((X.term i).S.base.metric 0) p q)
      (by positivity)).mpr
    simpa only [metricDistance, hp] using le_of_not_gt hnot
  have hp2 : 2 ≤ (X.term i).S.scalar 0 p := by
    rw [hp]
  have hbound := hcmp eps heps hsmall sigma hsigma Phi hPhi X i 0 htime p hp2 q hdist
  rw [hp] at hbound
  linarith

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

set_option autoImplicit false

noncomputable section

open Filter Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open Geometry.Curvature
open CheegerGromovCompactness
open Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_eventually_nontrivial_high_scalar_tail
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hmod : ModelCurvatureBoundNearBase.{u, 0, 0} I3 kappa)
    (heps : 0 < eps) (hsigma : 0 < sigma) (hPhi : AdmissiblePinchingFunction Phi)
    (X : NormalizedSequence.{u} eps kappa sigma Phi)
    (hX : FiniteControlledRadius X) :
    ∃ epsStar D : ℝ, 0 < epsStar ∧ 0 < D ∧
      (eps ≤ epsStar → ∀ᶠ i in atTop,
      ∃ (gamma : ℝ → (X.term i).M) (L a : ℝ),
        0 ≤ a ∧ a ≤ L ∧ gamma 0 = (X.term i).basepoint ∧ gamma L = hX.points i ∧
        (∀ s ∈ Icc 0 L, ∀ t ∈ Icc 0 L,
          metricDistance ((X.term i).S.base.metric 0) (gamma s) (gamma t) = |s - t|) ∧
        (X.term i).S.scalar 0 (gamma a) = 2 ∧
        (∀ s ∈ Icc a L, 2 ≤ (X.term i).S.scalar 0 (gamma s)) ∧
        1 / Real.sqrt 2 < metricDistance ((X.term i).S.base.metric 0) (gamma a) (gamma L)) := by
  obtain ⟨epsStar, D, hepsStar, hD, hcmp⟩ :=
    exists_source_tail_endpoint_distance_lower hmod
  have hcurv : ∀ᶠ i in atTop, max 2 (2 * D) < (X.term i).S.scalar 0 (hX.points i) := by
    exact hX.curvature_limit.eventually_gt_atTop (max 2 (2 * D))
  refine ⟨epsStar, D, hepsStar, hD, ?_⟩
  intro hsmall
  filter_upwards [hcurv] with i hi
  obtain ⟨gamma, a, hzero, hend, hcont, hdist, ha, heq, hhigh⟩ :=
    exists_source_high_scalar_segment X i (hX.points i) (lt_of_le_of_lt (le_max_left _ _) hi)
  have hiD : 2 * D < (X.term i).S.scalar 0 (hX.points i) := lt_of_le_of_lt (le_max_right _ _) hi
  have hsep := hcmp eps heps hsmall sigma hsigma Phi hPhi X i
    (gamma a) (hX.points i) heq hiD
  refine ⟨gamma, metricDistance ((X.term i).S.base.metric 0) (X.term i).basepoint (hX.points i),
    a, ha.1, ha.2, hzero, hend, hdist, heq, hhigh, ?_⟩
  simpa only [hend] using hsep


end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
