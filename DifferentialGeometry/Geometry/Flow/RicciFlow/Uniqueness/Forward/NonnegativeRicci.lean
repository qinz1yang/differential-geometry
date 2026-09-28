import DifferentialGeometry.Geometry.Metric.ModelChange
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.Pullback
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.MetricFirstOrder
import DifferentialGeometry.Geometry.Connection.Convergence.ReferenceBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.Energy.CutoffGrowth
import DifferentialGeometry.Analysis.Calculus.Cutoff.Riemannian
import DifferentialGeometry.Analysis.Integration.Integral.VolumeGrowth
import DifferentialGeometry.Geometry.Metric.TensorInner.Estimates.CotangentNorm

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.TensorMetric
  (metricDiffSq)

open Bundle Set DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open scoped _root_.Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M]

private theorem density_bound (g₁ g₂ : ℝ → SmoothRiemannianMetric I M) (t : ℝ) (x : M)
    {C R₁ R₂ A : ℝ} (hC : 1 ≤ C)
    (heq : ∀ v : TangentSpace I x,
      C⁻¹ * (g₁ t).inner x v v ≤ (g₂ t).inner x v v ∧
        (g₂ t).inner x v v ≤ C * (g₁ t).inner x v v)
    (hR₁ : normSq0S (g₁ t) x 4 (metricRm04At (g₁ t) x) ≤ R₁)
    (hR₂ : normSq0S (g₂ t) x 4 (metricRm04At (g₂ t) x) ≤ R₂)
    (hA : connectionDifferenceSq (g₁ t) (g₂ t) x ≤ A) :
    forwardUniqueDensity g₁ g₂ t x ≤
      2 * (Module.finrank ℝ E : ℝ) + 2 * C ^ 2 * (Module.finrank ℝ E : ℝ) + A +
        2 * R₁ + 2 * (Module.finrank ℝ E : ℝ) ^ 7 * C ^ 6 * R₂ := by
  have hself (g : SmoothRiemannianMetric I M) :
      normSq0S g x 2 (metricTensorField g x) = (Module.finrank ℝ E : ℝ) := by
    obtain ⟨basis, hON⟩ := exists_orthonormal_basis g x
    have hinv := metricInverseInBasis_of_orthonormal g basis hON
    have hfield : metricTensorField g x = metricTensor0S g x := by
      ext v
      rw [metricTensorField_apply, metricTensor0S_apply]
    rw [hfield, normSq0S_metricTensor0S_eq_card g basis _ hinv, Fintype.card_fin]
    rfl
  have hbackground := normSq0S_upper_le_of_equiv (g₂ t) (g₁ t) x 2 hC
    (metric_equiv_symm (g₁ t) (g₂ t) x hC heq) (metricTensorField (g₂ t) x)
  rw [hself] at hbackground
  have hm := _root_.DifferentialGeometry.Tensor0SBundle.normSq0S_sub_le (g₁ t) x 2
    (metricTensorField (g₁ t) x) (metricTensorField (g₂ t) x)
  rw [hself] at hm
  have hcross := (norm_sq_cross_curvature_le (g₁ t) (g₂ t) x hC heq).trans
    (mul_le_mul_of_nonneg_left hR₂ (by positivity))
  have hrm := _root_.DifferentialGeometry.Tensor0SBundle.normSq0S_sub_le (g₁ t) x 4
    (metricRm04At (g₁ t) x)
    (CovariantDerivative.riemannCurvature04At (g₁ t) (metricCov (g₂ t)) (metricCov_smooth (g₂ t)) x)
  change rmDiffSq (g₁ t) (g₂ t) x ≤ _ at hrm
  change metricDiffSq (g₁ t) (g₂ t) x ≤ _ at hm
  dsimp only [forwardUniqueDensity]
  linarith

private theorem connection_sq_bound (g h : SmoothRiemannianMetric I M) (x : M)
    {A : ℝ} (hA : 0 ≤ A)
    (hconn : ∀ u w : TangentSpace I x,
      Real.sqrt (g.inner x
        (CovariantDerivative.difference (metricCov h) (metricCov g) x u w)
        (CovariantDerivative.difference (metricCov h) (metricCov g) x u w)) ≤
      A * Real.sqrt (g.inner x u u) * Real.sqrt (g.inner x w w)) :
    connectionDifferenceSq g h x ≤ (Module.finrank ℝ E : ℝ) ^ 3 * A ^ 2 := by
  classical
  have hswap (u w : TangentSpace I x) :
      CovariantDerivative.difference (metricCov g) (metricCov h) x u w =
        -CovariantDerivative.difference (metricCov h) (metricCov g) x u w := by
    obtain ⟨Y, hY⟩ := ContMDiffSection.exists_eq_at
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x u
    have hpair (g₁ g₂ : SmoothRiemannianMetric I M) :
        CovariantDerivative.difference (metricCov g₁) (metricCov g₂) x u w =
          (metricCov g₁).toFun Y x w - (metricCov g₂).toFun Y x w := by
      simpa only [PDE.DeTurck.connectionDifference, metricCov, LeviCivita, hY] using
        PDE.DeTurck.connectionDifference_apply g₁ g₂ (Y.mdifferentiableAt (x := x)) w
    rw [hpair, hpair]; abel
  obtain ⟨basis, hON⟩ := exists_orthonormal_basis g x
  have hinv := metricInverseInBasis_of_orthonormal g basis hON
  have hcomp (v : Fin 3 → Fin (Module.finrank ℝ (TangentSpace I x))) :
      |component0S basis (connectionDifferenceLowAt g h x) v| ≤ A := by
    rw [component0S_apply]
    change |Tensor0SSpace.eval (connectionDifferenceLowAt g h x) (fun i => basis (v i))| ≤ A
    rw [connectionDifferenceLowAt_apply, hswap, map_neg, neg_apply, abs_neg]
    have hcs := SmoothRiemannianMetric.abs_metric_inner_le_sqrt_metric_quadratic g x
      (CovariantDerivative.difference (metricCov h) (metricCov g) x (basis (v 1)) (basis (v 0)))
      (basis (v 2))
    have hc := hconn (basis (v 1)) (basis (v 0))
    simp only [hON, ite_true, Real.sqrt_one, mul_one] at hc hcs
    exact hcs.trans hc
  have h := normSq0S_le_card_of_component_bound g x 3 basis hinv
    (connectionDifferenceLowAt g h x) A hA hcomp
  simpa only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, connectionDifferenceSq_def,
    show Module.finrank ℝ (TangentSpace I x) = Module.finrank ℝ E from rfl] using h

end DifferentialGeometry.PDE.RicciFlow

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle _root_.Manifold MeasureTheory Set DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Geometry.Connection
open scoped _root_.Manifold ContDiff ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

private theorem forward_unique_of_bounded_density_of_ricci_nonnegative [ConnectedSpace M]
    (g₁ g₂ : ℝ → SmoothRiemannianMetric I M)
    {a b : ℝ}
    (hjoint₁ : ∀ (α : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (g₁ p.1) α p.2 i j)
        (Ico a b ×ˢ (trivializationAt E (TangentSpace I) α).baseSet))
    (hjoint₂ : ∀ (α : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (g₂ p.1) α p.2 i j)
        (Ico a b ×ˢ (trivializationAt E (TangentSpace I) α).baseSet))
    (hpde₁ : ∀ t ∈ Ico a b, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun s => (g₁ s).inner x v w)
        ((-2 : ℝ) * ricciTensor (I := I) (g₁ t) x v w) (Ici a) t)
    (hpde₂ : ∀ t ∈ Ico a b, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun s => (g₂ s).inner x v w)
        ((-2 : ℝ) * ricciTensor (I := I) (g₂ t) x v w) (Ici a) t)
    {C R₁ R₂ D₁ D₂ : ℝ} (hC : 1 ≤ C)
    (hEquiv : ∀ t ∈ Ico a b, ∀ x : M, ∀ v : TangentSpace I x,
      C⁻¹ * (g₁ t).inner x v v ≤ (g₂ t).inner x v v ∧
        (g₂ t).inner x v v ≤ C * (g₁ t).inner x v v)
    (hR₁ : ∀ t ∈ Ico a b, ∀ x : M,
      normSq0S (I := I) (g₁ t) x 4 (metricRm04At (I := I) (g₁ t) x) ≤ R₁)
    (hR₂ : ∀ t ∈ Ico a b, ∀ x : M,
      normSq0S (I := I) (g₂ t) x 4 (metricRm04At (I := I) (g₂ t) x) ≤ R₂)
    (hD₁ : ∀ t ∈ Ico a b, ∀ x : M, normSq0S (I := I) (g₂ t) x 5
      (metricNabla0S (I := I) (g₂ t)
        (CovariantDerivative.rm04Section (I := I) (g₂ t) (metricCov (I := I) (g₂ t))
          (metricCov_smooth (I := I) (g₂ t))) x) ≤ D₁)
    (hD₂ : ∀ t ∈ Ico a b, ∀ x : M, normSq0S (I := I) (g₂ t) x 6
      (metricNabla0S (I := I) (g₂ t) (metricNabla0S (I := I) (g₂ t)
        (CovariantDerivative.rm04Section (I := I) (g₂ t) (metricCov (I := I) (g₂ t))
          (metricCov_smooth (I := I) (g₂ t)))) x) ≤ D₂)
    (hcomplete : RiemannianMetricComplete (g₁ a))
    (hRic : BonnetMyers.RicciBoundedBelow (I := I) (g₁ a) 0)
    {Q : ℝ} (hQ : 1 ≤ Q)
    (hcompare : ∀ t ∈ Ico a b, ∀ x (v : TangentSpace I x),
      Q⁻¹ * (g₁ a).inner x v v ≤ (g₁ t).inner x v v ∧
        (g₁ t).inner x v v ≤ Q * (g₁ a).inner x v v)
    (hbound : ∃ D : ℝ, 0 ≤ D ∧ ∀ t ∈ Ico a b, ∀ x,
      forwardUniqueDensity (I := I) g₁ g₂ t x ≤ D)
    (hinitial : g₁ a = g₂ a) : ∀ t ∈ Ico a b, g₁ t = g₂ t := by
  classical
  obtain ⟨D, hD, hbound⟩ := hbound
  let o : M := Classical.choice (inferInstance : Nonempty M)
  obtain ⟨K, χ, hsupp, hrange, _, hcover, hzero, hderiv⟩ :=
    exists_contMDiff_distance_cutoff_sequence (g₁ a) hcomplete o
  have hQ0 : 0 < Q := zero_lt_one.trans_le hQ
  let n := Module.finrank ℝ E
  let V := D * Real.sqrt (Q ^ n) * VolumeComparison.euclideanUnitBallVolume n * 2 ^ n
  apply forward_unique_of_cutoff_energy_growth g₁ g₂ hjoint₁ hjoint₂ hpde₁ hpde₂
    hC hEquiv hR₁ hR₂ hD₁ hD₂ χ hsupp
    (fun x => (hcover x).imp fun k hk => by rw [hk]; exact one_ne_zero)
    (L := Q * (K : ℝ) ^ 2) (B := V) (R := 4 ^ n) (by positivity) (by positivity)
    _ _ hinitial
  · intro k t ht x
    have hmetric (v : TangentSpace I x) : (g₁ a).inner x v v ≤ Q * (g₁ t).inner x v v := by
      have h := mul_le_mul_of_nonneg_left (hcompare t ht x v).1 hQ0.le
      simpa only [← mul_assoc, mul_inv_cancel₀ hQ0.ne', one_mul] using h
    have hbase : normSq0S (g₁ a) x 1 (differential1FormFun (I := I) (χ k) x) ≤
        ((K : ℝ) * χ (k + 1) x) ^ 2 := by
      apply (normSq0S_one_le_iff (g₁ a) x _ (mul_nonneg K.coe_nonneg (hrange (k + 1) x).1)).mpr
      intro v
      rw [differential1FormFun_apply_eq_mvfderiv]
      exact hderiv k x v
    calc
      _ ≤ Q * normSq0S (g₁ a) x 1 (differential1FormFun (I := I) (χ k) x) :=
        normSq0S_one_le_of_metric_le (g₁ a) (g₁ t) x hQ0.le hmetric _
      _ ≤ Q * ((K : ℝ) * χ (k + 1) x) ^ 2 := mul_le_mul_of_nonneg_left hbase hQ0.le
      _ = _ := by ring
  · intro k t ht
    let r : ℝ := 2 * 4 ^ k
    have hr : 0 < r := by dsimp [r]; positivity
    have hval (x : M) : χ k x ^ 2 * forwardUniqueDensity (I := I) g₁ g₂ t x ∈ Icc 0 D := by
      have hc0 := (hrange k x).1
      have hc1 := (hrange k x).2
      have hc : χ k x ^ 2 ≤ 1 := by nlinarith
      constructor
      · exact mul_nonneg (sq_nonneg _) (density_nonneg g₁ g₂ t x)
      · exact (mul_le_mul_of_nonneg_right hc (density_nonneg g₁ g₂ t x)).trans
          (by simpa only [one_mul] using hbound t ht x)
    have hsupport : Function.support (fun x => χ k x ^ 2 * forwardUniqueDensity (I := I) g₁ g₂ t x) ⊆
        {x | riemannianEDistOf (g₁ a) o x < ENNReal.ofReal r} := by
      intro x hx
      by_contra hn
      have hd := mul_le_mul_right (le_of_not_gt hn) ((1 / 4 : ℝ≥0∞) ^ k)
      have hscale : (1 / 4 : ℝ≥0∞) ^ k * ENNReal.ofReal r = 2 := by
        simp only [r, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
          ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 4), ENNReal.ofReal_ofNat]
        rw [mul_left_comm, ← mul_pow, one_div,
          ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_pow, mul_one]
      rw [hscale] at hd
      have hz := hzero k x hd
      exact hx (by simp only [hz, zero_pow (by decide : 2 ≠ 0), zero_mul])
    have hi := VolumeComparison.integral_le_of_support_subset_ball_of_ricci_nonnegative
      (g₁ a) (g₁ t) hcomplete hRic o hr hQ0 (fun x _ v => (hcompare t ht x v).2)
      hval hsupport
    change (∫ x, χ k x ^ 2 * forwardUniqueDensity (I := I) g₁ g₂ t x
      ∂riemannianMeasureFamily g₁ t) ≤ _ at hi
    apply hi.trans_eq
    dsimp [r, V, n]
    rw [mul_pow, ← pow_mul, Nat.mul_comm k, pow_mul]
    ring

end DifferentialGeometry.PDE.RicciFlow

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Set _root_.Manifold DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Tensor.Coordinates
open scoped _root_.Manifold ContDiff _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]

private theorem forward_unique_on_slab_of_ricci_nonnegative_of_innerProductSpace
    {D : RealTimeInterval} (S₁ S₂ : SolutionOn (I := I) (M := M) D)
    (hS₁ : IsSolutionOn S₁) (hS₂ : IsSolutionOn S₂)
    {a₀ a b : ℝ} (hbuffer : a₀ < a) (hab : a < b)
    (hslab : Icc a₀ b ⊆ D.carrier) (hreg : Ioc a₀ b ⊆ D.regular)
    (hcomplete₁ : RiemannianMetricComplete (S₁.base.metric a₀))
    (hcomplete₂ : RiemannianMetricComplete (S₂.base.metric a₀))
    (hcurv₁ : ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Icc a₀ b, ∀ x,
      normSq0S (S₁.base.metric t) x 4 (S₁.base.rm04 t x) ≤ K)
    (hcurv₂ : ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Icc a₀ b, ∀ x,
      normSq0S (S₂.base.metric t) x 4 (S₂.base.rm04 t x) ≤ K)
    (hRic : BonnetMyers.RicciBoundedBelow (I := I) (S₁.base.metric a) 0)
    (hinitial : S₁.base.metric a = S₂.base.metric a) :
    ∀ t ∈ Icc a b, S₁.base.metric t = S₂.base.metric t := by
  classical
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨K₁, hK₁, hcurv₁⟩ := hcurv₁
  obtain ⟨K₂, hK₂, hcurv₂⟩ := hcurv₂
  obtain ⟨L₁, J₁, hL₁, hJ₁, heq₁, hjet₁⟩ :=
    exists_uniform_metric_first_order_bound_on_slab S₁ hS₁ hbuffer hab hslab hreg hcomplete₁ hK₁ hcurv₁
  obtain ⟨L₂, J₂, hL₂, hJ₂, heq₂, hjet₂⟩ :=
    exists_uniform_metric_first_order_bound_on_slab S₂ hS₂ hbuffer hab hslab hreg hcomplete₂ hK₂ hcurv₂
  rw [← hinitial] at heq₂ hjet₂
  have heq (t : ℝ) (ht : t ∈ Icc a b) :=
    (metricUniformEquivalentOn_symm (heq₁ t ht)).trans (heq₂ t ht)
  have hsub : Icc a b ⊆ Icc a₀ b := fun t ht => ⟨hbuffer.le.trans ht.1, ht.2⟩
  have hregular : Icc a b ⊆ D.regular := fun t ht => hreg ⟨hbuffer.trans_le ht.1, ht.2⟩
  have hcomplete : RiemannianMetricComplete (S₁.base.metric a) :=
    complete_of_ricBound S₁ hS₁ hslab hreg
      (K := (Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt K₁) (by positivity)
      (fun t ht x v => ricci_quadratic_form_bound_of_solution_curvature_bound S₁ x v (hcurv₁ t ht x))
      hcomplete₁ ⟨hbuffer.le, hab.le⟩
  let F : PointedFlowData (I := I) D := {
    M := M
    topology := inferInstance
    charted := inferInstance
    smooth := inferInstance
    sigmaCompact := inferInstance
    t2 := inferInstance
    t2TangentBundle := by infer_instance
    basepoint := Classical.choice (inferInstance : Nonempty M)
    S := S₂
    isSolution := hS₂ }
  have hshi := movingRm_of_bound F hbuffer hab.le hslab hreg hcomplete₂.complete hK₂ hcurv₂ 2
  have hgram (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S) :
      ∀ (α : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (S.base.metric p.1) α p.2 i j)
        (Ico a b ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) := by
    apply chartGramMatrix_joint_contMDiffOn S.family.metric (Ico a b)
    intro p hp
    exact (hS.smoothMetric.metricCLMSmoothAt
      (D.regular_isOpen.mem_nhds (hregular (Ico_subset_Icc_self hp.1)))).contMDiffWithinAt
  have hpde (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
      (t : ℝ) (ht : t ∈ Icc a b) (x : M) (v w : TangentSpace I x) :
      HasDerivAt (fun s => (S.base.metric s).inner x v w)
        (-2 * ricciTensor (S.base.metric t) x v w) t := by
    simpa only [SolutionOn.family_metric, SolutionOn.ricciAt, SolutionFamily.ricciAt,
      metricRicciAt_apply_eq_ricciTensor] using
      metricDerivAt S hS ⟨t, hregular ht⟩ x v w
  let A := Real.sqrt L₁ ^ 3 * (3 / 2 * L₂ ^ 3 * J₂ + 3 / 2 * L₁ ^ 3 * J₁)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  let n : ℝ := Module.finrank ℝ E
  let B := 2 * n + 2 * (L₁ * L₂) ^ 2 * n + n ^ 3 * A ^ 2 +
    2 * K₁ + 2 * n ^ 7 * (L₁ * L₂) ^ 6 * K₂
  have hbound : ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Ico a b, ∀ x,
      forwardUniqueDensity S₁.base.metric S₂.base.metric t x ≤ B := by
    refine ⟨max B 0, le_max_right _ _, fun t ht x => ?_⟩
    have htc := Ico_subset_Icc_self ht
    have hc := connection_sq_bound (S₁.base.metric t) (S₂.base.metric t) x hA
      (connectionDifference_norm_le_of_reference_metric_bounds (S₁.base.metric a)
        (S₁.base.metric t) (S₂.base.metric t) (heq₁ t htc) (heq₂ t htc)
        (hjet₁ t htc) (hjet₂ t htc) (mem_univ x))
    exact (density_bound S₁.base.metric S₂.base.metric t x (heq t htc).1
      (fun v => (heq t htc).2 x (mem_univ x) v)
      (hcurv₁ t (hsub htc) x) (hcurv₂ t (hsub htc) x) hc).trans (le_max_left _ _)
  have hhalf : ∀ t ∈ Ico a b, S₁.base.metric t = S₂.base.metric t := by
    apply forward_unique_of_bounded_density_of_ricci_nonnegative
      S₁.base.metric S₂.base.metric (hgram S₁ hS₁) (hgram S₂ hS₂)
      (fun t ht x v w => (hpde S₁ hS₁ t (Ico_subset_Icc_self ht) x v w).hasDerivWithinAt)
      (fun t ht x v w => (hpde S₂ hS₂ t (Ico_subset_Icc_self ht) x v w).hasDerivWithinAt)
      (C := L₁ * L₂) (heq a ⟨le_rfl, hab.le⟩).1
      (fun t ht x v => (heq t (Ico_subset_Icc_self ht)).2 x (mem_univ x) v)
      (fun t ht x => hcurv₁ t (hsub (Ico_subset_Icc_self ht)) x)
      (fun t ht x => hcurv₂ t (hsub (Ico_subset_Icc_self ht)) x)
      (D₁ := rmOpenBound (Module.finrank ℝ E) K₂ a₀ a b 2 1)
      (D₂ := rmOpenBound (Module.finrank ℝ E) K₂ a₀ a b 2 2)
      _ _ hcomplete hRic hL₁
      (fun t ht x v => (heq₁ t (Ico_subset_Icc_self ht)).2 x (mem_univ x) v)
      hbound hinitial
    · intro t ht x
      exact hshi 1 (by decide) t (Ico_subset_Icc_self ht) x
    · intro t ht x
      exact hshi 2 le_rfl t (Ico_subset_Icc_self ht) x
  intro t ht
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  have he : EqOn (fun s => (S₁.base.metric s).inner x v w)
      (fun s => (S₂.base.metric s).inner x v w) (Ico a b) := by
    intro s hs
    dsimp only
    rw [hhalf s hs]
  apply he.of_subset_closure
    (fun s hs => (hpde S₁ hS₁ s hs x v w).continuousAt.continuousWithinAt)
    (fun s hs => (hpde S₂ hS₂ s hs x v w).continuousAt.continuousWithinAt)
    Ico_subset_Icc_self _ ht
  rw [closure_Ico hab.ne]

end DifferentialGeometry.PDE.RicciFlow

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Set
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.CheegerGromovCompactness
open scoped _root_.Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]

theorem forward_unique_on_slab_of_ricci_nonnegative
    {D : RealTimeInterval} (S₁ S₂ : SolutionOn (I := I) (M := M) D)
    (hS₁ : IsSolutionOn S₁) (hS₂ : IsSolutionOn S₂)
    {a₀ a b : ℝ} (hbuffer : a₀ < a) (hab : a < b)
    (hslab : Icc a₀ b ⊆ D.carrier) (hreg : Ioc a₀ b ⊆ D.regular)
    (hcomplete₁ : RiemannianMetricComplete (S₁.base.metric a₀))
    (hcomplete₂ : RiemannianMetricComplete (S₂.base.metric a₀))
    (hcurv₁ : ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Icc a₀ b, ∀ x,
      normSq0S (S₁.base.metric t) x 4 (S₁.base.rm04 t x) ≤ K)
    (hcurv₂ : ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Icc a₀ b, ∀ x,
      normSq0S (S₂.base.metric t) x 4 (S₂.base.rm04 t x) ≤ K)
    (hRic : BonnetMyers.RicciBoundedBelow (I := I) (S₁.base.metric a) 0)
    (hinitial : S₁.base.metric a = S₂.base.metric a) :
    ∀ t ∈ Icc a b, S₁.base.metric t = S₂.base.metric t := by
  let e : E ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
    (Module.finBasis ℝ E).equivFun.toContinuousLinearEquiv.trans
      (EuclideanSpace.equiv (Fin (Module.finrank ℝ E)) ℝ).symm
  let J := I.transContinuousLinearEquiv e
  let Phi := ContinuousLinearEquiv.toTransContinuousLinearEquiv (n := ∞) I M e
  let U₁ : SolutionOn (I := J) (M := M) D := S₁.pullback Phi.symm
  let U₂ : SolutionOn (I := J) (M := M) D := S₂.pullback Phi.symm
  let _ : NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))) :=
    ⟨by simpa using (NeZero.ne (Module.finrank ℝ E))⟩
  have hcurv (S : SolutionOn (I := I) (M := M) D)
      (h : ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Icc a₀ b, ∀ x,
        normSq0S (S.base.metric t) x 4 (S.base.rm04 t x) ≤ K) :
      ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Icc a₀ b, ∀ x,
        normSq0S ((S.pullback Phi.symm).base.metric t) x 4
          ((S.pullback Phi.symm).base.rm04 t x) ≤ K := by
    obtain ⟨K, hK, h⟩ := h
    refine ⟨K, hK, fun t ht x => ?_⟩
    change normSq0S (Diffeomorph.pullbackMetricCross (S.base.metric t) Phi.symm) x 4
      (metricRm04At (Diffeomorph.pullbackMetricCross (S.base.metric t) Phi.symm) x) ≤ K
    rw [riemannNormSq_cross]
    exact h t ht x
  have hRicU : BonnetMyers.RicciBoundedBelow (U₁.base.metric a) 0 := by
    intro x v
    change 0 * _ ≤ ricciTensor (Diffeomorph.pullbackMetricCross (S₁.base.metric a) Phi.symm) x v v
    rw [zero_mul, ricciTensor_cross]
    simpa only [zero_mul] using hRic (Phi.symm x) (mfderiv J I Phi.symm x v)
  have he := forward_unique_on_slab_of_ricci_nonnegative_of_innerProductSpace
    U₁ U₂ (hS₁.pullback S₁ Phi.symm) (hS₂.pullback S₂ Phi.symm) hbuffer hab hslab hreg
    (RiemannianMetricComplete.pullbackCross _ Phi.symm hcomplete₁)
    (RiemannianMetricComplete.pullbackCross _ Phi.symm hcomplete₂)
    (hcurv S₁ hcurv₁) (hcurv S₂ hcurv₂) hRicU
    (congrArg (fun g => Diffeomorph.pullbackMetricCross g Phi.symm) hinitial)
  intro t ht
  have h := congrArg (fun g => Diffeomorph.pullbackMetricCross g Phi) (he t ht)
  change Diffeomorph.pullbackMetricCross
      (Diffeomorph.pullbackMetricCross (S₁.base.metric t) Phi.symm) Phi =
    Diffeomorph.pullbackMetricCross
      (Diffeomorph.pullbackMetricCross (S₂.base.metric t) Phi.symm) Phi at h
  simpa only [Diffeomorph.pullbackMetricCross_trans, Diffeomorph.self_trans_symm,
    Diffeomorph.pullbackMetricCross_refl] using h

end DifferentialGeometry.PDE.RicciFlow
