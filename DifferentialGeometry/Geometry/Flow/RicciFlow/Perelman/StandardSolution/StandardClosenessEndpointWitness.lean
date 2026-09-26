import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardFamilyCompactness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardWindowShiftConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedWitnessStrictRestriction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedWitnessEndpointPerturbation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.HighCurvatureModels
import DifferentialGeometry.Geometry.Curvature.Bounds.ScalarNorm
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardCurvatureControl
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardMetricControl
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.UniformLifetime
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SelectedCountersequenceAdapter
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.Distance
import DifferentialGeometry.Geometry.Metric.Comparison.PartialDiffeomorphDistance
import DifferentialGeometry.Geometry.Metric.Comparison.DistanceScaling

set_option autoImplicit false
noncomputable section
open Set Filter
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.PDE.RicciFlow

private local instance windowSigmaCompact (V : TopologicalSpace.Opens ThreeSpace) :
    SigmaCompactSpace V :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen (𝓡 3) V.isOpen)

section Orientation

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]

private def negOrientation (o : TangentOrientationSection M) : TangentOrientationSection M where
  orientation x := -o.orientation x
  locally_constant p x hx := by
    obtain ⟨U, hU, hxU, hsub, h⟩ := o.locally_constant p x hx
    exact ⟨U, hU, hxU, hsub, fun y hy => by simp only [Orientation.map_neg, h y hy]⟩

private theorem isOpen_setOf_orientation_eq (o₁ o₂ : TangentOrientationSection M) :
    IsOpen {x | o₁.orientation x = o₂.orientation x} := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  have hb : x ∈ (trivializationAt ThreeSpace (TangentSpace ThreeModel) x).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt ThreeSpace (TangentSpace ThreeModel) x
  obtain ⟨U₁, hU₁, hx₁, hs₁, h₁⟩ := o₁.locally_constant x x hb
  obtain ⟨U₂, hU₂, hx₂, hs₂, h₂⟩ := o₂.locally_constant x x hb
  refine ⟨U₁ ∩ U₂, fun y hy => ?_, hU₁.inter hU₂, hx₁, hx₂⟩
  apply (Orientation.map (Fin 3) (Surgery.Topology.tangentChartEquiv M x y (hs₁ hy.1))).injective
  have hx' : o₁.orientation x = o₂.orientation x := hx
  rw [h₁ y hy.1, hx']
  exact (h₂ y hy.2).symm

private theorem orientation_eq_or_eq_neg [PreconnectedSpace M]
    (o₁ o₂ : TangentOrientationSection M) :
    (∀ x, o₁.orientation x = o₂.orientation x) ∨
      ∀ x, o₁.orientation x = -o₂.orientation x := by
  have hA := isOpen_setOf_orientation_eq o₁ o₂
  have hB := isOpen_setOf_orientation_eq o₁ (negOrientation o₂)
  have hcompl : {x | o₁.orientation x = o₂.orientation x}ᶜ =
      {x | o₁.orientation x = (negOrientation o₂).orientation x} := by
    ext x
    rw [mem_compl_iff]
    change ¬ o₁.orientation x = o₂.orientation x ↔ o₁.orientation x = -o₂.orientation x
    constructor
    · intro hne
      exact (Orientation.eq_or_eq_neg (o₁.orientation x) (o₂.orientation x)
        (by rw [Fintype.card_fin]; exact finrank_euclideanSpace_fin.symm)).resolve_left hne
    · intro hneg heq
      exact Module.Ray.ne_neg_self (o₂.orientation x) (heq.symm.trans hneg)
  have hclopen : IsClopen {x | o₁.orientation x = o₂.orientation x} :=
    ⟨by rw [← isOpen_compl_iff, hcompl]; exact hB, hA⟩
  rcases isClopen_iff.mp hclopen with h | h
  · right
    intro x
    have hx : x ∈ {x | o₁.orientation x = o₂.orientation x}ᶜ := by rw [h]; exact notMem_empty x
    rw [hcompl] at hx
    exact hx
  · left
    intro x
    have hx : x ∈ {x | o₁.orientation x = o₂.orientation x} := by rw [h]; exact mem_univ x
    exact hx

variable {N : Type*} [TopologicalSpace N] [ChartedSpace ThreeSpace N] [IsManifold ThreeModel ∞ N]

private theorem exists_preserves_of_preconnected [PreconnectedSpace M]
    (o₀ o : TangentOrientationSection M) (oN : TangentOrientationSection N) (f : N → M)
    (s : Set N) (h : ∀ y ∈ s, ∃ hf : Function.Bijective (mfderiv ThreeModel ThreeModel f y),
      PreservesTangentOrientationAt oN o₀ f y hf) :
    ∃ oN' : TangentOrientationSection N, ∀ y ∈ s,
      ∃ hf : Function.Bijective (mfderiv ThreeModel ThreeModel f y),
        PreservesTangentOrientationAt oN' o f y hf := by
  rcases orientation_eq_or_eq_neg o o₀ with ho | ho
  · refine ⟨oN, fun y hy => ?_⟩
    obtain ⟨hf, hp⟩ := h y hy
    refine ⟨hf, ?_⟩
    unfold PreservesTangentOrientationAt at hp ⊢
    rw [ho]
    exact hp
  · refine ⟨negOrientation oN, fun y hy => ?_⟩
    obtain ⟨hf, hp⟩ := h y hy
    refine ⟨hf, ?_⟩
    unfold PreservesTangentOrientationAt at hp ⊢
    change Orientation.map (Fin 3) _ (-oN.orientation y) = o.orientation (f y)
    rw [ho, Orientation.map_neg, hp]

end Orientation

section WitnessGeometry

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}

omit [T2Space M] in
private theorem edist_embedding_le_of_lt_modelRadius {eps kappa : ℝ} {x : M} {t : ℝ}
    (W : WindowedModelWitness eps kappa S x t) {ρ : ℝ} (hρ : ρ < modelRadius eps)
    {y : W.model.M}
    (hy : y ∈ riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint ρ) :
    riemannianEDistOf (rescaledMetric S t (S.scalar t x) W.scalar_pos 0) x (W.embedding y) ≤
      ENNReal.ofReal (Real.sqrt (1 + eps) * ρ) := by
  have hR : 0 < modelRadius eps := inv_pos.mpr (Real.sqrt_pos.mpr W.eps_pos)
  have hL : 0 < Real.sqrt (1 + eps) := Real.sqrt_pos.mpr (by linarith [W.eps_pos])
  have hsource : riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint
      (modelRadius eps) ⊆ W.embedding.source :=
    (riemannianClosedBallOf_mono _ _ (by linarith)).trans W.buffered_ball
  have hupper : ∀ z ∈ riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint
      (modelRadius eps), ∀ v : TangentSpace I3 z,
      (rescaledMetric S t (S.scalar t x) W.scalar_pos 0).inner (W.embedding z)
        (mfderiv I3 I3 W.embedding z v) (mfderiv I3 I3 W.embedding z v) ≤
        Real.sqrt (1 + eps) ^ 2 * (W.model.S.base.metric 0).inner z v v := by
    intro z hz v
    have h0 : (0 : ℝ) ∈ Icc (-modelDepth eps) 0 :=
      ⟨neg_nonpos.mpr (inv_pos.mpr W.eps_pos).le, le_rfl⟩
    have heq := W.comparison.pullback_eq 0 z hz (fun _ => v)
    have hle := (W.comparison.equivalence 0 h0 z hz v).2
    rw [Real.sq_sqrt (by linarith [W.eps_pos])]
    rw [heq] at hle
    exact hle
  have hy' : riemannianEDistOf (W.model.S.base.metric 0) W.model.basepoint y <
      ENNReal.ofReal (modelRadius eps) :=
    lt_of_le_of_lt hy ((ENNReal.ofReal_lt_ofReal_iff hR).mpr hρ)
  have hmap := Perelman.KappaSolutions.edistOf_map_le_of_metric_upper_on_ball
    (W.model.S.base.metric 0) (rescaledMetric S t (S.scalar t x) W.scalar_pos 0) W.embedding
    W.model.basepoint y hR hL hsource hupper hy'
  rw [W.base_map] at hmap
  refine hmap.trans ?_
  rw [ENNReal.ofReal_mul hL.le]
  exact mul_le_mul_right hy _

private theorem toRestrictOpen_preserves {U : TopologicalSpace.Opens M} [SigmaCompactSpace U]
    {x : U} {eps kappa t : ℝ} (W : WindowedModelWitness eps kappa S x.val t)
    (hU : W.embedding '' riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint
      (modelRadius eps + 1) ⊆ (U : Set M))
    (o : TangentOrientationSection M) (oN : TangentOrientationSection W.model.M)
    (hO : ∀ y ∈ W.embedding.source, ∃ hf : Function.Bijective (mfderiv I3 I3 W.embedding y),
      PreservesTangentOrientationAt oN o W.embedding y hf) :
    ∀ y ∈ (W.toRestrictOpen hU).embedding.source,
      ∃ hf : Function.Bijective (mfderiv I3 I3 (W.toRestrictOpen hU).embedding y),
        PreservesTangentOrientationAt oN (o.restrictOpen U) (W.toRestrictOpen hU).embedding y
          hf := by
  intro y hy
  change W.model.M at y
  have hsrc := W.toRestrictOpen_source hU
  have hy' : y ∈ W.embedding.source ∩ W.embedding ⁻¹' (U : Set M) := hsrc ▸ hy
  have hlocal : (fun z => ((W.toRestrictOpen hU).embedding z : M)) =ᶠ[𝓝 y] W.embedding := by
    refine Filter.eventuallyEq_of_mem
      ((W.toRestrictOpen hU).embedding.open_source.mem_nhds hy) fun z hz => ?_
    have hz' : z ∈ W.embedding.source ∩ W.embedding ⁻¹' (U : Set M) := hsrc ▸ hz
    exact W.toRestrictOpen_embedding_coe hU hz'.2
  have hder : mfderiv I3 I3 (W.toRestrictOpen hU).embedding y =
      mfderiv I3 I3 W.embedding y :=
    (DifferentialGeometry.mfderiv_subtypeVal_comp (I := I3) (J := I3)
      (W.toRestrictOpen hU).embedding y).symm.trans hlocal.mfderiv_eq
  obtain ⟨hf, hpres⟩ := hO y hy'.1
  refine ⟨hder.symm ▸ hf, ?_⟩
  have hc := W.toRestrictOpen_embedding_coe hU hy'.2
  unfold PreservesTangentOrientationAt at hpres ⊢
  rw [TangentOrientationSection.restrictOpen_orientation]
  convert hpres using 2
  rw [hc]
  refine Iff.of_eq ?_
  congr 3
  exact LinearEquiv.ext fun v => congrArg (fun L => L v) hder

end WitnessGeometry

section StandardAge

open DifferentialGeometry.Tensor0SBundle

private theorem exists_standard_orientedWitness_of_age {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ τQ : ℝ, 1 ≤ τQ ∧ ∀ (Q : StandardSolution) (o : TangentOrientationSection ThreeSpace)
      (x : ThreeSpace) (t : ℝ), 0 ≤ t → t < 1 → τQ ≤ t * Q.val.toSolutionOn.scalar t x →
        OrientedWitness Q.val.toSolutionOn o ε standardModelKappa x t := by
  obtain ⟨α, hα, K, hK, hcurv⟩ := standard_uniform_initial_curvature_control
  obtain ⟨Q₀, hQ₀, hmodel⟩ := exists_standard_high_scalar_model_threshold hε hε1 hα
  have hmax := le_max_left Q₀ (α * (9 * K))
  refine ⟨max Q₀ (α * (9 * K)) + 1, by linarith, ?_⟩
  intro Q o x t ht0 ht1 hage
  have hlt : ENNReal.ofReal t < Q.val.lifetime := by
    rw [Q.lifetime_eq_one]
    exact ENNReal.ofReal_lt_one.mpr ht1
  have ht : t ∈ Q.val.domain :=
    (mem_lifetimeInterval_carrier Q.val.lifetime Q.val.lifetime_pos t).mpr ⟨ht0, hlt⟩
  have hαt : α ≤ t := by
    by_contra hlt'
    have hlt'' : t < α := lt_of_not_ge hlt'
    have hR : Q.val.toSolutionOn.scalar t x ≤ 9 * K := by
      have hrm := hcurv Q.val t ht0 hlt''.le hlt t ⟨ht0, le_rfl⟩ x
      rw [metricRm04_apply] at hrm
      have habs := scalar_abs_le_rm (Q.val.metric t) x
      have hdim : (Module.finrank ℝ (TangentSpace (𝓡 3) x) : ℝ) = 3 := by
        rw [show Module.finrank ℝ (TangentSpace (𝓡 3) x) = 3 from finrank_euclideanSpace_fin]
        norm_num
      rw [hdim] at habs
      change metricScalarAt (Q.val.metric t) x ≤ 9 * K
      have hle : (3 : ℝ) ^ 2 *
          Real.sqrt (normSq0S (Q.val.metric t) x 4 (metricRm04At (Q.val.metric t) x)) ≤
            9 * K := by
        nlinarith
      exact (le_abs_self _).trans (habs.trans hle)
    have h1 := mul_le_mul_of_nonneg_left hR ht0
    have h2 := mul_le_mul_of_nonneg_right hlt''.le (by positivity : (0 : ℝ) ≤ 9 * K)
    linarith [le_max_right Q₀ (α * (9 * K))]
  refine hmodel Q.val o x t ht hαt ht1 ?_
  change Q₀ ≤ Q.val.toSolutionOn.scalar t x
  rcases le_or_gt 0 (Q.val.toSolutionOn.scalar t x) with hR0 | hR0
  · have h1 := mul_le_mul_of_nonneg_right ht1.le hR0
    linarith
  · have h1 := mul_nonpos_of_nonneg_of_nonpos ht0 hR0.le
    linarith

end StandardAge

section WindowConvergence

private theorem exists_standard_time_lipschitz {Θ : ℝ} (hΘ0 : 0 ≤ Θ) (hΘ : Θ < 1) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ Q : StandardSolution, ∀ i ≤ 2, ∀ s ∈ Icc 0 Θ, ∀ t ∈ Icc 0 Θ,
      ∀ x : ThreeSpace, metricDerivNorm i (Q.val.metric s) (Q.val.metric t) StandardCap.metric x ≤
        L * |s - t| := by
  have hlt : ENNReal.ofReal Θ < uniformStandardLifetime := by
    rw [uniformStandardLifetime_eq_one]
    exact ENNReal.ofReal_lt_one.mpr hΘ
  obtain ⟨hlife, K, hK, hRm⟩ := uniformStandardLifetime_slab Θ hΘ0 hlt
  obtain ⟨Λ, -, C, L, -, hL, hstd⟩ := standard_metric_bounds_on_shorter_windows Θ K hΘ0 hK
  refine ⟨L 0 + L 1 + L 2, by linarith [hL 0, hL 1, hL 2], ?_⟩
  intro Q i hi s hs t ht x
  obtain ⟨-, -, hlip⟩ := hstd Q.val Θ hΘ0 le_rfl (hlife Q) (hRm Q)
  refine (hlip i s hs t ht x).trans (mul_le_mul_of_nonneg_right ?_ (abs_nonneg _))
  interval_cases i <;> linarith [hL 0, hL 1, hL 2]

private theorem tendsto_scalar_of_standard_close {Θ D T₀ : ℝ} (hΘ : Θ < 1)
    {Q : ℕ → StandardSolution} {Q' : StandardSolution}
    (hQ : ∀ K : Set (standardCapWindow D), IsCompact K → ∀ p : ℕ, ∀ e : ℝ, 0 < e →
      ∃ j : ℕ, ∀ i ≥ j, ∀ t ∈ Icc 0 Θ,
        metricDerivNormSupOn K p (((Q i).val.metric t).restrictOpen (standardCapWindow D))
          ((Q'.val.metric t).restrictOpen (standardCapWindow D))
          (StandardCap.metric.restrictOpen (standardCapWindow D)) < e)
    {T : ℕ → ℝ} (hTΘ : ∀ n, T n ∈ Icc 0 Θ) (hT : Tendsto T atTop (𝓝 T₀))
    {g : ℕ → SmoothRiemannianMetric (𝓡 3) (standardCapWindow D)}
    (hclose : ∀ p : ℕ, ∀ e : ℝ, 0 < e → ∀ᶠ n in atTop, ∀ i ≤ p, ∀ v : standardCapWindow D,
      metricDerivNorm i (g n) (((Q n).val.metric (T n)).restrictOpen (standardCapWindow D))
        (StandardCap.metric.restrictOpen (standardCapWindow D)) v < e)
    {z : ℕ → standardCapWindow D} {z₀ : standardCapWindow D} (hz : Tendsto z atTop (𝓝 z₀)) :
    Tendsto (fun n => metricScalarAt (g n) (z n)) atTop
      (𝓝 (metricScalarAt (Q'.val.metric T₀) z₀.val)) := by
  have hT₀ : T₀ ∈ Icc 0 Θ := isClosed_Icc.mem_of_tendsto hT (Eventually.of_forall hTΘ)
  obtain ⟨L, hL, hlip⟩ := exists_standard_time_lipschitz (hT₀.1.trans hT₀.2) hΘ
  rw [← metricScalarAt_restrictOpen (Q'.val.metric T₀) (standardCapWindow D) z₀]
  refine tendsto_metricScalarAt_of_metricDerivNormSupOn
    (R := StandardCap.metric.restrictOpen (standardCapWindow D)) (fun K hK e he => ?_) hz
  obtain ⟨j, hj⟩ := hQ K hK 2 (e / 4) (by positivity)
  have hδ : 0 < e / (4 * (L + 1)) := by positivity
  have hsmall : ∀ᶠ n in atTop, |T n - T₀| < e / (4 * (L + 1)) := by
    filter_upwards [Metric.tendsto_nhds.mp hT _ hδ] with n hn
    rwa [Real.dist_eq] at hn
  filter_upwards [hclose 2 (e / 4) (by positivity), eventually_ge_atTop j, hsmall]
    with n hn hnj hns
  have hLs : L * |T n - T₀| ≤ e / 4 := by
    have hL1 : 0 < L + 1 := by linarith
    have hmul : (L + 1) * |T n - T₀| ≤ (L + 1) * (e / (4 * (L + 1))) :=
      mul_le_mul_of_nonneg_left hns.le hL1.le
    have heq : (L + 1) * (e / (4 * (L + 1))) = e / 4 := by field_simp
    nlinarith [abs_nonneg (T n - T₀)]
  refine (metricDerivNormSupOn_le_of_forall K 2 _ _ _ (3 * (e / 4)) (by positivity)
    fun i hi v hv => ?_).trans_lt (by linarith)
  have h1 := (hn i hi v).le
  have h2 := (derivNorm_le_sup hK hi _ _ _ hv).trans (hj n hnj (T n) (hTΘ n)).le
  have h3 : metricDerivNorm i ((Q'.val.metric (T n)).restrictOpen (standardCapWindow D))
      ((Q'.val.metric T₀).restrictOpen (standardCapWindow D))
      (StandardCap.metric.restrictOpen (standardCapWindow D)) v ≤ e / 4 := by
    rw [metricDerivNorm_restrictOpen]
    exact (hlip Q' i hi _ (hTΘ n) _ hT₀ v.val).trans hLs
  have t1 := metricDerivNorm_triangle i (g n)
    (((Q n).val.metric (T n)).restrictOpen (standardCapWindow D))
    ((Q'.val.metric T₀).restrictOpen (standardCapWindow D))
    (StandardCap.metric.restrictOpen (standardCapWindow D)) v
  have t2 := metricDerivNorm_triangle i
    (((Q n).val.metric (T n)).restrictOpen (standardCapWindow D))
    ((Q'.val.metric (T n)).restrictOpen (standardCapWindow D))
    ((Q'.val.metric T₀).restrictOpen (standardCapWindow D))
    (StandardCap.metric.restrictOpen (standardCapWindow D)) v
  linarith

end WindowConvergence

section StandardImage

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

private theorem modelRadius_add_one_lt {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    modelRadius δ + 1 < modelRadius (δ / 4) := by
  have hs : Real.sqrt (δ / 4) = Real.sqrt δ / 2 := by
    rw [Real.sqrt_div' δ (by norm_num : (0 : ℝ) ≤ 4),
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hpos : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδ
  have hlt : Real.sqrt δ < 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_lt_sqrt hδ.le hδ1
  simp only [modelRadius, hs]
  rw [inv_div]
  have h1 : 1 < (Real.sqrt δ)⁻¹ := one_lt_inv₀ hpos |>.mpr hlt
  have h2 : 2 / Real.sqrt δ = 2 * (Real.sqrt δ)⁻¹ := by rw [div_eq_mul_inv]
  linarith

private theorem image_subset_standardCapWindow {Q : StandardSolution} {T₀ : ℝ}
    (hT₀ : T₀ ∈ Q.val.domain) {x : ThreeSpace} {δ kappa : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    (W : WindowedModelWitness (δ / 4) kappa
      (parabolicSolution Q.val.toSolutionOn T₀ 1 one_pos hT₀) x 0)
    {Λ : ℝ} (hΛ1 : 1 ≤ Λ)
    (hΛ : ∀ y (v : TangentSpace (𝓡 3) y),
      Λ⁻¹ * StandardCap.metric.inner y v v ≤ (Q.val.metric T₀).inner y v v)
    (hR : 1 ≤ Q.val.toSolutionOn.scalar T₀ x) {r D : ℝ} (hx : ‖x‖ ≤ r)
    (hD : r + 2 * (modelRadius δ + 1) * Real.sqrt Λ ≤ D) :
    W.embedding '' riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint
      (modelRadius δ + 1) ⊆ (standardCapWindow D : Set ThreeSpace) := by
  rintro _ ⟨y, hy, rfl⟩
  change ‖W.embedding y‖ < D + 1
  have hPs : (parabolicSolution Q.val.toSolutionOn T₀ 1 one_pos hT₀).scalar 0 x =
      Q.val.toSolutionOn.scalar T₀ x := by
    rw [parabolicSolution_scalar]
    simp [parabolicTime]
  have h1 := edist_embedding_le_of_lt_modelRadius W (modelRadius_add_one_lt hδ hδ1) hy
  have ht : parabolicTime T₀ 1 (parabolicTime 0
      ((parabolicSolution Q.val.toSolutionOn T₀ 1 one_pos hT₀).scalar 0 x) 0) = T₀ := by
    simp [parabolicTime]
  change riemannianEDistOf (scaleMetric _ W.scalar_pos
    (scaleMetric 1 one_pos (Q.val.metric (parabolicTime T₀ 1 (parabolicTime 0
      ((parabolicSolution Q.val.toSolutionOn T₀ 1 one_pos hT₀).scalar 0 x) 0)))))
    x (W.embedding y) ≤ _ at h1
  rw [ht, DifferentialGeometry.edistOf_scale, DifferentialGeometry.edistOf_scale,
    Real.sqrt_one, ENNReal.ofReal_one, one_mul] at h1
  have hΛ0 : 0 < Λ⁻¹ := inv_pos.mpr (by linarith)
  have h2 := DifferentialGeometry.le_edistOf_of_quad StandardCap.metric (Q.val.metric T₀) hΛ0
    hΛ x (W.embedding y)
  have h3 := StandardCap.radial_difference_le_edist x (W.embedding y)
  set u := |‖W.embedding y‖ - ‖x‖|
  set a := Real.sqrt ((parabolicSolution Q.val.toSolutionOn T₀ 1 one_pos hT₀).scalar 0 x)
  set b := Real.sqrt Λ⁻¹
  set c := Real.sqrt (1 + δ / 4) * (modelRadius δ + 1)
  have hρ : 0 < modelRadius δ + 1 := by
    have : 0 < modelRadius δ := inv_pos.mpr (Real.sqrt_pos.mpr hδ)
    linarith
  have hb : 0 ≤ b := Real.sqrt_nonneg _
  have ha1 : 1 ≤ a := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by rw [hPs]; exact hR)
  have hc : c ≤ 2 * (modelRadius δ + 1) := by
    refine mul_le_mul_of_nonneg_right ?_ hρ.le
    rw [Real.sqrt_le_left (by norm_num)]
    linarith
  have hchain : ENNReal.ofReal (a * (b * u)) ≤ ENNReal.ofReal c := by
    rw [ENNReal.ofReal_mul (Real.sqrt_nonneg _), ENNReal.ofReal_mul hb]
    exact (mul_le_mul_right (mul_le_mul_right h3 _) _).trans
      ((mul_le_mul_right h2 _).trans h1)
  have hreal := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hchain
  have hbΛ : b * Real.sqrt Λ = 1 := by
    rw [← Real.sqrt_mul hΛ0.le, inv_mul_cancel₀ (by linarith), Real.sqrt_one]
  have hu : u ≤ 2 * (modelRadius δ + 1) * Real.sqrt Λ := by
    have hsΛ : 0 ≤ Real.sqrt Λ := Real.sqrt_nonneg _
    have hu0 : 0 ≤ u := abs_nonneg _
    have hbu : b * u ≤ a * (b * u) := le_mul_of_one_le_left (mul_nonneg hb hu0) ha1
    calc u = b * u * Real.sqrt Λ := by rw [mul_comm b u, mul_assoc, hbΛ, mul_one]
      _ ≤ c * Real.sqrt Λ := mul_le_mul_of_nonneg_right (hbu.trans (hreal.trans le_rfl)) hsΛ
      _ ≤ _ := mul_le_mul_of_nonneg_right hc hsΛ
  have hn : ‖W.embedding y‖ ≤ ‖x‖ + u := by
    have := le_abs_self (‖W.embedding y‖ - ‖x‖)
    linarith
  linarith

end StandardImage

section Core

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

private theorem nonempty_euclidean_tangentOrientation :
    Nonempty (TangentOrientationSection ThreeSpace) := by
  let e := (finCongr (by simp : Module.finrank ℝ ThreeSpace = 3)).symm
  let o := DifferentialGeometry.Topology.Manifold.euclideanSmoothOrientation ThreeSpace
    (Orientation.reindex ℝ ThreeSpace e
      ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation))
  obtain ⟨O, _⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_manifoldOrientation_eq_of_smoothOrientation
      (𝓡 3) o
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp
  let O₃ : DifferentialGeometry.ManifoldOrientation (𝓡 3) ThreeSpace 3 :=
    cast (congrArg (fun n =>
      DifferentialGeometry.ManifoldOrientation (𝓡 3) ThreeSpace n) hdim) O
  exact ⟨{ orientation := O₃.orientation, locally_constant := O₃.locally_constant }⟩

private theorem isPreconnected_standardCapWindow (D : ℝ) :
    IsPreconnected (standardCapWindow D : Set ThreeSpace) := by
  have h : (standardCapWindow D : Set ThreeSpace) = Metric.ball 0 (D + 1) := by
    ext x
    simp [standardCapWindow]
  rw [h]
  exact (convex_ball 0 (D + 1)).isPreconnected

private theorem scaleMetric_one_eq {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M] (g : SmoothRiemannianMetric I M) :
    scaleMetric 1 one_pos g = g :=
  SmoothRiemannianMetric.ext_inner fun x v w => by rw [scaleMetric_one]

private theorem eventually_orientedWitness_of_strict_standard_witness_endpoint
    {δ Θ D T₀ : ℝ} (hδ : 0 < δ) (hΘ : Θ < 1)
    {Q : ℕ → StandardSolution} {Q' : StandardSolution}
    (hQ : ∀ K : Set (standardCapWindow D), IsCompact K → ∀ p : ℕ, ∀ e : ℝ, 0 < e →
      ∃ j : ℕ, ∀ i ≥ j, ∀ t ∈ Icc 0 Θ,
        metricDerivNormSupOn K p (((Q i).val.metric t).restrictOpen (standardCapWindow D))
          ((Q'.val.metric t).restrictOpen (standardCapWindow D))
          (StandardCap.metric.restrictOpen (standardCapWindow D)) < e)
    {T : ℕ → ℝ} (hT0 : ∀ n, 0 ≤ T n)
    (S : ∀ n, SolutionOn (I := I3) (M := standardCapWindow D)
      (RealTimeInterval.closed 0 (T n) (hT0 n)))
    (hS : ∀ n, IsSolutionOn (S n)) (hTΘ : ∀ n, T n ≤ Θ)
    (hclose : ∀ p : ℕ, ∀ e : ℝ, 0 < e → ∀ᶠ n in atTop, ∀ τ ∈ Icc 0 (T n), ∀ i ≤ p,
      ∀ v : standardCapWindow D, metricDerivNorm i ((S n).base.metric τ)
        (((Q n).val.metric τ).restrictOpen (standardCapWindow D))
        (StandardCap.metric.restrictOpen (standardCapWindow D)) v < e)
    (hT : Tendsto T atTop (𝓝 T₀)) {z : ℕ → standardCapWindow D} {z₀ : standardCapWindow D}
    (hz : Tendsto z atTop (𝓝 z₀))
    (hT₀mem : T₀ ∈ Q'.val.domain)
    (W : WindowedModelWitness δ standardModelKappa
      (parabolicSolution Q'.val.toSolutionOn T₀ 1 one_pos hT₀mem) z₀.val 0)
    (hstrict : ∀ a b, a + 2 * b ≤ modelOrder δ → ∀ s ∈ Icc (-modelDepth δ) 0,
      ∀ y ∈ riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint (modelRadius δ),
        tensor02CovDerivNormWith a (W.comparison.jet b s)
          (W.model.S.base.metric s) (W.model.S.base.metric s) y < δ)
    (oE : TangentOrientationSection ThreeSpace) (oN : TangentOrientationSection W.model.M)
    (hO : ∀ y ∈ W.embedding.source, ∃ hf : Function.Bijective (mfderiv I3 I3 W.embedding y),
      PreservesTangentOrientationAt oN oE W.embedding y hf)
    (hU : W.embedding '' riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint
      (modelRadius δ + 1) ⊆ (standardCapWindow D : Set ThreeSpace))
    (hmargin : 4 * (δ * (parabolicSolution Q'.val.toSolutionOn T₀ 1 one_pos hT₀mem).scalar 0
      z₀.val)⁻¹ ≤ T₀) :
    ∀ᶠ n in atTop, ∀ o : TangentOrientationSection (standardCapWindow D),
      OrientedWitness (S n) o δ standardModelKappa (z n) (T n) := by
  have hT₀Θ : T₀ ≤ Θ := le_of_tendsto' hT hTΘ
  have hR := W.scalar_pos
  obtain ⟨b, hbdef⟩ : ∃ b : ℝ, b = 2 * (δ *
      (parabolicSolution Q'.val.toSolutionOn T₀ 1 one_pos hT₀mem).scalar 0 z₀.val)⁻¹ :=
    ⟨_, rfl⟩
  have hw0 : 0 < (δ * (parabolicSolution Q'.val.toSolutionOn T₀ 1 one_pos hT₀mem).scalar 0
      z₀.val)⁻¹ := inv_pos.mpr (mul_pos hδ hR)
  have hbT : b < T₀ := by linarith
  have hwb : (δ * (parabolicSolution Q'.val.toSolutionOn T₀ 1 one_pos hT₀mem).scalar 0
      z₀.val)⁻¹ < b := by linarith
  have hb0 : -b ≤ 0 := by linarith
  have hcarP : (RealTimeInterval.closed (-b) 0 hb0).carrier ⊆
      (parabolicInterval (lifetimeInterval Q'.val.lifetime Q'.val.lifetime_pos) T₀ 1
        hT₀mem).carrier := by
    intro s hs
    have hs' : s ∈ Icc (-b) 0 := hs
    change parabolicTime T₀ 1 s ∈ (lifetimeInterval Q'.val.lifetime Q'.val.lifetime_pos).carrier
    rw [mem_lifetimeInterval_carrier]
    simp only [parabolicTime, div_one]
    exact ⟨by linarith [hs'.1],
      (ENNReal.ofReal_lt_one.mpr (by linarith [hs'.2])).trans_eq Q'.lifetime_eq_one.symm⟩
  have hregP : (RealTimeInterval.closed (-b) 0 hb0).regular ⊆
      (parabolicInterval (lifetimeInterval Q'.val.lifetime Q'.val.lifetime_pos) T₀ 1
        hT₀mem).regular := by
    intro s hs
    have hs' : s ∈ Ioo (-b) 0 := hs
    change parabolicTime T₀ 1 s ∈ (lifetimeInterval Q'.val.lifetime Q'.val.lifetime_pos).regular
    rw [mem_lifetimeInterval_regular]
    simp only [parabolicTime, div_one]
    exact ⟨by linarith [hs'.1],
      (ENNReal.ofReal_lt_one.mpr (by linarith [hs'.2])).trans_eq Q'.lifetime_eq_one.symm⟩
  have hP : IsSolutionOn (parabolicSolution Q'.val.toSolutionOn T₀ 1 one_pos hT₀mem) :=
    parabolicSolution_isSolutionOn _ Q'.val.isSolutionOn T₀ 1 one_pos hT₀mem
  have hS₀ : IsSolutionOn ((solutionOnRestrictOpen
      (parabolicSolution Q'.val.toSolutionOn T₀ 1 one_pos hT₀mem)
      (standardCapWindow D)).timeRestrict (RealTimeInterval.closed (-b) 0 hb0)) :=
    isSolutionOn_timeRestrict (isSolutionOn_restrictOpen _ hP _) hcarP hregP
  have hRs : (solutionOnRestrictOpen (parabolicSolution Q'.val.toSolutionOn T₀ 1 one_pos hT₀mem)
      (standardCapWindow D)).scalar 0 z₀ =
      (parabolicSolution Q'.val.toSolutionOn T₀ 1 one_pos hT₀mem).scalar 0 z₀.val :=
    scalar_restrictOpen _ _ 0 z₀
  have htime : (0 : ℝ) ∈ (RealTimeInterval.closed (-b) 0 hb0).carrier :=
    show (0 : ℝ) ∈ Icc (-b) 0 from ⟨by linarith, le_rfl⟩
  have hwinR : Icc (0 - (δ * (solutionOnRestrictOpen
      (parabolicSolution Q'.val.toSolutionOn T₀ 1 one_pos hT₀mem)
      (standardCapWindow D)).scalar 0 z₀)⁻¹) 0 ⊆
        (RealTimeInterval.closed (-b) 0 hb0).carrier := by
    rw [hRs]
    intro u hu
    exact ⟨by linarith [hu.1], hu.2⟩
  have hlow : -b < 0 - (δ * ((solutionOnRestrictOpen
      (parabolicSolution Q'.val.toSolutionOn T₀ 1 one_pos hT₀mem)
      (standardCapWindow D)).timeRestrict (RealTimeInterval.closed (-b) 0 hb0)).scalar 0
        z₀)⁻¹ := by
    rw [scalar_timeRestrict, hRs]
    linarith
  have hTn : ∀ n, T n ∈ (RealTimeInterval.closed 0 (T n) (hT0 n)).carrier :=
    fun n => show T n ∈ Icc 0 (T n) from ⟨hT0 n, le_rfl⟩
  have hcarS : ∀ n, b ≤ T n → (RealTimeInterval.closed (-b) 0 hb0).carrier ⊆
      (parabolicInterval (RealTimeInterval.closed 0 (T n) (hT0 n)) (T n) 1
        (hTn n)).carrier := by
    intro n hbn s hs
    have hs' : s ∈ Icc (-b) 0 := hs
    change parabolicTime (T n) 1 s ∈ Icc 0 (T n)
    simp only [parabolicTime, div_one]
    exact ⟨by linarith [hs'.1], by linarith [hs'.2]⟩
  have hregS : ∀ n, b ≤ T n → (RealTimeInterval.closed (-b) 0 hb0).regular ⊆
      (parabolicInterval (RealTimeInterval.closed 0 (T n) (hT0 n)) (T n) 1
        (hTn n)).regular := by
    intro n hbn s hs
    have hs' : s ∈ Ioo (-b) 0 := hs
    change parabolicTime (T n) 1 s ∈ Ioo 0 (T n)
    simp only [parabolicTime, div_one]
    exact ⟨by linarith [hs'.1], by linarith [hs'.2]⟩
  let S' : ℕ → SolutionOn (I := I3) (M := standardCapWindow D)
      (RealTimeInterval.closed (-b) 0 hb0) := fun n =>
    if h : b ≤ T n then
      (parabolicSolution (S n) (T n) 1 one_pos (hTn n)).timeRestrict
        (RealTimeInterval.closed (-b) 0 hb0)
    else (solutionOnRestrictOpen (parabolicSolution Q'.val.toSolutionOn T₀ 1 one_pos hT₀mem)
      (standardCapWindow D)).timeRestrict (RealTimeInterval.closed (-b) 0 hb0)
  have hS'pos : ∀ n, b ≤ T n → S' n =
      (parabolicSolution (S n) (T n) 1 one_pos (hTn n)).timeRestrict
        (RealTimeInterval.closed (-b) 0 hb0) := fun n h => dif_pos h
  have hS' : ∀ n, IsSolutionOn (S' n) := by
    intro n
    by_cases h : b ≤ T n
    · rw [hS'pos n h]
      exact isSolutionOn_timeRestrict
        (parabolicSolution_isSolutionOn (S n) (hS n) (T n) 1 one_pos (hTn n))
        (hcarS n h) (hregS n h)
    · rw [show S' n = _ from dif_neg h]
      exact hS₀
  have hbev : ∀ᶠ n in atTop, b ≤ T n :=
    (hT.eventually (Ioi_mem_nhds hbT)).mono fun n h => le_of_lt h
  have hL5 := StandardSolution.eventually_shifted_window_metricDerivNormSupOn_lt
    (T₀ := T₀) hΘ (show 0 < T₀ - b by linarith) hQ hTΘ hT
    (g := fun n τ => (S n).base.metric τ) hclose (J := Icc (T₀ - b) T₀) subset_rfl
  have hconv : ∀ K : Set (standardCapWindow D), IsCompact K → ∀ p : ℕ, ∀ e : ℝ, 0 < e →
      ∀ᶠ n in atTop, ∀ τ ∈ (RealTimeInterval.closed (-b) 0 hb0).carrier,
        metricDerivNormSupOn K p ((S' n).base.metric τ)
          (((solutionOnRestrictOpen (parabolicSolution Q'.val.toSolutionOn T₀ 1 one_pos hT₀mem)
            (standardCapWindow D)).timeRestrict (RealTimeInterval.closed (-b) 0 hb0)).base.metric
              τ) (StandardCap.metric.restrictOpen (standardCapWindow D)) < e := by
    intro K hK p e he
    filter_upwards [hL5 K hK p e he, hbev] with n hn hbn τ hτ
    have hτ' : τ ∈ Icc (-b) 0 := hτ
    have e1 : (S' n).base.metric τ =
        (S n).base.metric ((T₀ + τ) + (T n - T₀)) := by
      rw [hS'pos n hbn]
      change scaleMetric 1 one_pos ((S n).base.metric (parabolicTime (T n) 1 τ)) = _
      rw [scaleMetric_one_eq]
      congr 1
      simp only [parabolicTime, div_one]
      ring
    have e2 : ((solutionOnRestrictOpen (parabolicSolution Q'.val.toSolutionOn T₀ 1 one_pos
        hT₀mem) (standardCapWindow D)).timeRestrict
          (RealTimeInterval.closed (-b) 0 hb0)).base.metric τ =
        (Q'.val.metric (T₀ + τ)).restrictOpen (standardCapWindow D) := by
      change (scaleMetric 1 one_pos (Q'.val.toSolutionOn.base.metric
        (parabolicTime T₀ 1 τ))).restrictOpen _ = _
      rw [scaleMetric_one_eq]
      simp only [parabolicTime, div_one]
      rfl
    rw [e1, e2]
    exact hn (T₀ + τ) ⟨by linarith [hτ'.1], by linarith [hτ'.2]⟩
  have hscalar := SolutionOn.tendsto_scalar_of_metricDerivNormSupOn
    (StandardCap.metric.restrictOpen (standardCapWindow D)) hconv htime hz
  have hL4 := ((W.toRestrictOpen hU).timeRestrict (RealTimeInterval.closed (-b) 0 hb0) htime
    hwinR).eventually_strict_of_tendsto_flows_endpoint hS₀ hS' hlow (fun _ h => h)
    (fun _ h => h) (W.toRestrictOpen_strict hU hstrict) _ hconv hz hscalar
  have hOt := toRestrictOpen_preserves W hU oE oN hO
  have : PreconnectedSpace (standardCapWindow D) :=
    Subtype.preconnectedSpace (isPreconnected_standardCapWindow D)
  filter_upwards [hL4, hbev] with n hn hbn
  intro o
  obtain ⟨W', horient, -⟩ := hn
  obtain ⟨oN'', hO''⟩ := exists_preserves_of_preconnected
    (oE.restrictOpen (standardCapWindow D)) o oN _ _ hOt
  obtain ⟨oN', hO'⟩ := horient o oN'' hO''
  have hw : OrientedWitness (S' n) o δ standardModelKappa (z n) 0 := ⟨W', oN', hO'⟩
  rw [hS'pos n hbn] at hw
  have hw3 := (orientedWitness_paraSolution_iff (S n) o one_pos (hTn n) 0 (z n) δ
    standardModelKappa).mp (orientedWitness_of_timeRestrict (hcarS n hbn) hw)
  rwa [parabolicTime_zero] at hw3


private theorem eventually_orientedWitness_of_standard_close_endpoint
    {δ Θ D T₀ Λ r : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (hΘ : Θ < 1)
    {Q : ℕ → StandardSolution} {Q' : StandardSolution}
    (hQ : ∀ K : Set (standardCapWindow D), IsCompact K → ∀ p : ℕ, ∀ e : ℝ, 0 < e →
      ∃ j : ℕ, ∀ i ≥ j, ∀ t ∈ Icc 0 Θ,
        metricDerivNormSupOn K p (((Q i).val.metric t).restrictOpen (standardCapWindow D))
          ((Q'.val.metric t).restrictOpen (standardCapWindow D))
          (StandardCap.metric.restrictOpen (standardCapWindow D)) < e)
    {T : ℕ → ℝ} (hT0 : ∀ n, 0 ≤ T n)
    (S : ∀ n, SolutionOn (I := I3) (M := standardCapWindow D)
      (RealTimeInterval.closed 0 (T n) (hT0 n)))
    (hS : ∀ n, IsSolutionOn (S n)) (hTΘ : ∀ n, T n ≤ Θ)
    (hclose : ∀ p : ℕ, ∀ e : ℝ, 0 < e → ∀ᶠ n in atTop, ∀ τ ∈ Icc 0 (T n), ∀ i ≤ p,
      ∀ v : standardCapWindow D, metricDerivNorm i ((S n).base.metric τ)
        (((Q n).val.metric τ).restrictOpen (standardCapWindow D))
        (StandardCap.metric.restrictOpen (standardCapWindow D)) v < e)
    (hT : Tendsto T atTop (𝓝 T₀)) {z : ℕ → standardCapWindow D} {z₀ : standardCapWindow D}
    (hz : Tendsto z atTop (𝓝 z₀))
    (hwit : ∀ o : TangentOrientationSection ThreeSpace,
      OrientedWitness Q'.val.toSolutionOn o (δ / 4) standardModelKappa z₀.val T₀)
    (hT₀ : 0 < T₀) (hR1 : 1 ≤ Q'.val.toSolutionOn.scalar T₀ z₀.val) (hΛ1 : 1 ≤ Λ)
    (hΛ : ∀ y (v : TangentSpace (𝓡 3) y),
      Λ⁻¹ * StandardCap.metric.inner y v v ≤ (Q'.val.metric T₀).inner y v v)
    (hz₀ : ‖z₀.val‖ ≤ r) (hD : r + 2 * (modelRadius δ + 1) * Real.sqrt Λ ≤ D) :
    ∀ᶠ n in atTop, ∀ o : TangentOrientationSection (standardCapWindow D),
      OrientedWitness (S n) o δ standardModelKappa (z n) (T n) := by
  have hT₀Θ : T₀ ≤ Θ := le_of_tendsto' hT hTΘ
  have hT₀1 : T₀ < 1 := hT₀Θ.trans_lt hΘ
  have hT₀mem : T₀ ∈ Q'.val.domain := by
    refine (mem_lifetimeInterval_carrier _ _ T₀).mpr ⟨hT₀.le, ?_⟩
    rw [Q'.lifetime_eq_one]
    exact ENNReal.ofReal_lt_one.mpr (by linarith)
  obtain ⟨oE⟩ := nonempty_euclidean_tangentOrientation
  have hP : IsSolutionOn (parabolicSolution Q'.val.toSolutionOn T₀ 1 one_pos hT₀mem) :=
    parabolicSolution_isSolutionOn _ Q'.val.isSolutionOn T₀ 1 one_pos hT₀mem
  have hwP : OrientedWitness (parabolicSolution Q'.val.toSolutionOn T₀ 1 one_pos hT₀mem) oE
      (δ / 4) standardModelKappa z₀.val 0 := by
    refine (orientedWitness_paraSolution_iff Q'.val.toSolutionOn oE one_pos hT₀mem 0 z₀.val
      (δ / 4) standardModelKappa).mpr ?_
    rw [parabolicTime_zero]
    exact hwit oE
  obtain ⟨W₄, oN, hO⟩ := hwP
  have hPs : (parabolicSolution Q'.val.toSolutionOn T₀ 1 one_pos hT₀mem).scalar 0 z₀.val =
      Q'.val.toSolutionOn.scalar T₀ z₀.val := by
    rw [parabolicSolution_scalar]
    simp [parabolicTime]
  have hR0 : 0 < Q'.val.toSolutionOn.scalar T₀ z₀.val := by linarith
  have hwin4 : ((δ / 4) * Q'.val.toSolutionOn.scalar T₀ z₀.val)⁻¹ ≤ T₀ := by
    have hl := W₄.window_mem ⟨le_rfl, by
      have := inv_pos.mpr (mul_pos (by positivity : (0 : ℝ) < δ / 4) W₄.scalar_pos)
      linarith⟩
    rw [hPs] at hl
    change parabolicTime T₀ 1 (0 - ((δ / 4) * Q'.val.toSolutionOn.scalar T₀ z₀.val)⁻¹) ∈
      (lifetimeInterval Q'.val.lifetime Q'.val.lifetime_pos).carrier at hl
    rw [mem_lifetimeInterval_carrier] at hl
    simp only [parabolicTime, div_one] at hl
    linarith [hl.1]
  have hreg4 : ∀ s ∈ Ioo (-modelDepth (δ / 4)) 0, parabolicTime 0
      ((parabolicSolution Q'.val.toSolutionOn T₀ 1 one_pos hT₀mem).scalar 0 z₀.val) s ∈
      (parabolicInterval (lifetimeInterval Q'.val.lifetime Q'.val.lifetime_pos) T₀ 1
        hT₀mem).regular := by
    intro s hs
    rw [hPs]
    change parabolicTime T₀ 1 (parabolicTime 0 (Q'.val.toSolutionOn.scalar T₀ z₀.val) s) ∈
      (lifetimeInterval Q'.val.lifetime Q'.val.lifetime_pos).regular
    rw [mem_lifetimeInterval_regular]
    have hkey : -((δ / 4) * Q'.val.toSolutionOn.scalar T₀ z₀.val)⁻¹ <
        s / Q'.val.toSolutionOn.scalar T₀ z₀.val := by
      have h1 : -(δ / 4)⁻¹ < s := hs.1
      rw [lt_div_iff₀ hR0]
      have heq : -((δ / 4) * Q'.val.toSolutionOn.scalar T₀ z₀.val)⁻¹ *
          Q'.val.toSolutionOn.scalar T₀ z₀.val = -(δ / 4)⁻¹ := by
        field_simp
      rw [heq]
      exact h1
    have hneg : s / Q'.val.toSolutionOn.scalar T₀ z₀.val < 0 := div_neg_of_neg_of_pos hs.2 hR0
    simp only [parabolicTime, div_one, zero_add]
    exact ⟨by linarith,
      (ENNReal.ofReal_lt_one.mpr (by linarith)).trans_eq Q'.lifetime_eq_one.symm⟩
  have hlt : δ / 4 < δ := by linarith
  refine eventually_orientedWitness_of_strict_standard_witness_endpoint hδ hΘ hQ hT0 S hS hTΘ
    hclose hT hz hT₀mem (W₄.mono_of_regular hP hlt.le hδ1 hreg4)
    (W₄.mono_of_regular_strict_of_lt hP hlt hδ1 hreg4) oE oN hO
    (image_subset_standardCapWindow hT₀mem hδ hδ1 W₄ hΛ1 hΛ hR1 hz₀ hD) ?_
  rw [hPs]
  have heq : 4 * (δ * Q'.val.toSolutionOn.scalar T₀ z₀.val)⁻¹ =
      ((δ / 4) * Q'.val.toSolutionOn.scalar T₀ z₀.val)⁻¹ := by
    field_simp
  rw [heq]
  exact hwin4

theorem exists_uniform_orientedWitness_of_standard_close_endpoint {δ : ℝ} (hδ : 0 < δ)
    (hδ1 : δ < 1) :
    ∃ τQ : ℝ, 0 < τQ ∧ ∀ (Θ r : ℝ), Θ < 1 →
    ∃ (D : ℝ) (N : ℕ) (e : ℝ), r < D ∧ 0 < e ∧
    ∀ (Q : StandardSolution) (T : ℝ) (hT : 0 ≤ T), T ≤ Θ →
    ∀ (S : SolutionOn (I := ThreeModel) (M := standardCapWindow D)
        (RealTimeInterval.closed 0 T hT)), IsSolutionOn S →
    (∀ τ ∈ Icc 0 T, ∀ i ≤ N, ∀ v : standardCapWindow D,
      metricDerivNorm i (S.base.metric τ)
        ((Q.val.metric τ).restrictOpen (standardCapWindow D))
        (StandardCap.metric.restrictOpen (standardCapWindow D)) v < e) →
    ∀ (o : TangentOrientationSection (standardCapWindow D)) (z : standardCapWindow D),
      ‖z.val‖ < r → τQ ≤ T * S.scalar T z →
      OrientedWitness S o δ standardModelKappa z T := by
  obtain ⟨τQ, hτQ1, hage⟩ :=
    exists_standard_orientedWitness_of_age (ε := δ / 4) (by positivity) (by linarith)
  refine ⟨τQ, by linarith, fun Θ r hΘ => ?_⟩
  have hΘ' : max Θ 0 < 1 := max_lt hΘ one_pos
  have hlt : ENNReal.ofReal (max Θ 0) < uniformStandardLifetime := by
    rw [uniformStandardLifetime_eq_one]
    exact ENNReal.ofReal_lt_one.mpr hΘ'
  obtain ⟨hlife, K, hK, hRm⟩ := uniformStandardLifetime_slab (max Θ 0) (le_max_right _ _) hlt
  obtain ⟨Λ, hΛ1, C, L, -, -, hstd⟩ :=
    standard_metric_bounds_on_shorter_windows (max Θ 0) K (le_max_right _ _) hK
  have hΛ : ∀ (Q : StandardSolution), ∀ t ∈ Icc 0 Θ, ∀ y (v : TangentSpace (𝓡 3) y),
      Λ⁻¹ * StandardCap.metric.inner y v v ≤ (Q.val.metric t).inner y v v := by
    intro Q t ht y v
    have h := (hstd Q.val (max Θ 0) (le_max_right _ _) le_rfl (hlife Q) (hRm Q)).1 t
      ⟨ht.1, ht.2.trans (le_max_left _ _)⟩
    exact (h.2 y (mem_univ y) v).1
  set D := r + 2 * (modelRadius δ + 1) * Real.sqrt Λ with hDdef
  have hrD : r < D := by
    have : 0 < modelRadius δ := inv_pos.mpr (Real.sqrt_pos.mpr hδ)
    have : 0 < Real.sqrt Λ := Real.sqrt_pos.mpr (by linarith)
    rw [hDdef]
    nlinarith
  refine ⟨D, ?_⟩
  by_contra hcon
  have hex : ∀ n : ℕ, ∃ (Q : StandardSolution) (T : ℝ) (hT : 0 ≤ T), T ≤ Θ ∧
      ∃ (S : SolutionOn (I := ThreeModel) (M := standardCapWindow D)
        (RealTimeInterval.closed 0 T hT)), IsSolutionOn S ∧
      (∀ τ ∈ Icc 0 T, ∀ i ≤ n, ∀ v : standardCapWindow D,
        metricDerivNorm i (S.base.metric τ)
          ((Q.val.metric τ).restrictOpen (standardCapWindow D))
          (StandardCap.metric.restrictOpen (standardCapWindow D)) v < 1 / ((n : ℝ) + 1)) ∧
      ∃ (o : TangentOrientationSection (standardCapWindow D)) (z : standardCapWindow D),
        ‖z.val‖ < r ∧ τQ ≤ T * S.scalar T z ∧
          ¬ OrientedWitness S o δ standardModelKappa z T := by
    intro n
    by_contra h
    refine hcon ⟨n, 1 / ((n : ℝ) + 1), hrD, by positivity, ?_⟩
    intro Q T hT hTΘ S hS hcl o z hz hag
    by_contra hw
    exact h ⟨Q, T, hT, hTΘ, S, hS, hcl, o, z, hz, hag, hw⟩
  choose Q T hT0 hTΘ S hS hcl o z hz hag hw using hex
  obtain ⟨p, hp, φ, hφ, hlim⟩ := ((isCompact_Icc (a := (0 : ℝ)) (b := Θ)).prod
    (isCompact_closedBall (0 : ThreeSpace) r)).tendsto_subseq (x := fun n => (T n, (z n).val))
    fun n => ⟨⟨hT0 n, hTΘ n⟩, mem_closedBall_zero_iff.mpr (hz n).le⟩
  obtain ⟨ρ, hρ, Q', hQ'⟩ := StandardSolution.exists_subseq_tendsto hΘ (Q ∘ φ)
  have hψ : StrictMono (φ ∘ ρ) := hφ.comp hρ
  have hTψ : Tendsto (fun n => T (φ (ρ n))) atTop (𝓝 p.1) :=
    ((continuous_fst.tendsto p).comp hlim).comp hρ.tendsto_atTop
  have hzr : ‖p.2‖ ≤ r := mem_closedBall_zero_iff.mp hp.2
  let z₀ : standardCapWindow D := ⟨p.2, show ‖p.2‖ < D + 1 by linarith⟩
  have hzψ : Tendsto (fun n => z (φ (ρ n))) atTop (𝓝 z₀) :=
    tendsto_subtype_rng.mpr (((continuous_snd.tendsto p).comp hlim).comp hρ.tendsto_atTop)
  have hcloseψ := eventually_forall_metricDerivNorm_lt_of_tendsto
    (g := fun n τ => (S (φ (ρ n))).base.metric τ)
    (h := fun n τ => ((Q (φ (ρ n))).val.metric τ).restrictOpen (standardCapWindow D))
    (A := fun n => Icc 0 (T (φ (ρ n)))) (N := fun n => φ (ρ n))
    (ε := fun n => 1 / (((φ (ρ n) : ℕ) : ℝ) + 1)) hψ.tendsto_atTop
    (tendsto_one_div_add_atTop_nhds_zero_nat.comp hψ.tendsto_atTop)
    fun n => hcl (φ (ρ n))
  have hTmem : ∀ n, T (φ (ρ n)) ∈ Icc 0 Θ := fun n => ⟨hT0 _, hTΘ _⟩
  have hscal := tendsto_scalar_of_standard_close hΘ (hQ' D) hTmem hTψ
    (g := fun n => (S (φ (ρ n))).base.metric (T (φ (ρ n))))
    (fun p e he => (hcloseψ p e he).mono fun n hn i hi v =>
      hn _ ⟨hT0 _, le_rfl⟩ i hi v) hzψ
  have hagelim : τQ ≤ p.1 * Q'.val.toSolutionOn.scalar p.1 z₀.val :=
    ge_of_tendsto (hTψ.mul hscal) (Eventually.of_forall fun n => hag (φ (ρ n)))
  have hp1 : p.1 ∈ Icc 0 Θ := isClosed_Icc.mem_of_tendsto hTψ (Eventually.of_forall hTmem)
  have hp1lt : p.1 < 1 := hp1.2.trans_lt hΘ
  have hRpos : 0 < Q'.val.toSolutionOn.scalar p.1 z₀.val := by
    by_contra hneg
    have := mul_nonpos_of_nonneg_of_nonpos hp1.1 (le_of_not_gt hneg)
    linarith
  have hT₀ : 0 < p.1 := by
    rcases hp1.1.eq_or_lt with h0 | h0
    · rw [← h0, zero_mul] at hagelim
      linarith
    · exact h0
  have hR1 : 1 ≤ Q'.val.toSolutionOn.scalar p.1 z₀.val := by
    have := mul_le_mul_of_nonneg_right hp1lt.le hRpos.le
    linarith
  have hfin := eventually_orientedWitness_of_standard_close_endpoint hδ hδ1 hΘ (hQ' D)
    (fun n => hT0 (φ (ρ n))) (fun n => S (φ (ρ n))) (fun n => hS _) (fun n => hTΘ _)
    hcloseψ hTψ hzψ (fun o => hage Q' o z₀.val p.1 hp1.1 hp1lt hagelim) hT₀ hR1 hΛ1
    (hΛ Q' p.1 hp1) hzr le_rfl
  obtain ⟨n, hn⟩ := hfin.exists
  exact hw (φ (ρ n)) (hn (o (φ (ρ n))))

end Core

end DifferentialGeometry.PDE.RicciFlow
