import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.Scalar.Localized
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Distance.LocalCutoff
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Distance.LocalRicciBound
import DifferentialGeometry.Geometry.Curvature.ScalarNormBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Scalar.IntrinsicDerivation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Regularity

noncomputable section

open Bundle Filter Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Analysis.Parabolic
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [T2Space M]

private theorem scalar_trace_norm_bound
    [NeZero (Module.finrank ℝ E)]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (t : ℝ) (x : M) :
    (1 / (Module.finrank ℝ E : ℝ)) * S.scalar t x ^ 2 ≤
      normSq0S (I := I) (S.base.metric t) x 2 (S.ricci t x) := by
  classical
  let : Nonempty (CoordinateIdx (𝕜 := ℝ) E) :=
    ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne _)⟩⟩
  let basis := coordinateFrameAtToBasis (I := I) x
  let gInv := fun k l => inverseMetricFlatModelInChartComponent
    (I := I) (S.family.metric t) x k l (extChartAt I x x)
  have hinv : MetricInverseInBasisGen (I := I) (S.family.metric t) x basis gInv :=
    inverseMetricFlatModelInChart_metricInverseInBasis_center (I := I) (S.family.metric t) x
  have h := metricTracePair0SAt_sq_div_rank_le_normSq0S
    (I := I) (S.family.metric t) basis gInv hinv (S.ricci t x)
  rw [SolutionOn.scalar_eq_metricTrace]
  simpa only [CoordinateIdx, Fintype.card_fin, SolutionOn.family_metric, SolutionOn.ricci,
    SolutionFamily.ricci_apply, SolutionOn.ricciAt] using h

theorem scalar_parabolic_inequality_of_isSolution
    [I.Boundaryless] [NeZero (Module.finrank ℝ E)]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {t : ℝ} (ht : 0 < t) (hregular : t ∈ D.regular)
    (hslab : Icc 0 t ⊆ D.carrier) (x : M) :
    (2 / (Module.finrank ℝ E : ℝ)) * S.scalar t x ^ 2 ≤
      parabolicOperatorWithDrift (I := I) (flowG (I := I) S) t
        (fun _ y => (0 : TangentSpace I y)) S.scalar t x := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let : IsManifold I 1 M := IsManifold.of_le (I := I) (M := M)
    (n := (∞ : WithTop ℕ∞)) (by decide)
  have hderiv := ((scalar_curvature_evolution (I := I) S hS
    (⟨t, hregular⟩ : D.RegularTime) x).mono hslab).derivWithin
      ((uniqueDiffOn_Icc ht) t ⟨ht.le, le_rfl⟩)
  have htrace := scalar_trace_norm_bound S t x
  unfold parabolicOperatorWithDrift heatOperatorWithDrift
  rw [hderiv]
  have hzero : driftTerm (I := I) (flowG (I := I) S) t
      (fun y => (0 : TangentSpace I y)) (S.scalar t) x = 0 := by
    simp [driftTerm]
  rw [hzero]
  have hscaled := mul_le_mul_of_nonneg_left htrace (show (0 : ℝ) ≤ 2 by norm_num)
  change _ ≤ laplacianAt (I := I) (flowG (I := I) S) t (S.scalar t) x +
    2 * normSq0S (I := I) (S.base.metric t) x 2 (S.ricci t x) -
    (laplacianAt (I := I) (flowG (I := I) S) t (S.scalar t) x + 0)
  rw [show (2 : ℝ) / (Module.finrank ℝ E : ℝ) =
    2 * (1 / (Module.finrank ℝ E : ℝ)) by ring]
  nlinarith only [hscaled]


private theorem scalar_curvature_lower_bound_of_compactly_supported_cutoff
    [I.Boundaryless] [NeZero (Module.finrank ℝ E)]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {T δ ε : ℝ} (hT : 0 ≤ T) (herror : 0 ≤ δ + 2 * ε)
    (hslab : Icc 0 T ⊆ D.carrier) (hregular : Ioc 0 T ⊆ D.regular)
    (χ : ℝ → M → ℝ) (K : Set M) (hK : IsCompact K)
    (hχ : ∀ t ∈ Icc 0 T, ∀ x, χ t x ∈ Icc 0 1)
    (hsupport : ∀ t ∈ Icc 0 T, ∀ x ∉ K, χ t x = 0)
    (hcont : ContinuousOn (fun p : ℝ × M => χ p.1 p.2) (Icc 0 T ×ˢ K))
    (hcut : ∀ t ∈ Ioc 0 T, ∀ x, 0 < χ t x → S.scalar t x < 0 →
      ∃ φ : ℝ → M → ℝ,
        φ t x = χ t x ∧
        (∀ᶠ p in 𝓝[Icc 0 t ×ˢ (Set.univ : Set M)] (t, x), φ p.1 p.2 ≤ χ p.1 p.2) ∧
        DifferentiableWithinAt ℝ (fun s => φ s x) (Icc 0 t) t ∧
        (∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (φ t) y) ∧
        MDiffAt (T% fun y => gradientFun (I := I) (S.base.metric t) (φ t) y) x ∧
        parabolicOperatorWithDrift (I := I) (flowG (I := I) S) t
          (fun _ y => (0 : TangentSpace I y)) φ t x ≤ δ ∧
        (S.base.metric t).inner x (gradientFun (I := I) (S.base.metric t) (φ t) x)
          (gradientFun (I := I) (S.base.metric t) (φ t) x) ≤ ε * φ t x) :
    ∀ t ∈ Icc 0 T, ∀ x,
      -((Module.finrank ℝ E : ℝ) / 2) * (1 + T * (δ + 2 * ε)) ≤
        t * (χ t x * S.scalar t x) := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let : IsManifold I 1 M := IsManifold.of_le (I := I) (M := M)
    (n := (∞ : WithTop ℕ∞)) (by decide)
  have hn : 0 < (Module.finrank ℝ E : ℝ) :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne _))
  have hureg := scalarRegOfSol (I := I) S hS
  have hucont := hureg.scalar_continuousOn.mono (Set.prod_mono hslab Set.Subset.rfl)
  have hcontprod : ContinuousOn
      (fun p : ℝ × M => p.1 * (χ p.1 p.2 * S.scalar p.1 p.2)) (Icc 0 T ×ˢ K) :=
    continuous_fst.continuousOn.mul (hcont.mul
      (hucont.mono (Set.prod_mono Set.Subset.rfl (Set.subset_univ K))))
  have hsmall : ∀ t ∈ Icc 0 T, Icc 0 t ⊆ D.carrier := by
    intro t ht s hs
    exact hslab ⟨hs.1, hs.2.trans ht.2⟩
  have hbound := cutoff_quadratic_lower_bound_on_compact_support
    (flowG (I := I) S) (fun _ y => (0 : TangentSpace I y)) hT (div_pos two_pos hn)
    herror χ S.scalar K hK hχ hsupport hcontprod hucont
    (fun t ht x => hureg.scalar_time_within (K := Icc 0 t) (show t ∈ Icc 0 t from ⟨ht.1.le, le_rfl⟩) (hsmall t (show t ∈ Icc 0 T from ⟨ht.1.le, ht.2⟩)) x)
    (fun t ht x => hureg.scalar_space t (hslab ⟨ht.1.le, ht.2⟩) x)
    (fun t ht x => hureg.scalar_grad t (hslab ⟨ht.1.le, ht.2⟩) x)
    (fun t ht x => scalar_parabolic_inequality_of_isSolution S hS ht.1
      (hregular ht) (hsmall t ⟨ht.1.le, ht.2⟩) x) hcut
  intro t ht x
  have hcoef : -(1 + T * (δ + 2 * ε)) / (2 / (Module.finrank ℝ E : ℝ)) =
      -((Module.finrank ℝ E : ℝ) / 2) * (1 + T * (δ + 2 * ε)) := by
    field_simp
  rw [← hcoef]
  exact hbound t ht x

end DifferentialGeometry.PDE.RicciFlow

end

noncomputable section

open Bundle Filter Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Analysis.Parabolic
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

private theorem scalar_curvature_distance_cutoff_bound
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) {T R K C a : ℝ} (hT : 0 ≤ T)
    (hslab : Icc 0 T ⊆ D.carrier) (hregular : Ioc 0 T ⊆ D.regular)
    (hcomplete : ∀ t ∈ Icc 0 T, RiemannianMetricComplete (I := I) (S.base.metric t))
    (O : M) (hR : 0 < R) (hK : 0 ≤ K)
    (hRic : ∀ t ∈ Ioc 0 T, ∀ y : M,
      riemannianEDistOf (I := I) (S.base.metric t) O y < ENNReal.ofReal R →
      ∀ v : TangentSpace I y, ricciTensor (I := I) (S.base.metric t) y v v ≤
        K * (S.base.metric t).inner y v v)
    (ha : 0 < a) (haR : a * R < 1) (hC : 0 ≤ C)
    (hprofile : ∀ s : ℝ, (deriv Analysis.CutoffProfile.value s) ^ 2 ≤ C * Analysis.CutoffProfile.value s) :
    -((Module.finrank ℝ E : ℝ) / 2) *
      (1 + T * (Analysis.CutoffProfile.derivBound *
        (a * (2 * (Module.finrank ℝ E - 1 : ℝ) * Analysis.CutoffProfile.derivBound ^ 2 / R +
          K * R) + a ^ 2) + 2 * (C * a ^ 2))) ≤ T * S.scalar T O := by
  let χ : ℝ → M → ℝ := fun s y => Analysis.CutoffProfile.evalue
    (ENNReal.ofReal a * riemannianEDistOf (I := I) (S.base.metric s) O y)
  let δ := Analysis.CutoffProfile.derivBound *
    (a * (2 * (Module.finrank ℝ E - 1 : ℝ) * Analysis.CutoffProfile.derivBound ^ 2 / R +
      K * R) + a ^ 2)
  let ε := C * a ^ 2
  have hn : (1 : ℝ) ≤ Module.finrank ℝ E := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne (Module.finrank ℝ E))
  have hδ : 0 ≤ δ := by
    apply mul_nonneg Analysis.CutoffProfile.derivBound_nonneg
    apply add_nonneg _ (sq_nonneg a)
    exact mul_nonneg ha.le (add_nonneg
      (div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hn))
        (sq_nonneg _)) hR.le) (mul_nonneg hK hR.le))
  have hε : 0 ≤ ε := mul_nonneg hC (sq_nonneg a)
  obtain ⟨L, hL, hsupport⟩ := exists_compact_distance_cutoff_support S.base.metric
    hS.smoothMetric.metricTensor_cont isCompact_Icc hslab hcomplete O ha
  have hcont := continuousOn_distance_cutoff S.base.metric ordConnected_Icc
    (hS.smoothMetric.metricTensor_cont.mono hslab) hcomplete O a
  have hbound := scalar_curvature_lower_bound_of_compactly_supported_cutoff S hS hT
    (show 0 ≤ δ + 2 * ε from add_nonneg hδ (mul_nonneg (by norm_num) hε))
    hslab hregular χ L hL (fun s hs y => Analysis.CutoffProfile.evalue_mem_Icc _)
    hsupport (hcont.mono (Set.prod_mono Set.Subset.rfl (Set.subset_univ L)))
    (fun s hs y _ _ => distance_cutoff_lower_support_with_gradient_ratio S hS (hregular hs)
      hs.1 (hcomplete s ⟨hs.1.le, hs.2⟩) O hR hK (hRic s hs) ha.le haR hprofile y)
  have hself : χ T O = 1 := by
    simp only [χ, riemannianEDistOf_self, mul_zero]
    exact Analysis.CutoffProfile.evalue_one_of_le (by norm_num)
  simpa only [hself, one_mul, δ, ε] using hbound T ⟨hT, le_rfl⟩ O


private theorem scalar_curvature_lower_bound_of_local_ricci_bound
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) {T R K : ℝ} (hT : 0 ≤ T)
    (hslab : Icc 0 T ⊆ D.carrier) (hregular : Ioc 0 T ⊆ D.regular)
    (hcomplete : ∀ t ∈ Icc 0 T, RiemannianMetricComplete (I := I) (S.base.metric t))
    (O : M) (hR : 0 < R) (hK : 0 ≤ K)
    (hRic : ∀ t ∈ Ioc 0 T, ∀ y : M,
      riemannianEDistOf (I := I) (S.base.metric t) O y < ENNReal.ofReal R →
      ∀ v : TangentSpace I y, ricciTensor (I := I) (S.base.metric t) y v v ≤
        K * (S.base.metric t).inner y v v) :
    -((Module.finrank ℝ E : ℝ) / 2) ≤ T * S.scalar T O := by
  obtain ⟨C, hC, hprofile⟩ := Analysis.CutoffProfile.exists_deriv_sq
  let F : ℝ → ℝ := fun a => -((Module.finrank ℝ E : ℝ) / 2) *
    (1 + T * (Analysis.CutoffProfile.derivBound *
      (a * (2 * (Module.finrank ℝ E - 1 : ℝ) * Analysis.CutoffProfile.derivBound ^ 2 / R +
        K * R) + a ^ 2) + 2 * (C * a ^ 2)))
  have hF : Continuous F := by dsimp only [F]; fun_prop
  have hsmall : ∀ᶠ a : ℝ in 𝓝[>] 0, 0 < a ∧ a * R < 1 := by
    have hmul : ∀ᶠ a : ℝ in 𝓝 0, a * R < 1 :=
      (continuousAt_id.mul continuousAt_const).eventually
        (Iio_mem_nhds (by norm_num : (0 : ℝ) * R < 1))
    filter_upwards [self_mem_nhdsWithin, hmul.filter_mono nhdsWithin_le_nhds] with a ha hamul
    exact ⟨ha, hamul⟩
  have hbound : ∀ᶠ a : ℝ in 𝓝[>] 0, F a ≤ T * S.scalar T O := by
    filter_upwards [hsmall] with a ha
    exact scalar_curvature_distance_cutoff_bound S hS hT hslab hregular hcomplete
      O hR hK hRic ha.1 ha.2 hC hprofile
  have hlim : Tendsto F (𝓝[>] 0) (𝓝 (-((Module.finrank ℝ E : ℝ) / 2))) := by
    simpa only [F, zero_mul, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero, mul_zero,
      mul_one] using (hF.continuousAt (x := (0 : ℝ))).tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  exact le_of_tendsto hlim hbound


omit [NeZero (Module.finrank ℝ E)] in
private theorem scalar_curvature_lower_bound_of_regular_endpoint
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) {T : ℝ} (hT : 0 ≤ T)
    (hslab : Icc 0 T ⊆ D.carrier) (hregular : Ioc 0 T ⊆ D.regular)
    (hcomplete : ∀ t ∈ Icc 0 T, RiemannianMetricComplete (I := I) (S.base.metric t))
    (x : M) :
    -((Module.finrank ℝ E : ℝ) / 2) ≤ T * S.scalar T x := by
  by_cases hn : Module.finrank ℝ E = 0
  · have hscalar : S.scalar T x = 0 := metricScalarAt_eq_zero_of_finrank_eq_zero
      (I := I) (S.base.metric T) hn x
    simp only [hn, Nat.cast_zero, zero_div, neg_zero, hscalar, mul_zero, le_refl]
  · let _ : NeZero (Module.finrank ℝ E) := ⟨hn⟩
    obtain ⟨K, hK, hRic⟩ := exists_ricci_bound_on_distance_ball_on_compact S hS
      isCompact_Icc hslab hcomplete x 1
    exact scalar_curvature_lower_bound_of_local_ricci_bound S hS hT hslab hregular hcomplete
      x (show (0 : ℝ) < 1 by norm_num) hK
      (fun t ht y hy v => (le_abs_self _).trans (hRic t ⟨ht.1.le, ht.2⟩ y hy.le v))


private theorem scalar_product_bound_at_right_endpoint
    {M : Type*} [TopologicalSpace M] (u : ℝ → M → ℝ)
    {J : Set ℝ}
    (hu : ContinuousOn (fun p : ℝ × M => u p.1 p.2) (J ×ˢ (univ : Set M)))
    {T : ℝ} (hT : 0 < T) (hslab : Icc 0 T ⊆ J) (x : M) (c : ℝ)
    (hbound : ∀ t ∈ Ioo 0 T, c ≤ t * u t x) :
    c ≤ T * u T x := by
  have hmap : Continuous (fun t : ℝ => (t, x)) :=
    continuous_id.prodMk continuous_const
  have hcont : ContinuousOn (fun t : ℝ => u t x) (Icc 0 T) :=
    hu.comp hmap.continuousOn (fun t ht => ⟨hslab ht, Set.mem_univ x⟩)
  have hclosure : closure (Ioo 0 T) = Icc 0 T := closure_Ioo hT.ne
  have hprod : ContinuousOn (fun t : ℝ => t * u t x) (closure (Ioo 0 T)) := by
    rw [hclosure]
    exact continuousOn_id.mul hcont
  have hmem : T ∈ closure (Ioo 0 T) := by
    rw [hclosure]
    exact ⟨hT.le, le_rfl⟩
  exact le_on_closure hbound continuousOn_const hprod hmem

omit [NeZero (Module.finrank ℝ E)] in
theorem scalar_curvature_lower_bound_of_complete
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) {T : ℝ} (hT : 0 ≤ T)
    (hslab : Icc 0 T ⊆ D.carrier) (hregular : Ioo 0 T ⊆ D.regular)
    (hcomplete : ∀ t ∈ Icc 0 T, RiemannianMetricComplete (I := I) (S.base.metric t))
    (x : M) :
    -((Module.finrank ℝ E : ℝ) / 2) ≤ T * S.scalar T x := by
  by_cases hzero : T = 0
  · rw [hzero, zero_mul]
    exact neg_nonpos.mpr (div_nonneg (Nat.cast_nonneg _) (by norm_num))
  have hTpos : 0 < T := lt_of_le_of_ne hT (Ne.symm hzero)
  have hbound : ∀ t ∈ Ioo 0 T,
      -((Module.finrank ℝ E : ℝ) / 2) ≤ t * S.scalar t x := by
    intro t ht
    exact scalar_curvature_lower_bound_of_regular_endpoint (I := I) S hS ht.1.le
      (fun s hs => hslab ⟨hs.1, hs.2.trans ht.2.le⟩)
      (fun s hs => hregular ⟨hs.1, hs.2.trans_lt ht.2⟩)
      (fun s hs => hcomplete s ⟨hs.1, hs.2.trans ht.2.le⟩) x
  exact scalar_product_bound_at_right_endpoint S.scalar hS.scalarCont hTpos hslab x _ hbound


omit [NeZero (Module.finrank ℝ E)] in
theorem scalar_curvature_lower_bound_on_interval_of_complete
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) {a b : ℝ} (hab : a ≤ b)
    (hslab : Icc a b ⊆ D.carrier) (hregular : Ioo a b ⊆ D.regular)
    (hcomplete : ∀ t ∈ Icc a b, RiemannianMetricComplete (I := I) (S.base.metric t))
    (x : M) :
    -((Module.finrank ℝ E : ℝ) / 2) ≤ (b - a) * S.scalar b x := by
  have hslab' : Icc 0 (b - a) ⊆ (D.timeShift a).carrier := by
    intro t ht
    apply hslab
    constructor <;> linarith [ht.1, ht.2]
  have hreg' : Ioo 0 (b - a) ⊆ (D.timeShift a).regular := by
    intro t ht
    apply hregular
    constructor <;> linarith [ht.1, ht.2]
  have hcomplete' : ∀ t ∈ Icc 0 (b - a),
      RiemannianMetricComplete (I := I) ((S.timeShift a).base.metric t) := by
    intro t ht
    apply hcomplete
    constructor <;> linarith [ht.1, ht.2]
  simpa only [SolutionOn.timeShift_scalar, sub_add_cancel] using
    scalar_curvature_lower_bound_of_complete (S.timeShift a) (isSolutionOn_timeShift hS a)
      (sub_nonneg.mpr hab) hslab' hreg' hcomplete' x

omit [NeZero (Module.finrank ℝ E)] in
theorem scalar_curvature_ge_neg_dim_div_two_time_of_complete
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) {a b : ℝ} (hab : a < b)
    (hslab : Icc a b ⊆ D.carrier) (hregular : Ioo a b ⊆ D.regular)
    (hcomplete : ∀ t ∈ Icc a b, RiemannianMetricComplete (I := I) (S.base.metric t))
    (x : M) :
    -(Module.finrank ℝ E : ℝ) / (2 * (b - a)) ≤ S.scalar b x := by
  have h := scalar_curvature_lower_bound_on_interval_of_complete S hS hab.le hslab hregular hcomplete x
  apply (div_le_iff₀ (mul_pos two_pos (sub_pos.mpr hab))).2
  linarith only [h]

end DifferentialGeometry.PDE.RicciFlow

end
