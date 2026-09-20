import DifferentialGeometry.Geometry.Operator.Gradient.LipschitzBound
import DifferentialGeometry.Geometry.Comparison.DistanceFamily
import DifferentialGeometry.Analysis.Calculus.Cutoff.Profile

noncomputable section

open Set
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

theorem exists_compact_distance_cutoff_support
    (g : ℝ → SmoothRiemannianMetric I M) {J : Set ℝ}
    (hg : tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 J
      (fun t x => Tensor0SBundle.metricTensorField (I := I) (g t) x))
    {K : Set ℝ} (hK : IsCompact K) (hKJ : K ⊆ J)
    (hcomplete : ∀ t ∈ K, RiemannianMetricComplete (I := I) (g t))
    (O : M) {a : ℝ} (ha : 0 < a) :
    ∃ L : Set M, IsCompact L ∧
      ∀ t ∈ K, ∀ x ∉ L, Analysis.CutoffProfile.evalue
        (ENNReal.ofReal a * riemannianEDistOf (I := I) (g t) O x) = 0 := by
  obtain ⟨L, hL, hcover⟩ := exists_compact_riemannianEDistOf_le_of_isCompact
    (I := I) g hg hK hKJ hcomplete O (2 / a)
  refine ⟨L, hL, ?_⟩
  intro t ht x hx
  have hdist : ENNReal.ofReal (2 / a) ≤ riemannianEDistOf (I := I) (g t) O x := by
    by_contra hn
    exact hx (hcover t ht x (le_of_not_ge hn))
  apply Analysis.CutoffProfile.evalue_zero_of_ge
  have hmul := mul_le_mul_right hdist (ENNReal.ofReal a)
  rw [← ENNReal.ofReal_mul ha.le] at hmul
  have hcoef : a * (2 / a) = 2 := by field_simp
  simpa only [hcoef, ENNReal.ofReal_ofNat] using hmul

theorem continuousOn_distance_cutoff
    (g : ℝ → SmoothRiemannianMetric I M) {J : Set ℝ} (hJ : J.OrdConnected)
    (hg : tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 J
      (fun t x => Tensor0SBundle.metricTensorField (I := I) (g t) x))
    (hcomplete : ∀ t ∈ J, RiemannianMetricComplete (I := I) (g t))
    (O : M) (a : ℝ) :
    ContinuousOn (fun p : ℝ × M => Analysis.CutoffProfile.evalue
      (ENNReal.ofReal a * riemannianEDistOf (I := I) (g p.1) O p.2))
      (J ×ˢ (Set.univ : Set M)) := by
  have hd := continuousOn_riemannianEDistOf (I := I) g hJ hg hcomplete O
  have hmul : Continuous (fun r : ENNReal => ENNReal.ofReal a * r) :=
    ENNReal.continuous_const_mul ENNReal.ofReal_ne_top
  exact Analysis.CutoffProfile.continuous_evalue.comp_continuousOn (hmul.comp_continuousOn hd)

omit [SigmaCompactSpace M] in
open scoped Bundle ENNReal NNReal in
open Geometry.Operator in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem grad_norm_distance_cutoff_le
    (g h : SmoothRiemannianMetric I M) (hgh : ∀ x v, g.inner x v v ≤ h.inner x v v)
    (o : M) (a : ℝ≥0) (x : M) :
    Real.sqrt (h.inner x
      (gradFun h (fun y => Analysis.CutoffProfile.evalue
        ((a : ℝ≥0∞) * riemannianEDistOf g o y)) x)
      (gradFun h (fun y => Analysis.CutoffProfile.evalue
        ((a : ℝ≥0∞) * riemannianEDistOf g o y)) x)) ≤ Analysis.CutoffProfile.derivBound * a := by
  let : LocallyCompactSpace M := _root_.Manifold.locallyCompact_of_finiteDimensional I
  let : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : PseudoEMetricSpace M := PseudoEMetricSpace.ofRiemannianMetric I M
  have hlip := Analysis.CutoffProfile.lipschitzWith_edist a o
  apply grad_norm_le_lip_all h (L := ⟨Analysis.CutoffProfile.derivBound,
    Analysis.CutoffProfile.derivBound_nonneg⟩ * a)
  intro y z
  exact (hlip y z).trans (mul_le_mul_right (edistOf_mono g h hgh y z) _)

omit [T2Space M] [SigmaCompactSpace M] in
open scoped ENNReal NNReal in
open Geometry.Operator in
theorem support_gradFun_distance_cutoff_subset
    (g h : SmoothRiemannianMetric I M) (o : M) (a : ℝ≥0) :
    Function.support (fun x => gradFun h (fun y => Analysis.CutoffProfile.evalue
        ((a : ℝ≥0∞) * riemannianEDistOf g o y)) x) ⊆
      {x | (a : ℝ≥0∞) * riemannianEDistOf g o x ∈ Set.Ioo 1 2} := by
  intro x hx
  let f : M → ℝ := fun y => Analysis.CutoffProfile.evalue
    ((a : ℝ≥0∞) * riemannianEDistOf g o y)
  have hd : MDifferentiableAt I 𝓘(ℝ, ℝ) f x := by
    by_contra hn
    exact hx (gradFun_eq_zero_of_mfderiv_eq_zero h f (mfderiv_zero_of_not_mdifferentiableAt hn))
  constructor
  · by_contra hn
    have hf : f x = 1 := Analysis.CutoffProfile.evalue_one_of_le (le_of_not_gt hn)
    have hmax : IsLocalMax f x := Filter.Eventually.of_forall fun y => by
      rw [hf]
      exact (Analysis.CutoffProfile.evalue_mem_Icc _).2
    exact hx (gradientFun_eq_zero_of_isLocalMax h hmax hd)
  · by_contra hn
    have hf : f x = 0 := Analysis.CutoffProfile.evalue_zero_of_ge (le_of_not_gt hn)
    have hmin : IsLocalMin f x := Filter.Eventually.of_forall fun y => by
      rw [hf]
      exact (Analysis.CutoffProfile.evalue_mem_Icc _).1
    exact hx (gradientFun_eq_zero_of_isLocalMin h hmin hd)

omit [SigmaCompactSpace M] in
open scoped ENNReal NNReal in
open Geometry.Operator in
theorem abs_inner_grad_distance_cutoff_le_of_linear_growth
    (g h : SmoothRiemannianMetric I M) (hgh : ∀ x v, g.inner x v v ≤ h.inner x v v)
    (o : M) (a C : ℝ≥0) (x : M) (v : TangentSpace I x) {w : ℝ} (hw : 0 ≤ w)
    (hv : Real.sqrt (h.inner x v v) ≤ C * (1 + (riemannianEDistOf g o x).toReal) * w) :
    |h.inner x v (gradFun h (fun y => Analysis.CutoffProfile.evalue
      ((a : ℝ≥0∞) * riemannianEDistOf g o y)) x)| ≤
        Analysis.CutoffProfile.derivBound * C * (a + 2) * w := by
  let f : M → ℝ := fun y => Analysis.CutoffProfile.evalue
    ((a : ℝ≥0∞) * riemannianEDistOf g o y)
  by_cases hz : gradFun h f x = 0
  · change |h.inner x v (gradFun h f x)| ≤ _
    rw [hz, map_zero, abs_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg Analysis.CutoffProfile.derivBound_nonneg C.coe_nonneg)
      (by positivity)) hw
  have hs := support_gradFun_distance_cutoff_subset g h o a hz
  have hr : (a : ℝ) * (riemannianEDistOf g o x).toReal < 2 := by
    have hp : (a : ℝ≥0∞) * riemannianEDistOf g o x ≠ ⊤ :=
      ne_top_of_le_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) hs.2.le
    have hh := (ENNReal.toReal_lt_toReal hp (by norm_num)).mpr hs.2
    simpa only [ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.toReal_ofNat] using hh
  have hc := grad_norm_distance_cutoff_le g h hgh o a x
  calc
    _ ≤ Real.sqrt (h.inner x v v) *
        Real.sqrt (h.inner x (gradFun h f x) (gradFun h f x)) :=
      abs_inner_le_sqrt_mul_sqrt h x v (gradFun h f x)
    _ ≤ (C * (1 + (riemannianEDistOf g o x).toReal) * w) *
        (Analysis.CutoffProfile.derivBound * a) :=
      mul_le_mul hv hc (Real.sqrt_nonneg _) (by positivity)
    _ = Analysis.CutoffProfile.derivBound * C *
        (a + a * (riemannianEDistOf g o x).toReal) * w := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (add_le_add_right hr.le _) (by
        exact mul_nonneg Analysis.CutoffProfile.derivBound_nonneg C.coe_nonneg)) hw

section
open Filter
open scoped ENNReal NNReal Topology Bundle

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem hasCompactSupport_distance_cutoff
    (g : SmoothRiemannianMetric I M) (hg : RiemannianMetricComplete g) (o : M)
    {a : ℝ≥0} (ha : 0 < a) :
    HasCompactSupport (fun x => Analysis.CutoffProfile.evalue
      ((a : ℝ≥0∞) * riemannianEDistOf g o x)) := by
  by_cases hdim : Module.finrank ℝ E = 0
  · let _ : Subsingleton E := Module.finrank_zero_iff.mp hdim
    let _ : Subsingleton H := I.injective.subsingleton
    let _ : DiscreteTopology M := ChartedSpace.discreteTopology H M
    let _ : Bundle.RiemannianBundle (fun y : M => TangentSpace I y) := ⟨g.toRiemannianMetric⟩
    apply (isCompact_singleton (x := o)).of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal _ isClosed_singleton
    intro x hx
    have hfin : riemannianEDistOf g o x ≠ ⊤ := by
      intro htop
      apply hx
      apply Analysis.CutoffProfile.evalue_zero_of_ge
      rw [htop, ENNReal.mul_top (by exact_mod_cast ha.ne')]
      exact le_top
    have hfin' : _root_.Manifold.riemannianEDist I o x < ⊤ := lt_top_iff_ne_top.mpr hfin
    obtain ⟨γ, hγ0, hγ1, hγ, _⟩ :=
      _root_.Manifold.exists_lt_locally_constant_of_riemannianEDist_lt hfin' zero_lt_one
    have hox : o = x := by
      rw [← hγ0, ← hγ1]
      exact TotallyDisconnectedSpace.eq_of_continuous γ hγ.continuous 0 1
    exact mem_singleton_iff.mpr hox.symm
  · let _ : NeZero (Module.finrank ℝ E) := ⟨hdim⟩
    have haR : (0 : ℝ) < a := ha
    have hK := hg.closedEBall_isCompact o (2 / (a : ℝ))
    apply hK.of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal _ hK.isClosed
    intro x hx
    by_contra hn
    have hd : ENNReal.ofReal (2 / (a : ℝ)) ≤ riemannianEDistOf g o x :=
      (not_le.mp hn).le
    apply hx
    apply Analysis.CutoffProfile.evalue_zero_of_ge
    have hmul := mul_le_mul_right hd (a : ℝ≥0∞)
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul haR.le] at hmul
    have hcoef : (a : ℝ) * (2 / a) = 2 := by field_simp
    simpa only [hcoef, ENNReal.ofReal_ofNat, ENNReal.ofReal_coe_nnreal] using hmul

omit [I.Boundaryless] [SigmaCompactSpace M] in
theorem eventually_distance_cutoff_eq_one_on_isCompact
    [PreconnectedSpace M] (g : SmoothRiemannianMetric I M) (o : M)
    {K : Set M} (hK : IsCompact K) {ι : Type*} {l : Filter ι}
    (a : ι → ℝ≥0) (ha : Tendsto a l (𝓝 0)) :
    ∀ᶠ i in l, ∀ x ∈ K, Analysis.CutoffProfile.evalue
      ((a i : ℝ≥0∞) * riemannianEDistOf g o x) = 1 := by
  have hd : Continuous (fun x => (riemannianEDistOf g o x).toReal) :=
    continuous_iff_continuousAt.mpr fun x =>
      (ENNReal.continuousAt_toReal (riemannianEDistOf_ne_top g o x)).comp
        (continuous_riemannianEDist g o).continuousAt
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hd.continuousOn
  have haR : Tendsto (fun i => (a i : ℝ)) l (𝓝 0) :=
    NNReal.continuous_coe.continuousAt.tendsto.comp ha
  have hab : Tendsto (fun i => (a i : ℝ) * B) l (𝓝 0) := by
    simpa only [zero_mul] using haR.mul_const B
  filter_upwards [hab.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with i hi x hx
  apply Analysis.CutoffProfile.evalue_one_of_le
  apply (ENNReal.toReal_le_toReal
    (ENNReal.mul_ne_top ENNReal.coe_ne_top (riemannianEDistOf_ne_top g o x)) ENNReal.one_ne_top).mp
  simp only [ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.toReal_one]
  have hxB : (riemannianEDistOf g o x).toReal ≤ B := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg] using hB x hx
  exact (mul_le_mul_of_nonneg_left hxB (a i).coe_nonneg).trans hi.le

omit [I.Boundaryless] [SigmaCompactSpace M] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem edist_distance_cutoff_le
    (g : SmoothRiemannianMetric I M) (o : M) (a : ℝ≥0) (x y : M) :
    edist (Analysis.CutoffProfile.evalue ((a : ℝ≥0∞) * riemannianEDistOf g o x))
      (Analysis.CutoffProfile.evalue ((a : ℝ≥0∞) * riemannianEDistOf g o y)) ≤
      (⟨Analysis.CutoffProfile.derivBound, Analysis.CutoffProfile.derivBound_nonneg⟩ * a : ℝ≥0) *
        riemannianEDistOf g x y := by
  let : LocallyCompactSpace M := _root_.Manifold.locallyCompact_of_finiteDimensional I
  let : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : PseudoEMetricSpace M := PseudoEMetricSpace.ofRiemannianMetric I M
  exact Analysis.CutoffProfile.lipschitzWith_edist a o x y


end

end DifferentialGeometry.Geometry.Riemannian
