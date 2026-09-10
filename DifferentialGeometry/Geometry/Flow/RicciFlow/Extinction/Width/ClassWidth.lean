import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.LeastArea
import Mathlib.Topology.Order.Compact
import DifferentialGeometry.Geometry.Metric.Family.Basic

noncomputable section

open Bundle Manifold Set MeasureTheory Topology
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Width

open Surgery.Topology

local instance sphereTwoNonempty : Nonempty (Sphere 2) :=
  (show (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1).Nonempty from
    NormedSpace.sphere_nonempty.mpr (by norm_num)).coe_sort

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [finiteDimensionalE : FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [boundarylessI : I.Boundaryless]
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
  [t2Q : T2Space Q] [compactQ : CompactSpace Q] [connectedQ : ConnectedSpace Q]

theorem regularFamily_area_bddAbove (g : SmoothRiemannianMetric I Q)
    (Γ : RegularFamily (I := I) (Q := Q) (Sphere 2)) :
    BddAbove (Set.range (fun k => regularLeastArea g (Γ k))) :=
  (isCompact_range ((continuous_regularLeastArea g).comp Γ.continuous)).bddAbove


def familyMaximum (g : SmoothRiemannianMetric I Q)
    (Γ : RegularFamily (I := I) (Q := Q) (Sphere 2)) : ℝ :=
  sSup (Set.range (fun k => regularLeastArea g (Γ k)))

theorem regularLeastArea_le_familyMaximum (g : SmoothRiemannianMetric I Q)
    (Γ : RegularFamily (I := I) (Q := Q) (Sphere 2)) (k : Sphere 2) :
    regularLeastArea g (Γ k) ≤ familyMaximum g Γ :=
  le_csSup (regularFamily_area_bddAbove g Γ) ⟨k, rfl⟩


theorem familyMaximum_attained (g : SmoothRiemannianMetric I Q)
    (Γ : RegularFamily (I := I) (Q := Q) (Sphere 2)) :
    ∃ k : Sphere 2, familyMaximum g Γ = regularLeastArea g (Γ k) := by
  obtain ⟨k, _, hk⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty
    (((continuous_regularLeastArea g).comp Γ.continuous).continuousOn)
  refine ⟨k, le_antisymm ?_ (regularLeastArea_le_familyMaximum g Γ k)⟩
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨p, rfl⟩
  exact hk (Set.mem_univ p)

theorem familyMaximum_nonneg (g : SmoothRiemannianMetric I Q)
    (Γ : RegularFamily (I := I) (Q := Q) (Sphere 2)) : 0 ≤ familyMaximum g Γ := by
  obtain ⟨k, hk⟩ := familyMaximum_attained g Γ
  rw [hk]
  exact regularLeastArea_nonneg g (Γ k)


def regularAreaMap (g : SmoothRiemannianMetric I Q) :
    C(ContractibleRegularLoop (I := I) (Q := Q), ℝ) :=
  ⟨regularLeastArea g, continuous_regularLeastArea g⟩


theorem familyMaximum_eq_norm (g : SmoothRiemannianMetric I Q)
    (Γ : RegularFamily (I := I) (Q := Q) (Sphere 2)) :
    familyMaximum g Γ = ‖(regularAreaMap g).comp Γ‖ := by
  apply le_antisymm
  · obtain ⟨k, hk⟩ := familyMaximum_attained g Γ
    rw [hk]
    exact (le_abs_self _).trans (((regularAreaMap g).comp Γ).norm_coe_le_norm k)
  · apply (ContinuousMap.norm_le _ (familyMaximum_nonneg g Γ)).mpr
    intro k
    simpa only [ContinuousMap.comp_apply, regularAreaMap, ContinuousMap.coe_mk,
      Real.norm_eq_abs, abs_of_nonneg (regularLeastArea_nonneg g (Γ k))] using
      regularLeastArea_le_familyMaximum g Γ k


theorem continuous_familyMaximum (g : SmoothRiemannianMetric I Q) :
    Continuous (familyMaximum g : RegularFamily (I := I) (Q := Q) (Sphere 2) → ℝ) := by
  have h : Continuous (fun Γ : RegularFamily (I := I) (Q := Q) (Sphere 2) =>
      ‖(regularAreaMap g).comp Γ‖) :=
    continuous_norm.comp (ContinuousMap.continuous_postcomp (regularAreaMap g))
  exact h.congr fun Γ => (familyMaximum_eq_norm g Γ).symm


def representativeMaxima (g : SmoothRiemannianMetric I Q)
    (ξ : FreeContractibleSphereClass Q) : Set ℝ :=
  Set.range (fun Γ : RegularRepresentative (I := I) ξ => familyMaximum g Γ.1)

theorem representativeMaxima_nonempty (g : SmoothRiemannianMetric I Q)
    (ξ : FreeContractibleSphereClass Q) : (representativeMaxima g ξ).Nonempty := by
  obtain ⟨Γ⟩ := regularRepresentative_nonempty (I := I) ξ
  exact ⟨familyMaximum g Γ.1, Γ, rfl⟩

theorem representativeMaxima_bddBelow (g : SmoothRiemannianMetric I Q)
    (ξ : FreeContractibleSphereClass Q) : BddBelow (representativeMaxima g ξ) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨Γ, rfl⟩
  exact familyMaximum_nonneg g Γ.1


def classWidth (g : SmoothRiemannianMetric I Q) (ξ : FreeContractibleSphereClass Q) : ℝ :=
  sInf (representativeMaxima g ξ)

theorem classWidth_nonneg (g : SmoothRiemannianMetric I Q)
    (ξ : FreeContractibleSphereClass Q) : 0 ≤ classWidth g ξ := by
  apply le_csInf (representativeMaxima_nonempty g ξ)
  rintro _ ⟨Γ, rfl⟩
  exact familyMaximum_nonneg g Γ.1

theorem classWidth_le_familyMaximum (g : SmoothRiemannianMetric I Q)
    (ξ : FreeContractibleSphereClass Q) (Γ : RegularRepresentative (I := I) ξ) :
    classWidth g ξ ≤ familyMaximum g Γ.1 :=
  csInf_le (representativeMaxima_bddBelow g ξ) ⟨Γ, rfl⟩


theorem familyMaximum_le_mul (g h : SmoothRiemannianMetric I Q) {c : ℝ} (hc : 0 ≤ c)
    (Γ : RegularFamily (I := I) (Q := Q) (Sphere 2))
    (hpoint : ∀ k, regularLeastArea h (Γ k) ≤ c * regularLeastArea g (Γ k)) :
    familyMaximum h Γ ≤ c * familyMaximum g Γ := by
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨k, rfl⟩
  exact (hpoint k).trans
    (mul_le_mul_of_nonneg_left (regularLeastArea_le_familyMaximum g Γ k) hc)


theorem classWidth_le_mul (g h : SmoothRiemannianMetric I Q) {c : ℝ} (hc : 0 < c)
    (ξ : FreeContractibleSphereClass Q)
    (hfamily : ∀ Γ : RegularRepresentative (I := I) ξ,
      familyMaximum h Γ.1 ≤ c * familyMaximum g Γ.1) :
    classWidth h ξ ≤ c * classWidth g ξ := by
  have hlower : classWidth h ξ / c ≤ classWidth g ξ := by
    apply le_csInf (representativeMaxima_nonempty g ξ)
    rintro _ ⟨Γ, rfl⟩
    apply (div_le_iff₀ hc).mpr
    simpa only [mul_comm] using (classWidth_le_familyMaximum h ξ Γ).trans (hfamily Γ)
  have h := (div_le_iff₀ hc).mp hlower
  simpa only [mul_comm] using h


theorem exists_representative_maximum_lt (g : SmoothRiemannianMetric I Q)
    (ξ : FreeContractibleSphereClass Q) {η : ℝ} (hη : 0 < η) :
    ∃ Γ : RegularRepresentative (I := I) ξ, familyMaximum g Γ.1 < classWidth g ξ + η := by
  obtain ⟨a, ⟨Γ, rfl⟩, hΓ⟩ := exists_lt_of_csInf_lt
    (representativeMaxima_nonempty g ξ)
    (show sInf (representativeMaxima g ξ) < classWidth g ξ + η from
      lt_add_of_pos_right _ hη)
  exact ⟨Γ, hΓ⟩


def nullFamilyClass (q : Q) : FreeContractibleSphereClass Q :=
  FreeHomotopyClass.mk (ContinuousMap.const (Sphere 2)
    (⟨constantLoops q, isContractibleLoop_constant q⟩ : ContractibleContinuousLoop Q))

def constantRegularRepresentative (q : Q) : RegularRepresentative (I := I) (nullFamilyClass q) :=
  ⟨ContinuousMap.const (Sphere 2) (constantContractibleRegularLoop q), rfl⟩

omit connectedQ in
theorem regularLeastArea_constant (g : SmoothRiemannianMetric I Q) (q : Q) :
    regularLeastArea g (constantContractibleRegularLoop q) = 0 :=
  leastArea_const g q

omit connectedQ in
theorem familyMaximum_constant (g : SmoothRiemannianMetric I Q) (q : Q) :
    familyMaximum g (constantRegularRepresentative (I := I) q).1 = 0 := by
  unfold familyMaximum constantRegularRepresentative
  simp only [ContinuousMap.const_apply, regularLeastArea_constant, Set.range_const, csSup_singleton]


theorem classWidth_null (g : SmoothRiemannianMetric I Q) (q : Q) :
    classWidth g (nullFamilyClass q) = 0 := by
  apply le_antisymm
  · simpa only [familyMaximum_constant] using
      classWidth_le_familyMaximum g (nullFamilyClass q) (constantRegularRepresentative q)
  · exact classWidth_nonneg g (nullFamilyClass q)

theorem rfs_width_finiteness (g : SmoothRiemannianMetric I Q)
    (ξ : FreeContractibleSphereClass Q) {N : ℕ}
    (e : SmoothLoopEmbedding (I := I) (Q := Q) N) {η : ℝ} (hη : 0 < η) :
    ∃ Γ : RegularRepresentative (I := I) ξ,
      familyMaximum g Γ.1 < classWidth g ξ + η ∧ HasContinuousSmoothLoopJets e Γ.1 := by
  classical
  obtain ⟨Γ, hΓ⟩ := exists_representative_maximum_lt g ξ hη
  let i : C(ContractibleRegularLoop (I := I) (Q := Q), RegularLoop I Q) :=
    ⟨Subtype.val, continuous_subtype_val⟩
  let Γr : C(Sphere 2, RegularLoop I Q) := i.comp Γ.1
  obtain ⟨_, _, hsmooth⟩ := rfs_loop_smoothing g e
  obtain ⟨ε₀, hε₀, S, hjets, _, hhom, hregular, _⟩ :=
    hsmooth (Sphere 2) (regularLoopInclusion.comp Γr)
  have hctrS (ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) ε₀) (k : Sphere 2) :
      IsContractibleLoop (S ε k).toContinuousLoop := by
    obtain ⟨F, _, hF⟩ := hhom ε hε
    have h := hF k (Γ.1 k).2 1
    exact Eq.mp (congrArg IsContractibleLoop (F.apply_one k)) h
  let T : ℝ → RegularFamily (I := I) (Q := Q) (Sphere 2) := fun ε =>
    if hε : ε ∈ Ioo (0 : ℝ) ε₀ then
      ⟨fun k => ⟨S ε k, hctrS ε hε k⟩, (S ε).continuous.subtype_mk _⟩
    else Γ.1
  have hevent : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∈ Ioo (0 : ℝ) ε₀ := Ioo_mem_nhdsGT hε₀
  have hT : Filter.Tendsto T (𝓝[>] (0 : ℝ)) (𝓝 Γ.1) := by
    apply (ContinuousMap.isInducing_postcomp i IsInducing.subtypeVal).tendsto_nhds_iff.mpr
    have heq : (fun ε => i.comp (T ε)) =ᶠ[𝓝[>] (0 : ℝ)] S := by
      filter_upwards [hevent] with ε hε
      ext k
      simp only [T, dif_pos hε, ContinuousMap.comp_apply, i, ContinuousMap.coe_mk]
    exact ((hregular Γr rfl).1).congr' heq.symm
  have hmax := (continuous_familyMaximum g).continuousAt.tendsto.comp hT
  have hbound : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      familyMaximum g (T ε) < classWidth g ξ + η :=
    hmax.eventually (gt_mem_nhds hΓ)
  obtain ⟨ε, hε, hboundε⟩ := (hevent.and hbound).exists
  obtain ⟨F, _, hF⟩ := hhom ε hε
  have hhomT : ContinuousMap.Homotopic (contractibleRegularLoopInclusion.comp Γ.1)
      (contractibleRegularLoopInclusion.comp (T ε)) := by
    refine ⟨{
      toFun := fun p => ⟨F p, hF p.2 (Γ.1 p.2).2 p.1⟩
      continuous_toFun := (map_continuous F).subtype_mk _
      map_zero_left := ?_
      map_one_left := ?_ }⟩
    · intro k
      apply Subtype.ext
      exact F.apply_zero k
    · intro k
      apply Subtype.ext
      change F (1, k) = (T ε k).1.toContinuousLoop
      simpa only [T, dif_pos hε, ContinuousMap.coe_mk] using
        (show F (1, k) = (S ε k).toContinuousLoop from F.apply_one k)
  have hclass : FreeHomotopyClass.mk (contractibleRegularLoopInclusion.comp (T ε)) = ξ :=
    ((FreeHomotopyClass.mk_eq_mk_iff _ _).mpr hhomT).symm.trans Γ.2
  refine ⟨⟨T ε, hclass⟩, hboundε, ?_⟩
  simpa only [HasContinuousSmoothLoopJets, HasContinuousSmoothJets, T, dif_pos hε,
    ContinuousMap.coe_mk] using hjets ε hε

theorem classWidth_metric_comparison (g h : SmoothRiemannianMetric I Q)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hmetric : ∀ q (v : TangentSpace I q),
      a ^ 2 * g.inner q v v ≤ h.inner q v v ∧ h.inner q v v ≤ b ^ 2 * g.inner q v v)
    (ξ : FreeContractibleSphereClass Q) :
    a ^ 2 * classWidth g ξ ≤ classWidth h ξ ∧
      classWidth h ξ ≤ b ^ 2 * classWidth g ξ := by
  have hb : 0 < b := ha.trans_le hab
  have hupper : classWidth h ξ ≤ b ^ 2 * classWidth g ξ := by
    apply classWidth_le_mul g h (sq_pos_of_pos hb) ξ
    intro Γ
    exact familyMaximum_le_mul g h (sq_nonneg b) Γ.1 fun k =>
      (regularLeastArea_metric_comparison g h ha hab hmetric (Γ.1 k)).2
  have hlower : classWidth g ξ ≤ (a ^ 2)⁻¹ * classWidth h ξ := by
    apply classWidth_le_mul h g (inv_pos.mpr (sq_pos_of_pos ha)) ξ
    intro Γ
    apply familyMaximum_le_mul h g (inv_nonneg.mpr (sq_nonneg a)) Γ.1
    intro k
    have hk := (regularLeastArea_metric_comparison g h ha hab hmetric (Γ.1 k)).1
    exact (le_inv_mul_iff₀ (sq_pos_of_pos ha)).mpr hk
  refine ⟨?_, hupper⟩
  exact (le_inv_mul_iff₀ (sq_pos_of_pos ha)).mp hlower

theorem classWidth_scale (g : SmoothRiemannianMetric I Q) {c : ℝ} (hc : 0 < c)
    (ξ : FreeContractibleSphereClass Q) :
    classWidth (scaleMetric c hc g) ξ = c * classWidth g ξ := by
  have hmetric : ∀ q (v : TangentSpace I q),
      (Real.sqrt c) ^ 2 * g.inner q v v ≤ (scaleMetric c hc g).inner q v v ∧
      (scaleMetric c hc g).inner q v v ≤ (Real.sqrt c) ^ 2 * g.inner q v v := by
    intro q v
    simp [Real.sq_sqrt hc.le]
  have h := classWidth_metric_comparison g (scaleMetric c hc g)
    (Real.sqrt_pos.mpr hc) (le_refl (Real.sqrt c)) hmetric ξ
  simpa only [Real.sq_sqrt hc.le] using le_antisymm h.2 h.1

omit boundarylessI connectedQ in
theorem eventually_uniform_relative_metric_bound
    (D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval)
    (g : ℝ → SmoothRiemannianMetric I Q)
    (hg : DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn D g)
    (t₀ : D.carrier) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t : D.carrier in 𝓝 t₀, ∀ q (v : TangentSpace I q),
      |(g t).inner q v v - (g t₀).inner q v v| ≤ ε * (g t₀).inner q v v := by
  let U := MetricUnitTangent (I := I) (M := Q) (g t₀)
  let : CompactSpace U := isCompact_univ_iff.mp (metricUnit_compact (g t₀))
  let F : D.carrier → C(U, ℝ) := fun t =>
    ⟨fun p => (g t).inner p.1.proj p.1.2 p.1.2,
      (metricQuad_cont (g t)).comp continuous_subtype_val⟩
  have hF : Continuous F := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun p : D.carrier × U =>
      (g p.1).inner p.2.1.proj p.2.1.2 p.2.1.2)
    have hquad := DifferentialGeometry.Geometry.Curvature.tensor0SFamily_quadCont hg.metricTensor_cont
    have hc := hquad.comp (continuous_fst.prodMk
      (continuous_subtype_val.comp continuous_snd :
        Continuous (fun p : D.carrier × U => p.2.1)))
    convert hc using 1
    ext p
    simp only [Function.comp_apply, quad02, Tensor0SBundle.metricTensorField_apply]
    rfl
  have hclose := (Metric.tendsto_nhds.mp (hF.tendsto t₀)) ε hε
  filter_upwards [hclose] with t ht
  have heval (q : Q) (v : TangentSpace I q) :
      quad02 (Tensor0SBundle.metricTensorField (g t) q -
        Tensor0SBundle.metricTensorField (g t₀) q) v =
      (g t).inner q v v - (g t₀).inner q v v := by
    unfold quad02
    rw [sub_apply, Tensor0SBundle.metricTensorField_apply,
      Tensor0SBundle.metricTensorField_apply]
  have hall := unitAbsBound_to_all (g t₀)
    (fun q => Tensor0SBundle.metricTensorField (g t) q -
      Tensor0SBundle.metricTensorField (g t₀) q) (C := ε) (by
    intro p
    have hp := (ContinuousMap.dist_apply_le_dist p).trans_lt ht
    rw [heval]
    convert! hp.le using 1)
  simpa only [heval] using hall


theorem classWidth_relative_metric_bound (g h : SmoothRiemannianMetric I Q)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδone : δ < 1)
    (hmetric : ∀ q (v : TangentSpace I q),
      |h.inner q v v - g.inner q v v| ≤ δ * g.inner q v v)
    (ξ : FreeContractibleSphereClass Q) :
    |classWidth h ξ - classWidth g ξ| ≤ δ * classWidth g ξ := by
  have hminus : 0 < 1 - δ := sub_pos.mpr hδone
  have hplus : 0 ≤ 1 + δ := by linarith
  have hquad : ∀ q (v : TangentSpace I q),
      (Real.sqrt (1 - δ)) ^ 2 * g.inner q v v ≤ h.inner q v v ∧
      h.inner q v v ≤ (Real.sqrt (1 + δ)) ^ 2 * g.inner q v v := by
    intro q v
    rw [Real.sq_sqrt hminus.le, Real.sq_sqrt hplus]
    obtain ⟨hl, hu⟩ := abs_le.mp (hmetric q v)
    constructor <;> nlinarith
  have hw := classWidth_metric_comparison g h (Real.sqrt_pos.mpr hminus)
    (Real.sqrt_le_sqrt (by linarith)) hquad ξ
  rw [Real.sq_sqrt hminus.le, Real.sq_sqrt hplus] at hw
  exact abs_le.mpr ⟨by nlinarith [hw.1], by nlinarith [hw.2]⟩


theorem leastArea_relative_metric_bound (g h : SmoothRiemannianMetric I Q)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδone : δ < 1)
    (hmetric : ∀ q (v : TangentSpace I q),
      |h.inner q v v - g.inner q v v| ≤ δ * g.inner q v v)
    (γ : ContinuousFreeLoop Q) (hctr : IsContractibleLoop γ)
    (hlipg : IsLipschitzLoop g γ) (hliph : IsLipschitzLoop h γ) :
    |leastArea h γ hctr hliph - leastArea g γ hctr hlipg| ≤
      δ * leastArea g γ hctr hlipg := by
  have hminus : 0 < 1 - δ := sub_pos.mpr hδone
  have hplus : 0 ≤ 1 + δ := by linarith
  have hquad : ∀ q (v : TangentSpace I q),
      (Real.sqrt (1 - δ)) ^ 2 * g.inner q v v ≤ h.inner q v v ∧
      h.inner q v v ≤ (Real.sqrt (1 + δ)) ^ 2 * g.inner q v v := by
    intro q v
    rw [Real.sq_sqrt hminus.le, Real.sq_sqrt hplus]
    obtain ⟨hl, hu⟩ := abs_le.mp (hmetric q v)
    constructor <;> nlinarith
  have ha := leastArea_metric_comparison g h (Real.sqrt_pos.mpr hminus)
    (Real.sqrt_le_sqrt (by linarith)) hquad γ hctr hlipg hliph
  rw [Real.sq_sqrt hminus.le, Real.sq_sqrt hplus] at ha
  exact abs_le.mpr ⟨by nlinarith [ha.1], by nlinarith [ha.2]⟩

include finiteDimensionalE boundarylessI t2Q compactQ connectedQ in
theorem continuousOn_classWidth_metricFamily
    (D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval)
    (g : ℝ → SmoothRiemannianMetric I Q)
    (hg : DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn D g)
    (ξ : FreeContractibleSphereClass Q) :
    ContinuousOn (fun t => classWidth (g t) ξ) D.carrier := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  rw [continuous_iff_continuousAt]
  intro t₀
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let A := classWidth (g t₀) ξ
  have hA : 0 ≤ A := classWidth_nonneg (g t₀) ξ
  let δ := min (1 / 2 : ℝ) (ε / (A + 1))
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos hε (by positivity))
  have hδone : δ < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have hδA : δ * A < ε := by
    have hh := (le_div_iff₀ (show 0 < A + 1 by positivity)).mp
      (show δ ≤ ε / (A + 1) from min_le_right _ _)
    nlinarith
  filter_upwards [eventually_uniform_relative_metric_bound D g hg t₀ hδ] with t ht
  rw [Real.dist_eq]
  exact (classWidth_relative_metric_bound (g t₀) (g t) hδ.le hδone ht ξ).trans_lt hδA

include finiteDimensionalE boundarylessI t2Q compactQ connectedQ in
theorem continuousOn_leastArea_metricFamily
    (D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval)
    (g : ℝ → SmoothRiemannianMetric I Q)
    (hg : DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn D g)
    (g₀ : SmoothRiemannianMetric I Q) (γ : ContinuousFreeLoop Q)
    (hctr : IsContractibleLoop γ) (hlip : IsLipschitzLoop g₀ γ) :
    ContinuousOn (fun t => leastArea (g t) γ hctr
      ((isLipschitzLoop_metric_iff g₀ (g t) γ).mp hlip)) D.carrier := by
  let hLip (t : ℝ) := (isLipschitzLoop_metric_iff g₀ (g t) γ).mp hlip
  apply continuousOn_iff_continuous_domRestrict.mpr
  rw [continuous_iff_continuousAt]
  intro t₀
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let A := leastArea (g t₀) γ hctr (hLip t₀)
  have hA : 0 ≤ A := leastArea_nonneg (g t₀) γ hctr (hLip t₀)
  let δ := min (1 / 2 : ℝ) (ε / (A + 1))
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos hε (by positivity))
  have hδone : δ < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have hδA : δ * A < ε := by
    have hh := (le_div_iff₀ (show 0 < A + 1 by positivity)).mp
      (show δ ≤ ε / (A + 1) from min_le_right _ _)
    nlinarith
  filter_upwards [eventually_uniform_relative_metric_bound D g hg t₀ hδ] with t ht
  rw [Real.dist_eq]
  exact (leastArea_relative_metric_bound (g t₀) (g t) hδ.le hδone ht γ hctr
    (hLip t₀) (hLip t)).trans_lt hδA


theorem regularLeastArea_relative_metric_bound (g h : SmoothRiemannianMetric I Q)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδone : δ < 1)
    (hmetric : ∀ q (v : TangentSpace I q),
      |h.inner q v v - g.inner q v v| ≤ δ * g.inner q v v)
    (γ : ContractibleRegularLoop (I := I) (Q := Q)) :
    |regularLeastArea h γ - regularLeastArea g γ| ≤ δ * regularLeastArea g γ := by
  have hminus : 0 < 1 - δ := sub_pos.mpr hδone
  have hplus : 0 ≤ 1 + δ := by linarith
  have hquad : ∀ q (v : TangentSpace I q),
      (Real.sqrt (1 - δ)) ^ 2 * g.inner q v v ≤ h.inner q v v ∧
      h.inner q v v ≤ (Real.sqrt (1 + δ)) ^ 2 * g.inner q v v := by
    intro q v
    rw [Real.sq_sqrt hminus.le, Real.sq_sqrt hplus]
    obtain ⟨hl, hu⟩ := abs_le.mp (hmetric q v)
    constructor <;> nlinarith
  have harea := regularLeastArea_metric_comparison g h (Real.sqrt_pos.mpr hminus)
    (Real.sqrt_le_sqrt (by linarith)) hquad γ
  rw [Real.sq_sqrt hminus.le, Real.sq_sqrt hplus] at harea
  exact abs_le.mpr ⟨by nlinarith [harea.1], by nlinarith [harea.2]⟩

theorem tendsto_regularLeastArea_of_uniform_metric
    (g : SmoothRiemannianMetric I Q) (gseq : ℕ → SmoothRiemannianMetric I Q)
    (hg : ∀ ε : ℝ, 0 < ε → ∀ᶠ j in Filter.atTop,
      ∀ q (v : TangentSpace I q),
        |(gseq j).inner q v v - g.inner q v v| ≤ ε * g.inner q v v)
    (γ : ContractibleRegularLoop (I := I) (Q := Q))
    (γseq : ℕ → ContractibleRegularLoop (I := I) (Q := Q))
    (hγ : Filter.Tendsto γseq Filter.atTop (𝓝 γ)) :
    Filter.Tendsto (fun j => regularLeastArea (gseq j) (γseq j)) Filter.atTop
      (𝓝 (regularLeastArea g γ)) := by
  have hbase := (continuous_regularLeastArea g).continuousAt.tendsto.comp hγ
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let B := regularLeastArea g γ + 1
  have hB : 0 < B := by
    dsimp [B]
    linarith [regularLeastArea_nonneg g γ]
  let δ := min (1 / 2 : ℝ) (ε / (2 * B))
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos hε (by positivity))
  have hδone : δ < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have hδB : δ * B ≤ ε / 2 := by
    calc
      δ * B ≤ (ε / (2 * B)) * B := mul_le_mul_of_nonneg_right (min_le_right _ _) hB.le
      _ = ε / 2 := by field_simp [hB.ne']
  have hsmall : 0 < min (1 : ℝ) (ε / 2) := lt_min (by norm_num) (by positivity)
  have hclose := (Metric.tendsto_nhds.mp hbase) (min (1 : ℝ) (ε / 2)) hsmall
  filter_upwards [hg δ hδ, hclose] with j hj hclosej
  rw [Real.dist_eq] at hclosej ⊢
  simp only [Function.comp_apply] at hclosej
  have hBbound : regularLeastArea g (γseq j) ≤ B := by
    have h := (abs_lt.mp (hclosej.trans_le (min_le_left _ _))).2
    dsimp [B]
    linarith
  have hhalf : |regularLeastArea g (γseq j) - regularLeastArea g γ| < ε / 2 :=
    hclosej.trans_le (min_le_right _ _)
  calc
    |regularLeastArea (gseq j) (γseq j) - regularLeastArea g γ| ≤
        |regularLeastArea (gseq j) (γseq j) - regularLeastArea g (γseq j)| +
          |regularLeastArea g (γseq j) - regularLeastArea g γ| := abs_sub_le _ _ _
    _ ≤ δ * regularLeastArea g (γseq j) +
        |regularLeastArea g (γseq j) - regularLeastArea g γ| :=
      add_le_add (regularLeastArea_relative_metric_bound g (gseq j) hδ.le hδone hj
        (γseq j)) le_rfl
    _ < δ * B + ε / 2 :=
      add_lt_add_of_le_of_lt (mul_le_mul_of_nonneg_left hBbound hδ.le) hhalf
    _ ≤ ε := by linarith

end DifferentialGeometry.PDE.RicciFlow.Extinction.Width
