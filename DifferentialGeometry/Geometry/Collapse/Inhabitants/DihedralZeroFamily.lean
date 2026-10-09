import DifferentialGeometry.Geometry.Collapse.Inhabitants.DihedralPointedModels
import DifferentialGeometry.Geometry.Collapse.Inhabitants.DihedralRay
import DifferentialGeometry.Geometry.Collapse.LocalExport.ZeroModelBall
import DifferentialGeometry.Geometry.Metric.Scaling.RescaleComposition

/-! Actual connected dihedral zero-model families with original LC58 moving limits,
internal cone/model data, and at least two distinct centres from two genuine rank-zero tips. -/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.Collapse GC.Endpoint GC.Geometry.SphericalProduct
open DifferentialGeometry.Geometry.Riemannian Bundle GC.MetricGeometry
open Filter Set
open scoped Topology Manifold ContDiff
attribute [local instance] sphereDimension cylinderDimension
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace
namespace DifferentialGeometry.Geometry.Collapse

def dihedralZeroConeCarrier (ε : ℝ) (hε : 0 < ε) (b : Unit ⊕ ℝ) : Type :=
  Classical.choose (dihedralModelCone ε hε b)
@[instance_reducible] def dihedralZeroConeMetric (ε : ℝ) (hε : 0 < ε) (b : Unit ⊕ ℝ) :
    MetricSpace (dihedralZeroConeCarrier ε hε b) :=
  Classical.choose (Classical.choose_spec (dihedralModelCone ε hε b))
def dihedralZeroConeBase (ε : ℝ) (hε : 0 < ε) (b : Unit ⊕ ℝ) : dihedralZeroConeCarrier ε hε b :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec (dihedralModelCone ε hε b)))
theorem dihedralZeroConeClauses (ε : ℝ) (hε : 0 < ε) (b : Unit ⊕ ℝ) :
    let modelMetric : MetricSpace (dihedralModelCarrier b) := dihedralModelMetricSpace ε hε b
    let _coneMetric : MetricSpace (dihedralZeroConeCarrier ε hε b) := dihedralZeroConeMetric ε hε b
    Nonempty (RadialConeData (dihedralZeroConeBase ε hε b)) ∧
      ProperSpace (dihedralZeroConeCarrier ε hε b) ∧ ∀ τ : ℝ, 0 < τ → τ < 1 → ∃ R0 : ℝ,
      ∀ R : ℝ, ∀ hR : 0 < R, R0 ≤ R →
        Nonempty (@KleinerLottApprox (dihedralModelCarrier b) (dihedralZeroConeCarrier ε hε b)
          (modelMetric.rescale R⁻¹ (inv_pos.mpr hR)) (dihedralZeroConeMetric ε hε b)
          (dihedralModelBase b) (dihedralZeroConeBase ε hε b) τ) :=
  Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (dihedralModelCone ε hε b)))
def dihedralZeroConeRadial (ε : ℝ) (hε : 0 < ε) (b : Unit ⊕ ℝ) :
    letI := dihedralZeroConeMetric ε hε b
    RadialConeData (dihedralZeroConeBase ε hε b) := (dihedralZeroConeClauses ε hε b).1.some
theorem dihedralZeroConeProper (ε : ℝ) (hε : 0 < ε) (b : Unit ⊕ ℝ) :
    letI := dihedralZeroConeMetric ε hε b
    ProperSpace (dihedralZeroConeCarrier ε hε b) := (dihedralZeroConeClauses ε hε b).2.1
abbrev dihedralZeroSource :=
  (connectedSum projectiveThreeSpaceLift.{0} projectiveThreeSpaceLift.{0}).Carrier


theorem dihedralZeroScaleMetricUnit (g : SmoothRiemannianMetric (𝓡 3) dihedralZeroSource) :
    scaleMetric ((1 : ℝ)⁻¹ ^ 2) (by positivity) g = g := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  have h := congrArg (fun inner => inner x v w) (scaleMetric_one g)
  simpa only [inv_one, one_pow] using h
theorem dihedralZeroUnitModel :
  ∀ (ε : ℝ) (hε : 0 < ε) (L : ℕ → ℝ) (hL : ∀ i, 0 < L i),
    Tendsto L atTop atTop → ∀ z : ℕ → dihedralZeroSource,
    ∃ b : Unit ⊕ ℝ, ∃ k : ℕ → ℕ, StrictMono k ∧
      @PointedGHConverges (fun _i : ℕ => dihedralZeroSource)
        (fun i => (inducedMetricSpace (dihedralMetric ε (L (k i)) hε (hL (k i)))).rescale
          (1 : ℝ)⁻¹ (by positivity))
        (dihedralModelCarrier b) (dihedralModelMetricSpace ε hε b)
        (fun i => z (k i)) (dihedralModelBase b) ∧
      (letI := dihedralModelMetricSpace ε hε b
      ∃ jm : ∀ _i, PartialDiffeomorph (𝓡 3) (𝓡 3) (dihedralModelCarrier b) dihedralZeroSource ∞,
        (∀ i, jm i (dihedralModelBase b) = z (k i)) ∧ ∀ r : ℝ, 0 < r → ∃ i0 : ℕ,
        ∃ hsub : ∀ l, ((⟨Metric.ball (dihedralModelBase b) r, Metric.isOpen_ball⟩ :
          TopologicalSpace.Opens (dihedralModelCarrier b)) : Set (dihedralModelCarrier b)) ⊆
            (jm (l + i0)).source,
        ∀ K : Set (⟨Metric.ball (dihedralModelBase b) r, Metric.isOpen_ball⟩ :
          TopologicalSpace.Opens (dihedralModelCarrier b)),
          IsCompact K → CheegerGromovCompactness.MetricCPConvergenceOn K 1
            (fun l => PartialDiffeomorph.pullbackMetricOn (jm (l + i0)) _ (hsub l)
              (scaleMetric ((1 : ℝ)⁻¹ ^ 2) (by positivity)
                (dihedralMetric ε (L (k (l + i0))) hε (hL (k (l + i0))))))
            ((dihedralModelMetric ε hε b).restrictOpen _)
            ((dihedralModelMetric ε hε b).restrictOpen _)) ∧
      ∃ Hb : ℕ → ℝ, Tendsto Hb atTop atTop ∧ ∀ (j : ℕ),
        ∀ y ∈ @Metric.ball dihedralZeroSource
          ((inducedMetricSpace (dihedralMetric ε (L (k j)) hε (hL (k j)))).rescale
            (1 : ℝ)⁻¹ (by positivity)).toPseudoMetricSpace (z (k j)) (Hb j),
          SectionalBoundedBelowAt (scaleMetric ((1 : ℝ)⁻¹ ^ 2) (by positivity)
            (dihedralMetric ε (L (k j)) hε (hL (k j)))) y (-((Hb j)⁻¹ ^ 2)) := by
  intro ε hε L hL hLt z
  obtain ⟨b, k, hk, hGH, hcharts, Hb, hHbt, hcurv⟩ :=
    dihedralIndexedMoving.{0} ε hε L hL hLt z
  refine ⟨b, k, hk, ?_, ?_, Hb, hHbt, ?_⟩
  · have hmetric (i : ℕ) :
        (inducedMetricSpace (dihedralMetric ε (L (k i)) hε (hL (k i)))).rescale
          (1 : ℝ)⁻¹ (by positivity) =
        inducedMetricSpace (dihedralMetric ε (L (k i)) hε (hL (k i))) := by
      simp only [inv_one, MetricSpace.rescale_one]
    rw [funext hmetric]
    exact hGH
  · obtain ⟨jm, hanchors, hballs⟩ := hcharts
    refine ⟨jm, hanchors, ?_⟩
    intro r hr
    obtain ⟨i0, hsub, hK⟩ := hballs r hr
    refine ⟨i0, hsub, ?_⟩
    intro K hcompact
    simpa only [dihedralZeroScaleMetricUnit] using hK K hcompact
  · intro j y _hy
    simpa only [dihedralZeroScaleMetricUnit] using hcurv j y

def dihedralZeroLengths (α : ℕ) : ℝ := (α : ℝ) + 201
theorem dihedralZeroLengthsPositive (α : ℕ) : 0 < dihedralZeroLengths α := by
  dsimp [dihedralZeroLengths]
  positivity
def dihedralZeroFamilyMetric (ε : ℝ) (hε : 0 < ε) (α : ℕ) :
    SmoothRiemannianMetric (𝓡 3) dihedralZeroSource :=
  dihedralMetric ε (dihedralZeroLengths α) hε (dihedralZeroLengthsPositive α)

theorem exists_dihedralZeroModelFamily :
  ∀ (ε : ℝ) (hε : 0 < ε),
  letI : ∀ b : Unit ⊕ ℝ, MetricSpace (dihedralModelCarrier b) :=
    fun b => dihedralModelMetricSpace ε hε b
  letI : ∀ b : Unit ⊕ ℝ, MetricSpace (dihedralZeroConeCarrier ε hε b) :=
    fun b => dihedralZeroConeMetric ε hε b
  ∃ εsel δ T V : ℝ, 0 < εsel ∧ εsel < 1 / 4 ∧ 0 < δ ∧ 0 < T ∧ T ≤ V ∧
    ∃ α0 : ℕ, ∀ α : ℕ, α0 < α →
    letI := inducedMetricSpace (dihedralZeroFamilyMetric ε hε α)
    Nonempty (ZeroModelFamily (𝓡 3) dihedralZeroSource (dihedralZeroFamilyMetric ε hε α)
      (fun _p => (1 : ℝ)) (fun _p => by norm_num) (fun _k => (1 / 1000 : ℝ))
      dihedralModelCarrier (dihedralZeroConeCarrier ε hε) (dihedralZeroConeBase ε hε)
      δ εsel (1 / 1000) T V) := by
  intro ε hε
  let _modelMetrics : ∀ b : Unit ⊕ ℝ, MetricSpace (dihedralModelCarrier b) :=
    fun b => dihedralModelMetricSpace ε hε b
  let _coneMetrics : ∀ b : Unit ⊕ ℝ, MetricSpace (dihedralZeroConeCarrier ε hε b) :=
    fun b => dihedralZeroConeMetric ε hε b
  let _modelBundles : ∀ b : Unit ⊕ ℝ,
      RiemannianBundle (fun x : dihedralModelCarrier b => TangentSpace (𝓡 3) x) :=
    fun b => dihedralModelBundle ε hε b
  let _modelRiemannian : ∀ b : Unit ⊕ ℝ, IsRiemannianManifold (𝓡 3) (dihedralModelCarrier b) :=
    fun b => dihedralModelRiemannian ε hε b
  let _modelContinuous : ∀ b : Unit ⊕ ℝ,
      IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
        (fun x : dihedralModelCarrier b => TangentSpace (𝓡 3) x) :=
    fun b => dihedralModelContinuousBundle ε hε b
  let _modelComplete : ∀ b : Unit ⊕ ℝ, CompleteSpace (dihedralModelCarrier b) :=
    fun b => dihedralModelCompleteSpace ε hε b
  let _coneProper : ∀ b : Unit ⊕ ℝ, ProperSpace (dihedralZeroConeCarrier ε hε b) :=
    fun b => dihedralZeroConeProper ε hε b
  have hLt : Tendsto dihedralZeroLengths atTop atTop :=
    tendsto_atTop_add_const_right _ 201 tendsto_natCast_atTop_atTop
  have hmodel (a : ℕ → ℕ) (ha : Tendsto a atTop atTop) (z : ℕ → dihedralZeroSource) :=
    dihedralZeroUnitModel ε hε (fun i => dihedralZeroLengths (a i))
      (fun i => dihedralZeroLengthsPositive (a i)) (hLt.comp ha) z
  exact eventually_nonempty_zeroModelFamily (I := 𝓡 3) (M := fun _α => dihedralZeroSource)
    (N := dihedralModelCarrier) (C := dihedralZeroConeCarrier ε hε)
    (β := fun _k => (1 / 1000 : ℝ)) (ζ := (1 / 2 : ℝ))
    (by simp) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (dihedralZeroFamilyMetric ε hε) (fun _α _p => (1 : ℝ))
    (fun _α => continuous_const) (fun _α _p => by norm_num)
    (dihedralModelMetric ε hε) (fun b => dihedralModelNorm ε hε b)
    (fun b => dihedralModelSectional ε hε b) dihedralModelBase (dihedralZeroConeBase ε hε)
    (dihedralZeroConeRadial ε hε) (fun b => (dihedralZeroConeClauses ε hε b).2.2) hmodel
    (e := (1 / 1000 : ℝ)) (by norm_num) (by norm_num)


theorem exists_dihedralZeroModelFamily_twoCentres :
  ∃ (ε : ℝ) (hε : 0 < ε),
  letI : ∀ b : Unit ⊕ ℝ, MetricSpace (dihedralModelCarrier b) :=
    fun b => dihedralModelMetricSpace ε hε b
  letI : ∀ b : Unit ⊕ ℝ, MetricSpace (dihedralZeroConeCarrier ε hε b) :=
    fun b => dihedralZeroConeMetric ε hε b
  ∃ εsel δ T V : ℝ, 0 < εsel ∧ εsel < 1 / 4 ∧ 0 < δ ∧ 0 < T ∧ T ≤ V ∧
    ∃ α0 : ℕ, ∀ α : ℕ, α0 < α →
    letI := inducedMetricSpace (dihedralZeroFamilyMetric ε hε α)
    ∃ F : ZeroModelFamily (𝓡 3) dihedralZeroSource (dihedralZeroFamilyMetric ε hε α)
      (fun _p => (1 : ℝ)) (fun _p => by norm_num) (fun _k => (1 / 1000 : ℝ))
      dihedralModelCarrier (dihedralZeroConeCarrier ε hε) (dihedralZeroConeBase ε hε)
      δ εsel (1 / 1000) T V,
      ∃ i ∈ F.centres, ∃ j ∈ F.centres, i ≠ j := by
  obtain ⟨ε, hε, hTips⟩ := exists_dihedral_zeroRankTips_scale.{0, 0}
    (fun _k => (1 / 1000 : ℝ)) (by intro _k _hk _hk3; norm_num)
  refine ⟨ε, hε, ?_⟩
  let _modelMetrics : ∀ b : Unit ⊕ ℝ, MetricSpace (dihedralModelCarrier b) :=
    fun b => dihedralModelMetricSpace ε hε b
  let _coneMetrics : ∀ b : Unit ⊕ ℝ, MetricSpace (dihedralZeroConeCarrier ε hε b) :=
    fun b => dihedralZeroConeMetric ε hε b
  obtain ⟨εsel, δ, T, V, hεsel, hεquarter, hδ, hT, hTV, α0, hFamily⟩ :=
    exists_dihedralZeroModelFamily ε hε
  have hV : 0 < V := lt_of_lt_of_le hT hTV
  have hLt : Tendsto dihedralZeroLengths atTop atTop :=
    tendsto_atTop_add_const_right _ 201 tendsto_natCast_atTop_atTop
  obtain ⟨α1, hα1⟩ := eventually_atTop.mp (hLt.eventually_ge_atTop (V + 1))
  refine ⟨εsel, δ, T, V, hεsel, hεquarter, hδ, hT, hTV, max α0 α1, ?_⟩
  intro α hα
  let sourceMetric : MetricSpace dihedralZeroSource :=
    inducedMetricSpace (dihedralZeroFamilyMetric ε hε α)
  obtain ⟨F⟩ := hFamily α (by omega)
  obtain ⟨hlzero, hrzero, hdist⟩ :=
    hTips (dihedralZeroLengths α) (dihedralZeroLengthsPositive α) (by
      dsimp [dihedralZeroLengths]
      have h0 : (0 : ℝ) ≤ (α : ℝ) := Nat.cast_nonneg α
      linarith)
  have hscale : sourceMetric.rescale (1 : ℝ)⁻¹ (by positivity) = sourceMetric := by
    simp only [inv_one, MetricSpace.rescale_one]
  have hmem (p : dihedralZeroSource)
      (hp : @splittingRank.{0, 0} dihedralZeroSource sourceMetric p
        (fun _k => (1 / 1000 : ℝ)) 3 = 0) :
      p ∈ scaledSplittingStratum.{0, 0} (fun _p => (1 : ℝ)) (fun _p => by norm_num)
        (fun _k => (1 / 1000 : ℝ)) 0 := by
    change @splittingRank.{0, 0} dihedralZeroSource
      (sourceMetric.rescale (1 : ℝ)⁻¹ (by positivity)) p (fun _k => (1 / 1000 : ℝ)) 3 = 0
    rw [hscale]
    exact hp
  obtain ⟨i, hci⟩ := mem_iUnion.mp (F.covers_stratum (hmem dihedralLeftTip hlzero))
  obtain ⟨hi, hleft⟩ := mem_iUnion.mp hci
  obtain ⟨j, hcj⟩ := mem_iUnion.mp (F.covers_stratum (hmem dihedralRightTip hrzero))
  obtain ⟨hj, hright⟩ := mem_iUnion.mp hcj
  refine ⟨F, i, hi, j, hj, ?_⟩
  intro hij
  subst j
  have hrleft : (F.zero i hi).radius ≤ V := by
    simpa only [mul_one] using (F.radius_mem i hi).2
  have hrright : (F.zero i hj).radius ≤ V := by
    simpa only [mul_one] using (F.radius_mem i hj).2
  have hl : dist dihedralLeftTip i < (F.zero i hi).radius / 10 := hleft
  have hr : dist dihedralRightTip i < (F.zero i hj).radius / 10 := hright
  have htri := dist_triangle dihedralLeftTip i dihedralRightTip
  rw [dist_comm i dihedralRightTip] at htri
  have hlarge := hα1 α (by omega)
  have hdistCurrent : dihedralZeroLengths α ≤ dist dihedralLeftTip dihedralRightTip := hdist
  linarith only [hdistCurrent, hlarge, htri, hl, hr, hrleft, hrright, hV]

end DifferentialGeometry.Geometry.Collapse
