import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StaticCap
import DifferentialGeometry.Geometry.Neck.Recentering
import DifferentialGeometry.Topology.Manifold.ImmersionDifferential

noncomputable section

open Set Bundle Manifold Function
open DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private local instance : Fact (Module.finrank ℝ ThreeSpace = 2 + 1) := ⟨by simp⟩
private local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (2 + 1))) = 2 + 1) :=
  ⟨by simp⟩
private local instance : NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ)) := ⟨by simp⟩
private local instance (O : TopologicalSpace.Opens NeckCylinder) : SigmaCompactSpace O :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen NeckCylinderModel O.isOpen)

theorem roundCylinderMetric_eq_geometry :
    roundCylinderMetric = (Geometry.Metric.roundCylinderMetric (E := ThreeSpace) (n := 2)) := by
  apply SmoothRiemannianMetric.ext_inner
  intro x V W
  have hkey : ∀ (V : TangentSpace NeckCylinderModel x),
      mfderiv NeckCylinderModel ThreeModel
          (fun p : NeckCylinder => (p.1.1 : ThreeSpace)) x V
        = dIncl (E := ThreeSpace) (n := 2) x.1 V.1 := by
    intro V
    have hcomp : (fun p : NeckCylinder => (p.1.1 : ThreeSpace)) =
        ((↑) : Sphere 2 → ThreeSpace) ∘ Prod.fst := by
      rw [← Function.comp_def]
    rw [hcomp]
    rw [mfderiv_comp x
      ((contMDiff_coe_sphere (E := ThreeSpace) (n := 2) (m := ∞)).contMDiffAt.mdifferentiableAt
        (by simp))
      (mdifferentiableAt_fst (x := x))]
    rw [mfderiv_fst]
    rfl
  have hsnd : ∀ (V : TangentSpace NeckCylinderModel x),
      mfderiv NeckCylinderModel 𝓘(ℝ, ℝ) Prod.snd x V = V.2 := by
    intro V
    rw [mfderiv_snd]
    rfl
  have h := (Classical.choose_spec
    (exists_unique_shrinkingCylinderMetric (⟨0, by norm_num⟩ : Iio (1 : ℝ)))).1 x V W
  rw [roundCylinderMetric, shrinkingCylinderMetric]
  rw [h, shrinkingCylinderInner, hkey V, hkey W, hsnd V, hsnd W]
  rw [Geometry.Metric.roundCylinderMetric_inner]
  norm_num
  rfl

theorem isCompact_neckClosedTest (δ : ℝ) : IsCompact (neckClosedTest δ) := by
  rw [Topology.IsEmbedding.isCompact_iff
    (Topology.IsEmbedding.subtypeVal (p := fun q => q ∈ neckBuffer δ))]
  have himg : (Subtype.val '' neckClosedTest δ : Set NeckCylinder) =
      (Set.univ : Set (Sphere 2)) ×ˢ Icc (-δ⁻¹) δ⁻¹ := by
    ext q
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨Set.mem_univ _, hy⟩
    · rintro ⟨-, hq⟩
      refine ⟨⟨q, ?_⟩, hq, rfl⟩
      change -δ⁻¹ - 1 < q.2 ∧ q.2 < δ⁻¹ + 1
      constructor <;> linarith [hq.1, hq.2]
  rw [himg]
  exact isCompact_univ.prod isCompact_Icc

theorem metricDerivNormSupOn_nonneg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    (K : Set M) (p : ℕ) (gk gInf gRef : SmoothRiemannianMetric I M) :
    0 ≤ metricDerivNormSupOn K p gk gInf gRef := by
  rw [metricDerivNormSupOn]
  exact Real.sSup_nonneg (by rintro r ⟨a, ha, x, hx, rfl⟩; rw [metricDerivNorm]; positivity)

section SupTransport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem metricDerivNormSupOn_scaleMetric_left_le {K : Set M} (hK : IsCompact K) (p : ℕ)
    (c : ℝ) (hc : 0 < c) (g gRef : SmoothRiemannianMetric I M) :
    metricDerivNormSupOn K p (scaleMetric c hc g) gRef gRef ≤
      c * metricDerivNormSupOn K p g gRef gRef +
        |c - 1| * Real.sqrt (Module.finrank ℝ E : ℝ) := by
  apply metricDerivNormSupOn_le_of_forall
  · exact add_nonneg (mul_nonneg hc.le (metricDerivNormSupOn_nonneg K p g gRef gRef))
      (mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _))
  · intro a ha x hx
    refine (metricDerivNorm_scaleMetric_left_le c hc g gRef a x).trans ?_
    have hle := derivNorm_le_sup (I := I) hK ha g gRef gRef hx
    have h1 : 0 ≤ |c - 1| := abs_nonneg _
    have h2 : 0 ≤ Real.sqrt (Module.finrank ℝ E : ℝ) := Real.sqrt_nonneg _
    nlinarith [hc.le]

theorem metricDerivNormSupOn_scaleMetric_left_lt {K : Set M} (hK : IsCompact K) (p : ℕ)
    (c : ℝ) (hc : 0 < c) (g gRef : SmoothRiemannianMetric I M) {ε : ℝ}
    (hsmall : metricDerivNormSupOn K p g gRef gRef < ε) :
    metricDerivNormSupOn K p (scaleMetric c hc g) gRef gRef <
      c * ε + |c - 1| * Real.sqrt (Module.finrank ℝ E : ℝ) := by
  refine (metricDerivNormSupOn_scaleMetric_left_le hK p c hc g gRef).trans_lt ?_
  have h := mul_lt_mul_of_pos_left hsmall hc
  linarith

theorem metricDerivNorm_lt_of_sup_lt {K : Set M} (hK : IsCompact K) {a p : ℕ} (hap : a ≤ p)
    (gk gInf gRef : SmoothRiemannianMetric I M) {ε : ℝ}
    (hsmall : metricDerivNormSupOn K p gk gInf gRef < ε) {x : M} (hx : x ∈ K) :
    metricDerivNorm a gk gInf gRef x < ε :=
  (derivNorm_le_sup (I := I) hK hap gk gInf gRef hx).trans_lt hsmall

end SupTransport

theorem metricDerivNormSupOn_recenteringMetric {ε δ σ : ℝ} (hσ : σ ^ 2 = 1)
    (hfit : ε⁻¹ + 1 ≤ δ⁻¹)
    (H HInf : SmoothRiemannianMetric ((𝓡 2).prod 𝓘(ℝ, ℝ)) (Geometry.Neck.bufferedCylinder δ))
    (K : Set (Geometry.Neck.bufferedCylinder ε)) (p : ℕ) :
    metricDerivNormSupOn K p (Geometry.Neck.recenteringMetric hσ hfit H)
        (Geometry.Neck.recenteringMetric hσ hfit HInf) (Geometry.Neck.referenceMetric ε) =
      metricDerivNormSupOn (Geometry.Neck.recenteringCylinderMap hσ hfit '' K) p H HInf
        (Geometry.Neck.referenceMetric δ) := by
  have heq : ∀ (a : ℕ) (x : Geometry.Neck.bufferedCylinder ε),
      metricDerivNorm a (Geometry.Neck.recenteringMetric hσ hfit H)
          (Geometry.Neck.recenteringMetric hσ hfit HInf) (Geometry.Neck.referenceMetric ε) x =
        metricDerivNorm a H HInf (Geometry.Neck.referenceMetric δ)
          (Geometry.Neck.recenteringCylinderMap hσ hfit x) :=
    fun a x => Geometry.Neck.metricDerivNorm_recenteringMetric hσ hfit H HInf a x
  simp only [metricDerivNormSupOn]
  congr 1
  ext r
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨a, ha, x, hx, hr⟩
    exact ⟨a, ha, Geometry.Neck.recenteringCylinderMap hσ hfit x, ⟨x, hx, rfl⟩,
      (heq a x).symm.trans hr⟩
  · rintro ⟨a, ha, y, ⟨x, hx, rfl⟩, hy⟩
    exact ⟨a, ha, x, hx, (heq a x).trans hy⟩

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] [T2Space M]

theorem NormalizedNeck.metricScalarAt_normalizedMetric {g : SmoothRiemannianMetric ThreeModel M}
    {δ : ℝ} {k : ℕ} (N : NormalizedNeck g δ k) (x : neckBuffer δ) :
    metricScalarAt N.normalizedMetric x = metricScalarAt g (N.chart x) / N.scale := by
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ) = Module.finrank ℝ ThreeSpace := by
    simp [ThreeSpace]
  have hinj : ∀ y : neckBuffer δ, Injective (mfderiv NeckCylinderModel ThreeModel
      (N.chart : neckBuffer δ → M) y) :=
    fun y => DifferentialGeometry.Topology.Manifold.injective_mfderiv_of_isImmersionAt
      NeckCylinderModel ThreeModel (N.chart : neckBuffer δ → M) y
      (N.chart_smooth.isImmersion.isImmersionAt y)
  have hlocal : IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ (N.chart : neckBuffer δ → M) :=
    isLocalDiffeomorph_of_injective_mfderiv (N.chart : neckBuffer δ → M)
      N.chart_smooth.contMDiff hinj hdim
  have hEq : N.normalizedMetric =
      pullbackMetricOfInjectiveLocalDiffeomorph (scaleMetric N.scale N.scale_pos g)
        (N.chart : neckBuffer δ → M) hlocal N.chart_smooth.isEmbedding.injective := by
    apply SmoothRiemannianMetric.ext_inner
    intro y V W
    rw [pullbackMetricOfInjectiveLocalDiffeomorph_inner, scaleMetric_inner, N.normalized_inner]
  rw [hEq]
  exact metricScalarAt_pullbackMetricOfInjectiveLocalDiffeomorph_scale (I := NeckCylinderModel)
    (J := ThreeModel) g (N.chart : neckBuffer δ → M) hlocal
    N.chart_smooth.isEmbedding.injective N.scale N.scale_pos x

theorem NormalizedNeck.abs_scalar_ratio_sub_one_le {g : SmoothRiemannianMetric ThreeModel M}
    {δ : ℝ} {k : ℕ} (N : NormalizedNeck g δ k) (hk : 2 ≤ k) (hδ : δ ≤ 1 / 2)
    (x : neckBuffer δ) (hx : x ∈ neckClosedTest δ) :
    |metricScalarAt g (N.chart x) / N.scale - 1| ≤ 4323 * δ := by
  have hcl := N.closeness
  rw [roundCylinderMetric_eq_geometry] at hcl
  have hpt : ∀ j : ℕ, j ≤ 2 →
      metricDerivNorm j N.normalizedMetric
        ((Geometry.Metric.roundCylinderMetric (E := ThreeSpace) (n := 2)).restrictOpen
          (neckBuffer δ))
        ((Geometry.Metric.roundCylinderMetric (E := ThreeSpace) (n := 2)).restrictOpen
          (neckBuffer δ)) x ≤ δ :=
    fun j hj => (metricDerivNorm_lt_of_sup_lt (isCompact_neckClosedTest δ)
      (hj.trans hk) _ _ _ hcl hx).le
  have h := abs_scalar_curvature_restricted_roundCylinder_sub_one_le (neckBuffer δ)
    N.normalizedMetric x δ hδ hpt
  rw [← N.metricScalarAt_normalizedMetric x]
  exact h

theorem neckShift_mem_neckBuffer {c δ s : ℝ} (hfit : (c * δ)⁻¹ + 1 ≤ δ⁻¹) (hs : s ^ 2 = 1)
    (x : neckBuffer (c * δ)) :
    (x.1.1, s * (1 + x.1.2)) ∈ neckBuffer δ := by
  change -δ⁻¹ - 1 < s * (1 + x.1.2) ∧ s * (1 + x.1.2) < δ⁻¹ + 1
  rcases sq_eq_one_iff.mp hs with rfl | rfl <;> constructor <;> linarith [x.2.1, x.2.2, hfit]

theorem neckShift_mem_neckClosedTest {c δ s : ℝ} (hfit : (c * δ)⁻¹ + 1 ≤ δ⁻¹)
    (hs : s ^ 2 = 1) (x : neckBuffer (c * δ)) (hx : x ∈ neckClosedTest (c * δ)) :
    (⟨(x.1.1, s * (1 + x.1.2)), neckShift_mem_neckBuffer hfit hs x⟩ : neckBuffer δ) ∈
      neckClosedTest δ := by
  change -δ⁻¹ ≤ s * (1 + x.1.2) ∧ s * (1 + x.1.2) ≤ δ⁻¹
  rcases sq_eq_one_iff.mp hs with rfl | rfl <;> constructor <;>
    linarith [hx.1, hx.2, hfit]

theorem recenter_scaled_error_bound {lam δ : ℝ} (hδ : 0 < δ) (hlam : |lam - 1| ≤ 4323 * δ)
    (hsmall : 4323 * δ < 11353) :
    lam * δ + |lam - 1| * Real.sqrt 3 < 20000 * δ := by
  have hroot : Real.sqrt 3 ≤ 2 := by
    rw [Real.sqrt_le_iff]
    norm_num
  have hlamu : lam ≤ 1 + 4323 * δ := by linarith [abs_le.mp hlam]
  have hcorr : |lam - 1| * Real.sqrt 3 ≤ 4323 * δ * 2 :=
    mul_le_mul hlam hroot (Real.sqrt_nonneg 3) (by positivity)
  have h1 : lam * δ ≤ (1 + 4323 * δ) * δ := mul_le_mul_of_nonneg_right hlamu hδ.le
  have hsum : lam * δ + |lam - 1| * Real.sqrt 3 ≤
      (1 + 4323 * δ) * δ + 4323 * δ * 2 := add_le_add h1 hcorr
  have hkey : 4323 * δ * δ < 11353 * δ := mul_lt_mul_of_pos_right hsmall hδ
  have hgoal : (1 + 4323 * δ) * δ + 4323 * δ * 2 < 20000 * δ := by
    nlinarith [hkey]
  linarith [hsum, hgoal]

theorem neckShift_neckClosedTest_subset {c δ s : ℝ} (hfit : (c * δ)⁻¹ + 1 ≤ δ⁻¹)
    (hs : s ^ 2 = 1) :
    (fun x : neckBuffer (c * δ) =>
        (⟨(x.1.1, s * (1 + x.1.2)), neckShift_mem_neckBuffer hfit hs x⟩ : neckBuffer δ)) ''
        neckClosedTest (c * δ) ⊆ neckClosedTest δ :=
  fun _ ⟨x, hx, hy⟩ => hy ▸ neckShift_mem_neckClosedTest hfit hs x hx

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
