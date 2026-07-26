import DifferentialGeometry.Analysis.Sobolev.Tensor.ChartWkpQuot
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Completeness.IteratedSobolevQuot
import DifferentialGeometry.Analysis.Sobolev.Chart.SmoothDensity.SmoothMulQuant
import DifferentialGeometry.Analysis.Sobolev.Manifold.IteratedSobolevEmbedding

/-!
# A theorem-valued Banach structure on tensor chart Sobolev classes

`WkpTensorQuot` already carries the explicit operations `qzero`, `qadd`,
`qneg`, `qsub`, and `qsmul`, together with the finite quotient norm and its
sequence-level completeness theorem.  The definitions in this file package
those proved operations as ordinary structure values.  Nothing is registered
as a global or scoped instance.

This is the structure needed by the finite-chart Ricci--DeTurck parametrix:
consumers install the four values below with local `letI` declarations, use
continuous linear maps and the Neumann inverse, and then leave the local
instance scope.  Thus the tensor quotient remains inert for unrelated
typeclass search.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Tensor

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩
private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-! ## Scalar-module laws for the explicit quotient operations -/

theorem qone_smul
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p)
    (a : WkpTensorQuot (I := I) (M := M) g r s k p hp) :
    qsmul (I := I) (M := M) g r s k p hp 1 a = a := by
  refine Quotient.inductionOn a ?_
  intro S
  change Quotient.mk
      (tensorChartSetoid (I := I) (M := M) g r s k p hp) (1 • S) =
    Quotient.mk (tensorChartSetoid (I := I) (M := M) g r s k p hp) S
  rw [one_smul]

theorem qmul_smul
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (a b : ℝ)
    (u : WkpTensorQuot (I := I) (M := M) g r s k p hp) :
    qsmul (I := I) (M := M) g r s k p hp (a * b) u =
      qsmul (I := I) (M := M) g r s k p hp a
        (qsmul (I := I) (M := M) g r s k p hp b u) := by
  refine Quotient.inductionOn u ?_
  intro S
  change Quotient.mk
      (tensorChartSetoid (I := I) (M := M) g r s k p hp) ((a * b) • S) =
    Quotient.mk (tensorChartSetoid (I := I) (M := M) g r s k p hp)
      (a • b • S)
  rw [mul_smul]

theorem qsmul_zero
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (c : ℝ) :
    qsmul (I := I) (M := M) g r s k p hp c
        (qzero (I := I) (M := M) g r s k p hp) =
      qzero (I := I) (M := M) g r s k p hp := by
  change Quotient.mk
      (tensorChartSetoid (I := I) (M := M) g r s k p hp)
        (c • (0 : WkpTensor (I := I) (M := M) g r s k p hp)) =
    Quotient.mk (tensorChartSetoid (I := I) (M := M) g r s k p hp) 0
  rw [smul_zero]

theorem qsmul_add
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (c : ℝ)
    (a b : WkpTensorQuot (I := I) (M := M) g r s k p hp) :
    qsmul (I := I) (M := M) g r s k p hp c
        (qadd (I := I) (M := M) g r s k p hp a b) =
      qadd (I := I) (M := M) g r s k p hp
        (qsmul (I := I) (M := M) g r s k p hp c a)
        (qsmul (I := I) (M := M) g r s k p hp c b) := by
  refine Quotient.inductionOn₂ a b ?_
  intro S T
  change Quotient.mk
      (tensorChartSetoid (I := I) (M := M) g r s k p hp) (c • (S + T)) =
    Quotient.mk (tensorChartSetoid (I := I) (M := M) g r s k p hp)
      (c • S + c • T)
  rw [smul_add]

theorem qadd_smul
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (a b : ℝ)
    (u : WkpTensorQuot (I := I) (M := M) g r s k p hp) :
    qsmul (I := I) (M := M) g r s k p hp (a + b) u =
      qadd (I := I) (M := M) g r s k p hp
        (qsmul (I := I) (M := M) g r s k p hp a u)
        (qsmul (I := I) (M := M) g r s k p hp b u) := by
  refine Quotient.inductionOn u ?_
  intro S
  change Quotient.mk
      (tensorChartSetoid (I := I) (M := M) g r s k p hp) ((a + b) • S) =
    Quotient.mk (tensorChartSetoid (I := I) (M := M) g r s k p hp)
      (a • S + b • S)
  rw [add_smul]

theorem qzero_smul
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p)
    (u : WkpTensorQuot (I := I) (M := M) g r s k p hp) :
    qsmul (I := I) (M := M) g r s k p hp 0 u =
      qzero (I := I) (M := M) g r s k p hp := by
  refine Quotient.inductionOn u ?_
  intro S
  change Quotient.mk
      (tensorChartSetoid (I := I) (M := M) g r s k p hp) (0 • S) =
    Quotient.mk (tensorChartSetoid (I := I) (M := M) g r s k p hp) 0
  rw [zero_smul]

/-! ## The theorem-valued algebra and normed structures -/

/-- The explicit quotient operations form an additive commutative group.
This is a structure value, not an instance. -/
noncomputable def tensorQAddGroup
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (p : ℝ≥0∞) (hp : 1 ≤ p) :
    AddCommGroup (WkpTensorQuot (I := I) (M := M) g r s k p hp) where
  zero := qzero (I := I) (M := M) g r s k p hp
  add := qadd (I := I) (M := M) g r s k p hp
  neg := qneg (I := I) (M := M) g r s k p hp
  sub := qsub (I := I) (M := M) g r s k p hp
  add_assoc := qadd_assoc (I := I) (M := M) g r s k hp
  zero_add := qzero_add (I := I) (M := M) g r s k hp
  add_zero := qadd_zero (I := I) (M := M) g r s k hp
  add_comm := qadd_comm (I := I) (M := M) g r s k hp
  neg_add_cancel := qneg_add_self (I := I) (M := M) g r s k hp
  sub_eq_add_neg := qsub_eq_add_neg (I := I) (M := M) g r s k hp
  nsmul := nsmulRec
  zsmul := zsmulRec

private noncomputable def tensorQModule
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (p : ℝ≥0∞) (hp : 1 ≤ p) :
    @Module ℝ
      (WkpTensorQuot (I := I) (M := M) g r s k p hp)
      _ (tensorQAddGroup (I := I) (M := M) g r s k p hp).toAddCommMonoid where
  smul := fun c => qsmul (I := I) (M := M) g r s k p hp c
  one_smul := qone_smul (I := I) (M := M) g r s k hp
  mul_smul := qmul_smul (I := I) (M := M) g r s k hp
  smul_zero := qsmul_zero (I := I) (M := M) g r s k hp
  smul_add := qsmul_add (I := I) (M := M) g r s k hp
  add_smul := qadd_smul (I := I) (M := M) g r s k hp
  zero_smul := qzero_smul (I := I) (M := M) g r s k hp

private noncomputable def tensorQNorm
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (p : ℝ≥0∞) (hp : 1 ≤ p) :
    Norm (WkpTensorQuot (I := I) (M := M) g r s k p hp) where
  norm a :=
    (wkpTensorQNorm (I := I) (M := M) g r s k p hp a).toReal

private noncomputable def tensorQCore
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (p : ℝ≥0∞) (hp : 1 ≤ p) :
    @NormedSpace.Core ℝ
      (WkpTensorQuot (I := I) (M := M) g r s k p hp)
      _ (tensorQAddGroup (I := I) (M := M) g r s k p hp)
      (tensorQModule (I := I) (M := M) g r s k p hp)
      (tensorQNorm (I := I) (M := M) g r s k p hp) where
  norm_nonneg _ := ENNReal.toReal_nonneg
  norm_smul c a := by
    change (wkpTensorQNorm (I := I) (M := M) g r s k p hp
        (qsmul (I := I) (M := M) g r s k p hp c a)).toReal =
      ‖c‖ *
        (wkpTensorQNorm (I := I) (M := M) g r s k p hp a).toReal
    rw [qnorm_smul (I := I) (M := M) g r s k hp,
      ENNReal.toReal_mul, toReal_enorm]
  norm_triangle a b := by
    change (wkpTensorQNorm (I := I) (M := M) g r s k p hp
        (qadd (I := I) (M := M) g r s k p hp a b)).toReal ≤
      (wkpTensorQNorm (I := I) (M := M) g r s k p hp a).toReal +
        (wkpTensorQNorm (I := I) (M := M) g r s k p hp b).toReal
    have ha_ne : wkpTensorQNorm (I := I) (M := M) g r s k p hp a ≠ ∞ :=
      (qnorm_lt_top (I := I) (M := M) g r s k hp a).ne
    have hb_ne : wkpTensorQNorm (I := I) (M := M) g r s k p hp b ≠ ∞ :=
      (qnorm_lt_top (I := I) (M := M) g r s k hp b).ne
    have hadd := qnorm_add_le (I := I) (M := M) g r s k hp a b
    have hreal := ENNReal.toReal_mono
      (ENNReal.add_ne_top.mpr ⟨ha_ne, hb_ne⟩) hadd
    rwa [ENNReal.toReal_add ha_ne hb_ne] at hreal
  norm_eq_zero_iff a := by
    change (wkpTensorQNorm (I := I) (M := M) g r s k p hp a).toReal = 0 ↔
      a = qzero (I := I) (M := M) g r s k p hp
    constructor
    · intro hzero
      rcases (ENNReal.toReal_eq_zero_iff _).mp hzero with hqzero | hqtop
      · exact (qnorm_eq_zero (I := I) (M := M) g r s k hp a).mp hqzero
      · exact ((qnorm_lt_top (I := I) (M := M) g r s k hp a).ne hqtop).elim
    · intro ha
      rw [ha, qnorm_zero (I := I) (M := M) g r s k hp]
      exact ENNReal.toReal_zero

/-- The quotient norm and explicit group operations produce a genuine normed
additive commutative group.  This is a structure value, not an instance. -/
noncomputable def tensorQNormedGroup
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (p : ℝ≥0∞) (hp : 1 ≤ p) :
    NormedAddCommGroup
      (WkpTensorQuot (I := I) (M := M) g r s k p hp) :=
  @NormedAddCommGroup.ofCore ℝ
    (WkpTensorQuot (I := I) (M := M) g r s k p hp)
    _ (tensorQAddGroup (I := I) (M := M) g r s k p hp)
    (tensorQModule (I := I) (M := M) g r s k p hp)
    (tensorQNorm (I := I) (M := M) g r s k p hp)
    (tensorQCore (I := I) (M := M) g r s k p hp)

/-- The real scalar action and quotient norm produce a normed real vector
space.  This is a structure value, not an instance. -/
noncomputable def tensorQNormedSpace
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (p : ℝ≥0∞) (hp : 1 ≤ p) :
    @NormedSpace ℝ
      (WkpTensorQuot (I := I) (M := M) g r s k p hp)
      _ (@NormedAddCommGroup.toSeminormedAddCommGroup
        (WkpTensorQuot (I := I) (M := M) g r s k p hp)
        (tensorQNormedGroup (I := I) (M := M) g r s k p hp)) :=
  @NormedSpace.ofCore ℝ
    (WkpTensorQuot (I := I) (M := M) g r s k p hp)
    _ (@NormedAddCommGroup.toSeminormedAddCommGroup
      (WkpTensorQuot (I := I) (M := M) g r s k p hp)
      (tensorQNormedGroup (I := I) (M := M) g r s k p hp))
    (tensorQModule (I := I) (M := M) g r s k p hp)
    (tensorQCore (I := I) (M := M) g r s k p hp)

/-! ## Completeness for the generated metric -/

/-- The theorem-valued normed structure on `WkpTensorQuot` is complete when
`1 ≤ p < ∞`.  The proof is exactly `qdist_limit`, after identifying the
generated norm distance with the already proved explicit `qdist`. -/
theorem tensorQComplete
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ∞) :
    @CompleteSpace
      (WkpTensorQuot (I := I) (M := M) g r s k p hp)
      (tensorQNormedGroup (I := I) (M := M) g r s k p hp).toUniformSpace := by
  letI : NormedAddCommGroup
      (WkpTensorQuot (I := I) (M := M) g r s k p hp) :=
    tensorQNormedGroup (I := I) (M := M) g r s k p hp
  letI : NormedSpace ℝ
      (WkpTensorQuot (I := I) (M := M) g r s k p hp) :=
    tensorQNormedSpace (I := I) (M := M) g r s k p hp
  have hnorm (a : WkpTensorQuot (I := I) (M := M) g r s k p hp) :
      ‖a‖ =
        (wkpTensorQNorm (I := I) (M := M) g r s k p hp a).toReal := rfl
  have hsub (a b : WkpTensorQuot (I := I) (M := M) g r s k p hp) :
      a - b = qsub (I := I) (M := M) g r s k p hp a b := rfl
  apply Metric.complete_of_cauchySeq_tendsto
  intro u hu
  have hq_cauchy : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m n : ℕ,
      N ≤ m → N ≤ n →
      qdist (I := I) (M := M) g r s k p hp (u m) (u n) < ε := by
    rw [Metric.cauchySeq_iff] at hu
    intro ε hε
    obtain ⟨N, hN⟩ := hu ε hε
    refine ⟨N, ?_⟩
    intro m n hm hn
    have hmn := hN m hm n hn
    rw [dist_eq_norm] at hmn
    simpa only [qdist, hnorm, hsub] using hmn
  obtain ⟨v, hv⟩ :=
    qdist_limit (I := I) (M := M) g r s k hp hp_top u hq_cauchy
  refine ⟨v, ?_⟩
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hv' := hv
  change Tendsto (fun n => dist (u n) v) atTop (𝒰 0)
  simpa only [dist_eq_norm, qdist, hnorm, hsub] using hv'

/-! ## The finite full-Euclidean component carrier -/

/-- The separated scalar Sobolev space on the whole Euclidean model.  Local
chart data enter this carrier only after the strict inner cutoff has made
their zero extension globally Sobolev. -/
abbrev FullWkpQ (d k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p) : Type _ :=
  @EuclidWkpQ d k p hp Set.univ ⟨isOpen_univ⟩

/-- A finite atlas/component array of full-Euclidean Sobolev classes. -/
abbrev FineWkpArray (ι : Type*) (r s k : ℕ) (p : ℝ≥0∞)
    (hp : 1 ≤ p) :=
  ι → TensorCompIdx (E := E) r s →
    FullWkpQ (Module.finrank ℝ E) k p hp

/-- The finite component array inherits a normed additive group from the
theorem-valued scalar quotient structure.  This is not an instance. -/
noncomputable def fineWkpGroup
    (ι : Type*) (r s k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p) :
    NormedAddCommGroup (FineWkpArray (E := E) ι r s k p hp) := by
  letI : NormedAddCommGroup
      (FullWkpQ (Module.finrank ℝ E) k p hp) :=
    @ewkpNormedGroup (Module.finrank ℝ E) k p hp Set.univ ⟨isOpen_univ⟩
  infer_instance

/-- The finite component array inherits a normed real vector-space structure
from the scalar quotient.  This is not an instance. -/
noncomputable def fineWkpSpace
    (ι : Type*) (r s k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p) :
    @NormedSpace ℝ (FineWkpArray (E := E) ι r s k p hp) _
      (@NormedAddCommGroup.toSeminormedAddCommGroup
        (FineWkpArray (E := E) ι r s k p hp)
        (fineWkpGroup (E := E) ι r s k p hp)) := by
  letI : NormedAddCommGroup
      (FullWkpQ (Module.finrank ℝ E) k p hp) :=
    @ewkpNormedGroup (Module.finrank ℝ E) k p hp Set.univ ⟨isOpen_univ⟩
  letI : NormedSpace ℝ
      (FullWkpQ (Module.finrank ℝ E) k p hp) :=
    @ewkpNormedSpace (Module.finrank ℝ E) k p hp Set.univ ⟨isOpen_univ⟩
  infer_instance

/-- The finite component array is complete because every scalar quotient
factor is complete.  This is a structure value, not an instance. -/
theorem fineWkpComplete
    (ι : Type*) (r s k : ℕ) {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hp_top : p ≠ ∞) :
    @CompleteSpace (FineWkpArray (E := E) ι r s k p hp)
      (fineWkpGroup (E := E) ι r s k p hp).toUniformSpace := by
  letI : NormedAddCommGroup
      (FullWkpQ (Module.finrank ℝ E) k p hp) :=
    @ewkpNormedGroup (Module.finrank ℝ E) k p hp Set.univ ⟨isOpen_univ⟩
  letI : NormedSpace ℝ
      (FullWkpQ (Module.finrank ℝ E) k p hp) :=
    @ewkpNormedSpace (Module.finrank ℝ E) k p hp Set.univ ⟨isOpen_univ⟩
  letI : CompleteSpace
      (FullWkpQ (Module.finrank ℝ E) k p hp) :=
    @ewkpComplete (Module.finrank ℝ E) _ k p hp hp_top Set.univ ⟨isOpen_univ⟩
  infer_instance

/-! ## Fine localization of genuine tensor components -/

local notation "EuclN" =>
  EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-- Multiplication by one fixed smooth manifold function preserves the
Sobolev regularity of one fixed canonical chart component.  Unlike the
manifold-level multiplication theorem, this local form assumes regularity
only in the chart under consideration. -/
private theorem chartMul_mem
    (k : ℕ) {p : ℝ≥0∞} (hp : 1 ≤ p)
    (φ : C^∞⟮I, M; ℝ⟯) (α : M) {u : M → ℝ}
    (hu : MemWkp (d := Module.finrank ℝ E) k p
      (Chart.chartPushed (I := I) (M := M)
        (chartAtlasPOU I M) α u)
      (Chart.chartTargetEuclid (I := I) (M := M) α)) :
    MemWkp (d := Module.finrank ℝ E) k p
      (Chart.chartPushed (I := I) (M := M)
        (chartAtlasPOU I M) α
        (fun x => (φ : M → ℝ) x * u x))
      (Chart.chartTargetEuclid (I := I) (M := M) α) := by
  classical
  obtain ⟨b, hb_smooth, _, hb_one, hb_supp⟩ :=
    Chart.exists_chart_cutoff_M (I := I) (M := M) α
  have hbφ_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => b x * (φ : M → ℝ) x) :=
    hb_smooth.mul φ.contMDiff
  have hbφ_supp : tsupport (fun x : M => b x * (φ : M → ℝ) x) ⊆
      (chartAt H α).source := by
    have heq : (fun x : M => b x * (φ : M → ℝ) x) =
        (fun x : M => b x • (φ : M → ℝ) x) := by
      funext x
      rfl
    rw [heq]
    exact (tsupport_smul_subset_left (f := b)
      (g := (φ : M → ℝ))).trans hb_supp
  obtain ⟨C, _hC, hC⟩ :=
    Chart.smoothExtensionScalar_iteratedFDeriv_bound
      (I := I) (M := M) α hbφ_smooth hbφ_supp k
  let Ω : Set EuclN :=
    Chart.chartTargetEuclid (I := I) (M := M) α
  let Λ : EuclN → ℝ :=
    Chart.smoothExtensionScalar (I := I) (M := M) α
      (fun x : M => b x * (φ : M → ℝ) x)
  have hΩ : IsOpen Ω :=
    Chart.chartTargetEuclid_isOpen (I := I) (M := M) α
  have hΛ : ContDiff ℝ (⊤ : ℕ∞) Λ := by
    exact Chart.contDiff_smoothExtensionScalar
      (I := I) (M := M) α hbφ_smooth hbφ_supp
  have hfactor :
      Chart.chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
          (fun x => (φ : M → ℝ) x * u x) =ᵐ[volume.restrict Ω]
        (fun y => Λ y *
          Chart.chartPushed (I := I) (M := M)
            (chartAtlasPOU I M) α u y) := by
    refine (MeasureTheory.ae_restrict_iff'
      (Chart.chartTargetEuclid_measurableSet
        (I := I) (M := M) α)).mpr ?_
    refine Filter.Eventually.of_forall (fun y hy => ?_)
    exact Chart.chartPushed_mul_eq_smoothExtension_mul_chartPushed
      (I := I) (M := M) (α := α) (b := b)
      (φ := (φ : M → ℝ)) (u := u) hb_one hy
  have hΛbound : ∀ j ≤ k, ∀ y ∈ Ω,
      ‖iteratedFDeriv ℝ j Λ y‖ ≤ C :=
    fun j hj y _ => hC j hj y
  have hprod : MemWkp (d := Module.finrank ℝ E) k p
      (fun y => Λ y *
        Chart.chartPushed (I := I) (M := M)
          (chartAtlasPOU I M) α u y) Ω :=
    MemWkp.smul_smooth_bounded (d := Module.finrank ℝ E)
      k hp hΩ hΛ hΛbound hu
  exact (MemWkp_congr_ae (d := Module.finrank ℝ E)
    hp hΩ hfactor.symm).mp hprod

/-- The fine localization of one tensor component.  It first takes the
canonical POU-weighted component and then multiplies it by the additional
fine partition weight `φ`.  The raw pushforward makes the result identically
zero outside the chart target. -/
noncomputable def fineLocComp
    (r s : ℕ) (φ : C^∞⟮I, M; ℝ⟯)
    (S : RSTensorSection I M r s) (α : M)
    (P : TensorCompIdx (E := E) r s) : EuclN → ℝ :=
  Chart.chartPushedRaw (I := I) (M := M) α
    (fun x =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x *
        ((φ : M → ℝ) x *
          secCompRaw (I := I) (M := M) r s S α P.1 P.2 x))

/-- On the chart target, fine localization is ordinary scalar
multiplication of the canonical tensor component. -/
theorem fineLoc_apply
    (r s : ℕ) (φ : C^∞⟮I, M; ℝ⟯)
    (S : RSTensorSection I M r s) (α : M)
    (P : TensorCompIdx (E := E) r s) {y : EuclN}
    (hy : y ∈ Chart.chartTargetEuclid (I := I) (M := M) α) :
    fineLocComp (I := I) (M := M) r s φ S α P y =
      (φ : M → ℝ)
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
        secChartComp (I := I) (M := M) r s S α P.1 P.2 y := by
  rw [fineLocComp,
    Chart.chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy,
    secComp_apply_mem (I := I) (M := M) r s S α P.1 P.2 hy]
  unfold secCompPou
  ring

/-- Fine-localized components vanish outside their chart target. -/
theorem fineLoc_apply_off
    (r s : ℕ) (φ : C^∞⟮I, M; ℝ⟯)
    (S : RSTensorSection I M r s) (α : M)
    (P : TensorCompIdx (E := E) r s) {y : EuclN}
    (hy : y ∉ Chart.chartTargetEuclid (I := I) (M := M) α) :
    fineLocComp (I := I) (M := M) r s φ S α P y = 0 := by
  unfold fineLocComp
  exact Chart.chartPushedRaw_apply_of_notMem
    (I := I) (M := M) α _ hy

/-- Fine localization is additive before passing to either quotient. -/
theorem fineLoc_add
    (r s : ℕ) (φ : C^∞⟮I, M; ℝ⟯)
    (S T : RSTensorSection I M r s) (α : M)
    (P : TensorCompIdx (E := E) r s) :
    fineLocComp (I := I) (M := M) r s φ (S + T) α P =
      fineLocComp (I := I) (M := M) r s φ S α P +
        fineLocComp (I := I) (M := M) r s φ T α P := by
  funext y
  by_cases hy : y ∈ Chart.chartTargetEuclid (I := I) (M := M) α
  · rw [fineLoc_apply (I := I) (M := M) r s φ (S + T) α P hy,
      fineLoc_apply (I := I) (M := M) r s φ S α P hy,
      fineLoc_apply (I := I) (M := M) r s φ T α P hy,
      secChartComp_add (I := I) (M := M) r s S T α P.1 P.2]
    simp only [Pi.add_apply]
    ring
  · rw [fineLoc_apply_off (I := I) (M := M) r s φ (S + T) α P hy,
      fineLoc_apply_off (I := I) (M := M) r s φ S α P hy,
      fineLoc_apply_off (I := I) (M := M) r s φ T α P hy]
    rfl

/-- Fine localization commutes with real scalar multiplication before
passing to either quotient. -/
theorem fineLoc_smul
    (r s : ℕ) (φ : C^∞⟮I, M; ℝ⟯) (c : ℝ)
    (S : RSTensorSection I M r s) (α : M)
    (P : TensorCompIdx (E := E) r s) :
    fineLocComp (I := I) (M := M) r s φ (c • S) α P =
      c • fineLocComp (I := I) (M := M) r s φ S α P := by
  funext y
  by_cases hy : y ∈ Chart.chartTargetEuclid (I := I) (M := M) α
  · rw [fineLoc_apply (I := I) (M := M) r s φ (c • S) α P hy,
      fineLoc_apply (I := I) (M := M) r s φ S α P hy,
      secChartComp_smul (I := I) (M := M) r s c S α P.1 P.2]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  · rw [fineLoc_apply_off (I := I) (M := M) r s φ (c • S) α P hy,
      fineLoc_apply_off (I := I) (M := M) r s φ S α P hy]
    simp

/-- Fine localization retains the compact canonical POU support. -/
theorem fineLoc_support
    (r s : ℕ) (φ : C^∞⟮I, M; ℝ⟯)
    (S : RSTensorSection I M r s) (α : M)
    (P : TensorCompIdx (E := E) r s) :
    tsupport (fineLocComp (I := I) (M := M) r s φ S α P) ⊆
      Chart.chartTargetEuclid (I := I) (M := M) α := by
  unfold fineLocComp
  exact Chart.ChartTower.tsupport_chartPushedRaw_pou_mul_subset_target
    (I := I) (M := M) α
      (fun x => (φ : M → ℝ) x *
        secCompRaw (I := I) (M := M) r s S α P.1 P.2 x)

/-- Fine localization has compact Euclidean support. -/
theorem fineLoc_compact
    (r s : ℕ) (φ : C^∞⟮I, M; ℝ⟯)
    (S : RSTensorSection I M r s) (α : M)
    (P : TensorCompIdx (E := E) r s) :
    HasCompactSupport
      (fineLocComp (I := I) (M := M) r s φ S α P) := by
  unfold fineLocComp
  exact Chart.ChartTower.hasCompactSupport_chartPushedRaw_pou_mul
    (I := I) (M := M) α
      (fun x => (φ : M → ℝ) x *
        secCompRaw (I := I) (M := M) r s S α P.1 P.2 x)

private theorem fineLoc_target_ae
    (r s : ℕ) (φ : C^∞⟮I, M; ℝ⟯)
    (S : RSTensorSection I M r s) (α : M)
    (P : TensorCompIdx (E := E) r s) :
    fineLocComp (I := I) (M := M) r s φ S α P =ᵐ[
      volume.restrict
        (Chart.chartTargetEuclid (I := I) (M := M) α)]
      Chart.chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        (fun x => (φ : M → ℝ) x *
          secCompRaw (I := I) (M := M) r s S α P.1 P.2 x) := by
  simpa only [fineLocComp] using
    (Chart.chartPushedRaw_pou_mul_ae_eq_chartPushed_on_target
      (I := I) (M := M) (chartAtlasPOU I M) α
      (fun x => (φ : M → ℝ) x *
        secCompRaw (I := I) (M := M) r s S α P.1 P.2 x))

private theorem secComp_target_ae
    (r s : ℕ) (S : RSTensorSection I M r s) (α : M)
    (P : TensorCompIdx (E := E) r s) :
    secChartComp (I := I) (M := M) r s S α P.1 P.2 =ᵐ[
      volume.restrict
        (Chart.chartTargetEuclid (I := I) (M := M) α)]
      Chart.chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        (secCompRaw (I := I) (M := M) r s S α P.1 P.2) := by
  simpa only [secChartComp, secCompPou] using
    (Chart.chartPushedRaw_pou_mul_ae_eq_chartPushed_on_target
      (I := I) (M := M) (chartAtlasPOU I M) α
      (secCompRaw (I := I) (M := M) r s S α P.1 P.2))

/-- Fine localization is a bounded operation from the genuine tensor norm to
one scalar chart norm.  The constant depends only on the fixed fine weight,
chart, Sobolev order, and exponent, never on the tensor section. -/
theorem fineLoc_joint
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    (φ : C^∞⟮I, M; ℝ⟯) (α : M)
    (P : TensorCompIdx (E := E) r s) :
    ∃ K : ℝ, 0 < K ∧
      ∀ S : WkpTensor (I := I) (M := M) g r s k p hp,
        MemWkp (d := Module.finrank ℝ E) k p
            (fineLocComp (I := I) (M := M) r s φ S.1 α P)
            (Chart.chartTargetEuclid (I := I) (M := M) α) ∧
          wkpNorm (d := Module.finrank ℝ E) k p
              (fineLocComp (I := I) (M := M) r s φ S.1 α P)
              (Chart.chartTargetEuclid (I := I) (M := M) α) ≤
            ENNReal.ofReal K *
              wkpTensorNorm (I := I) (M := M) g k p S.1 := by
  obtain ⟨K, hK, hKbound⟩ :=
    Chart.MemWkpChart_smooth_mul_per_chart_quant
      (I := I) (M := M) k hp hp_top φ α
  refine ⟨K, hK, ?_⟩
  intro S
  let Ω : Set EuclN :=
    Chart.chartTargetEuclid (I := I) (M := M) α
  have hΩ : IsOpen Ω :=
    Chart.chartTargetEuclid_isOpen (I := I) (M := M) α
  have hsecRaw : MemWkp (d := Module.finrank ℝ E) k p
      (secChartComp (I := I) (M := M) r s S.1 α P.1 P.2) Ω :=
    S.2 α P.1 P.2
  have hsec : MemWkp (d := Module.finrank ℝ E) k p
      (Chart.chartPushed (I := I) (M := M)
        (chartAtlasPOU I M) α
        (secCompRaw (I := I) (M := M) r s S.1 α P.1 P.2)) Ω :=
    (MemWkp_congr_ae (d := Module.finrank ℝ E) hp hΩ
      (secComp_target_ae (I := I) (M := M) r s S.1 α P)).mp hsecRaw
  have hlocChart := chartMul_mem (I := I) (M := M)
    k hp φ α hsec
  have hloc : MemWkp (d := Module.finrank ℝ E) k p
      (fineLocComp (I := I) (M := M) r s φ S.1 α P) Ω :=
    (MemWkp_congr_ae (d := Module.finrank ℝ E) hp hΩ
      (fineLoc_target_ae (I := I) (M := M) r s φ S.1 α P).symm).mp
        hlocChart
  refine ⟨hloc, ?_⟩
  calc
    wkpNorm (d := Module.finrank ℝ E) k p
        (fineLocComp (I := I) (M := M) r s φ S.1 α P) Ω =
      wkpNorm (d := Module.finrank ℝ E) k p
        (Chart.chartPushed (I := I) (M := M)
          (chartAtlasPOU I M) α
          (fun x => (φ : M → ℝ) x *
            secCompRaw (I := I) (M := M) r s S.1 α P.1 P.2 x)) Ω :=
        wkpNorm_congr_ae (d := Module.finrank ℝ E) hp hΩ
          (fineLoc_target_ae (I := I) (M := M) r s φ S.1 α P)
    _ ≤ ENNReal.ofReal K *
        wkpNorm (d := Module.finrank ℝ E) k p
          (Chart.chartPushed (I := I) (M := M)
            (chartAtlasPOU I M) α
            (secCompRaw (I := I) (M := M) r s S.1 α P.1 P.2)) Ω :=
      hKbound hsec
    _ = ENNReal.ofReal K *
        wkpNorm (d := Module.finrank ℝ E) k p
          (secChartComp (I := I) (M := M) r s S.1 α P.1 P.2) Ω := by
      rw [wkpNorm_congr_ae (d := Module.finrank ℝ E) hp hΩ
        (secComp_target_ae (I := I) (M := M) r s S.1 α P).symm]
    _ ≤ ENNReal.ofReal K *
        wkpTensorNorm (I := I) (M := M) g k p S.1 :=
      mul_le_mul_left'
        (wkpNorm_secComp_le (I := I) (M := M) g k p
          S.1 α P.1 P.2) _

/-- The same fine-localized component, viewed on all of Euclidean space by
zero extension, remains in `W^{k,p}`. -/
theorem fineLoc_mem_univ
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    (φ : C^∞⟮I, M; ℝ⟯) (α : M)
    (P : TensorCompIdx (E := E) r s)
    (S : WkpTensor (I := I) (M := M) g r s k p hp) :
    MemWkp (d := Module.finrank ℝ E) k p
      (fineLocComp (I := I) (M := M) r s φ S.1 α P) Set.univ := by
  apply MemWkp.extend_zero (d := Module.finrank ℝ E) hp hp_top
    (Chart.chartTargetEuclid_isOpen (I := I) (M := M) α)
    isOpen_univ (subset_univ _)
  · exact ((fineLoc_joint (I := I) (M := M) g r s k hp hp_top
      φ α P).choose_spec.2 S).1
  · exact fineLoc_support (I := I) (M := M) r s φ S.1 α P
  · exact fineLoc_compact (I := I) (M := M) r s φ S.1 α P

/-- The full-space norm of a fine component is exactly its chart-target
norm; no extension loss is paid. -/
theorem fineLoc_norm_univ
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    (φ : C^∞⟮I, M; ℝ⟯) (α : M)
    (P : TensorCompIdx (E := E) r s)
    (S : WkpTensor (I := I) (M := M) g r s k p hp) :
    wkpNorm (d := Module.finrank ℝ E) k p
        (fineLocComp (I := I) (M := M) r s φ S.1 α P) Set.univ =
      wkpNorm (d := Module.finrank ℝ E) k p
        (fineLocComp (I := I) (M := M) r s φ S.1 α P)
        (Chart.chartTargetEuclid (I := I) (M := M) α) := by
  exact wkpNorm_extend_zero (d := Module.finrank ℝ E) hp hp_top
    (Chart.chartTargetEuclid_isOpen (I := I) (M := M) α)
    isOpen_univ (subset_univ _)
    ((fineLoc_joint (I := I) (M := M) g r s k hp hp_top
      φ α P).choose_spec.2 S).1
    (fineLoc_support (I := I) (M := M) r s φ S.1 α P)
    (fineLoc_compact (I := I) (M := M) r s φ S.1 α P)

/-- A fine-localized representative in the full Euclidean Sobolev carrier. -/
noncomputable def fineLocWkp
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    (φ : C^∞⟮I, M; ℝ⟯) (α : M)
    (P : TensorCompIdx (E := E) r s)
    (S : WkpTensor (I := I) (M := M) g r s k p hp) :
    @EuclidWkp (Module.finrank ℝ E) k p hp Set.univ ⟨isOpen_univ⟩ :=
  ⟨fineLocComp (I := I) (M := M) r s φ S.1 α P,
    fineLoc_mem_univ (I := I) (M := M) g r s k hp hp_top φ α P S⟩

/-- Tensor a.e. equality descends through every fine localization. -/
theorem fineLoc_ae
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (φ : C^∞⟮I, M; ℝ⟯) (α : M)
    (P : TensorCompIdx (E := E) r s)
    {S T : RSTensorSection I M r s}
    (hST : TensorAEEq (I := I) (M := M) g S T) :
    fineLocComp (I := I) (M := M) r s φ S α P =ᵐ[volume]
      fineLocComp (I := I) (M := M) r s φ T α P := by
  let Ω : Set EuclN :=
    Chart.chartTargetEuclid (I := I) (M := M) α
  apply MeasureTheory.ae_of_ae_restrict_of_ae_restrict_compl Ω
  · have hmem : ∀ᵐ y ∂(volume : Measure EuclN).restrict Ω, y ∈ Ω :=
      ae_restrict_mem
        (Chart.chartTargetEuclid_measurableSet (I := I) (M := M) α)
    filter_upwards [hST α P.1 P.2, hmem] with y hSy hy
    rw [fineLoc_apply (I := I) (M := M) r s φ S α P hy,
      fineLoc_apply (I := I) (M := M) r s φ T α P hy, hSy]
  · have hmem : ∀ᵐ y ∂(volume : Measure EuclN).restrict Ωᶜ, y ∈ Ωᶜ :=
      ae_restrict_mem
        (Chart.chartTargetEuclid_measurableSet
          (I := I) (M := M) α).compl
    filter_upwards [hmem] with y hy
    rw [fineLoc_apply_off (I := I) (M := M) r s φ S α P hy,
      fineLoc_apply_off (I := I) (M := M) r s φ T α P hy]

/-- One fine block of the quotient-level extraction map. -/
noncomputable def fineLocMap
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    (φ : C^∞⟮I, M; ℝ⟯) (α : M)
    (P : TensorCompIdx (E := E) r s) :
    WkpTensorQuot (I := I) (M := M) g r s k p hp →
      FullWkpQ (Module.finrank ℝ E) k p hp :=
  Quotient.lift
    (fun S => Quotient.mk
      (@euclidWkpSetoid (Module.finrank ℝ E) k p hp Set.univ
        ⟨isOpen_univ⟩)
      (fineLocWkp (I := I) (M := M) g r s k hp hp_top φ α P S))
    (fun S T hST => Quotient.sound (by
      change fineLocComp (I := I) (M := M) r s φ S.1 α P =ᵐ[
        volume.restrict Set.univ]
          fineLocComp (I := I) (M := M) r s φ T.1 α P
      simpa only [Measure.restrict_univ] using
        fineLoc_ae (I := I) (M := M) g r s φ α P hST))

/-- A quotient-level fine block preserves addition. -/
theorem fineLocMap_add
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    (φ : C^∞⟮I, M; ℝ⟯) (α : M)
    (P : TensorCompIdx (E := E) r s)
    (a b : WkpTensorQuot (I := I) (M := M) g r s k p hp) :
    fineLocMap (I := I) (M := M) g r s k hp hp_top φ α P
        (qadd (I := I) (M := M) g r s k p hp a b) =
      eadd k p hp Set.univ
        (fineLocMap (I := I) (M := M) g r s k hp hp_top φ α P a)
        (fineLocMap (I := I) (M := M) g r s k hp hp_top φ α P b) := by
  refine Quotient.inductionOn₂ a b ?_
  intro S T
  apply Quotient.sound
  change fineLocComp (I := I) (M := M) r s φ (S.1 + T.1) α P =ᵐ[
      volume.restrict Set.univ]
    (fineLocComp (I := I) (M := M) r s φ S.1 α P +
      fineLocComp (I := I) (M := M) r s φ T.1 α P)
  exact Filter.Eventually.of_forall (fun y =>
    congrFun (fineLoc_add (I := I) (M := M) r s φ S.1 T.1 α P) y)

/-- A quotient-level fine block preserves real scalar multiplication. -/
theorem fineLocMap_smul
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    (φ : C^∞⟮I, M; ℝ⟯) (α : M)
    (P : TensorCompIdx (E := E) r s) (c : ℝ)
    (a : WkpTensorQuot (I := I) (M := M) g r s k p hp) :
    fineLocMap (I := I) (M := M) g r s k hp hp_top φ α P
        (qsmul (I := I) (M := M) g r s k p hp c a) =
      esmul k p hp Set.univ c
        (fineLocMap (I := I) (M := M) g r s k hp hp_top φ α P a) := by
  refine Quotient.inductionOn a ?_
  intro S
  apply Quotient.sound
  change fineLocComp (I := I) (M := M) r s φ (c • S.1) α P =ᵐ[
      volume.restrict Set.univ]
    (c • fineLocComp (I := I) (M := M) r s φ S.1 α P)
  exact Filter.Eventually.of_forall (fun y =>
    congrFun (fineLoc_smul (I := I) (M := M) r s φ c S.1 α P) y)

/-- The quotient norm of one fine extraction block is bounded by the genuine
tensor quotient norm. -/
theorem fineLocMap_bound
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    (φ : C^∞⟮I, M; ℝ⟯) (α : M)
    (P : TensorCompIdx (E := E) r s) :
    ∃ K : ℝ, 0 < K ∧
      ∀ a : WkpTensorQuot (I := I) (M := M) g r s k p hp,
        ewkpNorm (d := Module.finrank ℝ E) k p hp Set.univ
            (fineLocMap (I := I) (M := M) g r s k hp hp_top φ α P a) ≤
          ENNReal.ofReal K *
            wkpTensorQNorm (I := I) (M := M) g r s k p hp a := by
  obtain ⟨K, hK, hjoint⟩ :=
    fineLoc_joint (I := I) (M := M) g r s k hp hp_top φ α P
  refine ⟨K, hK, ?_⟩
  intro a
  refine Quotient.inductionOn a ?_
  intro S
  change wkpNorm (d := Module.finrank ℝ E) k p
      (fineLocComp (I := I) (M := M) r s φ S.1 α P) Set.univ ≤
    ENNReal.ofReal K *
      wkpTensorNorm (I := I) (M := M) g k p S.1
  rw [fineLoc_norm_univ (I := I) (M := M) g r s k hp hp_top φ α P S]
  exact (hjoint S).2

/-- Simultaneous quotient-level extraction into a finite family of fine
blocks.  Continuous linearity is packaged after installing the theorem-valued
normed structures locally. -/
noncomputable def fineExtractMap
    {ι : Type*} (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    (φ : ι → C^∞⟮I, M; ℝ⟯) (α : ι → M) :
    WkpTensorQuot (I := I) (M := M) g r s k p hp →
      FineWkpArray (E := E) ι r s k p hp :=
  fun a z P =>
    fineLocMap (I := I) (M := M) g r s k hp hp_top (φ z) (α z) P a

/-- The finite extraction map preserves the explicit quotient additions
coordinatewise. -/
theorem fineExtract_add
    {ι : Type*} (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    (φ : ι → C^∞⟮I, M; ℝ⟯) (α : ι → M)
    (a b : WkpTensorQuot (I := I) (M := M) g r s k p hp) :
    fineExtractMap (I := I) (M := M) g r s k hp hp_top φ α
        (qadd (I := I) (M := M) g r s k p hp a b) =
      fun z P => eadd k p hp Set.univ
        (fineExtractMap (I := I) (M := M) g r s k hp hp_top φ α a z P)
        (fineExtractMap (I := I) (M := M) g r s k hp hp_top φ α b z P) := by
  funext z P
  exact fineLocMap_add (I := I) (M := M) g r s k hp hp_top
    (φ z) (α z) P a b

/-- The finite extraction map preserves the explicit quotient scalar actions
coordinatewise. -/
theorem fineExtract_smul
    {ι : Type*} (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    (φ : ι → C^∞⟮I, M; ℝ⟯) (α : ι → M) (c : ℝ)
    (a : WkpTensorQuot (I := I) (M := M) g r s k p hp) :
    fineExtractMap (I := I) (M := M) g r s k hp hp_top φ α
        (qsmul (I := I) (M := M) g r s k p hp c a) =
      fun z P => esmul k p hp Set.univ c
        (fineExtractMap (I := I) (M := M) g r s k hp hp_top φ α a z P) := by
  funext z P
  exact fineLocMap_smul (I := I) (M := M) g r s k hp hp_top
    (φ z) (α z) P c a

end Tensor
end Sobolev
end Analysis
end DifferentialGeometry
