import DifferentialGeometry.Analysis.Sobolev.Chart.Defs
import DifferentialGeometry.Analysis.Sobolev.Chart.Banach

/-!
# Atlas-flexible chart-based Sobolev norms on a smooth manifold

The file `Chart.lean` defines `wkpNormChart g k p u` using a fixed canonical
partition of unity `chartAtlasPOU I M`. This file generalises that definition
to any smooth partition of unity subordinate to the canonical chart family
`fun α : M => (chartAt H α).source`, and establishes that

* `wkpNormChartGen g k p ρ u` reduces to `wkpNormChart g k p u` when `ρ` is the
  canonical chart-atlas POU;
* the norm depends only on the pointwise values of `ρ` (extensional congruence);
* basic algebraic and structural properties (zero function, linearity, ae
  invariance) carry over from the canonical case.

The file additionally provides standalone infrastructure useful for downstream
atlas-comparison work:

* finite-support truncation of the POU sum on compact `M`;
* product-of-POU support analysis (used by atlas-comparison arguments);
* a finite-form `wkpNormChartFin` that sums over the finite set of POU members
  with non-empty support on compact `M`, with proof that it equals the full
  `tsum` form.

The current Sobolev infrastructure provides a Leibniz product rule for first
order weak partial derivatives (`HasWeakPartialDeriv.mul_smooth`) but no
analogue at order ≥ 2 and no chain rule for higher order weak partials under a
smooth diffeomorphism. Consequently, comparing the chart-Sobolev norms attached
to two distinct POUs (or two distinct atlases) at order `k ≥ 1` requires
infrastructure that does not yet exist in the project. The structural framework
is established here so that, once those analytical tools become available, the
multiplicative-equivalence statement can be formulated cleanly using
`wkpNormChartGen`.
-/

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Function
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Chart

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The general chart-pushed `Wkp`-membership predicate, parametrised by an
arbitrary smooth partition of unity `ρ : SmoothPartitionOfUnity M I M univ`
indexed by `M` and subordinate to the canonical chart family. -/
def MemWkpChartGen [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (_g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (k : ℕ) (p : ℝ≥0∞)
    (ρ : SmoothPartitionOfUnity M I M Set.univ)
    (u : M → ℝ) : Prop :=
  ∀ α : M,
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E)
      k p
      (chartPushed (I := I) (M := M) ρ α u)
      (chartTargetEuclid (I := I) (M := M) α)

/-- The general chart-based `Wkp` norm, parametrised by a smooth partition of
unity `ρ : SmoothPartitionOfUnity M I M univ` indexed by `M` and subordinate
to the canonical chart family. -/
def wkpNormChartGen [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (_g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (k : ℕ) (p : ℝ≥0∞)
    (ρ : SmoothPartitionOfUnity M I M Set.univ)
    (u : M → ℝ) : ℝ≥0∞ :=
  ∑' α : M,
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
      (d := Module.finrank ℝ E)
      k p
      (chartPushed (I := I) (M := M) ρ α u)
      (chartTargetEuclid (I := I) (M := M) α)

/-- For the canonical chart-atlas POU, `MemWkpChartGen` reduces to `MemWkpChart`. -/
theorem MemWkpChartGen_chartAtlasPOU
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (k : ℕ) (p : ℝ≥0∞) (u : M → ℝ) :
    MemWkpChartGen (I := I) (M := M) g k p
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) u ↔
      MemWkpChart (I := I) (M := M) g k p u := Iff.rfl

/-- For the canonical chart-atlas POU, `wkpNormChartGen` reduces to
`wkpNormChart`. -/
theorem wkpNormChartGen_chartAtlasPOU
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (k : ℕ) (p : ℝ≥0∞) (u : M → ℝ) :
    wkpNormChartGen (I := I) (M := M) g k p
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) u =
      wkpNormChart (I := I) (M := M) g k p u := rfl

/-- Pointwise equality of POU values implies pointwise equality of chart-pushed
functions. -/
theorem chartPushed_congr_of_pointwise_eq
    (ρ ρ' : SmoothPartitionOfUnity M I M Set.univ)
    (h : ∀ α : M, ∀ x : M, (ρ α : C^∞⟮I, M; ℝ⟯) x = (ρ' α : C^∞⟮I, M; ℝ⟯) x)
    (α : M) (u : M → ℝ) :
    chartPushed (I := I) (M := M) ρ α u =
      chartPushed (I := I) (M := M) ρ' α u := by
  funext y
  unfold chartPushed
  rw [h α]

/-- Two pointwise-equal POUs yield the same general chart-Sobolev norm. -/
theorem wkpNormChartGen_congr_of_pointwise_eq
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (k : ℕ) (p : ℝ≥0∞)
    (ρ ρ' : SmoothPartitionOfUnity M I M Set.univ)
    (h : ∀ α : M, ∀ x : M, (ρ α : C^∞⟮I, M; ℝ⟯) x = (ρ' α : C^∞⟮I, M; ℝ⟯) x)
    (u : M → ℝ) :
    wkpNormChartGen (I := I) (M := M) g k p ρ u =
      wkpNormChartGen (I := I) (M := M) g k p ρ' u := by
  unfold wkpNormChartGen
  refine tsum_congr (fun α => ?_)
  rw [chartPushed_congr_of_pointwise_eq (I := I) (M := M) ρ ρ' h α u]

/-- Two pointwise-equal POUs yield the same general chart-Sobolev membership
predicate. -/
theorem MemWkpChartGen_congr_of_pointwise_eq
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {k : ℕ} {p : ℝ≥0∞}
    (ρ ρ' : SmoothPartitionOfUnity M I M Set.univ)
    (h : ∀ α : M, ∀ x : M, (ρ α : C^∞⟮I, M; ℝ⟯) x = (ρ' α : C^∞⟮I, M; ℝ⟯) x)
    (u : M → ℝ) :
    MemWkpChartGen (I := I) (M := M) g k p ρ u ↔
      MemWkpChartGen (I := I) (M := M) g k p ρ' u := by
  refine ⟨fun H α => ?_, fun H α => ?_⟩
  · have hcp := chartPushed_congr_of_pointwise_eq (I := I) (M := M) ρ ρ' h α u
    rw [← hcp]
    exact H α
  · have hcp := chartPushed_congr_of_pointwise_eq (I := I) (M := M) ρ ρ'
      h α u
    rw [hcp]
    exact H α

omit [IsManifold I ∞ M] in
/-- Generalised chart-pushed-of-zero is zero. -/
theorem chartPushed_zero_gen
    (ρ : SmoothPartitionOfUnity M I M Set.univ) (α : M) :
    chartPushed (I := I) (M := M) ρ α (fun _ => (0 : ℝ)) =
      (fun _ => (0 : ℝ)) :=
  chartPushed_zero (I := I) (M := M) ρ α

/-- Membership of the zero function in `MemWkpChartGen`. -/
theorem MemWkpChartGen_zero_fun
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (ρ : SmoothPartitionOfUnity M I M Set.univ) :
    MemWkpChartGen (I := I) (M := M) g k p ρ (fun _ : M => (0 : ℝ)) := by
  intro α
  rw [chartPushed_zero_gen]
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_zero_fun
    (d := Module.finrank ℝ E) hp (chartTargetEuclid_isOpen (I := I) (M := M) α)

/-- The general chart-based norm of the zero function is zero. -/
theorem wkpNormChartGen_zero_fun
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (ρ : SmoothPartitionOfUnity M I M Set.univ) :
    wkpNormChartGen (I := I) (M := M) g k p ρ (fun _ : M => (0 : ℝ)) = 0 := by
  unfold wkpNormChartGen
  have hpt : ∀ α : M,
      DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
        (d := Module.finrank ℝ E) k p
        (chartPushed (I := I) (M := M) ρ α (fun _ : M => (0 : ℝ)))
        (chartTargetEuclid (I := I) (M := M) α) = 0 := by
    intro α
    rw [chartPushed_zero_gen]
    exact DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_zero_fun_zero
      (d := Module.finrank ℝ E) hp
      (chartTargetEuclid_isOpen (I := I) (M := M) α)
  rw [tsum_congr hpt]
  exact tsum_zero

omit [IsManifold I ∞ M] in
/-- Generalised chart-pushed of a sum is the sum of chart-pushed values. -/
theorem chartPushed_add_gen
    (ρ : SmoothPartitionOfUnity M I M Set.univ) (α : M) (u v : M → ℝ) :
    chartPushed (I := I) (M := M) ρ α (fun x => u x + v x) =
      (fun y =>
        chartPushed (I := I) (M := M) ρ α u y +
          chartPushed (I := I) (M := M) ρ α v y) :=
  chartPushed_add (I := I) (M := M) ρ α u v

omit [IsManifold I ∞ M] in
/-- Generalised chart-pushed of a constant scalar multiple. -/
theorem chartPushed_const_smul_gen
    (ρ : SmoothPartitionOfUnity M I M Set.univ) (α : M) (c : ℝ) (u : M → ℝ) :
    chartPushed (I := I) (M := M) ρ α (fun x => c * u x) =
      (fun y => c * chartPushed (I := I) (M := M) ρ α u y) :=
  chartPushed_const_smul (I := I) (M := M) ρ α c u

/-- `MemWkpChartGen` is closed under addition. -/
theorem MemWkpChartGen_add
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (ρ : SmoothPartitionOfUnity M I M Set.univ)
    {u v : M → ℝ}
    (hu : MemWkpChartGen (I := I) (M := M) g k p ρ u)
    (hv : MemWkpChartGen (I := I) (M := M) g k p ρ v) :
    MemWkpChartGen (I := I) (M := M) g k p ρ (fun x => u x + v x) := by
  intro α
  rw [chartPushed_add_gen]
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.add
    (d := Module.finrank ℝ E) hp
    (chartTargetEuclid_isOpen (I := I) (M := M) α)
    (hu α) (hv α)

/-- `MemWkpChartGen` is closed under scalar multiplication. -/
theorem MemWkpChartGen_const_smul
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (ρ : SmoothPartitionOfUnity M I M Set.univ)
    (c : ℝ) {u : M → ℝ}
    (hu : MemWkpChartGen (I := I) (M := M) g k p ρ u) :
    MemWkpChartGen (I := I) (M := M) g k p ρ (fun x => c * u x) := by
  intro α
  rw [chartPushed_const_smul_gen]
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.const_smul
    (d := Module.finrank ℝ E) hp
    (chartTargetEuclid_isOpen (I := I) (M := M) α)
    (hu α) c

/-- `MemWkpChartGen` is closed under negation. -/
theorem MemWkpChartGen_neg
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (ρ : SmoothPartitionOfUnity M I M Set.univ)
    {u : M → ℝ}
    (hu : MemWkpChartGen (I := I) (M := M) g k p ρ u) :
    MemWkpChartGen (I := I) (M := M) g k p ρ (fun x => -u x) := by
  have h := MemWkpChartGen_const_smul (I := I) (M := M) g hp ρ (-1) hu
  have hEq : (fun x : M => (-1 : ℝ) * u x) = (fun x : M => -u x) := by
    funext x; ring
  rw [hEq] at h
  exact h

/-- `MemWkpChartGen` is closed under subtraction. -/
theorem MemWkpChartGen_sub
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (ρ : SmoothPartitionOfUnity M I M Set.univ)
    {u v : M → ℝ}
    (hu : MemWkpChartGen (I := I) (M := M) g k p ρ u)
    (hv : MemWkpChartGen (I := I) (M := M) g k p ρ v) :
    MemWkpChartGen (I := I) (M := M) g k p ρ (fun x => u x - v x) := by
  have hneg := MemWkpChartGen_neg (I := I) (M := M) g hp ρ hv
  have h := MemWkpChartGen_add (I := I) (M := M) g hp ρ hu hneg
  have hEq : (fun x : M => u x + -v x) = (fun x : M => u x - v x) := by
    funext x; ring
  rw [hEq] at h
  exact h

/-- The triangle inequality for the general chart-based norm. -/
theorem wkpNormChartGen_add_le
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (ρ : SmoothPartitionOfUnity M I M Set.univ)
    {u v : M → ℝ}
    (hu : MemWkpChartGen (I := I) (M := M) g k p ρ u)
    (hv : MemWkpChartGen (I := I) (M := M) g k p ρ v) :
    wkpNormChartGen (I := I) (M := M) g k p ρ (fun x => u x + v x) ≤
      wkpNormChartGen (I := I) (M := M) g k p ρ u +
        wkpNormChartGen (I := I) (M := M) g k p ρ v := by
  unfold wkpNormChartGen
  rw [← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum ?_
  intro α
  rw [chartPushed_add_gen]
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_add_le
    (d := Module.finrank ℝ E) hp
    (chartTargetEuclid_isOpen (I := I) (M := M) α)
    (hu α) (hv α)

/-- The scalar-multiplication identity for the general chart-based norm. -/
theorem wkpNormChartGen_const_smul
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (ρ : SmoothPartitionOfUnity M I M Set.univ)
    (c : ℝ) {u : M → ℝ}
    (hu : MemWkpChartGen (I := I) (M := M) g k p ρ u) :
    wkpNormChartGen (I := I) (M := M) g k p ρ (fun x => c * u x) =
      ‖c‖ₑ * wkpNormChartGen (I := I) (M := M) g k p ρ u := by
  unfold wkpNormChartGen
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr ?_
  intro α
  rw [chartPushed_const_smul_gen]
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_const_smul
    (d := Module.finrank ℝ E) hp
    (chartTargetEuclid_isOpen (I := I) (M := M) α)
    (hu α) c

/-- Membership in `W^{k+1,p}_chart` (general POU) implies membership in
`W^{k,p}_chart` (general POU). -/
theorem MemWkpChartGen.le_succ
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    {g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M}
    {k : ℕ} {p : ℝ≥0∞}
    {ρ : SmoothPartitionOfUnity M I M Set.univ}
    {u : M → ℝ}
    (h : MemWkpChartGen (I := I) (M := M) g (k + 1) p ρ u) :
    MemWkpChartGen (I := I) (M := M) g k p ρ u := by
  intro α
  exact (h α).le_succ

/-- Membership in `W^{k',p}_chart` (general POU) implies membership in
`W^{k,p}_chart` (general POU) whenever `k ≤ k'`. -/
theorem MemWkpChartGen.le_of_le
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    {g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M}
    {k k' : ℕ} {p : ℝ≥0∞}
    {ρ : SmoothPartitionOfUnity M I M Set.univ}
    {u : M → ℝ}
    (hk : k ≤ k') (h : MemWkpChartGen (I := I) (M := M) g k' p ρ u) :
    MemWkpChartGen (I := I) (M := M) g k p ρ u := by
  intro α
  exact (h α).le_of_le hk

/-- On compact `M`, the general chart-based norm is finite for any function
in `MemWkpChartGen`. -/
theorem wkpNormChartGen_lt_top_of_memWkpChartGen
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (ρ : SmoothPartitionOfUnity M I M Set.univ)
    {u : M → ℝ} (hu : MemWkpChartGen (I := I) (M := M) g k p ρ u) :
    wkpNormChartGen (I := I) (M := M) g k p ρ u < ⊤ := by
  classical
  unfold wkpNormChartGen
  set f : M → ℝ≥0∞ := fun α =>
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
      (d := Module.finrank ℝ E) k p
      (chartPushed (I := I) (M := M) ρ α u)
      (chartTargetEuclid (I := I) (M := M) α) with hf_def
  have hPOU_locFin : LocallyFinite
      (fun α : M => Function.support (ρ α : M → ℝ)) :=
    ρ.locallyFinite
  have hSupport_finite : {α : M | (Function.support (ρ α : M → ℝ)).Nonempty}.Finite :=
    hPOU_locFin.finite_nonempty_of_compact
  have hf_zero_off : ∀ α : M, (Function.support (ρ α : M → ℝ)) = ∅ →
        f α = 0 := by
    intro α hα
    have hρ_empty : ∀ x : M, (ρ α : M → ℝ) x = 0 := by
      intro x
      have : x ∉ Function.support (ρ α : M → ℝ) := by
        rw [hα]
        exact Set.notMem_empty x
      simpa [Function.mem_support] using this
    have hChartPushed_zero : chartPushed (I := I) (M := M) ρ α u =
        (fun _ => (0 : ℝ)) := by
      funext y
      unfold chartPushed
      rw [hρ_empty]
      ring
    change DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
      (d := Module.finrank ℝ E) k p
      (chartPushed (I := I) (M := M) ρ α u)
      (chartTargetEuclid (I := I) (M := M) α) = 0
    rw [hChartPushed_zero]
    exact DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_zero_fun_zero
      (d := Module.finrank ℝ E) hp
      (chartTargetEuclid_isOpen (I := I) (M := M) α)
  set S : Set M := {α : M | (Function.support (ρ α : M → ℝ)).Nonempty}
      with hS_def
  have hS_finite : S.Finite := hSupport_finite
  have htsum_eq : ∑' α : M, f α = ∑ α ∈ hS_finite.toFinset, f α := by
    rw [tsum_eq_sum]
    intro α hα
    have hαS : α ∉ S := by
      intro hαS
      apply hα
      exact (Set.Finite.mem_toFinset _).mpr hαS
    have hempty : (Function.support (ρ α : M → ℝ)) = ∅ := by
      have h_not_nonempty : ¬ (Function.support (ρ α : M → ℝ)).Nonempty := by
        intro hne
        exact hαS hne
      exact Set.not_nonempty_iff_eq_empty.mp h_not_nonempty
    exact hf_zero_off α hempty
  rw [htsum_eq]
  apply ENNReal.sum_lt_top.mpr
  intro α _
  rw [hf_def]
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_lt_top_of_memWkp
    (d := Module.finrank ℝ E) (hu α)

/-- The set of POU members with non-empty support is finite on a compact
manifold. -/
theorem support_set_finite_of_compactSpace
    [CompactSpace M]
    (ρ : SmoothPartitionOfUnity M I M Set.univ) :
    {α : M | (Function.support (ρ α : M → ℝ)).Nonempty}.Finite :=
  ρ.locallyFinite.finite_nonempty_of_compact

/-- The set of POU members whose `tsupport` contains a given point is finite. -/
theorem fintsupport_finite
    (ρ : SmoothPartitionOfUnity M I M Set.univ) (x₀ : M) :
    {α : M | x₀ ∈ tsupport (ρ α : M → ℝ)}.Finite :=
  ρ.finite_tsupport x₀

omit [IsManifold I ∞ M] in
/-- The product of two POU members has support contained in the intersection of
their respective supports. -/
theorem support_pou_mul_subset
    (ρ ρ' : SmoothPartitionOfUnity M I M Set.univ) (α β : M) :
    Function.support (fun x : M => (ρ α : M → ℝ) x * (ρ' β : M → ℝ) x) ⊆
      Function.support (ρ α : M → ℝ) ∩ Function.support (ρ' β : M → ℝ) := by
  intro x hx
  simp only [Function.mem_support] at hx
  refine ⟨?_, ?_⟩ <;> simp only [Function.mem_support] <;> intro h <;>
    apply hx <;> rw [h] <;> ring

omit [IsManifold I ∞ M] in
/-- The product of two POU members has `tsupport` contained in the intersection
of their respective `tsupport`s. -/
theorem tsupport_pou_mul_subset
    (ρ ρ' : SmoothPartitionOfUnity M I M Set.univ) (α β : M) :
    tsupport (fun x : M => (ρ α : M → ℝ) x * (ρ' β : M → ℝ) x) ⊆
      tsupport (ρ α : M → ℝ) ∩ tsupport (ρ' β : M → ℝ) := by
  refine subset_inter ?_ ?_
  · refine closure_mono ?_
    intro x hx
    simp only [Function.mem_support] at hx
    simp only [Function.mem_support]
    intro h; exact hx (by rw [h]; ring)
  · refine closure_mono ?_
    intro x hx
    simp only [Function.mem_support] at hx
    simp only [Function.mem_support]
    intro h; exact hx (by rw [h]; ring)

/-- If `ρ` is subordinate to the canonical chart family, the `tsupport` of each
POU member lies inside the corresponding chart source. -/
theorem tsupport_subset_chartAt_source
    (ρ : SmoothPartitionOfUnity M I M Set.univ)
    (hρ : ρ.IsSubordinate (fun α : M => (chartAt H α).source))
    (α : M) :
    tsupport (ρ α : M → ℝ) ⊆ (chartAt H α).source := hρ α

/-- If `ρ` is subordinate to the canonical chart family, the support of each POU
member lies inside the corresponding chart source. -/
theorem support_subset_chartAt_source
    (ρ : SmoothPartitionOfUnity M I M Set.univ)
    (hρ : ρ.IsSubordinate (fun α : M => (chartAt H α).source))
    (α : M) :
    Function.support (ρ α : M → ℝ) ⊆ (chartAt H α).source :=
  (subset_tsupport _).trans (tsupport_subset_chartAt_source ρ hρ α)

/-- On a compact manifold, every POU member is bounded uniformly in `α`. The
existing `SmoothPartitionOfUnity.le_one` already gives a pointwise bound by `1`;
this lemma is a convenient packaging. -/
theorem chartPushed_pointwise_bound
    (ρ : SmoothPartitionOfUnity M I M Set.univ) (α : M) (u : M → ℝ)
    (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    |chartPushed (I := I) (M := M) ρ α u y| ≤
      |u ((extChartAt I α).symm (toEuclidean.symm y))| := by
  unfold chartPushed
  rw [abs_mul]
  have hbound : |(ρ α : C^∞⟮I, M; ℝ⟯) ((extChartAt I α).symm (toEuclidean.symm y))| ≤ 1 := by
    rw [abs_of_nonneg (ρ.nonneg α _)]
    exact ρ.le_one α _
  have hu_nonneg : 0 ≤ |u ((extChartAt I α).symm (toEuclidean.symm y))| := abs_nonneg _
  calc
    |(ρ α : C^∞⟮I, M; ℝ⟯) ((extChartAt I α).symm (toEuclidean.symm y))| *
        |u ((extChartAt I α).symm (toEuclidean.symm y))|
      ≤ 1 * |u ((extChartAt I α).symm (toEuclidean.symm y))| :=
        mul_le_mul_of_nonneg_right hbound hu_nonneg
    _ = |u ((extChartAt I α).symm (toEuclidean.symm y))| := one_mul _

/-- The finite-support form of the general chart-based Sobolev norm on compact
`M`: a finite sum over the (finite) set of POU members with non-empty support. -/
def wkpNormChartFin
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (_g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (k : ℕ) (p : ℝ≥0∞)
    (ρ : SmoothPartitionOfUnity M I M Set.univ)
    (u : M → ℝ) : ℝ≥0∞ :=
  ∑ α ∈ (support_set_finite_of_compactSpace (I := I) (M := M) ρ).toFinset,
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
      (d := Module.finrank ℝ E)
      k p
      (chartPushed (I := I) (M := M) ρ α u)
      (chartTargetEuclid (I := I) (M := M) α)

/-- On compact `M`, the general chart-based norm equals the finite-form norm. -/
theorem wkpNormChartGen_eq_wkpNormChartFin
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (ρ : SmoothPartitionOfUnity M I M Set.univ)
    (u : M → ℝ) :
    wkpNormChartGen (I := I) (M := M) g k p ρ u =
      wkpNormChartFin (I := I) (M := M) g k p ρ u := by
  classical
  let f : M → ℝ≥0∞ := fun α =>
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
      (d := Module.finrank ℝ E) k p
      (chartPushed (I := I) (M := M) ρ α u)
      (chartTargetEuclid (I := I) (M := M) α)
  have hLHS : wkpNormChartGen (I := I) (M := M) g k p ρ u = ∑' α : M, f α := rfl
  have hRHS : wkpNormChartFin (I := I) (M := M) g k p ρ u =
      ∑ α ∈ (support_set_finite_of_compactSpace (I := I) (M := M) ρ).toFinset,
        f α := rfl
  rw [hLHS, hRHS]
  have hf_zero_off : ∀ α : M, (Function.support (ρ α : M → ℝ)) = ∅ →
        f α = 0 := by
    intro α hα
    have hρ_empty : ∀ x : M, (ρ α : M → ℝ) x = 0 := by
      intro x
      have : x ∉ Function.support (ρ α : M → ℝ) := by
        rw [hα]
        exact Set.notMem_empty x
      simpa [Function.mem_support] using this
    have hChartPushed_zero : chartPushed (I := I) (M := M) ρ α u =
        (fun _ => (0 : ℝ)) := by
      funext y
      unfold chartPushed
      rw [hρ_empty]
      ring
    change DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
      (d := Module.finrank ℝ E) k p
      (chartPushed (I := I) (M := M) ρ α u)
      (chartTargetEuclid (I := I) (M := M) α) = 0
    rw [hChartPushed_zero]
    exact DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_zero_fun_zero
      (d := Module.finrank ℝ E) hp
      (chartTargetEuclid_isOpen (I := I) (M := M) α)
  rw [tsum_eq_sum]
  intro α hα
  have hαS : α ∉ {α : M | (Function.support (ρ α : M → ℝ)).Nonempty} := by
    intro hαS
    apply hα
    exact (Set.Finite.mem_toFinset _).mpr hαS
  have hempty : (Function.support (ρ α : M → ℝ)) = ∅ := by
    have h_not_nonempty : ¬ (Function.support (ρ α : M → ℝ)).Nonempty := by
      intro hne
      exact hαS hne
    exact Set.not_nonempty_iff_eq_empty.mp h_not_nonempty
  exact hf_zero_off α hempty

/-- On compact `M`, the cardinality of the set of POU members with non-empty
support is determined by a `Finset` extracted from local finiteness. -/
def chartTransitionFinset
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (ρ : SmoothPartitionOfUnity M I M Set.univ) : Finset M :=
  (support_set_finite_of_compactSpace (I := I) (M := M) ρ).toFinset

/-- The chart-transition Finset contains exactly those POU indices with non-empty
support. -/
theorem mem_chartTransitionFinset_iff
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (ρ : SmoothPartitionOfUnity M I M Set.univ) (α : M) :
    α ∈ chartTransitionFinset (I := I) (M := M) ρ ↔
      (Function.support (ρ α : M → ℝ)).Nonempty := by
  unfold chartTransitionFinset
  rw [Set.Finite.mem_toFinset]
  rfl

/-- An auxiliary handle: smoothness of the chart-transition derivative on the
open overlap of two canonical chart sources. -/
theorem chartAt_transition_hasFDerivWithinAt_overlap
    [I.Boundaryless] (α β : M) :
    ∀ y ∈ (extChartAt I α) ''
      ((chartAt H α).source ∩ (chartAt H β).source),
        HasFDerivWithinAt (extChartAt I β ∘ (extChartAt I α).symm)
          (tangentCoordChange I α β ((extChartAt I α).symm y))
          ((extChartAt I α) ''
            ((chartAt H α).source ∩ (chartAt H β).source)) y :=
  DifferentialGeometry.Integral.Measure.extChartAt_transition_hasFDerivWithinAt_on_overlap_image
    (I := I) α β Set.inter_subset_left Set.inter_subset_right

end Chart
end Sobolev
end Analysis
end DifferentialGeometry
