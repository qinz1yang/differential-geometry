import DifferentialGeometry.Analysis.Sobolev.Tensor.FineTensorRepack

/-!
# Quantitative Sobolev reassembly of one fine tensor block

The middle cutoff makes an arbitrary full-Euclidean Sobolev component safe to
pull back to the manifold.  This file combines the cutoff multiplier, the
outer-cutoff transition estimate, and the exact chart-component formula into
one bounded reassembly theorem.  It is the local analytic input for the finite
atlas retraction in the fixed-background parametrix.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

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

local notation "EuclN" =>
  EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-- Reassemble one fine Euclidean component block after applying its middle
cutoff. -/
noncomputable def fineBlock
    (rFine : M → ℝ) (hr : ∀ α, 0 < rFine α)
    (r s : ℕ) (z : CanonFineFlat (I := I) (M := M) rFine hr)
    (u : TensorCompIdx (E := E) r s → EuclN → ℝ) :
    RSTensorSection I M r s :=
  chartRepack (I := I) (M := M) r s
    (canonFlatBase (I := I) (M := M) rFine hr z)
    (fun Q => canonCutMul (I := I) (M := M) rFine hr z (u Q))

private theorem memWkp_sum
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) {U : Set EuclN} (hU : IsOpen U)
    {A : Type*} (t : Finset A) (f : A → EuclN → ℝ)
    (hf : ∀ a ∈ t, MemWkp (d := Module.finrank ℝ E) k p (f a) U) :
    MemWkp (d := Module.finrank ℝ E) k p
      (fun y => ∑ a ∈ t, f a y) U := by
  classical
  induction t using Finset.induction with
  | empty =>
      simpa using MemWkp_zero_fun (d := Module.finrank ℝ E) hp hU
  | @insert a t ha ih =>
      have hsplit : (fun y => ∑ b ∈ insert a t, f b y) =
          (fun y => f a y + ∑ b ∈ t, f b y) := by
        funext y
        rw [Finset.sum_insert ha]
      rw [hsplit]
      exact MemWkp.add (d := Module.finrank ℝ E) hp hU
        (hf a (Finset.mem_insert_self a t))
        (ih (fun b hb => hf b (Finset.mem_insert_of_mem hb)))

/-- Every target component of one middle-cutoff fine block is in `W^{k,p}`.
The input components are full-Euclidean Sobolev representatives. -/
theorem fineBlock_comp_mem
    (rFine : M → ℝ) (hr : ∀ α, 0 < rFine α)
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    (z : CanonFineFlat (I := I) (M := M) rFine hr)
    (u : TensorCompIdx (E := E) r s → EuclN → ℝ)
    (hu : ∀ Q, MemWkp (d := Module.finrank ℝ E) k p (u Q) Set.univ)
    (α : M) (P : TensorCompIdx (E := E) r s) :
    MemWkp (d := Module.finrank ℝ E) k p
      (secChartComp (I := I) (M := M) r s
        (fineBlock (I := I) (M := M) rFine hr r s z u) α P.1 P.2)
      (Chart.chartTargetEuclid (I := I) (M := M) α) := by
  classical
  let v : TensorCompIdx (E := E) r s → EuclN → ℝ :=
    fun Q => canonCutMul (I := I) (M := M) rFine hr z (u Q)
  have hv : ∀ Q, MemWkp (d := Module.finrank ℝ E) k p (v Q) Set.univ := by
    intro Q
    exact ((canonCut_joint (I := I) (M := M) rFine hr z k hp hp_top).choose_spec.2
      (hu Q)).1
  have hv_src : ∀ Q, MemWkp (d := Module.finrank ℝ E) k p (v Q)
      (Chart.chartTargetEuclid (I := I) (M := M)
        (canonFlatBase (I := I) (M := M) rFine hr z)) := by
    intro Q
    exact MemWkp.mono_set (d := Module.finrank ℝ E) hp isOpen_univ
      (Chart.chartTargetEuclid_isOpen (I := I) (M := M)
        (canonFlatBase (I := I) (M := M) rFine hr z))
      (Set.subset_univ _) (hv Q)
  have hterm : ∀ Q, MemWkp (d := Module.finrank ℝ E) k p
      (fineSecTerm (I := I) (M := M) rFine hr r s z α P Q (v Q))
      (Chart.chartTargetEuclid (I := I) (M := M) α) := by
    intro Q
    exact ((fineTerm_joint (I := I) (M := M) rFine hr g r s k hp hp_top
      z α P Q).choose_spec.2 (hv_src Q)
        (canonCutMul_supp (I := I) (M := M) rFine hr z (u Q))).1
  have hsum : MemWkp (d := Module.finrank ℝ E) k p
      (fun y => ∑ Q : TensorCompIdx (E := E) r s,
        fineSecTerm (I := I) (M := M) rFine hr r s z α P Q (v Q) y)
      (Chart.chartTargetEuclid (I := I) (M := M) α) := by
    simpa only [Finset.sum_univ] using
      memWkp_sum (E := E) hp
        (Chart.chartTargetEuclid_isOpen (I := I) (M := M) α)
        Finset.univ
        (fun Q => fineSecTerm (I := I) (M := M)
          rFine hr r s z α P Q (v Q))
        (fun Q _ => hterm Q)
  have heq := finePullEq (I := I) (M := M) rFine hr r s z v
    (fun Q => canonCutMul_supp (I := I) (M := M) rFine hr z (u Q)) α P
  exact (MemWkp_congr_ae (d := Module.finrank ℝ E) hp
    (Chart.chartTargetEuclid_isOpen (I := I) (M := M) α) heq).mpr hsum

/-- One middle-cutoff fine block is a genuine global tensor `W^{k,p}`
section. -/
theorem fineBlock_mem
    (rFine : M → ℝ) (hr : ∀ α, 0 < rFine α)
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    (z : CanonFineFlat (I := I) (M := M) rFine hr)
    (u : TensorCompIdx (E := E) r s → EuclN → ℝ)
    (hu : ∀ Q, MemWkp (d := Module.finrank ℝ E) k p (u Q) Set.univ) :
    MemWkpTensor (I := I) (M := M) g k p
      (fineBlock (I := I) (M := M) rFine hr r s z u) := by
  intro α Idx Jdx
  exact fineBlock_comp_mem (I := I) (M := M) rFine hr g r s k hp hp_top
    z u hu α ⟨Idx, Jdx⟩

/-- Quantitative componentwise bound for one middle-cutoff fine block.  The
finite positive weights depend only on the fixed charts, cutoffs, tensor
indices, Sobolev order, and exponent. -/
theorem fineBlock_bound
    (rFine : M → ℝ) (hr : ∀ α, 0 < rFine α)
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    (z : CanonFineFlat (I := I) (M := M) rFine hr)
    (α : M) (P : TensorCompIdx (E := E) r s) :
    ∃ K : TensorCompIdx (E := E) r s → ℝ,
      (∀ Q, 0 < K Q) ∧
      ∀ (u : TensorCompIdx (E := E) r s → EuclN → ℝ),
        (∀ Q, MemWkp (d := Module.finrank ℝ E) k p (u Q) Set.univ) →
        wkpNorm (d := Module.finrank ℝ E) k p
            (secChartComp (I := I) (M := M) r s
              (fineBlock (I := I) (M := M) rFine hr r s z u) α P.1 P.2)
            (Chart.chartTargetEuclid (I := I) (M := M) α) ≤
          ∑ Q : TensorCompIdx (E := E) r s,
            ENNReal.ofReal (K Q) *
              wkpNorm (d := Module.finrank ℝ E) k p (u Q) Set.univ := by
  classical
  obtain ⟨Kc, hKc, hcut⟩ :=
    canonCut_joint (I := I) (M := M) rFine hr z k hp hp_top
  choose Kt hKt hterm using fun Q : TensorCompIdx (E := E) r s =>
    fineTerm_joint (I := I) (M := M) rFine hr g r s k hp hp_top z α P Q
  refine ⟨fun Q => Kt Q * Kc, fun Q => mul_pos (hKt Q) hKc, ?_⟩
  intro u hu
  let v : TensorCompIdx (E := E) r s → EuclN → ℝ :=
    fun Q => canonCutMul (I := I) (M := M) rFine hr z (u Q)
  have hv : ∀ Q, MemWkp (d := Module.finrank ℝ E) k p (v Q) Set.univ := by
    intro Q
    exact (hcut (hu Q)).1
  have hv_src : ∀ Q, MemWkp (d := Module.finrank ℝ E) k p (v Q)
      (Chart.chartTargetEuclid (I := I) (M := M)
        (canonFlatBase (I := I) (M := M) rFine hr z)) := by
    intro Q
    exact MemWkp.mono_set (d := Module.finrank ℝ E) hp isOpen_univ
      (Chart.chartTargetEuclid_isOpen (I := I) (M := M)
        (canonFlatBase (I := I) (M := M) rFine hr z))
      (Set.subset_univ _) (hv Q)
  have hterm_mem : ∀ Q, MemWkp (d := Module.finrank ℝ E) k p
      (fineSecTerm (I := I) (M := M) rFine hr r s z α P Q (v Q))
      (Chart.chartTargetEuclid (I := I) (M := M) α) := by
    intro Q
    exact ((hterm Q) (hv_src Q)
      (canonCutMul_supp (I := I) (M := M) rFine hr z (u Q))).1
  have hsum := wkpNorm_sum_le (d := Module.finrank ℝ E) hp
    (Chart.chartTargetEuclid_isOpen (I := I) (M := M) α)
    Finset.univ
    (fun Q => fineSecTerm (I := I) (M := M)
      rFine hr r s z α P Q (v Q))
    (fun Q _ => hterm_mem Q)
  have hsum' :
      wkpNorm (d := Module.finrank ℝ E) k p
          (fun y => ∑ Q : TensorCompIdx (E := E) r s,
            fineSecTerm (I := I) (M := M)
              rFine hr r s z α P Q (v Q) y)
          (Chart.chartTargetEuclid (I := I) (M := M) α) ≤
        ∑ Q : TensorCompIdx (E := E) r s,
          wkpNorm (d := Module.finrank ℝ E) k p
            (fineSecTerm (I := I) (M := M)
              rFine hr r s z α P Q (v Q))
            (Chart.chartTargetEuclid (I := I) (M := M) α) := by
    simpa only [Finset.sum_univ] using hsum
  have heq := finePullEq (I := I) (M := M) rFine hr r s z v
    (fun Q => canonCutMul_supp (I := I) (M := M) rFine hr z (u Q)) α P
  rw [wkpNorm_congr_ae (d := Module.finrank ℝ E) hp
    (Chart.chartTargetEuclid_isOpen (I := I) (M := M) α) heq]
  refine hsum'.trans ?_
  refine Finset.sum_le_sum ?_
  intro Q _
  have hQ := (hterm Q) (hv_src Q)
    (canonCutMul_supp (I := I) (M := M) rFine hr z (u Q))
  have hmono := wkpNorm_mono_set (d := Module.finrank ℝ E) hp isOpen_univ
    (Chart.chartTargetEuclid_isOpen (I := I) (M := M)
      (canonFlatBase (I := I) (M := M) rFine hr z))
    (Set.subset_univ _) (hv Q)
  calc
    wkpNorm (d := Module.finrank ℝ E) k p
        (fineSecTerm (I := I) (M := M) rFine hr r s z α P Q (v Q))
        (Chart.chartTargetEuclid (I := I) (M := M) α) ≤
      ENNReal.ofReal (Kt Q) *
        wkpNorm (d := Module.finrank ℝ E) k p (v Q)
          (Chart.chartTargetEuclid (I := I) (M := M)
            (canonFlatBase (I := I) (M := M) rFine hr z)) := hQ.2
    _ ≤ ENNReal.ofReal (Kt Q) *
        wkpNorm (d := Module.finrank ℝ E) k p (v Q) Set.univ :=
      mul_le_mul_left' hmono _
    _ ≤ ENNReal.ofReal (Kt Q) *
        (ENNReal.ofReal Kc *
          wkpNorm (d := Module.finrank ℝ E) k p (u Q) Set.univ) :=
      mul_le_mul_left' (hcut (hu Q)).2 _
    _ = ENNReal.ofReal (Kt Q * Kc) *
        wkpNorm (d := Module.finrank ℝ E) k p (u Q) Set.univ := by
      rw [ENNReal.ofReal_mul (hKt Q).le]
      simp only [mul_assoc]

end Tensor
end Sobolev
end Analysis
end DifferentialGeometry
