import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.CovariantDerivativePointwiseBounds

noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set Filter Topology Bundle Manifold DifferentialGeometry.Tensor0SBundle ContinuousLinearMap
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.Integral.Connection

open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Spectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

def HasCapWin (g₀ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    {r c : ℕ} (X : SmoothCcTensor g₀ r c) (K : ℕ → ℝ) : Prop :=
  ∀ (i : ℕ) (x : M),
    riemannianFiberNormSq (I := I) (M := M) g₀ r (c + i) x
        ((iteratedCovGrad (I := I) g₀ r c i X).toSection x) ≤
      K i * Combinatorics.antidiagonalTupleGridWindow
        (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ (iteratedCovGrad (I := I) g₀ 0 2 1 P) x) (i + 1)

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private lemma oneLeCapW (g₀ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    (x : M) (i : ℕ) :
    (1 : ℝ) ≤ Combinatorics.antidiagonalTupleGridWindow
      (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ (iteratedCovGrad (I := I) g₀ 0 2 1 P) x) (i + 1) :=
  Combinatorics.one_le_antidiagonalTupleGridWindow _
    (covariantJetFiberNormSqGrid_nonneg (I := I) (M := M) g₀ _ x) (by omega)

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private lemma nnCapW (g₀ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    (x : M) (i : ℕ) :
    (0 : ℝ) ≤ Combinatorics.antidiagonalTupleGridWindow
      (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ (iteratedCovGrad (I := I) g₀ 0 2 1 P) x) (i + 1) :=
  le_trans zero_le_one (oneLeCapW (I := I) (M := M) g₀ P x i)

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem capOfArm (g₀ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    {Λ : ℝ} (hΛ1 : 1 ≤ Λ)
    (hP0 : ∀ x : M, covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x 0 ≤ Λ)
    (hP1 : ∀ x : M, covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x 1 ≤ Λ)
    {r c : ℕ} (X : SmoothCcTensor g₀ r c) {K : ℕ → ℝ} (hK : ∀ i, 0 ≤ K i)
    (hX : ∀ (i : ℕ) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ r (c + i) x
          ((iteratedCovGrad (I := I) g₀ r c i X).toSection x) ≤
        K i * Combinatorics.antidiagonalTupleGridWindow
          (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x) (i + 2)) :
    HasCapWin (I := I) (M := M) g₀ P X (fun i => K i * antidiagonalTupleGridWindowShiftConstant Λ (i + 1)) := by
  intro i x
  simpa using antidiagonalTupleGridWindow_covariantDerivative_shift (I := I) (M := M) g₀ P hΛ1 hP0 hP1 X hK 0
    (fun j y => by simpa using hX j y) i x

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem capOfBnd (g₀ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    {r c : ℕ} (X : SmoothCcTensor g₀ r c) {S : ℕ → ℝ} (hS : ∀ i, 0 ≤ S i)
    (hX : ∀ (i : ℕ) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ r (c + i) x
        ((iteratedCovGrad (I := I) g₀ r c i X).toSection x) ≤ S i) :
    HasCapWin (I := I) (M := M) g₀ P X S := by
  intro i x
  exact le_trans (hX i x)
    (le_mul_of_one_le_right (hS i) (oneLeCapW (I := I) (M := M) g₀ P x i))

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private lemma capBaseLe (g₀ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    (x : M) {i j : ℕ} (hj : 1 ≤ j) (hji : j ≤ i) :
    covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x (j + 1) ≤
      Combinatorics.antidiagonalTupleGridWindow
        (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ (iteratedCovGrad (I := I) g₀ 0 2 1 P) x) (i + 1) := by
  classical
  set b : ℕ → ℝ := covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x with hb_def
  have hb : ∀ k, 0 ≤ b k := covariantJetFiberNormSqGrid_nonneg (I := I) (M := M) g₀ P x
  have hb' : ∀ k, 0 ≤ (fun k => b (k + 1)) k := fun k => hb _
  have hsingle := Combinatorics.single_factor_mul_antidiagonalTupleGrid_le
    (fun k => b (k + 1)) hb' 0 j hj
  rw [Combinatorics.antidiagonalTupleGrid_zero, mul_one, zero_add] at hsingle
  refine le_trans hsingle ?_
  rw [← covariantDerivative_grid (I := I) (M := M) g₀ P x]
  exact Combinatorics.antidiagonalTupleGrid_le_window _ hb' (by omega)

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem capOfP (g₀ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    {Λ : ℝ} (hΛ1 : 1 ≤ Λ)
    (hP0 : ∀ x : M, covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x 0 ≤ Λ)
    (hP1 : ∀ x : M, covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x 1 ≤ Λ) :
    HasCapWin (I := I) (M := M) g₀ P P (fun _ => Λ) := by
  classical
  intro i x
  have hone := oneLeCapW (I := I) (M := M) g₀ P x i
  have hnn := nnCapW (I := I) (M := M) g₀ P x i
  have hΛ0 : (0 : ℝ) ≤ Λ := le_trans zero_le_one hΛ1
  have hgoal : covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x i ≤
      Λ * Combinatorics.antidiagonalTupleGridWindow
        (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ (iteratedCovGrad (I := I) g₀ 0 2 1 P) x) (i + 1) := by
    match i with
    | 0 => exact le_trans (hP0 x) (le_mul_of_one_le_right hΛ0 hone)
    | 1 => exact le_trans (hP1 x) (le_mul_of_one_le_right hΛ0 hone)
    | (k + 2) =>
        have h := capBaseLe (I := I) (M := M) g₀ P x (i := k + 2) (j := k + 1)
          (by omega) (by omega)
        nlinarith [h, hnn]
  exact hgoal

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem capOfDP (g₀ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    {Λ : ℝ} (hΛ1 : 1 ≤ Λ)
    (hP1 : ∀ x : M, covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x 1 ≤ Λ) :
    HasCapWin (I := I) (M := M) g₀ P (covGrad (I := I) (M := M) g₀ 0 2 P) (fun _ => Λ) := by
  classical
  intro i x
  have hone := oneLeCapW (I := I) (M := M) g₀ P x i
  have hnn := nnCapW (I := I) (M := M) g₀ P x i
  have hΛ0 : (0 : ℝ) ≤ Λ := le_trans zero_le_one hΛ1
  rw [riemannianFiberNormSq_iteratedCovGrad_covGrad_comm_rs (I := I) (M := M) g₀ 0 2 i P x]
  have hgoal : covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x (i + 1) ≤
      Λ * Combinatorics.antidiagonalTupleGridWindow
        (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ (iteratedCovGrad (I := I) g₀ 0 2 1 P) x) (i + 1) := by
    match i with
    | 0 => exact le_trans (hP1 x) (le_mul_of_one_le_right hΛ0 hone)
    | (k + 1) =>
        have h := capBaseLe (I := I) (M := M) g₀ P x (i := k + 1) (j := k + 1)
          (by omega) (by omega)
        nlinarith [h, hnn]
  exact hgoal

theorem capApp (g₀ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    {p a b : ℕ} (Φ : SmoothCcTensor g₀ a b) (W : SmoothCcTensor g₀ p a)
    {KΦ KW : ℕ → ℝ} (hKΦ : ∀ i, 0 ≤ KΦ i) (hKW : ∀ l, 0 ≤ KW l)
    (hΦ : HasCapWin (I := I) (M := M) g₀ P Φ KΦ)
    (hW : HasCapWin (I := I) (M := M) g₀ P W KW) :
    HasCapWin (I := I) (M := M) g₀ P (ccOperatorFieldComp (I := I) (M := M) g₀ p a b Φ W)
      (operatorFieldCompositionGridConstant (E := E) 0 0 KΦ KW) := by
  intro n x
  simpa using operatorFieldComposition_antidiagonalTupleGridWindow_bound (I := I) (M := M) g₀ (u := 0) (v := 0) Φ W
    (iteratedCovGrad (I := I) g₀ 0 2 1 P) hKΦ hKW
    (fun i' y => by simpa using hΦ i' y) (fun l y => by simpa using hW l y) n x

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem capMono (g₀ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    {r c : ℕ} {X : SmoothCcTensor g₀ r c} {K K' : ℕ → ℝ}
    (hKK : ∀ i, K i ≤ K' i) (hX : HasCapWin (I := I) (M := M) g₀ P X K) :
    HasCapWin (I := I) (M := M) g₀ P X K' := by
  intro i x
  exact le_trans (hX i x)
    (mul_le_mul_of_nonneg_right (hKK i) (nnCapW (I := I) (M := M) g₀ P x i))

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem capCongr (g₀ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    {r c : ℕ} {X Y : SmoothCcTensor g₀ r c} {K : ℕ → ℝ} (hXY : Y = X)
    (hX : HasCapWin (I := I) (M := M) g₀ P X K) :
    HasCapWin (I := I) (M := M) g₀ P Y K := by
  rw [hXY]; exact hX

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem capAdd (g₀ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    {r c : ℕ} {X Y : SmoothCcTensor g₀ r c} {KX KY : ℕ → ℝ}
    (hX : HasCapWin (I := I) (M := M) g₀ P X KX)
    (hY : HasCapWin (I := I) (M := M) g₀ P Y KY) :
    HasCapWin (I := I) (M := M) g₀ P (X + Y) (fun i => 2 * KX i + 2 * KY i) := by
  intro i x
  have hsplit : riemannianFiberNormSq (I := I) (M := M) g₀ r (c + i) x
        ((iteratedCovGrad (I := I) g₀ r c i (X + Y)).toSection x) ≤
      2 * riemannianFiberNormSq (I := I) (M := M) g₀ r (c + i) x
          ((iteratedCovGrad (I := I) g₀ r c i X).toSection x) +
        2 * riemannianFiberNormSq (I := I) (M := M) g₀ r (c + i) x
          ((iteratedCovGrad (I := I) g₀ r c i Y).toSection x) := by
    rw [iteratedCovGrad_add (I := I) g₀ r c i X Y, SmoothCcTensor.toSection_add,
      ContMDiffSection.coe_add, Pi.add_apply]
    exact riemannianFiberNormSq_add_le (I := I) (M := M) g₀ r (c + i) x _ _
  refine hsplit.trans ?_
  have h1 := hX i x
  have h2 := hY i x
  nlinarith [h1, h2, nnCapW (I := I) (M := M) g₀ P x i]

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem capSmul (g₀ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    {r c : ℕ} {X : SmoothCcTensor g₀ r c} {K : ℕ → ℝ} (t : ℝ)
    (hX : HasCapWin (I := I) (M := M) g₀ P X K) :
    HasCapWin (I := I) (M := M) g₀ P (t • X) (fun i => t ^ 2 * K i) := by
  intro i x
  have heq : riemannianFiberNormSq (I := I) (M := M) g₀ r (c + i) x
        ((iteratedCovGrad (I := I) g₀ r c i (t • X)).toSection x) =
      t ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ r (c + i) x
        ((iteratedCovGrad (I := I) g₀ r c i X).toSection x) := by
    rw [DifferentialGeometry.Analysis.Sobolev.iteratedCovGrad_smul_real
      (I := I) (M := M) g₀ r c i t X,
      SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply,
      DifferentialGeometry.Analysis.Elliptic.riemannianFiberNormSq_smul (I := I) (M := M) g₀ r (c + i) x t _]
  rw [heq, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hX i x) (sq_nonneg t)

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem capNeg (g₀ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    {r c : ℕ} {X : SmoothCcTensor g₀ r c} {K : ℕ → ℝ}
    (hX : HasCapWin (I := I) (M := M) g₀ P X K) :
    HasCapWin (I := I) (M := M) g₀ P (-X) K := by
  have hneg : (-X) = (-1 : ℝ) • X := by rw [neg_smul, one_smul]
  rw [hneg]
  refine capMono (I := I) (M := M) g₀ P (fun i => ?_)
    (capSmul (I := I) (M := M) g₀ P (-1 : ℝ) hX)
  norm_num

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem capSub (g₀ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    {r c : ℕ} {X Y : SmoothCcTensor g₀ r c} {KX KY : ℕ → ℝ}
    (hX : HasCapWin (I := I) (M := M) g₀ P X KX)
    (hY : HasCapWin (I := I) (M := M) g₀ P Y KY) :
    HasCapWin (I := I) (M := M) g₀ P (X - Y) (fun i => 2 * KX i + 2 * KY i) := by
  have h := capAdd (I := I) (M := M) g₀ P hX (capNeg (I := I) (M := M) g₀ P hY)
  rwa [← sub_eq_add_neg] at h

omit [NeZero (Module.finrank ℝ E)] in
theorem capReindex (g₀ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    {r c : ℕ} {X : SmoothCcTensor g₀ r c} {K : ℕ → ℝ} (ρ : Equiv.Perm (Fin r))
    (hX : HasCapWin (I := I) (M := M) g₀ P X K) :
    HasCapWin (I := I) (M := M) g₀ P
      (reindexCoeffGen (I := I) (M := M) g₀ r c X ρ) K := by
  intro i x
  rw [riemannianFiberNormSq_iteratedCovGrad_reindexCoeffGen_eq (I := I) (M := M) g₀ r c X ρ i x]
  exact hX i x

theorem capDdc (g₀ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    {r c : ℕ} {X : SmoothCcTensor g₀ r c} {K : ℕ → ℝ} (σ : Equiv.Perm (Fin c))
    (hX : HasCapWin (I := I) (M := M) g₀ P X K) :
    HasCapWin (I := I) (M := M) g₀ P
      (rsDomDomCongrSection (I := I) (M := M) g₀ r c σ X) K := by
  intro i x
  rw [riemannianFiberNormSq_iteratedCovGrad_rs_eq_of_section_domDomCongr (I := I) (M := M) g₀ r c σ X
    (rsDomDomCongrSection (I := I) (M := M) g₀ r c σ X)
    (fun y d => by rw [rsDomDomCongrSection_toSection, toModel_rsDomDomCongr_apply]) i x]
  exact hX i x

omit [NeZero (Module.finrank ℝ E)] in
theorem capDdc0 (g₀ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    {c : ℕ} {X : SmoothCcTensor g₀ 0 c} {K : ℕ → ℝ} (σ : Equiv.Perm (Fin c))
    (hX : HasCapWin (I := I) (M := M) g₀ P X K) :
    HasCapWin (I := I) (M := M) g₀ P (domDomCongrSection (I := I) g₀ σ X) K := by
  intro i x
  rw [riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀ σ X i x]
  exact hX i x

theorem capSlotExt (g₀ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    {r c : ℕ} {X : SmoothCcTensor g₀ r c} {K : ℕ → ℝ}
    (hX : HasCapWin (I := I) (M := M) g₀ P X K) :
    HasCapWin (I := I) (M := M) g₀ P (slotExtend (I := I) (M := M) g₀ r c X)
      (fun i => (Module.finrank ℝ E : ℝ) * K i) := by
  intro i x
  have hfr : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
  refine le_trans (riemannianFiberNormSq_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ r c X i x) ?_
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (hX i x) hfr

theorem capIter (g₀ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    {r c : ℕ} {X : SmoothCcTensor g₀ r c} {K : ℕ → ℝ} (w : ℕ)
    (hX : HasCapWin (I := I) (M := M) g₀ P X K) :
    HasCapWin (I := I) (M := M) g₀ P (slotExtendIter (I := I) (M := M) g₀ r c w X)
      (fun i => (Module.finrank ℝ E : ℝ) ^ w * K i) := by
  induction w with
  | zero => simpa using hX
  | succ w ih =>
      have hrec : slotExtendIter (I := I) (M := M) g₀ r c (w + 1) X =
          slotExtend (I := I) (M := M) g₀ (r + w) (c + w)
            (slotExtendIter (I := I) (M := M) g₀ r c w X) := rfl
      have h := capSlotExt (I := I) (M := M) g₀ P ih
      rw [← hrec] at h
      refine capMono (I := I) (M := M) g₀ P (fun i => ?_) h
      simp only [pow_succ]
      ring_nf
      exact le_of_eq rfl

theorem capJet (g₀ : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ0 : 0 ≤ Λ) :
    ∃ Kint : ℕ → ℝ, (∀ k, 0 ≤ Kint k) ∧
      ∀ (P : SmoothCcTensor g₀ 0 2),
        (∀ x : M, covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x 1 ≤ Λ) →
        ∀ {r c : ℕ} (X : SmoothCcTensor g₀ r c) {K : ℕ → ℝ}, (∀ i, 0 ≤ K i) →
          HasCapWin (I := I) (M := M) g₀ P X K →
          ∀ n : ℕ,
            ‖iteratedCovGrad (I := I) g₀ r c n X‖ ^ 2 ≤
              K n * (∑ k ∈ Finset.range (n + 1), Kint k) *
                (1 + ∑ j ∈ Finset.range (n + 2),
                  ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  classical
  obtain ⟨Kint, hKint_nn, hint⟩ :=
    antidiagonalTupleGridWindow_bound_to_jet_bound (I := I) (M := M) g₀ (Λ₁ := Real.sqrt Λ) (Real.sqrt_nonneg Λ)
  refine ⟨Kint, hKint_nn, ?_⟩
  intro P hP1 r c X K hK hX n
  have hcap : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 1) x
      ((iteratedCovGrad (I := I) g₀ 0 2 1 P).toSection x) ≤ Real.sqrt Λ ^ 2 := by
    intro x
    rw [Real.sq_sqrt hΛ0]
    simpa using hP1 x
  exact hint P hcap r c n 1 X (K n) (hK n) (fun x => by simpa using hX n x)

end DifferentialGeometry.Integral.Connection

end
