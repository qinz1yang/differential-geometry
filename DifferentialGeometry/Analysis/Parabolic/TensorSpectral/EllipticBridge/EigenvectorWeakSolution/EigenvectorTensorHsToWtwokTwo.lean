import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorManifoldSobolevAggregate
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SobolevScale.Defs

/-!
# From a finitely-supported spectral Sobolev element to a smooth `W^{2k,2}` section

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, an order `k : ℕ` and
a real Sobolev exponent `σ`, this file constructs, from each element
`T : tensorHs g r s σ` whose eigenbasis coordinates have **finite support**, a
smooth, compactly-supported representative

  `tensorHsSmoothRepr T hT_fs : SmoothCcTensor g r s`,

namely the finite linear combination
`∑ i ∈ support, T.coeff i • eigenvectorSmooth g r s i`. The
representative is a true `W^{2k, 2}` element (`MemWtwokTwo g k`) and its
`L²`-image agrees, for `σ ≥ 0`, with the canonical inclusion
`tensorHsToL2 … hσ T`.

The headline aggregates the manifold-aggregated per-eigenvector Sobolev bound
`eigenvectorSmooth_wtwokTwoNorm_le_uniform` (with the uniform
constant `C`) into a *single* `W^{2k, 2}` bound for every finitely-supported
coordinate family, with the same uniform geometric constant `C`:

  `wtwokTwoNorm g k (tensorHsSmoothRepr T hT_fs) ≤
    ENNReal.ofReal C *
      ENNReal.ofReal (∑ i ∈ support, |T.coeff i| · (i.fst.val)⁻¹ ^ (2k + 1))`.

The right-hand side is, by Cauchy–Schwarz on the finite support, controllable
by the spectral Sobolev norm of `T` at any exponent `σ` sufficiently large to
make the dual eigenvalue tail summable; downstream consumers pick `σ`.

The eigenbasis used throughout is the intrinsic compact-operator eigenbasis
`tensorResolventEigenbasisVec (… intrinsic g r s)`, so no
chart-selection hypothesis is required.

## Main definitions

* `tensorHsSmoothRepr T hT_fs` — the smooth compactly-supported
  representative of a finitely-supported `Hˢ` element, as a finite linear
  combination of the smooth eigenvector representatives.

## Main results

* `tensorHsSmoothRepr_memWtwokTwo` — the smooth representative lies
  in `MemWtwokTwo g k` for every `k : ℕ`.
* `tensorHsSmoothRepr_toL2` — for `σ ≥ 0`, the `L²`-image of the
  smooth representative coincides with the canonical inclusion
  `tensorHsToL2 … hσ T`.
* `tensorHsSmoothRepr_wtwokTwoNorm_le_uniform` — the
  manifold-aggregated `W^{2k, 2}` bound: a single geometric constant `C ≥ 0`,
  uniform over *every* exponent `σ` and *every* finitely-supported `Hˢ`
  element, controls the Sobolev norm of the smooth representative by the
  explicit finite sum of `|coeff i| · (i.fst.val)⁻¹^(2k + 1)` over the support.

## Sign convention

We follow the geometer convention `Δ_∇ = -∇* ∇`, with spectrum `⊆ (-∞, 0]`. The
resolvent is `(1 - Δ_∇)⁻¹` (spectrum `⊆ (0, 1]`). The resolvent eigenvalue at
sigma-index `i` is `μ = i.fst.val ∈ (0, 1]` and `μ⁻¹ = 1 + λ_i ≥ 1`.
-/

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option linter.unusedSectionVars false

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Sobolev.Tensor
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

namespace TensorHsSmoothReprAux

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)

open scoped Classical in
/-- Reading the coordinate of a finite linear combination of the
`tensorHsBasisVec` family at index `j`: it is `T.coeff j` whenever `j` lies in
the chosen finite subset, else zero. -/
private lemma sum_basisVec_coeff_apply
    (σ : ℝ) (S : Finset (TensorEigenIdx (I := I) (M := M) g r s))
    (T : tensorHs (I := I) (M := M) g r s σ)
    (j : TensorEigenIdx (I := I) (M := M) g r s) :
    (∑ i ∈ S, T.coeff i •
        tensorHsBasisVec (I := I) (M := M)
          (g := g) (r := r) (s := s) σ i).coeff j =
      ∑ i ∈ S, (if j = i then T.coeff i else 0) := by
  classical
  induction S using Finset.induction with
  | empty => simp
  | insert i A hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih,
        tensorHs.add_coeff]
      simp only [tensorHs.smul_coeff, tensorHsBasisVec_coeff,
        mul_ite, mul_one, mul_zero]

end TensorHsSmoothReprAux

/-- A finitely-supported `Hˢ` element equals the *finite* sum, over its
support, of its spectral basis components. The `Hˢ`-norm convergence of the
spectral expansion (`tensorHs.hasSum_smul_basisVec`) collapses to this finite
identity when the coordinate family has finite support. -/
theorem tensorHs_eq_finset_sum_of_finite_support
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    {σ : ℝ} (T : tensorHs (I := I) (M := M) g r s σ)
    (hT_fs : (Function.support T.coeff).Finite) :
    T = ∑ i ∈ hT_fs.toFinset, T.coeff i •
      tensorHsBasisVec (I := I) (M := M)
        (g := g) (r := r) (s := s) σ i := by
  classical
  refine tensorHs.ext ?_
  funext j
  rw [TensorHsSmoothReprAux.sum_basisVec_coeff_apply
    (I := I) (M := M) g r s σ hT_fs.toFinset T j]
  by_cases hj_supp : j ∈ Function.support T.coeff
  · have hj_mem : j ∈ hT_fs.toFinset := hT_fs.mem_toFinset.mpr hj_supp
    have h_isolate :
        ∑ i ∈ hT_fs.toFinset, (if j = i then T.coeff i else 0) =
          (if j = j then T.coeff j else 0) := by
      refine Finset.sum_eq_single_of_mem j hj_mem ?_
      intro i _ hij
      simp [Ne.symm hij]
    rw [h_isolate]
    simp
  · have hzero : T.coeff j = 0 := by
      by_contra hne
      exact hj_supp (Function.mem_support.mpr hne)
    have h_rhs_zero :
        ∑ i ∈ hT_fs.toFinset,
            (if j = i then T.coeff i else (0 : ℝ)) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro i _hi
      by_cases h : j = i
      · subst h; simp [hzero]
      · simp [h]
    rw [hzero, h_rhs_zero]

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

namespace TensorHsSmoothReprAux

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)

/-- The finite linear combination `∑ i ∈ S, c i • eigenvectorSmooth g r s i`
of the smooth eigenvector representatives, viewed as a `SmoothCcTensor g r s`,
over a finite set `S` of eigen-indices with real coefficients `c`. -/
private def partialSum_unconditional
    (S : Finset (TensorEigenIdx (I := I) (M := M) g r s))
    (c : TensorEigenIdx (I := I) (M := M) g r s → ℝ) :
    SmoothCcTensor g r s :=
  ∑ i ∈ S, c i • eigenvectorSmooth (I := I) (M := M) g r s i

/-- The empty partial sum `partialSum_unconditional g r s ∅ c` is the zero
section of `SmoothCcTensor g r s`. -/
private lemma partialSum_empty_unconditional
    (c : TensorEigenIdx (I := I) (M := M) g r s → ℝ) :
    partialSum_unconditional (I := I) (M := M) g r s (∅ :
      Finset (TensorEigenIdx (I := I) (M := M) g r s)) c =
      (0 : SmoothCcTensor g r s) := by
  unfold partialSum_unconditional; simp

open scoped Classical in
/-- Inserting a fresh index `j ∉ S` adds the summand
`c j • eigenvectorSmooth g r s j` to the partial sum:
`partialSum_unconditional g r s (insert j S) c =
  c j • eigenvectorSmooth g r s j + partialSum_unconditional g r s S c`. -/
private lemma partialSum_insert_unconditional
    {S : Finset (TensorEigenIdx (I := I) (M := M) g r s)}
    {j : TensorEigenIdx (I := I) (M := M) g r s} (hj : j ∉ S)
    (c : TensorEigenIdx (I := I) (M := M) g r s → ℝ) :
    partialSum_unconditional (I := I) (M := M) g r s (insert j S) c =
      c j • eigenvectorSmooth (I := I) (M := M) g r s j +
        partialSum_unconditional (I := I) (M := M) g r s S c := by
  unfold partialSum_unconditional; rw [Finset.sum_insert hj]

/-- Every finite partial sum `partialSum_unconditional g r s S c` lies in
`MemWtwokTwo g k`, by induction on `S` using that each smooth eigenvector
representative is `W^{2k,2}` and that `MemWtwokTwo` is closed under scalar
multiplication and addition. -/
private lemma partialSum_memWtwokTwo_unconditional
    (k : ℕ)
    (S : Finset (TensorEigenIdx (I := I) (M := M) g r s))
    (c : TensorEigenIdx (I := I) (M := M) g r s → ℝ) :
    MemWtwokTwo (I := I) (M := M) g k
      (partialSum_unconditional (I := I) (M := M) g r s S c) := by
  classical
  induction S using Finset.induction with
  | empty =>
      rw [partialSum_empty_unconditional (I := I) (M := M) g r s c]
      exact MemWtwokTwo_zero_section (I := I) (M := M) g k
  | insert j A hj ih =>
      rw [partialSum_insert_unconditional (I := I) (M := M) g r s hj c]
      refine MemWtwokTwo_add (I := I) (M := M) g ?_ ih
      exact MemWtwokTwo_smul (I := I) (M := M) g (c j)
        (tensorEigenvector_memWtwokTwo (I := I) (M := M) g r s j k)

end TensorHsSmoothReprAux

/-- The smooth, compactly-supported representative of a finitely-supported
`Hˢ` element `T`: the finite linear combination
`∑ i ∈ support, T.coeff i • eigenvectorSmooth g r s i` over the (finite)
support of `T`'s eigenbasis coordinates. -/
noncomputable def tensorHsSmoothRepr
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    {σ : ℝ} (T : tensorHs (I := I) (M := M) g r s σ)
    (hT_fs : (Function.support T.coeff).Finite) :
    SmoothCcTensor g r s :=
  TensorHsSmoothReprAux.partialSum_unconditional (I := I) (M := M) g r s
    hT_fs.toFinset T.coeff

/-- Unfolds the smooth representative `tensorHsSmoothRepr T hT_fs` to its
defining finite sum `∑ i ∈ hT_fs.toFinset, T.coeff i • eigenvectorSmooth g r s i`
(definitional equality). -/
theorem tensorHsSmoothRepr_eq
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    {σ : ℝ} (T : tensorHs (I := I) (M := M) g r s σ)
    (hT_fs : (Function.support T.coeff).Finite) :
    tensorHsSmoothRepr (I := I) (M := M) T hT_fs =
      ∑ i ∈ hT_fs.toFinset,
        T.coeff i •
          eigenvectorSmooth (I := I) (M := M) g r s i := rfl

/-- The smooth representative `tensorHsSmoothRepr T hT_fs` lies in
`MemWtwokTwo g k` for every `k : ℕ`. -/
theorem tensorHsSmoothRepr_memWtwokTwo
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    {σ : ℝ} (T : tensorHs (I := I) (M := M) g r s σ)
    (hT_fs : (Function.support T.coeff).Finite) (k : ℕ) :
    MemWtwokTwo (I := I) (M := M) g k
      (tensorHsSmoothRepr (I := I) (M := M) T hT_fs) :=
  TensorHsSmoothReprAux.partialSum_memWtwokTwo_unconditional
    (I := I) (M := M) g r s k hT_fs.toFinset T.coeff

/-- For `σ ≥ 0`, the `L²`-image (`TensorL2`-coercion) of the smooth
representative `tensorHsSmoothRepr T hT_fs` coincides with the canonical
inclusion `tensorHsToL2 … hσ T` of `T` into `L²`. -/
theorem tensorHsSmoothRepr_toL2
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    {σ : ℝ} (hσ : 0 ≤ σ) (T : tensorHs (I := I) (M := M) g r s σ)
    (hT_fs : (Function.support T.coeff).Finite) :
    (tensorHsSmoothRepr (I := I) (M := M) T hT_fs :
        TensorL2 r s g) =
      tensorHsToL2 (I := I) (M := M)
        (g := g) (r := r) (s := s)
        (tensorResolventL2_isCompactOperator (I := I) (M := M)
          g r s) hσ T := by
  classical
  rw [tensorHsSmoothRepr_eq (I := I) (M := M) T hT_fs]
  conv_rhs => rw [tensorHs_eq_finset_sum_of_finite_support
    (I := I) (M := M) T hT_fs]
  rw [map_sum]
  refine Eq.symm ?_
  have h_coe :
      ((∑ i ∈ hT_fs.toFinset,
            T.coeff i • eigenvectorSmooth
              (I := I) (M := M) g r s i : SmoothCcTensor g r s) :
          TensorL2 r s g) =
      ∑ i ∈ hT_fs.toFinset,
        ((T.coeff i • eigenvectorSmooth
            (I := I) (M := M) g r s i : SmoothCcTensor g r s) :
          TensorL2 r s g) := by
    rw [show ((∑ i ∈ hT_fs.toFinset,
            T.coeff i • eigenvectorSmooth
              (I := I) (M := M) g r s i : SmoothCcTensor g r s) :
          TensorL2 r s g) =
        SmoothCcTensor.toL2 (g := g) (r := r) (s := s)
          (∑ i ∈ hT_fs.toFinset,
            T.coeff i • eigenvectorSmooth
              (I := I) (M := M) g r s i) from
      (SmoothCcTensor.toL2_apply _).symm]
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro i _hi
    exact SmoothCcTensor.toL2_apply (g := g) (r := r) (s := s)
      (T.coeff i • eigenvectorSmooth (I := I) (M := M) g r s i)
  rw [h_coe]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  rw [map_smul]
  rw [tensorHsToL2_tensorHsBasisVec (I := I) (M := M)
    (h_compact := tensorResolventL2_isCompactOperator
      (I := I) (M := M) g r s) hσ i]
  rw [tensorResolventHilbertEigenbasisSigma_apply
    (I := I) (M := M)
    (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s) i]
  have hcoe_smul :
      ((T.coeff i • eigenvectorSmooth
          (I := I) (M := M) g r s i : SmoothCcTensor g r s) :
        TensorL2 r s g) =
      T.coeff i • ((eigenvectorSmooth
          (I := I) (M := M) g r s i : SmoothCcTensor g r s) :
          TensorL2 r s g) := by
    have h1 :
        ((T.coeff i • eigenvectorSmooth
            (I := I) (M := M) g r s i : SmoothCcTensor g r s) :
          TensorL2 r s g) =
        SmoothCcTensor.toL2 (g := g) (r := r) (s := s)
          (T.coeff i • eigenvectorSmooth
            (I := I) (M := M) g r s i) := by
      rw [SmoothCcTensor.toL2_apply]
    have h2 :
        ((eigenvectorSmooth
            (I := I) (M := M) g r s i : SmoothCcTensor g r s) :
          TensorL2 r s g) =
        SmoothCcTensor.toL2 (g := g) (r := r) (s := s)
          (eigenvectorSmooth (I := I) (M := M) g r s i) := by
      rw [SmoothCcTensor.toL2_apply]
    rw [h1, h2, map_smul]
  rw [hcoe_smul]
  congr 1
  exact (eigenvectorSmooth_toL2 (I := I) (M := M) g r s i).symm

namespace TensorHsSmoothReprAux

variable (g : SmoothRiemannianMetric I M) (r s : ℕ) (k : ℕ)

/-- Per-summand `W^{2k,2}` bound: assuming each smooth eigenvector
representative satisfies the uniform bound `hC_bound`, the scaled summand
`c i • eigenvectorSmooth g r s i` has `wtwokTwoNorm` at most
`|c i| · C · (i.fst.val)⁻¹^(2k+1)` (in `ENNReal`). Uses scalar homogeneity of
the norm and that the eigenbasis vectors are unit-normalized. -/
private lemma summand_wtwokTwoNorm_le_unconditional
    {C : ℝ} (_hC_nn : 0 ≤ C)
    (hC_bound : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      wtwokTwoNorm (I := I) (M := M) g k
          (eigenvectorSmooth (I := I) (M := M) g r s i)
        ≤ ENNReal.ofReal (C * (i.fst.val)⁻¹ ^ (2 * k + 1)) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec
                (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i‖)
    (c : TensorEigenIdx (I := I) (M := M) g r s → ℝ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    wtwokTwoNorm (I := I) (M := M) g k
        (c i • eigenvectorSmooth (I := I) (M := M) g r s i)
      ≤ ENNReal.ofReal |c i| *
          ENNReal.ofReal (C * (i.fst.val)⁻¹ ^ (2 * k + 1)) := by
  have h_mem : MemWtwokTwo (I := I) (M := M) g k
      (eigenvectorSmooth (I := I) (M := M) g r s i) :=
    tensorEigenvector_memWtwokTwo (I := I) (M := M) g r s i k
  have h_smul := wtwokTwoNorm_smul (I := I) (M := M) g (c i) h_mem
  rw [h_smul]
  rw [Real.enorm_eq_ofReal_abs]
  have h_vec_norm :
      ‖tensorResolventEigenbasisVec (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M)
          g r s) i‖ = 1 :=
    (tensorResolventEigenbasisVec_orthonormal (I := I) (M := M)
      (g := g) (r := r) (s := s)
      (tensorResolventL2_isCompactOperator (I := I) (M := M)
        g r s)).norm_eq_one i
  have h_bd : wtwokTwoNorm (I := I) (M := M) g k
        (eigenvectorSmooth (I := I) (M := M) g r s i)
      ≤ ENNReal.ofReal (C * (i.fst.val)⁻¹ ^ (2 * k + 1)) := by
    have h := hC_bound i
    rw [h_vec_norm, ENNReal.ofReal_one, mul_one] at h
    exact h
  exact mul_le_mul_of_nonneg_left h_bd (zero_le _)

/-- Finite-sum `W^{2k,2}` bound: under the uniform per-eigenvector bound
`hC_bound`, the `wtwokTwoNorm` of the partial sum
`partialSum_unconditional g r s S c` is at most
`∑ i ∈ S, |c i| · C · (i.fst.val)⁻¹^(2k+1)` (in `ENNReal`). Proved by
induction on `S` via the triangle inequality and the per-summand bound. -/
private lemma partialSum_wtwokTwoNorm_le_sum_unconditional
    {C : ℝ} (hC_nn : 0 ≤ C)
    (hC_bound : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      wtwokTwoNorm (I := I) (M := M) g k
          (eigenvectorSmooth (I := I) (M := M) g r s i)
        ≤ ENNReal.ofReal (C * (i.fst.val)⁻¹ ^ (2 * k + 1)) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec
                (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i‖)
    (S : Finset (TensorEigenIdx (I := I) (M := M) g r s))
    (c : TensorEigenIdx (I := I) (M := M) g r s → ℝ) :
    wtwokTwoNorm (I := I) (M := M) g k
        (partialSum_unconditional (I := I) (M := M) g r s S c)
      ≤ ∑ i ∈ S, ENNReal.ofReal |c i| *
          ENNReal.ofReal (C * (i.fst.val)⁻¹ ^ (2 * k + 1)) := by
  classical
  induction S using Finset.induction with
  | empty =>
      rw [partialSum_empty_unconditional (I := I) (M := M) g r s c,
        wtwokTwoNorm_zero_section (I := I) (M := M) g k, Finset.sum_empty]
  | insert j A hj ih =>
      rw [partialSum_insert_unconditional (I := I) (M := M) g r s hj c]
      have h_mem_summand : MemWtwokTwo (I := I) (M := M) g k
          (c j • eigenvectorSmooth (I := I) (M := M) g r s j) :=
        MemWtwokTwo_smul (I := I) (M := M) g (c j)
          (tensorEigenvector_memWtwokTwo
            (I := I) (M := M) g r s j k)
      have h_mem_partial : MemWtwokTwo (I := I) (M := M) g k
          (partialSum_unconditional (I := I) (M := M) g r s A c) :=
        partialSum_memWtwokTwo_unconditional (I := I) (M := M) g r s k A c
      have h_tri := wtwokTwoNorm_add_le (I := I) (M := M) g
        h_mem_summand h_mem_partial
      refine le_trans h_tri ?_
      rw [Finset.sum_insert hj]
      have h_sumand_bd :=
        summand_wtwokTwoNorm_le_unconditional (I := I) (M := M) g r s k
          hC_nn hC_bound c j
      exact add_le_add h_sumand_bd ih

end TensorHsSmoothReprAux

/-- The manifold-aggregated `W^{2k, 2}` bound: there is a single geometric
constant `C ≥ 0`, uniform over every exponent `σ` and every finitely-supported
`Hˢ` element `T`, with `wtwokTwoNorm g k (tensorHsSmoothRepr T hT_fs)` bounded by
`ENNReal.ofReal C · ENNReal.ofReal (∑ i ∈ support, |T.coeff i| · (i.fst.val)⁻¹^(2k+1))`.
The constant comes from the per-eigenvector uniform bound
`eigenvectorSmooth_wtwokTwoNorm_le_uniform`, aggregated over the finite support. -/
theorem tensorHsSmoothRepr_wtwokTwoNorm_le_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {σ : ℝ} (T : tensorHs (I := I) (M := M) g r s σ)
        (hT_fs : (Function.support T.coeff).Finite),
        wtwokTwoNorm (I := I) (M := M) g k
            (tensorHsSmoothRepr (I := I) (M := M) T hT_fs)
          ≤ ENNReal.ofReal C *
              ENNReal.ofReal (∑ i ∈ hT_fs.toFinset,
                |T.coeff i| * (i.fst.val)⁻¹ ^ (2 * k + 1)) := by
  classical
  obtain ⟨C, hC_nn, hC_bound⟩ :=
    eigenvectorSmooth_wtwokTwoNorm_le_uniform
      (I := I) (M := M) g r s k
  refine ⟨C, hC_nn, ?_⟩
  intro σ T hT_fs
  unfold tensorHsSmoothRepr
  refine le_trans
    (TensorHsSmoothReprAux.partialSum_wtwokTwoNorm_le_sum_unconditional
      (I := I) (M := M) g r s k hC_nn hC_bound hT_fs.toFinset T.coeff)
    ?_
  have h_eigval_inv_one_le :
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s, (1 : ℝ) ≤ (i.fst.val)⁻¹ :=
    fun i => sharpDiff_eigen_inv_one_le (I := I) (M := M) g r s i
  have h_eigval_inv_nn :
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s, (0 : ℝ) ≤ (i.fst.val)⁻¹ :=
    fun i => le_trans zero_le_one (h_eigval_inv_one_le i)
  have h_pow_nn :
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        (0 : ℝ) ≤ (i.fst.val)⁻¹ ^ (2 * k + 1) :=
    fun i => pow_nonneg (h_eigval_inv_nn i) _
  have h_C_pow_nn :
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        (0 : ℝ) ≤ C * (i.fst.val)⁻¹ ^ (2 * k + 1) :=
    fun i => mul_nonneg hC_nn (h_pow_nn i)
  have h_summand_eq :
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        ENNReal.ofReal |T.coeff i| *
          ENNReal.ofReal (C * (i.fst.val)⁻¹ ^ (2 * k + 1)) =
        ENNReal.ofReal
          (|T.coeff i| * (C * (i.fst.val)⁻¹ ^ (2 * k + 1))) := by
    intro i
    rw [← ENNReal.ofReal_mul (abs_nonneg _)]
  rw [Finset.sum_congr rfl (fun i _hi => h_summand_eq i)]
  have h_summand_nn :
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        (0 : ℝ) ≤ |T.coeff i| * (C * (i.fst.val)⁻¹ ^ (2 * k + 1)) :=
    fun i => mul_nonneg (abs_nonneg _) (h_C_pow_nn i)
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _hi => h_summand_nn i)]
  have h_sum_eq :
      ∑ i ∈ hT_fs.toFinset,
          |T.coeff i| * (C * (i.fst.val)⁻¹ ^ (2 * k + 1)) =
        C * ∑ i ∈ hT_fs.toFinset,
          |T.coeff i| * (i.fst.val)⁻¹ ^ (2 * k + 1) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i _hi; ring
  rw [h_sum_eq]
  rw [ENNReal.ofReal_mul hC_nn]

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
