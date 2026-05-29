import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorManifoldSobolevAggregate
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SobolevScale.Defs

/-!
# From a finitely-supported spectral Sobolev element to a smooth `W^{2k,2}` section

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, the uniform-Sobolev
hypothesis `h_atlas`, an order `k : ℕ` and a real Sobolev exponent `σ`, this
file constructs, from each element `T : tensorHs g r s σ` whose
eigenbasis coordinates have **finite support**, a smooth, compactly-supported
representative

  `tensorHsSmoothRepr T hT_fs : SmoothCcTensor g r s`,

namely the finite linear combination
`∑ i ∈ support, T.coeff i • eigenvectorSmooth g r s h_atlas i`. The
representative is a true `W^{2k, 2}` element (`MemWtwokTwo g k`) and its
`L²`-image agrees, for `σ ≥ 0`, with the canonical inclusion
`tensorHsToL2 hσ T`.

The headline aggregates the manifold-aggregated per-eigenvector Sobolev bound
`eigenvectorSmooth_wtwokTwoNorm_le_uniform` (with the uniform constant `C`) into
a *single* `W^{2k, 2}` bound for every finitely-supported coordinate family,
with the same uniform geometric constant `C`:

  `wtwokTwoNorm g k (tensorHsSmoothRepr T hT_fs) ≤
    ENNReal.ofReal C *
      ENNReal.ofReal (∑ i ∈ support, |T.coeff i| · (i.fst.val)⁻¹ ^ (2k + 1))`.

The right-hand side is, by Cauchy–Schwarz on the finite support, controllable
by the spectral Sobolev norm of `T` at any exponent `σ` sufficiently large to
make the dual eigenvalue tail summable; downstream consumers pick `σ`.

## Main definitions

* `tensorHsSmoothRepr T hT_fs` — the smooth compactly-supported representative
  of a finitely-supported `Hˢ` element, as a finite linear combination of the
  smooth eigenvector representatives.

## Main results

* `tensorHsSmoothRepr_memWtwokTwo` — the smooth representative lies in
  `MemWtwokTwo g k` for every `k : ℕ`.
* `tensorHsSmoothRepr_toL2` — for `σ ≥ 0`, the `L²`-image of the smooth
  representative coincides with the canonical inclusion `tensorHsToL2 hσ T`.
* `tensorHsSmoothRepr_wtwokTwoNorm_le_uniform` — the manifold-aggregated
  `W^{2k, 2}` bound: a single geometric constant `C ≥ 0`, uniform over *every*
  exponent `σ` and *every* finitely-supported `Hˢ` element, controls the
  Sobolev norm of the smooth representative by the explicit finite sum of
  `|coeff i| · (i.fst.val)⁻¹^(2k + 1)` over the support.

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

/-! ## File-local Borel-space instances on `E` and `M` -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-! ## The smooth representative of a finitely-supported `Hˢ` element

For a finitely-supported coordinate family `T.coeff`, the spectral
decomposition `T = ∑_{i ∈ support} (coeff i T) • bᵢ` makes sense as a *finite*
sum. Replacing each abstract eigenvector `bᵢ = tensorResolventEigenbasisVec
h_atlas i` by its smooth representative `eigenvectorSmooth g r s h_atlas i`
yields a smooth, compactly-supported tensor section. -/

namespace TensorHsSmoothReprAux

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)

/-- For a coordinate family `c : TensorEigenIdx g r s → ℝ` and a finite subset
`S` of the eigenbasis index set, the partial smooth representative
`∑ i ∈ S, c i • eigenvectorSmooth g r s h_atlas i`. -/
private def partialSum (S : Finset (TensorEigenIdx (I := I) (M := M) g r s))
    (c : TensorEigenIdx (I := I) (M := M) g r s → ℝ) :
    SmoothCcTensor g r s :=
  ∑ i ∈ S, c i • eigenvectorSmooth (I := I) (M := M) g r s h_atlas i

/-- The empty partial sum is the zero section. -/
private lemma partialSum_empty
    (c : TensorEigenIdx (I := I) (M := M) g r s → ℝ) :
    partialSum (I := I) (M := M) g r s h_atlas (∅ :
      Finset (TensorEigenIdx (I := I) (M := M) g r s)) c =
      (0 : SmoothCcTensor g r s) := by
  unfold partialSum; simp

open scoped Classical in
/-- Inserting a new index into the partial sum is the addition of the new
summand with the partial sum over the remaining set. -/
private lemma partialSum_insert
    {S : Finset (TensorEigenIdx (I := I) (M := M) g r s)}
    {j : TensorEigenIdx (I := I) (M := M) g r s} (hj : j ∉ S)
    (c : TensorEigenIdx (I := I) (M := M) g r s → ℝ) :
    partialSum (I := I) (M := M) g r s h_atlas (insert j S) c =
      c j • eigenvectorSmooth (I := I) (M := M) g r s h_atlas j +
        partialSum (I := I) (M := M) g r s h_atlas S c := by
  unfold partialSum; rw [Finset.sum_insert hj]

/-- For *every* `k`, the partial smooth representative lies in
`MemWtwokTwo g k`: each summand `c i • eigenvectorSmooth …` is, by closure of
`MemWtwokTwo` under scalar multiplication, in the space; closure under finite
addition follows by `Finset` induction. -/
private lemma partialSum_memWtwokTwo
    (k : ℕ)
    (S : Finset (TensorEigenIdx (I := I) (M := M) g r s))
    (c : TensorEigenIdx (I := I) (M := M) g r s → ℝ) :
    MemWtwokTwo (I := I) (M := M) g k
      (partialSum (I := I) (M := M) g r s h_atlas S c) := by
  classical
  induction S using Finset.induction with
  | empty =>
      rw [partialSum_empty (I := I) (M := M) g r s h_atlas c]
      exact MemWtwokTwo_zero_section (I := I) (M := M) g k
  | insert j A hj ih =>
      rw [partialSum_insert (I := I) (M := M) g r s h_atlas hj c]
      refine MemWtwokTwo_add (I := I) (M := M) g ?_ ih
      exact MemWtwokTwo_smul (I := I) (M := M) g (c j)
        (tensorEigenvector_memWtwokTwo (I := I) (M := M) g r s h_atlas j k)

end TensorHsSmoothReprAux

/-- **The smooth representative of a finitely-supported `Hˢ` element.**

For an element `T : tensorHs g r s σ` whose coordinate family
`T.coeff` has finite support `hT_fs`, the canonical smooth, compactly-supported
representative is the finite linear combination

  `∑ i ∈ hT_fs.toFinset, T.coeff i • eigenvectorSmooth g r s h_atlas i`.

Each summand lies in the `ℝ`-module `SmoothCcTensor g r s`, so the finite sum
stays inside it. The representative depends only on the coordinate family, not
on the choice of finite cover of the support. -/
noncomputable def tensorHsSmoothRepr
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    {σ : ℝ} (T : tensorHs (I := I) (M := M) g r s σ)
    (hT_fs : (Function.support T.coeff).Finite) :
    SmoothCcTensor g r s :=
  TensorHsSmoothReprAux.partialSum (I := I) (M := M) g r s h_atlas
    hT_fs.toFinset T.coeff

/-- Unfolding of the smooth representative as the canonical finite sum of the
smooth eigenvector representatives. -/
theorem tensorHsSmoothRepr_eq
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    {σ : ℝ} (T : tensorHs (I := I) (M := M) g r s σ)
    (hT_fs : (Function.support T.coeff).Finite) :
    tensorHsSmoothRepr (I := I) (M := M) h_atlas T hT_fs =
      ∑ i ∈ hT_fs.toFinset,
        T.coeff i •
          eigenvectorSmooth (I := I) (M := M) g r s h_atlas i := rfl

/-- The smooth representative of a finitely-supported `Hˢ` element lies in the
tensor Sobolev space `W^{2k, 2}` for *every* `k : ℕ`. -/
theorem tensorHsSmoothRepr_memWtwokTwo
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    {σ : ℝ} (T : tensorHs (I := I) (M := M) g r s σ)
    (hT_fs : (Function.support T.coeff).Finite) (k : ℕ) :
    MemWtwokTwo (I := I) (M := M) g k
      (tensorHsSmoothRepr (I := I) (M := M) h_atlas T hT_fs) :=
  TensorHsSmoothReprAux.partialSum_memWtwokTwo
    (I := I) (M := M) g r s h_atlas k hT_fs.toFinset T.coeff

/-! ## Identification with the canonical `Hˢ → L²` inclusion

For `σ ≥ 0`, the canonical inclusion `tensorHsToL2 hσ : Hˢ →L[ℝ] L²` sends `T`
to the `L²` tensor with the same eigenbasis coordinates. For a finitely-supported
`T`, that `L²` element is itself a finite linear combination of the abstract
eigenvectors `tensorResolventEigenbasisVec h_atlas i`; replacing each abstract
eigenvector by its smooth representative gives exactly `tensorHsSmoothRepr`. -/

namespace TensorHsSmoothReprAux

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)

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
  -- The summand vanishes except at `i = j`, where it is `T.coeff j`.
  by_cases hj_supp : j ∈ Function.support T.coeff
  · -- `j` is in the support, so it is in `hT_fs.toFinset`.
    have hj_mem : j ∈ hT_fs.toFinset := hT_fs.mem_toFinset.mpr hj_supp
    have h_isolate :
        ∑ i ∈ hT_fs.toFinset, (if j = i then T.coeff i else 0) =
          (if j = j then T.coeff j else 0) := by
      refine Finset.sum_eq_single_of_mem j hj_mem ?_
      intro i _ hij
      simp [Ne.symm hij]
    rw [h_isolate]
    simp
  · -- `j` is not in the support, so `T.coeff j = 0`, and the sum is `0`.
    have hzero : T.coeff j = 0 := by
      by_contra hne
      exact hj_supp (Function.mem_support.mpr hne)
    -- Show LHS = RHS by demonstrating both sides equal `0`.
    have h_rhs_zero :
        ∑ i ∈ hT_fs.toFinset,
            (if j = i then T.coeff i else (0 : ℝ)) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro i _hi
      by_cases h : j = i
      · subst h; simp [hzero]
      · simp [h]
    rw [hzero, h_rhs_zero]

/-- For `σ ≥ 0`, the canonical `L²` inclusion sends the smooth representative
of a finitely-supported `Hˢ` element to the same `L²` element as the abstract
inclusion `tensorHsToL2 hσ T`. -/
theorem tensorHsSmoothRepr_toL2
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    {σ : ℝ} (hσ : 0 ≤ σ) (T : tensorHs (I := I) (M := M) g r s σ)
    (hT_fs : (Function.support T.coeff).Finite) :
    (tensorHsSmoothRepr (I := I) (M := M) h_atlas T hT_fs : TensorL2 r s g) =
      tensorHsToL2 (I := I) (M := M)
        (g := g) (r := r) (s := s) h_atlas hσ T := by
  classical
  -- Unfold the smooth representative to its finite sum.
  rw [tensorHsSmoothRepr_eq (I := I) (M := M) h_atlas T hT_fs]
  -- Rewrite `T` as the finite sum of its basis components.
  conv_rhs => rw [tensorHs_eq_finset_sum_of_finite_support
    (I := I) (M := M) T hT_fs]
  -- Push the inclusion `tensorHsToL2 hσ` (a continuous linear map) through the
  -- finite sum and the scalar multiples.
  rw [map_sum]
  -- Match summand by summand.
  refine Eq.symm ?_
  -- We push the `SmoothCcTensor → TensorL2` coercion through the finite sum.
  -- A finite sum in `SmoothCcTensor` coerces to the same finite sum in
  -- `TensorL2`: use the algebra-hom property of the inclusion
  -- `SmoothCcTensor.toL2`.
  have h_coe :
      ((∑ i ∈ hT_fs.toFinset,
            T.coeff i • eigenvectorSmooth
              (I := I) (M := M) g r s h_atlas i : SmoothCcTensor g r s) :
          TensorL2 r s g) =
      ∑ i ∈ hT_fs.toFinset,
        ((T.coeff i • eigenvectorSmooth
            (I := I) (M := M) g r s h_atlas i : SmoothCcTensor g r s) :
          TensorL2 r s g) := by
    -- The coercion `SmoothCcTensor → TensorL2` is the continuous linear map
    -- `SmoothCcTensor.toL2`; rewrite via `toL2_apply` on both sides, then
    -- push the sum through via `map_sum`.
    rw [show ((∑ i ∈ hT_fs.toFinset,
            T.coeff i • eigenvectorSmooth
              (I := I) (M := M) g r s h_atlas i : SmoothCcTensor g r s) :
          TensorL2 r s g) =
        SmoothCcTensor.toL2 (g := g) (r := r) (s := s)
          (∑ i ∈ hT_fs.toFinset,
            T.coeff i • eigenvectorSmooth
              (I := I) (M := M) g r s h_atlas i) from
      (SmoothCcTensor.toL2_apply _).symm]
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro i _hi
    exact SmoothCcTensor.toL2_apply (g := g) (r := r) (s := s)
      (T.coeff i • eigenvectorSmooth (I := I) (M := M) g r s h_atlas i)
  rw [h_coe]
  -- Per-summand: `(c • eigenvectorSmooth i : TensorL2) = c • (eigenvectorSmooth i : TensorL2)`
  -- via the linearity of `SmoothCcTensor → TensorL2`. Use the
  -- `SmoothCcTensor.toL2` continuous linear map and `eigenvectorSmooth_toL2`.
  refine Finset.sum_congr rfl ?_
  intro i _hi
  -- The summand identity, summarised:
  --   tensorHsToL2 hσ (T.coeff i • tensorHsBasisVec h_atlas σ i)
  --     = T.coeff i • tensorResolventHilbertEigenbasisSigma h_atlas i      (linearity of tensorHsToL2 + tensorHsToL2_tensorHsBasisVec)
  --     = T.coeff i • tensorResolventEigenbasisVec h_atlas i               (tensorResolventHilbertEigenbasisSigma_apply)
  --     = T.coeff i • (eigenvectorSmooth g r s h_atlas i : TensorL2 r s g) (eigenvectorSmooth_toL2)
  rw [map_smul]
  rw [tensorHsToL2_tensorHsBasisVec (I := I) (M := M) hσ i]
  rw [tensorResolventHilbertEigenbasisSigma_apply
    (I := I) (M := M) h_atlas i]
  -- The coercion of `c • S` in `SmoothCcTensor` to `TensorL2` is `c •` the
  -- coercion of `S`, via the `Module`-hom structure of `SmoothCcTensor.toL2`.
  have hcoe_smul :
      ((T.coeff i • eigenvectorSmooth
          (I := I) (M := M) g r s h_atlas i : SmoothCcTensor g r s) :
        TensorL2 r s g) =
      T.coeff i • ((eigenvectorSmooth
          (I := I) (M := M) g r s h_atlas i : SmoothCcTensor g r s) :
          TensorL2 r s g) := by
    have h1 :
        ((T.coeff i • eigenvectorSmooth
            (I := I) (M := M) g r s h_atlas i : SmoothCcTensor g r s) :
          TensorL2 r s g) =
        SmoothCcTensor.toL2 (g := g) (r := r) (s := s)
          (T.coeff i • eigenvectorSmooth
            (I := I) (M := M) g r s h_atlas i) := by
      rw [SmoothCcTensor.toL2_apply]
    have h2 :
        ((eigenvectorSmooth
            (I := I) (M := M) g r s h_atlas i : SmoothCcTensor g r s) :
          TensorL2 r s g) =
        SmoothCcTensor.toL2 (g := g) (r := r) (s := s)
          (eigenvectorSmooth (I := I) (M := M) g r s h_atlas i) := by
      rw [SmoothCcTensor.toL2_apply]
    rw [h1, h2, map_smul]
  rw [hcoe_smul]
  -- The remaining identity is the `L²` coercion of `eigenvectorSmooth` =
  -- `tensorResolventEigenbasisVec` (`eigenvectorSmooth_toL2`).
  congr 1
  exact (eigenvectorSmooth_toL2 (I := I) (M := M) g r s h_atlas i).symm

/-! ## The uniform Sobolev bound on the smooth representative

Aggregating the manifold-aggregated per-eigenvector Sobolev bound
`eigenvectorSmooth_wtwokTwoNorm_le_uniform` over the finite support of the
coordinate family — via the triangle inequality and scalar homogeneity of the
tensor Sobolev norm — yields the *single*-constant `W^{2k, 2}` bound on the
smooth representative of every finitely-supported `Hˢ` element. -/

namespace TensorHsSmoothReprAux

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
  (k : ℕ)

/-- The per-summand bound on `wtwokTwoNorm` of `c i • eigenvectorSmooth …`,
specialised from `eigenvectorSmooth_wtwokTwoNorm_le_uniform`. With `C ≥ 0` the
uniform geometric constant and `‖vec‖ = 1` (eigenbasis vectors are
orthonormal), the bound becomes
`‖c i‖ₑ * ofReal (C · μ_i⁻¹^(2k + 1))`. -/
private lemma summand_wtwokTwoNorm_le
    {C : ℝ} (_hC_nn : 0 ≤ C)
    (hC_bound : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      wtwokTwoNorm (I := I) (M := M) g k
          (eigenvectorSmooth (I := I) (M := M) g r s h_atlas i)
        ≤ ENNReal.ofReal (C * (i.fst.val)⁻¹ ^ (2 * k + 1)) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec
                (I := I) (M := M) h_atlas i‖)
    (c : TensorEigenIdx (I := I) (M := M) g r s → ℝ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    wtwokTwoNorm (I := I) (M := M) g k
        (c i • eigenvectorSmooth (I := I) (M := M) g r s h_atlas i)
      ≤ ENNReal.ofReal |c i| *
          ENNReal.ofReal (C * (i.fst.val)⁻¹ ^ (2 * k + 1)) := by
  -- Apply the scalar homogeneity at the section level.
  have h_mem : MemWtwokTwo (I := I) (M := M) g k
      (eigenvectorSmooth (I := I) (M := M) g r s h_atlas i) :=
    tensorEigenvector_memWtwokTwo (I := I) (M := M) g r s h_atlas i k
  have h_smul := wtwokTwoNorm_smul (I := I) (M := M) g (c i) h_mem
  rw [h_smul]
  -- `‖c i‖ₑ = ENNReal.ofReal |c i|`.
  rw [Real.enorm_eq_ofReal_abs]
  -- Use the per-eigenvector bound and the unit-norm identity.
  have h_vec_norm :
      ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖ = 1 :=
    (tensorResolventEigenbasisVec_orthonormal (I := I) (M := M)
      (g := g) (r := r) (s := s) h_atlas).norm_eq_one i
  have h_bd : wtwokTwoNorm (I := I) (M := M) g k
        (eigenvectorSmooth (I := I) (M := M) g r s h_atlas i)
      ≤ ENNReal.ofReal (C * (i.fst.val)⁻¹ ^ (2 * k + 1)) := by
    have h := hC_bound i
    rw [h_vec_norm, ENNReal.ofReal_one, mul_one] at h
    exact h
  exact mul_le_mul_of_nonneg_left h_bd (zero_le _)

/-- The partial sum's `wtwokTwoNorm` is bounded, by the triangle inequality and
the per-summand bound, by the finite sum
`∑ i ∈ S, ofReal |c i| · ofReal (C · μ_i⁻¹^(2k + 1))`. -/
private lemma partialSum_wtwokTwoNorm_le_sum
    {C : ℝ} (hC_nn : 0 ≤ C)
    (hC_bound : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      wtwokTwoNorm (I := I) (M := M) g k
          (eigenvectorSmooth (I := I) (M := M) g r s h_atlas i)
        ≤ ENNReal.ofReal (C * (i.fst.val)⁻¹ ^ (2 * k + 1)) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec
                (I := I) (M := M) h_atlas i‖)
    (S : Finset (TensorEigenIdx (I := I) (M := M) g r s))
    (c : TensorEigenIdx (I := I) (M := M) g r s → ℝ) :
    wtwokTwoNorm (I := I) (M := M) g k
        (partialSum (I := I) (M := M) g r s h_atlas S c)
      ≤ ∑ i ∈ S, ENNReal.ofReal |c i| *
          ENNReal.ofReal (C * (i.fst.val)⁻¹ ^ (2 * k + 1)) := by
  classical
  induction S using Finset.induction with
  | empty =>
      rw [partialSum_empty (I := I) (M := M) g r s h_atlas c,
        wtwokTwoNorm_zero_section (I := I) (M := M) g k, Finset.sum_empty]
  | insert j A hj ih =>
      rw [partialSum_insert (I := I) (M := M) g r s h_atlas hj c]
      -- Triangle inequality: both arguments are `MemWtwokTwo`.
      have h_mem_summand : MemWtwokTwo (I := I) (M := M) g k
          (c j • eigenvectorSmooth (I := I) (M := M) g r s h_atlas j) :=
        MemWtwokTwo_smul (I := I) (M := M) g (c j)
          (tensorEigenvector_memWtwokTwo
            (I := I) (M := M) g r s h_atlas j k)
      have h_mem_partial : MemWtwokTwo (I := I) (M := M) g k
          (partialSum (I := I) (M := M) g r s h_atlas A c) :=
        partialSum_memWtwokTwo (I := I) (M := M) g r s h_atlas k A c
      have h_tri := wtwokTwoNorm_add_le (I := I) (M := M) g
        h_mem_summand h_mem_partial
      refine le_trans h_tri ?_
      rw [Finset.sum_insert hj]
      have h_sumand_bd :=
        summand_wtwokTwoNorm_le (I := I) (M := M) g r s h_atlas k
          hC_nn hC_bound c j
      exact add_le_add h_sumand_bd ih

end TensorHsSmoothReprAux

/-! ## The headline: a single uniform constant for every finitely-supported `Hˢ` element -/

/-- **Manifold-aggregated `W^{2k, 2}` Sobolev bound for the smooth
representative of a finitely-supported spectral Sobolev element.**

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, the uniform-Sobolev
hypothesis `h_atlas` and an order `k : ℕ`, there is a single geometric
constant `C ≥ 0` — uniform over every Sobolev exponent `σ` and every
finitely-supported element `T : tensorHs g r s σ` — such that the
global tensor Sobolev norm `wtwokTwoNorm g k (tensorHsSmoothRepr T hT_fs)` of
the canonical smooth representative is bounded by

  `ENNReal.ofReal C *
    ENNReal.ofReal (∑ i ∈ hT_fs.toFinset,
      |T.coeff i| · (i.fst.val)⁻¹ ^ (2 * k + 1))`.

The proof aggregates the manifold-aggregated per-eigenvector bound
`eigenvectorSmooth_wtwokTwoNorm_le_uniform` over the finite support of the
coordinate family via the triangle inequality and scalar homogeneity of the
tensor Sobolev norm; eigenbasis vectors have unit `L²` norm, eliminating the
`‖vec‖` factor; the per-summand `ofReal` constants combine to a single
`ofReal` of the finite sum thanks to non-negativity. -/
theorem tensorHsSmoothRepr_wtwokTwoNorm_le_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {σ : ℝ} (T : tensorHs (I := I) (M := M) g r s σ)
        (hT_fs : (Function.support T.coeff).Finite),
        wtwokTwoNorm (I := I) (M := M) g k
            (tensorHsSmoothRepr (I := I) (M := M) h_atlas T hT_fs)
          ≤ ENNReal.ofReal C *
              ENNReal.ofReal (∑ i ∈ hT_fs.toFinset,
                |T.coeff i| * (i.fst.val)⁻¹ ^ (2 * k + 1)) := by
  classical
  obtain ⟨C, hC_nn, hC_bound⟩ :=
    eigenvectorSmooth_wtwokTwoNorm_le_uniform
      (I := I) (M := M) g r s h_atlas k
  refine ⟨C, hC_nn, ?_⟩
  intro σ T hT_fs
  -- Unfold the smooth representative to the partial sum.
  unfold tensorHsSmoothRepr
  -- Apply the partial-sum bound.
  refine le_trans
    (TensorHsSmoothReprAux.partialSum_wtwokTwoNorm_le_sum
      (I := I) (M := M) g r s h_atlas k hC_nn hC_bound hT_fs.toFinset T.coeff)
    ?_
  -- The finite sum `∑ i, ofReal |c i| · ofReal (C * μ⁻¹^…)` equals
  -- `ofReal C · ofReal (∑ i, |c i| · μ⁻¹^…)` by `ofReal` linearity on
  -- non-negative summands.
  -- Step 1: combine each `ofReal |c i| · ofReal (C * μ⁻¹^…)` into one
  -- `ofReal (|c i| · C · μ⁻¹^…)`.
  have h_eigval_inv_one_le :
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s, (1 : ℝ) ≤ (i.fst.val)⁻¹ :=
    fun i => sharpDiff_eigen_inv_one_le (I := I) (M := M) g r s h_atlas i
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
  -- Step 2: `∑ i, ofReal (|c i| · (C · μ⁻¹^…)) = ofReal (∑ i, …)`.
  have h_summand_nn :
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        (0 : ℝ) ≤ |T.coeff i| * (C * (i.fst.val)⁻¹ ^ (2 * k + 1)) :=
    fun i => mul_nonneg (abs_nonneg _) (h_C_pow_nn i)
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _hi => h_summand_nn i)]
  -- Step 3: factor `C` out of the inner sum:
  -- `∑ |c i| · (C · μ⁻¹^…) = C · ∑ |c i| · μ⁻¹^…`.
  have h_sum_eq :
      ∑ i ∈ hT_fs.toFinset,
          |T.coeff i| * (C * (i.fst.val)⁻¹ ^ (2 * k + 1)) =
        C * ∑ i ∈ hT_fs.toFinset,
          |T.coeff i| * (i.fst.val)⁻¹ ^ (2 * k + 1) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i _hi; ring
  rw [h_sum_eq]
  -- Step 4: split `ofReal (C · ∑ …) = ofReal C · ofReal (∑ …)`.
  rw [ENNReal.ofReal_mul hC_nn]

/-! ## Sanity tests -/

section ElaborationTests

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)

example {σ : ℝ} (T : tensorHs (I := I) (M := M) g r s σ)
    (hT_fs : (Function.support T.coeff).Finite) :
    SmoothCcTensor g r s :=
  tensorHsSmoothRepr (I := I) (M := M) h_atlas T hT_fs

example {σ : ℝ} (T : tensorHs (I := I) (M := M) g r s σ)
    (hT_fs : (Function.support T.coeff).Finite) (k : ℕ) :
    MemWtwokTwo (I := I) (M := M) g k
      (tensorHsSmoothRepr (I := I) (M := M) h_atlas T hT_fs) :=
  tensorHsSmoothRepr_memWtwokTwo (I := I) (M := M) h_atlas T hT_fs k

example (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {σ : ℝ} (T : tensorHs (I := I) (M := M) g r s σ)
        (hT_fs : (Function.support T.coeff).Finite),
        wtwokTwoNorm (I := I) (M := M) g k
            (tensorHsSmoothRepr (I := I) (M := M) h_atlas T hT_fs)
          ≤ ENNReal.ofReal C *
              ENNReal.ofReal (∑ i ∈ hT_fs.toFinset,
                |T.coeff i| * (i.fst.val)⁻¹ ^ (2 * k + 1)) :=
  tensorHsSmoothRepr_wtwokTwoNorm_le_uniform (I := I) (M := M) g r s h_atlas k

example {σ : ℝ} (hσ : 0 ≤ σ)
    (T : tensorHs (I := I) (M := M) g r s σ)
    (hT_fs : (Function.support T.coeff).Finite) :
    (tensorHsSmoothRepr (I := I) (M := M) h_atlas T hT_fs : TensorL2 r s g) =
      tensorHsToL2 (I := I) (M := M)
        (g := g) (r := r) (s := s) h_atlas hσ T :=
  tensorHsSmoothRepr_toL2 (I := I) (M := M) h_atlas hσ T hT_fs

end ElaborationTests

/-! ## Chart-locality-free twins

The declarations below re-key every `h_atlas`-dependent result above onto the
intrinsic compact-operator eigenbasis
`tensorResolventEigenbasisVec_ofCompact (… intrinsic g r s)`, eliminating the
chart-selection hypothesis `h_atlas`. Each twin proves the same statement as its
original, with `h_atlas` removed, and consumes the corresponding chart-locality-
free twins of its dependencies. -/

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

namespace TensorHsSmoothReprAux

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)

/-- Chart-locality-free twin of `partialSum`. -/
private def partialSum_unconditional
    (S : Finset (TensorEigenIdx (I := I) (M := M) g r s))
    (c : TensorEigenIdx (I := I) (M := M) g r s → ℝ) :
    SmoothCcTensor g r s :=
  ∑ i ∈ S, c i • eigenvectorSmooth_unconditional (I := I) (M := M) g r s i

/-- Chart-locality-free twin of `partialSum_empty`. -/
private lemma partialSum_empty_unconditional
    (c : TensorEigenIdx (I := I) (M := M) g r s → ℝ) :
    partialSum_unconditional (I := I) (M := M) g r s (∅ :
      Finset (TensorEigenIdx (I := I) (M := M) g r s)) c =
      (0 : SmoothCcTensor g r s) := by
  unfold partialSum_unconditional; simp

open scoped Classical in
/-- Chart-locality-free twin of `partialSum_insert`. -/
private lemma partialSum_insert_unconditional
    {S : Finset (TensorEigenIdx (I := I) (M := M) g r s)}
    {j : TensorEigenIdx (I := I) (M := M) g r s} (hj : j ∉ S)
    (c : TensorEigenIdx (I := I) (M := M) g r s → ℝ) :
    partialSum_unconditional (I := I) (M := M) g r s (insert j S) c =
      c j • eigenvectorSmooth_unconditional (I := I) (M := M) g r s j +
        partialSum_unconditional (I := I) (M := M) g r s S c := by
  unfold partialSum_unconditional; rw [Finset.sum_insert hj]

/-- Chart-locality-free twin of `partialSum_memWtwokTwo`. -/
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
        (tensorEigenvector_memWtwokTwo_unconditional (I := I) (M := M) g r s j k)

end TensorHsSmoothReprAux

/-- Chart-locality-free twin of `tensorHsSmoothRepr`. -/
noncomputable def tensorHsSmoothRepr_unconditional
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    {σ : ℝ} (T : tensorHs (I := I) (M := M) g r s σ)
    (hT_fs : (Function.support T.coeff).Finite) :
    SmoothCcTensor g r s :=
  TensorHsSmoothReprAux.partialSum_unconditional (I := I) (M := M) g r s
    hT_fs.toFinset T.coeff

/-- Chart-locality-free twin of `tensorHsSmoothRepr_eq`. -/
theorem tensorHsSmoothRepr_eq_unconditional
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    {σ : ℝ} (T : tensorHs (I := I) (M := M) g r s σ)
    (hT_fs : (Function.support T.coeff).Finite) :
    tensorHsSmoothRepr_unconditional (I := I) (M := M) T hT_fs =
      ∑ i ∈ hT_fs.toFinset,
        T.coeff i •
          eigenvectorSmooth_unconditional (I := I) (M := M) g r s i := rfl

/-- Chart-locality-free twin of `tensorHsSmoothRepr_memWtwokTwo`. -/
theorem tensorHsSmoothRepr_memWtwokTwo_unconditional
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    {σ : ℝ} (T : tensorHs (I := I) (M := M) g r s σ)
    (hT_fs : (Function.support T.coeff).Finite) (k : ℕ) :
    MemWtwokTwo (I := I) (M := M) g k
      (tensorHsSmoothRepr_unconditional (I := I) (M := M) T hT_fs) :=
  TensorHsSmoothReprAux.partialSum_memWtwokTwo_unconditional
    (I := I) (M := M) g r s k hT_fs.toFinset T.coeff

/-- Chart-locality-free twin of `tensorHsSmoothRepr_toL2`. -/
theorem tensorHsSmoothRepr_toL2_unconditional
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    {σ : ℝ} (hσ : 0 ≤ σ) (T : tensorHs (I := I) (M := M) g r s σ)
    (hT_fs : (Function.support T.coeff).Finite) :
    (tensorHsSmoothRepr_unconditional (I := I) (M := M) T hT_fs :
        TensorL2 r s g) =
      tensorHsToL2_ofCompact (I := I) (M := M)
        (g := g) (r := r) (s := s)
        (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
          g r s) hσ T := by
  classical
  -- Unfold the smooth representative to its finite sum.
  rw [tensorHsSmoothRepr_eq_unconditional (I := I) (M := M) T hT_fs]
  -- Rewrite `T` as the finite sum of its basis components.
  conv_rhs => rw [tensorHs_eq_finset_sum_of_finite_support
    (I := I) (M := M) T hT_fs]
  -- Push the inclusion (a continuous linear map) through the finite sum.
  rw [map_sum]
  refine Eq.symm ?_
  -- The `SmoothCcTensor → TensorL2` coercion pushes through the finite sum.
  have h_coe :
      ((∑ i ∈ hT_fs.toFinset,
            T.coeff i • eigenvectorSmooth_unconditional
              (I := I) (M := M) g r s i : SmoothCcTensor g r s) :
          TensorL2 r s g) =
      ∑ i ∈ hT_fs.toFinset,
        ((T.coeff i • eigenvectorSmooth_unconditional
            (I := I) (M := M) g r s i : SmoothCcTensor g r s) :
          TensorL2 r s g) := by
    rw [show ((∑ i ∈ hT_fs.toFinset,
            T.coeff i • eigenvectorSmooth_unconditional
              (I := I) (M := M) g r s i : SmoothCcTensor g r s) :
          TensorL2 r s g) =
        SmoothCcTensor.toL2 (g := g) (r := r) (s := s)
          (∑ i ∈ hT_fs.toFinset,
            T.coeff i • eigenvectorSmooth_unconditional
              (I := I) (M := M) g r s i) from
      (SmoothCcTensor.toL2_apply _).symm]
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro i _hi
    exact SmoothCcTensor.toL2_apply (g := g) (r := r) (s := s)
      (T.coeff i • eigenvectorSmooth_unconditional (I := I) (M := M) g r s i)
  rw [h_coe]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  rw [map_smul]
  rw [tensorHsToL2_ofCompact_tensorHsBasisVec (I := I) (M := M)
    (h_compact := tensorResolventL2_isCompactOperator_intrinsic
      (I := I) (M := M) g r s) hσ i]
  rw [tensorResolventHilbertEigenbasisSigma_ofCompact_apply
    (I := I) (M := M)
    (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M) g r s) i]
  -- The coercion of `c • S` in `SmoothCcTensor` to `TensorL2` is `c •` the
  -- coercion of `S`.
  have hcoe_smul :
      ((T.coeff i • eigenvectorSmooth_unconditional
          (I := I) (M := M) g r s i : SmoothCcTensor g r s) :
        TensorL2 r s g) =
      T.coeff i • ((eigenvectorSmooth_unconditional
          (I := I) (M := M) g r s i : SmoothCcTensor g r s) :
          TensorL2 r s g) := by
    have h1 :
        ((T.coeff i • eigenvectorSmooth_unconditional
            (I := I) (M := M) g r s i : SmoothCcTensor g r s) :
          TensorL2 r s g) =
        SmoothCcTensor.toL2 (g := g) (r := r) (s := s)
          (T.coeff i • eigenvectorSmooth_unconditional
            (I := I) (M := M) g r s i) := by
      rw [SmoothCcTensor.toL2_apply]
    have h2 :
        ((eigenvectorSmooth_unconditional
            (I := I) (M := M) g r s i : SmoothCcTensor g r s) :
          TensorL2 r s g) =
        SmoothCcTensor.toL2 (g := g) (r := r) (s := s)
          (eigenvectorSmooth_unconditional (I := I) (M := M) g r s i) := by
      rw [SmoothCcTensor.toL2_apply]
    rw [h1, h2, map_smul]
  rw [hcoe_smul]
  congr 1
  exact (eigenvectorSmooth_toL2_unconditional (I := I) (M := M) g r s i).symm

namespace TensorHsSmoothReprAux

variable (g : SmoothRiemannianMetric I M) (r s : ℕ) (k : ℕ)

/-- Chart-locality-free twin of `summand_wtwokTwoNorm_le`. -/
private lemma summand_wtwokTwoNorm_le_unconditional
    {C : ℝ} (_hC_nn : 0 ≤ C)
    (hC_bound : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      wtwokTwoNorm (I := I) (M := M) g k
          (eigenvectorSmooth_unconditional (I := I) (M := M) g r s i)
        ≤ ENNReal.ofReal (C * (i.fst.val)⁻¹ ^ (2 * k + 1)) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec_ofCompact
                (I := I) (M := M)
                (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                  g r s) i‖)
    (c : TensorEigenIdx (I := I) (M := M) g r s → ℝ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    wtwokTwoNorm (I := I) (M := M) g k
        (c i • eigenvectorSmooth_unconditional (I := I) (M := M) g r s i)
      ≤ ENNReal.ofReal |c i| *
          ENNReal.ofReal (C * (i.fst.val)⁻¹ ^ (2 * k + 1)) := by
  have h_mem : MemWtwokTwo (I := I) (M := M) g k
      (eigenvectorSmooth_unconditional (I := I) (M := M) g r s i) :=
    tensorEigenvector_memWtwokTwo_unconditional (I := I) (M := M) g r s i k
  have h_smul := wtwokTwoNorm_smul (I := I) (M := M) g (c i) h_mem
  rw [h_smul]
  rw [Real.enorm_eq_ofReal_abs]
  have h_vec_norm :
      ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
        (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
          g r s) i‖ = 1 :=
    (tensorResolventEigenbasisVec_ofCompact_orthonormal (I := I) (M := M)
      (g := g) (r := r) (s := s)
      (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
        g r s)).norm_eq_one i
  have h_bd : wtwokTwoNorm (I := I) (M := M) g k
        (eigenvectorSmooth_unconditional (I := I) (M := M) g r s i)
      ≤ ENNReal.ofReal (C * (i.fst.val)⁻¹ ^ (2 * k + 1)) := by
    have h := hC_bound i
    rw [h_vec_norm, ENNReal.ofReal_one, mul_one] at h
    exact h
  exact mul_le_mul_of_nonneg_left h_bd (zero_le _)

/-- Chart-locality-free twin of `partialSum_wtwokTwoNorm_le_sum`. -/
private lemma partialSum_wtwokTwoNorm_le_sum_unconditional
    {C : ℝ} (hC_nn : 0 ≤ C)
    (hC_bound : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      wtwokTwoNorm (I := I) (M := M) g k
          (eigenvectorSmooth_unconditional (I := I) (M := M) g r s i)
        ≤ ENNReal.ofReal (C * (i.fst.val)⁻¹ ^ (2 * k + 1)) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec_ofCompact
                (I := I) (M := M)
                (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
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
          (c j • eigenvectorSmooth_unconditional (I := I) (M := M) g r s j) :=
        MemWtwokTwo_smul (I := I) (M := M) g (c j)
          (tensorEigenvector_memWtwokTwo_unconditional
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

/-- Chart-locality-free twin of `tensorHsSmoothRepr_wtwokTwoNorm_le_uniform`. -/
theorem tensorHsSmoothRepr_wtwokTwoNorm_le_uniform_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {σ : ℝ} (T : tensorHs (I := I) (M := M) g r s σ)
        (hT_fs : (Function.support T.coeff).Finite),
        wtwokTwoNorm (I := I) (M := M) g k
            (tensorHsSmoothRepr_unconditional (I := I) (M := M) T hT_fs)
          ≤ ENNReal.ofReal C *
              ENNReal.ofReal (∑ i ∈ hT_fs.toFinset,
                |T.coeff i| * (i.fst.val)⁻¹ ^ (2 * k + 1)) := by
  classical
  obtain ⟨C, hC_nn, hC_bound⟩ :=
    eigenvectorSmooth_wtwokTwoNorm_le_uniform_unconditional
      (I := I) (M := M) g r s k
  refine ⟨C, hC_nn, ?_⟩
  intro σ T hT_fs
  unfold tensorHsSmoothRepr_unconditional
  refine le_trans
    (TensorHsSmoothReprAux.partialSum_wtwokTwoNorm_le_sum_unconditional
      (I := I) (M := M) g r s k hC_nn hC_bound hT_fs.toFinset T.coeff)
    ?_
  have h_eigval_inv_one_le :
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s, (1 : ℝ) ≤ (i.fst.val)⁻¹ :=
    fun i => sharpDiff_eigen_inv_one_le_unconditional (I := I) (M := M) g r s i
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
