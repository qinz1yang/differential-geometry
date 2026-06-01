import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization.SpectralChartRegularityGeneral

/-!
# Eigenvalue-tail summability from a polynomial counting bound

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` modelled
on a finite-dimensional real inner-product space `E`, the predicate
`EigenvalueTailSummable g r s` asks for *some* exponent `p > 0` making the family
`i ↦ (1 + λᵢ)^{-p}` over the tensor eigen-index set summable.

This file provides the **counting → summability** converter: the standard
real-analytic fact that a polynomial bound on the eigenvalue-counting function
`N(Λ) = #{i : 1 + λᵢ < Λ}` forces eigenvalue-tail summability. Concretely, if for
every dyadic threshold `2^{n+1}` the shell `{i : 1 + λᵢ < 2^{n+1}}` is contained
in a finite family of cardinality at most `A · 2^{(n+1)·q}`, then `i ↦ (1 + λᵢ)^{-p}`
is summable at the explicit exponent `p = q + 2 > 0`.

The argument is the textbook dyadic decomposition. Partition the index set by the
shell index `m(i) = ⌊log₂ ⌊1 + λᵢ⌋⌋`, so that `2^{m(i)} ≤ 1 + λᵢ < 2^{m(i)+1}`.
On shell `m` the summand is bounded by `2^{-m·p}`, the shell has at most `A·2^{(m+1)q}`
elements (by the counting hypothesis, since membership in the shell forces `1 + λᵢ`
below `2^{m+1}`), so the shell contributes at most `A·2^q·2^{-2m}`, and summing the
geometric series in `m` gives a uniform bound on every finite partial sum. The
conclusion follows from `summable_of_sum_le`.

This isolates the purely analytic counting → summability step from the geometric
local-Weyl counting bound itself (the local reproducing-kernel diagonal estimate),
which is supplied separately.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

/-- **Dyadic counting ⟹ summability.**

Let `w : ι → ℝ` with `w i ≥ 1`. Suppose there is a family of finsets `count n`
such that every index with `w i < 2^{n+1}` lies in `count n`, and
`#(count n) ≤ A · 2^{(n+1)·q}` (a polynomial-in-`2^n` counting bound of degree
`q`). Then `i ↦ (w i)^{-(q+2)}` is summable.

This is the standard "Weyl counting ⟹ Schatten" step: a polynomial bound of degree
`q` on the dyadic counting function forces summability of `(w i)^{-p}` for the
explicit exponent `p = q + 2`. -/
theorem counting_summable_dyadic {ι : Type*} (w : ι → ℝ) (hw : ∀ i, 1 ≤ w i)
    (q : ℕ) (A : ℝ) (hA : 0 ≤ A)
    (count : ℕ → Finset ι)
    (hcount_mem : ∀ (n : ℕ) (i : ι), w i < 2 ^ (n + 1) → i ∈ count n)
    (hcount_card : ∀ n : ℕ, ((count n).card : ℝ) ≤ A * 2 ^ ((n + 1) * q)) :
    Summable (fun i => (w i) ^ (-((q : ℝ) + 2))) := by
  classical
  set p : ℝ := (q : ℝ) + 2 with hp_def
  have hp_nn : (0 : ℝ) ≤ p := by rw [hp_def]; positivity
  set f : ι → ℝ := fun i => (w i) ^ (-p) with hf_def
  set shell : ι → ℕ := fun i => Nat.log 2 ⌊w i⌋₊ with hshell_def
  have hwpos : ∀ i, 0 < w i := fun i => lt_of_lt_of_le one_pos (hw i)
  have hwnn : ∀ i, 0 ≤ w i := fun i => (hwpos i).le
  have hfloor1 : ∀ i, 1 ≤ ⌊w i⌋₊ := fun i => (Nat.one_le_floor_iff (w i)).mpr (hw i)
  have h_lower : ∀ i, (2 : ℝ) ^ (shell i) ≤ w i := by
    intro i
    have h1 : 2 ^ (shell i) ≤ ⌊w i⌋₊ :=
      Nat.pow_log_le_self 2 (Nat.one_le_iff_ne_zero.mp (hfloor1 i))
    calc (2 : ℝ) ^ (shell i) = ((2 ^ (shell i) : ℕ) : ℝ) := by push_cast; ring
      _ ≤ (⌊w i⌋₊ : ℝ) := by exact_mod_cast h1
      _ ≤ w i := Nat.floor_le (hwnn i)
  have h_upper : ∀ i, w i < 2 ^ (shell i + 1) := by
    intro i
    have h0 : ⌊w i⌋₊ < 2 ^ (shell i + 1) :=
      Nat.lt_pow_succ_log_self one_lt_two ⌊w i⌋₊
    have h1 : ⌊w i⌋₊ + 1 ≤ 2 ^ (shell i + 1) := Nat.succ_le_of_lt h0
    have h2 : w i < (⌊w i⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one (w i)
    have h3 : (⌊w i⌋₊ : ℝ) + 1 ≤ (2 : ℝ) ^ (shell i + 1) := by
      calc (⌊w i⌋₊ : ℝ) + 1 = ((⌊w i⌋₊ + 1 : ℕ) : ℝ) := by push_cast; ring
        _ ≤ ((2 ^ (shell i + 1) : ℕ) : ℝ) := by exact_mod_cast h1
        _ = (2 : ℝ) ^ (shell i + 1) := by push_cast; ring
    linarith
  have h_mem_count : ∀ i, i ∈ count (shell i) := fun i => hcount_mem (shell i) i (h_upper i)
  have hf_nn : ∀ i, 0 ≤ f i := fun i => Real.rpow_nonneg (hwnn i) _
  have hf_le : ∀ i, f i ≤ (2 : ℝ) ^ (-(shell i : ℝ) * p) := by
    intro i
    rw [hf_def]
    have h2pos : (0 : ℝ) < (2 : ℝ) ^ (shell i) := by positivity
    have hstep : (w i) ^ (-p) ≤ ((2 : ℝ) ^ (shell i)) ^ (-p) :=
      Real.rpow_le_rpow_of_nonpos h2pos (h_lower i) (neg_nonpos.mpr hp_nn)
    refine hstep.trans (le_of_eq ?_)
    rw [← Real.rpow_natCast (2 : ℝ) (shell i),
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    ring_nf
  set g : ℕ → ℝ := fun m => A * 2 ^ q * (2 : ℝ) ^ (-(2 : ℝ) * m) with hg_def
  have hsummand_eq : (fun m : ℕ => (2 : ℝ) ^ (-(2 : ℝ) * m)) = fun m : ℕ => ((1 : ℝ) / 4) ^ m := by
    funext m
    have hbase : (2 : ℝ) ^ (-(2 : ℝ)) = (1 : ℝ) / 4 := by
      rw [show (-(2 : ℝ)) = -((2 : ℕ) : ℝ) by norm_num,
        Real.rpow_neg (by norm_num), Real.rpow_natCast]
      norm_num
    rw [show (-(2 : ℝ) * (m : ℝ)) = ((m : ℝ) * (-(2 : ℝ))) by ring,
      Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have h2m_pos : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
    rw [show (-(2 : ℝ)) = -((2 : ℕ) : ℝ) by norm_num,
      Real.rpow_neg h2m_pos.le, Real.rpow_natCast]
    rw [← pow_mul, mul_comm m 2, pow_mul, ← inv_pow]
    norm_num
  have hbase_summable : Summable (fun m : ℕ => (2 : ℝ) ^ (-(2 : ℝ) * m)) := by
    rw [hsummand_eq]
    exact summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hg_summable : Summable g := hbase_summable.mul_left (A * 2 ^ q)
  have hg_nn : ∀ m, 0 ≤ g m := fun m => by rw [hg_def]; positivity
  refine summable_of_sum_le (c := ∑' m, g m) hf_nn (fun u => ?_)
  have hpartition :
      ∑ m ∈ u.image shell, ∑ i ∈ u with shell i = m, f i = ∑ i ∈ u, f i :=
    Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem shell hi) f
  rw [← hpartition]
  have hfiber : ∀ m ∈ u.image shell,
      ∑ i ∈ u with shell i = m, f i ≤ g m := by
    intro m _hm
    have hbound_each : ∀ i ∈ u.filter (fun i => shell i = m),
        f i ≤ (2 : ℝ) ^ (-(m : ℝ) * p) := by
      intro i hi
      have hsi : shell i = m := (Finset.mem_filter.mp hi).2
      have := hf_le i
      rwa [hsi] at this
    have hcard_le :
        (u.filter (fun i => shell i = m)).card ≤ (count m).card := by
      apply Finset.card_le_card
      intro i hi
      have hsi : shell i = m := (Finset.mem_filter.mp hi).2
      have := h_mem_count i
      rwa [hsi] at this
    calc ∑ i ∈ u with shell i = m, f i
        ≤ ∑ _i ∈ u.filter (fun i => shell i = m), (2 : ℝ) ^ (-(m : ℝ) * p) :=
          Finset.sum_le_sum hbound_each
      _ = ((u.filter (fun i => shell i = m)).card : ℝ) * (2 : ℝ) ^ (-(m : ℝ) * p) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((count m).card : ℝ) * (2 : ℝ) ^ (-(m : ℝ) * p) := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by norm_num) _)
          exact_mod_cast hcard_le
      _ ≤ (A * 2 ^ ((m + 1) * q)) * (2 : ℝ) ^ (-(m : ℝ) * p) := by
          apply mul_le_mul_of_nonneg_right (hcount_card m)
            (Real.rpow_nonneg (by norm_num) _)
      _ = g m := by
          simp only [hg_def, hp_def]
          have h2pos : (0:ℝ) < 2 := by norm_num
          have h2q : (2 : ℝ) ^ ((m + 1) * q) = (2 : ℝ) ^ (((m : ℝ) * q + q) : ℝ) := by
            rw [← Real.rpow_natCast (2 : ℝ) ((m + 1) * q)]
            congr 1
            push_cast
            ring
          have h2qcast : (2 : ℝ) ^ q = (2 : ℝ) ^ ((q : ℝ)) := (Real.rpow_natCast 2 q).symm
          have hexpL : ((m : ℝ) * q + q) + (-(m : ℝ) * (q + 2)) = (q : ℝ) + (-2 * (m : ℝ)) := by
            ring
          rw [h2q, h2qcast, mul_assoc A, mul_assoc A,
            ← Real.rpow_add h2pos, ← Real.rpow_add h2pos, hexpL]
  refine (Finset.sum_le_sum hfiber).trans ?_
  exact hg_summable.sum_le_tsum _ (fun m _ => hg_nn m)

open MetricRealization
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- A polynomial dyadic counting bound on the tensor Laplacian spectrum gives
`EigenvalueTailSummable g r s`.

The hypotheses say that for every `n` the dyadic shell `{i : 1 + λᵢ < 2^{n+1}}` is
contained in a finite family `count n` with `#(count n) ≤ A · 2^{(n+1)·q}` (with
`A ≥ 0`). The conclusion is the existential predicate `EigenvalueTailSummable g r s`,
which is realized here at the explicit exponent `p = q + 2 > 0`: the family
`i ↦ (1 + λᵢ)^{-(q+2)}` is summable.

This is the geometric specialization of the abstract dyadic converter
`counting_summable_dyadic` to the tensor eigen-index set, taking the weight
`w i = 1 + λᵢ ≥ 1` (using `tensor_lambda_nonneg`). It supplies the Schatten-type
eigenvalue-tail summability that the spectral smooth-representative gate consumes;
the polynomial counting bound itself (a local Weyl law) is provided separately. -/
theorem eigenvalueTailSummable_of_polynomial_counting_bound
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (q : ℕ) (A : ℝ) (hA : 0 ≤ A)
    (count : ℕ → Finset (TensorSpectral.TensorEigenIdx (I := I) (M := M) g r s))
    (hcount_mem : ∀ (n : ℕ) (i : TensorSpectral.TensorEigenIdx (I := I) (M := M) g r s),
      1 + TensorEigenIdx.lambda (I := I) (M := M) i < 2 ^ (n + 1) → i ∈ count n)
    (hcount_card : ∀ n : ℕ, ((count n).card : ℝ) ≤ A * 2 ^ ((n + 1) * q)) :
    EigenvalueTailSummable (I := I) (M := M) g r s := by
  refine ⟨(q : ℝ) + 2, by positivity, ?_⟩
  have hw : ∀ i : TensorSpectral.TensorEigenIdx (I := I) (M := M) g r s,
      (1 : ℝ) ≤ 1 + TensorEigenIdx.lambda (I := I) (M := M) i := by
    intro i
    have := tensor_lambda_nonneg (I := I) (M := M) i
    linarith
  exact counting_summable_dyadic
    (fun i => 1 + TensorEigenIdx.lambda (I := I) (M := M) i) hw q A hA count
    hcount_mem hcount_card

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
