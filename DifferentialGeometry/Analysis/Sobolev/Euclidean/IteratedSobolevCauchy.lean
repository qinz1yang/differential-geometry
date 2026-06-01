import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolev
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# Completeness of the iterated Euclidean Sobolev space `W^{k,p}`

For `1 < p < ∞` and an open set `Ω ⊆ EuclideanSpace ℝ (Fin d)`, the iterated
Sobolev predicate `MemWkp k p · Ω` is closed under `wkpNorm`-Cauchy convergence:
every Cauchy sequence has a `MemWkp k p · Ω` limit, and the convergence is in
`wkpNorm`.

The proof:

1. Each iterated weak partial of order `j ≤ k`, of a Cauchy sequence in
   `wkpNorm`, is `eLpNorm`-Cauchy on `Ω`.
2. By Mathlib's `MeasureTheory.Lp.cauchy_complete_eLpNorm`, each such sequence
   has a limit in `L^p(Ω)`.
3. The limits at successive orders are weak partials of one another, by the
   integration-by-parts duality `HasWeakPartialDeriv.of_eLpNormApprox_p`.
4. Hence the order-`0` limit is in `MemWkp k p · Ω`, with iterated weak partials
   given by the limits at higher orders.
5. The convergence in `wkpNorm` is the sum of `eLpNorm` convergence over all
   `(j, β)` pairs.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Euclidean

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The `wkpNorm` is dominated termwise by the sum over `(j, β)` of `eLpNorm`s of
iterated weak partials. In particular, for any fixed `(j₀, β₀)` with `j₀ ≤ k`,
the `eLpNorm` of the order-`j₀` weak partial is bounded by the `wkpNorm`. -/
theorem eLpNorm_iterWeakPartial_le_wkpNorm
    {k : ℕ} (p : ℝ≥0∞) (u : E → ℝ) (Ω : Set E)
    (j₀ : ℕ) (hj₀ : j₀ ≤ k) (β₀ : Fin j₀ → Fin d) :
    eLpNorm (iterWeakPartial (d := d) p j₀ β₀ u Ω) p (volume.restrict Ω) ≤
      wkpNorm (d := d) k p u Ω := by
  classical
  unfold wkpNorm
  have h_inner :
      eLpNorm (iterWeakPartial (d := d) p j₀ β₀ u Ω) p (volume.restrict Ω) ≤
        ∑ β : Fin j₀ → Fin d,
          eLpNorm (iterWeakPartial (d := d) p j₀ β u Ω) p (volume.restrict Ω) :=
    Finset.single_le_sum
      (f := fun β : Fin j₀ → Fin d =>
        eLpNorm (iterWeakPartial (d := d) p j₀ β u Ω) p (volume.restrict Ω))
      (s := (Finset.univ : Finset (Fin j₀ → Fin d)))
      (fun _ _ => zero_le _) (Finset.mem_univ _)
  have h_outer :
      (∑ β : Fin j₀ → Fin d,
        eLpNorm (iterWeakPartial (d := d) p j₀ β u Ω) p (volume.restrict Ω)) ≤
      ∑ j ∈ Finset.range (k + 1),
        ∑ β : Fin j → Fin d,
          eLpNorm (iterWeakPartial (d := d) p j β u Ω) p (volume.restrict Ω) := by
    refine Finset.single_le_sum
      (f := fun j : ℕ =>
        ∑ β : Fin j → Fin d,
          eLpNorm (iterWeakPartial (d := d) p j β u Ω) p (volume.restrict Ω))
      (s := Finset.range (k + 1))
      (fun _ _ => zero_le _) ?_
    rw [Finset.mem_range]
    omega
  exact le_trans h_inner h_outer

/-- For a sequence `(u n)` whose `wkpNorm` differences are bounded by a summable
`B N`, every iterated weak partial of order `j ≤ k` is `eLpNorm`-Cauchy with the
same bound. -/
theorem iterWeakPartial_cauchy_of_wkpNorm_cauchy
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    {Ω : Set E} (hΩ : IsOpen Ω)
    {u : ℕ → E → ℝ}
    (hu : ∀ n, MemWkp (d := d) k p (u n) Ω)
    {B : ℕ → ℝ≥0∞}
    (h_cau : ∀ N n m, N ≤ n → N ≤ m →
      wkpNorm (d := d) k p (fun x => u n x - u m x) Ω < B N)
    {j : ℕ} (hj : j ≤ k) (β : Fin j → Fin d) :
    ∀ N n m, N ≤ n → N ≤ m →
      eLpNorm
        (fun x => iterWeakPartial (d := d) p j β (u n) Ω x -
          iterWeakPartial (d := d) p j β (u m) Ω x)
        p (volume.restrict Ω) < B N := by
  intro N n m hn hm
  have h_bound := h_cau N n m hn hm
  have h_iter_le := eLpNorm_iterWeakPartial_le_wkpNorm
    (d := d) (k := k) (p := p)
    (u := fun x => u n x - u m x) (Ω := Ω) j hj β
  have h_uW : MemWkp (d := d) j p (u n) Ω := MemWkp.le_of_le hj (hu n)
  have h_vW : MemWkp (d := d) j p (u m) Ω := MemWkp.le_of_le hj (hu m)
  have h_iter_sub_ae :=
    iterWeakPartial_add_ae (d := d) hp hΩ β h_uW (MemWkp.neg (d := d) hp hΩ h_vW)
  have h_iter_neg_ae := iterWeakPartial_const_smul_ae
    (d := d) hp hΩ β h_vW (-1)
  have h_iter_sub : iterWeakPartial (d := d) p j β (fun x => u n x - u m x) Ω
      =ᵐ[volume.restrict Ω]
      (fun x => iterWeakPartial (d := d) p j β (u n) Ω x -
        iterWeakPartial (d := d) p j β (u m) Ω x) := by
    have h_eq_un_sub : (fun x => u n x - u m x) = (fun x => u n x + (-1) * u m x) := by
      funext x; ring
    rw [h_eq_un_sub]
    have h_neg_uW : MemWkp (d := d) j p (fun x => (-1 : ℝ) * u m x) Ω :=
      MemWkp.const_smul (d := d) hp hΩ h_vW (-1)
    have h_iter_add :=
      iterWeakPartial_add_ae (d := d) hp hΩ β h_uW h_neg_uW
    refine h_iter_add.trans ?_
    have h_iter_smul := iterWeakPartial_const_smul_ae
      (d := d) hp hΩ β h_vW (-1)
    filter_upwards [h_iter_smul] with x hx
    rw [hx]
    ring
  rw [eLpNorm_congr_ae h_iter_sub] at h_iter_le
  exact lt_of_le_of_lt h_iter_le h_bound

/-- For `1 ≤ p`, every Cauchy sequence in `wkpNorm` has an `eLpNorm`-limit
of every iterated weak partial of order `j ≤ k`, and the limit is in `MemLp`. -/
theorem exists_eLpNorm_limit_iterWeakPartial
    {k : ℕ} {p : ℝ≥0∞} (hp_one : 1 ≤ p)
    {Ω : Set E} (hΩ : IsOpen Ω)
    {u : ℕ → E → ℝ}
    (hu : ∀ n, MemWkp (d := d) k p (u n) Ω)
    {B : ℕ → ℝ≥0∞} (hB : ∑' i, B i ≠ ∞)
    (h_cau : ∀ N n m, N ≤ n → N ≤ m →
      wkpNorm (d := d) k p (fun x => u n x - u m x) Ω < B N)
    {j : ℕ} (hj : j ≤ k) (β : Fin j → Fin d) :
    ∃ (v : E → ℝ), MemLp v p (volume.restrict Ω) ∧
      atTop.Tendsto
        (fun n => eLpNorm
          (fun x => iterWeakPartial (d := d) p j β (u n) Ω x - v x)
          p (volume.restrict Ω))
        (𝓝 0) := by
  classical
  have h_iter_memLp : ∀ n,
      MemLp (iterWeakPartial (d := d) p j β (u n) Ω) p (volume.restrict Ω) := by
    intro n
    have h_uWj : MemWkp (d := d) j p (u n) Ω := MemWkp.le_of_le hj (hu n)
    exact iterWeakPartial_memLp_of_memWkp (d := d) (p := p) h_uWj β
  have h_iter_cau :=
    iterWeakPartial_cauchy_of_wkpNorm_cauchy (d := d) hp_one hΩ hu h_cau hj β
  have h_iter_cau' : ∀ N n m : ℕ, N ≤ n → N ≤ m →
      eLpNorm
        ((fun n => iterWeakPartial (d := d) p j β (u n) Ω) n -
          (fun n => iterWeakPartial (d := d) p j β (u n) Ω) m)
        p (volume.restrict Ω) < B N := by
    intro N n m hn hm
    have h := h_iter_cau N n m hn hm
    have hEq :
        ((fun n => iterWeakPartial (d := d) p j β (u n) Ω) n -
          (fun n => iterWeakPartial (d := d) p j β (u n) Ω) m) =
        fun x => iterWeakPartial (d := d) p j β (u n) Ω x -
          iterWeakPartial (d := d) p j β (u m) Ω x := by
      funext x
      simp [Pi.sub_apply]
    rw [hEq]
    exact h
  rcases MeasureTheory.Lp.cauchy_complete_eLpNorm
      (μ := volume.restrict Ω) hp_one h_iter_memLp hB h_iter_cau'
      with ⟨v, hv_memLp, hv_tendsto⟩
  refine ⟨v, hv_memLp, ?_⟩
  have hEq : (fun n => eLpNorm
        ((fun n => iterWeakPartial (d := d) p j β (u n) Ω) n - v)
        p (volume.restrict Ω)) =
      (fun n => eLpNorm
        (fun x => iterWeakPartial (d := d) p j β (u n) Ω x - v x)
        p (volume.restrict Ω)) := by
    funext n
    rfl
  rw [hEq] at hv_tendsto
  exact hv_tendsto

end Euclidean
end Sobolev
end Analysis
end DifferentialGeometry
