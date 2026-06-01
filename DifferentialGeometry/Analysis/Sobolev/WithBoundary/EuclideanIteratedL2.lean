import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedL2
import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolevHalfSpace

/-!
# `L²`-convention iterated Euclidean Sobolev norm and inner product on
half-space-friendly domains

This module is the half-space-friendly parallel of
`Analysis/Sobolev/EuclideanIteratedL2.lean`. Given a half-space-friendly
carrier `Ω ⊆ E` (an open subset of `E` intersected with the closed
half-space `{y | 0 ≤ y 0}`), we define the *Dirichlet (zero-trace)*
`L²`-convention norm and inner product

  `‖u‖_{W^{k,2}_0(Ω)}² = ∑_{|β| ≤ k} ‖∂^β u‖²_{L²(interiorHalfSpace Ω)}`

  `⟨u, v⟩_{W^{k,2}_0(Ω)} = ∑_{|β| ≤ k} ∫_{interiorHalfSpace Ω}
        (∂^β u)(∂^β v) dx`,

i.e., the boundaryless `wkpNormL2 / wkpInnerL2` evaluated on the open
*interior part* `interiorHalfSpace Ω = Ω ∩ {y | 0 < y 0}`. This is the
zero-trace variant: weak partials are tested against test functions whose
support is strictly inside `interiorHalfSpace Ω`, and consequently
cannot reach the boundary hyperplane.

All structural results — finiteness, ae-invariance, scalar homogeneity,
triangle inequality, equivalence with the linear-sum
`wkpNormHalfSpace k 2 u Ω` — are direct reductions to the corresponding
boundaryless lemmas on `interiorHalfSpace Ω`.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal RealInnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Euclidean

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The squared `L²`-convention Sobolev norm on a half-space-friendly
domain `Ω`: the boundaryless `L²`-Sobolev squared norm evaluated on the
open interior part `interiorHalfSpace Ω`. -/
def wkpNormL2SqHalfSpace (k : ℕ) (u : E → ℝ) (Ω : Set E) : ℝ≥0∞ :=
  wkpNormL2Sq (d := d) k u (interiorHalfSpace Ω)

/-- The `L²`-convention Sobolev norm on a half-space-friendly domain `Ω`:
the boundaryless `L²`-Sobolev norm evaluated on the open interior part
`interiorHalfSpace Ω`. -/
def wkpNormL2HalfSpace (k : ℕ) (u : E → ℝ) (Ω : Set E) : ℝ≥0∞ :=
  wkpNormL2 (d := d) k u (interiorHalfSpace Ω)

@[simp] lemma wkpNormL2SqHalfSpace_def
    (k : ℕ) (u : E → ℝ) (Ω : Set E) :
    wkpNormL2SqHalfSpace (d := d) k u Ω =
      wkpNormL2Sq (d := d) k u (interiorHalfSpace Ω) := rfl

@[simp] lemma wkpNormL2HalfSpace_def
    (k : ℕ) (u : E → ℝ) (Ω : Set E) :
    wkpNormL2HalfSpace (d := d) k u Ω =
      wkpNormL2 (d := d) k u (interiorHalfSpace Ω) := rfl

/-- The half-space `L²`-Sobolev norm equals the rpow of the squared norm
by `1/2`. -/
theorem wkpNormL2HalfSpace_eq_rpow
    (k : ℕ) (u : E → ℝ) (Ω : Set E) :
    wkpNormL2HalfSpace (d := d) k u Ω =
      wkpNormL2SqHalfSpace (d := d) k u Ω ^ ((1 : ℝ) / 2) := by
  unfold wkpNormL2HalfSpace wkpNormL2SqHalfSpace
  exact wkpNormL2_eq_rpow (d := d) k u (interiorHalfSpace Ω)

/-- The `L²`-convention Sobolev inner product on a half-space-friendly
domain `Ω`: the boundaryless `L²`-Sobolev inner product evaluated on the
open interior part `interiorHalfSpace Ω`. -/
def wkpInnerL2HalfSpace (k : ℕ) (u v : E → ℝ) (Ω : Set E) : ℝ :=
  wkpInnerL2 (d := d) k u v (interiorHalfSpace Ω)

@[simp] lemma wkpInnerL2HalfSpace_def
    (k : ℕ) (u v : E → ℝ) (Ω : Set E) :
    wkpInnerL2HalfSpace (d := d) k u v Ω =
      wkpInnerL2 (d := d) k u v (interiorHalfSpace Ω) := rfl

/-- `wkpNormL2SqHalfSpace 0 u Ω = (eLpNorm u 2)²` on the interior part. -/
theorem wkpNormL2SqHalfSpace_zero
    (u : E → ℝ) (Ω : Set E) :
    wkpNormL2SqHalfSpace (d := d) 0 u Ω =
      eLpNorm u 2 ((volume : Measure E).restrict (interiorHalfSpace Ω)) ^ (2 : ℕ) := by
  unfold wkpNormL2SqHalfSpace
  exact wkpNormL2Sq_zero (d := d) u (interiorHalfSpace Ω)

/-- `wkpNormL2SqHalfSpace k 0 Ω = 0` for half-space-friendly `Ω`. -/
theorem wkpNormL2SqHalfSpace_zero_fun_zero
    {k : ℕ} {Ω : Set E} (hΩ : IsHalfSpaceRelOpen (d := d) Ω) :
    wkpNormL2SqHalfSpace (d := d) k (fun _ : E => (0 : ℝ)) Ω = 0 := by
  unfold wkpNormL2SqHalfSpace
  exact wkpNormL2Sq_zero_fun_zero (d := d) (interiorHalfSpace_isOpen hΩ)

/-- `wkpNormL2HalfSpace k 0 Ω = 0` for half-space-friendly `Ω`. -/
theorem wkpNormL2HalfSpace_zero_fun_zero
    {k : ℕ} {Ω : Set E} (hΩ : IsHalfSpaceRelOpen (d := d) Ω) :
    wkpNormL2HalfSpace (d := d) k (fun _ : E => (0 : ℝ)) Ω = 0 := by
  unfold wkpNormL2HalfSpace
  exact wkpNormL2_zero_fun_zero (d := d) (interiorHalfSpace_isOpen hΩ)

/-- For `u ∈ W^{k,2}_0(Ω)`, the squared `L²`-Sobolev norm is finite. -/
theorem wkpNormL2SqHalfSpace_lt_top_of_memWkpHalfSpace
    {k : ℕ} {u : E → ℝ} {Ω : Set E}
    (h : MemWkpHalfSpace (d := d) k 2 u Ω) :
    wkpNormL2SqHalfSpace (d := d) k u Ω < ∞ := by
  unfold wkpNormL2SqHalfSpace
  exact wkpNormL2Sq_lt_top_of_memWkp (d := d) h

/-- For `u ∈ W^{k,2}_0(Ω)`, the `L²`-Sobolev norm is finite. -/
theorem wkpNormL2HalfSpace_lt_top_of_memWkpHalfSpace
    {k : ℕ} {u : E → ℝ} {Ω : Set E}
    (h : MemWkpHalfSpace (d := d) k 2 u Ω) :
    wkpNormL2HalfSpace (d := d) k u Ω < ∞ := by
  unfold wkpNormL2HalfSpace
  exact wkpNormL2_lt_top_of_memWkp (d := d) h

/-- `wkpNormL2SqHalfSpace` is invariant under ae-equality on the interior
part. -/
theorem wkpNormL2SqHalfSpace_congr_ae
    {k : ℕ} {Ω : Set E} (hΩ : IsHalfSpaceRelOpen (d := d) Ω)
    {u v : E → ℝ}
    (huv : u =ᵐ[(volume : Measure E).restrict (interiorHalfSpace Ω)] v) :
    wkpNormL2SqHalfSpace (d := d) k u Ω =
      wkpNormL2SqHalfSpace (d := d) k v Ω := by
  unfold wkpNormL2SqHalfSpace
  exact wkpNormL2Sq_congr_ae (d := d) (interiorHalfSpace_isOpen hΩ) huv

/-- `wkpNormL2HalfSpace` is invariant under ae-equality on the interior
part. -/
theorem wkpNormL2HalfSpace_congr_ae
    {k : ℕ} {Ω : Set E} (hΩ : IsHalfSpaceRelOpen (d := d) Ω)
    {u v : E → ℝ}
    (huv : u =ᵐ[(volume : Measure E).restrict (interiorHalfSpace Ω)] v) :
    wkpNormL2HalfSpace (d := d) k u Ω =
      wkpNormL2HalfSpace (d := d) k v Ω := by
  unfold wkpNormL2HalfSpace
  exact wkpNormL2_congr_ae (d := d) (interiorHalfSpace_isOpen hΩ) huv

/-- ae-invariance form using ae-equality on the carrier. -/
theorem wkpNormL2SqHalfSpace_congr_ae_of_carrier
    {k : ℕ} {Ω : Set E} (hΩ : IsHalfSpaceRelOpen (d := d) Ω)
    {u v : E → ℝ}
    (huv : u =ᵐ[(volume : Measure E).restrict Ω] v) :
    wkpNormL2SqHalfSpace (d := d) k u Ω =
      wkpNormL2SqHalfSpace (d := d) k v Ω := by
  rw [volume_restrict_interiorHalfSpace_eq hΩ] at huv
  exact wkpNormL2SqHalfSpace_congr_ae (d := d) hΩ huv

/-- ae-invariance form using ae-equality on the carrier. -/
theorem wkpNormL2HalfSpace_congr_ae_of_carrier
    {k : ℕ} {Ω : Set E} (hΩ : IsHalfSpaceRelOpen (d := d) Ω)
    {u v : E → ℝ}
    (huv : u =ᵐ[(volume : Measure E).restrict Ω] v) :
    wkpNormL2HalfSpace (d := d) k u Ω =
      wkpNormL2HalfSpace (d := d) k v Ω := by
  rw [volume_restrict_interiorHalfSpace_eq hΩ] at huv
  exact wkpNormL2HalfSpace_congr_ae (d := d) hΩ huv

/-- Squaring `wkpNormL2HalfSpace` recovers `wkpNormL2SqHalfSpace`. -/
theorem wkpNormL2HalfSpace_sq_eq_wkpNormL2SqHalfSpace
    (k : ℕ) (u : E → ℝ) (Ω : Set E) :
    wkpNormL2HalfSpace (d := d) k u Ω ^ (2 : ℕ) =
      wkpNormL2SqHalfSpace (d := d) k u Ω := by
  unfold wkpNormL2HalfSpace wkpNormL2SqHalfSpace
  exact wkpNormL2_sq_eq_wkpNormL2Sq (d := d) k u (interiorHalfSpace Ω)

/-- The triangle inequality for `wkpNormL2HalfSpace`. -/
theorem wkpNormL2HalfSpace_add_le
    {k : ℕ} {Ω : Set E} (hΩ : IsHalfSpaceRelOpen (d := d) Ω)
    {u v : E → ℝ}
    (hu : MemWkpHalfSpace (d := d) k 2 u Ω)
    (hv : MemWkpHalfSpace (d := d) k 2 v Ω) :
    wkpNormL2HalfSpace (d := d) k (fun x => u x + v x) Ω ≤
      wkpNormL2HalfSpace (d := d) k u Ω +
        wkpNormL2HalfSpace (d := d) k v Ω := by
  unfold wkpNormL2HalfSpace
  exact wkpNormL2_add_le (d := d) (interiorHalfSpace_isOpen hΩ) hu hv

/-- Scalar multiplication identity for `wkpNormL2SqHalfSpace`. -/
theorem wkpNormL2SqHalfSpace_const_smul
    {k : ℕ} {Ω : Set E} (hΩ : IsHalfSpaceRelOpen (d := d) Ω)
    {u : E → ℝ} (hu : MemWkpHalfSpace (d := d) k 2 u Ω) (c : ℝ) :
    wkpNormL2SqHalfSpace (d := d) k (fun x => c * u x) Ω =
      ‖c‖ₑ ^ (2 : ℕ) * wkpNormL2SqHalfSpace (d := d) k u Ω := by
  unfold wkpNormL2SqHalfSpace
  exact wkpNormL2Sq_const_smul (d := d) (interiorHalfSpace_isOpen hΩ) hu c

/-- Scalar multiplication identity for `wkpNormL2HalfSpace`. -/
theorem wkpNormL2HalfSpace_const_smul
    {k : ℕ} {Ω : Set E} (hΩ : IsHalfSpaceRelOpen (d := d) Ω)
    {u : E → ℝ} (hu : MemWkpHalfSpace (d := d) k 2 u Ω) (c : ℝ) :
    wkpNormL2HalfSpace (d := d) k (fun x => c * u x) Ω =
      ‖c‖ₑ * wkpNormL2HalfSpace (d := d) k u Ω := by
  unfold wkpNormL2HalfSpace
  exact wkpNormL2_const_smul (d := d) (interiorHalfSpace_isOpen hΩ) hu c

/-- `wkpNormL2HalfSpace ≤ wkpNormHalfSpace` at `p = 2`, the Euclidean
side dominates the linear-sum side from below. -/
theorem wkpNormL2HalfSpace_le_wkpNormHalfSpace
    {k : ℕ} {u : E → ℝ} {Ω : Set E}
    (hu : MemWkpHalfSpace (d := d) k 2 u Ω) :
    wkpNormL2HalfSpace (d := d) k u Ω ≤
      wkpNormHalfSpace (d := d) k 2 u Ω := by
  unfold wkpNormL2HalfSpace wkpNormHalfSpace
  exact wkpNormL2_le_wkpNorm (d := d) hu

/-- `wkpNormHalfSpace ≤ √N · wkpNormL2HalfSpace` at `p = 2`. -/
theorem wkpNormHalfSpace_le_sqrt_card_mul_wkpNormL2HalfSpace
    {k : ℕ} {u : E → ℝ} {Ω : Set E}
    (hu : MemWkpHalfSpace (d := d) k 2 u Ω) :
    wkpNormHalfSpace (d := d) k 2 u Ω ≤
      ENNReal.ofReal (Real.sqrt (wkpIndexCardL2 k d)) *
        wkpNormL2HalfSpace (d := d) k u Ω := by
  unfold wkpNormL2HalfSpace wkpNormHalfSpace
  exact wkpNorm_le_sqrt_card_mul_wkpNormL2 (d := d) hu

/-- The `L²`-Sobolev half-space inner product is symmetric. -/
theorem wkpInnerL2HalfSpace_comm
    (k : ℕ) (u v : E → ℝ) (Ω : Set E) :
    wkpInnerL2HalfSpace (d := d) k u v Ω =
      wkpInnerL2HalfSpace (d := d) k v u Ω := by
  unfold wkpInnerL2HalfSpace
  exact wkpInnerL2_comm (d := d) k u v (interiorHalfSpace Ω)

/-- The `L²`-Sobolev half-space inner product is non-negative on the
diagonal. -/
theorem wkpInnerL2HalfSpace_self_nonneg
    (k : ℕ) (u : E → ℝ) (Ω : Set E) :
    0 ≤ wkpInnerL2HalfSpace (d := d) k u u Ω := by
  unfold wkpInnerL2HalfSpace
  exact wkpInnerL2_self_nonneg (d := d) k u (interiorHalfSpace Ω)

/-- Bilinearity (left additivity) of the half-space inner product. -/
theorem wkpInnerL2HalfSpace_add_left
    {k : ℕ} {Ω : Set E} (hΩ : IsHalfSpaceRelOpen (d := d) Ω)
    {u₁ u₂ v : E → ℝ}
    (hu₁ : MemWkpHalfSpace (d := d) k 2 u₁ Ω)
    (hu₂ : MemWkpHalfSpace (d := d) k 2 u₂ Ω)
    (hv : MemWkpHalfSpace (d := d) k 2 v Ω) :
    wkpInnerL2HalfSpace (d := d) k (fun x => u₁ x + u₂ x) v Ω =
      wkpInnerL2HalfSpace (d := d) k u₁ v Ω +
        wkpInnerL2HalfSpace (d := d) k u₂ v Ω := by
  unfold wkpInnerL2HalfSpace
  exact wkpInnerL2_add_left (d := d) (interiorHalfSpace_isOpen hΩ)
    hu₁ hu₂ hv

/-- Scalar-multiplication identity (left slot) of the half-space inner
product. -/
theorem wkpInnerL2HalfSpace_smul_left
    {k : ℕ} {Ω : Set E} (hΩ : IsHalfSpaceRelOpen (d := d) Ω)
    {u : E → ℝ} (v : E → ℝ)
    (hu : MemWkpHalfSpace (d := d) k 2 u Ω) (c : ℝ) :
    wkpInnerL2HalfSpace (d := d) k (fun x => c * u x) v Ω =
      c * wkpInnerL2HalfSpace (d := d) k u v Ω := by
  unfold wkpInnerL2HalfSpace
  exact wkpInnerL2_smul_left (d := d) (interiorHalfSpace_isOpen hΩ)
    v hu c

/-- For `u ∈ W^{k,2}_0(Ω)`, the squared `L²`-Sobolev half-space norm
(real-valued) equals the half-space inner product `⟨u, u⟩`. -/
theorem wkpNormL2SqHalfSpace_toReal_eq_wkpInnerL2HalfSpace_self
    {k : ℕ} {u : E → ℝ} {Ω : Set E}
    (hu : MemWkpHalfSpace (d := d) k 2 u Ω) :
    (wkpNormL2SqHalfSpace (d := d) k u Ω).toReal =
      wkpInnerL2HalfSpace (d := d) k u u Ω := by
  unfold wkpNormL2SqHalfSpace wkpInnerL2HalfSpace
  exact wkpNormL2Sq_toReal_eq_wkpInnerL2_self (d := d) hu

/-- The squared `L²`-Sobolev half-space norm equals the half-space inner
product `⟨u, u⟩`, in `ℝ` (with both sides finite for
`MemWkpHalfSpace k 2 u Ω`). -/
theorem wkpNormL2HalfSpace_sq_toReal_eq_wkpInnerL2HalfSpace_self
    {k : ℕ} {u : E → ℝ} {Ω : Set E}
    (hu : MemWkpHalfSpace (d := d) k 2 u Ω) :
    ((wkpNormL2HalfSpace (d := d) k u Ω).toReal) ^ 2 =
      wkpInnerL2HalfSpace (d := d) k u u Ω := by
  unfold wkpNormL2HalfSpace wkpInnerL2HalfSpace
  exact wkpNormL2_sq_toReal_eq_wkpInnerL2_self (d := d) hu

end Euclidean
end Sobolev
end Analysis
end DifferentialGeometry
