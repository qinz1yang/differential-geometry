import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolev
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Algebra.Order.Chebyshev

/-!
# `L²`-convention iterated Euclidean Sobolev norm and inner product

The iterated Sobolev norm `wkpNorm k 2 u Ω` defined in
`EuclideanIteratedSobolev.lean` is the *linear* sum
`∑_{|β| ≤ k} ‖∂^β u‖_{L²(Ω)}`. While this is convenient for general `p`,
it is not directly compatible with an inner-product structure when
`p = 2`. The standard `L²`-Sobolev convention uses the Euclidean
combination

  `‖u‖_{W^{k,2}} = (∑_{|β| ≤ k} ‖∂^β u‖²_{L²(Ω)})^{1/2}`,

i.e. the square root of the sum of squared `L²` norms of all iterated
weak partials of order at most `k`. This norm derives from the bilinear
inner product

  `⟨u, v⟩_{W^{k,2}} = ∑_{|β| ≤ k} ∫_Ω (∂^β u)(∂^β v) dx`.

This file introduces these `L²`-convention quantities and establishes
their basic properties: triangle inequality, scaling, finiteness, and
norm equivalence with the linear-sum convention.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal RealInnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Euclidean

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Sigma type indexing all multi-indices of order `j ≤ k` for the iterated
weak partial derivatives. -/
abbrev wkpIdx (k d : ℕ) : Type := (j : Fin (k + 1)) × (Fin j.val → Fin d)

/-- The number of multi-indices of order `≤ k` in `d` directions. -/
def wkpIndexCardL2 (k d : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (k + 1), d ^ j

theorem wkpIndexCardL2_eq_card (k d : ℕ) :
    wkpIndexCardL2 k d = Fintype.card (wkpIdx k d) := by
  classical
  unfold wkpIndexCardL2
  rw [Fintype.card_sigma]
  rw [show (Finset.range (k + 1)) = (Finset.univ : Finset (Fin (k + 1))).image Fin.val by
    ext j; simp [Finset.mem_range, Finset.mem_image, Fin.exists_iff, Finset.mem_univ]]
  rw [Finset.sum_image (fun i _ j _ hij => Fin.val_inj.mp hij)]
  simp [Fintype.card_pi, Fintype.card_fin, Fin.sum_univ_eq_sum_range]

/-- The squared `L²`-convention Sobolev norm of order `k`: the sum of
squared `L²(Ω)` norms of all iterated weak partials of order `≤ k`. -/
def wkpNormL2Sq (k : ℕ) (u : E → ℝ) (Ω : Set E) : ℝ≥0∞ :=
  ∑ j ∈ Finset.range (k + 1),
    ∑ β : Fin j → Fin d,
      eLpNorm (iterWeakPartial (d := d) (2 : ℝ≥0∞) j β u Ω) 2 (volume.restrict Ω) ^ (2 : ℕ)

/-- The `L²`-convention Sobolev norm of order `k`: the square root of
the sum of squared `L²(Ω)` norms of all iterated weak partials of order
`≤ k`. -/
def wkpNormL2 (k : ℕ) (u : E → ℝ) (Ω : Set E) : ℝ≥0∞ :=
  wkpNormL2Sq (d := d) k u Ω ^ ((1 : ℝ) / 2)

theorem wkpNormL2Sq_eq_sum
    (k : ℕ) (u : E → ℝ) (Ω : Set E) :
    wkpNormL2Sq (d := d) k u Ω =
      ∑ j ∈ Finset.range (k + 1),
        ∑ β : Fin j → Fin d,
          eLpNorm (iterWeakPartial (d := d) (2 : ℝ≥0∞) j β u Ω) 2
              (volume.restrict Ω) ^ (2 : ℕ) := rfl

theorem wkpNormL2_eq_rpow
    (k : ℕ) (u : E → ℝ) (Ω : Set E) :
    wkpNormL2 (d := d) k u Ω =
      wkpNormL2Sq (d := d) k u Ω ^ ((1 : ℝ) / 2) := rfl

/-- The `L²` Sobolev norm sum reindexed via the Sigma type. -/
theorem wkpNormL2Sq_eq_sigma_sum
    (k : ℕ) (u : E → ℝ) (Ω : Set E) :
    wkpNormL2Sq (d := d) k u Ω =
      ∑ a : wkpIdx k d,
        eLpNorm (iterWeakPartial (d := d) (2 : ℝ≥0∞) a.1.val a.2 u Ω) 2
          (volume.restrict Ω) ^ (2 : ℕ) := by
  classical
  unfold wkpNormL2Sq
  rw [show (Finset.range (k + 1)) = (Finset.univ : Finset (Fin (k + 1))).image Fin.val by
    ext j; simp [Finset.mem_range, Finset.mem_image, Fin.exists_iff, Finset.mem_univ]]
  rw [Finset.sum_image (fun i _ j _ hij => Fin.val_inj.mp hij)]
  rw [← Finset.univ_sigma_univ (κ := fun (i : Fin (k + 1)) => (Fin i.val → Fin d))]
  rw [Finset.sum_sigma]

/-- Linear-sum norm `wkpNorm k 2` reindexed via the Sigma type. -/
theorem wkpNorm_two_eq_sigma_sum
    (k : ℕ) (u : E → ℝ) (Ω : Set E) :
    wkpNorm (d := d) k 2 u Ω =
      ∑ a : wkpIdx k d,
        eLpNorm (iterWeakPartial (d := d) (2 : ℝ≥0∞) a.1.val a.2 u Ω) 2
          (volume.restrict Ω) := by
  classical
  unfold wkpNorm
  rw [show (Finset.range (k + 1)) = (Finset.univ : Finset (Fin (k + 1))).image Fin.val by
    ext j; simp [Finset.mem_range, Finset.mem_image, Fin.exists_iff, Finset.mem_univ]]
  rw [Finset.sum_image (fun i _ j _ hij => Fin.val_inj.mp hij)]
  rw [← Finset.univ_sigma_univ (κ := fun (i : Fin (k + 1)) => (Fin i.val → Fin d))]
  rw [Finset.sum_sigma]

/-- `wkpNormL2Sq 0 u Ω = (eLpNorm u 2 (volume.restrict Ω))²`. -/
theorem wkpNormL2Sq_zero
    (u : E → ℝ) (Ω : Set E) :
    wkpNormL2Sq (d := d) 0 u Ω =
      eLpNorm u 2 (volume.restrict Ω) ^ (2 : ℕ) := by
  classical
  unfold wkpNormL2Sq
  rw [Finset.sum_range_one]
  have hUniq : ∀ α : Fin 0 → Fin d, α = (fun i : Fin 0 => i.elim0) := fun α => by
    funext i; exact i.elim0
  haveI : Unique (Fin 0 → Fin d) :=
    { default := fun i : Fin 0 => i.elim0
      uniq := fun α => (hUniq α).symm ▸ rfl }
  rw [Fintype.sum_unique
        (f := fun α : Fin 0 → Fin d =>
          eLpNorm (iterWeakPartial (d := d) (2 : ℝ≥0∞) 0 α u Ω) 2
              (volume.restrict Ω) ^ (2 : ℕ))]
  simp [iterWeakPartial_zero]

/-- The `L²`-convention Sobolev inner product of order `k`:
`⟨u, v⟩_{W^{k,2}} = ∑_{|β| ≤ k} ∫_Ω (∂^β u)(∂^β v) dx`. -/
def wkpInnerL2 (k : ℕ) (u v : E → ℝ) (Ω : Set E) : ℝ :=
  ∑ j ∈ Finset.range (k + 1),
    ∑ β : Fin j → Fin d,
      ∫ x in Ω,
        iterWeakPartial (d := d) (2 : ℝ≥0∞) j β u Ω x *
          iterWeakPartial (d := d) (2 : ℝ≥0∞) j β v Ω x

theorem wkpInnerL2_eq_sum
    (k : ℕ) (u v : E → ℝ) (Ω : Set E) :
    wkpInnerL2 (d := d) k u v Ω =
      ∑ j ∈ Finset.range (k + 1),
        ∑ β : Fin j → Fin d,
          ∫ x in Ω,
            iterWeakPartial (d := d) (2 : ℝ≥0∞) j β u Ω x *
              iterWeakPartial (d := d) (2 : ℝ≥0∞) j β v Ω x := rfl

/-- The `L²` Sobolev inner product reindexed via the Sigma type. -/
theorem wkpInnerL2_eq_sigma_sum
    (k : ℕ) (u v : E → ℝ) (Ω : Set E) :
    wkpInnerL2 (d := d) k u v Ω =
      ∑ a : wkpIdx k d,
        ∫ x in Ω,
          iterWeakPartial (d := d) (2 : ℝ≥0∞) a.1.val a.2 u Ω x *
            iterWeakPartial (d := d) (2 : ℝ≥0∞) a.1.val a.2 v Ω x := by
  classical
  unfold wkpInnerL2
  rw [show (Finset.range (k + 1)) = (Finset.univ : Finset (Fin (k + 1))).image Fin.val by
    ext j; simp [Finset.mem_range, Finset.mem_image, Fin.exists_iff, Finset.mem_univ]]
  rw [Finset.sum_image (fun i _ j _ hij => Fin.val_inj.mp hij)]
  rw [← Finset.univ_sigma_univ (κ := fun (i : Fin (k + 1)) => (Fin i.val → Fin d))]
  rw [Finset.sum_sigma]

/-- `wkpNormL2Sq k 0 Ω = 0`. -/
theorem wkpNormL2Sq_zero_fun_zero
    {k : ℕ} {Ω : Set E} (hΩ : IsOpen Ω) :
    wkpNormL2Sq (d := d) k (fun _ : E => (0 : ℝ)) Ω = 0 := by
  classical
  unfold wkpNormL2Sq
  refine Finset.sum_eq_zero ?_
  intro j _
  refine Finset.sum_eq_zero ?_
  intro β _
  have h_zero_ae : (fun _ : E => (0 : ℝ)) =ᵐ[volume.restrict Ω] (fun _ => 0) :=
    Filter.Eventually.of_forall (fun _ => rfl)
  have h_iter_ae := iterWeakPartial_ae_zero_of_input_ae_zero (d := d)
    (p := (2 : ℝ≥0∞)) (by norm_num) hΩ j β h_zero_ae
  rw [eLpNorm_congr_ae h_iter_ae]
  simp

/-- `wkpNormL2 k 0 Ω = 0`. -/
theorem wkpNormL2_zero_fun_zero
    {k : ℕ} {Ω : Set E} (hΩ : IsOpen Ω) :
    wkpNormL2 (d := d) k (fun _ : E => (0 : ℝ)) Ω = 0 := by
  unfold wkpNormL2
  rw [wkpNormL2Sq_zero_fun_zero (d := d) hΩ]
  exact ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)

/-- For `u ∈ W^{k,2}(Ω)`, the squared `L²`-Sobolev norm is finite. -/
theorem wkpNormL2Sq_lt_top_of_memWkp
    {k : ℕ} {u : E → ℝ} {Ω : Set E}
    (h : MemWkp (d := d) k 2 u Ω) :
    wkpNormL2Sq (d := d) k u Ω < ∞ := by
  classical
  unfold wkpNormL2Sq
  refine ENNReal.sum_lt_top.mpr ?_
  intro j hj
  refine ENNReal.sum_lt_top.mpr ?_
  intro β _
  have hj_le : j ≤ k := by
    rw [Finset.mem_range] at hj; omega
  have h_uWj : MemWkp (d := d) j 2 u Ω := MemWkp.le_of_le hj_le h
  have h_iter := iterWeakPartial_memLp_of_memWkp (d := d) (p := 2) h_uWj β
  exact ENNReal.pow_lt_top h_iter.eLpNorm_lt_top

/-- For `u ∈ W^{k,2}(Ω)`, the `L²`-Sobolev norm is finite. -/
theorem wkpNormL2_lt_top_of_memWkp
    {k : ℕ} {u : E → ℝ} {Ω : Set E}
    (h : MemWkp (d := d) k 2 u Ω) :
    wkpNormL2 (d := d) k u Ω < ∞ := by
  unfold wkpNormL2
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (wkpNormL2Sq_lt_top_of_memWkp (d := d) h).ne

/-- `wkpNormL2Sq` is invariant under ae-equality on `volume.restrict Ω`
for open `Ω`. -/
theorem wkpNormL2Sq_congr_ae
    {k : ℕ} {Ω : Set E} (hΩ : IsOpen Ω)
    {u v : E → ℝ} (huv : u =ᵐ[volume.restrict Ω] v) :
    wkpNormL2Sq (d := d) k u Ω = wkpNormL2Sq (d := d) k v Ω := by
  classical
  unfold wkpNormL2Sq
  refine Finset.sum_congr rfl ?_
  intro j _
  refine Finset.sum_congr rfl ?_
  intro β _
  have h_iter_ae : iterWeakPartial (d := d) (2 : ℝ≥0∞) j β u Ω
      =ᵐ[volume.restrict Ω] iterWeakPartial (d := d) (2 : ℝ≥0∞) j β v Ω :=
    iterWeakPartial_ae_congr (d := d) (by norm_num) hΩ j β huv
  rw [eLpNorm_congr_ae h_iter_ae]

/-- `wkpNormL2` is invariant under ae-equality on `volume.restrict Ω`
for open `Ω`. -/
theorem wkpNormL2_congr_ae
    {k : ℕ} {Ω : Set E} (hΩ : IsOpen Ω)
    {u v : E → ℝ} (huv : u =ᵐ[volume.restrict Ω] v) :
    wkpNormL2 (d := d) k u Ω = wkpNormL2 (d := d) k v Ω := by
  unfold wkpNormL2
  rw [wkpNormL2Sq_congr_ae (d := d) hΩ huv]

/-- Squaring `wkpNormL2` recovers `wkpNormL2Sq`. -/
theorem wkpNormL2_sq_eq_wkpNormL2Sq
    (k : ℕ) (u : E → ℝ) (Ω : Set E) :
    wkpNormL2 (d := d) k u Ω ^ (2 : ℕ) = wkpNormL2Sq (d := d) k u Ω := by
  unfold wkpNormL2
  rw [show ((wkpNormL2Sq (d := d) k u Ω) ^ ((1 : ℝ) / 2)) ^ (2 : ℕ) =
      (wkpNormL2Sq (d := d) k u Ω) ^ (((1 : ℝ) / 2) * ((2 : ℕ) : ℝ)) by
    rw [← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul]]
  rw [show ((1 : ℝ) / 2) * ((2 : ℕ) : ℝ) = 1 by norm_num]
  rw [ENNReal.rpow_one]

/-- `wkpNormL2 k u Ω = ENNReal.ofReal √((wkpNormL2Sq k u Ω).toReal)`
when `wkpNormL2Sq k u Ω` is finite. -/
private theorem wkpNormL2_eq_ofReal_sqrt_toReal
    {k : ℕ} {u : E → ℝ} {Ω : Set E}
    (hSq : wkpNormL2Sq (d := d) k u Ω ≠ ∞) :
    wkpNormL2 (d := d) k u Ω =
      ENNReal.ofReal (Real.sqrt (wkpNormL2Sq (d := d) k u Ω).toReal) := by
  unfold wkpNormL2
  have h_toReal_pow :
      (wkpNormL2Sq (d := d) k u Ω) ^ ((1 : ℝ) / 2) =
        ENNReal.ofReal ((wkpNormL2Sq (d := d) k u Ω).toReal ^ ((1 : ℝ) / 2)) := by
    rw [← ENNReal.ofReal_toReal hSq]
    rw [ENNReal.toReal_ofReal ENNReal.toReal_nonneg]
    rw [ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg
        (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  rw [h_toReal_pow]
  rw [show (wkpNormL2Sq (d := d) k u Ω).toReal ^ ((1 : ℝ) / 2) =
      Real.sqrt (wkpNormL2Sq (d := d) k u Ω).toReal by
    rw [Real.sqrt_eq_rpow]]

/-- The triangle inequality for `wkpNormL2`. Each summand `(eLpNorm (∂^β (u + v)) 2)²`
is bounded by `(eLpNorm (∂^β u) 2 + eLpNorm (∂^β v) 2)²` (via the Minkowski inequality on
`L²(Ω)`); then we apply the Euclidean triangle inequality on the finite-dimensional sum. -/
theorem wkpNormL2_add_le
    {k : ℕ} {Ω : Set E} (hΩ : IsOpen Ω)
    {u v : E → ℝ}
    (hu : MemWkp (d := d) k 2 u Ω) (hv : MemWkp (d := d) k 2 v Ω) :
    wkpNormL2 (d := d) k (fun x => u x + v x) Ω ≤
      wkpNormL2 (d := d) k u Ω + wkpNormL2 (d := d) k v Ω := by
  classical
  set f : wkpIdx k d → ℝ≥0∞ := fun a =>
    eLpNorm (iterWeakPartial (d := d) (2 : ℝ≥0∞) a.1.val a.2 u Ω) 2 (volume.restrict Ω)
    with hf_def
  set g : wkpIdx k d → ℝ≥0∞ := fun a =>
    eLpNorm (iterWeakPartial (d := d) (2 : ℝ≥0∞) a.1.val a.2 v Ω) 2 (volume.restrict Ω)
    with hg_def
  set h : wkpIdx k d → ℝ≥0∞ := fun a =>
    eLpNorm (iterWeakPartial (d := d) (2 : ℝ≥0∞) a.1.val a.2
        (fun x => u x + v x) Ω) 2 (volume.restrict Ω)
    with hh_def
  have h_per_a : ∀ a : wkpIdx k d, h a ≤ f a + g a := by
    intro a
    obtain ⟨⟨j, hj⟩, β⟩ := a
    have hj_le : j ≤ k := Nat.lt_succ_iff.mp hj
    have h_uWj : MemWkp (d := d) j 2 u Ω := MemWkp.le_of_le hj_le hu
    have h_vWj : MemWkp (d := d) j 2 v Ω := MemWkp.le_of_le hj_le hv
    have h_iter_add_ae :=
      iterWeakPartial_add_ae (d := d) (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ β h_uWj h_vWj
    change eLpNorm _ 2 _ ≤ _
    rw [eLpNorm_congr_ae h_iter_add_ae]
    have h_iter_u := iterWeakPartial_memLp_of_memWkp (d := d) (p := (2 : ℝ≥0∞)) h_uWj β
    have h_iter_v := iterWeakPartial_memLp_of_memWkp (d := d) (p := (2 : ℝ≥0∞)) h_vWj β
    have htr := eLpNorm_add_le (μ := volume.restrict Ω) (p := (2 : ℝ≥0∞))
      h_iter_u.aestronglyMeasurable h_iter_v.aestronglyMeasurable
      (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have hEq : (iterWeakPartial (d := d) (2 : ℝ≥0∞) j β u Ω +
        iterWeakPartial (d := d) (2 : ℝ≥0∞) j β v Ω) =
        fun x => iterWeakPartial (d := d) (2 : ℝ≥0∞) j β u Ω x +
          iterWeakPartial (d := d) (2 : ℝ≥0∞) j β v Ω x := by
      funext x; simp [Pi.add_apply]
    rw [hEq] at htr
    exact htr
  have h_finiteness_f : ∀ a : wkpIdx k d, f a < ∞ := by
    intro a
    obtain ⟨⟨j, hj⟩, β⟩ := a
    have hj_le : j ≤ k := Nat.lt_succ_iff.mp hj
    have h_uWj : MemWkp (d := d) j 2 u Ω := MemWkp.le_of_le hj_le hu
    exact (iterWeakPartial_memLp_of_memWkp (d := d) (p := (2 : ℝ≥0∞)) h_uWj β).eLpNorm_lt_top
  have h_finiteness_g : ∀ a : wkpIdx k d, g a < ∞ := by
    intro a
    obtain ⟨⟨j, hj⟩, β⟩ := a
    have hj_le : j ≤ k := Nat.lt_succ_iff.mp hj
    have h_vWj : MemWkp (d := d) j 2 v Ω := MemWkp.le_of_le hj_le hv
    exact (iterWeakPartial_memLp_of_memWkp (d := d) (p := (2 : ℝ≥0∞)) h_vWj β).eLpNorm_lt_top
  have h_finiteness_h : ∀ a : wkpIdx k d, h a < ∞ := fun a =>
    lt_of_le_of_lt (h_per_a a)
      (lt_of_le_of_ne le_top
        (ENNReal.add_ne_top.mpr ⟨(h_finiteness_f a).ne, (h_finiteness_g a).ne⟩))
  let fR : wkpIdx k d → ℝ := fun a => (f a).toReal
  let gR : wkpIdx k d → ℝ := fun a => (g a).toReal
  let hR : wkpIdx k d → ℝ := fun a => (h a).toReal
  have hfR_nonneg : ∀ a : wkpIdx k d, 0 ≤ fR a := fun a => ENNReal.toReal_nonneg
  have hgR_nonneg : ∀ a : wkpIdx k d, 0 ≤ gR a := fun a => ENNReal.toReal_nonneg
  have hhR_nonneg : ∀ a : wkpIdx k d, 0 ≤ hR a := fun a => ENNReal.toReal_nonneg
  have hhR_le : ∀ a, hR a ≤ fR a + gR a := by
    intro a
    have h_lhs := h_per_a a
    have h_rhs_ne : f a + g a ≠ ∞ :=
      ENNReal.add_ne_top.mpr ⟨(h_finiteness_f a).ne, (h_finiteness_g a).ne⟩
    have h_lhs_le := ENNReal.toReal_mono h_rhs_ne h_lhs
    rw [ENNReal.toReal_add (h_finiteness_f a).ne (h_finiteness_g a).ne] at h_lhs_le
    exact h_lhs_le
  have h_triangle :
      Real.sqrt (∑ a : wkpIdx k d, hR a ^ 2) ≤
        Real.sqrt (∑ a : wkpIdx k d, fR a ^ 2) + Real.sqrt (∑ a : wkpIdx k d, gR a ^ 2) := by
    let FR : EuclideanSpace ℝ (wkpIdx k d) := WithLp.toLp 2 fR
    let GR : EuclideanSpace ℝ (wkpIdx k d) := WithLp.toLp 2 gR
    let HR : EuclideanSpace ℝ (wkpIdx k d) := WithLp.toLp 2 hR
    have hFR_apply : ∀ a, FR a = fR a := fun a => rfl
    have hGR_apply : ∀ a, GR a = gR a := fun a => rfl
    have hHR_apply : ∀ a, HR a = hR a := fun a => rfl
    have h_norm_FR : ‖FR‖ = Real.sqrt (∑ a : wkpIdx k d, fR a ^ 2) := by
      rw [EuclideanSpace.norm_eq]
      congr 1
      refine Finset.sum_congr rfl ?_
      intro a _
      rw [Real.norm_eq_abs, sq_abs, hFR_apply]
    have h_norm_GR : ‖GR‖ = Real.sqrt (∑ a : wkpIdx k d, gR a ^ 2) := by
      rw [EuclideanSpace.norm_eq]
      congr 1
      refine Finset.sum_congr rfl ?_
      intro a _
      rw [Real.norm_eq_abs, sq_abs, hGR_apply]
    have h_norm_HR : ‖HR‖ = Real.sqrt (∑ a : wkpIdx k d, hR a ^ 2) := by
      rw [EuclideanSpace.norm_eq]
      congr 1
      refine Finset.sum_congr rfl ?_
      intro a _
      rw [Real.norm_eq_abs, sq_abs, hHR_apply]
    have h_componentwise : ∀ a, ‖HR a‖ ≤ ‖(FR + GR) a‖ := by
      intro a
      rw [Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (by rw [hHR_apply]; exact hhR_nonneg a),
          abs_of_nonneg (by
            rw [show (FR + GR) a = FR a + GR a from rfl, hFR_apply, hGR_apply]
            exact add_nonneg (hfR_nonneg a) (hgR_nonneg a))]
      rw [hHR_apply, show (FR + GR) a = FR a + GR a from rfl, hFR_apply, hGR_apply]
      exact hhR_le a
    have h_le_sum : ‖HR‖ ≤ ‖FR + GR‖ := by
      rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
      apply Real.sqrt_le_sqrt
      apply Finset.sum_le_sum
      intro a _
      have hH_nn : 0 ≤ ‖HR a‖ := norm_nonneg _
      have h_le := h_componentwise a
      nlinarith [sq_nonneg (‖HR a‖ - ‖(FR + GR) a‖), norm_nonneg (HR a), norm_nonneg ((FR + GR) a)]
    have h_lp_triangle : ‖FR + GR‖ ≤ ‖FR‖ + ‖GR‖ := norm_add_le FR GR
    rw [← h_norm_HR, ← h_norm_FR, ← h_norm_GR]
    linarith
  have hu_v : MemWkp (d := d) k 2 (fun x => u x + v x) Ω :=
    MemWkp.add (d := d) (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ hu hv
  have hSq_uv_ne : wkpNormL2Sq (d := d) k (fun x => u x + v x) Ω ≠ ∞ :=
    (wkpNormL2Sq_lt_top_of_memWkp (d := d) hu_v).ne
  have hSq_u_ne : wkpNormL2Sq (d := d) k u Ω ≠ ∞ :=
    (wkpNormL2Sq_lt_top_of_memWkp (d := d) hu).ne
  have hSq_v_ne : wkpNormL2Sq (d := d) k v Ω ≠ ∞ :=
    (wkpNormL2Sq_lt_top_of_memWkp (d := d) hv).ne
  have hSq_u_toReal :
      (wkpNormL2Sq (d := d) k u Ω).toReal = ∑ a : wkpIdx k d, fR a ^ 2 := by
    rw [wkpNormL2Sq_eq_sigma_sum]
    rw [ENNReal.toReal_sum (fun a _ => (ENNReal.pow_lt_top (h_finiteness_f a)).ne)]
    apply Finset.sum_congr (rfl : (Finset.univ : Finset (wkpIdx k d)) = Finset.univ)
    intro a _
    rw [ENNReal.toReal_pow]
  have hSq_v_toReal :
      (wkpNormL2Sq (d := d) k v Ω).toReal = ∑ a : wkpIdx k d, gR a ^ 2 := by
    rw [wkpNormL2Sq_eq_sigma_sum]
    rw [ENNReal.toReal_sum (fun a _ => (ENNReal.pow_lt_top (h_finiteness_g a)).ne)]
    apply Finset.sum_congr (rfl : (Finset.univ : Finset (wkpIdx k d)) = Finset.univ)
    intro a _
    rw [ENNReal.toReal_pow]
  have hSq_uv_toReal :
      (wkpNormL2Sq (d := d) k (fun x => u x + v x) Ω).toReal =
        ∑ a : wkpIdx k d, hR a ^ 2 := by
    rw [wkpNormL2Sq_eq_sigma_sum]
    rw [ENNReal.toReal_sum (fun a _ => (ENNReal.pow_lt_top (h_finiteness_h a)).ne)]
    apply Finset.sum_congr (rfl : (Finset.univ : Finset (wkpIdx k d)) = Finset.univ)
    intro a _
    rw [ENNReal.toReal_pow]
  rw [wkpNormL2_eq_ofReal_sqrt_toReal hSq_uv_ne]
  rw [wkpNormL2_eq_ofReal_sqrt_toReal hSq_u_ne]
  rw [wkpNormL2_eq_ofReal_sqrt_toReal hSq_v_ne]
  rw [hSq_uv_toReal, hSq_u_toReal, hSq_v_toReal]
  rw [← ENNReal.ofReal_add (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  exact h_triangle

/-- Scalar multiplication identity for `wkpNormL2Sq`. -/
theorem wkpNormL2Sq_const_smul
    {k : ℕ} {Ω : Set E} (hΩ : IsOpen Ω)
    {u : E → ℝ} (hu : MemWkp (d := d) k 2 u Ω) (c : ℝ) :
    wkpNormL2Sq (d := d) k (fun x => c * u x) Ω =
      ‖c‖ₑ ^ (2 : ℕ) * wkpNormL2Sq (d := d) k u Ω := by
  classical
  unfold wkpNormL2Sq
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro j hj
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro β _
  have hj_le : j ≤ k := by
    rw [Finset.mem_range] at hj; omega
  have h_uWj : MemWkp (d := d) j 2 u Ω := MemWkp.le_of_le hj_le hu
  have h_iter_smul_ae :=
    iterWeakPartial_const_smul_ae (d := d) (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ β h_uWj c
  rw [eLpNorm_congr_ae h_iter_smul_ae]
  have heq : (fun x => c * iterWeakPartial (d := d) (2 : ℝ≥0∞) j β u Ω x) =
      (c : ℝ) • iterWeakPartial (d := d) (2 : ℝ≥0∞) j β u Ω := by
    funext x; simp [Pi.smul_apply, smul_eq_mul]
  rw [heq, eLpNorm_const_smul]
  rw [mul_pow]

/-- Scalar multiplication identity for `wkpNormL2`. -/
theorem wkpNormL2_const_smul
    {k : ℕ} {Ω : Set E} (hΩ : IsOpen Ω)
    {u : E → ℝ} (hu : MemWkp (d := d) k 2 u Ω) (c : ℝ) :
    wkpNormL2 (d := d) k (fun x => c * u x) Ω =
      ‖c‖ₑ * wkpNormL2 (d := d) k u Ω := by
  unfold wkpNormL2
  rw [wkpNormL2Sq_const_smul (d := d) hΩ hu c]
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  congr 1
  rw [show ((‖c‖ₑ : ℝ≥0∞) ^ (2 : ℕ)) = ‖c‖ₑ ^ ((2 : ℕ) : ℝ) by
    rw [ENNReal.rpow_natCast]]
  rw [← ENNReal.rpow_mul]
  norm_num

/-- Equivalence inequality 1: `wkpNormL2 ≤ wkpNorm` at `p = 2`.
This uses that `√(∑ a_i²) ≤ ∑ a_i` for nonneg `a_i`. -/
theorem wkpNormL2_le_wkpNorm
    {k : ℕ} {u : E → ℝ} {Ω : Set E}
    (hu : MemWkp (d := d) k 2 u Ω) :
    wkpNormL2 (d := d) k u Ω ≤ wkpNorm (d := d) k 2 u Ω := by
  classical
  set f : wkpIdx k d → ℝ≥0∞ := fun a =>
    eLpNorm (iterWeakPartial (d := d) (2 : ℝ≥0∞) a.1.val a.2 u Ω) 2 (volume.restrict Ω)
    with hf_def
  have h_finiteness_f : ∀ a : wkpIdx k d, f a < ∞ := by
    intro a
    obtain ⟨⟨j, hj⟩, β⟩ := a
    have hj_le : j ≤ k := Nat.lt_succ_iff.mp hj
    have h_uWj : MemWkp (d := d) j 2 u Ω := MemWkp.le_of_le hj_le hu
    exact (iterWeakPartial_memLp_of_memWkp (d := d) (p := (2 : ℝ≥0∞)) h_uWj β).eLpNorm_lt_top
  let fR : wkpIdx k d → ℝ := fun a => (f a).toReal
  have hfR_nonneg : ∀ a : wkpIdx k d, 0 ≤ fR a := fun a => ENNReal.toReal_nonneg
  have h_real : Real.sqrt (∑ a : wkpIdx k d, fR a ^ 2) ≤ ∑ a : wkpIdx k d, fR a := by
    have h_aux : ∀ a ∈ (Finset.univ : Finset (wkpIdx k d)), fR a ^ 2 ≤ fR a * (∑ b, fR b) := by
      intro a _
      rw [sq]
      apply mul_le_mul_of_nonneg_left _ (hfR_nonneg a)
      exact Finset.single_le_sum (f := fR) (fun b _ => hfR_nonneg b) (Finset.mem_univ _)
    have h_sq_le : ∑ a : wkpIdx k d, fR a ^ 2 ≤ (∑ a : wkpIdx k d, fR a) ^ 2 := by
      calc ∑ a : wkpIdx k d, fR a ^ 2
          ≤ ∑ a : wkpIdx k d, fR a * (∑ b, fR b) := Finset.sum_le_sum h_aux
        _ = (∑ a : wkpIdx k d, fR a) * (∑ b, fR b) := by rw [← Finset.sum_mul]
        _ = (∑ a : wkpIdx k d, fR a) ^ 2 := by rw [sq]
    have h_sum_nonneg : 0 ≤ ∑ a : wkpIdx k d, fR a :=
      Finset.sum_nonneg (fun a _ => hfR_nonneg a)
    calc Real.sqrt (∑ a : wkpIdx k d, fR a ^ 2)
        ≤ Real.sqrt ((∑ a : wkpIdx k d, fR a) ^ 2) := Real.sqrt_le_sqrt h_sq_le
      _ = |∑ a : wkpIdx k d, fR a| := Real.sqrt_sq_eq_abs _
      _ = ∑ a : wkpIdx k d, fR a := abs_of_nonneg h_sum_nonneg
  have hSq_finite : wkpNormL2Sq (d := d) k u Ω ≠ ∞ :=
    (wkpNormL2Sq_lt_top_of_memWkp (d := d) hu).ne
  have hLin_finite : wkpNorm (d := d) k 2 u Ω ≠ ∞ :=
    (wkpNorm_lt_top_of_memWkp (d := d) hu).ne
  have hSq_toReal :
      (wkpNormL2Sq (d := d) k u Ω).toReal = ∑ a : wkpIdx k d, fR a ^ 2 := by
    rw [wkpNormL2Sq_eq_sigma_sum]
    rw [ENNReal.toReal_sum (fun a _ => (ENNReal.pow_lt_top (h_finiteness_f a)).ne)]
    apply Finset.sum_congr (rfl : (Finset.univ : Finset (wkpIdx k d)) = Finset.univ)
    intro a _
    rw [ENNReal.toReal_pow]
  have hLin_toReal :
      (wkpNorm (d := d) k 2 u Ω).toReal = ∑ a : wkpIdx k d, fR a := by
    rw [wkpNorm_two_eq_sigma_sum]
    rw [ENNReal.toReal_sum (fun a _ => (h_finiteness_f a).ne)]
  rw [wkpNormL2_eq_ofReal_sqrt_toReal hSq_finite, hSq_toReal]
  rw [show wkpNorm (d := d) k 2 u Ω = ENNReal.ofReal (∑ a : wkpIdx k d, fR a) from by
    rw [← hLin_toReal, ENNReal.ofReal_toReal hLin_finite]]
  exact ENNReal.ofReal_le_ofReal h_real

/-- Equivalence inequality 2: `wkpNorm ≤ √N · wkpNormL2` at `p = 2`,
where `N = wkpIndexCardL2 k d` is the number of multi-indices of order `≤ k`.
This uses Cauchy-Schwarz `(∑ a_i)² ≤ N · ∑ a_i²`. -/
theorem wkpNorm_le_sqrt_card_mul_wkpNormL2
    {k : ℕ} {u : E → ℝ} {Ω : Set E}
    (hu : MemWkp (d := d) k 2 u Ω) :
    wkpNorm (d := d) k 2 u Ω ≤
      ENNReal.ofReal (Real.sqrt (wkpIndexCardL2 k d)) *
        wkpNormL2 (d := d) k u Ω := by
  classical
  have h_card_A : (Fintype.card (wkpIdx k d) : ℝ) = wkpIndexCardL2 k d := by
    rw [wkpIndexCardL2_eq_card]
  set f : wkpIdx k d → ℝ≥0∞ := fun a =>
    eLpNorm (iterWeakPartial (d := d) (2 : ℝ≥0∞) a.1.val a.2 u Ω) 2 (volume.restrict Ω)
    with hf_def
  have h_finiteness_f : ∀ a : wkpIdx k d, f a < ∞ := by
    intro a
    obtain ⟨⟨j, hj⟩, β⟩ := a
    have hj_le : j ≤ k := Nat.lt_succ_iff.mp hj
    have h_uWj : MemWkp (d := d) j 2 u Ω := MemWkp.le_of_le hj_le hu
    exact (iterWeakPartial_memLp_of_memWkp (d := d) (p := (2 : ℝ≥0∞)) h_uWj β).eLpNorm_lt_top
  let fR : wkpIdx k d → ℝ := fun a => (f a).toReal
  have hfR_nonneg : ∀ a : wkpIdx k d, 0 ≤ fR a := fun a => ENNReal.toReal_nonneg
  have h_real : (∑ a : wkpIdx k d, fR a) ≤
      Real.sqrt (Fintype.card (wkpIdx k d) : ℝ) * Real.sqrt (∑ a : wkpIdx k d, fR a ^ 2) := by
    have h_CS : (∑ a : wkpIdx k d, fR a) ^ 2 ≤
        (Fintype.card (wkpIdx k d) : ℝ) * ∑ a : wkpIdx k d, fR a ^ 2 := by
      have h := @sq_sum_le_card_mul_sum_sq (wkpIdx k d) ℝ _ _ _ _ Finset.univ fR
      rw [Finset.card_univ] at h
      exact h
    have h_card_nonneg : 0 ≤ (Fintype.card (wkpIdx k d) : ℝ) := Nat.cast_nonneg _
    have h_sum_sq_nonneg : 0 ≤ ∑ a : wkpIdx k d, fR a ^ 2 :=
      Finset.sum_nonneg (fun a _ => sq_nonneg _)
    have h_sum_nonneg : 0 ≤ ∑ a : wkpIdx k d, fR a :=
      Finset.sum_nonneg (fun a _ => hfR_nonneg a)
    have h_RHS_nonneg : 0 ≤ Real.sqrt (Fintype.card (wkpIdx k d) : ℝ) * Real.sqrt (∑ a : wkpIdx k d, fR a ^ 2) :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    nlinarith [Real.sq_sqrt h_card_nonneg, Real.sq_sqrt h_sum_sq_nonneg,
      h_CS, h_sum_nonneg, h_RHS_nonneg, sq_nonneg ((∑ a : wkpIdx k d, fR a) -
        (Real.sqrt (Fintype.card (wkpIdx k d) : ℝ) * Real.sqrt (∑ a : wkpIdx k d, fR a ^ 2)))]
  have hSq_finite : wkpNormL2Sq (d := d) k u Ω ≠ ∞ :=
    (wkpNormL2Sq_lt_top_of_memWkp (d := d) hu).ne
  have hLin_finite : wkpNorm (d := d) k 2 u Ω ≠ ∞ :=
    (wkpNorm_lt_top_of_memWkp (d := d) hu).ne
  have hSq_toReal :
      (wkpNormL2Sq (d := d) k u Ω).toReal = ∑ a : wkpIdx k d, fR a ^ 2 := by
    rw [wkpNormL2Sq_eq_sigma_sum]
    rw [ENNReal.toReal_sum (fun a _ => (ENNReal.pow_lt_top (h_finiteness_f a)).ne)]
    apply Finset.sum_congr (rfl : (Finset.univ : Finset (wkpIdx k d)) = Finset.univ)
    intro a _
    rw [ENNReal.toReal_pow]
  have hLin_toReal :
      (wkpNorm (d := d) k 2 u Ω).toReal = ∑ a : wkpIdx k d, fR a := by
    rw [wkpNorm_two_eq_sigma_sum]
    rw [ENNReal.toReal_sum (fun a _ => (h_finiteness_f a).ne)]
  rw [show wkpNorm (d := d) k 2 u Ω = ENNReal.ofReal (∑ a : wkpIdx k d, fR a) from by
    rw [← hLin_toReal, ENNReal.ofReal_toReal hLin_finite]]
  rw [wkpNormL2_eq_ofReal_sqrt_toReal hSq_finite, hSq_toReal]
  rw [show ENNReal.ofReal (Real.sqrt (wkpIndexCardL2 k d)) =
      ENNReal.ofReal (Real.sqrt (Fintype.card (wkpIdx k d) : ℝ)) from by rw [h_card_A]]
  rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
  exact ENNReal.ofReal_le_ofReal h_real

/-- The `L²`-Sobolev inner product is symmetric. -/
theorem wkpInnerL2_comm
    (k : ℕ) (u v : E → ℝ) (Ω : Set E) :
    wkpInnerL2 (d := d) k u v Ω = wkpInnerL2 (d := d) k v u Ω := by
  unfold wkpInnerL2
  refine Finset.sum_congr rfl ?_
  intro j _
  refine Finset.sum_congr rfl ?_
  intro β _
  refine integral_congr_ae ?_
  filter_upwards with x using mul_comm _ _

/-- Pointwise pseudo-additivity: for `u₁, u₂, v ∈ W^{j,2}(Ω)`, the iterated weak
partial of `u₁ + u₂` is ae-equal to the sum of the iterated weak partials of `u₁`
and `u₂`, so the inner product is additive on the pointwise pre-Hilbert structure.

We prove additivity in the first slot at order `j ≤ k`, working inside a single
summand. The full result `wkpInnerL2_add_left` follows by summation. -/
theorem wkpInnerL2_add_left
    {k : ℕ} {Ω : Set E} (hΩ : IsOpen Ω)
    {u₁ u₂ v : E → ℝ}
    (hu₁ : MemWkp (d := d) k 2 u₁ Ω) (hu₂ : MemWkp (d := d) k 2 u₂ Ω)
    (hv : MemWkp (d := d) k 2 v Ω) :
    wkpInnerL2 (d := d) k (fun x => u₁ x + u₂ x) v Ω =
      wkpInnerL2 (d := d) k u₁ v Ω + wkpInnerL2 (d := d) k u₂ v Ω := by
  classical
  unfold wkpInnerL2
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro j hj
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro β _
  have hj_le : j ≤ k := by rw [Finset.mem_range] at hj; omega
  have h_u₁Wj : MemWkp (d := d) j 2 u₁ Ω := MemWkp.le_of_le hj_le hu₁
  have h_u₂Wj : MemWkp (d := d) j 2 u₂ Ω := MemWkp.le_of_le hj_le hu₂
  have h_vWj : MemWkp (d := d) j 2 v Ω := MemWkp.le_of_le hj_le hv
  have h_iter_add_ae :=
    iterWeakPartial_add_ae (d := d) (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ β h_u₁Wj h_u₂Wj
  have h_iter_u₁ := iterWeakPartial_memLp_of_memWkp (d := d) (p := (2 : ℝ≥0∞)) h_u₁Wj β
  have h_iter_u₂ := iterWeakPartial_memLp_of_memWkp (d := d) (p := (2 : ℝ≥0∞)) h_u₂Wj β
  have h_iter_v := iterWeakPartial_memLp_of_memWkp (d := d) (p := (2 : ℝ≥0∞)) h_vWj β
  have h_int_eq :
      ∫ x in Ω,
        iterWeakPartial (d := d) (2 : ℝ≥0∞) j β (fun x => u₁ x + u₂ x) Ω x *
          iterWeakPartial (d := d) (2 : ℝ≥0∞) j β v Ω x =
      ∫ x in Ω,
        (iterWeakPartial (d := d) (2 : ℝ≥0∞) j β u₁ Ω x +
          iterWeakPartial (d := d) (2 : ℝ≥0∞) j β u₂ Ω x) *
          iterWeakPartial (d := d) (2 : ℝ≥0∞) j β v Ω x := by
    refine integral_congr_ae ?_
    filter_upwards [h_iter_add_ae] with x hx
    rw [hx]
  rw [h_int_eq]
  have h_int₁ : Integrable (fun x =>
      iterWeakPartial (d := d) (2 : ℝ≥0∞) j β u₁ Ω x *
        iterWeakPartial (d := d) (2 : ℝ≥0∞) j β v Ω x) (volume.restrict Ω) :=
    h_iter_u₁.integrable_mul h_iter_v
  have h_int₂ : Integrable (fun x =>
      iterWeakPartial (d := d) (2 : ℝ≥0∞) j β u₂ Ω x *
        iterWeakPartial (d := d) (2 : ℝ≥0∞) j β v Ω x) (volume.restrict Ω) :=
    h_iter_u₂.integrable_mul h_iter_v
  rw [show (fun x =>
      (iterWeakPartial (d := d) (2 : ℝ≥0∞) j β u₁ Ω x +
        iterWeakPartial (d := d) (2 : ℝ≥0∞) j β u₂ Ω x) *
        iterWeakPartial (d := d) (2 : ℝ≥0∞) j β v Ω x) =
      (fun x =>
        iterWeakPartial (d := d) (2 : ℝ≥0∞) j β u₁ Ω x *
          iterWeakPartial (d := d) (2 : ℝ≥0∞) j β v Ω x +
        iterWeakPartial (d := d) (2 : ℝ≥0∞) j β u₂ Ω x *
          iterWeakPartial (d := d) (2 : ℝ≥0∞) j β v Ω x) from by
    funext x; ring]
  exact integral_add h_int₁ h_int₂

/-- Scalar-multiplication identity for the `L²`-Sobolev inner product (left slot). -/
theorem wkpInnerL2_smul_left
    {k : ℕ} {Ω : Set E} (hΩ : IsOpen Ω)
    {u : E → ℝ} (v : E → ℝ)
    (hu : MemWkp (d := d) k 2 u Ω) (c : ℝ) :
    wkpInnerL2 (d := d) k (fun x => c * u x) v Ω =
      c * wkpInnerL2 (d := d) k u v Ω := by
  classical
  unfold wkpInnerL2
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro j hj
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro β _
  have hj_le : j ≤ k := by rw [Finset.mem_range] at hj; omega
  have h_uWj : MemWkp (d := d) j 2 u Ω := MemWkp.le_of_le hj_le hu
  have h_iter_smul_ae :=
    iterWeakPartial_const_smul_ae (d := d) (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ β h_uWj c
  rw [show (∫ x in Ω,
      iterWeakPartial (d := d) (2 : ℝ≥0∞) j β (fun x => c * u x) Ω x *
        iterWeakPartial (d := d) (2 : ℝ≥0∞) j β v Ω x) =
      ∫ x in Ω,
        (c * iterWeakPartial (d := d) (2 : ℝ≥0∞) j β u Ω x) *
          iterWeakPartial (d := d) (2 : ℝ≥0∞) j β v Ω x from by
    refine integral_congr_ae ?_
    filter_upwards [h_iter_smul_ae] with x hx
    rw [hx]]
  rw [show (fun x =>
      (c * iterWeakPartial (d := d) (2 : ℝ≥0∞) j β u Ω x) *
        iterWeakPartial (d := d) (2 : ℝ≥0∞) j β v Ω x) =
      (fun x => c * (iterWeakPartial (d := d) (2 : ℝ≥0∞) j β u Ω x *
        iterWeakPartial (d := d) (2 : ℝ≥0∞) j β v Ω x)) from by
    funext x; ring]
  rw [integral_const_mul]

/-- The `L²`-Sobolev inner product is non-negative on the diagonal. -/
theorem wkpInnerL2_self_nonneg
    (k : ℕ) (u : E → ℝ) (Ω : Set E) :
    0 ≤ wkpInnerL2 (d := d) k u u Ω := by
  classical
  unfold wkpInnerL2
  refine Finset.sum_nonneg ?_
  intro j _
  refine Finset.sum_nonneg ?_
  intro β _
  exact integral_nonneg (fun x => mul_self_nonneg _)

/-- For `u ∈ W^{k,2}(Ω)`, the squared `L²`-Sobolev norm (real-valued) equals
the `L²`-Sobolev inner product `⟨u, u⟩`. -/
theorem wkpNormL2Sq_toReal_eq_wkpInnerL2_self
    {k : ℕ} {u : E → ℝ} {Ω : Set E}
    (hu : MemWkp (d := d) k 2 u Ω) :
    (wkpNormL2Sq (d := d) k u Ω).toReal = wkpInnerL2 (d := d) k u u Ω := by
  classical
  unfold wkpNormL2Sq wkpInnerL2
  rw [ENNReal.toReal_sum]
  · refine Finset.sum_congr rfl ?_
    intro j hj
    rw [ENNReal.toReal_sum]
    · refine Finset.sum_congr rfl ?_
      intro β _
      have hj_le : j ≤ k := by rw [Finset.mem_range] at hj; omega
      have h_uWj : MemWkp (d := d) j 2 u Ω := MemWkp.le_of_le hj_le hu
      have h_iter := iterWeakPartial_memLp_of_memWkp (d := d) (p := (2 : ℝ≥0∞)) h_uWj β
      rw [ENNReal.toReal_pow]
      rw [MemLp.eLpNorm_eq_integral_rpow_norm
          (two_ne_zero) (ENNReal.ofNat_ne_top) h_iter]
      rw [ENNReal.toReal_ofReal (by positivity)]
      rw [show (((((2 : ℝ≥0∞) : ℝ≥0∞).toReal : ℝ))⁻¹) = (2 : ℝ)⁻¹ by norm_num]
      rw [show (((((2 : ℝ≥0∞) : ℝ≥0∞).toReal : ℝ))) = (2 : ℝ) by norm_num]
      have h_pow_eq :
          ((∫ a, ‖iterWeakPartial (d := d) (2 : ℝ≥0∞) j β u Ω a‖ ^ (2 : ℝ)
              ∂(volume.restrict Ω)) ^ ((2 : ℝ)⁻¹)) ^ (2 : ℕ) =
            ∫ a, ‖iterWeakPartial (d := d) (2 : ℝ≥0∞) j β u Ω a‖ ^ (2 : ℝ)
              ∂(volume.restrict Ω) := by
        have h_nn : (0 : ℝ) ≤ ∫ a, ‖iterWeakPartial (d := d) (2 : ℝ≥0∞) j β u Ω a‖ ^ (2 : ℝ)
            ∂(volume.restrict Ω) := by
          apply integral_nonneg
          intro x; positivity
        rw [show (((∫ a, ‖iterWeakPartial (d := d) (2 : ℝ≥0∞) j β u Ω a‖ ^ (2 : ℝ)
            ∂(volume.restrict Ω)) ^ ((2 : ℝ)⁻¹)) ^ (2 : ℕ) : ℝ) =
            ((∫ a, ‖iterWeakPartial (d := d) (2 : ℝ≥0∞) j β u Ω a‖ ^ (2 : ℝ)
              ∂(volume.restrict Ω)) ^ ((2 : ℝ)⁻¹)) ^ ((2 : ℕ) : ℝ) by
          rw [← Real.rpow_natCast]]
        rw [← Real.rpow_mul h_nn]
        rw [show ((2 : ℝ)⁻¹ * ((2 : ℕ) : ℝ)) = 1 by norm_num]
        rw [Real.rpow_one]
      rw [h_pow_eq]
      refine integral_congr_ae ?_
      filter_upwards with x
      rw [Real.norm_eq_abs, show ((2 : ℝ) : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
          Real.rpow_natCast, sq_abs, sq]
    · intro β _
      have hj_le : j ≤ k := by rw [Finset.mem_range] at hj; omega
      have h_uWj : MemWkp (d := d) j 2 u Ω := MemWkp.le_of_le hj_le hu
      have h_iter := iterWeakPartial_memLp_of_memWkp (d := d) (p := (2 : ℝ≥0∞)) h_uWj β
      exact (ENNReal.pow_lt_top h_iter.eLpNorm_lt_top).ne
  · intro j hj
    refine ENNReal.sum_lt_top.mpr ?_ |>.ne
    intro β _
    have hj_le : j ≤ k := by rw [Finset.mem_range] at hj; omega
    have h_uWj : MemWkp (d := d) j 2 u Ω := MemWkp.le_of_le hj_le hu
    have h_iter := iterWeakPartial_memLp_of_memWkp (d := d) (p := (2 : ℝ≥0∞)) h_uWj β
    exact ENNReal.pow_lt_top h_iter.eLpNorm_lt_top

/-- The squared `L²`-Sobolev norm equals the `L²`-Sobolev inner product `⟨u, u⟩`,
in `ℝ≥0∞` (with both sides finite for `MemWkp k 2 u Ω`). -/
theorem wkpNormL2_sq_toReal_eq_wkpInnerL2_self
    {k : ℕ} {u : E → ℝ} {Ω : Set E}
    (hu : MemWkp (d := d) k 2 u Ω) :
    ((wkpNormL2 (d := d) k u Ω).toReal) ^ 2 = wkpInnerL2 (d := d) k u u Ω := by
  rw [show ((wkpNormL2 (d := d) k u Ω).toReal) ^ 2 =
      (wkpNormL2Sq (d := d) k u Ω).toReal by
    have hSq_finite : wkpNormL2Sq (d := d) k u Ω ≠ ∞ :=
      (wkpNormL2Sq_lt_top_of_memWkp (d := d) hu).ne
    rw [wkpNormL2_eq_ofReal_sqrt_toReal hSq_finite]
    rw [ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]
    rw [Real.sq_sqrt ENNReal.toReal_nonneg]]
  exact wkpNormL2Sq_toReal_eq_wkpInnerL2_self (d := d) hu

end Euclidean
end Sobolev
end Analysis
end DifferentialGeometry
