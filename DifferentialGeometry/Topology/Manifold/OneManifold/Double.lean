import DifferentialGeometry.Topology.Manifold.OneManifold.BoundaryFunction

/-!
# The double of a compact one-manifold with boundary

`Double M = {(x, s) ∈ M × ℝ | |s| = bdryFn x}` is two copies of `M` (the sheets `s ≥ 0` and
`s ≤ 0`) glued along the boundary. It carries a smooth boundaryless atlas modelled on `ℝ`:

* at a point with `s = 0` (a boundary point `p` of `M`), the fold chart `(x, s) ↦ s` on
  `bdryNbhd p`, whose inverse is `s ↦ (chart⁻¹ (r |s|), s)`;
* at a point with `s ≠ 0`, the sheet chart `(x, s) ↦ chart coordinate of x` on one sheet.

Coordinate changes are compositions of coordinate changes of `M` with `s ↦ ± r s`, so the
double is a compact `T₂` smooth one-manifold without boundary.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

noncomputable section

namespace DifferentialGeometry.Topology.Manifold.OneManifold

/-- The sign of a real number, with value `1` at `0`. -/
def sgn (s : ℝ) : ℝ := if 0 ≤ s then 1 else -1

theorem abs_sgn (s : ℝ) : |sgn s| = 1 := by
  unfold sgn
  split_ifs <;> simp

theorem sgn_mul_abs (s : ℝ) : sgn s * |s| = s := by
  unfold sgn
  split_ifs with h
  · rw [one_mul, abs_of_nonneg h]
  · rw [abs_of_neg (not_le.mp h)]
    ring

theorem sgn_mul_self (s : ℝ) : sgn s * s = |s| := by
  unfold sgn
  split_ifs with h
  · rw [one_mul, abs_of_nonneg h]
  · rw [abs_of_neg (not_le.mp h)]
    ring

theorem sgn_mul_sgn (s : ℝ) : sgn s * sgn s = 1 := by
  unfold sgn
  split_ifs <;> norm_num

theorem mul_eq_abs_of_pos {σ a : ℝ} (hσ : |σ| = 1) (h : 0 < σ * a) : σ * a = |a| := by
  rw [← abs_of_pos h, abs_mul, hσ, one_mul]

theorem mul_abs_eq_of_pos {σ a : ℝ} (hσ : |σ| = 1) (h : 0 < σ * a) : σ * |a| = a := by
  rw [← mul_eq_abs_of_pos hσ h, ← mul_assoc]
  rcases abs_eq (zero_le_one' ℝ) |>.mp hσ with h1 | h1 <;> rw [h1] <;> ring

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 1) M]
  [IsManifold (𝓡∂ 1) ∞ M] [CompactSpace M]

variable (M) in
/-- The double of a compact one-manifold with boundary. -/
abbrev Double := {q : M × ℝ // |q.2| = bdryFn q.1}

theorem double_snd_abs (q : Double M) : |q.1.2| = bdryFn q.1.1 := q.2

/-! ### Fold charts -/

/-- The point of `M` with fold coordinate `s` near the boundary point `p`. -/
def foldPoint (p : Bdry M) (s : ℝ) : M :=
  (chartAt (EuclideanHalfSpace 1) p.1).symm (halfPt (bdryRadius p * |s|))

/-- The inverse of the fold chart at `p`. -/
def foldInv (p : Bdry M) (s : ℝ) : Double M :=
  ⟨(foldPoint p s, sgn s * bdryFn (foldPoint p s)), by
    change |sgn s * bdryFn (foldPoint p s)| = bdryFn (foldPoint p s)
    rw [abs_mul, abs_sgn, one_mul, abs_of_nonneg (bdryFn_nonneg _)]⟩

/-- The target of the fold chart at `p`. -/
def foldTarget (p : Bdry M) : Set ℝ :=
  {s | halfPt (bdryRadius p * |s|) ∈ (chartAt (EuclideanHalfSpace 1) p.1).target ∧
    foldPoint p s ∈ bdryNbhd p}

theorem radius_mul_abs_of_mem_bdryNbhd (p : Bdry M) (q : Double M) (hq : q.1.1 ∈ bdryNbhd p) :
    bdryRadius p * |q.1.2| = chartCoord (chartAt (EuclideanHalfSpace 1) p.1) q.1.1 := by
  rw [double_snd_abs, bdryFn_eq_on_bdryNbhd p hq]
  field_simp [(bdryRadius_pos p).ne']

theorem foldPoint_snd (p : Bdry M) (q : Double M) (hq : q.1.1 ∈ bdryNbhd p) :
    foldPoint p q.1.2 = q.1.1 := by
  unfold foldPoint
  rw [radius_mul_abs_of_mem_bdryNbhd p q hq, halfPt_chartCoord,
    (chartAt _ p.1).left_inv (bdryNbhd_subset_source p hq)]

theorem bdryFn_foldPoint (p : Bdry M) {s : ℝ} (hs : s ∈ foldTarget p) :
    bdryFn (foldPoint p s) = |s| := by
  rw [bdryFn_eq_on_bdryNbhd p hs.2]
  unfold foldPoint
  rw [chartCoord_symm_halfPt _ (mul_nonneg (bdryRadius_pos p).le (abs_nonneg s)) hs.1]
  field_simp [(bdryRadius_pos p).ne']

theorem foldInv_snd (p : Bdry M) {s : ℝ} (hs : s ∈ foldTarget p) : (foldInv p s).1.2 = s := by
  change sgn s * bdryFn (foldPoint p s) = s
  rw [bdryFn_foldPoint p hs, sgn_mul_abs]

omit [CompactSpace M] in
theorem continuous_radius_halfPt (p : Bdry M) :
    Continuous fun s : ℝ => halfPt (bdryRadius p * |s|) :=
  continuous_halfPt.comp (continuous_const.mul continuous_abs)

omit [CompactSpace M] in
theorem continuousOn_foldPoint (p : Bdry M) : ContinuousOn (foldPoint p) (foldTarget p) :=
  (chartAt (EuclideanHalfSpace 1) p.1).continuousOn_symm.comp
    (continuous_radius_halfPt p).continuousOn fun _ hs => hs.1

/-- The fold chart at a boundary point `p`: `(x, s) ↦ s` near `(p, 0)`. -/
def foldChart [T2Space M] (p : Bdry M) : OpenPartialHomeomorph (Double M) ℝ where
  toFun q := q.1.2
  invFun := foldInv p
  source := {q | q.1.1 ∈ bdryNbhd p}
  target := foldTarget p
  map_source' := by
    intro q hq
    refine ⟨?_, by rw [foldPoint_snd p q hq]; exact hq⟩
    rw [radius_mul_abs_of_mem_bdryNbhd p q hq, halfPt_chartCoord]
    exact (chartAt _ p.1).map_source (bdryNbhd_subset_source p hq)
  map_target' := fun _ hs => hs.2
  left_inv' := by
    intro q hq
    apply Subtype.ext
    apply Prod.ext
    · exact foldPoint_snd p q hq
    · change sgn q.1.2 * bdryFn (foldPoint p q.1.2) = q.1.2
      rw [foldPoint_snd p q hq, ← double_snd_abs, sgn_mul_abs]
  right_inv' := fun _ hs => foldInv_snd p hs
  open_source := (isOpen_bdryNbhd p).preimage (continuous_fst.comp continuous_subtype_val)
  open_target := ((chartAt (EuclideanHalfSpace 1) p.1).isOpen_inter_preimage_symm
    (isOpen_bdryNbhd p)).preimage (continuous_radius_halfPt p)
  continuousOn_toFun := (continuous_snd.comp continuous_subtype_val).continuousOn
  continuousOn_invFun := by
    have hc : ContinuousOn (fun s => (foldInv p s).1) (foldTarget p) :=
      ((continuousOn_foldPoint p).prodMk continuousOn_id).congr fun s hs =>
        Prod.ext rfl (foldInv_snd p hs)
    exact Topology.IsEmbedding.subtypeVal.isInducing.continuousOn_iff.mpr hc

/-! ### Sheet charts -/

/-- The inverse of the sheet chart built on a chart `e` of `M`, on the sheet of sign `sgn s₀`. -/
def sheetInv (e : OpenPartialHomeomorph M (EuclideanHalfSpace 1)) (s₀ t : ℝ) : Double M :=
  ⟨(e.symm (halfPt t), sgn s₀ * bdryFn (e.symm (halfPt t))), by
    change |sgn s₀ * bdryFn (e.symm (halfPt t))| = bdryFn (e.symm (halfPt t))
    rw [abs_mul, abs_sgn, one_mul, abs_of_nonneg (bdryFn_nonneg _)]⟩

theorem not_mem_boundary_of_snd_ne_zero (q : Double M) (hq : q.1.2 ≠ 0) :
    q.1.1 ∉ (𝓡∂ 1).boundary M := by
  rw [← bdryFn_pos_iff, ← double_snd_abs]
  exact abs_pos.mpr hq

theorem chartCoord_pos_of_snd_ne_zero {e : OpenPartialHomeomorph M (EuclideanHalfSpace 1)}
    (he : e ∈ atlas (EuclideanHalfSpace 1) M) (q : Double M) (hs : q.1.1 ∈ e.source)
    (hq : q.1.2 ≠ 0) : 0 < chartCoord e q.1.1 := by
  refine (isInteriorPoint_iff_coord_pos he hs).mp ?_
  rw [(𝓡∂ 1).isInteriorPoint_iff_not_isBoundaryPoint]
  exact not_mem_boundary_of_snd_ne_zero q hq

theorem bdryFn_symm_halfPt_pos {e : OpenPartialHomeomorph M (EuclideanHalfSpace 1)}
    (he : e ∈ atlas (EuclideanHalfSpace 1) M) {t : ℝ} (ht : 0 < t) (hte : halfPt t ∈ e.target) :
    0 < bdryFn (e.symm (halfPt t)) := by
  rw [bdryFn_pos_iff]
  have hint : (𝓡∂ 1).IsInteriorPoint (e.symm (halfPt t)) := by
    rw [isInteriorPoint_iff_coord_pos he (e.map_target hte)]
    change 0 < chartCoord e (e.symm (halfPt t))
    rw [chartCoord_symm_halfPt e ht.le hte]
    exact ht
  exact (𝓡∂ 1).isInteriorPoint_iff_not_isBoundaryPoint _ |>.mp hint

/-- The sheet chart: on the sheet of sign `sgn s₀` over the source of a chart `e` of `M`,
`(x, s) ↦ chart coordinate of x`. -/
def sheetChart [T2Space M] (e : OpenPartialHomeomorph M (EuclideanHalfSpace 1))
    (he : e ∈ atlas (EuclideanHalfSpace 1) M) (s₀ : ℝ) : OpenPartialHomeomorph (Double M) ℝ where
  toFun q := chartCoord e q.1.1
  invFun := sheetInv e s₀
  source := {q | q.1.1 ∈ e.source ∧ 0 < sgn s₀ * q.1.2}
  target := {t | 0 < t ∧ halfPt t ∈ e.target}
  map_source' := by
    intro q hq
    have hne : q.1.2 ≠ 0 := by
      intro h
      have hq2 : 0 < sgn s₀ * q.1.2 := hq.2
      rw [h, mul_zero] at hq2
      exact lt_irrefl 0 hq2
    refine ⟨chartCoord_pos_of_snd_ne_zero he q hq.1 hne, ?_⟩
    rw [halfPt_chartCoord]
    exact e.map_source hq.1
  map_target' := by
    intro t ht
    refine ⟨e.map_target ht.2, ?_⟩
    change 0 < sgn s₀ * (sgn s₀ * bdryFn (e.symm (halfPt t)))
    rw [← mul_assoc, sgn_mul_sgn, one_mul]
    exact bdryFn_symm_halfPt_pos he ht.1 ht.2
  left_inv' := by
    intro q hq
    apply Subtype.ext
    apply Prod.ext
    · change e.symm (halfPt (chartCoord e q.1.1)) = q.1.1
      rw [halfPt_chartCoord, e.left_inv hq.1]
    · change sgn s₀ * bdryFn (e.symm (halfPt (chartCoord e q.1.1))) = q.1.2
      rw [halfPt_chartCoord, e.left_inv hq.1, ← double_snd_abs]
      exact mul_abs_eq_of_pos (abs_sgn s₀) hq.2
  right_inv' := fun t ht => chartCoord_symm_halfPt e ht.1.le ht.2
  open_source := (e.open_source.preimage (continuous_fst.comp continuous_subtype_val)).inter
    (isOpen_lt continuous_const
      (continuous_const.mul (continuous_snd.comp continuous_subtype_val)))
  open_target := isOpen_Ioi.inter (e.open_target.preimage continuous_halfPt)
  continuousOn_toFun :=
    (continuousOn_chartCoord e).comp (continuous_fst.comp continuous_subtype_val).continuousOn
      fun _ hq => hq.1
  continuousOn_invFun := by
    have hp : ContinuousOn (fun t : ℝ => e.symm (halfPt t)) {t | 0 < t ∧ halfPt t ∈ e.target} :=
      e.continuousOn_symm.comp continuous_halfPt.continuousOn fun _ ht => ht.2
    have hc : ContinuousOn (fun t => (sheetInv e s₀ t).1) {t | 0 < t ∧ halfPt t ∈ e.target} :=
      hp.prodMk (continuousOn_const.mul (continuous_bdryFn.comp_continuousOn hp))
    exact Topology.IsEmbedding.subtypeVal.isInducing.continuousOn_iff.mpr hc

/-! ### The atlas -/

theorem mem_boundary_of_snd_eq_zero (q : Double M) (h : q.1.2 = 0) :
    q.1.1 ∈ (𝓡∂ 1).boundary M := by
  rw [← bdryFn_eq_zero_iff, ← double_snd_abs, h, abs_zero]

/-- The preferred chart of the double at a point. -/
def doubleChartAt [T2Space M] (q : Double M) : OpenPartialHomeomorph (Double M) ℝ :=
  if h : q.1.2 = 0 then foldChart ⟨q.1.1, mem_boundary_of_snd_eq_zero q h⟩
  else sheetChart (chartAt (EuclideanHalfSpace 1) q.1.1) (chart_mem_atlas _ _) q.1.2

theorem mem_doubleChartAt_source [T2Space M] (q : Double M) : q ∈ (doubleChartAt q).source := by
  unfold doubleChartAt
  split_ifs with h
  · exact mem_bdryNbhd_self ⟨q.1.1, mem_boundary_of_snd_eq_zero q h⟩
  · refine ⟨mem_chart_source _ q.1.1, ?_⟩
    rw [sgn_mul_self]
    exact abs_pos.mpr h

instance [T2Space M] : ChartedSpace ℝ (Double M) where
  atlas := range doubleChartAt
  chartAt := doubleChartAt
  mem_chart_source := mem_doubleChartAt_source
  chart_mem_atlas q := ⟨q, rfl⟩

end DifferentialGeometry.Topology.Manifold.OneManifold
