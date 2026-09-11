import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Analysis.Calculus.LocalExtr.Basic

open Set Function Topology
open scoped Manifold ContDiff
set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.Manifold.BoundaryCollar

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]


def chartHeight (p : M) (y : M) : ℝ := extChartAt (𝓡∂ n) p y 0

theorem chartHeight_nonneg (p y : M) : 0 ≤ chartHeight (n := n) p y :=
  (chartAt (EuclideanHalfSpace n) p y).property


theorem contMDiffOn_chartHeight {k : ℕ∞ω} [IsManifold (𝓡∂ n) k M] (p : M) :
    ContMDiffOn (𝓡∂ n) 𝓘(ℝ, ℝ) k (chartHeight (n := n) p)
      (chartAt (EuclideanHalfSpace n) p).source := by
  exact (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin n)).contMDiff.comp_contMDiffOn contMDiffOn_extChartAt

variable [IsManifold (𝓡∂ n) 1 M]


theorem chartHeight_eq_zero_iff (p : M) {y : M}
    (hy : y ∈ (chartAt (EuclideanHalfSpace n) p).source) :
    chartHeight (n := n) p y = 0 ↔ (𝓡∂ n).IsBoundaryPoint y := by
  have hi : (𝓡∂ n).IsInteriorPoint y ↔ 0 < chartHeight (n := n) p y := by
    rw [ModelWithCorners.isInteriorPoint_iff_of_mem_atlas (n := 1) one_ne_zero
      (chart_mem_atlas (EuclideanHalfSpace n) p) hy]
    constructor
    · intro h
      have hh := OpenPartialHomeomorph.interior_extend_target_subset_interior_range
        (chartAt (EuclideanHalfSpace n) p) h
      simpa only [interior_range_modelWithCornersEuclideanHalfSpace] using! hh
    · intro h
      apply (chartAt (EuclideanHalfSpace n) p).mem_interior_extend_target
        ((chartAt (EuclideanHalfSpace n) p).map_source hy)
      simpa only [interior_range_modelWithCornersEuclideanHalfSpace] using! h
  rw [ModelWithCorners.isBoundaryPoint_iff_not_isInteriorPoint, hi]
  exact ⟨fun h => by rw [h]; exact lt_irrefl _,
    fun h => le_antisymm (not_lt.mp h) (chartHeight_nonneg (n := n) p y)⟩

theorem mfderiv_chartHeight (p : M) {y : M}
    (hy : y ∈ (chartAt (EuclideanHalfSpace n) p).source) :
    mfderiv (𝓡∂ n) 𝓘(ℝ, ℝ) (chartHeight (n := n) p) y =
      (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin n)).comp
        (mfderiv (𝓡∂ n) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (extChartAt (𝓡∂ n) p) y) := by
  have hh := mfderiv_comp y
    ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin n)).differentiableAt.mdifferentiableAt) (mdifferentiableAt_extChartAt (I := 𝓡∂ n) (x := p) hy)
  simpa only [mfderiv_eq_fderiv, ContinuousLinearMap.fderiv] using! hh

theorem mfderiv_chartHeight_ne_zero (p : M) {y : M}
    (hy : y ∈ (chartAt (EuclideanHalfSpace n) p).source) :
    mfderiv (𝓡∂ n) 𝓘(ℝ, ℝ) (chartHeight (n := n) p) y ≠ 0 := by
  rw [mfderiv_chartHeight (n := n) p hy]
  intro h
  have hyext : y ∈ (extChartAt (𝓡∂ n) p).source := by simpa only [extChartAt_source] using hy
  obtain ⟨v, hv⟩ := (isInvertible_mfderiv_extChartAt (I := 𝓡∂ n) (x := p) (y := y) hyext).surjective
    (EuclideanSpace.single (0 : Fin n) (1 : ℝ))
  have hh := congrArg (fun L : TangentSpace (𝓡∂ n) y →L[ℝ] ℝ => L v) h
  change (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin n))
    ((mfderiv (𝓡∂ n) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (extChartAt (𝓡∂ n) p) y) v) = 0 at hh
  erw [hv] at hh
  norm_num [EuclideanSpace.proj] at hh

omit [IsManifold (𝓡∂ n) 1 M] in
private theorem mfderiv_nonneg_of_nonneg {f : M → ℝ} {y : M}
    (hf : MDifferentiableAt (𝓡∂ n) 𝓘(ℝ, ℝ) f y)
    (hy : (𝓡∂ n).IsBoundaryPoint y) (hf0 : f y = 0) (hpos : ∀ᶠ x in 𝓝 y, 0 ≤ f x)
    {v : EuclideanSpace ℝ (Fin n)} (hv : 0 ≤ v 0) :
    @LE.le ℝ inferInstance 0 (mfderiv (𝓡∂ n) 𝓘(ℝ, ℝ) f y v) := by
  let z := extChartAt (𝓡∂ n) y y
  have hz : z 0 = 0 := by
    have hh := hy
    rw [ModelWithCorners.isBoundaryPoint_iff,
      frontier_range_modelWithCornersEuclideanHalfSpace] at hh
    exact hh.symm
  have hmin : IsLocalMinOn (writtenInExtChartAt (𝓡∂ n) 𝓘(ℝ, ℝ) y f)
      (range (𝓡∂ n)) z := by
    filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (extChartAt_preimage_mem_nhds (I := 𝓡∂ n) hpos)] with w hw
    change f ((extChartAt (𝓡∂ n) y).symm z) ≤ f ((extChartAt (𝓡∂ n) y).symm w)
    rw [extChartAt_to_inv, hf0]
    exact hw
  rw [hf.mfderiv]
  apply hmin.fderivWithin_nonneg
  apply mem_posTangentConeAt_of_segment_subset
  apply (𝓡∂ n).convex_range.segment_subset
  · exact mem_range_self _
  · rw [range_modelWithCornersEuclideanHalfSpace]
    change 0 ≤ (z + v) 0
    simpa only [PiLp.add_apply, hz, zero_add] using hv

omit [IsManifold (𝓡∂ n) 1 M] in
theorem mfderiv_eq_pos_smul_proj_of_nonneg {f : M → ℝ} {y : M}
    (hf : MDifferentiableAt (𝓡∂ n) 𝓘(ℝ, ℝ) f y)
    (hy : (𝓡∂ n).IsBoundaryPoint y) (hf0 : f y = 0) (hpos : ∀ᶠ x in 𝓝 y, 0 ≤ f x)
    (hreg : mfderiv (𝓡∂ n) 𝓘(ℝ, ℝ) f y ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ mfderiv (𝓡∂ n) 𝓘(ℝ, ℝ) f y =
      c • EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin n) := by
  let L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := mfderiv (𝓡∂ n) 𝓘(ℝ, ℝ) f y
  let u := EuclideanSpace.single (0 : Fin n) (1 : ℝ)
  have hu : u 0 = 1 := by simp [u]
  have hnonneg := fun v hv => mfderiv_nonneg_of_nonneg hf hy hf0 hpos (v := v) hv
  have hker (v : EuclideanSpace ℝ (Fin n)) (hv : v 0 = 0) : L v = 0 := by
    apply le_antisymm
    · have hh := hnonneg (-v) (by simp only [PiLp.neg_apply, hv, neg_zero, le_refl])
      change 0 ≤ L (-v) at hh
      simpa only [map_neg, neg_nonneg] using hh
    · exact hnonneg v (le_of_eq hv.symm)
  have hL : L = (L u) • EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin n) := by
    ext v
    have hh := hker (v - (v 0) • u) (by simp only [PiLp.sub_apply, PiLp.smul_apply, hu,
      smul_eq_mul, mul_one, sub_self])
    change L v = L u * v 0
    simpa only [map_sub, map_smul, smul_eq_mul, sub_eq_zero, mul_comm] using hh
  refine ⟨L u, lt_of_le_of_ne (hnonneg u (by rw [hu]; exact zero_le_one)) ?_, hL⟩
  intro hh
  apply hreg
  change L = 0
  rw [hL, ← hh, zero_smul]

theorem mfderiv_chartHeight_eq_pos_smul_proj (p : M) {y : M}
    (hy : y ∈ (chartAt (EuclideanHalfSpace n) p).source)
    (hb : (𝓡∂ n).IsBoundaryPoint y) :
    ∃ c : ℝ, 0 < c ∧ mfderiv (𝓡∂ n) 𝓘(ℝ, ℝ) (chartHeight (n := n) p) y =
      c • EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin n) :=
  mfderiv_eq_pos_smul_proj_of_nonneg
    (((contMDiffOn_chartHeight (n := n) p).contMDiffAt
      ((chartAt (EuclideanHalfSpace n) p).open_source.mem_nhds hy)).mdifferentiableAt one_ne_zero)
    hb ((chartHeight_eq_zero_iff (n := n) p hy).mpr hb) (Filter.Eventually.of_forall (chartHeight_nonneg (n := n) p))
    (mfderiv_chartHeight_ne_zero (n := n) p hy)

end DifferentialGeometry.Manifold.BoundaryCollar
