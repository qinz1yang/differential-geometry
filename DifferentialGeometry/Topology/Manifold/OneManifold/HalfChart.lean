import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

/-!
# Charts of one-manifolds with boundary

For a manifold modelled on the closed half-line `EuclideanHalfSpace 1`, a chart is recorded by
its real coordinate `(e x).val 0 ≥ 0`. This file proves:

* `halfPt`: the point of the half-line with a given (nonnegative) coordinate;
* `isInteriorPoint_iff_coord_pos`, `isBoundaryPoint_iff_coord_eq_zero`: a point of a chart
  source is interior iff its coordinate is positive;
* `contDiffOn_coord_transition`: coordinate changes between two charts of the atlas are smooth
  as real functions on the positive half-line.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

noncomputable section

namespace DifferentialGeometry.Topology.Manifold.OneManifold

/-- The point of `EuclideanHalfSpace 1` with coordinate `max t 0`. -/
def halfPt (t : ℝ) : EuclideanHalfSpace 1 :=
  ⟨EuclideanSpace.single 0 (max t 0), by simp⟩

theorem halfPt_val_zero (t : ℝ) : (halfPt t).val 0 = max t 0 := by
  simp [halfPt]

theorem halfPt_val_zero_of_nonneg {t : ℝ} (ht : 0 ≤ t) : (halfPt t).val 0 = t := by
  rw [halfPt_val_zero, max_eq_left ht]

theorem val_eq_single (y : EuclideanSpace ℝ (Fin 1)) : y = EuclideanSpace.single 0 (y 0) := by
  ext i
  fin_cases i
  simp

theorem halfPt_coord (y : EuclideanHalfSpace 1) : halfPt (y.val 0) = y := by
  apply Subtype.ext
  change EuclideanSpace.single 0 (max (y.val 0) 0) = y.val
  rw [max_eq_left y.2]
  exact (val_eq_single y.val).symm

theorem continuous_halfPt : Continuous halfPt := by
  apply Continuous.subtype_mk
  have h : (fun t : ℝ => EuclideanSpace.single (0 : Fin 1) (max t 0)) =
      fun t => (max t 0) • EuclideanSpace.single (0 : Fin 1) (1 : ℝ) := by
    funext t
    ext i
    fin_cases i
    simp
  rw [h]
  exact (continuous_id.max continuous_const).smul continuous_const

theorem continuous_coord : Continuous (fun y : EuclideanHalfSpace 1 => y.val 0) :=
  (EuclideanSpace.proj (0 : Fin 1) : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ).continuous.comp
    continuous_subtype_val

theorem coord_injective {y y' : EuclideanHalfSpace 1} (h : y.val 0 = y'.val 0) : y = y' := by
  rw [← halfPt_coord y, ← halfPt_coord y', h]

theorem model_halfPt {t : ℝ} (ht : 0 ≤ t) :
    (𝓡∂ 1) (halfPt t) = EuclideanSpace.single 0 t := by
  change EuclideanSpace.single 0 (max t 0) = _
  rw [max_eq_left ht]

theorem model_symm_single {t : ℝ} (ht : 0 ≤ t) :
    (𝓡∂ 1).symm (EuclideanSpace.single 0 t) = halfPt t := by
  rw [← model_halfPt ht, ModelWithCorners.left_inv]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 1) M]
  [IsManifold (𝓡∂ 1) ∞ M]

theorem isInteriorPoint_iff_coord_pos {e : OpenPartialHomeomorph M (EuclideanHalfSpace 1)}
    (he : e ∈ atlas (EuclideanHalfSpace 1) M) {x : M} (hx : x ∈ e.source) :
    (𝓡∂ 1).IsInteriorPoint x ↔ 0 < (e x).val 0 := by
  rw [(𝓡∂ 1).isInteriorPoint_iff_of_mem_atlas (n := ∞) (by simp) he hx]
  have hext : e.extend (𝓡∂ 1) x = (e x).val := rfl
  constructor
  · intro h
    have h2 : e.extend (𝓡∂ 1) x ∈ interior (range (𝓡∂ 1)) :=
      interior_mono (e.extend_target_subset_range (I := 𝓡∂ 1)) h
    rw [interior_range_modelWithCornersEuclideanHalfSpace] at h2
    simpa [hext] using h2
  · intro h
    rw [mem_interior]
    refine ⟨(𝓡∂ 1).symm ⁻¹' e.target ∩ interior (range (𝓡∂ 1)), ?_, ?_, ?_⟩
    · rintro y ⟨hy1, hy2⟩
      rw [e.extend_target]
      exact ⟨hy1, interior_subset hy2⟩
    · exact ((𝓡∂ 1).continuous_symm.isOpen_preimage _ e.open_target).inter isOpen_interior
    · refine ⟨?_, ?_⟩
      · change (𝓡∂ 1).symm ((𝓡∂ 1) (e x)) ∈ e.target
        rw [ModelWithCorners.left_inv]
        exact e.map_source hx
      · rw [interior_range_modelWithCornersEuclideanHalfSpace]
        exact h

theorem isBoundaryPoint_iff_coord_eq_zero {e : OpenPartialHomeomorph M (EuclideanHalfSpace 1)}
    (he : e ∈ atlas (EuclideanHalfSpace 1) M) {x : M} (hx : x ∈ e.source) :
    (𝓡∂ 1).IsBoundaryPoint x ↔ (e x).val 0 = 0 := by
  have h := (𝓡∂ 1).isInteriorPoint_iff_not_isBoundaryPoint x
  rw [isInteriorPoint_iff_coord_pos he hx] at h
  constructor
  · intro hb
    exact le_antisymm (not_lt.mp fun hlt => h.mp hlt hb) (e x).2
  · intro h0
    by_contra hb
    have hpos := h.mpr hb
    rw [h0] at hpos
    exact lt_irrefl _ hpos

theorem contDiffOn_coord_transition {e e' : OpenPartialHomeomorph M (EuclideanHalfSpace 1)}
    (he : e ∈ atlas (EuclideanHalfSpace 1) M) (he' : e' ∈ atlas (EuclideanHalfSpace 1) M) :
    ContDiffOn ℝ ∞ (fun t : ℝ => (e' (e.symm (halfPt t))).val 0)
      {t | 0 < t ∧ halfPt t ∈ e.target ∧ e.symm (halfPt t) ∈ e'.source} := by
  have hc := (𝓡∂ 1).contDiffOn_extendCoordChange (n := ∞)
    (IsManifold.subset_maximalAtlas he) (IsManifold.subset_maximalAtlas he')
  have hsingle : ContDiff ℝ ∞ (fun t : ℝ => EuclideanSpace.single (0 : Fin 1) t) := by
    have h : (fun t : ℝ => EuclideanSpace.single (0 : Fin 1) t) =
        fun t => t • EuclideanSpace.single (0 : Fin 1) (1 : ℝ) := by
      funext t
      ext i
      fin_cases i
      simp
    rw [h]
    exact contDiff_id.smul contDiff_const
  have hmaps : MapsTo (fun t : ℝ => EuclideanSpace.single (0 : Fin 1) t)
      {t | 0 < t ∧ halfPt t ∈ e.target ∧ e.symm (halfPt t) ∈ e'.source}
      ((𝓡∂ 1).extendCoordChange e e').source := by
    rintro t ⟨ht, hte, hte'⟩
    rw [(𝓡∂ 1).extendCoordChange_source]
    exact ⟨halfPt t, ⟨hte, hte'⟩, model_halfPt ht.le⟩
  have hcomp := ((EuclideanSpace.proj (0 : Fin 1) : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ).contDiff
    ).comp_contDiffOn (hc.comp hsingle.contDiffOn hmaps)
  refine hcomp.congr ?_
  rintro t ⟨ht, -, -⟩
  change (e' (e.symm (halfPt t))).val 0 =
    ((𝓡∂ 1) (e' (e.symm ((𝓡∂ 1).symm (EuclideanSpace.single 0 t))))) 0
  rw [model_symm_single ht.le]
  rfl

end DifferentialGeometry.Topology.Manifold.OneManifold
