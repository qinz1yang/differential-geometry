import DifferentialGeometry.Geometry.Collapse.BoundaryCloud.BlockIsolation
import DifferentialGeometry.Geometry.Collapse.BoundaryCloud.ModelBlock
import DifferentialGeometry.Geometry.Collapse.BoundaryCloud.ExactMarker
import DifferentialGeometry.Geometry.Collapse.BoundaryCloud.TorusCollar
import DifferentialGeometry.Geometry.Collapse.BoundaryCloud.SupportLists
import DifferentialGeometry.Geometry.Collapse.BoundaryCloud.AffineHeight
import DifferentialGeometry.Geometry.Collapse.BoundaryCloud.RetainedFaces
import DifferentialGeometry.Geometry.Collapse.BoundaryCloud.Decomposition

/-!
# Row-level consequences of the BCG/BCF kernels (blueprint 207B, B:8699–9976)

Concrete consumers that combine the kernels into the printed numerical row statements:
* `exists_modelBlock_derivative_bounds` — (BCG03.b) with ONE early constant `P` for every reference.
* `subsingleton_supports_meeting_reference_ball` — BCG01: at most one boundary support meets `D_a`.
* `abs_height_sub_forty_lt_thousandth` — BCG06: the frontier lies in `39.999 < η_b < 40.001`.
* `boundary_marker_eq_one_of_near_band_point` — BCG05: marker exactly one at the core preimage.
* `boundary_block_eq_zero_of_stages` — BCG04: zero physical block through all stages.
* `exists_slim_base_interval_union` — BCF01: the chartwise `K₃` for a compact base interval.
-/

set_option autoImplicit false
open Set Metric
open scoped BigOperators

namespace DifferentialGeometry.Geometry.Collapse.BoundaryCloud

open DifferentialGeometry.Analysis

/-- (BCG03.b) with one early constant: `‖DΦ_{a,b}‖ ≤ P` and `‖D²Φ_{a,b}‖ ≤ R_a P` for every
reference radius `R_a > 0`, centering and row of norm at most one. -/
theorem exists_modelBlock_derivative_bounds (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    ∃ P : ℝ, 1 ≤ P ∧ ∀ (s₀ R : ℝ) (A : E →L[ℝ] ℝ) (z₀ z : E), 0 < R → ‖A‖ ≤ 1 →
      ‖fderiv ℝ (modelBlock s₀ R A z₀) z‖ ≤ P ∧
        ‖fderiv ℝ (fderiv ℝ (modelBlock s₀ R A z₀)) z‖ ≤ R * P := by
  obtain ⟨P, hP1, hP, hP'⟩ := exists_boundaryBlock_deriv_bounds
  exact ⟨P, hP1, fun s₀ R A z₀ z hR hA =>
    ⟨norm_fderiv_modelBlock_le s₀ hR.ne' hA hP z₀ z,
      norm_fderiv_fderiv_modelBlock_le s₀ hR hA hP' z₀ z⟩⟩

/-- BCG01: with BCP03's separation `≥ 1` between distinct closed boundary supports, at most one of
them meets the original reference domain `D_a = B(p_a, C_a R_a)`. -/
theorem subsingleton_supports_meeting_reference_ball {X ι : Type*} [PseudoMetricSpace X]
    (S : ι → Set X) (hsep : ∀ i j, i ≠ j → ∀ x ∈ S i, ∀ y ∈ S j, 1 ≤ dist x y)
    {p : X} {C R L r : ℝ} (hC : C ≤ 95 / 100 * L) (hL : 0 < L) (hR0 : 0 ≤ R) (hR : R < 2 * r)
    (hr : r * (1000 * L) < 1) :
    {i | (S i ∩ ball p (C * R)).Nonempty}.Subsingleton := by
  intro i hi j hj
  refine eq_of_supports_meet_small_set S (ball p (C * R)) hsep (fun x hx y hy => ?_) hi hj
  have := dist_lt_of_mem_reference_ball hC hL hR0 hR hr hx hy
  linarith

/-- BCG06: on the internal frontier `u_b = 40 v_b`, `v_b ≥ .9`, with block errors `< ε_∂ < 10⁻⁶`,
the height satisfies `|η_b - 40| < .001` (every point of the full preimage). -/
theorem abs_height_sub_forty_lt_thousandth {u v η ζ ε : ℝ} (hu : |u - η * ζ| < ε)
    (hv : |v - ζ| < ε) (hv9 : 9 / 10 ≤ v) (hε : ε < 1 / 1000000) (heq : u = 40 * v) :
    |η - 40| < 1 / 1000 :=
  (abs_height_sub_forty_lt_of_frontier hu hv hv9 (by linarith) heq).trans
    (height_frontier_bound hε)

/-- BCG05 at a contributing center: if the core point has band height `32 ≤ η_b(p) ≤ 78` and the
center's actual core preimage `q_y` has physical block within `r_∂ < 10⁻⁴`, the original marker at
`q_y` is exactly one and `31 < η_b(q_y) < 79`. -/
theorem boundary_marker_eq_one_of_near_band_point {s t r : ℝ} (ht : t ∈ Icc (32 : ℝ) 78)
    (hnear : ‖boundaryBlock s - boundaryBlock t‖ < r) (hr : r < 1 / 10000) :
    s ∈ Ioo (31 : ℝ) 79 ∧ boundaryProfile s = 1 := by
  obtain ⟨hclose, hone⟩ := abs_sub_lt_and_boundaryProfile_eq_one_of_block_near ht hnear hr
  exact ⟨⟨by linarith [(abs_lt.mp hclose).1, ht.1], by linarith [(abs_lt.mp hclose).2, ht.2]⟩,
    hone⟩

/-- BCG04: through all stages the WHOLE physical block stays zero when every active stage output is a
zero of the spectral section of a contributor list with zero block centers and block-kernel planes. -/
theorem boundary_block_eq_zero_of_stages {H A : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [FiniteDimensional ℝ H] (V : Submodule ℝ H) (f g : ℕ → H)
    (t : ℕ → ℝ) (n : ℕ) (s : Set ℝ) (hs : (1 : ℝ) ∈ s)
    (hstep : ∀ j < n, f (j + 1) = f j + t j • (g j - f j))
    (hcontrib : ∀ j < n, t j ≠ 0 → V.starProjection (f j) = 0 →
      ∃ (S : Finset A) (L : A → Submodule ℝ H) (x : A → H) (w : A → ℝ),
        ∑ i ∈ S, w i = 1 ∧ (∀ i ∈ S, w i ≠ 0 → L i ≤ Vᗮ) ∧
        (∀ i ∈ S, w i ≠ 0 → V.starProjection (x i) = 0) ∧
        ∑ i ∈ S, w i • (⨆ a ∈ s, Module.End.eigenspace
          (∑ k ∈ S, w k • (L k)ᗮ.starProjection).toLinearMap a).starProjection (g j - x i) = 0)
    (h0 : V.starProjection (f 0) = 0) : ∀ j ≤ n, V.starProjection (f j) = 0 :=
  starProjection_stages_eq_of_contributors V 0 f g t n s hs hstep hcontrib h0

/-- BCF01 on a base chart interval: the slab image `[α, β]` inside an open base interval
`(α', β')` lies in the interior of a finite union of closed intervals inside `(α', β')` whose
frontier avoids the finite face set. -/
theorem exists_slim_base_interval_union {α β α' β' : ℝ} (hα : α' < α) (hβ : β < β')
    {F : Set ℝ} (hF : F.Finite) :
    ∃ I : Finset (ℝ × ℝ), (∀ ab ∈ I, ab.1 < ab.2) ∧
      IsCompact (⋃ ab ∈ I, Icc ab.1 ab.2) ∧ (⋃ ab ∈ I, Icc ab.1 ab.2) ⊆ Ioo α' β' ∧
      Icc α β ⊆ interior (⋃ ab ∈ I, Icc ab.1 ab.2) ∧
      Disjoint (frontier (⋃ ab ∈ I, Icc ab.1 ab.2)) F :=
  exists_compact_interval_union_avoiding isCompact_Icc isOpen_Ioo
    (fun _ hx => ⟨hα.trans_le hx.1, hx.2.trans_lt hβ⟩) hF

end DifferentialGeometry.Geometry.Collapse.BoundaryCloud
