import DifferentialGeometry.Analysis.InnerProductSpace.RetainedCoordinateGraphRow
import DifferentialGeometry.Analysis.InnerProductSpace.OrthogonalErrorCoordinates

/-!
# CGP06 on the convex graph domain, for graphs in orthogonal-sum form

Blueprint `master207B.tex`, CGP06 (`lem:fibration-retained-coordinate-graph`, B:4130–4174); external
draft 59 §4, third step ("CGP06, the retained coordinate has a lower bound on the same `L_x`"):
"integrate the derivative bound over the WHOLE convex graph domain retained by CFS15, and prove that
the projection is injective on that graph and a local diffeomorphism".

CFS15's local graphs are stored in orthogonal-sum form: `g : L → Lᗮ` on the parameter ball
`B_L(0, R)` and the graph point `x + orthogonalCoordinateSum L (t, g t)`, with the jet bound
`‖D^j g‖ ≤ (ε/3) r (r⁻¹)^j` (so `‖Dg‖ ≤ ε/3`). The CGP06 row of the tree
(`cgp06_retained_coordinate_graph`) is stated for `g : L → H` and the point `x + t + g t`. This module
carries the row over to the orthogonal-sum form, on naive data (a plane, a convex parameter ball, a
coordinate projection), and adds the coframe bound on the derivative image of the graph:

* `orthogonalGraph_apply_BPRE`: `x + orthogonalCoordinateSum L (t, g t) = x + t + g t`.
* `cgp06_orthogonal_graph_BPRE`: injective on the whole ball, invertible differential at every
  parameter, open image, smooth inverse on the image.
* `norm_fderiv_le_of_iteratedFDeriv_one_BPRE`: CFS15's jet bound at order one is the slope bound
  `‖Dg‖ ≤ ε/3`.
* `hasFDerivAt_orthogonalGraph_BPRE`, `coframe_range_fderiv_orthogonalGraph_BPRE`: the derivative of
  the graph map is `ι_L + ι_{Lᗮ} ∘ Dg(t)`, and on its range (the tangent plane of the graph)
  `(m - a)|w| ≤ (1 + a)|π w|`.
* `cgp06_row_orthogonal_graph_BPRE`: the row with the sufficient criterion `m = 1/(2Ω)`
  (`retained_coordinate_lower_bound_of_reference_graph`, the plane being any same-dimensional plane
  with normal error `ν`) and the slope bound `a < 1/(2Ω)`: the four CGP06 assertions plus the
  tangent-plane coframe bound.
-/

set_option autoImplicit false

noncomputable section

open Set Metric
open scoped Topology ContDiff

namespace DifferentialGeometry.Analysis

section Graph

variable {H F : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ H] in
/-- The orthogonal-sum graph point is `x + t + g t`. -/
theorem orthogonalGraph_apply_BPRE (L : Submodule ℝ H) (g : L → Lᗮ) (x : H) (t : L) :
    x + orthogonalCoordinateSum L (t, g t) = x + (t : H) + ((g t : Lᗮ) : H) := by
  change x + ((t : H) + ((g t : Lᗮ) : H)) = _
  rw [add_assoc]

omit [FiniteDimensional ℝ H] in
/-- The ambient lift `t ↦ (g t : H)` keeps the slope bound. -/
theorem norm_fderiv_coe_le_BPRE (L : Submodule ℝ H) (g : L → Lᗮ) {t : L}
    (hg : DifferentiableAt ℝ g t) :
    ‖fderiv ℝ (fun s : L => ((g s : Lᗮ) : H)) t‖ ≤ ‖fderiv ℝ g t‖ := by
  have h : HasFDerivAt (fun s : L => ((g s : Lᗮ) : H)) (Lᗮ.subtypeL.comp (fderiv ℝ g t)) t :=
    Lᗮ.subtypeL.hasFDerivAt.comp t hg.hasFDerivAt
  rw [h.fderiv]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_of_le_one_left (norm_nonneg _) (Submodule.norm_subtypeL_le _))

omit [FiniteDimensional ℝ H] in
/-- CFS15's jet bound at order one is a slope bound. -/
theorem norm_fderiv_le_of_iteratedFDeriv_one_BPRE {L : Submodule ℝ H} (g : L → Lᗮ) {ε r : ℝ}
    (hr : 0 < r) {t : L} (hjet : ‖iteratedFDeriv ℝ 1 g t‖ ≤ (ε / 3) * r * (r⁻¹) ^ 1) :
    ‖fderiv ℝ g t‖ ≤ ε / 3 := by
  rw [norm_iteratedFDeriv_one, pow_one, mul_assoc, mul_inv_cancel₀ hr.ne', mul_one] at hjet
  exact hjet

/-- **CGP06 for an orthogonal-sum graph.** If `|π v| ≥ m |v|` on `L`, `dim L = dim F`, `‖π‖ ≤ 1`,
`g : L → Lᗮ` is smooth on the convex ball `B_L(0, R)` with `‖Dg‖ ≤ a < m`, then the retained
coordinate `t ↦ π (x + orthogonalCoordinateSum L (t, g t))` is injective on the WHOLE ball, has an
invertible differential at every parameter, has open image and a smooth inverse on it. -/
theorem cgp06_orthogonal_graph_BPRE (L : Submodule ℝ H) (π : H →L[ℝ] F) (hπ : ‖π‖ ≤ 1)
    {m a R : ℝ} (hm : ∀ v ∈ L, m * ‖v‖ ≤ ‖π v‖) (hma : a < m)
    (hdim : Module.finrank ℝ L = Module.finrank ℝ F)
    (g : L → Lᗮ) (hg : ContDiffOn ℝ ∞ g (ball 0 R))
    (hDg : ∀ t ∈ ball (0 : L) R, ‖fderiv ℝ g t‖ ≤ a) (x : H) :
    InjOn (fun t : L => π (x + orthogonalCoordinateSum L (t, g t))) (ball 0 R) ∧
    (∀ t ∈ ball (0 : L) R, ∃ T : L ≃L[ℝ] F,
      HasFDerivAt (fun t : L => π (x + orthogonalCoordinateSum L (t, g t))) (T : L →L[ℝ] F) t) ∧
    IsOpen ((fun t : L => π (x + orthogonalCoordinateSum L (t, g t))) '' ball 0 R) ∧
    ∃ σ : F → L,
      InvOn σ (fun t : L => π (x + orthogonalCoordinateSum L (t, g t))) (ball 0 R)
        ((fun t : L => π (x + orthogonalCoordinateSum L (t, g t))) '' ball 0 R) ∧
      ContDiffOn ℝ ∞ σ ((fun t : L => π (x + orthogonalCoordinateSum L (t, g t))) '' ball 0 R) := by
  have hfun : (fun t : L => π (x + orthogonalCoordinateSum L (t, g t))) =
      fun t : L => π (x + (t : H) + ((g t : Lᗮ) : H)) := by
    funext t
    rw [orthogonalGraph_apply_BPRE]
  have hg' : ContDiffOn ℝ ∞ (fun s : L => ((g s : Lᗮ) : H)) (ball 0 R) :=
    Lᗮ.subtypeL.contDiff.comp_contDiffOn hg
  have hDg' : ∀ t ∈ ball (0 : L) R, ‖fderiv ℝ (fun s : L => ((g s : Lᗮ) : H)) t‖ ≤ a := by
    intro t ht
    have hgd : DifferentiableAt ℝ g t :=
      (hg.contDiffAt (isOpen_ball.mem_nhds ht)).differentiableAt (by simp)
    exact (norm_fderiv_coe_le_BPRE L g hgd).trans (hDg t ht)
  rw [hfun]
  exact cgp06_retained_coordinate_graph L π hπ hm hma hdim _ hg' hDg' x

omit [FiniteDimensional ℝ H] [FiniteDimensional ℝ F] in
/-- The derivative of the orthogonal-sum graph map is `ι_L + ι_{Lᗮ} ∘ Dg(t)`. -/
theorem hasFDerivAt_orthogonalGraph_BPRE (L : Submodule ℝ H) (g : L → Lᗮ) (x : H) {t : L}
    (hg : DifferentiableAt ℝ g t) :
    HasFDerivAt (fun s : L => x + orthogonalCoordinateSum L (s, g s))
      (L.subtypeL + Lᗮ.subtypeL.comp (fderiv ℝ g t)) t := by
  have hfun : (fun s : L => x + orthogonalCoordinateSum L (s, g s)) =
      fun s : L => x + (s : H) + ((g s : Lᗮ) : H) := by
    funext s
    rw [orthogonalGraph_apply_BPRE]
  rw [hfun]
  have h1 : HasFDerivAt (fun s : L => x + (s : H)) L.subtypeL t := by
    have h := (hasFDerivAt_const x t).add L.subtypeL.hasFDerivAt
    rw [zero_add] at h
    exact h
  exact h1.add (Lᗮ.subtypeL.hasFDerivAt.comp t hg.hasFDerivAt)

omit [FiniteDimensional ℝ H] [FiniteDimensional ℝ F] in
/-- **Coframe bound on the tangent plane of the graph.** On the range of the derivative of the graph
map at a parameter with `‖Dg(t)‖ ≤ a ≤ m`, the retained coordinate satisfies
`(m - a)|w| ≤ (1 + a)|π w|`. -/
theorem coframe_range_fderiv_orthogonalGraph_BPRE (L : Submodule ℝ H) (π : H →L[ℝ] F)
    (hπ : ‖π‖ ≤ 1) {m a : ℝ} (hm : ∀ v ∈ L, m * ‖v‖ ≤ ‖π v‖) (hma : a ≤ m)
    (g : L → Lᗮ) (x : H) {t : L} (hg : DifferentiableAt ℝ g t) (hDg : ‖fderiv ℝ g t‖ ≤ a) :
    ∀ w ∈ LinearMap.range
        (fderiv ℝ (fun s : L => x + orthogonalCoordinateSum L (s, g s)) t : L →ₗ[ℝ] H),
      (m - a) * ‖w‖ ≤ (1 + a) * ‖π w‖ := by
  rintro w ⟨v, rfl⟩
  rw [(hasFDerivAt_orthogonalGraph_BPRE L g x hg).fderiv]
  set A : L →L[ℝ] H := Lᗮ.subtypeL.comp (fderiv ℝ g t) with hA
  have hAn : ‖A‖ ≤ a := (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_of_le_one_left (norm_nonneg _) (Submodule.norm_subtypeL_le _)).trans hDg)
  have ha0 : 0 ≤ a := (norm_nonneg _).trans hAn
  have hw : ((L.subtypeL + A : L →L[ℝ] H) : L →ₗ[ℝ] H) v = (v : H) + A v := rfl
  rw [hw]
  have hlow := retained_coordinate_fderiv_lower_bound L π hπ hm A hAn v
  have hup : ‖(v : H) + A v‖ ≤ (1 + a) * ‖v‖ := by
    refine (norm_add_le _ _).trans ?_
    have h2 : ‖A v‖ ≤ a * ‖v‖ := (A.le_opNorm v).trans (mul_le_mul_of_nonneg_right hAn (norm_nonneg v))
    rw [Submodule.norm_coe]
    linarith
  have hma' : 0 ≤ m - a := sub_nonneg.mpr hma
  calc (m - a) * ‖(v : H) + A v‖ ≤ (m - a) * ((1 + a) * ‖v‖) :=
        mul_le_mul_of_nonneg_left hup hma'
    _ = (1 + a) * ((m - a) * ‖v‖) := by ring
    _ ≤ (1 + a) * ‖π ((v : H) + A v)‖ := mul_le_mul_of_nonneg_left hlow (by linarith)

end Graph

section Criterion

variable {X E H : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

/-- **CGP06 (row, orthogonal-sum graph, with its sufficient criterion and the tangent coframe).**
For the reference derivative `T` (`π T = I`, `‖T‖ ≤ Ω`, `Ω ≥ 1`), `‖D - T Dη‖ ≤ e` with a right
inverse of `Dη` of norm `≤ 2`, a plane `L` with `dim L = dim E` and normal error
`‖(I - Π_L) D‖ ≤ ν`, `ν + e ≤ 1/(48Ω)`, and a smooth orthogonal-sum graph `g : L → Lᗮ` with
`‖Dg‖ ≤ a < 1/(2Ω)` over the convex ball `B_L(0, R)`: the retained coordinate is injective on the
whole ball, has invertible differentials, open image and a smooth inverse on it; and on the tangent
plane of the graph at every parameter, `(1/(2Ω) - a)|w| ≤ (1 + a)|π w|`. -/
theorem cgp06_row_orthogonal_graph_BPRE (π : H →L[ℝ] E) (hπ : ‖π‖ ≤ 1)
    (T : E →L[ℝ] H) (hπT : π.comp T = ContinuousLinearMap.id ℝ E) {Ω e ν : ℝ} (hT : ‖T‖ ≤ Ω)
    (D : X →L[ℝ] H) (Dη : X →L[ℝ] E) (B : E →L[ℝ] X)
    (hB : Dη.comp B = ContinuousLinearMap.id ℝ E) (hBn : ‖B‖ ≤ 2) (hD : ‖D - T.comp Dη‖ ≤ e)
    (L : Submodule ℝ H) (hdim : Module.finrank ℝ L = Module.finrank ℝ E)
    (hν : ‖Lᗮ.starProjection.comp D‖ ≤ ν) (hΩ : 1 ≤ Ω) (he : 0 ≤ e) (hν0 : 0 ≤ ν)
    (hsmall : ν + e ≤ 1 / (48 * Ω)) {a R : ℝ} (ha : a < 1 / (2 * Ω))
    (g : L → Lᗮ) (hg : ContDiffOn ℝ ∞ g (ball 0 R))
    (hDg : ∀ t ∈ ball (0 : L) R, ‖fderiv ℝ g t‖ ≤ a) (x : H) :
    InjOn (fun t : L => π (x + orthogonalCoordinateSum L (t, g t))) (ball 0 R) ∧
    (∀ t ∈ ball (0 : L) R, ∃ S : L ≃L[ℝ] E,
      HasFDerivAt (fun t : L => π (x + orthogonalCoordinateSum L (t, g t))) (S : L →L[ℝ] E) t) ∧
    IsOpen ((fun t : L => π (x + orthogonalCoordinateSum L (t, g t))) '' ball 0 R) ∧
    (∃ σ : E → L,
      InvOn σ (fun t : L => π (x + orthogonalCoordinateSum L (t, g t))) (ball 0 R)
        ((fun t : L => π (x + orthogonalCoordinateSum L (t, g t))) '' ball 0 R) ∧
      ContDiffOn ℝ ∞ σ ((fun t : L => π (x + orthogonalCoordinateSum L (t, g t))) '' ball 0 R)) ∧
    ∀ t ∈ ball (0 : L) R, ∀ w ∈ LinearMap.range
        (fderiv ℝ (fun s : L => x + orthogonalCoordinateSum L (s, g s)) t : L →ₗ[ℝ] H),
      (1 / (2 * Ω) - a) * ‖w‖ ≤ (1 + a) * ‖π w‖ := by
  have hcrit := retained_coordinate_lower_bound_of_reference_graph π hπ T hπT hT D Dη B hB hBn
    hD L hdim hν hΩ he hν0 hsmall
  have hΩpos : 0 < Ω := zero_lt_one.trans_le hΩ
  have hm : ∀ v ∈ L, 1 / (2 * Ω) * ‖v‖ ≤ ‖π v‖ := by
    intro v hv
    rw [one_div, ← div_eq_inv_mul, div_le_iff₀ (by positivity)]
    linarith [hcrit v hv]
  obtain ⟨h1, h2, h3, h4⟩ := cgp06_orthogonal_graph_BPRE L π hπ hm ha hdim g hg hDg x
  refine ⟨h1, h2, h3, h4, fun t ht => ?_⟩
  have hgd : DifferentiableAt ℝ g t :=
    (hg.contDiffAt (isOpen_ball.mem_nhds ht)).differentiableAt (by simp)
  exact coframe_range_fderiv_orthogonalGraph_BPRE L π hπ hm ha.le g x hgd (hDg t ht)

end Criterion

end DifferentialGeometry.Analysis
