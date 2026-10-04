import DifferentialGeometry.Analysis.InnerProductSpace.RetainedCoordinateInverse

/-!
# CGP06 as a row: the retained coordinate on the whole local graph

Blueprint 207B, CGP06 (`lem:fibration-retained-coordinate-graph`, B:4130–4174). For the graph map
`G t = x + t + g t` over the parameter ball `B_L(0, R)` (`g` smooth, `‖Dg‖ ≤ a < m`,
`|π v| ≥ m |v|` on `L`, `dim L = dim F`), the retained coordinate `π ∘ G`:
* is injective on the ball (`injOn_retained_coordinate_graph`);
* has an invertible differential at every parameter, so it is a local diffeomorphism
  (`hasFDerivAt_retained_coordinate_graph_equiv`, from `retained_coordinate_fderiv_lower_bound`);
* has an open image and a smooth inverse on it (Codex X94,
  `exists_smooth_inverse_retained_coordinate_graph`).
`cgp06_retained_coordinate_graph` packages the three assertions; `cgp06_row_of_reference_graph`
adds the sufficient criterion `m = 1/(2Ω)` (`retained_coordinate_lower_bound_of_reference_graph`).
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped Topology ContDiff

namespace DifferentialGeometry.Analysis

section Graph

variable {H F : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- CGP06, local diffeomorphism clause: at every parameter of the ball the retained coordinate
of the graph has an invertible differential `π ∘ (ι_L + Dg(t))`. -/
theorem hasFDerivAt_retained_coordinate_graph_equiv
    (L : Submodule ℝ H) (π : H →L[ℝ] F) (hπ : ‖π‖ ≤ 1)
    {m a R : ℝ} (hm : ∀ v ∈ L, m * ‖v‖ ≤ ‖π v‖) (hma : a < m)
    (hdim : Module.finrank ℝ L = Module.finrank ℝ F)
    (g : L → H) (hg : ContDiffOn ℝ ∞ g (Metric.ball 0 R))
    (hDg : ∀ t ∈ Metric.ball (0 : L) R, ‖fderiv ℝ g t‖ ≤ a) (x : H) :
    ∀ t ∈ Metric.ball (0 : L) R, ∃ T : L ≃L[ℝ] F,
      HasFDerivAt (fun t : L => π (x + t + g t)) (T : L →L[ℝ] F) t := by
  intro t ht
  have hgd : DifferentiableAt ℝ g t :=
    (hg.contDiffAt (Metric.isOpen_ball.mem_nhds ht)).differentiableAt (by simp)
  let A : L →L[ℝ] F := π.comp (L.subtypeL + fderiv ℝ g t)
  have hA : HasFDerivAt (fun t : L => π (x + t + g t)) A t := by
    refine π.hasFDerivAt.comp t ?_
    convert! (((hasFDerivAt_const x t).add L.subtypeL.hasFDerivAt).add hgd.hasFDerivAt) using 1
    simp
  have hAi : Function.Injective A := by
    apply (LinearMap.ker_eq_bot).mp
    apply le_antisymm _ bot_le
    intro v hv
    change A v = 0 at hv
    change v = 0
    have hl := retained_coordinate_fderiv_lower_bound L π hπ hm (fderiv ℝ g t) (hDg t ht) v
    change (m - a) * ‖v‖ ≤ ‖A v‖ at hl
    rw [hv, norm_zero] at hl
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg v])
  have hAs : Function.Surjective A :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hAi
  exact ⟨ContinuousLinearEquiv.ofBijective A (LinearMap.ker_eq_bot.mpr hAi)
    (LinearMap.range_eq_top.mpr hAs), hA⟩

/-- **CGP06 (row).** If `|π v| ≥ m |v|` on `L`, `dim L = dim F`, `‖π‖ ≤ 1`, `g` is smooth on
`B_L(0, R)` with `‖Dg‖ ≤ a < m`, then the retained coordinate `t ↦ π (x + t + g t)` is injective
on the ball, a local diffeomorphism (invertible differential everywhere), its image is open and its
inverse on the image is smooth. -/
theorem cgp06_retained_coordinate_graph
    (L : Submodule ℝ H) (π : H →L[ℝ] F) (hπ : ‖π‖ ≤ 1)
    {m a R : ℝ} (hm : ∀ v ∈ L, m * ‖v‖ ≤ ‖π v‖) (hma : a < m)
    (hdim : Module.finrank ℝ L = Module.finrank ℝ F)
    (g : L → H) (hg : ContDiffOn ℝ ∞ g (Metric.ball 0 R))
    (hDg : ∀ t ∈ Metric.ball (0 : L) R, ‖fderiv ℝ g t‖ ≤ a) (x : H) :
    Set.InjOn (fun t : L => π (x + t + g t)) (Metric.ball 0 R) ∧
    (∀ t ∈ Metric.ball (0 : L) R, ∃ T : L ≃L[ℝ] F,
      HasFDerivAt (fun t : L => π (x + t + g t)) (T : L →L[ℝ] F) t) ∧
    IsOpen ((fun t : L => π (x + t + g t)) '' Metric.ball 0 R) ∧
    ∃ σ : F → L,
      Set.InvOn σ (fun t : L => π (x + t + g t)) (Metric.ball 0 R)
        ((fun t : L => π (x + t + g t)) '' Metric.ball 0 R) ∧
      ContDiffOn ℝ ∞ σ ((fun t : L => π (x + t + g t)) '' Metric.ball 0 R) :=
  ⟨injOn_retained_coordinate_graph L π hπ hm hma g
      (fun t ht => (hg.contDiffAt (Metric.isOpen_ball.mem_nhds ht)).differentiableAt (by simp))
      hDg x,
    hasFDerivAt_retained_coordinate_graph_equiv L π hπ hm hma hdim g hg hDg x,
    exists_smooth_inverse_retained_coordinate_graph L π hπ hm hma hdim g hg hDg x⟩

end Graph

section Criterion

variable {X E H : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

/-- **CGP06 (row, with its sufficient criterion).** For the reference derivative `T` (`π T = I`,
`‖T‖ ≤ Ω`, `Ω ≥ 1`), `‖D - T Dη‖ ≤ e` with a right inverse of `Dη` of norm `≤ 2`, a plane `L` with
`dim L = dim E` and normal error `‖(I - Π_L) D‖ ≤ ν`, `ν + e ≤ 1/(48Ω)`, and a smooth graph
`‖Dg‖ ≤ a < 1/(2Ω)` over `B_L(0, R)`: the retained coordinate is injective on the ball, a local
diffeomorphism, with open image and smooth inverse on it. -/
theorem cgp06_row_of_reference_graph (π : H →L[ℝ] E) (hπ : ‖π‖ ≤ 1)
    (T : E →L[ℝ] H) (hπT : π.comp T = ContinuousLinearMap.id ℝ E) {Ω e ν : ℝ} (hT : ‖T‖ ≤ Ω)
    (D : X →L[ℝ] H) (Dη : X →L[ℝ] E) (B : E →L[ℝ] X)
    (hB : Dη.comp B = ContinuousLinearMap.id ℝ E) (hBn : ‖B‖ ≤ 2) (hD : ‖D - T.comp Dη‖ ≤ e)
    (L : Submodule ℝ H) (hdim : Module.finrank ℝ L = Module.finrank ℝ E)
    (hν : ‖Lᗮ.starProjection.comp D‖ ≤ ν) (hΩ : 1 ≤ Ω) (he : 0 ≤ e) (hν0 : 0 ≤ ν)
    (hsmall : ν + e ≤ 1 / (48 * Ω)) {a R : ℝ} (ha : a < 1 / (2 * Ω))
    (g : L → H) (hg : ContDiffOn ℝ ∞ g (Metric.ball 0 R))
    (hDg : ∀ t ∈ Metric.ball (0 : L) R, ‖fderiv ℝ g t‖ ≤ a) (x : H) :
    Set.InjOn (fun t : L => π (x + t + g t)) (Metric.ball 0 R) ∧
    (∀ t ∈ Metric.ball (0 : L) R, ∃ S : L ≃L[ℝ] E,
      HasFDerivAt (fun t : L => π (x + t + g t)) (S : L →L[ℝ] E) t) ∧
    IsOpen ((fun t : L => π (x + t + g t)) '' Metric.ball 0 R) ∧
    ∃ σ : E → L,
      Set.InvOn σ (fun t : L => π (x + t + g t)) (Metric.ball 0 R)
        ((fun t : L => π (x + t + g t)) '' Metric.ball 0 R) ∧
      ContDiffOn ℝ ∞ σ ((fun t : L => π (x + t + g t)) '' Metric.ball 0 R) := by
  have hcrit := retained_coordinate_lower_bound_of_reference_graph π hπ T hπT hT D Dη B hB hBn
    hD L hdim hν hΩ he hν0 hsmall
  have hΩpos : 0 < Ω := zero_lt_one.trans_le hΩ
  have hm : ∀ v ∈ L, 1 / (2 * Ω) * ‖v‖ ≤ ‖π v‖ := by
    intro v hv
    rw [one_div, ← div_eq_inv_mul, div_le_iff₀ (by positivity)]
    linarith [hcrit v hv]
  exact cgp06_retained_coordinate_graph L π hπ hm ha hdim g hg hDg x

end Criterion

end DifferentialGeometry.Analysis
