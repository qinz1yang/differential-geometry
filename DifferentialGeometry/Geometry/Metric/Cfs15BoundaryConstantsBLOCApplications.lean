import DifferentialGeometry.Geometry.Metric.Cfs15BoundaryConstantsBLOC
import DifferentialGeometry.Geometry.Metric.Cfs15StageOutputBlendBLOCApplications

/-!
# Consumers of the BCG04 / BCG05 constant chain

* `flat_contributor_near_BLOC`: the contributor chain (BCG05.a) on the actual contributors of the flat
  inhabitant (radius `1`, `Σ = ε/10000`, `ρ = 6000/ε`): every contributor of the window at `x` lies
  within `150 ε⁻¹ = ρ/40` of `x`.
* `marker_band_of_block_BLOC`: BCG05's marker division, height shift and height band composed at
  `r_∂ ≤ 10⁻⁴`: a block value within `r_∂` of `(η_p, 1)` with `32 ≤ η_p ≤ 78` has height in `(31, 79)`.
* `plane_chain3_error_BLOC`: BCG04's error lemma and its segment form on the explicit `ℝ²` chain of
  `Cfs15StageOutputBlendBLOCApplications` (the exact branch: the second coordinate never moves).
-/

set_option autoImplicit false

noncomputable section

open Set Metric
open DifferentialGeometry.Analysis

namespace GC.MetricGeometry

/-- **BCG05.a on the flat inhabitant**: for the flat output (radius `1`) and `x` in the cloud, every
contributor `i` of the whole window at `x` satisfies `dist i x < 150 ε⁻¹`, and
`150 ε⁻¹ ≤ (6000/ε)/40` (the chain with `Σ = ε/10000`, `ρ = 6000/ε`). -/
theorem flat_contributor_near_BLOC {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] {k K : ℕ} {ε cw : ℝ} (L : Submodule ℝ H)
    (O : Cfs15StageOutput k K ε cw ((L : Set H) ∩ closedBall 0 1) (L : Set H) (fun _ => 1)
      (fun _ => L)) (x : H) :
    ∀ i ∈ O.I, (closedBall i (80 * ε⁻¹ * 1) ∩ ball x (8 * ε⁻¹ * 1)).Nonempty →
      dist i x < 150 * ε⁻¹ ∧ 150 * ε⁻¹ ≤ 6000 / ε / 40 := by
  intro i _ hwin
  have hε := O.eps_pos
  have hprod : ε / 10000 * (6000 / ε) = 3 / 5 := by field_simp; norm_num
  have h := contributor_near_BLOC (ε := ε) (ry := 1) (rx := 1) (sj := ε / 10000) (ρ := 6000 / ε)
    hwin hε zero_le_one (by norm_num) (by rw [hprod]; norm_num) le_rfl (by positivity)
  have h150 : 250 * ε⁻¹ * (ε / 10000 * (6000 / ε)) = 150 * ε⁻¹ := by rw [hprod]; ring
  rw [h150] at h
  exact ⟨h.1, h.2.1⟩

/-- **BCG05's marker chain at `r_∂ ≤ 10⁻⁴`**: if the boundary block of `q_y`, written `(u, v)`, is
within `r_∂` of `(η_p, 1)` coordinatewise and `32 ≤ η_p ≤ 78`, then the divided height `u/v` lies
in `(31, 79)`. -/
theorem marker_band_of_block_BLOC {u v ηp rb : ℝ} (hrb : rb ≤ 1 / 10000) (hu : |u - ηp| < rb)
    (hv : |v - 1| < rb) (hp₀ : 32 ≤ ηp) (hp₁ : ηp ≤ 78) : 31 < u / v ∧ u / v < 79 :=
  height_band_BLOC hp₀ hp₁ ((marker_division_BLOC hu hv (by linarith) hp₁ (by linarith)).trans
    (height_shift_lt_BLOC hrb))

/-- **BCG04's error on the explicit `ℝ²` chain**: for the chain of `plane_chain3_kernel_BLOC` and
every `r_∂ > 0`, `c₃ > 0`, the second coordinate of `g₃ − u` has size `< 20c₃r_∂`, along the whole
segment `[u, g₃]` (here through the exact branch). -/
theorem plane_chain3_error_BLOC (K : ℕ) (ε : ℝ) (hε : 0 < ε) (hεsmall : ε ≤ 1 / 10) :
    ∃ cw : ℝ, 0 ≤ cw ∧ ∃ O : Cfs15StageOutput 1 K ε cw
        ((planeAxisZero_BLOC : Set (EuclideanSpace ℝ (Fin 2))) ∩ closedBall 0 1)
        (planeAxisZero_BLOC : Set (EuclideanSpace ℝ (Fin 2))) (fun _ => 1)
        (fun _ => planeAxisZero_BLOC),
      ∀ (t rb c₃ : ℝ), 0 < rb → 0 < c₃ →
        ∀ q ∈ segment ℝ (t • EuclideanSpace.single (0 : Fin 2) (1 : ℝ))
          (explicitStage_BLOC O.ambient 0 (explicitStage_BLOC O.ambient 0
            (explicitStage_BLOC O.ambient 0 (t • EuclideanSpace.single (0 : Fin 2) (1 : ℝ))))),
          ‖EuclideanSpace.proj (1 : Fin 2) (q - t • EuclideanSpace.single (0 : Fin 2) (1 : ℝ))‖ <
            20 * c₃ * rb := by
  obtain ⟨cw, hcw, O, hO⟩ := plane_chain3_kernel_BLOC K ε hε hεsmall
  refine ⟨cw, hcw, O, fun t rb c₃ hrb hc₃ => ?_⟩
  set u := t • EuclideanSpace.single (0 : Fin 2) (1 : ℝ) with hu
  set g := explicitStage_BLOC O.ambient 0 (explicitStage_BLOC O.ambient 0
    (explicitStage_BLOC O.ambient 0 u)) with hg
  have hJu : EuclideanSpace.proj (1 : Fin 2) u = 0 := by simp [hu]
  have hJg : EuclideanSpace.proj (1 : Fin 2) g = 0 := (hO t).2.2
  have hJ : ‖(EuclideanSpace.proj (1 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => by
      rw [one_mul]
      exact PiLp.norm_apply_le y 1
  have herr := boundary_error_norm_lt_BLOC (EuclideanSpace.proj (1 : Fin 2)) hJ
    (g := g) (f := u) (ρ := (‖g - u‖ + 1) / c₃) (rb := rb) (cj := c₃) (c₃ := c₃)
    (fun _ => by rw [hJg, hJu]) (by rw [mul_div_cancel₀ _ hc₃.ne']; linarith) le_rfl hc₃ hrb
    (by positivity)
  exact segment_error_lt_BLOC (EuclideanSpace.proj (1 : Fin 2)) herr

end GC.MetricGeometry
