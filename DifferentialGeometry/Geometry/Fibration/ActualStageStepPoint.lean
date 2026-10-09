import DifferentialGeometry.Geometry.Fibration.ActualStageNearestApplications

/-!
# GAF02's stage step at one point, localized by the cutoff's closed support (CFS16 + CFS17/CFS20)

Blueprint `master207B.tex`, GAF02 (B:5797, proof: "At each step its CLOSED support localizes the
original point to the corresponding original core. CFS16 puts the perturbed input inside that
core's half-tube. … CFS20 gives the cumulative value and derivative bounds"), for one stage
`Ψ = adjustmentMap Q P ψ` applied after a map `f` with prior error `‖f p − F p‖ ≤ Eρ(p)`:

* `adjustmentMap_eventuallyEq_id_GAF5`: off `tsupport ψ` the adjustment is the identity near `y`.
* `stage_step_local_GAF5` (CFS16): if `f p ∈ tsupport ψ` localizes `x = π_Q F(p)` into the cloud
  `S`, then with `E ≤ 3Σ/10` and the two-sided preimage ratio `3/5`, `π_Q f(p)` lies in the half
  tube of `B(x, Σρ(sel x))` and `‖P(π_Q f p) − π_Q f p‖ ≤ aρ(p)`, `a = (5/3)ΞΣ + (1 + Ξ)E`
  (GAF01's budget).
* `stage_step_value_point_GAF5`: `‖Ψ(f p) − F p‖ ≤ (E + a)ρ(p)`.
* `stage_step_deriv_point_GAF5`: on a manifold, pointwise along `w` with any weight `N(w) ≥ 0`:
  `‖d(Ψ ∘ f)_p w − dF_p w‖ ≤ (ab(L + H₀) + Ξ(L + H₀) + ν + 2H₀)N(w)` (GAF01's derivative budget),
  and `Ψ` is differentiable at `f p`.
-/

set_option autoImplicit false

open Filter Set Metric
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Analysis

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

omit [FiniteDimensional ℝ H] in
/-- Off the closed support of the cutoff the adjustment is the identity near `y`. -/
theorem adjustmentMap_eventuallyEq_id_GAF5 (Q : Submodule ℝ H) [Q.HasOrthogonalProjection]
    (P : H → H) {ψ : H → ℝ} {y : H} (hy : y ∉ tsupport ψ) :
    adjustmentMap Q P ψ =ᶠ[𝓝 y] id := by
  have h0 : ψ =ᶠ[𝓝 y] 0 := notMem_tsupport_iff_eventuallyEq.mp hy
  refine h0.mono fun z hz => ?_
  rw [adjustmentMap_apply, hz]
  simp

variable {X : Type*}

/-- **CFS16 at one point**: the closed support localizes, the perturbed input lies in the half tube
and the stage projection moves it by at most `aρ(p)`, `a = (5/3)ΞΣ + (1 + Ξ)E`. -/
theorem stage_step_local_GAF5 (Q : Submodule ℝ H) [Q.HasOrthogonalProjection] (S : Set H)
    (sel : H → X) (ρ : X → ℝ) (plane : H → Submodule ℝ H)
    (Pst : H → H) (ψ : H → ℝ) {Ξ sg E : ℝ}
    (hΞ : 0 ≤ Ξ) (hsg : 0 < sg) (hE0 : 0 ≤ E) (hE : E ≤ 3 * sg / 10)
    (hPst : ∀ x ∈ S, ∀ z ∈ ball x (sg * ρ (sel x)),
      ‖Pst z - (x + (plane x).starProjection (z - x))‖ ≤ Ξ * (sg * ρ (sel x)))
    (F f : X → H) {p : X} (hρp : 0 < ρ p)
    (hloc : f p ∈ tsupport ψ → Q.starProjection (F p) ∈ S)
    (hratio : ∀ x ∈ S, ∀ q, Q.starProjection (F q) = x →
      3 / 5 * ρ q ≤ ρ (sel x) ∧ ρ (sel x) ≤ 5 / 3 * ρ q)
    (hprior : ‖f p - F p‖ ≤ E * ρ p) (hp : f p ∈ tsupport ψ) :
    Q.starProjection (F p) ∈ S ∧
      Q.starProjection (f p) ∈ ball (Q.starProjection (F p))
        (sg * ρ (sel (Q.starProjection (F p)))) ∧
      ‖Pst (Q.starProjection (f p)) - Q.starProjection (f p)‖ ≤
        (5 / 3 * Ξ * sg + (1 + Ξ) * E) * ρ p := by
  have hxS := hloc hp
  obtain ⟨hr1, hr2⟩ := hratio _ hxS p rfl
  have hzx : ‖Q.starProjection (f p) - Q.starProjection (F p)‖ ≤ E * ρ p := by
    rw [← map_sub]
    exact (Q.norm_starProjection_apply_le _).trans hprior
  have hball : Q.starProjection (f p) ∈ ball (Q.starProjection (F p))
      (sg * ρ (sel (Q.starProjection (F p)))) := by
    rw [mem_ball, dist_eq_norm]
    have h1 : E * ρ p ≤ 3 * sg / 10 * ρ p := mul_le_mul_of_nonneg_right hE hρp.le
    have h2 : 3 * sg / 10 * ρ p ≤ 3 * sg / 10 * (5 / 3 * ρ (sel (Q.starProjection (F p)))) := by
      have hr1' : ρ p ≤ 5 / 3 * ρ (sel (Q.starProjection (F p))) := by linarith
      exact mul_le_mul_of_nonneg_left hr1' (by positivity)
    have hsel0 : 0 < ρ (sel (Q.starProjection (F p))) := by linarith
    nlinarith
  refine ⟨hxS, hball, ?_⟩
  have h := norm_sub_self_le_of_affine_GAF3 (plane (Q.starProjection (F p)))
    (hPst _ hxS _ hball)
  have h3 : Ξ * (sg * ρ (sel (Q.starProjection (F p)))) ≤ Ξ * (sg * (5 / 3 * ρ p)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hr2 hsg.le) hΞ
  have h4 : 0 ≤ Ξ * E * ρ p := by positivity
  calc _ ≤ Ξ * (sg * ρ (sel (Q.starProjection (F p)))) +
        ‖Q.starProjection (f p) - Q.starProjection (F p)‖ := h
    _ ≤ Ξ * (sg * (5 / 3 * ρ p)) + E * ρ p := add_le_add h3 hzx
    _ ≤ (5 / 3 * Ξ * sg + (1 + Ξ) * E) * ρ p := by nlinarith

/-- **CFS20's value step at one point, localized**: `‖Ψ(f p) − F p‖ ≤ (E + a)ρ(p)` with GAF01's
`a = (5/3)ΞΣ + (1 + Ξ)E` (off the closed support of `ψ` the stage does not move `f p`). -/
theorem stage_step_value_point_GAF5 (Q : Submodule ℝ H) [Q.HasOrthogonalProjection] (S : Set H)
    (sel : H → X) (ρ : X → ℝ) (plane : H → Submodule ℝ H) (Pst : H → H) (ψ : H → ℝ)
    (hψI : ∀ y, ψ y ∈ Icc (0 : ℝ) 1) {Ξ sg E : ℝ} (hΞ : 0 ≤ Ξ) (hsg : 0 < sg) (hE0 : 0 ≤ E)
    (hE : E ≤ 3 * sg / 10)
    (hPst : ∀ x ∈ S, ∀ z ∈ ball x (sg * ρ (sel x)),
      ‖Pst z - (x + (plane x).starProjection (z - x))‖ ≤ Ξ * (sg * ρ (sel x)))
    (F f : X → H) {p : X} (hρp : 0 < ρ p)
    (hloc : f p ∈ tsupport ψ → Q.starProjection (F p) ∈ S)
    (hratio : ∀ x ∈ S, ∀ q, Q.starProjection (F q) = x →
      3 / 5 * ρ q ≤ ρ (sel x) ∧ ρ (sel x) ≤ 5 / 3 * ρ q)
    (hprior : ‖f p - F p‖ ≤ E * ρ p) :
    ‖adjustmentMap Q Pst ψ (f p) - F p‖ ≤ (E + (5 / 3 * Ξ * sg + (1 + Ξ) * E)) * ρ p := by
  by_cases hp : f p ∈ tsupport ψ
  · have hv := (stage_step_local_GAF5 Q S sel ρ plane Pst ψ hΞ hsg hE0 hE hPst F f hρp hloc
      hratio hprior hp).2.2
    exact adjustmentMap_step_value_GAF3 Q (P := Pst) (hψI _) hv hprior
  · have h0 : ψ (f p) = 0 := image_eq_zero_of_notMem_tsupport hp
    rw [adjustmentMap_apply, h0, zero_smul, add_zero]
    have ha : 0 ≤ (5 / 3 * Ξ * sg + (1 + Ξ) * E) * ρ p := by positivity
    have heq : (E + (5 / 3 * Ξ * sg + (1 + Ξ) * E)) * ρ p =
        E * ρ p + (5 / 3 * Ξ * sg + (1 + Ξ) * E) * ρ p := by ring
    linarith

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] {G : Type*} [TopologicalSpace G]
  {I : ModelWithCorners ℝ E' G} {M : Type*} [TopologicalSpace M] [ChartedSpace G M]

/-- **CFS20's derivative step at one point of a manifold, localized**: pointwise along `w` with a
weight `N(w) ≥ 0`, from `‖dF w‖ ≤ LN(w)`, the normal error `‖(I − Π_x)π_Q dF w‖ ≤ νN(w)` at the
localized cloud point `x = π_Q F(p)`, the prior error `‖df w − dF w‖ ≤ H₀N(w)`, the stage
projection's derivative `‖DP − Π_x‖ ≤ Ξ` on `B(x, Σρ(sel x))` and the cutoff bound
`‖Dψ(f p)‖ ≤ b/ρ(p)` on the closed support: `Ψ` is differentiable at `f p` and
`‖d(Ψ ∘ f)_p w − dF_p w‖ ≤ (ab(L + H₀) + Ξ(L + H₀) + ν + 2H₀)N(w)`. -/
theorem stage_step_deriv_point_GAF5 (Q : Submodule ℝ H) [Q.HasOrthogonalProjection] (S : Set H)
    (sel : H → M) (ρ : M → ℝ) (plane : H → Submodule ℝ H) (Pst : H → H) (ψ : H → ℝ)
    (hψI : ∀ y, ψ y ∈ Icc (0 : ℝ) 1) {Ξ sg E b L H₀ ν : ℝ} (hΞ : 0 ≤ Ξ) (hsg : 0 < sg)
    (hE0 : 0 ≤ E) (hE : E ≤ 3 * sg / 10) (hb : 0 ≤ b) (hL : 0 ≤ L) (hH₀ : 0 ≤ H₀) (hν : 0 ≤ ν)
    (hPst : ∀ x ∈ S, ∀ z ∈ ball x (sg * ρ (sel x)),
      ‖Pst z - (x + (plane x).starProjection (z - x))‖ ≤ Ξ * (sg * ρ (sel x)))
    (hPd : ∀ x ∈ S, ∀ z ∈ ball x (sg * ρ (sel x)),
      DifferentiableAt ℝ Pst z ∧ ‖fderiv ℝ Pst z - (plane x).starProjection‖ ≤ Ξ)
    (F f : M → H) {p : M} (hρp : 0 < ρ p)
    (hloc : f p ∈ tsupport ψ → Q.starProjection (F p) ∈ S)
    (hratio : ∀ x ∈ S, ∀ q, Q.starProjection (F q) = x →
      3 / 5 * ρ q ≤ ρ (sel x) ∧ ρ (sel x) ≤ 5 / 3 * ρ q)
    (hprior : ‖f p - F p‖ ≤ E * ρ p) (hf : MDifferentiableAt I 𝓘(ℝ, H) f p)
    (hψd : f p ∈ tsupport ψ → DifferentiableAt ℝ ψ (f p) ∧ ‖fderiv ℝ ψ (f p)‖ ≤ b / ρ p)
    (Nw : TangentSpace I p → ℝ) (hN : ∀ w, 0 ≤ Nw w)
    (hfirst : ∀ w, ‖mvfderiv I F p w‖ ≤ L * Nw w)
    (hnormal : Q.starProjection (F p) ∈ S → ∀ w,
      ‖(ContinuousLinearMap.id ℝ H - (plane (Q.starProjection (F p))).starProjection)
        (Q.starProjection (mvfderiv I F p w))‖ ≤ ν * Nw w)
    (hpriorD : ∀ w, ‖mvfderiv I f p w - mvfderiv I F p w‖ ≤ H₀ * Nw w) :
    DifferentiableAt ℝ (adjustmentMap Q Pst ψ) (f p) ∧
      ∀ w, ‖mvfderiv I (adjustmentMap Q Pst ψ ∘ f) p w - mvfderiv I F p w‖ ≤
        ((5 / 3 * Ξ * sg + (1 + Ξ) * E) * b * (L + H₀) + Ξ * (L + H₀) + ν + 2 * H₀) * Nw w := by
  by_cases hp : f p ∈ tsupport ψ
  · have hst := stage_step_local_GAF5 Q S sel ρ plane Pst ψ hΞ hsg hE0 hE hPst F f hρp hloc
      hratio hprior hp
    have hPdz := hPd _ hst.1 _ hst.2.1
    have hψdd := hψd hp
    have hΨ : DifferentiableAt ℝ (adjustmentMap Q Pst ψ) (f p) :=
      (hasFDerivAt_adjustmentMap_GAF3 Q hPdz.1 hψdd.1).differentiableAt
    refine ⟨hΨ, fun w => ?_⟩
    rw [mvfderiv_comp_apply_of_differentiableAt_GAF3 hf hΨ w]
    exact adjustmentMap_step_deriv_GAF3 Q (T := E') hPdz.1 hψdd.1
      (plane (Q.starProjection (F p))).starProjection (mvfderiv I f p) (mvfderiv I F p) w hb hΞ
      hL hH₀ hρp (hN w) (hψI _) (norm_id_sub_starProjection_le_GAF3 _) hst.2.2 hψdd.2 hPdz.2
      (hfirst w) (hnormal hst.1 w) (hpriorD w)
  · have hev := adjustmentMap_eventuallyEq_id_GAF5 Q Pst hp
    have hΨ : DifferentiableAt ℝ (adjustmentMap Q Pst ψ) (f p) :=
      differentiableAt_id.congr_of_eventuallyEq hev
    have hD : fderiv ℝ (adjustmentMap Q Pst ψ) (f p) = ContinuousLinearMap.id ℝ H := by
      rw [hev.fderiv_eq, fderiv_id]
    refine ⟨hΨ, fun w => ?_⟩
    rw [mvfderiv_comp_apply_of_differentiableAt_GAF3 hf hΨ w, hD, ContinuousLinearMap.id_apply]
    have h1 : 0 ≤ (5 / 3 * Ξ * sg + (1 + Ξ) * E) * b * (L + H₀) := by positivity
    have h2 : 0 ≤ Ξ * (L + H₀) := by positivity
    have h3 : H₀ ≤ (5 / 3 * Ξ * sg + (1 + Ξ) * E) * b * (L + H₀) + Ξ * (L + H₀) + ν + 2 * H₀ := by
      linarith
    exact (hpriorD w).trans (mul_le_mul_of_nonneg_right h3 (hN w))

end DifferentialGeometry.Geometry.Collapse
