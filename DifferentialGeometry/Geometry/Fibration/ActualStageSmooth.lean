import DifferentialGeometry.Geometry.Fibration.ActualStageStepPoint

/-!
# GAF02 step 5: smoothness of the stage maps along the stage outputs (CFS18)

Blueprint `master207B.tex`, GAF02 (B:5797) proof, smoothness: each stage map
`Ψ = adjustmentMap Q P ψ` is smooth near every point `f p` of the preceding stage output — off the
closed support of `ψ` it is the identity near `f p`; on it, CFS31's localization and CFS16's half
tube put `π_Q f(p)` into a ball `B(x, Σρ(sel x))`, `x ∈ S`, where the stage projection is smooth.
Hence `Ψ ∘ f` is smooth when `f` is.

* `adjustmentMap_contDiffAt_GAF6`, `adjustmentMap_contDiffAt_of_notMem_GAF6`: the two local cases.
* `stage_step_mem_ball_GAF6`: CFS16's half tube without the projection bounds.
* `stage_step_contDiffAt_point_GAF6`: `Ψ` is smooth at `f p`.
* `contMDiff_comp_of_contDiffAt_GAF6`: `Ψ ∘ f` is smooth on the manifold.
* `projected_stage_map_GAF6`: `π_Q ∘ a` keeps CFS14 (3)'s value/derivative bounds of `a` (planes
  in `Q`, centres in `Q`), is `Q`-valued, and is smooth where `a` is (the stage projections
  `P_k = π_{Q_k} ∘ a_k` of CFS31).
-/

set_option autoImplicit false

open Filter Set Metric
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Analysis

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- On the closed support: `Ψ` is smooth at `y` when `P` is smooth at `π_Q y` and `ψ` at `y`. -/
theorem adjustmentMap_contDiffAt_GAF6 (Q : Submodule ℝ H) [Q.HasOrthogonalProjection]
    {P : H → H} {ψ : H → ℝ} {y : H} (hP : ContDiffAt ℝ ∞ P (Q.starProjection y))
    (hψ : ContDiffAt ℝ ∞ ψ y) : ContDiffAt ℝ ∞ (adjustmentMap Q P ψ) y := by
  have hQ : ContDiffAt ℝ ∞ (fun x => Q.starProjection x) y :=
    Q.starProjection.contDiff.contDiffAt
  have hPQ : ContDiffAt ℝ ∞ (fun x => P (Q.starProjection x)) y := hP.comp y hQ
  exact contDiffAt_id.add (hψ.smul (hPQ.sub hQ))

/-- Off the closed support: `Ψ` is the identity near `y`, hence smooth at `y`. -/
theorem adjustmentMap_contDiffAt_of_notMem_GAF6 (Q : Submodule ℝ H) [Q.HasOrthogonalProjection]
    (P : H → H) {ψ : H → ℝ} {y : H} (hy : y ∉ tsupport ψ) :
    ContDiffAt ℝ ∞ (adjustmentMap Q P ψ) y :=
  contDiffAt_id.congr_of_eventuallyEq (adjustmentMap_eventuallyEq_id_GAF5 Q P hy)

variable {X : Type*}

/-- **CFS16's half tube**: with `E ≤ 3Σ/10` and the preimage ratio, a localized point has
`π_Q f(p) ∈ B(x, Σρ(sel x))`, `x = π_Q F(p)`. -/
theorem stage_step_mem_ball_GAF6 (Q : Submodule ℝ H) [Q.HasOrthogonalProjection] (S : Set H)
    (sel : H → X) (ρ : X → ℝ) {sg E : ℝ} (hsg : 0 < sg) (hE : E ≤ 3 * sg / 10)
    (F f : X → H) {p : X} (hρp : 0 < ρ p) (hxS : Q.starProjection (F p) ∈ S)
    (hratio : ∀ x ∈ S, ∀ q, Q.starProjection (F q) = x →
      3 / 5 * ρ q ≤ ρ (sel x) ∧ ρ (sel x) ≤ 5 / 3 * ρ q)
    (hprior : ‖f p - F p‖ ≤ E * ρ p) :
    Q.starProjection (f p) ∈ ball (Q.starProjection (F p))
      (sg * ρ (sel (Q.starProjection (F p)))) := by
  obtain ⟨hr1, -⟩ := hratio _ hxS p rfl
  have hzx : ‖Q.starProjection (f p) - Q.starProjection (F p)‖ ≤ E * ρ p := by
    rw [← map_sub]
    exact (Q.norm_starProjection_apply_le _).trans hprior
  rw [mem_ball, dist_eq_norm]
  have h1 : E * ρ p ≤ 3 * sg / 10 * ρ p := mul_le_mul_of_nonneg_right hE hρp.le
  have hr1' : ρ p ≤ 5 / 3 * ρ (sel (Q.starProjection (F p))) := by linarith
  have h2 : 3 * sg / 10 * ρ p ≤ 3 * sg / 10 * (5 / 3 * ρ (sel (Q.starProjection (F p)))) :=
    mul_le_mul_of_nonneg_left hr1' (by positivity)
  have hsel0 : 0 < ρ (sel (Q.starProjection (F p))) := by linarith
  nlinarith

/-- **The stage map is smooth at every point of the preceding output** (CFS18): either `f p` is
off the closed support of `ψ`, or it localizes into a ball where the stage projection is smooth. -/
theorem stage_step_contDiffAt_point_GAF6 (Q : Submodule ℝ H) [Q.HasOrthogonalProjection]
    (S : Set H) (sel : H → X) (ρ : X → ℝ) (Pst : H → H) (ψ : H → ℝ) {sg E : ℝ} (hsg : 0 < sg)
    (hE : E ≤ 3 * sg / 10)
    (hPsm : ∀ x ∈ S, ∀ z ∈ ball x (sg * ρ (sel x)), ContDiffAt ℝ ∞ Pst z)
    (F f : X → H) {p : X} (hρp : 0 < ρ p)
    (hloc : f p ∈ tsupport ψ → Q.starProjection (F p) ∈ S)
    (hratio : ∀ x ∈ S, ∀ q, Q.starProjection (F q) = x →
      3 / 5 * ρ q ≤ ρ (sel x) ∧ ρ (sel x) ≤ 5 / 3 * ρ q)
    (hprior : ‖f p - F p‖ ≤ E * ρ p) (hψsm : f p ∈ tsupport ψ → ContDiffAt ℝ ∞ ψ (f p)) :
    ContDiffAt ℝ ∞ (adjustmentMap Q Pst ψ) (f p) := by
  by_cases hp : f p ∈ tsupport ψ
  · have hxS := hloc hp
    exact adjustmentMap_contDiffAt_GAF6 Q
      (hPsm _ hxS _ (stage_step_mem_ball_GAF6 Q S sel ρ hsg hE F f hρp hxS hratio hprior))
      (hψsm hp)
  · exact adjustmentMap_contDiffAt_of_notMem_GAF6 Q Pst hp

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] {G : Type*} [TopologicalSpace G]
  {I : ModelWithCorners ℝ E' G} {M : Type*} [TopologicalSpace M] [ChartedSpace G M]

/-- A map smooth at every point of the image of a smooth manifold map gives a smooth composite. -/
theorem contMDiff_comp_of_contDiffAt_GAF6 {f : M → H} {Ψ : H → H}
    (hf : ContMDiff I 𝓘(ℝ, H) ∞ f) (hΨ : ∀ p, ContDiffAt ℝ ∞ Ψ (f p)) :
    ContMDiff I 𝓘(ℝ, H) ∞ (Ψ ∘ f) :=
  fun p => (hΨ p).contMDiffAt.comp p (hf p)

/-- **The projected stage map** `π_Q ∘ a`: if the planes and the centres lie in `Q`, it keeps
CFS14 (3)'s value and derivative bounds of `a` on every ball, takes values in `Q`, and is smooth
wherever `a` is. -/
theorem projected_stage_map_GAF6 (Q : Submodule ℝ H) [Q.HasOrthogonalProjection] (S : Set H)
    (r : H → ℝ) (plane : H → Submodule ℝ H) [∀ x, (plane x).HasOrthogonalProjection]
    (hplane : ∀ x ∈ S, plane x ≤ Q) (hSQ : S ⊆ Q) (a : H → H) {Ξ : ℝ}
    (ha : ∀ x ∈ S, ∀ z ∈ ball x (r x),
      ‖a z - (x + (plane x).starProjection (z - x))‖ ≤ Ξ * r x ∧ DifferentiableAt ℝ a z ∧
        ‖fderiv ℝ a z - (plane x).starProjection‖ ≤ Ξ) :
    (∀ z, Q.starProjection (a z) ∈ Q) ∧
      (∀ z, ContDiffAt ℝ ∞ a z → ContDiffAt ℝ ∞ (fun y => Q.starProjection (a y)) z) ∧
      ∀ x ∈ S, ∀ z ∈ ball x (r x),
        ‖Q.starProjection (a z) - (x + (plane x).starProjection (z - x))‖ ≤ Ξ * r x ∧
        DifferentiableAt ℝ (fun y => Q.starProjection (a y)) z ∧
        ‖fderiv ℝ (fun y => Q.starProjection (a y)) z - (plane x).starProjection‖ ≤ Ξ := by
  refine ⟨fun z => Q.starProjection_apply_mem _, fun z hz =>
    Q.starProjection.contDiff.contDiffAt.comp z hz, fun x hx z hz => ?_⟩
  obtain ⟨hv, hd, hD⟩ := ha x hx z hz
  have hfix : ∀ w ∈ Q, Q.starProjection w = w := fun w hw =>
    Q.starProjection_eq_self_iff.mpr hw
  have hmem : x + (plane x).starProjection (z - x) ∈ Q :=
    Q.add_mem (hSQ hx) (hplane x hx ((plane x).starProjection_apply_mem _))
  have hDcomp : fderiv ℝ (fun y => Q.starProjection (a y)) z =
      Q.starProjection.comp (fderiv ℝ a z) :=
    (Q.starProjection.hasFDerivAt.comp z hd.hasFDerivAt).fderiv
  refine ⟨?_, (Q.starProjection.differentiableAt).comp z hd, ?_⟩
  · rw [← hfix _ hmem, ← map_sub]
    exact (Q.norm_starProjection_apply_le _).trans hv
  · rw [hDcomp]
    refine ContinuousLinearMap.opNorm_le_bound _ ((norm_nonneg _).trans hD) fun v => ?_
    have hPi : Q.starProjection ((plane x).starProjection v) = (plane x).starProjection v :=
      hfix _ (hplane x hx ((plane x).starProjection_apply_mem _))
    have heq : (Q.starProjection.comp (fderiv ℝ a z) - (plane x).starProjection) v =
        Q.starProjection ((fderiv ℝ a z - (plane x).starProjection) v) := by
      simp only [sub_apply, ContinuousLinearMap.comp_apply, map_sub, hPi]
    rw [heq]
    calc ‖Q.starProjection ((fderiv ℝ a z - (plane x).starProjection) v)‖ ≤
        ‖(fderiv ℝ a z - (plane x).starProjection) v‖ := Q.norm_starProjection_apply_le _
      _ ≤ ‖fderiv ℝ a z - (plane x).starProjection‖ * ‖v‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ Ξ * ‖v‖ := mul_le_mul_of_nonneg_right hD (norm_nonneg v)

end DifferentialGeometry.Geometry.Collapse
