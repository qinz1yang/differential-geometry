import DifferentialGeometry.Geometry.Metric.Cfs15StageOutput

/-!
# The locality kernel of BCG04 / BCG05 on one native stage output

Blueprint `master207B.tex`, BCG04 (B:9132, global physical boundary-block isolation) and BCG05
(B:9202, exact boundary marker at every contributing plane); external draft 61 §3.4–3.5,
disposition D61-8. Both proofs read the WHOLE contributor window of the smoothing at the original
stage core point `x`: every selected centre `i` with `B̄(i, 80ε⁻¹r_i) ∩ B(x, 8ε⁻¹r_x) ≠ ∅` (not only
the centres whose weight is nonzero at the input). This file turns GAF03's three-level locality
`Cfs15StageOutput.locality_C15` (stated with a submodule `Kk` and a vector `c`) into the form the two
rows consume, for an arbitrary continuous linear map `J : H →L[ℝ] F` (the projection `J_b` onto a
whole boundary block) and a value `c : F`:

* `Cfs15StageOutput.exists_contributor_BLOC`: the window at `x ∈ S` is never empty.
* `Cfs15StageOutput.affine_locality_BLOC`: if every contributor `i` of the window has `J i = c`
  and plane `P i ≤ ker J`, then `J ∘ η = J − c` on `B(x, 8ε⁻¹r_x)`, `J ≡ c` on the native zero set
  there, and on `B(x, r_x)` the ambient nearest map `a`, the nearest map `p` and `D a` satisfy
  `J (a z) = c`, `J (p z) = c`, `J ∘ D a(z) = 0`.
* `linear_kernel_BLOC` (`c = 0`: everything lands in `ker J`, BCG04's form) and
  `scalar_marker_BLOC` (`F = ℝ`, `c = 1`: BCG05's scalar marker `v_b`; only the scalar kernel, the
  height direction stays free); `_of_cloud_BLOC` forms with the contributor hypotheses on `S`.

The rows' binding (contributors' actual support lists and model preimages give `J_b y = 0`,
`L_y ⊆ ker J_b`, resp. `v_b y = 1`, `L_y ⊆ ker v_b`) belongs to the boundary chain.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter
open scoped ContDiff Manifold Topology

namespace GC.MetricGeometry

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- `J ∘ π_{(ker J)ᗮ} = J` for a continuous linear map on a finite-dimensional space. -/
theorem clm_apply_starProjection_kerOrth_BLOC (J : H →L[ℝ] F) (w : H) :
    J ((LinearMap.ker (J : H →ₗ[ℝ] F))ᗮ.starProjection w) = J w := by
  have h := Submodule.sub_starProjection_mem_orthogonal
    (K := (LinearMap.ker (J : H →ₗ[ℝ] F))ᗮ) w
  rw [Submodule.orthogonal_orthogonal] at h
  have h0 : J (w - (LinearMap.ker (J : H →ₗ[ℝ] F))ᗮ.starProjection w) = 0 := h
  rw [map_sub, sub_eq_zero] at h0
  exact h0.symm

namespace Cfs15StageOutput

variable {k K : ℕ} {ε cw : ℝ} {S T : Set H} {r : H → ℝ} {P : H → Submodule ℝ H}

/-- **The contributor window is never empty**: for `x ∈ S` some selected centre `i` has
`x ∈ B̄(i, 80ε⁻¹r_i) ∩ B(x, 8ε⁻¹r_x)` (the tube covers `x`). -/
theorem exists_contributor_BLOC (O : Cfs15StageOutput k K ε cw S T r P) {x : H} (hx : x ∈ S) :
    ∃ i ∈ O.I, x ∈ closedBall i (80 * ε⁻¹ * r i) ∩ ball x (8 * ε⁻¹ * r x) := by
  have hrx := O.radius_pos x hx
  have hε := O.eps_pos
  have hxx : x ∈ ball x (8 * ε⁻¹ * r x) := mem_ball_self (by positivity)
  obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (O.ball_subset_tube hx hxx)
  refine ⟨i, hi, ?_, hxx⟩
  have hri := O.radius_pos_I i hi
  rw [mem_closedBall]
  have h1 : dist x i < 20 * ε⁻¹ * r i := hxi
  have h2 : 0 < ε⁻¹ * r i := by positivity
  linarith

/-- **The affine locality kernel** (BCG04 / BCG05 at one stage). If every contributor `i` of the
whole window at `x ∈ S` (`B̄(i, 80ε⁻¹r_i) ∩ B(x, 8ε⁻¹r_x) ≠ ∅`) has `J i = c` and `P i ≤ ker J`,
then: `J (η z) = J z − c` on `B(x, 8ε⁻¹r_x)`; `J w = c` on `Z ∩ B(x, 8ε⁻¹r_x)`; and on `B(x, r_x)`:
`J (a z) = c`, `J (p z) = c` for the nearest map, and `J ∘ D a(z) = 0`. -/
theorem affine_locality_BLOC (O : Cfs15StageOutput k K ε cw S T r P) {x : H} (hx : x ∈ S)
    (J : H →L[ℝ] F) (c : F)
    (hcontrib : ∀ i ∈ O.I, (closedBall i (80 * ε⁻¹ * r i) ∩ ball x (8 * ε⁻¹ * r x)).Nonempty →
      J i = c ∧ P i ≤ LinearMap.ker (J : H →ₗ[ℝ] F)) :
    (∀ z ∈ ball x (8 * ε⁻¹ * r x), J (cfs15Section_C15 ε r P O.hI z) = J z - c) ∧
    (∀ w ∈ O.Z ∩ ball x (8 * ε⁻¹ * r x), J w = c) ∧
    (∀ z ∈ ball x (r x), J (O.ambient z) = c) ∧
    (∀ z (hz : z ∈ cfs15Omega_C15 S r), z ∈ ball x (r x) → J (O.p ⟨z, hz⟩ : H) = c) ∧
    (∀ z ∈ ball x (r x), J.comp (fderiv ℝ O.ambient z) = 0) := by
  obtain ⟨i₀, hi₀, hwin⟩ := O.exists_contributor_BLOC hx
  have hKo : (LinearMap.ker (J : H →ₗ[ℝ] F))ᗮᗮ = LinearMap.ker (J : H →ₗ[ℝ] F) :=
    Submodule.orthogonal_orthogonal _
  have hJK := clm_apply_starProjection_kerOrth_BLOC J
  have hc0 : J i₀ = c := (hcontrib i₀ hi₀ ⟨x, hwin⟩).1
  have hloc := O.locality_C15 hx (LinearMap.ker (J : H →ₗ[ℝ] F))ᗮ
    ((LinearMap.ker (J : H →ₗ[ℝ] F))ᗮ.starProjection i₀) (fun i hi hne => by
      obtain ⟨hJi, hPi⟩ := hcontrib i hi hne
      refine ⟨?_, by rw [hKo]; exact hPi⟩
      rw [← sub_eq_zero, ← map_sub, Submodule.starProjection_apply_eq_zero_iff, hKo,
        LinearMap.mem_ker]
      change J (i - i₀) = 0
      rw [map_sub, hJi, hc0, sub_self])
  have h3 : ∀ z ∈ ball x (r x), J (O.ambient z) = c := fun z hz => by
    have h := congrArg J (hloc.2.2 z hz)
    rwa [hJK, hJK, hc0] at h
  refine ⟨fun z hz => ?_, fun w hw => ?_, h3, fun z hzΩ hz => ?_, fun z hz => ?_⟩
  · have h := congrArg J (hloc.1 z hz)
    rwa [hJK, map_sub, hJK, hJK, hc0] at h
  · have h := congrArg J (hloc.2.1 w hw)
    rwa [hJK, hJK, hc0] at h
  · rw [← O.ambient_eq z hzΩ]
    exact h3 z hz
  · have hev : (fun y => J (O.ambient y)) =ᶠ[𝓝 z] fun _ => c :=
      eventually_of_mem (isOpen_ball.mem_nhds hz) fun y hy => h3 y hy
    have hda : DifferentiableAt ℝ O.ambient z := (O.ambient_value_deriv hx hz).2.1
    have hcomp : fderiv ℝ (fun y => J (O.ambient y)) z = J.comp (fderiv ℝ O.ambient z) :=
      (J.hasFDerivAt.comp z hda.hasFDerivAt).fderiv
    rw [← hcomp, hev.fderiv_eq]
    exact fderiv_const_apply c

/-- **BCG04's linear kernel** (`c = 0`): if every contributor `i` of the whole window at `x ∈ S`
has `J i = 0` and `P i ≤ ker J`, then `J ∘ η = J` on `B(x, 8ε⁻¹r_x)`, the native zero set there lies
in `ker J`, and on `B(x, r_x)` the outputs `a z` and `p z` lie in `ker J` and `J ∘ D a(z) = 0`. -/
theorem linear_kernel_BLOC (O : Cfs15StageOutput k K ε cw S T r P) {x : H} (hx : x ∈ S)
    (J : H →L[ℝ] F)
    (hcontrib : ∀ i ∈ O.I, (closedBall i (80 * ε⁻¹ * r i) ∩ ball x (8 * ε⁻¹ * r x)).Nonempty →
      J i = 0 ∧ P i ≤ LinearMap.ker (J : H →ₗ[ℝ] F)) :
    (∀ z ∈ ball x (8 * ε⁻¹ * r x), J (cfs15Section_C15 ε r P O.hI z) = J z) ∧
    O.Z ∩ ball x (8 * ε⁻¹ * r x) ⊆ LinearMap.ker (J : H →ₗ[ℝ] F) ∧
    (∀ z ∈ ball x (r x), O.ambient z ∈ LinearMap.ker (J : H →ₗ[ℝ] F)) ∧
    (∀ z (hz : z ∈ cfs15Omega_C15 S r), z ∈ ball x (r x) →
      (O.p ⟨z, hz⟩ : H) ∈ LinearMap.ker (J : H →ₗ[ℝ] F)) ∧
    (∀ z ∈ ball x (r x), J.comp (fderiv ℝ O.ambient z) = 0) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := O.affine_locality_BLOC hx J 0 hcontrib
  exact ⟨fun z hz => by rw [h1 z hz, sub_zero], fun w hw => h2 w hw, fun z hz => h3 z hz,
    fun z hzΩ hz => h4 z hzΩ hz, h5⟩

/-- **BCG05's scalar marker kernel** (`F = ℝ`, `c = 1`): if every contributor `i` of the whole
window at `x ∈ S` has `v i = 1` and `P i ≤ ker v`, then `v ∘ η = v − 1` on `B(x, 8ε⁻¹r_x)`, `v ≡ 1`
on the native zero set there, and on `B(x, r_x)`: `v (a z) = 1`, `v (p z) = 1`, `v ∘ D a(z) = 0`. -/
theorem scalar_marker_BLOC (O : Cfs15StageOutput k K ε cw S T r P) {x : H} (hx : x ∈ S)
    (v : H →L[ℝ] ℝ)
    (hcontrib : ∀ i ∈ O.I, (closedBall i (80 * ε⁻¹ * r i) ∩ ball x (8 * ε⁻¹ * r x)).Nonempty →
      v i = 1 ∧ P i ≤ LinearMap.ker (v : H →ₗ[ℝ] ℝ)) :
    (∀ z ∈ ball x (8 * ε⁻¹ * r x), v (cfs15Section_C15 ε r P O.hI z) = v z - 1) ∧
    (∀ w ∈ O.Z ∩ ball x (8 * ε⁻¹ * r x), v w = 1) ∧
    (∀ z ∈ ball x (r x), v (O.ambient z) = 1) ∧
    (∀ z (hz : z ∈ cfs15Omega_C15 S r), z ∈ ball x (r x) → v (O.p ⟨z, hz⟩ : H) = 1) ∧
    (∀ z ∈ ball x (r x), v.comp (fderiv ℝ O.ambient z) = 0) :=
  O.affine_locality_BLOC hx v 1 hcontrib

/-- `affine_locality_BLOC` with the contributor hypothesis on the whole cloud `S`. -/
theorem affine_locality_of_cloud_BLOC (O : Cfs15StageOutput k K ε cw S T r P) {x : H}
    (hx : x ∈ S) (J : H →L[ℝ] F) (c : F)
    (hcontrib : ∀ i ∈ S, (closedBall i (80 * ε⁻¹ * r i) ∩ ball x (8 * ε⁻¹ * r x)).Nonempty →
      J i = c ∧ P i ≤ LinearMap.ker (J : H →ₗ[ℝ] F)) :
    (∀ z ∈ ball x (8 * ε⁻¹ * r x), J (cfs15Section_C15 ε r P O.hI z) = J z - c) ∧
    (∀ w ∈ O.Z ∩ ball x (8 * ε⁻¹ * r x), J w = c) ∧
    (∀ z ∈ ball x (r x), J (O.ambient z) = c) ∧
    (∀ z (hz : z ∈ cfs15Omega_C15 S r), z ∈ ball x (r x) → J (O.p ⟨z, hz⟩ : H) = c) ∧
    (∀ z ∈ ball x (r x), J.comp (fderiv ℝ O.ambient z) = 0) :=
  O.affine_locality_BLOC hx J c fun i hi => hcontrib i (O.I_subset hi)

/-- `linear_kernel_BLOC` with the contributor hypothesis on the whole cloud `S`. -/
theorem linear_kernel_of_cloud_BLOC (O : Cfs15StageOutput k K ε cw S T r P) {x : H}
    (hx : x ∈ S) (J : H →L[ℝ] F)
    (hcontrib : ∀ i ∈ S, (closedBall i (80 * ε⁻¹ * r i) ∩ ball x (8 * ε⁻¹ * r x)).Nonempty →
      J i = 0 ∧ P i ≤ LinearMap.ker (J : H →ₗ[ℝ] F)) :
    (∀ z ∈ ball x (8 * ε⁻¹ * r x), J (cfs15Section_C15 ε r P O.hI z) = J z) ∧
    O.Z ∩ ball x (8 * ε⁻¹ * r x) ⊆ LinearMap.ker (J : H →ₗ[ℝ] F) ∧
    (∀ z ∈ ball x (r x), O.ambient z ∈ LinearMap.ker (J : H →ₗ[ℝ] F)) ∧
    (∀ z (hz : z ∈ cfs15Omega_C15 S r), z ∈ ball x (r x) →
      (O.p ⟨z, hz⟩ : H) ∈ LinearMap.ker (J : H →ₗ[ℝ] F)) ∧
    (∀ z ∈ ball x (r x), J.comp (fderiv ℝ O.ambient z) = 0) :=
  O.linear_kernel_BLOC hx J fun i hi => hcontrib i (O.I_subset hi)

/-- `scalar_marker_BLOC` with the contributor hypothesis on the whole cloud `S`. -/
theorem scalar_marker_of_cloud_BLOC (O : Cfs15StageOutput k K ε cw S T r P) {x : H}
    (hx : x ∈ S) (v : H →L[ℝ] ℝ)
    (hcontrib : ∀ i ∈ S, (closedBall i (80 * ε⁻¹ * r i) ∩ ball x (8 * ε⁻¹ * r x)).Nonempty →
      v i = 1 ∧ P i ≤ LinearMap.ker (v : H →ₗ[ℝ] ℝ)) :
    (∀ z ∈ ball x (8 * ε⁻¹ * r x), v (cfs15Section_C15 ε r P O.hI z) = v z - 1) ∧
    (∀ w ∈ O.Z ∩ ball x (8 * ε⁻¹ * r x), v w = 1) ∧
    (∀ z ∈ ball x (r x), v (O.ambient z) = 1) ∧
    (∀ z (hz : z ∈ cfs15Omega_C15 S r), z ∈ ball x (r x) → v (O.p ⟨z, hz⟩ : H) = 1) ∧
    (∀ z ∈ ball x (r x), v.comp (fderiv ℝ O.ambient z) = 0) :=
  O.scalar_marker_BLOC hx v fun i hi => hcontrib i (O.I_subset hi)

end Cfs15StageOutput

end GC.MetricGeometry
