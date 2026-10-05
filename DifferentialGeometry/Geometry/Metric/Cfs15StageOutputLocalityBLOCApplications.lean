import DifferentialGeometry.Geometry.Metric.Cfs15StageOutputApplications
import DifferentialGeometry.Geometry.Metric.Cfs15StageOutputLocalityBLOC

/-!
# Consumers of the BCG04 / BCG05 locality kernel: flat clouds in a plane

* The linear kernel on the flat inhabitant of `Cfs15StageOutputApplications`: on a flat cloud in a
  subspace `L ≤ ker J` the ambient nearest map stays in `ker J` with `J ∘ D a = 0`
  (`flat_linear_kernel_BLOC`).
* A translated flat inhabitant (`exists_cfs15StageOutput_affineFlat_BLOC`: the cloud
  `(q + L) ∩ B̄(q, 1) ⊆ q + L`, radius `1`, plane `L`) and the scalar kernel on it: a functional with
  `L ≤ ker v` and `v q = 1` stays exactly `1` on the ambient nearest map
  (`affineFlat_scalar_marker_BLOC`).
* Explicit instances in `ℝ²`: the first axis `L₀ = ℝ e₀` with `J = ` the second coordinate
  (`plane_flat_linear_kernel_BLOC`), and the line `e₁ + L₀` with the second coordinate as the
  scalar marker `= 1` (`plane_affineFlat_scalar_marker_BLOC`).
-/

set_option autoImplicit false

noncomputable section

open Set Metric
open scoped ContDiff Manifold Topology

namespace GC.MetricGeometry

universe u

/-- **The linear kernel on the flat inhabitant**: on the flat cloud `L ∩ B̄(0, 1)` with `L ≤ ker J`,
the ambient nearest map sends every `B(x, 1)` (`x` in the cloud) into `ker J` and `J ∘ D a = 0`. -/
theorem flat_linear_kernel_BLOC {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {k K : ℕ}
    {ε cw : ℝ} (L : Submodule ℝ H)
    (O : Cfs15StageOutput k K ε cw ((L : Set H) ∩ closedBall 0 1) (L : Set H) (fun _ => 1)
      (fun _ => L)) (J : H →L[ℝ] F) (hLJ : L ≤ LinearMap.ker (J : H →ₗ[ℝ] F)) :
    ∀ x ∈ (L : Set H) ∩ closedBall 0 1, ∀ z ∈ ball x 1,
      O.ambient z ∈ LinearMap.ker (J : H →ₗ[ℝ] F) ∧ J.comp (fderiv ℝ O.ambient z) = 0 := by
  intro x hx z hz
  have h := O.linear_kernel_of_cloud_BLOC hx J fun i hi _ => ⟨hLJ hi.1, hLJ⟩
  exact ⟨h.2.2.1 z hz, h.2.2.2.2 z hz⟩

/-- **A translated flat cloud carries a stage output.** For `0 < ε ≤ 1/10` there is `c_w ≥ 0` such
that for every `k`-dimensional subspace `L` and every point `q`, the cloud
`(q + L) ∩ B̄(q, 1) ⊆ q + L` with radius `1` and plane `L` has a stage output. -/
theorem exists_cfs15StageOutput_affineFlat_BLOC (k K : ℕ) (ε : ℝ) (hε : 0 < ε)
    (hεsmall : ε ≤ 1 / 10) :
    ∃ cw : ℝ, 0 ≤ cw ∧
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
        (L : Submodule ℝ H) (q : H), Module.finrank ℝ L = k →
        Nonempty (Cfs15StageOutput k K ε cw
          ((AffineSubspace.mk' q L : Set H) ∩ closedBall q 1) (AffineSubspace.mk' q L : Set H)
          (fun _ => 1) (fun _ => L)) := by
  obtain ⟨cw, hcw, δ₀, hδ₀, h⟩ := exists_cfs15StageOutput_C15.{u} k K 1 ε le_rfl hε hεsmall
  refine ⟨cw, hcw, fun H _ _ _ L q hL => ?_⟩
  refine h H _ _ inter_subset_left
    ((isCompact_closedBall q 1).totallyBounded.subset inter_subset_right) (fun _ => 1)
    (fun _ => L) (fun _ _ => hL) 1 1 δ₀ one_pos (fun _ _ => le_rfl) (fun _ _ => le_rfl) hδ₀
    le_rfl (fun _ _ _ _ _ => by norm_num) ?_
  intro x hx
  have hmk : AffineSubspace.mk' x L = AffineSubspace.mk' q L := by
    conv_lhs => rw [← AffineSubspace.direction_mk' q L]
    exact AffineSubspace.mk'_eq hx.1
  rw [hmk, hausdorffEDist_self]
  exact zero_le

/-- **The scalar kernel on the translated flat inhabitant**: if `L ≤ ker v` and `v q = 1`, the
ambient nearest map of the cloud `(q + L) ∩ B̄(q, 1)` has `v ∘ a = 1` and `v ∘ D a = 0` on every
`B(x, 1)`. -/
theorem affineFlat_scalar_marker_BLOC {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] {k K : ℕ} {ε cw : ℝ} (L : Submodule ℝ H) (q : H)
    (O : Cfs15StageOutput k K ε cw ((AffineSubspace.mk' q L : Set H) ∩ closedBall q 1)
      (AffineSubspace.mk' q L : Set H) (fun _ => 1) (fun _ => L)) (v : H →L[ℝ] ℝ)
    (hLv : L ≤ LinearMap.ker (v : H →ₗ[ℝ] ℝ)) (hq : v q = 1) :
    ∀ x ∈ (AffineSubspace.mk' q L : Set H) ∩ closedBall q 1, ∀ z ∈ ball x 1,
      v (O.ambient z) = 1 ∧ v.comp (fderiv ℝ O.ambient z) = 0 := by
  intro x hx z hz
  have hval : ∀ y ∈ (AffineSubspace.mk' q L : Set H), v y = 1 := fun y hy => by
    have hyq : y - q ∈ L := by
      have := AffineSubspace.mem_mk'.mp hy
      rwa [vsub_eq_sub] at this
    have h0 : v (y - q) = 0 := hLv hyq
    rw [map_sub, hq, sub_eq_zero] at h0
    exact h0
  have h := O.scalar_marker_of_cloud_BLOC hx v fun i hi _ => ⟨hval i hi.1, hLv⟩
  exact ⟨h.2.2.1 z hz, h.2.2.2.2 z hz⟩

/-- The first axis `ℝ e₀` of `ℝ²`. -/
abbrev planeAxisZero_BLOC : Submodule ℝ (EuclideanSpace ℝ (Fin 2)) :=
  Submodule.span ℝ {EuclideanSpace.single (0 : Fin 2) (1 : ℝ)}

theorem finrank_planeAxisZero_BLOC : Module.finrank ℝ planeAxisZero_BLOC = 1 := by
  refine finrank_span_singleton ?_
  intro h
  have := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 0) h
  simp at this

theorem planeAxisZero_le_ker_BLOC :
    planeAxisZero_BLOC ≤ LinearMap.ker
      ((EuclideanSpace.proj (1 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) :
        EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] ℝ) := by
  rw [Submodule.span_le, singleton_subset_iff]
  change EuclideanSpace.proj (1 : Fin 2) (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) = 0
  simp

/-- **An explicit consumer in `ℝ²` (linear kernel).** For `0 < ε ≤ 1/10` and every jet order, the
flat cloud on the first axis has a stage output whose ambient nearest map has second coordinate
exactly `0` (and derivative of the second coordinate `0`) on every `B(x, 1)`. -/
theorem plane_flat_linear_kernel_BLOC (K : ℕ) (ε : ℝ) (hε : 0 < ε) (hεsmall : ε ≤ 1 / 10) :
    ∃ cw : ℝ, 0 ≤ cw ∧ ∃ O : Cfs15StageOutput 1 K ε cw
        ((planeAxisZero_BLOC : Set (EuclideanSpace ℝ (Fin 2))) ∩ closedBall 0 1)
        (planeAxisZero_BLOC : Set (EuclideanSpace ℝ (Fin 2))) (fun _ => 1)
        (fun _ => planeAxisZero_BLOC),
      ∀ x ∈ (planeAxisZero_BLOC : Set (EuclideanSpace ℝ (Fin 2))) ∩ closedBall 0 1,
        ∀ z ∈ ball x 1, EuclideanSpace.proj (1 : Fin 2) (O.ambient z) = 0 ∧
          (EuclideanSpace.proj (1 : Fin 2)).comp (fderiv ℝ O.ambient z) = 0 := by
  obtain ⟨cw, hcw, h⟩ := exists_cfs15StageOutput_flat_C15.{0} 1 K ε hε hεsmall
  obtain ⟨O⟩ := h (EuclideanSpace ℝ (Fin 2)) planeAxisZero_BLOC finrank_planeAxisZero_BLOC
  refine ⟨cw, hcw, O, fun x hx z hz => ?_⟩
  have h' := flat_linear_kernel_BLOC planeAxisZero_BLOC O (EuclideanSpace.proj (1 : Fin 2))
    planeAxisZero_le_ker_BLOC x hx z hz
  exact ⟨h'.1, h'.2⟩

/-- **An explicit consumer in `ℝ²` (scalar marker).** The flat cloud on the line `e₁ + ℝ e₀` has a
stage output whose ambient nearest map has second coordinate exactly `1` (with zero derivative)
on every `B(x, 1)`. -/
theorem plane_affineFlat_scalar_marker_BLOC (K : ℕ) (ε : ℝ) (hε : 0 < ε)
    (hεsmall : ε ≤ 1 / 10) :
    ∃ cw : ℝ, 0 ≤ cw ∧ ∃ O : Cfs15StageOutput 1 K ε cw
        ((AffineSubspace.mk' (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) planeAxisZero_BLOC :
            Set (EuclideanSpace ℝ (Fin 2))) ∩
          closedBall (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) 1)
        (AffineSubspace.mk' (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) planeAxisZero_BLOC :
          Set (EuclideanSpace ℝ (Fin 2))) (fun _ => 1) (fun _ => planeAxisZero_BLOC),
      ∀ x ∈ (AffineSubspace.mk' (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) planeAxisZero_BLOC :
            Set (EuclideanSpace ℝ (Fin 2))) ∩
          closedBall (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) 1,
        ∀ z ∈ ball x 1, EuclideanSpace.proj (1 : Fin 2) (O.ambient z) = 1 ∧
          (EuclideanSpace.proj (1 : Fin 2)).comp (fderiv ℝ O.ambient z) = 0 := by
  obtain ⟨cw, hcw, h⟩ := exists_cfs15StageOutput_affineFlat_BLOC.{0} 1 K ε hε hεsmall
  obtain ⟨O⟩ := h (EuclideanSpace ℝ (Fin 2)) planeAxisZero_BLOC
    (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) finrank_planeAxisZero_BLOC
  refine ⟨cw, hcw, O, fun x hx z hz => ?_⟩
  exact affineFlat_scalar_marker_BLOC planeAxisZero_BLOC _ O (EuclideanSpace.proj (1 : Fin 2))
    planeAxisZero_le_ker_BLOC (by simp) x hx z hz

end GC.MetricGeometry
