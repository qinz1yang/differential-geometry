import DifferentialGeometry.Geometry.Metric.RadialConeRays
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false

namespace GC.MetricGeometry

open Set
open scoped NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X]

structure TwoRayConeData (p : X) where
  rays : Set (ℝ≥0 → X)
  isometry : ∀ γ ∈ rays, Isometry γ
  basepoint : ∀ γ ∈ rays, γ 0 = p
  coverage : ∀ x, ∃ γ ∈ rays, ∃ t, γ t = x
  pair_distance : ∀ γ ∈ rays, ∀ η ∈ rays,
    ∃ u v : EuclideanSpace ℝ (Fin 2), ‖u‖ = 1 ∧ ‖v‖ = 1 ∧
      ∀ s t : ℝ≥0, dist (γ s) (η t) = dist ((s : ℝ) • u) ((t : ℝ) • v)

private theorem planar_ray_dist_sq (u v : EuclideanSpace ℝ (Fin 2))
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (s t : ℝ≥0) :
    dist ((s : ℝ) • u) ((t : ℝ) • v) ^ 2 =
      (s : ℝ) ^ 2 + (t : ℝ) ^ 2 - 2 * (s : ℝ) * (t : ℝ) * ⟪u, v⟫_ℝ := by
  rw [dist_eq_norm, norm_sub_sq_real]
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg s.coe_nonneg,
    abs_of_nonneg t.coe_nonneg, hu, hv, mul_one, real_inner_smul_left,
    real_inner_smul_right]
  ring

private theorem exists_planar_unit_vectors {c : ℝ} (hc : -1 ≤ c ∧ c ≤ 1) :
    ∃ u v : EuclideanSpace ℝ (Fin 2), ‖u‖ = 1 ∧ ‖v‖ = 1 ∧ ⟪u, v⟫_ℝ = c := by
  let u : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![1, 0]
  let v : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![c, Real.sqrt (1 - c ^ 2)]
  have hc2 : 0 ≤ 1 - c ^ 2 := by nlinarith [hc.1, hc.2]
  have hu : ‖u‖ = 1 := by
    have hh := EuclideanSpace.real_norm_sq_eq u
    simp only [Fin.sum_univ_two] at hh
    change ‖u‖ ^ 2 = 1 ^ 2 + 0 ^ 2 at hh
    nlinarith [norm_nonneg u]
  have hv : ‖v‖ = 1 := by
    have hh := EuclideanSpace.real_norm_sq_eq v
    simp only [Fin.sum_univ_two] at hh
    change ‖v‖ ^ 2 = c ^ 2 + Real.sqrt (1 - c ^ 2) ^ 2 at hh
    rw [Real.sq_sqrt hc2] at hh
    nlinarith [norm_nonneg v]
  refine ⟨u, v, hu, hv, ?_⟩
  simp [u, v, PiLp.inner_apply, Fin.sum_univ_two]

namespace TwoRayConeData

variable {p : X} (C : TwoRayConeData p)

theorem dist_apex {γ : ℝ≥0 → X} (hγ : γ ∈ C.rays) (t : ℝ≥0) :
    dist p (γ t) = (t : ℝ) := by
  conv_lhs => arg 1; rw [← C.basepoint γ hγ]
  rw [(C.isometry γ hγ).dist_eq]
  change |(0 : ℝ) - t| = (t : ℝ)
  rw [zero_sub, abs_neg, abs_of_nonneg t.coe_nonneg]

noncomputable def chosenRay (x : X) : ℝ≥0 → X := (C.coverage x).choose

theorem chosenRay_mem (x : X) : C.chosenRay x ∈ C.rays := (C.coverage x).choose_spec.1

theorem chosenRay_through (x : X) : C.chosenRay x (nndist p x) = x := by
  obtain ⟨t, ht⟩ := (C.coverage x).choose_spec.2
  have hr := C.dist_apex (C.chosenRay_mem x) t
  change dist p ((C.coverage x).choose t) = (t : ℝ) at hr
  rw [ht] at hr
  have htn : t = nndist p x := by
    apply NNReal.eq
    exact hr.symm
  rw [← htn]
  exact ht

noncomputable def toRadialConeData : RadialConeData p where
  map t x := C.chosenRay x (t * nndist p x)
  map_zero x := by rw [zero_mul]; exact C.basepoint _ (C.chosenRay_mem x)
  map_one x := by rw [one_mul]; exact C.chosenRay_through x
  dist_sq s t x y := by
    obtain ⟨u, v, hu, hv, hpair⟩ := C.pair_distance
      (C.chosenRay x) (C.chosenRay_mem x) (C.chosenRay y) (C.chosenRay_mem y)
    have hxy := hpair (nndist p x) (nndist p y)
    rw [C.chosenRay_through, C.chosenRay_through] at hxy
    have hsq := congrArg (fun r : ℝ => r ^ 2) hxy
    rw [planar_ray_dist_sq u v hu hv] at hsq
    simp only [coe_nndist] at hsq
    rw [hpair, planar_ray_dist_sq u v hu hv]
    simp only [NNReal.coe_mul, coe_nndist]
    unfold radialConeKernel
    rw [hsq]
    ring

end TwoRayConeData

namespace RadialConeData

variable {p : X} (H : RadialConeData p)

theorem unitRay_pair_distance {x y : X} (hx : x ≠ p) (hy : y ≠ p) :
    ∃ u v : EuclideanSpace ℝ (Fin 2), ‖u‖ = 1 ∧ ‖v‖ = 1 ∧
      ∀ s t : ℝ≥0, dist (H.unitRay x s) (H.unitRay y t) =
        dist ((s : ℝ) • u) ((t : ℝ) • v) := by
  have hxpos : 0 < dist p x := dist_pos.mpr hx.symm
  have hypos : 0 < dist p y := dist_pos.mpr hy.symm
  let c := radialConeKernel p x y / (dist p x * dist p y)
  have hc : -1 ≤ c ∧ c ≤ 1 := by
    obtain ⟨hl, hu⟩ := radialConeKernel_bounds p x y
    dsimp [c]
    constructor
    · exact (le_div_iff₀ (mul_pos hxpos hypos)).mpr (by linarith)
    · exact (div_le_iff₀ (mul_pos hxpos hypos)).mpr (by linarith)
  obtain ⟨u, v, hu, hv, huv⟩ := exists_planar_unit_vectors hc
  refine ⟨u, v, hu, hv, fun s t => ?_⟩
  apply (sq_eq_sq₀ dist_nonneg dist_nonneg).mp
  rw [planar_ray_dist_sq u v hu hv, huv]
  change dist (H.map (s / nndist p x) x) (H.map (t / nndist p y) y) ^ 2 = _
  rw [H.dist_sq]
  simp only [NNReal.coe_div, coe_nndist]
  dsimp [c]
  field_simp

noncomputable def toTwoRayConeData [Nontrivial X] : TwoRayConeData p where
  rays := Set.range (fun x : {x : X // x ≠ p} => H.unitRay x.val)
  isometry γ hγ := by
    obtain ⟨x, rfl⟩ := hγ
    exact H.unitRay_isometry x.property
  basepoint γ hγ := by
    obtain ⟨x, rfl⟩ := hγ
    exact H.unitRay_zero x.val
  coverage x := by
    by_cases hx : x = p
    · obtain ⟨y, hy⟩ := exists_ne p
      exact ⟨H.unitRay y, ⟨⟨y, hy⟩, rfl⟩, 0, (H.unitRay_zero y).trans hx.symm⟩
    · exact ⟨H.unitRay x, ⟨⟨x, hx⟩, rfl⟩, nndist p x, H.unitRay_through hx⟩
  pair_distance γ hγ η hη := by
    obtain ⟨x, rfl⟩ := hγ
    obtain ⟨y, rfl⟩ := hη
    exact H.unitRay_pair_distance x.property y.property

end RadialConeData

theorem nonempty_radialConeData_iff_twoRayConeData {p : X} [Nontrivial X] :
    Nonempty (RadialConeData p) ↔ Nonempty (TwoRayConeData p) :=
  ⟨fun ⟨H⟩ => ⟨H.toTwoRayConeData⟩, fun ⟨C⟩ => ⟨C.toRadialConeData⟩⟩


end GC.MetricGeometry
