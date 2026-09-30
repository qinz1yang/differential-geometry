# Full AC83 independent acceptance

Thirteen public theorems, five definitions, one structure and four private helpers in three leaves add65 owned declarations, including42 generated declarations. The360-module gate checks1692 declarations in3195 jobs. All new transitive closures use only propext, Classical.choice and Quot.sound. Source-copy and accepted-import regression lint is silent;30 reports cover all19 public production declarations and11 concrete regressions. Declaration kinds were inspected; defLemma is unavailable. Earlier mathematical leaves are unchanged. The inherited AreaUpperBarrier warning is outside these closures. The separate blueprint static audit passes. No migrated-root/PDF/Overleaf build or human approval is claimed.

Root and two independent agents read the complete frozen proof and checked source contracts. An independent agent compiled the production lint and concrete driver. Root read all final added reverse-constructor/affine-roundtrip tests. Final acceptance tests import canonical production leaves. Production uses only targeted imports, no tactic umbrella. Docstrings in the temporary candidate were removed under the project leaf convention without changing its proof bodies.

The independent ray-family input consists of actual unit isometries, common apex, coverage and Euclidean planar pair realizations. Its conversion to full radial data is proved from the ordinary Euclidean norm identity. Conversely, explicit plane unit vectors realize the normalized metric polarization kernel in[-1,1]. There is no common plane embedding assumed for all rays. Literal pair-union onto isometries and their converse constructor preserve every original ray parameter, including coincident rays and the common apex. Zero-distance fibers make the union construction well-defined. Every supplied ray is the canonical ray; positive meetings force equality; the covering family equals all actual unit rays at the apex. The radial-family roundtrip preserves the original maps everywhere.

Independent ray inputs are constructed on the actual half-line and real line. Tests check all-parameter multiplication, positive and negative scaling, coincident and opposite onto union realizations, original parameter retention and unique half-line unit ray. A negative singleton control proves literal ray data impossible while actual radial data exist. The reverse constructor is applied to actual union isometries and recovers all original real-ray scalings, including3*(-5)=-15. A separately supplied affine radial cone at7 passes through the entire conversion roundtrip: every map remains7+s*(x-7), and its value at s3,x-5 is-29.

Full AC83, including the previously open KL two-ray equivalence, is proved. The nontrivial iff and the explicit singleton-or-two-ray iff keep KL's literal unit-ray convention distinct from the blueprint's allowed point. No angular quotient, angular metric triangle inequality, angular-link curvature, tangent producer or rescaling-only cone claim is made. Blueprint207 and migration interfaces remain unchanged.

```lean
import DifferentialGeometry.Geometry.Metric.TwoRayConeUnion
import DifferentialGeometry.Geometry.Metric.TwoRayConeCompatibility
import Mathlib.Tactic

set_option autoImplicit false

namespace GCTwoRayConventionReview

open GC.MetricGeometry
open scoped NNReal

private noncomputable def axis : EuclideanSpace ℝ (Fin 2) := PiLp.single 2 0 1

private theorem axis_norm : ‖axis‖ = 1 := by simp [axis]

/-- Input ray data on the actual half-line, independent of radial cone data. -/
private noncomputable def halfLineData : TwoRayConeData (0 : ℝ≥0) where
  rays := {id}
  isometry γ hγ := by
    have h : γ = id := Set.mem_singleton_iff.mp hγ
    subst γ
    exact isometry_id
  basepoint γ hγ := by
    have h : γ = id := Set.mem_singleton_iff.mp hγ
    subst γ
    rfl
  coverage x := ⟨id, Set.mem_singleton _, x, rfl⟩
  pair_distance γ hγ η hη := by
    have h1 : γ = id := Set.mem_singleton_iff.mp hγ
    have h2 : η = id := Set.mem_singleton_iff.mp hη
    subst γ
    subst η
    refine ⟨axis, axis, axis_norm, axis_norm, fun s t => ?_⟩
    change |(s : ℝ) - t| = dist ((s : ℝ) • axis) ((t : ℝ) • axis)
    rw [dist_eq_norm, ← sub_smul, norm_smul, axis_norm, mul_one, Real.norm_eq_abs]

theorem halfline_constructed_scaling :
    ∀ s t : ℝ≥0, halfLineData.toRadialConeData.map s t = s * t := by
  intro s t
  exact halfLineData.toRadialConeData_map_ray (γ := id) (by simp [halfLineData]) s t

theorem halfline_positive_scale_regression :
    halfLineData.toRadialConeData.map 3 5 = 15 := by
  rw [halfline_constructed_scaling]
  norm_num

theorem coincident_pair_has_onto_union_realization :
    ∃ u v : EuclideanSpace ℝ (Fin 2), ‖u‖ = 1 ∧ ‖v‖ = 1 ∧
      Nonempty (↥(Set.range (id : ℝ≥0 → ℝ≥0) ∪ Set.range id) ≃ᵢ
        ↥(Set.range (fun t : ℝ≥0 => (t : ℝ) • u) ∪
          Set.range (fun t : ℝ≥0 => (t : ℝ) • v))) := by
  obtain ⟨u, v, hu, hv, e, _, _⟩ := halfLineData.exists_pair_union_isometry
    (γ := id) (η := id) (by simp [halfLineData]) (by simp [halfLineData])
  exact ⟨u, v, hu, hv, ⟨e⟩⟩

theorem halfline_has_only_the_original_unit_ray (γ : ℝ≥0 → ℝ≥0)
    (hγ : Isometry γ) (hz : γ 0 = 0) : γ = id := by
  have hh := halfLineData.mem_rays_iff.mpr ⟨hγ, hz⟩
  exact Set.mem_singleton_iff.mp hh

theorem singleton_convention_is_separate :
    Nonempty (RadialConeData PUnit.unit) ∧ ¬ Nonempty (TwoRayConeData PUnit.unit) := by
  constructor
  · exact ⟨RadialConeData.ofSubsingleton _⟩
  · rintro ⟨C⟩
    exact C.not_subsingleton inferInstance


private def realRay (b : Bool) (t : ℝ≥0) : ℝ := if b then (t : ℝ) else -(t : ℝ)
private noncomputable def realDirection (b : Bool) : EuclideanSpace ℝ (Fin 2) :=
  if b then axis else -axis

private theorem realRay_isometry (b : Bool) : Isometry (realRay b) := by
  apply Isometry.of_dist_eq
  intro s t
  cases b
  · change |-(s : ℝ) - -(t : ℝ)| = |(s : ℝ) - t|
    rw [neg_sub_neg, abs_sub_comm]
  · rfl

private theorem realDirection_norm (b : Bool) : ‖realDirection b‖ = 1 := by
  cases b <;> simp [realDirection, axis_norm]

private theorem realRay_embedding (b : Bool) (t : ℝ≥0) :
    realRay b t • axis = (t : ℝ) • realDirection b := by
  cases b <;> simp [realRay, realDirection]

private theorem axis_embedding_isometry : Isometry (fun x : ℝ => x • axis) := by
  apply Isometry.of_dist_eq
  intro s t
  rw [dist_eq_norm, ← sub_smul, norm_smul, axis_norm, mul_one, Real.norm_eq_abs, Real.dist_eq]

/-- Two original opposite rays, built without any radial cone assumption. -/
private noncomputable def realRayData : TwoRayConeData (0 : ℝ) where
  rays := Set.range realRay
  isometry γ hγ := by obtain ⟨b, rfl⟩ := hγ; exact realRay_isometry b
  basepoint γ hγ := by obtain ⟨b, rfl⟩ := hγ; cases b <;> simp [realRay]
  coverage x := by
    by_cases hx : 0 ≤ x
    · exact ⟨realRay true, ⟨true, rfl⟩, x.toNNReal, by simp [realRay, Real.coe_toNNReal _ hx]⟩
    · have hx' : 0 ≤ -x := neg_nonneg.mpr (le_of_not_ge hx)
      exact ⟨realRay false, ⟨false, rfl⟩, (-x).toNNReal,
        by simp [realRay, Real.coe_toNNReal _ hx']⟩
  pair_distance γ hγ η hη := by
    obtain ⟨b, rfl⟩ := hγ
    obtain ⟨c, rfl⟩ := hη
    refine ⟨realDirection b, realDirection c, realDirection_norm b, realDirection_norm c, ?_⟩
    intro s t
    have hh := axis_embedding_isometry.dist_eq (realRay b s) (realRay c t)
    rw [realRay_embedding, realRay_embedding] at hh
    exact hh.symm

theorem opposite_ray_scaling_regression : realRayData.toRadialConeData.map 3 (-5) = -15 := by
  have hh := realRayData.toRadialConeData_map_ray (γ := realRay false) ⟨false, rfl⟩ 3 5
  norm_num [realRay] at hh
  exact hh

theorem positive_and_negative_rays_are_distinct : realRay true ≠ realRay false := by
  intro hh
  have he := congrFun hh 1
  norm_num [realRay] at he

theorem opposite_pair_has_onto_union_realization :
    ∃ u v : EuclideanSpace ℝ (Fin 2), ‖u‖ = 1 ∧ ‖v‖ = 1 ∧
      ∃ e : ↥(Set.range (realRay true) ∪ Set.range (realRay false)) ≃ᵢ
        ↥(Set.range (fun t : ℝ≥0 => (t : ℝ) • u) ∪
          Set.range (fun t : ℝ≥0 => (t : ℝ) • v)),
        (e ⟨5, Or.inl ⟨5, rfl⟩⟩).val = (5 : ℝ) • u ∧
        (e ⟨-5, Or.inr ⟨5, rfl⟩⟩).val = (5 : ℝ) • v := by
  obtain ⟨u, v, hu, hv, e, heplus, heminus⟩ := realRayData.exists_pair_union_isometry
    (γ := realRay true) (η := realRay false) ⟨true, rfl⟩ ⟨false, rfl⟩
  exact ⟨u, v, hu, hv, e, heplus 5, heminus 5⟩


/-- Reconstruct the ray interface from ACTUAL union isometries and then recover
scaling on both original real rays. -/
theorem original_ray_scaling_from_union_isometries :
    let C := TwoRayConeData.ofPairUnionIsometries (0 : ℝ) realRayData.rays
      realRayData.isometry realRayData.basepoint realRayData.coverage
      (fun _ hγ _ hη => realRayData.exists_pair_union_isometry hγ hη)
    (∀ (b : Bool) (s t : ℝ≥0), C.toRadialConeData.map s (realRay b t) = realRay b (s * t)) ∧
      C.toRadialConeData.map 3 (-5) = -15 := by
  dsimp only
  let C := TwoRayConeData.ofPairUnionIsometries (0 : ℝ) realRayData.rays
    realRayData.isometry realRayData.basepoint realRayData.coverage
    (fun _ hγ _ hη => realRayData.exists_pair_union_isometry hγ hη)
  change (∀ (b : Bool) (s t : ℝ≥0), C.toRadialConeData.map s (realRay b t) = realRay b (s * t)) ∧ _
  have hscale (b : Bool) (s t : ℝ≥0) :=
    C.toRadialConeData_map_ray (γ := realRay b) ⟨b, rfl⟩ s t
  refine ⟨hscale, ?_⟩
  have hh := hscale false 3 5
  norm_num [realRay] at hh
  exact hh

/-- Independent actual translated radial maps, not obtained from ray data. -/
private noncomputable def affineRealCone (p : ℝ) : RadialConeData p where
  map t x := p + (t : ℝ) * (x - p)
  map_zero x := by simp
  map_one x := by simp
  dist_sq s t x y := by
    simp only [radialConeKernel, Real.dist_eq, sq_abs]
    ring

theorem translated_radial_roundtrip_everywhere (s : ℝ≥0) (x : ℝ) :
    (affineRealCone 7).toTwoRayConeData.toRadialConeData.map s x =
      7 + (s : ℝ) * (x - 7) :=
  (affineRealCone 7).toTwoRayConeData_toRadialConeData_map s x

theorem translated_radial_roundtrip_numeric :
    (affineRealCone 7).toTwoRayConeData.toRadialConeData.map 3 (-5) = -29 := by
  rw [translated_radial_roundtrip_everywhere]
  norm_num

end GCTwoRayConventionReview

#print axioms GC.MetricGeometry.TwoRayConeData
#print axioms GC.MetricGeometry.TwoRayConeData.dist_apex
#print axioms GC.MetricGeometry.TwoRayConeData.chosenRay
#print axioms GC.MetricGeometry.TwoRayConeData.chosenRay_mem
#print axioms GC.MetricGeometry.TwoRayConeData.chosenRay_through
#print axioms GC.MetricGeometry.TwoRayConeData.toRadialConeData
#print axioms GC.MetricGeometry.RadialConeData.unitRay_pair_distance
#print axioms GC.MetricGeometry.RadialConeData.toTwoRayConeData
#print axioms GC.MetricGeometry.nonempty_radialConeData_iff_twoRayConeData
#print axioms GC.MetricGeometry.TwoRayConeData.exists_pair_union_isometry
#print axioms GC.MetricGeometry.TwoRayConeData.ofPairUnionIsometries
#print axioms GC.MetricGeometry.TwoRayConeData.ray_eq_unitRay
#print axioms GC.MetricGeometry.TwoRayConeData.rays_eq_of_meet
#print axioms GC.MetricGeometry.TwoRayConeData.toRadialConeData_map_ray
#print axioms GC.MetricGeometry.TwoRayConeData.mem_rays_iff
#print axioms GC.MetricGeometry.TwoRayConeData.not_subsingleton
#print axioms GC.MetricGeometry.RadialConeData.toTwoRayConeData_toRadialConeData_map
#print axioms GC.MetricGeometry.RadialConeData.ofSubsingleton
#print axioms GC.MetricGeometry.nonempty_radialConeData_iff_subsingleton_or_twoRayConeData
#print axioms GCTwoRayConventionReview.halfline_constructed_scaling
#print axioms GCTwoRayConventionReview.halfline_positive_scale_regression
#print axioms GCTwoRayConventionReview.coincident_pair_has_onto_union_realization
#print axioms GCTwoRayConventionReview.halfline_has_only_the_original_unit_ray
#print axioms GCTwoRayConventionReview.singleton_convention_is_separate
#print axioms GCTwoRayConventionReview.opposite_ray_scaling_regression
#print axioms GCTwoRayConventionReview.positive_and_negative_rays_are_distinct
#print axioms GCTwoRayConventionReview.opposite_pair_has_onto_union_realization
#print axioms GCTwoRayConventionReview.original_ray_scaling_from_union_isometries
#print axioms GCTwoRayConventionReview.translated_radial_roundtrip_everywhere
#print axioms GCTwoRayConventionReview.translated_radial_roundtrip_numeric
#lint- only unusedArguments simpNF synTaut
```
