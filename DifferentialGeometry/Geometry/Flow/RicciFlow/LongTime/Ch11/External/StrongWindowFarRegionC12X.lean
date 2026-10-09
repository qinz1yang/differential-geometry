import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardCylinderSliceConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.Distance
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Norm.Comparison
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Norm.ReferenceChange
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Scaling

/-!
# Standard-solution far region, uniformly in time (C12X, S16 `hwin` far branch; O-C12X-S16J G4d)

For `Θ < 1`, an order `p`, an accuracy `η > 0` and an axial half-length `L`, there is a radius
`D` such that for every standard solution, every time `T ∈ [0, Θ]` and every point `x` with
`‖x‖ ≥ D`, the pullback of the time-`T` metric by the radial chart
`(ω, z) ↦ (‖x‖ + z) • rot_x ω` is `η`-close in `C^p` to the shrinking cylinder at the same time
`T` on `S² × [-L, L]`, measured with the cylinder itself as reference.

The proof is the contradiction argument of `StandardSolution.exists_far_radial_spatialNeck`
(`SS/StandardFarRegion`): along a bad sequence the times converge, `t_n → s`, and the pulled-back
metrics converge to the cylinder at `s`
(`exists_standard_cylinder_metric_subsequence_at_tendsto_time`, built on the time-uniform
closed limit `exists_standard_cylinder_closed_limit`).  Two cylinder slices differ by
`2 (b - a)` times a fixed tensor, so `cyl t_n → cyl s`; the reference change
`metric_deriv_norm_reference_change_le` then moves the reference from `cyl s` to `cyl t_n`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.StandardCap
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

private local instance s16j_sphereDim : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

/-- Two slices of the shrinking cylinder differ by `2 (b - a)` times a fixed tensor. -/
private theorem s16j_metricTensorField_cyl_sub {a b : ℝ} (ha : a < 1) (hb : b < 1) :
    metricTensorField (shrinkingCylinderMetric (E := E3) a) -
        metricTensorField (shrinkingCylinderMetric (E := E3) b) =
      (2 * (b - a)) • (metricTensorField (shrinkingCylinderMetric (E := E3) 0) -
        metricTensorField (shrinkingCylinderMetric (E := E3) (1 / 2))) := by
  ext x v
  simp only [ContMDiffSection.coe_sub, ContMDiffSection.coe_smul, Pi.sub_apply, Pi.smul_apply]
  rw [Tensor0SSpace.sub_apply, Tensor0SSpace.smul_apply, Tensor0SSpace.sub_apply,
    metricTensorField_apply, metricTensorField_apply, metricTensorField_apply,
    metricTensorField_apply, shrinkingCylinderMetric_inner ha, shrinkingCylinderMetric_inner hb,
    shrinkingCylinderMetric_inner (by norm_num : (0 : ℝ) < 1),
    shrinkingCylinderMetric_inner (by norm_num : (1 / 2 : ℝ) < 1), smul_eq_mul]
  ring

/-- The `C^q` distance of two cylinder slices, for any reference metric. -/
theorem metricDerivNorm_shrinkingCylinder_slices_C12X (q : ℕ) {a b : ℝ} (ha : a < 1)
    (hb : b < 1) (R : SmoothRiemannianMetric SpatialNeckCylinderModel SpatialNeckCylinder)
    (z : SpatialNeckCylinder) :
    metricDerivNorm q (shrinkingCylinderMetric (E := EuclideanSpace ℝ (Fin 3)) a)
        (shrinkingCylinderMetric (E := EuclideanSpace ℝ (Fin 3)) b) R z =
      |2 * (b - a)| * metricDerivNorm q (shrinkingCylinderMetric (E := EuclideanSpace ℝ (Fin 3)) 0)
        (shrinkingCylinderMetric (E := EuclideanSpace ℝ (Fin 3)) (1 / 2)) R z := by
  have key (f₁ f₂ : SmoothRiemannianMetric SpatialNeckCylinderModel SpatialNeckCylinder) :
      metricCovDeriv f₁ R q z - metricCovDeriv f₂ R q z =
        (covDerivOfField R (metricTensorField f₁ - metricTensorField f₂) q) z := by
    rw [covDerivOfField_sub, metricCovDeriv_eq_covDerivOfField f₁ R q,
      metricCovDeriv_eq_covDerivOfField f₂ R q]
    rfl
  unfold metricDerivNorm metricDiffCovDerivAt
  rw [key, key, s16j_metricTensorField_cyl_sub ha hb, covDerivOfField_smul]
  exact sqrt_normSq0S_smul R z (q + 2) _ _

/-- **Far region of the standard solution, uniformly in time.**  For `Θ < 1`, an order `p`,
`η > 0` and `L`, there is `D > 0` such that for every standard solution `S`, every
`T ∈ [0, Θ]` and every `x` with `D ≤ ‖x‖`, the pullback `G` of `S.val.metric T` by the radial
chart `F (ω, z) = (‖x‖ + z) • rot_x ω` (on an open `U ⊇ S² × [-L, L]` inside its source) is
`η`-close in `C^p` to the shrinking cylinder at time `T`, with that cylinder as reference. -/
theorem StandardSolution.exists_far_radial_cylinder_close_C12X
    {Θ : ℝ} (hΘ : Θ < 1) (p : ℕ) {η : ℝ} (hη : 0 < η) (L : ℝ) :
    ∃ D : ℝ, 0 < D ∧ ∀ (S : StandardSolution) (T : ℝ), T ∈ Icc 0 Θ →
      ∀ x : EuclideanSpace ℝ (Fin 3), D ≤ ‖x‖ →
      ∃ (F : PartialDiffeomorph SpatialNeckCylinderModel (𝓡 3) SpatialNeckCylinder
          (EuclideanSpace ℝ (Fin 3)) ∞)
        (G : SmoothRiemannianMetric SpatialNeckCylinderModel SpatialNeckCylinder)
        (U : Set SpatialNeckCylinder),
        (∀ z, F z = (‖x‖ + z.2) • pointedInitialRotation x z.1.val) ∧
        IsOpen U ∧ (univ : Set SpatialNeckSphere) ×ˢ Icc (-L) L ⊆ U ∧ U ⊆ F.source ∧
        (∀ z ∈ U, ∀ v w : TangentSpace SpatialNeckCylinderModel z,
          G.inner z v w = (S.val.metric T).inner (F z)
            (mfderiv SpatialNeckCylinderModel (𝓡 3) F z v)
            (mfderiv SpatialNeckCylinderModel (𝓡 3) F z w)) ∧
        ∀ q ≤ p, ∀ z ∈ (univ : Set SpatialNeckSphere) ×ˢ Icc (-L) L,
          metricDerivNorm q G (shrinkingCylinderMetric (E := EuclideanSpace ℝ (Fin 3)) T)
            (shrinkingCylinderMetric (E := EuclideanSpace ℝ (Fin 3)) T) z < η := by
  by_contra hcon
  push Not at hcon
  choose S t ht x hx hbad using fun n : ℕ => hcon ((n : ℝ) + 1) (by positivity)
  obtain ⟨s, hsI, φ, hφ, hlim⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) Θ)).tendsto_subseq ht
  have hτ : 0 < max Θ (1 / 2) := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hτ1 : max Θ (1 / 2) < 1 := max_lt hΘ (by norm_num)
  have htime : ∀ n, (t ∘ φ) n ∈ Icc 0 (max Θ (1 / 2)) := fun n =>
    Icc_subset_Icc_right (le_max_left _ _) (ht (φ n))
  have hescape : Tendsto (fun n => (riemannianEDistOf ((S (φ n)).val.metric 0) 0
      (x (φ n))).toReal) atTop atTop := by
    have heq : ∀ n, (riemannianEDistOf ((S (φ n)).val.metric 0) 0 (x (φ n))).toReal =
        ‖x (φ n)‖ := by
      intro n
      rw [(S (φ n)).val.initial, distance_zero]
    simp only [heq]
    refine tendsto_atTop_mono (fun n => ?_) tendsto_natCast_atTop_atTop
    have h1 := hx (φ n)
    have h2 : (n : ℝ) ≤ φ n := by exact_mod_cast hφ.id_le n
    linarith
  obtain ⟨ψ, G, F, hψ, hconv, hFform, hloc⟩ :=
    exists_standard_cylinder_metric_subsequence_at_tendsto_time hτ hτ1 (S ∘ φ) (x ∘ φ)
      (t ∘ φ) htime hlim hescape
  have hs1 : s < 1 := lt_of_le_of_lt hsI.2 hΘ
  let cs := shrinkingCylinderMetric (E := E3) s
  have hconv' := hconv.change_reference cs
  let K : Set SpatialNeckCylinder := (univ : Set SpatialNeckSphere) ×ˢ Icc (-L) L
  let K' : Set SpatialNeckCylinder := (univ : Set SpatialNeckSphere) ×ˢ Icc (-(L + 1)) (L + 1)
  let u : Set SpatialNeckCylinder := (univ : Set SpatialNeckSphere) ×ˢ Ioo (-(L + 1)) (L + 1)
  have hK : IsCompact K := isCompact_univ.prod isCompact_Icc
  have hK' : IsCompact K' := isCompact_univ.prod isCompact_Icc
  have hu : IsOpen u := isOpen_univ.prod isOpen_Ioo
  have huK' : u ⊆ K' := prod_mono subset_rfl Ioo_subset_Icc_self
  have hKu : K ⊆ u := prod_mono subset_rfl (Icc_subset_Ioo (by linarith) (by linarith))
  obtain ⟨δ, hδ, hδ1, hδdim, hδbud⟩ :=
    exists_metric_reference_change_delta (E := EuclideanSpace ℝ (Fin 2) × ℝ) p (half_pos hη)
  obtain ⟨n0, hn0⟩ := hconv' K' hK' p δ hδ
  obtain ⟨B, hB, hBb⟩ := metricDerivNorm_bddOn hK' p (shrinkingCylinderMetric (E := E3) 0)
    (shrinkingCylinderMetric (E := E3) (1 / 2)) cs
  have htend : Tendsto (fun n => t (φ (ψ n))) atTop (𝓝 s) := hlim.comp hψ.tendsto_atTop
  obtain ⟨n1, hn1⟩ := eventually_atTop.mp
    ((Metric.tendsto_nhds.mp htend) (δ / (2 * (B + 1))) (by positivity))
  obtain ⟨n2, hn2⟩ := eventually_atTop.mp (hloc K hK)
  let n := max n0 (max n1 n2)
  obtain ⟨U, hU, hKU, hUs, hGU⟩ := hn2 n ((le_max_right _ _).trans (le_max_right _ _))
  let m := φ (ψ n)
  have htm : t m < 1 := (ht m).2.trans_lt hΘ
  obtain ⟨q, hq, z, hz, hbig⟩ := hbad m (F n) (G n) U (hFform n) hU hKU hUs hGU
  have hA : ∀ y ∈ u, ∀ j, j ≤ p → metricDerivNorm j (G n) cs cs y ≤ δ := fun y hy j hj =>
    (derivNorm_le_sup hK' hj _ _ _ (huK' hy)).trans (hn0 n (le_max_left _ _)).le
  have hdt : |t m - s| < δ / (2 * (B + 1)) := by
    have := hn1 n ((le_max_left _ _).trans (le_max_right _ _))
    rwa [Real.dist_eq] at this
  have hInf : ∀ y ∈ u, ∀ j, j ≤ p →
      metricDerivNorm j (shrinkingCylinderMetric (E := E3) (t m)) cs cs y ≤ δ := by
    intro y hy j hj
    rw [metricDerivNorm_shrinkingCylinder_slices_C12X j htm hs1]
    have h2 : |2 * (s - t m)| = 2 * |t m - s| := by
      rw [abs_mul, abs_of_pos two_pos, abs_sub_comm]
    have hb := hBb j hj y (huK' hy)
    have hn : 0 ≤ metricDerivNorm j (shrinkingCylinderMetric (E := E3) 0)
        (shrinkingCylinderMetric (E := E3) (1 / 2)) cs y := Real.sqrt_nonneg _
    have hfrac : δ / (2 * (B + 1)) * (2 * B) ≤ δ := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith
    rw [h2]
    calc 2 * |t m - s| * metricDerivNorm j (shrinkingCylinderMetric (E := E3) 0)
          (shrinkingCylinderMetric (E := E3) (1 / 2)) cs y
        ≤ 2 * (δ / (2 * (B + 1))) * B :=
          mul_le_mul (by linarith) hb hn (by positivity)
      _ ≤ δ := by linarith
  have hfin := metric_deriv_norm_reference_change_le hu (G n)
    (shrinkingCylinderMetric (E := E3) (t m)) cs p hδ.le hδ1.le hδdim hδbud hA hInf z
    (hKu hz) q hq
  linarith

end DifferentialGeometry.PDE.RicciFlow
