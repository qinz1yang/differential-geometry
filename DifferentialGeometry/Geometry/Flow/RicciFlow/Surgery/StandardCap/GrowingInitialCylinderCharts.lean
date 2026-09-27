import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.EndChart
import DifferentialGeometry.Geometry.Neck.CylinderExhaustion
import DifferentialGeometry.Geometry.Metric.RoundCylinder
import DifferentialGeometry.Geometry.Metric.PolarCoordinates

set_option autoImplicit false
noncomputable section
open Set Filter Function TopologicalSpace Bundle Manifold
open DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Geometry.Metric DifferentialGeometry.Geometry.Neck
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev S2 := Metric.sphere (0 : E3) 1
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)
private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

def initialPolarDiffeomorph (e : E3 ≃ₗᵢ[ℝ] E3) (a : ℝ) :
    PartialDiffeomorph IC (𝓡 3) (S2 × ℝ) E3 ∞ :=
  (roundCylinderDiffeomorph (n := 2) e a).toPartialDiffeomorph.trans
    (euclideanPolarDiffeomorph (n := 2))

@[simp] theorem initialPolarDiffeomorph_apply (e : E3 ≃ₗᵢ[ℝ] E3) (a : ℝ)
    (q : S2 × ℝ) :
    initialPolarDiffeomorph e a q = (a + q.2) • e (q.1 : E3) := by
  change euclideanPolarMap (roundCylinderDiffeomorph (n := 2) e a q) = _
  rw [roundCylinderDiffeomorph_apply]
  rfl

@[simp] theorem initialPolarDiffeomorph_source (e : E3 ≃ₗᵢ[ℝ] E3) (a : ℝ) :
    (initialPolarDiffeomorph e a).source = {q : S2 × ℝ | 0 < a + q.2} := by
  ext q
  change (q ∈ (univ : Set (S2 × ℝ)) ∧
    0 < (roundCylinderDiffeomorph (n := 2) e a q).2) ↔ 0 < a + q.2
  rw [roundCylinderDiffeomorph_apply]
  simp only [mem_univ, true_and]

@[simp] theorem initialPolarDiffeomorph_target (e : E3 ≃ₗᵢ[ℝ] E3) (a : ℝ) :
    (initialPolarDiffeomorph e a).target = {0}ᶜ := by
  ext x
  change (x ≠ 0 ∧ (euclideanPolarDiffeomorph (n := 2)).symm x ∈
    (univ : Set (S2 × ℝ))) ↔ x ≠ 0
  simp only [mem_univ, and_true]

theorem initialPolarDiffeomorph_norm (e : E3 ≃ₗᵢ[ℝ] E3) (a : ℝ)
    {q : S2 × ℝ} (hq : 0 < a + q.2) :
    ‖initialPolarDiffeomorph e a q‖ = a + q.2 := by
  rw [initialPolarDiffeomorph_apply, norm_smul, e.norm_map,
    norm_eq_of_mem_sphere, mul_one, Real.norm_eq_abs, abs_of_pos hq]

theorem initialPolarDiffeomorph_symm_height (e : E3 ≃ₗᵢ[ℝ] E3) (a : ℝ)
    {x : E3} (hx : x ≠ 0) :
    ((initialPolarDiffeomorph e a).symm x).2 = ‖x‖ - a := by
  change ((roundCylinderDiffeomorph (n := 2) e a).symm
    ((euclideanPolarDiffeomorph (n := 2)).symm x)).2 = _
  rw [roundCylinderDiffeomorph_symm_apply, euclideanPolarDiffeomorph_symm_snd hx]

private theorem initialPolarDiffeomorph_mfderiv (e : E3 ≃ₗᵢ[ℝ] E3) (a : ℝ)
    (q : S2 × ℝ) (v : TangentSpace IC q) :
    mfderiv IC (𝓡 3) (initialPolarDiffeomorph e a) q v =
      mfderiv IC (𝓡 3) euclideanPolarMap (roundCylinderDiffeomorph (n := 2) e a q)
        (mfderiv IC IC (roundCylinderDiffeomorph (n := 2) e a) q v) := by
  change mfderiv IC (𝓡 3)
    (euclideanPolarMap ∘ roundCylinderDiffeomorph (n := 2) e a) q v = _
  rw [mfderiv_comp q
    (euclideanPolarMap_smooth.mdifferentiableAt (by decide : (∞ : ℕ∞ω) ≠ 0))
    ((roundCylinderDiffeomorph (n := 2) e a).contMDiff.mdifferentiableAt (by decide)),
    ContinuousLinearMap.comp_apply]

theorem initialPolarDiffeomorph_metric_inner (e : E3 ≃ₗᵢ[ℝ] E3) (a : ℝ)
    (q : S2 × ℝ) (hq : transitionEnd ≤ a + q.2) (v w : TangentSpace IC q) :
    metric.inner (initialPolarDiffeomorph e a q)
      (mfderiv IC (𝓡 3) (initialPolarDiffeomorph e a) q v)
      (mfderiv IC (𝓡 3) (initialPolarDiffeomorph e a) q w) =
      (roundCylinderMetric (E := E3) (n := 2)).inner q v w := by
  rw [initialPolarDiffeomorph_mfderiv, initialPolarDiffeomorph_mfderiv]
  change metric.inner (euclideanPolarMap (roundCylinderDiffeomorph (n := 2) e a q))
    _ _ = _
  rw [metric_polar_pullback_cylindrical _ (by
    simpa only [roundCylinderDiffeomorph_apply] using hq)]
  have h := congrArg
    (fun g : SmoothRiemannianMetric IC (S2 × ℝ) => g.inner q v w)
    (pullback_roundCylinderMetric_roundCylinderDiffeomorph (n := 2) e a)
  rw [Diffeomorph.pullbackMetric_inner] at h
  exact h

private theorem openCylinder_subset_polar_source (e : E3 ≃ₗᵢ[ℝ] E3)
    {a L : ℝ} (hfit : transitionEnd + L ≤ a) :
    (openCylinder L : Set (S2 × ℝ)) ⊆ (initialPolarDiffeomorph e a).source := by
  intro q hq
  rw [initialPolarDiffeomorph_source]
  change 0 < a + q.2
  have hz : -L < q.2 := hq.1
  linarith [transitionEnd_pos]

def initialCylinderImage (e : E3 ≃ₗᵢ[ℝ] E3) (a L : ℝ)
    (hfit : transitionEnd + L ≤ a) : Opens E3 :=
  ⟨initialPolarDiffeomorph e a '' (openCylinder L : Set (S2 × ℝ)),
    image_opens_isOpen _ (openCylinder_subset_polar_source e hfit)⟩

def initialCylinderChart (e : E3 ≃ₗᵢ[ℝ] E3) (a L : ℝ)
    (hfit : transitionEnd + L ≤ a) :
    openCylinder L ≃ₘ⟮IC, 𝓡 3⟯ initialCylinderImage e a L hfit :=
  PartialDiffeomorph.toOpensDiffeo (initialPolarDiffeomorph e a)
    (openCylinder_subset_polar_source e hfit)

@[simp] theorem initialCylinderChart_apply (e : E3 ≃ₗᵢ[ℝ] E3) (a L : ℝ)
    (hfit : transitionEnd + L ≤ a) (q : openCylinder L) :
    (initialCylinderChart e a L hfit q : E3) = initialPolarDiffeomorph e a q.val := rfl

theorem initialCylinderImage_eq_shell (e : E3 ≃ₗᵢ[ℝ] E3) (a L : ℝ)
    (hfit : transitionEnd + L ≤ a) :
    (initialCylinderImage e a L hfit : Set E3) =
      {x : E3 | a - L < ‖x‖ ∧ ‖x‖ < a + L} := by
  ext x
  constructor
  · rintro ⟨q, hq, rfl⟩
    have hpos : 0 < a + q.2 := by
      have hs := openCylinder_subset_polar_source e hfit hq
      simpa only [initialPolarDiffeomorph_source, mem_ofPred_eq] using hs
    change a - L < ‖initialPolarDiffeomorph e a q‖ ∧
      ‖initialPolarDiffeomorph e a q‖ < a + L
    rw [initialPolarDiffeomorph_norm e a hpos]
    exact ⟨by linarith [hq.1], by linarith [hq.2]⟩
  · intro hx
    have hx0 : x ≠ 0 := norm_pos_iff.mp (by linarith [transitionEnd_pos, hx.1])
    refine ⟨(initialPolarDiffeomorph e a).symm x, ?_,
      (initialPolarDiffeomorph e a).right_inv' (by
        simpa only [initialPolarDiffeomorph_target, mem_compl_singleton_iff] using hx0)⟩
    change -L < ((initialPolarDiffeomorph e a).symm x).2 ∧
      ((initialPolarDiffeomorph e a).symm x).2 < L
    rw [initialPolarDiffeomorph_symm_height e a hx0]
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

theorem initialCylinderChart_pullback (e : E3 ≃ₗᵢ[ℝ] E3) (a L : ℝ)
    (hfit : transitionEnd + L ≤ a) :
    Diffeomorph.pullbackMetricCross (metric.restrictOpen (initialCylinderImage e a L hfit))
      (initialCylinderChart e a L hfit) =
        (roundCylinderMetric (E := E3) (n := 2)).restrictOpen (openCylinder L) := by
  apply SmoothRiemannianMetric.ext_inner
  intro q v w
  rw [Diffeomorph.pullbackMetricCross_inner, SmoothRiemannianMetric.restrictOpen_inner,
    SmoothRiemannianMetric.restrictOpen_inner, initialCylinderChart_apply]
  rw [show mfderiv IC (𝓡 3) (initialCylinderChart e a L hfit) q v =
      mfderiv IC (𝓡 3) (initialPolarDiffeomorph e a) q.val v from
    PartialDiffeomorph.mfderiv_toOpensDiffeo _
      (openCylinder_subset_polar_source e hfit) q v]
  rw [show mfderiv IC (𝓡 3) (initialCylinderChart e a L hfit) q w =
      mfderiv IC (𝓡 3) (initialPolarDiffeomorph e a) q.val w from
    PartialDiffeomorph.mfderiv_toOpensDiffeo _
      (openCylinder_subset_polar_source e hfit) q w]
  exact initialPolarDiffeomorph_metric_inner e a q.val (by linarith [q.property.1]) v w

theorem initialCylinderChart_distance (e : E3 ≃ₗᵢ[ℝ] E3) (a L : ℝ)
    (hfit : transitionEnd + L ≤ a) (q : openCylinder L) :
    (riemannianEDistOf metric 0 (initialCylinderChart e a L hfit q : E3)).toReal = a + q.val.2 := by
  rw [distance_zero, initialCylinderChart_apply]
  apply initialPolarDiffeomorph_norm
  linarith [transitionEnd_pos, q.property.1]

private theorem exists_pointedInitialRotation (x : E3) :
    ∃ e : E3 ≃ₗᵢ[ℝ] E3, initialPolarDiffeomorph e ‖x‖ (spherePoint, 0) = x := by
  by_cases hx : x = 0
  · refine ⟨LinearIsometryEquiv.refl ℝ E3, ?_⟩
    simp [hx]
  let p := ((euclideanPolarDiffeomorph (n := 2)).symm x).1
  obtain ⟨e, _, he⟩ := exists_sphereDiffeo_det_one (n := 2) (by norm_num) spherePoint p
  refine ⟨e, ?_⟩
  change euclideanPolarMap (roundCylinderDiffeomorph (n := 2) e ‖x‖ (spherePoint, 0)) = x
  rw [roundCylinderDiffeomorph_apply, add_zero, he]
  have hrad := euclideanPolarDiffeomorph_symm_snd (n := 2) hx
  have hq : (p, ‖x‖) = (euclideanPolarDiffeomorph (n := 2)).symm x := by
    exact Prod.ext rfl hrad.symm
  rw [hq]
  exact (euclideanPolarDiffeomorph (n := 2)).right_inv' hx

def pointedInitialRotation (x : E3) : E3 ≃ₗᵢ[ℝ] E3 :=
  (exists_pointedInitialRotation x).choose

theorem pointedInitialRotation_center (x : E3) :
    initialPolarDiffeomorph (pointedInitialRotation x) ‖x‖ (spherePoint, 0) = x :=
  (exists_pointedInitialRotation x).choose_spec

theorem initialCylinderChart_center (x : E3) (L : ℝ) (hL : 0 < L)
    (hfit : transitionEnd + L ≤ ‖x‖) :
    (initialCylinderChart (pointedInitialRotation x) ‖x‖ L hfit
      ⟨(spherePoint, 0), by exact ⟨neg_neg_of_pos hL, hL⟩⟩ : E3) = x :=
  pointedInitialRotation_center x

end DifferentialGeometry.PDE.RicciFlow.StandardCap

end
