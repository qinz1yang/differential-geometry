import DifferentialGeometry.Geometry.Neck.NormalizedDatum
import DifferentialGeometry.Geometry.Metric.CylinderRotation
import DifferentialGeometry.Topology.Manifold.OpenSubtype

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Metric
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Neck

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev S2 := Metric.sphere (0 : E3) 1
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)
private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

def openCylinder (L : ℝ) : Opens (S2 × ℝ) :=
  ⟨{q | q.2 ∈ Ioo (-L) L}, isOpen_Ioo.preimage continuous_snd⟩

theorem roundCylinderImage_bufferedCylinder_le (e : E3 ≃ₗᵢ[ℝ] E3) (z₀ : ℝ)
    {d B L : ℝ} (hfit : |z₀| + d⁻¹ + 1 ≤ B) (hBL : B < L) :
    roundCylinderImage (n := 2) e z₀ (bufferedCylinder d) ≤ openCylinder L := by
  rintro q ⟨z, hz, rfl⟩
  rw [roundCylinderDiffeomorph_apply]
  change -L < z₀ + z.2 ∧ z₀ + z.2 < L
  change -d⁻¹ - 1 < z.2 ∧ z.2 < d⁻¹ + 1 at hz
  constructor <;> linarith [hz.1, hz.2, neg_abs_le z₀, le_abs_self z₀]

def pointwiseCylinderMap (e : E3 ≃ₗᵢ[ℝ] E3) (z₀ : ℝ) {d B L : ℝ}
    (hfit : |z₀| + d⁻¹ + 1 ≤ B) (hBL : B < L) : bufferedCylinder d → openCylinder L :=
  Opens.inclusion (roundCylinderImage_bufferedCylinder_le e z₀ hfit hBL) ∘
    roundCylinderRestrict (n := 2) e z₀ (bufferedCylinder d)

theorem pointwiseCylinderMap_val (e : E3 ≃ₗᵢ[ℝ] E3) (z₀ : ℝ) {d B L : ℝ}
    (hfit : |z₀| + d⁻¹ + 1 ≤ B) (hBL : B < L) (q : bufferedCylinder d) :
    (pointwiseCylinderMap e z₀ hfit hBL q : S2 × ℝ) =
      (sphereDiffeo (n := 2) e q.val.1, z₀ + q.val.2) :=
  roundCylinderRestrict_apply e z₀ (bufferedCylinder d) q

theorem pointwiseCylinderMap_height_mem_Ioo (e : E3 ≃ₗᵢ[ℝ] E3) (z₀ : ℝ)
    {d B L : ℝ} (hfit : |z₀| + d⁻¹ + 1 ≤ B) (hBL : B < L)
    (q : bufferedCylinder d) :
    (pointwiseCylinderMap e z₀ hfit hBL q).val.2 ∈ Ioo (-B) B := by
  rw [pointwiseCylinderMap_val]
  have hq := q.property
  change -d⁻¹ - 1 < q.val.2 ∧ q.val.2 < d⁻¹ + 1 at hq
  change -B < z₀ + q.val.2 ∧ z₀ + q.val.2 < B
  constructor <;> linarith [hq.1, hq.2, neg_abs_le z₀, le_abs_self z₀]

theorem contMDiff_pointwiseCylinderMap (e : E3 ≃ₗᵢ[ℝ] E3) (z₀ : ℝ) {d B L : ℝ}
    (hfit : |z₀| + d⁻¹ + 1 ≤ B) (hBL : B < L) :
    ContMDiff IC IC ∞ (pointwiseCylinderMap e z₀ hfit hBL) :=
  (contMDiff_inclusion (roundCylinderImage_bufferedCylinder_le e z₀ hfit hBL)).comp
    (roundCylinderRestrict (n := 2) e z₀ (bufferedCylinder d)).contMDiff

theorem injective_pointwiseCylinderMap (e : E3 ≃ₗᵢ[ℝ] E3) (z₀ : ℝ) {d B L : ℝ}
    (hfit : |z₀| + d⁻¹ + 1 ≤ B) (hBL : B < L) :
    Injective (pointwiseCylinderMap e z₀ hfit hBL) := by
  intro x y hxy
  apply (roundCylinderRestrict (n := 2) e z₀ (bufferedCylinder d)).injective
  apply Subtype.ext
  exact congrArg (fun q : openCylinder L => q.val) hxy

theorem range_pointwiseCylinderMap (e : E3 ≃ₗᵢ[ℝ] E3) (z₀ : ℝ) {d B L : ℝ}
    (hfit : |z₀| + d⁻¹ + 1 ≤ B) (hBL : B < L) :
    range (pointwiseCylinderMap e z₀ hfit hBL) =
      {q : openCylinder L | q.val ∈ roundCylinderImage (n := 2) e z₀ (bufferedCylinder d)} := by
  ext q
  constructor
  · rintro ⟨x, rfl⟩
    exact (roundCylinderRestrict (n := 2) e z₀ (bufferedCylinder d) x).property
  · intro hq
    let a := roundCylinderRestrict (n := 2) e z₀ (bufferedCylinder d)
    refine ⟨a.symm ⟨q.val, hq⟩, ?_⟩
    apply Subtype.ext
    change (a (a.symm ⟨q.val, hq⟩)).val = q.val
    rw [a.apply_symm_apply]

theorem pointwiseCylinderMap_mfderiv (e : E3 ≃ₗᵢ[ℝ] E3) (z₀ : ℝ) {d B L : ℝ}
    (hfit : |z₀| + d⁻¹ + 1 ≤ B) (hBL : B < L) (q : bufferedCylinder d)
    (v : TangentSpace IC q) :
    mfderiv IC IC (pointwiseCylinderMap e z₀ hfit hBL) q v =
      (mfderiv (𝓡 2) (𝓡 2) (sphereDiffeo (n := 2) e) q.val.1 v.1, v.2) := by
  have hinc := (contMDiff_inclusion (I := IC) (n := ∞)
    (roundCylinderImage_bufferedCylinder_le e z₀ hfit hBL)).mdifferentiable (by simp)
  have hax := (roundCylinderRestrict (n := 2) e z₀ (bufferedCylinder d)).contMDiff
    |>.mdifferentiable (by simp)
  rw [pointwiseCylinderMap, mfderiv_comp q (hinc _) (hax _), mfderiv_opens_incl]
  change mfderiv IC IC (roundCylinderRestrict (n := 2) e z₀ (bufferedCylinder d)) q v = _
  exact roundCylinderRestrict_mfderiv e z₀ (bufferedCylinder d) q v

theorem image_pointwiseCylinderMap_controlledCylinder_subset (e : E3 ≃ₗᵢ[ℝ] E3)
    (z₀ : ℝ) {d B L : ℝ} (hfit : |z₀| + d⁻¹ + 1 ≤ B) (hBL : B < L) :
    pointwiseCylinderMap e z₀ hfit hBL '' controlledCylinder d ⊆
      {q : openCylinder L | q.val.2 ∈ Icc (-B) B} := by
  rintro q ⟨z, hz, rfl⟩
  change -B ≤ (pointwiseCylinderMap e z₀ hfit hBL z).val.2 ∧
    (pointwiseCylinderMap e z₀ hfit hBL z).val.2 ≤ B
  rw [pointwiseCylinderMap_val]
  change -d⁻¹ ≤ z.val.2 ∧ z.val.2 ≤ d⁻¹ at hz
  constructor <;> linarith [hz.1, hz.2, neg_abs_le z₀, le_abs_self z₀]

theorem point_mem_openCylinder_of_fit (y : S2) (z₀ : ℝ) {d B L : ℝ}
    (hd : 0 < d) (hfit : |z₀| + d⁻¹ + 1 ≤ B) (hBL : B < L) :
    (y, z₀) ∈ openCylinder L := by
  change -L < z₀ ∧ z₀ < L
  have hi := inv_pos.mpr hd
  constructor <;> linarith [neg_abs_le z₀, le_abs_self z₀]

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

def pointwiseChart {L : ℝ} (Φ : openCylinder L → M) (e : E3 ≃ₗᵢ[ℝ] E3)
    (z₀ : ℝ) {d B : ℝ} (hfit : |z₀| + d⁻¹ + 1 ≤ B) (hBL : B < L) :
    bufferedCylinder d → M := Φ ∘ pointwiseCylinderMap e z₀ hfit hBL

omit [TopologicalSpace M] in
theorem pointwiseChart_apply {L : ℝ} (Φ : openCylinder L → M) (e : E3 ≃ₗᵢ[ℝ] E3)
    (z₀ : ℝ) {d B : ℝ} (hfit : |z₀| + d⁻¹ + 1 ≤ B) (hBL : B < L)
    (q : bufferedCylinder d) :
    pointwiseChart Φ e z₀ hfit hBL q = Φ
      ⟨(sphereDiffeo (n := 2) e q.val.1, z₀ + q.val.2), by
        rw [← pointwiseCylinderMap_val e z₀ hfit hBL q]
        exact (pointwiseCylinderMap e z₀ hfit hBL q).property⟩ := by
  apply congrArg Φ
  apply Subtype.ext
  exact pointwiseCylinderMap_val e z₀ hfit hBL q

theorem contMDiff_pointwiseChart {L : ℝ} (Φ : openCylinder L → M)
    (hΦ : ContMDiff IC I ∞ Φ) (e : E3 ≃ₗᵢ[ℝ] E3) (z₀ : ℝ) {d B : ℝ}
    (hfit : |z₀| + d⁻¹ + 1 ≤ B) (hBL : B < L) :
    ContMDiff IC I ∞ (pointwiseChart Φ e z₀ hfit hBL) :=
  hΦ.comp (contMDiff_pointwiseCylinderMap e z₀ hfit hBL)

omit [TopologicalSpace M] in
theorem injective_pointwiseChart {L : ℝ} (Φ : openCylinder L → M)
    (hΦ : Injective Φ) (e : E3 ≃ₗᵢ[ℝ] E3) (z₀ : ℝ) {d B : ℝ}
    (hfit : |z₀| + d⁻¹ + 1 ≤ B) (hBL : B < L) :
    Injective (pointwiseChart Φ e z₀ hfit hBL) :=
  hΦ.comp (injective_pointwiseCylinderMap e z₀ hfit hBL)

theorem immersion_pointwiseChart {L : ℝ} (Φ : openCylinder L → M)
    (hΦ : ContMDiff IC I ∞ Φ) (hm : ∀ q, Injective (mfderiv IC I Φ q))
    (e : E3 ≃ₗᵢ[ℝ] E3) (z₀ : ℝ) {d B : ℝ}
    (hfit : |z₀| + d⁻¹ + 1 ≤ B) (hBL : B < L) (q : bufferedCylinder d) :
    Injective (mfderiv IC I (pointwiseChart Φ e z₀ hfit hBL) q) := by
  have hd := hΦ.mdifferentiable (by simp)
  have hc := (contMDiff_pointwiseCylinderMap e z₀ hfit hBL).mdifferentiable (by simp)
  rw [pointwiseChart, mfderiv_comp q (hd _) (hc _)]
  apply (hm _).comp
  intro v w hvw
  have hslots := (pointwiseCylinderMap_mfderiv e z₀ hfit hBL q v).symm.trans
    (hvw.trans (pointwiseCylinderMap_mfderiv e z₀ hfit hBL q w))
  have hfst := congrArg (fun u : EuclideanSpace ℝ (Fin 2) × ℝ => u.1) hslots
  have hsnd := congrArg (fun u : EuclideanSpace ℝ (Fin 2) × ℝ => u.2) hslots
  have hinj := ((sphereDiffeo (n := 2) e).toOpenPartialHomeomorph_mdifferentiable
    (by simp)).mfderiv_injective (x := q.val.1) (mem_univ _)
  exact Prod.ext (hinj hfst) hsnd

omit [TopologicalSpace M] in
theorem pointwiseChart_center {L : ℝ} (Φ : openCylinder L → M)
    (e : E3 ≃ₗᵢ[ℝ] E3) (yₚ : S2) (he : sphereDiffeo (n := 2) e spherePoint = yₚ)
    (z₀ : ℝ) {d B : ℝ} (hd : 0 < d)
    (hfit : |z₀| + d⁻¹ + 1 ≤ B) (hBL : B < L) :
    pointwiseChart Φ e z₀ hfit hBL (cylinderCenter d hd) =
      Φ ⟨(yₚ, z₀), point_mem_openCylinder_of_fit yₚ z₀ hd hfit hBL⟩ := by
  apply congrArg Φ
  apply Subtype.ext
  rw [pointwiseCylinderMap_val]
  simp only [cylinderCenter, he, add_zero]

end DifferentialGeometry.Geometry.Neck
