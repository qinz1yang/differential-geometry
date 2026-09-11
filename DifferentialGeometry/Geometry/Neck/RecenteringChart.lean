import DifferentialGeometry.Geometry.Neck.NormalizedDatum
import DifferentialGeometry.Geometry.Metric.CylinderAxial
import DifferentialGeometry.Topology.Manifold.OpenSubtype

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Metric
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Neck

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev S2 := Metric.sphere (0 : E3) 1
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)
private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

theorem cylinderAxialImage_bufferedCylinder_le {ε δ σ : ℝ}
    (hσ : σ ^ 2 = 1) (hfit : ε⁻¹ + 1 ≤ δ⁻¹) :
    cylinderAxialImage (I := 𝓡 2) σ σ hσ (bufferedCylinder ε) ≤ bufferedCylinder δ := by
  rintro q ⟨z, hz, rfl⟩
  change -δ⁻¹ - 1 < σ + σ * z.2 ∧ σ + σ * z.2 < δ⁻¹ + 1
  change -ε⁻¹ - 1 < z.2 ∧ z.2 < ε⁻¹ + 1 at hz
  rcases sq_eq_one_iff.mp hσ with rfl | rfl <;> constructor <;> linarith [hz.1, hz.2]

def recenteringCylinderMap {ε δ σ : ℝ} (hσ : σ ^ 2 = 1) (hfit : ε⁻¹ + 1 ≤ δ⁻¹) :
    bufferedCylinder ε → bufferedCylinder δ :=
  Opens.inclusion (cylinderAxialImage_bufferedCylinder_le hσ hfit) ∘
    cylinderAxialRestrict (I := 𝓡 2) σ σ hσ (bufferedCylinder ε)

theorem recenteringCylinderMap_val {ε δ σ : ℝ} (hσ : σ ^ 2 = 1)
    (hfit : ε⁻¹ + 1 ≤ δ⁻¹) (q : bufferedCylinder ε) :
    (recenteringCylinderMap hσ hfit q : S2 × ℝ) = (q.val.1, σ * (1 + q.val.2)) := by
  change (q.val.1, σ + σ * q.val.2) = (q.val.1, σ * (1 + q.val.2))
  apply Prod.ext
  · rfl
  · change σ + σ * q.val.2 = σ * (1 + q.val.2)
    ring

theorem contMDiff_recenteringCylinderMap {ε δ σ : ℝ} (hσ : σ ^ 2 = 1)
    (hfit : ε⁻¹ + 1 ≤ δ⁻¹) :
    ContMDiff IC IC ∞ (recenteringCylinderMap hσ hfit) :=
  (contMDiff_inclusion (cylinderAxialImage_bufferedCylinder_le hσ hfit)).comp
    (cylinderAxialRestrict (I := 𝓡 2) σ σ hσ (bufferedCylinder ε)).contMDiff

theorem injective_recenteringCylinderMap {ε δ σ : ℝ} (hσ : σ ^ 2 = 1)
    (hfit : ε⁻¹ + 1 ≤ δ⁻¹) : Injective (recenteringCylinderMap hσ hfit) := by
  intro x y hxy
  apply (cylinderAxialRestrict (I := 𝓡 2) σ σ hσ (bufferedCylinder ε)).injective
  apply Subtype.ext
  exact congrArg (fun q : bufferedCylinder δ => q.val) hxy

theorem range_recenteringCylinderMap {ε δ σ : ℝ} (hσ : σ ^ 2 = 1)
    (hfit : ε⁻¹ + 1 ≤ δ⁻¹) :
    range (recenteringCylinderMap hσ hfit) =
      {q : bufferedCylinder δ |
        q.val ∈ cylinderAxialImage (I := 𝓡 2) σ σ hσ (bufferedCylinder ε)} := by
  ext q
  constructor
  · rintro ⟨x, rfl⟩
    exact (cylinderAxialRestrict (I := 𝓡 2) σ σ hσ (bufferedCylinder ε) x).property
  · intro hq
    let a := cylinderAxialRestrict (I := 𝓡 2) σ σ hσ (bufferedCylinder ε)
    refine ⟨a.symm ⟨q.val, hq⟩, ?_⟩
    apply Subtype.ext
    change (a (a.symm ⟨q.val, hq⟩)).val = q.val
    rw [a.apply_symm_apply]

theorem recenteringCylinderMap_mfderiv {ε δ σ : ℝ} (hσ : σ ^ 2 = 1)
    (hfit : ε⁻¹ + 1 ≤ δ⁻¹) (q : bufferedCylinder ε) (v : TangentSpace IC q) :
    mfderiv IC IC (recenteringCylinderMap hσ hfit) q v = (v.1, σ * v.2) := by
  have hinc := (contMDiff_inclusion (I := IC) (n := ∞)
    (cylinderAxialImage_bufferedCylinder_le hσ hfit)).mdifferentiable (by simp)
  have hax := (cylinderAxialRestrict (I := 𝓡 2) σ σ hσ (bufferedCylinder ε)).contMDiff
    |>.mdifferentiable (by simp)
  rw [recenteringCylinderMap, mfderiv_comp q (hinc _) (hax _), mfderiv_opens_incl]
  change mfderiv IC IC (cylinderAxialRestrict (I := 𝓡 2) σ σ hσ (bufferedCylinder ε)) q v = _
  exact cylinderAxialRestrict_mfderiv σ σ hσ (bufferedCylinder ε) q v

theorem image_recenteringCylinderMap_controlledCylinder_subset {ε δ σ : ℝ}
    (hσ : σ ^ 2 = 1) (hfit : ε⁻¹ + 1 ≤ δ⁻¹) :
    recenteringCylinderMap hσ hfit '' controlledCylinder ε ⊆ controlledCylinder δ := by
  rintro q ⟨z, hz, rfl⟩
  change -δ⁻¹ ≤ (recenteringCylinderMap hσ hfit z).val.2 ∧
    (recenteringCylinderMap hσ hfit z).val.2 ≤ δ⁻¹
  rw [recenteringCylinderMap_val]
  change -ε⁻¹ ≤ z.val.2 ∧ z.val.2 ≤ ε⁻¹ at hz
  rcases sq_eq_one_iff.mp hσ with rfl | rfl <;> constructor <;> linarith [hz.1, hz.2]

theorem recenteringCylinderMap_signed_height {ε δ σ : ℝ} (hσ : σ ^ 2 = 1)
    (hfit : ε⁻¹ + 1 ≤ δ⁻¹) (q : bufferedCylinder ε) :
    σ * ((recenteringCylinderMap hσ hfit q).val.2 - σ) = q.val.2 := by
  rw [recenteringCylinderMap_val]
  change σ * (σ * (1 + q.val.2) - σ) = q.val.2
  calc
    _ = σ ^ 2 * q.val.2 := by ring
    _ = _ := by rw [hσ, one_mul]

theorem offset_mem_bufferedCylinder {δ σ : ℝ} (hδ : 0 < δ) (hσ : σ ^ 2 = 1)
    (y : S2) : (y, σ) ∈ bufferedCylinder δ := by
  change -δ⁻¹ - 1 < σ ∧ σ < δ⁻¹ + 1
  have hi := inv_pos.mpr hδ
  rcases sq_eq_one_iff.mp hσ with rfl | rfl <;> constructor <;> linarith

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

namespace normalizedDatum

variable {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}

def recenteringMap (d : normalizedDatum g x₀ δ k) {ε σ : ℝ}
    (hσ : σ ^ 2 = 1) (hfit : ε⁻¹ + 1 ≤ δ⁻¹) : bufferedCylinder ε → M :=
  d.map ∘ recenteringCylinderMap hσ hfit

theorem recenteringMap_apply (d : normalizedDatum g x₀ δ k) {ε σ : ℝ}
    (hσ : σ ^ 2 = 1) (hfit : ε⁻¹ + 1 ≤ δ⁻¹) (q : bufferedCylinder ε) :
    d.recenteringMap hσ hfit q = d.map
      ⟨(q.val.1, σ * (1 + q.val.2)), by
        rw [← recenteringCylinderMap_val hσ hfit q]
        exact (recenteringCylinderMap hσ hfit q).property⟩ := by
  apply congrArg d.map
  apply Subtype.ext
  exact recenteringCylinderMap_val hσ hfit q

theorem contMDiff_recenteringMap (d : normalizedDatum g x₀ δ k) {ε σ : ℝ}
    (hσ : σ ^ 2 = 1) (hfit : ε⁻¹ + 1 ≤ δ⁻¹) :
    ContMDiff IC I ∞ (d.recenteringMap hσ hfit) :=
  d.smooth.comp (contMDiff_recenteringCylinderMap hσ hfit)

theorem injective_recenteringMap (d : normalizedDatum g x₀ δ k) {ε σ : ℝ}
    (hσ : σ ^ 2 = 1) (hfit : ε⁻¹ + 1 ≤ δ⁻¹) : Injective (d.recenteringMap hσ hfit) :=
  d.injective.comp (injective_recenteringCylinderMap hσ hfit)

theorem immersion_recenteringMap (d : normalizedDatum g x₀ δ k) {ε σ : ℝ}
    (hσ : σ ^ 2 = 1) (hfit : ε⁻¹ + 1 ≤ δ⁻¹) (q : bufferedCylinder ε) :
    Injective (mfderiv IC I (d.recenteringMap hσ hfit) q) := by
  have hd := d.smooth.mdifferentiable (by simp)
  have hc := (contMDiff_recenteringCylinderMap hσ hfit).mdifferentiable (by simp)
  rw [recenteringMap, mfderiv_comp q (hd _) (hc _)]
  apply (d.immersion _).comp
  intro v w hvw
  have hslots : (v.1, σ * v.2) = (w.1, σ * w.2) :=
    (recenteringCylinderMap_mfderiv hσ hfit q v).symm.trans
      (hvw.trans (recenteringCylinderMap_mfderiv hσ hfit q w))
  have hσ0 : σ ≠ 0 := by intro hz; simp [hz] at hσ
  have hfst := congrArg (fun u : EuclideanSpace ℝ (Fin 2) × ℝ => u.1) hslots
  have hsnd := congrArg (fun u : EuclideanSpace ℝ (Fin 2) × ℝ => u.2) hslots
  exact Prod.ext hfst (mul_left_cancel₀ hσ0 hsnd)

theorem recenteringMap_center (d : normalizedDatum g x₀ δ k) {ε σ : ℝ}
    (hε : 0 < ε) (hσ : σ ^ 2 = 1) (hfit : ε⁻¹ + 1 ≤ δ⁻¹) :
    d.recenteringMap hσ hfit (cylinderCenter ε hε) =
      d.map ⟨(spherePoint, σ), offset_mem_bufferedCylinder d.precision_pos hσ spherePoint⟩ := by
  apply congrArg d.map
  apply Subtype.ext
  rw [recenteringCylinderMap_val]
  simp [cylinderCenter]

end normalizedDatum
end DifferentialGeometry.Geometry.Neck
