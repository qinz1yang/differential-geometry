import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapChartOverlap
import DifferentialGeometry.Geometry.Metric.PolarCoordinates

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold
open DifferentialGeometry.Topology.Manifold.Attachment DifferentialGeometry.Geometry.Neck
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev S2 := Metric.sphere (0 : E3) 1
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)
private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

def cuttingAnnulus (L δ : ℝ) : Opens E3 :=
  ⟨{x | L < ‖x‖ ∧ ‖x‖ < L + cuttingCollarWidth δ},
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)⟩

def cuttingAnnulusCollar {L δ : ℝ} (hL : 0 < L) (x : cuttingAnnulus L δ) :
    S2 × Ico (0 : ℝ) (cuttingCollarWidth δ) :=
  (retainedCylinderHomeomorphShell hL).symm ⟨⟨x.val, x.property.2⟩, x.property.1.le⟩

theorem cuttingAnnulusCollar_radius {L δ : ℝ} (hL : 0 < L) (x : cuttingAnnulus L δ) :
    (cuttingAnnulusCollar hL x).2.val = ‖x.val‖ - L := rfl

theorem cuttingAnnulusCollar_direction {L δ : ℝ} (hL : 0 < L) (x : cuttingAnnulus L δ) :
    (cuttingAnnulusCollar hL x).1.val = ‖x.val‖⁻¹ • x.val := by
  exact homeomorphUnitSphereProd_apply_fst_coe E3 _

theorem cuttingAnnulusCollar_radial {L δ : ℝ} (hL : 0 < L) (x : cuttingAnnulus L δ) :
    (L + (cuttingAnnulusCollar hL x).2.val) • (cuttingAnnulusCollar hL x).1.val = x.val :=
  congrArg (fun z : {y : {v : E3 // ‖v‖ < L + cuttingCollarWidth δ} // L ≤ ‖y.val‖} => z.val.val)
    ((retainedCylinderHomeomorphShell hL).apply_symm_apply ⟨⟨x.val, x.property.2⟩, x.property.1.le⟩)

def cuttingAnnulusCylinderMap {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (b : Bool) :
    cuttingAnnulus L δ → bufferedCylinder δ :=
  fun x => cuttingCollarCylinderMap hδ b (cuttingAnnulusCollar hL x)

theorem cuttingAnnulusCylinderMap_val {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (b : Bool) (x : cuttingAnnulus L δ) :
    (cuttingAnnulusCylinderMap hL hδ b x).val =
      ((cuttingAnnulusCollar hL x).1, cuttingSign b + cuttingSign b * (‖x.val‖ - L)) := rfl

theorem contMDiff_cuttingAnnulusCylinderMap {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (b : Bool) :
    ContMDiff (𝓡 3) IC ∞ (cuttingAnnulusCylinderMap hL hδ b) := by
  have hn : ContMDiff (𝓡 3) 𝓘(ℝ) ∞ (fun x : cuttingAnnulus L δ => ‖x.val‖) := by
    intro x
    apply (contMDiffAt_subtype_iff (U := cuttingAnnulus L δ)).mpr
    exact (contDiffAt_norm ℝ (norm_pos_iff.mp (hL.trans x.property.1))).contMDiffAt
  have hne (x : cuttingAnnulus L δ) : ‖x.val‖ ≠ 0 := (hL.trans x.property.1).ne'
  have hang : ContMDiff (𝓡 3) (𝓡 2) ∞ (fun x : cuttingAnnulus L δ => (cuttingAnnulusCollar hL x).1) := by
    have hv : ContMDiff (𝓡 3) (𝓡 3) ∞
        (fun x : cuttingAnnulus L δ => (cuttingAnnulusCollar hL x).1.val) := by
      simp_rw [cuttingAnnulusCollar_direction]
      exact (hn.inv₀ hne).smul (contMDiff_subtype_val (U := cuttingAnnulus L δ))
    exact ContMDiff.codRestrict_sphere hv (fun x => (cuttingAnnulusCollar hL x).1.property)
  apply (ContMDiff.subtypeVal_comp_iff (bufferedCylinder δ) (cuttingAnnulusCylinderMap hL hδ b)).mp
  exact hang.prodMk (contMDiff_const.add (contMDiff_const.mul (hn.sub contMDiff_const)))

def cuttingCylinderRadialMap (L δ : ℝ) (b : Bool) (q : bufferedCylinder δ) : E3 :=
  (L + cuttingSign b * q.val.2 - 1) • q.val.1.val

theorem contMDiff_cuttingCylinderRadialMap (L δ : ℝ) (b : Bool) :
    ContMDiff IC (𝓡 3) ∞ (cuttingCylinderRadialMap L δ b) := by
  have hv := contMDiff_subtype_val (n := ∞) (I := IC) (U := bufferedCylinder δ)
  exact ((contMDiff_const.add (contMDiff_const.mul (contMDiff_snd.comp hv))).sub contMDiff_const).smul
    ((contMDiff_coe_sphere (n := 2)).comp (contMDiff_fst.comp hv))

theorem cuttingCylinderRadialMap_annulus {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (b : Bool) (x : cuttingAnnulus L δ) :
    cuttingCylinderRadialMap L δ b (cuttingAnnulusCylinderMap hL hδ b x) = x.val := by
  change (L + cuttingSign b * (cuttingSign b + cuttingSign b * (‖x.val‖ - L)) - 1) •
    (cuttingAnnulusCollar hL x).1.val = x.val
  have he : L + cuttingSign b * (cuttingSign b + cuttingSign b * (‖x.val‖ - L)) - 1 =
      L + (cuttingAnnulusCollar hL x).2.val := by
    rw [cuttingAnnulusCollar_radius]
    calc
      _ = L + cuttingSign b ^ 2 + cuttingSign b ^ 2 * (‖x.val‖ - L) - 1 := by ring
      _ = _ := by rw [cuttingSign_sq]; ring
  rw [he]
  exact cuttingAnnulusCollar_radial hL x

theorem cuttingAnnulusCylinderMap_injective {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (b : Bool) :
    Injective (cuttingAnnulusCylinderMap hL hδ b) := by
  intro x y h
  apply Subtype.ext
  simpa only [cuttingCylinderRadialMap_annulus] using congrArg (cuttingCylinderRadialMap L δ b) h

theorem cuttingAnnulusCylinderMap_mfderiv_injective {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (b : Bool) (x : cuttingAnnulus L δ) :
    Injective (mfderiv (𝓡 3) IC (cuttingAnnulusCylinderMap hL hδ b) x) := by
  let F := cuttingAnnulusCylinderMap hL hδ b
  let G := cuttingCylinderRadialMap L δ b
  have he : G ∘ F = (Subtype.val : cuttingAnnulus L δ → E3) :=
    funext (cuttingCylinderRadialMap_annulus hL hδ b)
  have hd := mfderiv_comp (I := 𝓡 3) (I' := IC) (I'' := 𝓡 3) x
    ((contMDiff_cuttingCylinderRadialMap L δ b).mdifferentiable (by decide) (F x))
    ((contMDiff_cuttingAnnulusCylinderMap hL hδ b).mdifferentiable (by decide) x)
  change mfderiv (𝓡 3) (𝓡 3) (G ∘ F) x =
    (mfderiv IC (𝓡 3) G (F x)).comp (mfderiv (𝓡 3) IC F x) at hd
  rw [he, DifferentialGeometry.mfderiv_subtype_val] at hd
  intro v w hvw
  have h := congrArg (mfderiv IC (𝓡 3) G (F x)) hvw
  have hv := congrArg (fun D => D v) hd
  have hw := congrArg (fun D => D w) hd
  exact hv.trans (h.trans hw.symm)

theorem cuttingAnnulusCylinderMap_isLocalDiffeomorph {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (b : Bool) :
    IsLocalDiffeomorph (𝓡 3) IC ∞ (cuttingAnnulusCylinderMap hL hδ b) :=
  DifferentialGeometry.Topology.Manifold.isLocalDiffeomorph_of_injective_mfderiv _
    (contMDiff_cuttingAnnulusCylinderMap hL hδ b)
    (cuttingAnnulusCylinderMap_mfderiv_injective hL hδ b) (by simp)
end DifferentialGeometry.Topology.ThreeManifold.Surgery
