import DifferentialGeometry.Geometry.Collapse.Inhabitants.EdgeCapHeight
import DifferentialGeometry.Analysis.ODE.Flow.Complete
import DifferentialGeometry.Analysis.ODE.IntegralCurveNaturality
import DifferentialGeometry.Analysis.Calculus.Cutoff.GraphPacketProfiles
import Mathlib.Topology.Algebra.ConstMulAction
set_option autoImplicit false
noncomputable section
open Bundle Set Manifold
open DifferentialGeometry.Analysis DifferentialGeometry.Analysis.ODE
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse.EdgeCapFlow

def capFlowCutoff (Δ x : ℝ) : ℝ := edgeCoordinateProfile (x / (Δ / 2))
theorem capFlowCutoff_smooth (Δ : ℝ) : ContDiff ℝ ∞ (capFlowCutoff Δ) :=
  edgeProfiles_contDiff.1.comp (contDiff_id.div_const (Δ / 2))
theorem capFlowCutoff_compact (Δ : ℝ) (hΔ : 0 < Δ) : HasCompactSupport (capFlowCutoff Δ) := by
  have hK : HasCompactSupport edgeCoordinateProfile :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) edgeProfiles_support.1
  have hh := hK.comp_smul (inv_ne_zero (div_pos hΔ (by norm_num : (0 : ℝ) < 2)).ne')
  change HasCompactSupport (fun x : ℝ => edgeCoordinateProfile (x / (Δ / 2)))
  simpa only [smul_eq_mul, div_eq_mul_inv, mul_comm] using hh

theorem capFlowCutoff_one (Δ : ℝ) (hΔ : 0 < Δ) (x : ℝ) (hx : |x| ≤ 4 * Δ) :
    capFlowCutoff Δ x = 1 := by
  apply edgeProfiles_plateaus.1
  change -(8 : ℝ) ≤ x / (Δ / 2) ∧ x / (Δ / 2) ≤ 8
  rw [← abs_le, abs_div, abs_of_pos (div_pos hΔ (by norm_num))]
  apply (div_le_iff₀ (div_pos hΔ (by norm_num))).mpr
  nlinarith

theorem capFlowCutoff_zero (Δ : ℝ) (hΔ : 0 < Δ) (x : ℝ) (hx : 5 * Δ ≤ |x|) :
    capFlowCutoff Δ x = 0 := by
  by_contra hn
  have hs : x / (Δ / 2) ∈ tsupport edgeCoordinateProfile :=
    subset_tsupport _ hn
  have hb := edgeProfiles_support.1 hs
  have ha : |x / (Δ / 2)| ≤ 9 := abs_le.mpr hb
  rw [abs_div, abs_of_pos (div_pos hΔ (by norm_num))] at ha
  have hm := (div_le_iff₀ (div_pos hΔ (by norm_num))).mp ha
  nlinarith

def capScalarField (Δ : ℝ) (x : ℝ) : TangentSpace 𝓘(ℝ, ℝ) x := capFlowCutoff Δ x

theorem capScalarField_smooth (Δ : ℝ) :
    ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞
      (fun x : ℝ => (⟨x, capScalarField Δ x⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) :=
  contMDiff_vectorSpace_iff_contDiff.mpr (capFlowCutoff_smooth Δ)

theorem capScalarComplete (Δ : ℝ) (hΔ : 0 < Δ) :
    ∀ x : ℝ, ∃ γ : ℝ → ℝ, γ 0 = x ∧ IsMIntegralCurve γ (capScalarField Δ) :=
  exists_globalIntegralCurve_of_compactSupport (capScalarField Δ) (capScalarField_smooth Δ)
    (capFlowCutoff_compact Δ hΔ)

def capScalarFlow (Δ : ℝ) (hΔ : 0 < Δ) (t : ℝ) : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓘(ℝ, ℝ)⟯ ℝ :=
  curveAtDiffeomorph (capScalarField Δ) (capScalarField_smooth Δ) (capScalarComplete Δ hΔ) t

theorem capScalarFlow_joint (Δ : ℝ) (hΔ : 0 < Δ) :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × ℝ => capScalarFlow Δ hΔ q.1 q.2) :=
  contMDiff_curveAt (capScalarField Δ) (capScalarField_smooth Δ) (capScalarComplete Δ hΔ)

theorem capScalarFlow_zero (Δ : ℝ) (hΔ : 0 < Δ) :
    capScalarFlow Δ hΔ 0 = Diffeomorph.refl 𝓘(ℝ, ℝ) ℝ ∞ :=
  curveAtDiffeomorph_zero _ _ _

theorem capScalarFlow_add (Δ : ℝ) (hΔ : 0 < Δ) (s t : ℝ) :
    (capScalarFlow Δ hΔ s).trans (capScalarFlow Δ hΔ t) = capScalarFlow Δ hΔ (s + t) :=
  (curveAtDiffeomorph_add _ _ _ s t).symm

theorem capScalarFlow_fixed (Δ : ℝ) (hΔ : 0 < Δ) (x : ℝ) (hx : 5 * Δ ≤ |x|) (t : ℝ) :
    capScalarFlow Δ hΔ t x = x :=
  curveAt_eq_self_of_eq_zero (capScalarField Δ)
    ((capScalarField_smooth Δ).of_le (by norm_num)) (capScalarComplete Δ hΔ)
    (capFlowCutoff_zero Δ hΔ x hx) t

theorem capScalarFlow_preserves_interval (Δ : ℝ) (hΔ : 0 < Δ) (x : ℝ)
    (hx : |x| < 5 * Δ) (t : ℝ) : |capScalarFlow Δ hΔ t x| < 5 * Δ := by
  by_contra hn
  have hout : 5 * Δ ≤ |capScalarFlow Δ hΔ t x| := le_of_not_gt hn
  have hf := capScalarFlow_fixed Δ hΔ (capScalarFlow Δ hΔ t x) hout (-t)
  have hback : capScalarFlow Δ hΔ (-t) (capScalarFlow Δ hΔ t x) = x := by
    have h := congrArg (fun D : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓘(ℝ, ℝ)⟯ ℝ => D x)
      (capScalarFlow_add Δ hΔ t (-t))
    rw [add_neg_cancel, capScalarFlow_zero] at h
    change capScalarFlow Δ hΔ (-t) (capScalarFlow Δ hΔ t x) = x at h
    exact h
  have heq : capScalarFlow Δ hΔ t x = x := hf.symm.trans hback
  rw [heq] at hout
  exact (not_le_of_gt hx) hout

theorem capScalarFlow_translation (Δ : ℝ) (hΔ : 0 < Δ) (t : ℝ) (ht : |t| < 4 * Δ) :
    capScalarFlow Δ hΔ t 0 = t := by
  have hz : (0 : ℝ) ∈ Ioo (-(4 * Δ)) (4 * Δ) := by constructor <;> linarith
  have hcurve : IsMIntegralCurveOn (I := 𝓘(ℝ, ℝ)) (fun s : ℝ => s)
      (capScalarField Δ) (Ioo (-(4 * Δ)) (4 * Δ)) := by
    change IsMIntegralCurveOn (I := 𝓘(ℝ, ℝ)) (fun s : ℝ => s)
      (fun x : ℝ => capFlowCutoff Δ x) _
    apply isMIntegralCurveOn_iff_isIntegralCurveOn.mpr
    intro s hs
    have hb : |s| ≤ 4 * Δ := (abs_lt.mpr hs).le
    change HasDerivWithinAt (fun r : ℝ => r) (capFlowCutoff Δ s)
      (Ioo (-(4 * Δ)) (4 * Δ)) s
    rw [capFlowCutoff_one Δ hΔ s hb]
    exact (hasDerivAt_id s).hasDerivWithinAt
  have htraj := curveAt_integralCurve (capScalarField Δ) (capScalarComplete Δ hΔ) (0 : ℝ)
  have htrajOn := htraj.isMIntegralCurveOn (Ioo (-(4 * Δ)) (4 * Δ))
  have hstart := curveAt_zero (capScalarField Δ) (capScalarComplete Δ hΔ) (0 : ℝ)
  have heq := isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless hz
    ((capScalarField_smooth Δ).of_le (by norm_num : (1 : ℕ∞ω) ≤ ∞))
    htrajOn hcurve hstart
  exact heq (abs_lt.mp ht)

def capFlowInterval (Δ : ℝ) : TopologicalSpace.Opens ℝ :=
  ⟨{x | |x| < 5 * Δ}, isOpen_lt continuous_abs continuous_const⟩

theorem capScalarFlow_symm (Δ : ℝ) (hΔ : 0 < Δ) (t : ℝ) :
    (capScalarFlow Δ hΔ t).symm = capScalarFlow Δ hΔ (-t) :=
  curveAtDiffeomorph_symm _ _ _ t

def capIntervalFlow (Δ : ℝ) (hΔ : 0 < Δ) (t : ℝ) :
    capFlowInterval Δ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓘(ℝ, ℝ)⟯ capFlowInterval Δ where
  toFun x := ⟨capScalarFlow Δ hΔ t x, capScalarFlow_preserves_interval Δ hΔ x x.2 t⟩
  invFun x := ⟨capScalarFlow Δ hΔ (-t) x, capScalarFlow_preserves_interval Δ hΔ x x.2 (-t)⟩
  left_inv x := by
    apply Subtype.ext
    change capScalarFlow Δ hΔ (-t) (capScalarFlow Δ hΔ t x) = x
    rw [← capScalarFlow_symm]
    exact (capScalarFlow Δ hΔ t).symm_apply_apply x
  right_inv x := by
    apply Subtype.ext
    change capScalarFlow Δ hΔ t (capScalarFlow Δ hΔ (-t) x) = x
    rw [← capScalarFlow_symm]
    exact (capScalarFlow Δ hΔ t).apply_symm_apply x
  contMDiff_toFun := by
    apply (ContMDiff.subtypeVal_comp_iff (capFlowInterval Δ) _).mp
    exact (capScalarFlow Δ hΔ t).contMDiff.comp contMDiff_subtype_val
  contMDiff_invFun := by
    apply (ContMDiff.subtypeVal_comp_iff (capFlowInterval Δ) _).mp
    exact (capScalarFlow Δ hΔ (-t)).contMDiff.comp contMDiff_subtype_val

theorem capIntervalFlow_joint (Δ : ℝ) (hΔ : 0 < Δ) :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × capFlowInterval Δ => capIntervalFlow Δ hΔ q.1 q.2) := by
  apply (ContMDiff.subtypeVal_comp_iff (capFlowInterval Δ) _).mp
  exact (capScalarFlow_joint Δ hΔ).comp
    (contMDiff_fst.prodMk (contMDiff_subtype_val.comp contMDiff_snd))

theorem capIntervalFlow_zero (Δ : ℝ) (hΔ : 0 < Δ) :
    capIntervalFlow Δ hΔ 0 = Diffeomorph.refl 𝓘(ℝ, ℝ) (capFlowInterval Δ) ∞ := by
  ext x
  change capScalarFlow Δ hΔ 0 x = x
  rw [capScalarFlow_zero]
  rfl

theorem capIntervalFlow_add (Δ : ℝ) (hΔ : 0 < Δ) (s t : ℝ) :
    (capIntervalFlow Δ hΔ s).trans (capIntervalFlow Δ hΔ t) = capIntervalFlow Δ hΔ (s + t) := by
  ext x
  have h := congrArg (fun D : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓘(ℝ, ℝ)⟯ ℝ => D x)
    (capScalarFlow_add Δ hΔ s t)
  exact h

open DifferentialGeometry.Geometry.Collapse.EdgeCapSurface
open DifferentialGeometry.Geometry.Collapse.EdgeCapProduct
open DifferentialGeometry.Geometry.Collapse.EdgeCapHeight

def capRadialProductFlow (Δ : ℝ) (hΔ : 0 < Δ) (t : ℝ) :
    (capFlowInterval Δ × E2) ≃ₘ⟮𝓘(ℝ, ℝ).prod (𝓡 2), 𝓘(ℝ, ℝ).prod (𝓡 2)⟯
      (capFlowInterval Δ × E2) :=
  (capIntervalFlow Δ hΔ t).prodCongr (Diffeomorph.refl (𝓡 2) E2 ∞)

theorem capRadialProductFlow_radial (Δ : ℝ) (hΔ : 0 < Δ) (t : ℝ)
    (p : capFlowInterval Δ × E2) : (capRadialProductFlow Δ hΔ t p).2 = p.2 := rfl

theorem capRadialProductFlow_height (Δ : ℝ) (hΔ : 0 < Δ) (t : ℝ)
    (p : capFlowInterval Δ × E2) :
    capExampleF (capProductCoordinates
      (((capRadialProductFlow Δ hΔ t p).1 : ℝ), (capRadialProductFlow Δ hΔ t p).2)) =
      capExampleF (capProductCoordinates ((p.1 : ℝ), p.2)) := by
  simp only [capExampleF, Diffeomorph.symm_apply_apply, capRadialProductFlow_radial]

theorem capRadialProductFlow_joint (Δ : ℝ) (hΔ : 0 < Δ) :
    ContMDiff (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ).prod (𝓡 2))) (𝓘(ℝ, ℝ).prod (𝓡 2)) ∞
      (fun q : ℝ × (capFlowInterval Δ × E2) => capRadialProductFlow Δ hΔ q.1 q.2) :=
  ((capIntervalFlow_joint Δ hΔ).comp
    (contMDiff_fst.prodMk (contMDiff_fst.comp contMDiff_snd))).prodMk
      (contMDiff_snd.comp contMDiff_snd)


theorem capRadialProductFlow_zero (Δ : ℝ) (hΔ : 0 < Δ) :
    capRadialProductFlow Δ hΔ 0 =
      Diffeomorph.refl (𝓘(ℝ, ℝ).prod (𝓡 2)) (capFlowInterval Δ × E2) ∞ := by
  apply DFunLike.ext
  intro p
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg (fun D => (D p.1 : ℝ)) (capIntervalFlow_zero Δ hΔ)
  · rfl

theorem capRadialProductFlow_add (Δ : ℝ) (hΔ : 0 < Δ) (s t : ℝ) :
    (capRadialProductFlow Δ hΔ s).trans (capRadialProductFlow Δ hΔ t) =
      capRadialProductFlow Δ hΔ (s + t) := by
  apply DFunLike.ext
  intro p
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg (fun D => (D p.1 : ℝ)) (capIntervalFlow_add Δ hΔ s t)
  · rfl

end DifferentialGeometry.Geometry.Collapse.EdgeCapFlow
