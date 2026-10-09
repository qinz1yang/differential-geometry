import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.TorusCurveRelativePush
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.TorusBigonAnnulus
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.LinearSeams
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.CliffordCoordinates
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.FilledCarrier

/-!
# The mapping class group of the torus is linear

Chapter 6, packet K08, lane MC5 of the `TorusMappingClassLinear` programme (survey §5 MC5,
review 12). The annulus push of MC2 (`exists_isotopic_annulus_push`) and the relative push of MC4
(`exists_isotopic_beta_push`) discharge the two hypotheses of the curve-straightening chain, which
gives the frozen stage (ii) and (i) statements and the kernel theorem
`isotopic_refl_of_torusMatrix_eq_one` (a torus diffeomorphism with matrix `1` is isotopic to the
identity); `torusMappingClassLinear_holds` follows from the reduction of MC0.

Corollaries, each derived once from the theorem:
- `exists_collar_concordance` (W2): the slice diffeomorphism `(x, s) ↦ (collarTwist s x, s)` of
  `SF/LinearSeams.lean` built from the linear isotopy of `φ`.
- `exists_solidTorus_extension` (EXT): for `ψ` with matrix `1` and an isotopy `F` from `ψ` to the
  identity, `Θ (z, w) = (‖z‖ · u', w')` with `(u', w') = F (χ ‖z‖) (z / ‖z‖, w)`, where the cutoff
  `χ` is `0` for `‖z‖ ≥ 1` and `1` for `‖z‖ ≤ 1/2`; it is the identity on `‖z‖ < 1/2` and the
  radial extension of `ψ` on `‖z‖ ≥ 1`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

namespace GC.Seifert

open AnnulusStraightening

theorem exists_isotopic_height_one_of_forall_ne (φ : TDiff) (h : torusMatrix φ = 1)
    {s : Circle} (hs : ∀ z, heightOnCircle φ z ≠ s) :
    ∃ ψ : TDiff, IsotopicDiffeomorph φ ψ ∧ ∀ z, heightOnCircle ψ z = 1 :=
  exists_isotopic_height_one_of_forall_ne_of_push exists_isotopic_annulus_push φ h hs

theorem exists_isotopic_height_one (φ : TDiff) (h : torusMatrix φ = 1) :
    ∃ ψ : TDiff, IsotopicDiffeomorph φ ψ ∧ ∀ z, heightOnCircle ψ z = 1 :=
  exists_isotopic_height_one_of_push exists_isotopic_annulus_push φ h

theorem isotopic_refl_of_torusMatrix_eq_one (φ : TDiff) (h : torusMatrix φ = 1) :
    IsotopicDiffeomorph φ torusRefl :=
  isotopic_refl_of_torusMatrix_eq_one_of_push exists_isotopic_annulus_push
    exists_isotopic_beta_push φ h

theorem torusMappingClassLinear_holds : TorusMappingClassLinear :=
  torusMappingClassLinear_of_isotopic_refl isotopic_refl_of_torusMatrix_eq_one

theorem exists_collar_concordance (φ : TDiff) :
    ∃ Θ : (Torus × ℝ) ≃ₘ⟮signedCollarModel, signedCollarModel⟯ (Torus × ℝ),
      (∀ x s, s ≤ 1 / 4 →
        Θ (x, s) = (φ ((linearTorusDiffeomorph (torusUnit φ)).symm x), s)) ∧
      ∀ x s, 1 / 2 ≤ s → Θ (x, s) = (x, s) := by
  set hL := torusMappingClassLinear_holds
  refine ⟨sliceDiffeomorph (collarTwist hL φ) (contMDiff_collarTwist hL φ)
    (contMDiff_collarTwist_symm hL φ) (fun s : ℝ => s) contMDiff_id, fun x s hs => ?_,
    fun x s hs => ?_⟩
  · change (collarTwist hL φ s x, s) = _
    conv_lhs => rw [← (linearTorusDiffeomorph (torusUnit φ)).apply_symm_apply x]
    rw [collarTwist_apply_linear hL φ hs]
  · change (collarTwist hL φ s x, s) = _
    rw [collarTwist_of_ge hL φ hs]

def extCut (r : ℝ) : ℝ := Real.smoothTransition (2 - 2 * r)

theorem contDiff_extCut : ContDiff ℝ ∞ extCut :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub (contDiff_const.mul contDiff_id))

theorem extCut_of_le {r : ℝ} (hr : r ≤ 1 / 2) : extCut r = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem extCut_of_ge {r : ℝ} (hr : 1 ≤ r) : extCut r = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

def extMap (G : ℝ → TDiff) (x : ℂ × Circle) : ℂ × Circle :=
  (((‖x.1‖ : ℝ) : ℂ) * ((G (extCut ‖x.1‖) (unitOf x.1, x.2)).1 : ℂ),
    (G (extCut ‖x.1‖) (unitOf x.1, x.2)).2)

theorem norm_real_mul_circle {r : ℝ} (hr : 0 ≤ r) (u : Circle) : ‖(r : ℂ) * (u : ℂ)‖ = r := by
  rw [norm_mul, Complex.norm_real, Circle.norm_coe, mul_one, Real.norm_of_nonneg hr]

theorem unitOf_real_mul {r : ℝ} (hr : 0 < r) (u : Circle) : unitOf ((r : ℂ) * (u : ℂ)) = u := by
  rw [← Complex.real_smul]
  exact unitOf_smul hr u

theorem extMap_of_lt {G : ℝ → TDiff} (hG1 : ∀ p, G 1 p = p) {x : ℂ × Circle}
    (hx : ‖x.1‖ < 1 / 2) : extMap G x = x := by
  simp only [extMap, extCut_of_le hx.le, hG1]
  refine Prod.ext ?_ rfl
  change ((‖x.1‖ : ℝ) : ℂ) * (unitOf x.1 : ℂ) = x.1
  rw [← Complex.real_smul]
  exact norm_smul_unitOf x.1

theorem extMap_real_mul (G : ℝ → TDiff) {r : ℝ} (hr : 1 ≤ r) (u w : Circle) :
    extMap G ((r : ℂ) * (u : ℂ), w) = ((r : ℂ) * ((G 0 (u, w)).1 : ℂ), (G 0 (u, w)).2) := by
  simp only [extMap, norm_real_mul_circle (by linarith : (0 : ℝ) ≤ r),
    unitOf_real_mul (by linarith : (0 : ℝ) < r), extCut_of_ge hr]

theorem extMap_extMap {G H : ℝ → TDiff} (hG1 : ∀ p, G 1 p = p)
    (hHG : ∀ t p, H t (G t p) = p) (x : ℂ × Circle) : extMap H (extMap G x) = x := by
  have hH1 : ∀ p, H 1 p = p := fun p => by
    conv_lhs => rw [← hG1 p]
    exact hHG 1 p
  by_cases hx : ‖x.1‖ < 1 / 2
  · rw [extMap_of_lt hG1 hx, extMap_of_lt hH1 hx]
  · push Not at hx
    have hpos : 0 < ‖x.1‖ := by linarith
    set t := extCut ‖x.1‖
    set q := G t (unitOf x.1, x.2) with hq
    have he : extMap G x = (((‖x.1‖ : ℝ) : ℂ) * (q.1 : ℂ), q.2) := rfl
    rw [he]
    simp only [extMap, norm_real_mul_circle hpos.le, unitOf_real_mul hpos]
    change (((‖x.1‖ : ℝ) : ℂ) * ((H t (q.1, q.2)).1 : ℂ), (H t (q.1, q.2)).2) = x
    rw [show ((q.1, q.2) : Torus) = q from rfl, hq, hHG]
    refine Prod.ext ?_ rfl
    change ((‖x.1‖ : ℝ) : ℂ) * (unitOf x.1 : ℂ) = x.1
    rw [← Complex.real_smul]
    exact norm_smul_unitOf x.1

theorem contMDiff_extMap {G : ℝ → TDiff}
    (hG : ContMDiff (𝓘(ℝ).prod torusModel) torusModel ∞ (fun q : ℝ × Torus => G q.1 q.2))
    (hG1 : ∀ p, G 1 p = p) : ContMDiff PlaneCircleModel PlaneCircleModel ∞ (extMap G) := by
  intro x
  by_cases hx : ‖x.1‖ < 1 / 2
  · refine contMDiffAt_id.congr_of_eventuallyEq ?_
    have ho : IsOpen {q : ℂ × Circle | ‖q.1‖ < 1 / 2} :=
      isOpen_lt (continuous_norm.comp continuous_fst) continuous_const
    filter_upwards [ho.mem_nhds hx] with q hq
    exact extMap_of_lt hG1 hq
  · push Not at hx
    have hz : x.1 ≠ 0 := fun h0 => by rw [h0, norm_zero] at hx; linarith
    have hfst : ContMDiffAt PlaneCircleModel 𝓘(ℝ, ℂ) ∞ (fun q : ℂ × Circle => q.1) x :=
      contMDiff_fst.contMDiffAt
    have hn : ContMDiffAt PlaneCircleModel 𝓘(ℝ, ℝ) ∞ (fun q : ℂ × Circle => ‖q.1‖) x :=
      (contDiffAt_norm ℝ hz).contMDiffAt.comp x hfst
    have hu : ContMDiffAt PlaneCircleModel (𝓡 1) ∞ (fun q : ℂ × Circle => unitOf q.1) x :=
      (contMDiffOn_unitOf.contMDiffAt (isOpen_ne.mem_nhds hz)).comp x hfst
    have hχ : ContMDiffAt PlaneCircleModel 𝓘(ℝ, ℝ) ∞
        (fun q : ℂ × Circle => extCut ‖q.1‖) x :=
      contDiff_extCut.contMDiff.contMDiffAt.comp x hn
    have harg : ContMDiffAt PlaneCircleModel (𝓘(ℝ).prod torusModel) ∞
        (fun q : ℂ × Circle => (extCut ‖q.1‖, ((unitOf q.1, q.2) : Torus))) x :=
      hχ.prodMk (hu.prodMk contMDiff_snd.contMDiffAt)
    have hp : ContMDiffAt PlaneCircleModel torusModel ∞
        (fun q : ℂ × Circle => G (extCut ‖q.1‖) (unitOf q.1, q.2)) x :=
      hG.contMDiffAt.comp x harg
    have hofn : ContMDiffAt PlaneCircleModel 𝓘(ℝ, ℂ) ∞
        (fun q : ℂ × Circle => ((‖q.1‖ : ℝ) : ℂ)) x :=
      Complex.ofRealCLM.contDiff.contMDiff.contMDiffAt.comp x hn
    have hpc : ContMDiffAt PlaneCircleModel 𝓘(ℝ, ℂ) ∞
        (fun q : ℂ × Circle => ((G (extCut ‖q.1‖) (unitOf q.1, q.2)).1 : ℂ)) x :=
      contMDiff_circle_coe.contMDiffAt.comp x (contMDiff_fst.contMDiffAt.comp x hp)
    have hmul : ContMDiffAt PlaneCircleModel 𝓘(ℝ, ℂ) ∞ (fun q : ℂ × Circle =>
        ((‖q.1‖ : ℝ) : ℂ) * ((G (extCut ‖q.1‖) (unitOf q.1, q.2)).1 : ℂ)) x :=
      (contDiff_mul (𝕜 := ℝ) (𝔸 := ℂ)).contMDiff.contMDiffAt.comp x (hofn.prodMk_space hpc)
    exact hmul.prodMk (contMDiff_snd.contMDiffAt.comp x hp)

theorem exists_solidTorus_extension (ψ : TDiff) (h : torusMatrix ψ = 1) :
    ∃ Θ : (ℂ × Circle) ≃ₘ⟮PlaneCircleModel, PlaneCircleModel⟯ (ℂ × Circle),
      ∀ (r : ℝ) (u w : Circle), 1 ≤ r →
        Θ ((r : ℂ) * (u : ℂ), w) = ((r : ℂ) * ((ψ (u, w)).1 : ℂ), (ψ (u, w)).2) := by
  obtain ⟨F, hF, hF', h0, h1⟩ := isotopic_refl_of_torusMatrix_eq_one ψ h
  have hF1 : ∀ p, F 1 p = p := fun p => by rw [h1]; rfl
  have hF1' : ∀ p, (F 1).symm p = p := fun p => by rw [h1]; rfl
  refine ⟨{ toFun := extMap F
            invFun := extMap (fun t => (F t).symm)
            left_inv := extMap_extMap hF1 fun t p => (F t).symm_apply_apply p
            right_inv := extMap_extMap hF1' fun t p => (F t).apply_symm_apply p
            contMDiff_toFun := contMDiff_extMap hF hF1
            contMDiff_invFun := contMDiff_extMap (G := fun t => (F t).symm) hF' hF1' },
    fun r u w hr => ?_⟩
  change extMap F _ = _
  rw [extMap_real_mul F hr, h0]

end GC.Seifert
