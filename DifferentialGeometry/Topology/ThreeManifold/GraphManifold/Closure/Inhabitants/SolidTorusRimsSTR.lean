import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.SolidTorusFacesSTR

/-!
# S-SOLIDTORUS4 (suffix `_STR`), G7 part 1: the rim base and the circle fibres

* the rim base `rimPoint_STR τ` (the point `q = qOf(√(15/16), (1 - 2τ) c(√(15/16)))` of the circle
  base, `t(q) = τ`, `‖q‖² = 15/16`), smooth in `τ`;
* the fibres of the restricted circle bundle: `x ∈ fibre c ↔ x ∈ circle domain ∧ z₂(x) = q(c)`
  (`mem_fibre_STR`), whence `fibre_height_STR`;
* `rim_fibre_STR`: the whole rim over `τ` is the whole circle fibre over `rimPoint τ`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0.SolidTorusSTR

open GC.GraphManifold.Assembly.FC39P0.SolidTorusSTI GC.GraphManifold.Assembly.FC39P0

local instance carrierCharts_RimsSTR : ChartedSpace (EuclideanHalfSpace 3) Wc.Carrier := by
  change ChartedSpace (EuclideanHalfSpace 3) solidTorusSet.{0}
  exact inferInstance

local instance carrierSmooth_RimsSTR : IsManifold (𝓡∂ 3) ∞ Wc.Carrier := by
  change IsManifold (𝓡∂ 3) ∞ solidTorusSet.{0}
  exact inferInstance

/-! ## The rim point -/

/-- The modulus `√(15/16)` of `z₂` on the rim. -/
def rr_STR : ℝ := √(15 / 16)

theorem rr_sq_STR : rr_STR ^ 2 = 15 / 16 :=
  Real.sq_sqrt (by norm_num)

theorem rr_pos_STR : 0 < rr_STR := Real.sqrt_pos.mpr (by norm_num)

theorem kap_lt_rr_STR : kap_STR < rr_STR := by
  have h := rr_sq_STR
  have h0 := rr_pos_STR
  norm_num [kap_STR]
  nlinarith

theorem rr_lt_one_STR : rr_STR < 1 := by
  have h := rr_sq_STR
  have h0 := rr_pos_STR
  nlinarith

/-- The `Z`-coordinate of the rim point over `τ`. -/
def zRim_STR (τ : ℝ) : ℝ := (1 - 2 * τ) * cR_STR rr_STR

/-- The rim point `z₂ = q(τ)` of the circle base. -/
def qRim_STR (τ : ℝ) : ℂ := qOf_STR rr_STR (zRim_STR τ)

theorem norm_qRim_STR (τ : ℝ) : ‖qRim_STR τ‖ = rr_STR :=
  norm_qOf_STR rr_pos_STR.le _

theorem tOf_qRim_STR (τ : ℝ) : tOf_STR (qRim_STR τ) = τ := by
  have hc := cR_pos_STR kap_lt_rr_STR
  rw [tOf_STR, qRim_STR, zOf_qOf_STR rr_pos_STR, norm_qOf_STR rr_pos_STR.le, zRim_STR]
  field_simp
  ring

theorem re_lt_norm_qRim_STR (τ : ℝ) : (qRim_STR τ).re < ‖qRim_STR τ‖ := by
  rw [norm_qRim_STR, qRim_STR, qOf_re_STR]
  have h : zRim_STR τ ^ 2 + 1 ≠ 0 := by positivity
  have h0 := rr_pos_STR
  rw [div_lt_iff₀ (by positivity)]
  nlinarith

theorem zOf_qRim_STR (τ : ℝ) : zOf_STR (qRim_STR τ) = zRim_STR τ :=
  zOf_qOf_STR rr_pos_STR _

/-- The rim vector in the plane model. -/
def rimVec_STR (τ : ℝ) : EuclideanSpace ℝ (Fin 2) := modelPlaneComplex.symm (qRim_STR τ)

theorem norm_rimVec_STR (τ : ℝ) : ‖rimVec_STR τ‖ = rr_STR := by
  rw [rimVec_STR, LinearIsometryEquiv.norm_map, norm_qRim_STR]

theorem contDiff_rimVec_STR : ContDiff ℝ ∞ rimVec_STR := by
  have hZ : ContDiff ℝ ∞ zRim_STR := by
    unfold zRim_STR
    exact (contDiff_const.sub (contDiff_const.mul contDiff_id)).mul contDiff_const
  have hd : ContDiff ℝ ∞ fun τ => zRim_STR τ ^ 2 + 1 := (hZ.pow 2).add contDiff_const
  have hne : ∀ τ, zRim_STR τ ^ 2 + 1 ≠ 0 := fun τ => by positivity
  have h1 : ContDiff ℝ ∞ fun τ => rr_STR * (zRim_STR τ ^ 2 - 1) / (zRim_STR τ ^ 2 + 1) :=
    (contDiff_const.mul ((hZ.pow 2).sub contDiff_const)).div hd hne
  have h2 : ContDiff ℝ ∞ fun τ => 2 * rr_STR * zRim_STR τ / (zRim_STR τ ^ 2 + 1) :=
    (contDiff_const.mul hZ).div hd hne
  have hq : ContDiff ℝ ∞ qRim_STR := by
    have h := Complex.equivRealProdCLM.symm.contDiff.comp (h1.prodMk h2)
    convert h using 1
    funext τ
    apply Complex.ext <;> simp [qRim_STR, qOf_STR]
  exact modelPlaneComplex.symm.contDiff.comp hq

/-- The rim point of the circle base over `τ`. -/
def rimPoint_STR (τ : ℝ) : X135Radial.radialCircleBase :=
  ⟨⟨rimVec_STR τ, by
    change ‖rimVec_STR τ‖ < 1
    rw [norm_rimVec_STR]
    exact rr_lt_one_STR⟩, by
    change (1 / 2 : ℝ) < ‖rimVec_STR τ‖ ^ 2
    rw [norm_rimVec_STR, rr_sq_STR]
    norm_num⟩

theorem qOfBase_rimPoint_STR (τ : ℝ) : qOfBase_STR (rimPoint_STR τ) = qRim_STR τ :=
  modelPlaneComplex.apply_symm_apply _

theorem contMDiff_rimPoint_STR :
    ContMDiff 𝓘(ℝ, ℝ) (𝓡 2) ∞ rimPoint_STR := by
  have h : ContMDiff 𝓘(ℝ, ℝ) (𝓡 2) ∞
      (Subtype.val ∘ Subtype.val ∘ rimPoint_STR :
        ℝ → EuclideanSpace ℝ (Fin 2)) :=
    contDiff_rimVec_STR.contMDiff
  exact (contMDiff_subtypeVal_comp_iff X135Radial.radialCircleBase rimPoint_STR).mp
    ((contMDiff_subtypeVal_comp_iff loopCircleBase (Subtype.val ∘ rimPoint_STR)).mp h)

end GC.GraphManifold.Assembly.FC39P0.SolidTorusSTR
