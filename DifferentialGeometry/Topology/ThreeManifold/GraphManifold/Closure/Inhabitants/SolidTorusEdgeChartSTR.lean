import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.SolidTorusBallChartSTI

/-!
# S-SOLIDTORUS2 (suffix `_STR`), G2 part 1: the edge handle chart

The edge handle of the solid torus instance is the image of `D² × I` under the algebraic chart
`(ζ, t) ↦ (z₁, z₂)`, `z₁ = ζ/4`, `r = √(1 - |ζ|²/16)`, `Z = (1 - 2t) c(r)`,
`c(r) = √((r + κ)/(r - κ))`, `z₂ = r ((Z² - 1) + 2iZ)/(Z² + 1)` (`κ = 4/5`). Its inverse is
`ζ = 4 z₁`, `t = (1 - Z(z₂)/c(|z₂|))/2` with `Z(q) = Im q/(|q| - Re q)`. The chart is a partial
diffeomorphism from `{|ζ|² < 4} ⊆ ℝ³` onto `{‖z₁‖² < 1/4, Re z₂ < ‖z₂‖} ⊆ S³`. The fibre over `t`
is a graph over `|q|` in the `q`-plane (the curve `Z = (1 - 2t) c(|q|)`), the end fibres `t = 0, 1`
lie in the cap boundary `Re z₂ = κ`, and `4 t (1 - t) = 2r(κ - u)/((r - u)(r + κ))` (`u = Re q`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0.SolidTorusSTR

/-- The cap level `κ = 4/5`. -/
def kap_STR : ℝ := 4 / 5

/-- `c(r) = √((r+κ)/(r-κ))`. -/
def cR_STR (r : ℝ) : ℝ := √((r + kap_STR) / (r - kap_STR))

/-- `Z(q) = Im q / (|q| - Re q)`. -/
def zOf_STR (q : ℂ) : ℝ := q.im / (‖q‖ - q.re)

/-- The edge coordinate `t(q) = (1 - Z(q)/c(|q|))/2`. -/
def tOf_STR (q : ℂ) : ℝ := (1 - zOf_STR q / cR_STR ‖q‖) / 2

/-- The point `r ((Z²-1) + 2iZ)/(Z²+1)`. -/
def qOf_STR (r Z : ℝ) : ℂ := ⟨r * (Z ^ 2 - 1) / (Z ^ 2 + 1), 2 * r * Z / (Z ^ 2 + 1)⟩

theorem qOf_re_STR (r Z : ℝ) : (qOf_STR r Z).re = r * (Z ^ 2 - 1) / (Z ^ 2 + 1) := rfl

theorem qOf_im_STR (r Z : ℝ) : (qOf_STR r Z).im = 2 * r * Z / (Z ^ 2 + 1) := rfl

theorem norm_sq_qOf_STR (r Z : ℝ) : ‖qOf_STR r Z‖ ^ 2 = r ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, qOf_re_STR, qOf_im_STR]
  have h : Z ^ 2 + 1 ≠ 0 := by positivity
  field_simp
  ring

theorem norm_qOf_STR {r : ℝ} (hr : 0 ≤ r) (Z : ℝ) : ‖qOf_STR r Z‖ = r := by
  have h := norm_sq_qOf_STR r Z
  have h0 := norm_nonneg (qOf_STR r Z)
  nlinarith [sq_nonneg (‖qOf_STR r Z‖ - r), sq_nonneg (‖qOf_STR r Z‖ + r)]

theorem zOf_qOf_STR {r : ℝ} (hr : 0 < r) (Z : ℝ) : zOf_STR (qOf_STR r Z) = Z := by
  rw [zOf_STR, norm_qOf_STR hr.le, qOf_re_STR, qOf_im_STR]
  have h : Z ^ 2 + 1 ≠ 0 := by positivity
  have h2 : r - r * (Z ^ 2 - 1) / (Z ^ 2 + 1) = 2 * r / (Z ^ 2 + 1) := by
    field_simp
    ring
  rw [h2]
  field_simp

theorem qOf_zOf_STR {q : ℂ} (hq : q.re < ‖q‖) : qOf_STR ‖q‖ (zOf_STR q) = q := by
  have hpos : 0 < ‖q‖ - q.re := sub_pos.mpr hq
  have hr : 0 < ‖q‖ := by
    have h1 := Complex.abs_re_le_norm q
    have h2 := neg_abs_le q.re
    linarith
  have hsq : ‖q‖ ^ 2 = q.re ^ 2 + q.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hZ : zOf_STR q ^ 2 + 1 = 2 * ‖q‖ / (‖q‖ - q.re) := by
    rw [zOf_STR]
    field_simp
    nlinarith [hsq]
  have hZ2 : zOf_STR q ^ 2 - 1 = 2 * q.re / (‖q‖ - q.re) := by
    rw [zOf_STR]
    field_simp
    nlinarith [hsq]
  apply Complex.ext
  · rw [qOf_re_STR, hZ, hZ2]
    field_simp
  · rw [qOf_im_STR, hZ, zOf_STR]
    field_simp


/-! ## The edge handle coordinates -/

open GC.GraphManifold.Assembly.FC39P0.SolidTorusSTI

/-- `ρ₂(x) = x₀² + x₁²` (the squared modulus of the disk coordinate `ζ`). -/
def rho2_STR (x : EuclideanSpace ℝ (Fin 3)) : ℝ := x 0 ^ 2 + x 1 ^ 2

/-- `r(x) = √(1 - ρ₂/16)` (the modulus of `z₂`). -/
def rOf_STR (x : EuclideanSpace ℝ (Fin 3)) : ℝ := √(1 - rho2_STR x / 16)

/-- `Z(x) = (1 - 2 x₂) c(r)`. -/
def zFwd_STR (x : EuclideanSpace ℝ (Fin 3)) : ℝ := (1 - 2 * x 2) * cR_STR (rOf_STR x)

/-- `z₁ = (x₀ + i x₁)/4`. -/
def edgeFirst_STR (x : EuclideanSpace ℝ (Fin 3)) : ℂ := ⟨x 0 / 4, x 1 / 4⟩

/-- `z₂ = q(r, Z)`. -/
def edgeSecond_STR (x : EuclideanSpace ℝ (Fin 3)) : ℂ := qOf_STR (rOf_STR x) (zFwd_STR x)

theorem kap_lt_rOf_STR {x : EuclideanSpace ℝ (Fin 3)} (hx : rho2_STR x < 4) :
    kap_STR < rOf_STR x := by
  rw [rOf_STR, kap_STR]
  apply Real.lt_sqrt_of_sq_lt
  nlinarith

theorem rOf_pos_STR {x : EuclideanSpace ℝ (Fin 3)} (hx : rho2_STR x < 4) : 0 < rOf_STR x :=
  lt_trans (by norm_num [kap_STR]) (kap_lt_rOf_STR hx)

theorem rOf_sq_STR {x : EuclideanSpace ℝ (Fin 3)} (hx : rho2_STR x < 4) :
    rOf_STR x ^ 2 = 1 - rho2_STR x / 16 := by
  rw [rOf_STR]
  exact Real.sq_sqrt (by nlinarith)

theorem cR_sq_STR {r : ℝ} (hr : kap_STR < r) : cR_STR r ^ 2 = (r + kap_STR) / (r - kap_STR) := by
  rw [cR_STR]
  apply Real.sq_sqrt
  have h1 : 0 < r - kap_STR := sub_pos.mpr hr
  have h2 : 0 < r + kap_STR := by
    have : 0 < kap_STR := by norm_num [kap_STR]
    linarith
  positivity

theorem cR_pos_STR {r : ℝ} (hr : kap_STR < r) : 0 < cR_STR r := by
  rw [cR_STR]
  apply Real.sqrt_pos.mpr
  have h1 : 0 < r - kap_STR := sub_pos.mpr hr
  have h2 : 0 < r + kap_STR := by
    have : 0 < kap_STR := by norm_num [kap_STR]
    linarith
  positivity

theorem edge_norm_STR {x : EuclideanSpace ℝ (Fin 3)} (hx : rho2_STR x < 4) :
    ‖edgeFirst_STR x‖ ^ 2 + ‖edgeSecond_STR x‖ ^ 2 = 1 := by
  have h1 : ‖edgeFirst_STR x‖ ^ 2 = rho2_STR x / 16 := by
    rw [Complex.sq_norm, Complex.normSq_apply, rho2_STR]
    simp only [edgeFirst_STR]
    ring
  have h2 : ‖edgeSecond_STR x‖ ^ 2 = 1 - rho2_STR x / 16 := by
    rw [edgeSecond_STR, norm_qOf_STR (rOf_pos_STR hx).le, rOf_sq_STR hx]
  rw [h1, h2]
  ring


/-- The edge chart map `(ζ, t) ↦ (z₁, z₂)` (default point off the source). -/
def edgeMap_STR (x : EuclideanSpace ℝ (Fin 3)) : SphereCarrier.{0} :=
  if h : rho2_STR x < 4 then sphereOfPair (edgeFirst_STR x) (edgeSecond_STR x) (edge_norm_STR h)
  else graphDefault_STI

theorem edgeMap_of_lt_STR {x : EuclideanSpace ℝ (Fin 3)} (h : rho2_STR x < 4) :
    edgeMap_STR x = sphereOfPair (edgeFirst_STR x) (edgeSecond_STR x) (edge_norm_STR h) := by
  unfold edgeMap_STR
  split_ifs with h'
  · rfl
  · exact absurd h h'

theorem sphereFirst_edgeMap_STR {x : EuclideanSpace ℝ (Fin 3)} (h : rho2_STR x < 4) :
    sphereFirst (edgeMap_STR x) = edgeFirst_STR x := by
  rw [edgeMap_of_lt_STR h, sphereFirst_sphereOfPair]

theorem sphereSecond_edgeMap_STR {x : EuclideanSpace ℝ (Fin 3)} (h : rho2_STR x < 4) :
    sphereSecond (edgeMap_STR x) = edgeSecond_STR x := by
  rw [edgeMap_of_lt_STR h, sphereSecond_sphereOfPair]

/-- The inverse of the edge chart. -/
def edgeInv_STR (p : SphereCarrier.{0}) : EuclideanSpace ℝ (Fin 3) :=
  ofCoords_STI (4 * (sphereFirst p).re) (4 * (sphereFirst p).im) (tOf_STR (sphereSecond p))

/-- The target of the edge chart: `{‖z₁‖² < 1/4, Re z₂ < ‖z₂‖}`. -/
def edgeTarget_STR : Set SphereCarrier.{0} :=
  {p | ‖sphereFirst p‖ ^ 2 < 1 / 4 ∧ (sphereSecond p).re < ‖sphereSecond p‖}

theorem rho2_edgeInv_STR (p : SphereCarrier.{0}) :
    rho2_STR (edgeInv_STR p) = 16 * ‖sphereFirst p‖ ^ 2 := by
  rw [rho2_STR, Complex.sq_norm, Complex.normSq_apply]
  simp only [edgeInv_STR, ofCoords_zero_STI, ofCoords_one_STI]
  ring

theorem kap_lt_norm_second_STR {p : SphereCarrier.{0}} (hp : p ∈ edgeTarget_STR) :
    kap_STR < ‖sphereSecond p‖ := by
  have h := norm_sphereFirst_sq_add p
  have h0 := norm_nonneg (sphereSecond p)
  rw [kap_STR]
  nlinarith [hp.1]

theorem norm_second_pos_STR {p : SphereCarrier.{0}} (hp : p ∈ edgeTarget_STR) :
    0 < ‖sphereSecond p‖ :=
  lt_trans (by norm_num [kap_STR]) (kap_lt_norm_second_STR hp)

theorem edgeMap_mem_target_STR {x : EuclideanSpace ℝ (Fin 3)} (hx : rho2_STR x < 4) :
    edgeMap_STR x ∈ edgeTarget_STR := by
  have hr := rOf_pos_STR hx
  refine ⟨?_, ?_⟩
  · rw [sphereFirst_edgeMap_STR hx]
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [edgeFirst_STR]
    rw [rho2_STR] at hx
    nlinarith
  · rw [sphereSecond_edgeMap_STR hx, edgeSecond_STR, norm_qOf_STR hr.le, qOf_re_STR]
    have h : (0 : ℝ) < zFwd_STR x ^ 2 + 1 := by positivity
    rw [div_lt_iff₀ h]
    nlinarith [sq_nonneg (zFwd_STR x)]

theorem tOf_edgeSecond_STR {x : EuclideanSpace ℝ (Fin 3)} (hx : rho2_STR x < 4) :
    tOf_STR (edgeSecond_STR x) = x 2 := by
  have hr := rOf_pos_STR hx
  have hc := cR_pos_STR (kap_lt_rOf_STR hx)
  rw [tOf_STR, edgeSecond_STR, zOf_qOf_STR hr, norm_qOf_STR hr.le, zFwd_STR]
  field_simp
  ring

theorem edgeInv_edgeMap_STR {x : EuclideanSpace ℝ (Fin 3)} (hx : rho2_STR x < 4) :
    edgeInv_STR (edgeMap_STR x) = x := by
  have h0 : edgeInv_STR (edgeMap_STR x) 0 = x 0 := by
    simp only [edgeInv_STR, ofCoords_zero_STI, sphereFirst_edgeMap_STR hx, edgeFirst_STR]
    ring
  have h1 : edgeInv_STR (edgeMap_STR x) 1 = x 1 := by
    simp only [edgeInv_STR, ofCoords_one_STI, sphereFirst_edgeMap_STR hx, edgeFirst_STR]
    ring
  have h2 : edgeInv_STR (edgeMap_STR x) 2 = x 2 := by
    simp only [edgeInv_STR, ofCoords_two_STI, sphereSecond_edgeMap_STR hx]
    exact tOf_edgeSecond_STR hx
  ext i
  fin_cases i
  exacts [h0, h1, h2]

theorem rho2_lt_of_target_STR {p : SphereCarrier.{0}} (hp : p ∈ edgeTarget_STR) :
    rho2_STR (edgeInv_STR p) < 4 := by
  rw [rho2_edgeInv_STR]
  linarith [hp.1]

theorem edgeMap_edgeInv_STR {p : SphereCarrier.{0}} (hp : p ∈ edgeTarget_STR) :
    edgeMap_STR (edgeInv_STR p) = p := by
  have hlt := rho2_lt_of_target_STR hp
  have hn := norm_sphereFirst_sq_add p
  have hrq := kap_lt_norm_second_STR hp
  have hrOf : rOf_STR (edgeInv_STR p) = ‖sphereSecond p‖ := by
    rw [rOf_STR, rho2_edgeInv_STR]
    have : 1 - 16 * ‖sphereFirst p‖ ^ 2 / 16 = ‖sphereSecond p‖ ^ 2 := by linarith
    rw [this]
    exact Real.sqrt_sq (norm_nonneg _)
  have hc := cR_pos_STR hrq
  have hzf : zFwd_STR (edgeInv_STR p) = zOf_STR (sphereSecond p) := by
    rw [zFwd_STR, hrOf]
    simp only [edgeInv_STR, ofCoords_two_STI, tOf_STR]
    field_simp
    ring
  apply sphere_ext
  · rw [sphereFirst_edgeMap_STR hlt]
    apply Complex.ext <;> simp [edgeFirst_STR, edgeInv_STR]
  · rw [sphereSecond_edgeMap_STR hlt, edgeSecond_STR, hrOf, hzf]
    exact qOf_zOf_STR hp.2


/-! ## Smoothness -/

theorem contDiff_coord_STR (i : Fin 3) :
    ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin 3) => x i) :=
  (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ).contDiff

theorem contDiff_rho2_STR : ContDiff ℝ ∞ rho2_STR := by
  unfold rho2_STR
  exact ((contDiff_coord_STR 0).pow 2).add ((contDiff_coord_STR 1).pow 2)

theorem contDiffAt_rOf_STR {x : EuclideanSpace ℝ (Fin 3)} (hx : rho2_STR x < 4) :
    ContDiffAt ℝ ∞ rOf_STR x := by
  have hpos : 0 < 1 - rho2_STR x / 16 := by linarith
  have hin : ContDiffAt ℝ ∞ (fun x : EuclideanSpace ℝ (Fin 3) => 1 - rho2_STR x / 16) x :=
    (contDiff_const.sub (contDiff_rho2_STR.div_const 16)).contDiffAt
  exact (Real.contDiffAt_sqrt hpos.ne').comp x hin

theorem contDiffAt_cR_STR {r : ℝ} (hr : kap_STR < r) : ContDiffAt ℝ ∞ cR_STR r := by
  have h1 : 0 < r - kap_STR := sub_pos.mpr hr
  have h2 : 0 < r + kap_STR := by
    have : 0 < kap_STR := by norm_num [kap_STR]
    linarith
  have hin : ContDiffAt ℝ ∞ (fun r : ℝ => (r + kap_STR) / (r - kap_STR)) r :=
    ((contDiff_id.add contDiff_const).contDiffAt).div
      ((contDiff_id.sub contDiff_const).contDiffAt) h1.ne'
  exact (Real.contDiffAt_sqrt (div_pos h2 h1).ne').comp r hin

theorem contDiffAt_zFwd_STR {x : EuclideanSpace ℝ (Fin 3)} (hx : rho2_STR x < 4) :
    ContDiffAt ℝ ∞ zFwd_STR x := by
  unfold zFwd_STR
  exact (contDiff_const.sub (contDiff_const.mul (contDiff_coord_STR 2))).contDiffAt.mul
    ((contDiffAt_cR_STR (kap_lt_rOf_STR hx)).comp x (contDiffAt_rOf_STR hx))

theorem contDiffAt_qOf_STR {f g : EuclideanSpace ℝ (Fin 3) → ℝ} {x : EuclideanSpace ℝ (Fin 3)}
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x) :
    ContDiffAt ℝ ∞ (fun y => qOf_STR (f y) (g y)) x := by
  have h : (fun y => qOf_STR (f y) (g y)) = fun y =>
      (f y * (g y ^ 2 - 1) / (g y ^ 2 + 1) : ℝ) • (1 : ℂ) +
        (2 * f y * g y / (g y ^ 2 + 1) : ℝ) • Complex.I := by
    funext y
    apply Complex.ext <;> simp only [qOf_STR, Complex.add_re, Complex.add_im, Complex.smul_re,
      Complex.smul_im, Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im, smul_eq_mul] <;>
      ring
  rw [h]
  have hd : ContDiffAt ℝ ∞ (fun y => g y ^ 2 + 1) x := (hg.pow 2).add contDiffAt_const
  have hne : g x ^ 2 + 1 ≠ 0 := by positivity
  exact (((hf.mul ((hg.pow 2).sub contDiffAt_const)).div hd hne).smul contDiffAt_const).add
    ((((contDiffAt_const.mul hf).mul hg).div hd hne).smul contDiffAt_const)

theorem contDiffAt_edgeSecond_STR {x : EuclideanSpace ℝ (Fin 3)} (hx : rho2_STR x < 4) :
    ContDiffAt ℝ ∞ edgeSecond_STR x :=
  contDiffAt_qOf_STR (contDiffAt_rOf_STR hx) (contDiffAt_zFwd_STR hx)

theorem contDiff_edgeFirst_STR : ContDiff ℝ ∞ edgeFirst_STR := by
  have h : edgeFirst_STR = fun x => ((x 0 / 4 : ℝ)) • (1 : ℂ) + ((x 1 / 4 : ℝ)) • Complex.I := by
    funext x
    apply Complex.ext <;> simp [edgeFirst_STR]
  rw [h]
  exact (((contDiff_coord_STR 0).div_const 4).smul contDiff_const).add
    (((contDiff_coord_STR 1).div_const 4).smul contDiff_const)

theorem contDiffAt_tOf_STR {q : ℂ} (hq : kap_STR < ‖q‖) (hre : q.re < ‖q‖) :
    ContDiffAt ℝ ∞ tOf_STR q := by
  have hq0 : q ≠ 0 := by
    intro h
    rw [h, norm_zero] at hq
    norm_num [kap_STR] at hq
  have hn : ContDiffAt ℝ ∞ (fun q : ℂ => ‖q‖) q := contDiffAt_norm ℝ hq0
  have hz : ContDiffAt ℝ ∞ zOf_STR q := by
    unfold zOf_STR
    exact (Complex.imCLM.contDiff.contDiffAt).div
      (hn.sub Complex.reCLM.contDiff.contDiffAt) (sub_pos.mpr hre).ne'
  have hc : ContDiffAt ℝ ∞ (fun q : ℂ => cR_STR ‖q‖) q := (contDiffAt_cR_STR hq).comp q hn
  unfold tOf_STR
  exact (contDiffAt_const.sub (hz.div hc (cR_pos_STR hq).ne')).div_const 2

theorem isOpen_edgeTarget_STR : IsOpen edgeTarget_STR := by
  have h1 : IsOpen {p : SphereCarrier.{0} | ‖sphereFirst p‖ ^ 2 < 1 / 4} :=
    isOpen_lt ((continuous_norm.comp contMDiff_sphereFirst.continuous).pow 2) continuous_const
  have h2 : IsOpen {p : SphereCarrier.{0} | (sphereSecond p).re < ‖sphereSecond p‖} :=
    isOpen_lt (Complex.continuous_re.comp contMDiff_sphereSecond.continuous)
      (continuous_norm.comp contMDiff_sphereSecond.continuous)
  exact h1.inter h2

theorem isOpen_edgeSource_STR : IsOpen {x : EuclideanSpace ℝ (Fin 3) | rho2_STR x < 4} :=
  isOpen_lt contDiff_rho2_STR.continuous continuous_const

theorem contMDiffOn_edgeMap_STR :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ edgeMap_STR {x : EuclideanSpace ℝ (Fin 3) | rho2_STR x < 4} := by
  refine contMDiffOn_of_sphereFirst_sphereSecond isOpen_edgeSource_STR ?_ ?_
  · refine (contDiff_edgeFirst_STR.contMDiff.contMDiffOn).congr ?_
    intro x hx
    exact sphereFirst_edgeMap_STR hx
  · have hS : ContDiffOn ℝ ∞ edgeSecond_STR
        {x : EuclideanSpace ℝ (Fin 3) | rho2_STR x < 4} :=
      fun x hx => (contDiffAt_edgeSecond_STR hx).contDiffWithinAt
    refine hS.contMDiffOn.congr ?_
    intro x hx
    exact sphereSecond_edgeMap_STR hx

theorem contMDiffOn_edgeInv_STR :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ edgeInv_STR edgeTarget_STR := by
  have hre : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (fun p : SphereCarrier.{0} => 4 * (sphereFirst p).re) :=
    contMDiff_const.mul (Complex.reCLM.contDiff.contMDiff.comp contMDiff_sphereFirst)
  have him : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (fun p : SphereCarrier.{0} => 4 * (sphereFirst p).im) :=
    contMDiff_const.mul (Complex.imCLM.contDiff.contMDiff.comp contMDiff_sphereFirst)
  have ht : ContMDiffOn (𝓡 3) 𝓘(ℝ, ℝ) ∞ (fun p : SphereCarrier.{0} => tOf_STR (sphereSecond p))
      edgeTarget_STR := by
    have hQ : ContDiffOn ℝ ∞ tOf_STR {q : ℂ | kap_STR < ‖q‖ ∧ q.re < ‖q‖} :=
      fun q hq => (contDiffAt_tOf_STR hq.1 hq.2).contDiffWithinAt
    exact hQ.contMDiffOn.comp contMDiff_sphereSecond.contMDiffOn
      (fun p hp => ⟨kap_lt_norm_second_STR hp, hp.2⟩)
  exact contDiff_ofCoords_STI.contMDiff.comp_contMDiffOn
    (hre.contMDiffOn.prodMk_space (him.contMDiffOn.prodMk_space ht))

/-- **The edge chart**: a partial diffeomorphism from `{x₀² + x₁² < 4} ⊆ ℝ³` onto
`{‖z₁‖² < 1/4, Re z₂ < ‖z₂‖} ⊆ S³`. -/
def edgeChart_STR :
    PartialDiffeomorph (𝓡 3) (𝓡 3) (EuclideanSpace ℝ (Fin 3)) SphereCarrier.{0} ∞ where
  toFun := edgeMap_STR
  invFun := edgeInv_STR
  source := {x | rho2_STR x < 4}
  target := edgeTarget_STR
  map_source' := fun _ hx => edgeMap_mem_target_STR hx
  map_target' := fun _ hp => rho2_lt_of_target_STR hp
  left_inv' := fun _ hx => edgeInv_edgeMap_STR hx
  right_inv' := fun _ hp => edgeMap_edgeInv_STR hp
  open_source := isOpen_edgeSource_STR
  open_target := isOpen_edgeTarget_STR
  contMDiffOn_toFun := contMDiffOn_edgeMap_STR
  contMDiffOn_invFun := contMDiffOn_edgeInv_STR

end GC.GraphManifold.Assembly.FC39P0.SolidTorusSTR
