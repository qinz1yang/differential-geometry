import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveSplitCappedCharts

/-!
# Model maps of the split tube

Lane N2c, tier 1 (models). The three model maps of the split tube from `S² × ℝ`:
`capModel e s` (meridian disc of radius `6 |x₁ + i x₂|` at the fibre angle `tubeFibre e s h`),
`bandModel` (the host point `hostChart l (strip l (bandHeight l x₃ / angleScale h, h))` and the
fibre `u^{e₁} · exp (i e d · smoothSign x₃ · hostTheta h)`) and `seamModel e s` (seam coordinates
`((u, tubeFibre e s h), seamHeight x₃)`), and their local diffeomorphism property, assembled from
the hemisphere and band charts, the explicit diffeomorphisms `bandScaleDiffeo`, `stripDiffeo`
and `shearDiffeo`, the inversion chart `invChart` and the one-dimensional inverse function
theorem for `bandHeight` and `seamHeight`.
-/

set_option autoImplicit false

noncomputable section
open Set Filter Function Metric
open scoped Manifold ContDiff Topology

open DifferentialGeometry.Topology.Manifold
  (isLocalDiffeomorphAt_of_contMDiffOn_of_hasMFDerivAt_equiv)

namespace GC.Seifert.SplitTube

local notation "S2" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

abbrev PlaneModel := (𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))

theorem contDiff_angleScale : ContDiff ℝ ∞ angleScale := by
  rw [contDiff_iff_contDiffAt]
  intro h
  exact (contDiffAt_const.add ((contDiffAt_const.mul contDiffAt_id).pow 2)).sqrt
    (by simp only [id]; positivity)

theorem contMDiff_real_comp {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContMDiff PlaneModel 𝓘(ℝ, ℝ) ∞ f := by
  have h : ContMDiff PlaneModel 𝓘(ℝ, ℝ × ℝ) ∞ (fun q : ℝ × ℝ => q) :=
    contMDiff_fst.prodMk_space contMDiff_snd
  exact hf.contMDiff.comp h

def bandScaleDiffeo : (ℝ × ℝ) ≃ₘ⟮PlaneModel, PlaneModel⟯ (ℝ × ℝ) where
  toFun q := (q.1 / angleScale q.2, q.2)
  invFun q := (q.1 * angleScale q.2, q.2)
  left_inv q := by
    simp only
    rw [div_mul_cancel₀ _ (angleScale_pos q.2).ne']
  right_inv q := by
    simp only
    rw [mul_div_cancel_right₀ _ (angleScale_pos q.2).ne']
  contMDiff_toFun := by
    refine ContMDiff.prodMk ?_ contMDiff_snd
    exact contMDiff_real_comp (contDiff_fst.div (contDiff_angleScale.comp contDiff_snd)
      fun q => (angleScale_pos q.2).ne')
  contMDiff_invFun := by
    refine ContMDiff.prodMk ?_ contMDiff_snd
    exact contMDiff_real_comp (contDiff_fst.mul (contDiff_angleScale.comp contDiff_snd))

theorem contDiff_complex_mk {f g : ℝ × ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (fun q => (⟨f q, g q⟩ : ℂ)) := by
  have h : (fun q => (⟨f q, g q⟩ : ℂ)) =
      fun q => ((f q : ℝ) : ℂ) + ((g q : ℝ) : ℂ) * Complex.I := by
    funext q
    apply Complex.ext <;> simp
  rw [h]
  exact (Complex.ofRealCLM.contDiff.comp hf).add
    ((Complex.ofRealCLM.contDiff.comp hg).mul contDiff_const)

def stripInv (l : Fin 3) (w : ℂ) : ℝ × ℝ :=
  (w.im, (stripCenter l * stripBump w.im - w.re) / (tubeSlope * stripWidth w.im))

theorem tubeSlope_mul_stripWidth_ne (Y : ℝ) : tubeSlope * stripWidth Y ≠ 0 :=
  mul_ne_zero (by norm_num [tubeSlope]) (stripWidth_pos Y).ne'

def stripDiffeo (l : Fin 3) : (ℝ × ℝ) ≃ₘ⟮PlaneModel, 𝓘(ℝ, ℂ)⟯ ℂ where
  toFun := strip l
  invFun := stripInv l
  left_inv q := by
    have h1 : tubeSlope ≠ 0 := by norm_num [tubeSlope]
    have h2 := (stripWidth_pos q.1).ne'
    simp only [stripInv, strip]
    refine Prod.ext rfl ?_
    field_simp
    ring
  right_inv w := by
    have h1 : tubeSlope ≠ 0 := by norm_num [tubeSlope]
    have h2 := (stripWidth_pos w.im).ne'
    apply Complex.ext
    · simp only [strip, stripInv]
      field_simp
      ring
    · rfl
  contMDiff_toFun := by
    have h : ContDiff ℝ ∞ (strip l) := contDiff_complex_mk
      (((contDiff_const.mul contDiff_snd).neg.mul (contDiff_stripWidth.comp contDiff_fst)).add
        (contDiff_const.mul (contDiff_stripBump.comp contDiff_fst))) contDiff_fst
    have h2 : ContMDiff PlaneModel 𝓘(ℝ, ℝ × ℝ) ∞ (fun q : ℝ × ℝ => q) :=
      contMDiff_fst.prodMk_space contMDiff_snd
    exact h.contMDiff.comp h2
  contMDiff_invFun := by
    have him : ContDiff ℝ ∞ (fun w : ℂ => w.im) := Complex.imCLM.contDiff
    have hre : ContDiff ℝ ∞ (fun w : ℂ => w.re) := Complex.reCLM.contDiff
    refine ContMDiff.prodMk him.contMDiff ?_
    refine ContDiff.contMDiff ?_
    exact ((contDiff_const.mul (contDiff_stripBump.comp him)).sub hre).div
      (contDiff_const.mul (contDiff_stripWidth.comp him))
      fun w => tubeSlope_mul_stripWidth_ne w.im

def invChart (c : ℝ) : PartialDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ ∞ where
  toFun w := (c : ℂ) + w⁻¹
  invFun z := (z - c)⁻¹
  source := {w | w ≠ 0}
  target := {z | z ≠ c}
  map_source' := by
    intro w hw h
    simp only [add_eq_left, inv_eq_zero] at h
    exact hw h
  map_target' := by
    intro z hz
    exact inv_ne_zero (sub_ne_zero.mpr hz)
  left_inv' := by
    intro w _
    simp
  right_inv' := by
    intro z _
    simp
  open_source := isOpen_ne
  open_target := isOpen_ne
  contMDiffOn_toFun := by
    intro w hw
    exact ((contDiffAt_const.add ((contDiffAt_inv ℂ hw).restrict_scalars ℝ)).contMDiffAt
      ).contMDiffWithinAt
  contMDiffOn_invFun := by
    intro z hz
    have hz' : z - (c : ℂ) ≠ 0 := sub_ne_zero.mpr hz
    exact (((contDiffAt_inv ℂ hz').restrict_scalars ℝ).comp z
      (contDiffAt_id.sub contDiffAt_const)).contMDiffAt.contMDiffWithinAt

theorem hostChart_eq_invChart {l : Fin 3} (hl : l.val ≠ 0) :
    hostChart l = invChart (planarCenter 3 l) := by
  funext w
  simp [hostChart, hl, invChart]

theorem isLocalDiffeomorphAt_hostChart (l : Fin 3) {w : ℂ} (hw : l.val ≠ 0 → w ≠ 0) :
    IsLocalDiffeomorphAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (hostChart l) w := by
  by_cases hl : l.val = 0
  · have h : hostChart l = id := by
      funext z
      simp [hostChart, hl]
    rw [h]
    exact (Diffeomorph.refl 𝓘(ℝ, ℂ) ℂ ∞).isLocalDiffeomorph w
  · rw [hostChart_eq_invChart hl]
    exact (invChart _).isLocalDiffeomorphAt _ _ ∞ (hw hl)

theorem hostChart_injOn (l : Fin 3) {w w' : ℂ} (hw : l.val ≠ 0 → w ≠ 0)
    (hw' : l.val ≠ 0 → w' ≠ 0) (h : hostChart l w = hostChart l w') : w = w' := by
  by_cases hl : l.val = 0
  · simpa [hostChart, hl] using h
  · rw [hostChart_eq_invChart hl] at h
    have h1 := (invChart (planarCenter 3 l)).left_inv (hw hl)
    have h2 := (invChart (planarCenter 3 l)).left_inv (hw' hl)
    change (invChart (planarCenter 3 l)) w = (invChart (planarCenter 3 l)) w' at h
    rw [← h1, ← h2, h]

theorem isLocalDiffeomorphAt_of_hasDerivAt {g : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hg : ∀ y ∈ U, ContDiffAt ℝ ∞ g y) {x d : ℝ} (hx : x ∈ U) (hd : HasDerivAt g d x)
    (h0 : d ≠ 0) : IsLocalDiffeomorphAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ g x := by
  let A : ℝ ≃L[ℝ] ℝ := ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 _ h0)
  refine isLocalDiffeomorphAt_of_contMDiffOn_of_hasMFDerivAt_equiv
    g (U := U) (fun y hy => (hg y hy).contMDiffAt.contMDiffWithinAt) hU x hx A ?_
  refine hd.hasFDerivAt.hasMFDerivAt.congr_mfderiv ?_
  ext
  simp [A, ContinuousLinearEquiv.unitsEquivAut_apply]

theorem hasDerivAt_seamHeight {x : ℝ} (hx : |x| < 1) :
    HasDerivAt seamHeight (4 * (-x / latRadius x)) x := by
  change HasDerivAt (fun y => 4 * latRadius y - 2) _ x
  exact ((hasDerivAt_latRadius hx).const_mul 4).sub_const 2

theorem isLocalDiffeomorphAt_seamHeight {x : ℝ} (hx : |x| < 1) (hx0 : x ≠ 0) :
    IsLocalDiffeomorphAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ seamHeight x := by
  refine isLocalDiffeomorphAt_of_hasDerivAt (U := {y : ℝ | |y| < 1})
    (isOpen_lt continuous_abs continuous_const) (fun y hy => ?_) hx (hasDerivAt_seamHeight hx) ?_
  · exact (contDiffAt_const.mul (contDiffAt_latRadius hy)).sub contDiffAt_const
  · have := latRadius_pos hx
    apply mul_ne_zero (by norm_num)
    exact div_ne_zero (neg_ne_zero.mpr hx0) this.ne'

theorem contMDiff_circle_zpow {e : ℤ} (he : e = 1 ∨ e = -1) :
    ContMDiff (𝓡 1) (𝓡 1) ∞ (fun u : Circle => u ^ e) := by
  rcases he with rfl | rfl
  · simp only [zpow_one]
    exact contMDiff_id
  · simp only [zpow_neg, zpow_one]
    exact contMDiff_inv (𝓡 1) ∞

theorem zpow_zpow_unit {e : ℤ} (he : e = 1 ∨ e = -1) (u : Circle) : (u ^ e) ^ e = u := by
  rw [← zpow_mul]
  rcases he with rfl | rfl <;> simp

def bandPhase (e d : ℤ) (x h : ℝ) : Circle :=
  Circle.exp (e * d * smoothSign x * hostTheta h)

theorem contMDiff_bandPhase_comp {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    (e d : ℤ) {f g : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hg : ContMDiff I 𝓘(ℝ, ℝ) ∞ g) :
    ContMDiff I (𝓡 1) ∞ (fun x => bandPhase e d (f x) (g x)) :=
  contMDiff_circleExp.comp ((contMDiff_const.mul (contDiff_smoothSign.contMDiff.comp hf)).mul
    (contDiff_hostTheta.contMDiff.comp hg))

abbrev BandModel := ((𝓘(ℝ, ℝ)).prod (𝓡 1)).prod (𝓘(ℝ, ℝ))

def shearDiffeo (e₀ e₁ d : ℤ) (he₁ : e₁ = 1 ∨ e₁ = -1) :
    ((ℝ × Circle) × ℝ) ≃ₘ⟮BandModel, PlaneModel.prod (𝓡 1)⟯ ((ℝ × ℝ) × Circle) where
  toFun q := ((q.1.1, q.2), q.1.2 ^ e₁ * bandPhase e₀ d q.1.1 q.2)
  invFun q := ((q.1.1, (q.2 * (bandPhase e₀ d q.1.1 q.1.2)⁻¹) ^ e₁), q.1.2)
  left_inv q := by
    simp only [mul_inv_cancel_right, zpow_zpow_unit he₁]
  right_inv q := by
    simp only [zpow_zpow_unit he₁, inv_mul_cancel_right]
  contMDiff_toFun := by
    change ContMDiff BandModel (PlaneModel.prod (𝓡 1)) ∞
      (fun q : (ℝ × Circle) × ℝ => ((q.1.1, q.2), q.1.2 ^ e₁ * bandPhase e₀ d q.1.1 q.2))
    have hx : ContMDiff BandModel 𝓘(ℝ, ℝ) ∞ (fun q : (ℝ × Circle) × ℝ => q.1.1) :=
      contMDiff_fst.comp contMDiff_fst
    have hpair : ContMDiff BandModel PlaneModel ∞ (fun q : (ℝ × Circle) × ℝ => (q.1.1, q.2)) :=
      hx.prodMk contMDiff_snd
    have hu : ContMDiff BandModel (𝓡 1) ∞ (fun q : (ℝ × Circle) × ℝ => q.1.2 ^ e₁) :=
      (contMDiff_circle_zpow he₁).comp (contMDiff_snd.comp contMDiff_fst)
    have hb : ContMDiff BandModel (𝓡 1) ∞
        (fun q : (ℝ × Circle) × ℝ => bandPhase e₀ d q.1.1 q.2) :=
      contMDiff_bandPhase_comp e₀ d hx contMDiff_snd
    exact hpair.prodMk (hu.mul hb)
  contMDiff_invFun := by
    change ContMDiff (PlaneModel.prod (𝓡 1)) BandModel ∞
      (fun q : (ℝ × ℝ) × Circle =>
        ((q.1.1, (q.2 * (bandPhase e₀ d q.1.1 q.1.2)⁻¹) ^ e₁), q.1.2))
    have hb : ContMDiff (PlaneModel.prod (𝓡 1)) (𝓡 1) ∞
        (fun q : (ℝ × ℝ) × Circle => bandPhase e₀ d q.1.1 q.1.2) :=
      contMDiff_bandPhase_comp e₀ d (contMDiff_fst.comp contMDiff_fst)
        (contMDiff_snd.comp contMDiff_fst)
    have hν : ContMDiff (PlaneModel.prod (𝓡 1)) (𝓡 1) ∞
        (fun q : (ℝ × ℝ) × Circle => (q.2 * (bandPhase e₀ d q.1.1 q.1.2)⁻¹) ^ e₁) :=
      (contMDiff_circle_zpow he₁).comp (contMDiff_snd.mul hb.inv)
    have hx : ContMDiff (PlaneModel.prod (𝓡 1)) 𝓘(ℝ, ℝ) ∞ (fun q : (ℝ × ℝ) × Circle => q.1.1) :=
      contMDiff_fst.comp contMDiff_fst
    have hh : ContMDiff (PlaneModel.prod (𝓡 1)) 𝓘(ℝ, ℝ) ∞ (fun q : (ℝ × ℝ) × Circle => q.1.2) :=
      contMDiff_snd.comp contMDiff_fst
    exact (hx.prodMk hν).prodMk hh

def scaleSix : ℂ ≃L[ℝ] ℂ :=
  (LinearEquiv.smulOfUnit (Units.mk0 (6 : ℝ) (by norm_num))).toContinuousLinearEquiv

theorem scaleSix_apply (z : ℂ) : scaleSix z = (6 : ℝ) • z := rfl

def capModel (e : ℤ) (s : Bool) (q : S2 × ℝ) : ℂ × Circle :=
  ((6 : ℝ) • planeOf q.1, tubeFibre e s q.2)

theorem isLocalDiffeomorphAt_capModel {e : ℤ} (he : e = 1 ∨ e = -1) (s : Bool) {q : S2 × ℝ}
    (hq : 0 < sgnR s * heightOf q.1) :
    IsLocalDiffeomorphAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℂ).prod (𝓡 1)) ∞ (capModel e s) q := by
  have h1 : IsLocalDiffeomorphAt (𝓡 2) 𝓘(ℝ, ℂ) ∞ (scaleSix ∘ planeOf) q.1 :=
    ((capChart s).isLocalDiffeomorphAt _ _ ∞ hq).comp 𝓘(ℝ, ℂ) ℂ
      (scaleSix.toDiffeomorph.isLocalDiffeomorph _)
  exact h1.prodMap (isLocalDiffeomorphAt_tubeFibre he s q.2)

def permDiffeo : ((ℝ × Circle) × ℝ) ≃ₘ⟮BandModel, ((𝓡 1).prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℝ)⟯
    ((Circle × ℝ) × ℝ) where
  toFun q := ((q.1.2, q.2), q.1.1)
  invFun q := ((q.2, q.1.1), q.1.2)
  left_inv _ := rfl
  right_inv _ := rfl
  contMDiff_toFun :=
    ((contMDiff_snd.comp contMDiff_fst).prodMk contMDiff_snd).prodMk
      (contMDiff_fst.comp contMDiff_fst)
  contMDiff_invFun :=
    (contMDiff_snd.prodMk (contMDiff_fst.comp contMDiff_fst)).prodMk
      (contMDiff_snd.comp contMDiff_fst)

def seamModel (e : ℤ) (s : Bool) (q : S2 × ℝ) : GC.Endpoint.Torus × ℝ :=
  ((GC.GraphManifold.unitOf (planeOf q.1), tubeFibre e s q.2), seamHeight (heightOf q.1))

theorem isLocalDiffeomorphAt_seamModel {e : ℤ} (he : e = 1 ∨ e = -1) (s : Bool) {q : S2 × ℝ}
    (hq : |heightOf q.1| < 1) (hq0 : heightOf q.1 ≠ 0) :
    IsLocalDiffeomorphAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) GC.Endpoint.signedCollarModel ∞
      (seamModel e s) q := by
  have h1 : IsLocalDiffeomorphAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) BandModel ∞ (Prod.map bandChart id) q :=
    (bandChart.isLocalDiffeomorphAt _ _ ∞ hq).prodMap
      ((Diffeomorph.refl 𝓘(ℝ, ℝ) ℝ ∞).isLocalDiffeomorph q.2)
  have h2 := h1.comp _ _ (permDiffeo.isLocalDiffeomorph _)
  have h3 : IsLocalDiffeomorphAt (((𝓡 1).prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℝ))
      GC.Endpoint.signedCollarModel ∞
      (Prod.map (Prod.map (id : Circle → Circle) (tubeFibre e s)) seamHeight)
      (permDiffeo (Prod.map bandChart id q)) :=
    (((Diffeomorph.refl (𝓡 1) Circle ∞).isLocalDiffeomorph _).prodMap
      (isLocalDiffeomorphAt_tubeFibre he s _)).prodMap
      (isLocalDiffeomorphAt_seamHeight hq hq0)
  exact h2.comp _ _ h3

def bandBase (l : Fin 3) (q : ℝ × ℝ) : ℂ :=
  hostChart l (strip l (bandHeight l.val q.1 / angleScale q.2, q.2))

theorem bandBase_eq (l : Fin 3) :
    bandBase l = hostChart l ∘ stripDiffeo l ∘ bandScaleDiffeo ∘ Prod.map (bandHeight l.val) id :=
  rfl

theorem isLocalDiffeomorphAt_bandBase (l : Fin 3) {q : ℝ × ℝ} (hq : |q.1| < 1)
    (h0 : l.val ≠ 0 → strip l (bandHeight l.val q.1 / angleScale q.2, q.2) ≠ 0) :
    IsLocalDiffeomorphAt PlaneModel 𝓘(ℝ, ℂ) ∞ (bandBase l) q := by
  rw [bandBase_eq]
  have h1 : IsLocalDiffeomorphAt PlaneModel PlaneModel ∞ (Prod.map (bandHeight l.val) id) q :=
    (isLocalDiffeomorphAt_bandHeight l.val hq).prodMap
      ((Diffeomorph.refl 𝓘(ℝ, ℝ) ℝ ∞).isLocalDiffeomorph q.2)
  have h2 := h1.comp PlaneModel (ℝ × ℝ) (bandScaleDiffeo.isLocalDiffeomorph _)
  have h3 := h2.comp 𝓘(ℝ, ℂ) ℂ ((stripDiffeo l).isLocalDiffeomorph _)
  exact h3.comp 𝓘(ℝ, ℂ) ℂ (isLocalDiffeomorphAt_hostChart l h0)

def bandModel (e₀ e₁ d : ℤ) (l : Fin 3) (q : S2 × ℝ) : ℂ × Circle :=
  (bandBase l (heightOf q.1, q.2),
    GC.GraphManifold.unitOf (planeOf q.1) ^ e₁ * bandPhase e₀ d (heightOf q.1) q.2)

theorem bandModel_eq (e₀ e₁ d : ℤ) (he₁ : e₁ = 1 ∨ e₁ = -1) (l : Fin 3) :
    bandModel e₀ e₁ d l =
      Prod.map (bandBase l) id ∘ shearDiffeo e₀ e₁ d he₁ ∘ Prod.map bandChart id :=
  rfl

theorem isLocalDiffeomorphAt_bandModel (e₀ e₁ d : ℤ) (he₁ : e₁ = 1 ∨ e₁ = -1) (l : Fin 3)
    {q : S2 × ℝ} (hq : |heightOf q.1| < 1)
    (h0 : l.val ≠ 0 → strip l (bandHeight l.val (heightOf q.1) / angleScale q.2, q.2) ≠ 0) :
    IsLocalDiffeomorphAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℂ).prod (𝓡 1)) ∞
      (bandModel e₀ e₁ d l) q := by
  rw [bandModel_eq e₀ e₁ d he₁]
  have h1 : IsLocalDiffeomorphAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) BandModel ∞ (Prod.map bandChart id) q :=
    (bandChart.isLocalDiffeomorphAt _ _ ∞ hq).prodMap
      ((Diffeomorph.refl 𝓘(ℝ, ℝ) ℝ ∞).isLocalDiffeomorph q.2)
  have h2 := h1.comp _ _ ((shearDiffeo e₀ e₁ d he₁).isLocalDiffeomorph _)
  obtain ⟨y, hy⟩ : ∃ y, y = shearDiffeo e₀ e₁ d he₁ (Prod.map bandChart id q) := ⟨_, rfl⟩
  have hy1 : y.1 = (heightOf q.1, q.2) := by rw [hy]; rfl
  have h3 : IsLocalDiffeomorphAt (PlaneModel.prod (𝓡 1)) (𝓘(ℝ, ℂ).prod (𝓡 1)) ∞
      (Prod.map (bandBase l) id) (y.1, y.2) :=
    (isLocalDiffeomorphAt_bandBase l (q := y.1) (by rw [hy1]; exact hq)
      (by rw [hy1]; exact h0)).prodMap
      ((Diffeomorph.refl (𝓡 1) Circle ∞).isLocalDiffeomorph y.2)
  rw [Prod.mk.eta, hy] at h3
  exact h2.comp _ _ h3

end GC.Seifert.SplitTube
