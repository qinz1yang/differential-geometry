import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.ExtPortSlimXPI
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0SphereCircleChart

/-!
# FC39 external-port regression instance: the circle bundle

The circle bundle of the external-port instance on the carrier `T² × I = {1/2 ≤ |z| ≤ 3} × S¹`:
the fibres are the circle factor, the base is the open annulus `5/4 < ‖w‖ < 9/4` of `ℝ²`
(`w = toE2_XPI z`, the real coordinates of `z`), the domain is `5/4 < rad < 9/4`, one global
trivialisation `x ↦ (w, θ)`, and the closed base `C₁ = {3/2 ≤ ‖w‖ ≤ 2}` (an annulus: two boundary
circles, no corners). Result: `extportCircle_XPI : CircleBundle carrierW_XPI`, with its fibres,
tubes and region `{3/2 ≤ rad ≤ 2}` in closed form.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open DifferentialGeometry.Topology.Manifold Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0.ExtPortXPI

local notation "E2" => EuclideanSpace ℝ (Fin 2)

local instance carrierCharts_XPIc :
    ChartedSpace (EuclideanHalfSpace 3) carrierW_XPI.Carrier := by
  change ChartedSpace (EuclideanHalfSpace 3) (productSet.{0} 2)
  exact inferInstance

local instance carrierSmooth_XPIc : IsManifold (𝓡∂ 3) ∞ carrierW_XPI.Carrier := by
  change IsManifold (𝓡∂ 3) ∞ (productSet.{0} 2)
  exact inferInstance

/-- The real coordinates of `ℂ`. -/
def toE2_XPI : ℂ ≃ₗᵢ[ℝ] E2 := Complex.orthonormalBasisOneI.repr

theorem norm_toE2_XPI (z : ℂ) : ‖toE2_XPI z‖ = ‖z‖ := toE2_XPI.norm_map z

theorem norm_toE2_symm_XPI (w : E2) : ‖toE2_XPI.symm w‖ = ‖w‖ := toE2_XPI.symm.norm_map w

/-- The open base annulus `5/4 < ‖w‖ < 9/4`. -/
def circleBaseOpens_XPI : TopologicalSpace.Opens E2 :=
  ⟨{w | 5 / 4 < ‖w‖ ∧ ‖w‖ < 9 / 4},
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)⟩

/-- The circle domain `5/4 < rad < 9/4`. -/
def circleDomain_XPI : TopologicalSpace.Opens carrierW_XPI.Carrier :=
  ⟨{x | 5 / 4 < rad_XPI x ∧ rad_XPI x < 9 / 4},
    (isOpen_lt continuous_const continuous_rad_XPI).inter
      (isOpen_lt continuous_rad_XPI continuous_const)⟩

theorem mem_circleDomain_XPI {x : carrierW_XPI.Carrier} :
    x ∈ circleDomain_XPI ↔ 5 / 4 < rad_XPI x ∧ rad_XPI x < 9 / 4 :=
  Iff.rfl

/-- The carrier point `(z, θ)` of a base point and an angle. -/
def circlePoint_XPI (w : circleBaseOpens_XPI) (θ : Circle) : carrierW_XPI.Carrier :=
  ⟨(ULift.up (toE2_XPI.symm w.val), θ), by
    have hw := w.2
    change 5 / 4 < ‖w.val‖ ∧ ‖w.val‖ < 9 / 4 at hw
    apply (mem_planarSet_iff (Or.inl rfl) _).mpr
    apply (mem_planarModel_two _).mpr
    change ‖toE2_XPI.symm w.val‖ ≤ 3 ∧ 1 / 2 ≤ ‖toE2_XPI.symm w.val‖
    rw [norm_toE2_symm_XPI]
    constructor <;> linarith [hw.1, hw.2]⟩

theorem rad_circlePoint_XPI (w : circleBaseOpens_XPI) (θ : Circle) :
    rad_XPI (circlePoint_XPI w θ) = ‖w.val‖ :=
  norm_toE2_symm_XPI w.val

theorem circlePoint_mem_XPI (w : circleBaseOpens_XPI) (θ : Circle) :
    circlePoint_XPI w θ ∈ circleDomain_XPI := by
  rw [mem_circleDomain_XPI, rad_circlePoint_XPI]
  exact w.2

/-- The trivialisation map `x ↦ (w, θ)`. -/
def circleTrivMap_XPI (x : circleDomain_XPI) : circleBaseOpens_XPI × Circle :=
  (⟨toE2_XPI x.val.val.1.down, by
    have hx := x.2
    change 5 / 4 < ‖toE2_XPI x.val.val.1.down‖ ∧ ‖toE2_XPI x.val.val.1.down‖ < 9 / 4
    rw [norm_toE2_XPI]
    exact hx⟩, x.val.val.2)

/-- The inverse of the trivialisation. -/
def circleTrivInv_XPI (q : circleBaseOpens_XPI × Circle) : circleDomain_XPI :=
  ⟨circlePoint_XPI q.1 q.2, circlePoint_mem_XPI q.1 q.2⟩

theorem contMDiff_carrierVal_XPIc :
    ContMDiff (𝓡∂ 3) (𝓘(ℝ, ℂ).prod (𝓡 1)) ∞
      (Subtype.val : carrierW_XPI.Carrier → PlaneLift.{0} × Circle) :=
  (productAtlas.{0} 2).contMDiff_subtype_val

theorem circleTrivMap_smooth_XPI :
    ContMDiff (𝓡∂ 3) ((𝓡 2).prod (𝓡 1)) ∞ circleTrivMap_XPI := by
  have hval : ContMDiff (𝓡∂ 3) (𝓘(ℝ, ℂ).prod (𝓡 1)) ∞
      (fun x : circleDomain_XPI => x.val.val) :=
    contMDiff_carrierVal_XPIc.comp contMDiff_subtype_val
  have hz : ContMDiff (𝓡∂ 3) (𝓡 2) ∞
      (fun x : circleDomain_XPI => toE2_XPI x.val.val.1.down) :=
    (toE2_XPI.toContinuousLinearEquiv.toContinuousLinearMap.contDiff.contMDiff.comp
      (contMDiff_planeLift_down.comp (contMDiff_fst.comp hval)))
  refine ContMDiff.prodMk (fun x => ?_) (contMDiff_snd.comp hval)
  exact codRestr_contMDiffAt (V := circleBaseOpens_XPI)
    (f := fun x : circleDomain_XPI => toE2_XPI x.val.val.1.down)
    (fun x => (circleTrivMap_XPI x).1.2) (hz x)

theorem circleTrivInv_smooth_XPI :
    ContMDiff ((𝓡 2).prod (𝓡 1)) (𝓡∂ 3) ∞ circleTrivInv_XPI := by
  have hp : ContMDiff ((𝓡 2).prod (𝓡 1)) (𝓡∂ 3) ∞
      (fun q : circleBaseOpens_XPI × Circle => circlePoint_XPI q.1 q.2) := by
    apply ((productAtlas.{0} 2).contMDiff_iff_subtype_val _).mpr
    have hw : ContMDiff ((𝓡 2).prod (𝓡 1)) 𝓘(ℝ, ℂ) ∞
        (fun q : circleBaseOpens_XPI × Circle => toE2_XPI.symm q.1.val) :=
      toE2_XPI.symm.toContinuousLinearEquiv.toContinuousLinearMap.contDiff.contMDiff.comp
        (contMDiff_subtype_val.comp contMDiff_fst)
    exact (contMDiff_planeLift_up.comp hw).prodMk contMDiff_snd
  intro q
  exact codRestr_contMDiffAt (V := circleDomain_XPI)
    (f := fun q : circleBaseOpens_XPI × Circle => circlePoint_XPI q.1 q.2)
    (fun q => circlePoint_mem_XPI q.1 q.2) (hp q)

/-- **The global trivialisation** `x ↦ (w, θ)` of the circle domain. -/
def circleTriv_XPI :
    circleDomain_XPI ≃ₘ⟮𝓡∂ 3, (𝓡 2).prod (𝓡 1)⟯ (circleBaseOpens_XPI × Circle) where
  toFun := circleTrivMap_XPI
  invFun := circleTrivInv_XPI
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    change ((ULift.up (toE2_XPI.symm (toE2_XPI x.val.val.1.down)), x.val.val.2) :
      PlaneLift.{0} × Circle) = x.val.val
    rw [LinearIsometryEquiv.symm_apply_apply]
  right_inv q := by
    apply Prod.ext
    · apply Subtype.ext
      change toE2_XPI (toE2_XPI.symm q.1.val) = q.1.val
      exact LinearIsometryEquiv.apply_symm_apply _ _
    · rfl
  contMDiff_toFun := circleTrivMap_smooth_XPI
  contMDiff_invFun := circleTrivInv_smooth_XPI

/-- The bundle projection `x ↦ w`. -/
def circleProj_XPI (x : circleDomain_XPI) : circleBaseOpens_XPI := (circleTriv_XPI x).1

theorem circleProj_val_XPI (x : circleDomain_XPI) :
    (circleProj_XPI x).val = toE2_XPI x.val.val.1.down :=
  rfl

theorem contMDiff_circleProj_XPI : ContMDiff (𝓡∂ 3) (𝓡 2) ∞ circleProj_XPI :=
  contMDiff_fst.comp circleTriv_XPI.contMDiff

theorem circleProj_submersion_XPI (x : circleDomain_XPI) :
    Surjective (mfderiv (𝓡∂ 3) (𝓡 2) circleProj_XPI x) := by
  have hΦ : MDifferentiableAt (𝓡∂ 3) ((𝓡 2).prod (𝓡 1)) circleTriv_XPI x :=
    circleTriv_XPI.contMDiff.mdifferentiableAt (by simp)
  have hfst : MDifferentiableAt ((𝓡 2).prod (𝓡 1)) (𝓡 2)
      (Prod.fst : circleBaseOpens_XPI × Circle → circleBaseOpens_XPI) (circleTriv_XPI x) :=
    mdifferentiableAt_fst
  have h := mfderiv_comp x hfst hΦ
  change Surjective (mfderiv (𝓡∂ 3) (𝓡 2) (Prod.fst ∘ circleTriv_XPI) x)
  rw [h, mfderiv_fst]
  intro v
  obtain ⟨w, hw⟩ := (circleTriv_XPI.mfderivToContinuousLinearEquiv (by simp) x).surjective (v, 0)
  have hw' : mfderiv (𝓡∂ 3) ((𝓡 2).prod (𝓡 1)) circleTriv_XPI x w = (v, 0) := hw
  exact ⟨w, congrArg Prod.fst hw'⟩

/-- The projection as a continuous map. -/
def circleProjMap_XPI : C(circleDomain_XPI, circleBaseOpens_XPI) :=
  ⟨circleProj_XPI, contMDiff_circleProj_XPI.continuous⟩

/-- The trivialisation over `⊤` in the shape of the contract field. -/
def circleTrivTop_XPI :
    (TopologicalSpace.Opens.comap circleProjMap_XPI
        (⊤ : TopologicalSpace.Opens circleBaseOpens_XPI))
      ≃ₘ⟮𝓡∂ 3, (𝓡 2).prod (𝓡 1)⟯
        ((⊤ : TopologicalSpace.Opens circleBaseOpens_XPI) × Circle) :=
  (opensDiffeoOfForall_CIRCA (TopologicalSpace.Opens.comap circleProjMap_XPI ⊤)
    (fun _ => trivial)).trans (circleTriv_XPI.trans
    ((opensDiffeoOfForall_CIRCA ⊤ (fun _ => trivial)).symm.prodCongr
      (Diffeomorph.refl (𝓡 1) Circle ∞)))

theorem circleTrivTop_fst_XPI (x : TopologicalSpace.Opens.comap circleProjMap_XPI
    (⊤ : TopologicalSpace.Opens circleBaseOpens_XPI)) :
    ((circleTrivTop_XPI x).1).val = circleProj_XPI x.val :=
  rfl

/-- The closed base annulus `C₁ = {3/2 ≤ ‖w‖ ≤ 2}`. -/
def circleCbase_XPI : Set circleBaseOpens_XPI := {c | 3 / 2 ≤ ‖c.val‖ ∧ ‖c.val‖ ≤ 2}

theorem isCompact_circleCbase_XPI : IsCompact circleCbase_XPI := by
  have himg : Subtype.val '' circleCbase_XPI = {w : E2 | 3 / 2 ≤ ‖w‖ ∧ ‖w‖ ≤ 2} := by
    ext w
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact hc
    · intro hw
      exact ⟨⟨w, by
        change 5 / 4 < ‖w‖ ∧ ‖w‖ < 9 / 4
        constructor <;> linarith [hw.1, hw.2]⟩, hw, rfl⟩
  rw [Subtype.isCompact_iff, himg]
  have hset : {w : E2 | 3 / 2 ≤ ‖w‖ ∧ ‖w‖ ≤ 2} =
      Metric.closedBall 0 2 ∩ {w | 3 / 2 ≤ ‖w‖} := by
    ext w
    simp only [Set.mem_ofPred_eq, mem_inter_iff, Metric.mem_closedBall, dist_zero_right]
    exact and_comm
  rw [hset]
  exact (isCompact_closedBall 0 2).inter_right (isClosed_le continuous_const continuous_norm)

/-- **The circle bundle of the external-port instance.** -/
def extportCircle_XPI : CircleBundle carrierW_XPI where
  Base := circleBaseOpens_XPI
  domain := circleDomain_XPI
  domain_interior x hx :=
    mem_carrier_interior_XPI (by linarith [hx.1]) (by linarith [hx.2])
  proj := circleProjMap_XPI
  proj_smooth := contMDiff_circleProj_XPI
  proj_submersion := circleProj_submersion_XPI
  neighborhood _ := ⊤
  mem_neighborhood _ := trivial
  trivialization _ := circleTrivTop_XPI
  projection_trivialization _ x := circleTrivTop_fst_XPI x
  cbase := circleCbase_XPI
  cbase_compact := isCompact_circleCbase_XPI

/-! ## Fibres, tubes, region -/

theorem extportCircle_proj_XPI (x : circleDomain_XPI) :
    extportCircle_XPI.proj x = circleProj_XPI x :=
  rfl

/-- **Tubes**: the full circle preimage of a base set `V` is the set of carrier points whose
coordinate lies in `V`. -/
theorem extportCircle_tube_XPI (V : Set circleBaseOpens_XPI) :
    extportCircle_XPI.tube V =
      {x : carrierW_XPI.Carrier | toE2_XPI x.val.1.down ∈ Subtype.val '' V} := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨circleProj_XPI y, hy, rfl⟩
  · rintro ⟨c, hc, hcx⟩
    have hx : x ∈ circleDomain_XPI := by
      rw [mem_circleDomain_XPI]
      have h := c.2
      change 5 / 4 < ‖c.val‖ ∧ ‖c.val‖ < 9 / 4 at h
      rw [hcx, norm_toE2_XPI] at h
      exact h
    refine ⟨⟨x, hx⟩, ?_, rfl⟩
    change circleProj_XPI ⟨x, hx⟩ ∈ V
    have he : circleProj_XPI ⟨x, hx⟩ = c := Subtype.ext hcx.symm
    rw [he]
    exact hc

/-- **The whole circle fibre** over `c`: the carrier points with coordinate `c`. -/
theorem extportCircle_fibre_XPI (c : circleBaseOpens_XPI) :
    extportCircle_XPI.fibre c = {x : carrierW_XPI.Carrier | toE2_XPI x.val.1.down = c.val} := by
  have h := extportCircle_tube_XPI {c}
  rw [image_singleton] at h
  exact h

theorem circlePoint_mem_fibre_XPI (c : circleBaseOpens_XPI) (θ : Circle) :
    circlePoint_XPI c θ ∈ extportCircle_XPI.fibre c := by
  rw [extportCircle_fibre_XPI]
  exact LinearIsometryEquiv.apply_symm_apply _ _

theorem rad_of_mem_fibre_XPI {c : circleBaseOpens_XPI} {x : carrierW_XPI.Carrier}
    (hx : x ∈ extportCircle_XPI.fibre c) : rad_XPI x = ‖c.val‖ := by
  rw [extportCircle_fibre_XPI] at hx
  change toE2_XPI x.val.1.down = c.val at hx
  rw [← hx, norm_toE2_XPI]
  rfl

/-- **The region** `M₃ = E⁻¹(C₁) = {3/2 ≤ rad ≤ 2}`. -/
theorem extportCircle_region_XPI :
    extportCircle_XPI.region = {x : carrierW_XPI.Carrier | 3 / 2 ≤ rad_XPI x ∧ rad_XPI x ≤ 2} := by
  have h := extportCircle_tube_XPI circleCbase_XPI
  refine h.trans ?_
  ext x
  constructor
  · rintro ⟨c, hc, hcx⟩
    have hr : rad_XPI x = ‖c.val‖ := by
      change ‖x.val.1.down‖ = _
      rw [← norm_toE2_XPI, hcx]
    rw [Set.mem_ofPred_eq, hr]
    exact hc
  · intro hx
    refine ⟨⟨toE2_XPI x.val.1.down, ?_⟩, ?_, rfl⟩
    · change 5 / 4 < ‖toE2_XPI x.val.1.down‖ ∧ ‖toE2_XPI x.val.1.down‖ < 9 / 4
      rw [norm_toE2_XPI]
      change 5 / 4 < rad_XPI x ∧ rad_XPI x < 9 / 4
      constructor <;> linarith [hx.1, hx.2]
    · change 3 / 2 ≤ ‖toE2_XPI x.val.1.down‖ ∧ ‖toE2_XPI x.val.1.down‖ ≤ 2
      rw [norm_toE2_XPI]
      exact hx

end GC.GraphManifold.Assembly.FC39P0.ExtPortXPI
