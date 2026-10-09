import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.SolidTorusEdgeChartSTR
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.SolidTorusBallSTI
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageGeometryA74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereCutRelPlugMap

/-!
# S-SOLIDTORUS2 (suffix `_STR`), G2 part 2: the edge chart in the solid torus, the edge stage

The edge chart lifted to the carrier `Wc = X135Radial.carrier` (`edgeChartW_STR`, a partial
diffeomorphism `ℝ³ ⇀ Wc` of models `𝓡 3` and `𝓡∂ 3`), the open parent
`{‖z₁‖² < 1/4, Re z₂ < ‖z₂‖}`, the edge projection `t ∘ (chart)⁻¹ : parent → ℝ¹`, the height
`‖z₁‖²` and the level `1/16`, packaged as `edgeStage_STR : EdgeStage74 Wc`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0.SolidTorusSTR

open GC.GraphManifold.Assembly.FC39P0.SolidTorusSTI GC.GraphManifold.Assembly.FC39P0

local instance carrierCharts_EdgeSTR : ChartedSpace (EuclideanHalfSpace 3) Wc.Carrier := by
  change ChartedSpace (EuclideanHalfSpace 3) solidTorusSet.{0}
  exact inferInstance

local instance carrierSmooth_EdgeSTR : IsManifold (𝓡∂ 3) ∞ Wc.Carrier := by
  change IsManifold (𝓡∂ 3) ∞ solidTorusSet.{0}
  exact inferInstance

theorem graphDefault_mem_STR : graphDefault_STI ∈ solidTorusSet.{0} := by
  change cliffordHeight graphDefault_STI ≤ 0
  simp [cliffordHeight, graphDefault_STI]

theorem edgeMap_mem_solidTorus_STR (x : EuclideanSpace ℝ (Fin 3)) :
    edgeMap_STR x ∈ solidTorusSet.{0} := by
  by_cases hx : rho2_STR x < 4
  · have hp := (edgeMap_mem_target_STR hx).1
    change cliffordHeight (edgeMap_STR x) ≤ 0
    have h1 := norm_sphereFirst_sq_eq (edgeMap_STR x)
    linarith
  · unfold edgeMap_STR
    split_ifs with h
    · exact absurd h hx
    · exact graphDefault_mem_STR

/-- The edge chart map as a map into the carrier. -/
def edgeToW_STR (x : EuclideanSpace ℝ (Fin 3)) : Wc.Carrier :=
  ⟨edgeMap_STR x, edgeMap_mem_solidTorus_STR x⟩

/-- The target of the lifted edge chart. -/
def edgeTargetW_STR : Set Wc.Carrier := {w | w.val ∈ edgeTarget_STR}

theorem isOpen_edgeTargetW_STR : IsOpen edgeTargetW_STR :=
  isOpen_edgeTarget_STR.preimage continuous_subtype_val

/-- **The edge chart in the carrier**: a partial diffeomorphism `ℝ³ ⇀ Wc`. -/
def edgeChartW_STR :
    PartialDiffeomorph (𝓡 3) (𝓡∂ 3) (EuclideanSpace ℝ (Fin 3)) Wc.Carrier ∞ where
  toFun := edgeToW_STR
  invFun w := edgeInv_STR w.val
  source := {x | rho2_STR x < 4}
  target := edgeTargetW_STR
  map_source' := fun _ hx => edgeMap_mem_target_STR hx
  map_target' := fun _ hw => rho2_lt_of_target_STR hw
  left_inv' := fun _ hx => edgeInv_edgeMap_STR hx
  right_inv' := fun _ hw => Subtype.ext (edgeMap_edgeInv_STR hw)
  open_source := isOpen_edgeSource_STR
  open_target := isOpen_edgeTargetW_STR
  contMDiffOn_toFun := (contMDiffOn_solidTorus_iff edgeToW_STR _).2 contMDiffOn_edgeMap_STR
  contMDiffOn_invFun :=
    contMDiffOn_edgeInv_STR.comp contMDiff_solidTorus_val.contMDiffOn (fun _ hw => hw)


/-! ## Differentials in the chart coordinates -/

/-- A smooth function of the chart coordinates has the differential `d G ∘ d (chart⁻¹)`; if
`d G` is onto, so is the differential of `G ∘ chart⁻¹`. -/
theorem surjective_mfderiv_comp_symm_STR {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (G : EuclideanSpace ℝ (Fin 3) → F) {w : Wc.Carrier} (hw : w ∈ edgeChartW_STR.target)
    (hG : ContDiffAt ℝ ∞ G (edgeChartW_STR.symm w))
    (hs : Surjective (fderiv ℝ G (edgeChartW_STR.symm w))) :
    Surjective (mfderiv (𝓡∂ 3) 𝓘(ℝ, F) (G ∘ edgeChartW_STR.symm) w) := by
  have hsymm : MDifferentiableAt (𝓡∂ 3) (𝓡 3) edgeChartW_STR.symm w :=
    edgeChartW_STR.symm.mdifferentiableAt (by simp) hw
  have hGm : MDifferentiableAt (𝓡 3) 𝓘(ℝ, F) G (edgeChartW_STR.symm w) :=
    hG.contMDiffAt.mdifferentiableAt (by simp)
  have hchain := mfderiv_comp w hGm hsymm
  have hb : Bijective (mfderiv (𝓡∂ 3) (𝓡 3) edgeChartW_STR.symm w) :=
    bijective_mfderiv_of_mem_source edgeChartW_STR.symm hw
  rw [hchain]
  have hG' : mfderiv (𝓡 3) 𝓘(ℝ, F) G (edgeChartW_STR.symm w) =
      fderiv ℝ G (edgeChartW_STR.symm w) := mfderiv_eq_fderiv
  rw [hG']
  exact hs.comp hb.2


/-! ## The edge stage -/

/-- The coordinate `x ↦ x₂` as a map `ℝ³ → ℝ¹`. -/
def projLin_STR : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 1) :=
  (EuclideanSpace.proj (2 : Fin 3)).smulRight (EuclideanSpace.single (0 : Fin 1) (1 : ℝ))

theorem projLin_apply_STR (x : EuclideanSpace ℝ (Fin 3)) :
    projLin_STR x = EuclideanSpace.single (0 : Fin 1) (x 2) := by
  ext i
  fin_cases i
  simp [projLin_STR]

theorem projLin_zero_STR (x : EuclideanSpace ℝ (Fin 3)) : projLin_STR x 0 = x 2 := by
  rw [projLin_apply_STR]
  simp

theorem projLin_surjective_STR : Surjective projLin_STR := by
  intro v
  refine ⟨ofCoords_STI 0 0 (v 0), ?_⟩
  ext i
  fin_cases i
  simp [projLin_zero_STR]

/-- The open parent of the edge stage: `{‖z₁‖² < 1/4, Re z₂ < ‖z₂‖}`. -/
def edgeParent_STR : TopologicalSpace.Opens Wc.Carrier :=
  ⟨edgeTargetW_STR, isOpen_edgeTargetW_STR⟩

theorem mem_edgeParent_STR {w : Wc.Carrier} :
    w ∈ edgeParent_STR ↔ ‖sphereFirst w.val‖ ^ 2 < 1 / 4 ∧
      (sphereSecond w.val).re < ‖sphereSecond w.val‖ :=
  Iff.rfl

theorem edgeParent_interior_STR : (edgeParent_STR : Set Wc.Carrier) ⊆ Wc.interior := by
  intro w hw
  have h1 := norm_sphereFirst_sq_eq w.val
  have h2 := (mem_edgeParent_STR.1 hw).1
  exact (solidTorus_isInteriorPoint_iff w).mpr (by linarith)

/-- The edge projection `t ∘ (chart)⁻¹` as a plain function. -/
def edgeProjFun_STR (w : edgeParent_STR) : EuclideanSpace ℝ (Fin 1) :=
  projLin_STR (edgeInv_STR w.val.val)

theorem contMDiff_edgeProj_STR : ContMDiff (𝓡∂ 3) (𝓡 1) ∞ edgeProjFun_STR := by
  have hval : ContMDiff (𝓡∂ 3) (𝓡 3) ∞ (fun w : edgeParent_STR => w.val.val) :=
    contMDiff_solidTorus_val.comp contMDiff_subtype_val
  exact projLin_STR.contDiff.contMDiff.comp
    (contMDiffOn_edgeInv_STR.comp_contMDiff hval (fun w => w.2))

/-- The edge projection of the stage. -/
def edgeProj_STR : C(edgeParent_STR, EuclideanSpace ℝ (Fin 1)) :=
  ⟨edgeProjFun_STR, contMDiff_edgeProj_STR.continuous⟩

theorem edgeProj_submersion_STR (x : edgeParent_STR) :
    Surjective (mfderiv (𝓡∂ 3) (𝓡 1) edgeProj_STR x) := by
  change Surjective (mfderiv (𝓡∂ 3) (𝓡 1)
    (fun y : edgeParent_STR => (projLin_STR ∘ edgeChartW_STR.symm) y.val) x)
  rw [DifferentialGeometry.mfderiv_restrict_open (fun y : Wc.Carrier =>
    (projLin_STR ∘ edgeChartW_STR.symm) y) edgeParent_STR x]
  refine surjective_mfderiv_comp_symm_STR projLin_STR x.2 projLin_STR.contDiff.contDiffAt ?_
  rw [ContinuousLinearMap.fderiv]
  exact projLin_surjective_STR

/-- The height `‖z₁‖²` of the edge stage. -/
def edgeHeight_STR (w : edgeParent_STR) : ℝ := ‖sphereFirst w.val.val‖ ^ 2

theorem contMDiff_edgeHeight_STR : ContMDiff (𝓡∂ 3) 𝓘(ℝ, ℝ) ∞ edgeHeight_STR :=
  ((contDiff_norm_sq ℝ).contMDiff.comp contMDiff_sphereFirst).comp
    (contMDiff_solidTorus_val.comp contMDiff_subtype_val)

/-- The level of the edge stage: `‖z₁‖² = 1/16` (`|ζ| = 1`). -/
def edgeLevel_STR : ℝ := 1 / 16

/-- **The edge stage of the solid torus instance** (`q₁ = t`, `T = ‖z₁‖²`, level `1/16`). -/
def edgeStage_STR : EdgeStage74 Wc where
  Base := EuclideanSpace ℝ (Fin 1)
  parent := edgeParent_STR
  parent_interior := edgeParent_interior_STR
  proj := edgeProj_STR
  proj_smooth := contMDiff_edgeProj_STR
  proj_submersion := edgeProj_submersion_STR
  height := edgeHeight_STR
  height_smooth := contMDiff_edgeHeight_STR
  level := edgeLevel_STR


/-! ## Chart coordinates of the edge stage -/

theorem edgeInvW_apply_STR (w : Wc.Carrier) : edgeChartW_STR.symm w = edgeInv_STR w.val := rfl

theorem edgeInv_two_STR (p : SphereCarrier.{0}) :
    edgeInv_STR p 2 = tOf_STR (sphereSecond p) := by
  simp [edgeInv_STR]

theorem edgeProj_val_STR (w : edgeParent_STR) :
    edgeProj_STR w 0 = tOf_STR (sphereSecond w.val.val) := by
  change projLin_STR (edgeInv_STR w.val.val) 0 = _
  rw [projLin_zero_STR, edgeInv_two_STR]

theorem sphereFirst_sq_edgeToW_STR {x : EuclideanSpace ℝ (Fin 3)} (hx : rho2_STR x < 4) :
    ‖sphereFirst (edgeToW_STR x).val‖ ^ 2 = rho2_STR x / 16 := by
  change ‖sphereFirst (edgeMap_STR x)‖ ^ 2 = _
  rw [sphereFirst_edgeMap_STR hx, Complex.sq_norm, Complex.normSq_apply]
  simp only [edgeFirst_STR, rho2_STR]
  ring

theorem tOf_edgeToW_STR {x : EuclideanSpace ℝ (Fin 3)} (hx : rho2_STR x < 4) :
    tOf_STR (sphereSecond (edgeToW_STR x).val) = x 2 := by
  change tOf_STR (sphereSecond (edgeMap_STR x)) = _
  rw [sphereSecond_edgeMap_STR hx]
  exact tOf_edgeSecond_STR hx

theorem edgeToW_mem_parent_STR {x : EuclideanSpace ℝ (Fin 3)} (hx : rho2_STR x < 4) :
    edgeToW_STR x ∈ edgeParent_STR :=
  edgeMap_mem_target_STR hx

theorem edgeHeight_eq_STR (w : edgeParent_STR) :
    edgeHeight_STR w = (1 / 16 : ℝ) * rho2_STR (edgeInv_STR w.val.val) := by
  rw [edgeHeight_STR, rho2_edgeInv_STR]
  ring

theorem mfderiv_comp_symm_apply_STR {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (G : EuclideanSpace ℝ (Fin 3) → F) {w : Wc.Carrier} (hw : w ∈ edgeChartW_STR.target)
    (hG : ContDiffAt ℝ ∞ G (edgeChartW_STR.symm w)) (v : TangentSpace (𝓡∂ 3) w) :
    mfderiv (𝓡∂ 3) 𝓘(ℝ, F) (G ∘ edgeChartW_STR.symm) w v =
      fderiv ℝ G (edgeChartW_STR.symm w) (mfderiv (𝓡∂ 3) (𝓡 3) edgeChartW_STR.symm w v) := by
  have hsymm : MDifferentiableAt (𝓡∂ 3) (𝓡 3) edgeChartW_STR.symm w :=
    edgeChartW_STR.symm.mdifferentiableAt (by simp) hw
  have hGm : MDifferentiableAt (𝓡 3) 𝓘(ℝ, F) G (edgeChartW_STR.symm w) :=
    hG.contMDiffAt.mdifferentiableAt (by simp)
  have hchain := mfderiv_comp w hGm hsymm
  have hG' : mfderiv (𝓡 3) 𝓘(ℝ, F) G (edgeChartW_STR.symm w) =
      fderiv ℝ G (edgeChartW_STR.symm w) := mfderiv_eq_fderiv
  rw [hchain, hG']
  rfl

theorem hasFDerivAt_rho2_STR (x : EuclideanSpace ℝ (Fin 3)) :
    HasFDerivAt rho2_STR (x 0 • (EuclideanSpace.proj 0 : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) +
      x 0 • (EuclideanSpace.proj 0 : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) +
      (x 1 • (EuclideanSpace.proj 1 : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) +
      x 1 • (EuclideanSpace.proj 1 : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ))) x := by
  have h0 : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin 3) => z 0)
      (EuclideanSpace.proj 0 : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) x :=
    (EuclideanSpace.proj 0 : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ).hasFDerivAt
  have h1 : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin 3) => z 1)
      (EuclideanSpace.proj 1 : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) x :=
    (EuclideanSpace.proj 1 : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ).hasFDerivAt
  have h := (h0.mul h0).add (h1.mul h1)
  have hf : rho2_STR = fun z : EuclideanSpace ℝ (Fin 3) => z 0 * z 0 + z 1 * z 1 := by
    funext z
    simp only [rho2_STR]
    ring
  rw [hf]
  exact h

theorem fderiv_rho2_apply_STR (x e : EuclideanSpace ℝ (Fin 3)) :
    fderiv ℝ rho2_STR x e = 2 * x 0 * e 0 + 2 * x 1 * e 1 := by
  rw [(hasFDerivAt_rho2_STR x).fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul]
  change x 0 * e 0 + x 0 * e 0 + (x 1 * e 1 + x 1 * e 1) = 2 * x 0 * e 0 + 2 * x 1 * e 1
  ring


theorem contDiff_rho2_div_STR :
    ContDiff ℝ ∞ (fun z : EuclideanSpace ℝ (Fin 3) => (1 / 16 : ℝ) * rho2_STR z) :=
  contDiff_const.mul contDiff_rho2_STR

theorem mfderiv_edgeProj_apply_STR (x : edgeParent_STR)
    (v : TangentSpace (𝓡∂ 3) (x : Wc.Carrier)) :
    mfderiv (𝓡∂ 3) (𝓡 1) edgeProj_STR x v =
      projLin_STR (mfderiv (𝓡∂ 3) (𝓡 3) edgeChartW_STR.symm x.val v) := by
  have h := congrArg (fun L => L v) (DifferentialGeometry.mfderiv_restrict_open
    (I := 𝓡∂ 3) (J := 𝓡 1) (fun y : Wc.Carrier => (projLin_STR ∘ edgeChartW_STR.symm) y)
    edgeParent_STR x)
  have h2 := mfderiv_comp_symm_apply_STR projLin_STR x.2 projLin_STR.contDiff.contDiffAt v
  rw [ContinuousLinearMap.fderiv] at h2
  exact h.trans h2

theorem mfderiv_edgeHeight_apply_STR (x : edgeParent_STR)
    (v : TangentSpace (𝓡∂ 3) (x : Wc.Carrier)) :
    mfderiv (𝓡∂ 3) 𝓘(ℝ, ℝ) edgeHeight_STR x v =
      fderiv ℝ (fun z => (1 / 16 : ℝ) * rho2_STR z) (edgeInv_STR x.val.val)
        (mfderiv (𝓡∂ 3) (𝓡 3) edgeChartW_STR.symm x.val v) := by
  have hfun : edgeHeight_STR = fun y : edgeParent_STR =>
      ((fun z => (1 / 16 : ℝ) * rho2_STR z) ∘ edgeChartW_STR.symm) y.val :=
    funext edgeHeight_eq_STR
  rw [hfun]
  have h := congrArg (fun L => L v) (DifferentialGeometry.mfderiv_restrict_open
    (I := 𝓡∂ 3) (J := 𝓘(ℝ, ℝ))
    (fun y : Wc.Carrier => ((fun z => (1 / 16 : ℝ) * rho2_STR z) ∘ edgeChartW_STR.symm) y)
    edgeParent_STR x)
  have h2 := mfderiv_comp_symm_apply_STR (fun z => (1 / 16 : ℝ) * rho2_STR z) x.2
    contDiff_rho2_div_STR.contDiffAt v
  exact h.trans h2

theorem fderiv_rho2_div_apply_STR (x e : EuclideanSpace ℝ (Fin 3)) :
    fderiv ℝ (fun z => (1 / 16 : ℝ) * rho2_STR z) x e =
      (1 / 16 : ℝ) * (2 * x 0 * e 0 + 2 * x 1 * e 1) := by
  rw [((hasFDerivAt_rho2_STR x).const_mul (1 / 16 : ℝ)).fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul]
  change (1 / 16 : ℝ) * (x 0 * e 0 + x 0 * e 0 + (x 1 * e 1 + x 1 * e 1)) = _
  ring

/-- **EDP04 rank two on the level**: at the level `‖z₁‖² = 1/16` the pair `(dt, dT)` is onto. -/
theorem edgeRank_two_STR (x : edgeParent_STR) (hx : edgeHeight_STR x = edgeLevel_STR) :
    Surjective fun v : TangentSpace (𝓡∂ 3) (x : Wc.Carrier) =>
      (mfderiv (𝓡∂ 3) (𝓡 1) edgeProj_STR x v,
        mfderiv (𝓡∂ 3) 𝓘(ℝ, ℝ) edgeHeight_STR x v) := by
  have hb : Bijective (mfderiv (𝓡∂ 3) (𝓡 3) edgeChartW_STR.symm x.val) :=
    bijective_mfderiv_of_mem_source edgeChartW_STR.symm x.2
  set x₀ := edgeInv_STR x.val.val with hx₀
  have hρ : x₀ 0 ^ 2 + x₀ 1 ^ 2 = 1 := by
    have h := edgeHeight_eq_STR x
    rw [hx, edgeLevel_STR] at h
    change 1 / 16 = (1 / 16 : ℝ) * rho2_STR x₀ at h
    rw [rho2_STR] at h
    linarith
  intro p
  let a : EuclideanSpace ℝ (Fin 1) := p.1
  let b : ℝ := p.2
  obtain ⟨v, hv⟩ := hb.2 (ofCoords_STI (8 * b * x₀ 0) (8 * b * x₀ 1) (a 0))
  refine ⟨v, Prod.ext ?_ ?_⟩
  · refine (mfderiv_edgeProj_apply_STR x v).trans ((congrArg projLin_STR hv).trans ?_)
    ext i
    fin_cases i
    simp [projLin_zero_STR, a]
  · refine (mfderiv_edgeHeight_apply_STR x v).trans
      ((congrArg (fderiv ℝ (fun z => (1 / 16 : ℝ) * rho2_STR z) (edgeInv_STR x.val.val)) hv).trans
        ((fderiv_rho2_div_apply_STR _ _).trans ?_))
    simp only [ofCoords_zero_STI, ofCoords_one_STI]
    have h8 : 2 * x₀ 0 * (8 * b * x₀ 0) + 2 * x₀ 1 * (8 * b * x₀ 1) =
        16 * b * (x₀ 0 ^ 2 + x₀ 1 ^ 2) := by ring
    rw [h8, hρ]
    change (1 / 16 : ℝ) * (16 * b * 1) = b
    ring

end GC.GraphManifold.Assembly.FC39P0.SolidTorusSTR
