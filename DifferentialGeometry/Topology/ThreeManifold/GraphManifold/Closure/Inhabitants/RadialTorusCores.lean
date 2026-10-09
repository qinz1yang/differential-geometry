import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.RadialTorusCuspFaces

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0.X135Radial

local instance carrierCharts_CuspFunctions :
    ChartedSpace (EuclideanHalfSpace 3) carrier.Carrier := by
  change ChartedSpace (EuclideanHalfSpace 3) solidTorusSet.{0}
  exact inferInstance

local instance carrierSmooth_CuspFunctions : IsManifold (𝓡∂ 3) ∞ carrier.Carrier := by
  change IsManifold (𝓡∂ 3) ∞ solidTorusSet.{0}
  exact inferInstance

theorem height_smooth : ContMDiff (𝓡∂ 3) 𝓘(ℝ, ℝ) ∞ height :=
  contMDiff_cliffordHeight.comp contMDiff_solidTorus_val

theorem carrier_height_regular (p : carrier.Carrier) (hp : -1 < height p ∧ height p < 1) :
    mfderiv (𝓡∂ 3) 𝓘(ℝ, ℝ) height p ≠ 0 := by
  have hval := solidTorusAtlas.mfderiv_subtypeVal_bijective p
  have hchain := mfderiv_comp p
    (contMDiff_cliffordHeight.mdifferentiableAt (by simp))
    (contMDiff_solidTorus_val.mdifferentiableAt (by simp))
  intro hzero
  have hz : mfderiv (𝓡∂ 3) 𝓘(ℝ, ℝ)
      (cliffordHeight ∘ (Subtype.val : carrier.Carrier → SphereCarrier.{0})) p = 0 := hzero
  have hc := hchain.symm.trans hz
  apply radial_height_regular p.val hp
  ext v
  obtain ⟨u, hu⟩ := hval.2 v
  have hv := DFunLike.congr_fun hc u
  change mfderiv (𝓡 3) 𝓘(ℝ, ℝ) cliffordHeight p.val
    ((mfderiv (𝓡∂ 3) (𝓡 3) (Subtype.val : carrier.Carrier → SphereCarrier.{0}) p) u) = 0 at hv
  rw [hu] at hv
  exact hv

theorem carrier_mvfderiv_height_regular (p : carrier.Carrier)
    (hp : -1 < height p ∧ height p < 1) : mvfderiv (𝓡∂ 3) height p ≠ 0 := by
  intro hzero
  apply carrier_height_regular p hp
  ext v
  apply (NormedSpace.fromTangentSpace (height p)).injective
  have h := DFunLike.congr_fun hzero v
  simpa only [mvfderiv, ContinuousLinearMap.comp_apply, zero_apply,
    ContinuousLinearEquiv.coe_coe, map_zero] using h

def cuspDefiner (p : carrier.Carrier) : ℝ := -(1 / 4 : ℝ) - height p

def cuspNear : TopologicalSpace.Opens carrier.Carrier :=
  ⟨{p | -(3 / 8 : ℝ) < height p ∧ height p < -(1 / 8 : ℝ)},
    (isOpen_lt continuous_const height_continuous).inter
      (isOpen_lt height_continuous continuous_const)⟩

theorem cuspDefiner_smooth : ContMDiff (𝓡∂ 3) 𝓘(ℝ, ℝ) ∞ cuspDefiner :=
  contMDiff_const.sub height_smooth

theorem cuspDefiner_regular (p : carrier.Carrier) (hp : cuspDefiner p = 0) :
    mfderiv (𝓡∂ 3) 𝓘(ℝ, ℝ) cuspDefiner p ≠ 0 := by
  have he : height p = -(1 / 4 : ℝ) := sub_eq_zero.mp hp |>.symm
  have hreg := carrier_mvfderiv_height_regular p ⟨by rw [he]; norm_num,
    by rw [he]; norm_num⟩
  intro hzero
  have hz : mvfderiv (𝓡∂ 3) cuspDefiner p = 0 := by
    simp only [mvfderiv, hzero, ContinuousLinearMap.comp_zero]
  change mvfderiv (𝓡∂ 3) (fun p => -(1 / 4 : ℝ) - height p) p = 0 at hz
  rw [mvfderiv_fun_sub (g := fun _ => -(1 / 4 : ℝ)) (g' := height)
    mdifferentiableAt_const (height_smooth.mdifferentiableAt (by simp)),
    mvfderiv_const, zero_sub] at hz
  exact hreg (neg_eq_zero.mp hz)

theorem cuspNear_interior : (cuspNear : Set carrier.Carrier) ⊆ carrier.interior := by
  intro p hp
  exact (solidTorus_isInteriorPoint_iff p).mpr (hp.2.trans (by norm_num))

theorem cusp_near_eq : range cuspPiece.map ∩ cuspNear =
    {p | p ∈ cuspNear ∧ cuspDefiner p ≤ 0} := by
  change range cuspToCarrier ∩ cuspNear = {p | p ∈ cuspNear ∧ cuspDefiner p ≤ 0}
  rw [cuspToCarrier_range]
  ext p
  constructor
  · intro hp
    exact ⟨hp.2, sub_nonpos.mpr hp.1⟩
  · intro hp
    exact ⟨sub_nonpos.mp hp.2, hp.1⟩

theorem cuspEnd_map_false (t : Torus) :
    cuspPiece.map (cuspEnd false t) = boundary.torusMap 0 t := by
  rw [boundary_torusMap]
  apply Subtype.ext
  change cliffordSeamMap.{0} (t, -((Assembly.iccEnd false).val / 4)) =
    cliffordSeamMap.{0} (t, -halfZero.val 0)
  norm_num [Assembly.iccEnd, halfZero, GC.Endpoint.halfPoint]

theorem cuspEnd_map_range (b : Bool) :
    range (fun t => cuspPiece.map (cuspEnd b t)) =
      {p | height p = if b then -(1 / 4 : ℝ) else 0} := by
  ext p
  constructor
  · rintro ⟨t, rfl⟩
    exact cuspEnd_height b t
  · intro hp
    have hc : -(1 / 4 : ℝ) ≤ height p := by
      rw [hp]
      cases b <;> norm_num
    let q : cuspSet := ⟨p.val, (bandDefiner_nonpos_iff (by norm_num)).mpr ⟨hc, p.property⟩⟩
    have hq : q ∈ range (cuspEnd b) := by
      rw [cuspEnd_range]
      exact hp
    obtain ⟨t, ht⟩ := hq
    refine ⟨t, ?_⟩
    change cuspToCarrier (cuspEnd b t) = p
    rw [ht]
    exact Subtype.ext rfl

theorem cusp_internal_eq :
    range (fun t => cuspPiece.map (cuspEnd true t)) =
      {p | p ∈ cuspNear ∧ cuspDefiner p = 0} := by
  rw [cuspEnd_map_range true]
  ext p
  constructor
  · intro hp
    have hh : height p = -(1 / 4 : ℝ) := hp
    refine ⟨?_, ?_⟩
    · change -(3 / 8 : ℝ) < height p ∧ height p < -(1 / 8 : ℝ)
      rw [hh]
      constructor <;> norm_num
    · exact sub_eq_zero.mpr hh.symm
  · intro hp
    exact (sub_eq_zero.mp hp.2).symm

def radialCuspCores : Assembly.FC39P0.CuspCores carrier boundary where
  ports := boundary_exhausted
  piece := fun _ => cuspPiece
  product := fun _ => cuspPieceProduct
  external_end := by
    intro b t
    have hb : b = 0 := Subsingleton.elim b 0
    subst b
    exact cuspEnd_map_false t
  collar_owned := by
    intro b p hp
    have hb : b = 0 := Subsingleton.elim b 0
    subst b
    change p ∈ range cuspToCarrier
    rw [cuspToCarrier_range]
    have hh := collar_target_height hp
    change -(1 / 4 : ℝ) ≤ height p
    linarith
  collar_closure_off := by
    intro b
    have hb : b = 0 := Subsingleton.elim b 0
    subst b
    change Disjoint (closure (boundary.collar 0).target)
      (range fun t => cuspPiece.map (cuspEnd true t))
    rw [cuspEnd_map_range true]
    exact collar_closure_off_internal
  disjoint := by
    intro b b' hne
    exact (hne (Subsingleton.elim b b')).elim
  cuspFn := fun _ => cuspDefiner
  near := fun _ => cuspNear
  near_interior := fun _ => cuspNear_interior
  fn_smooth := fun _ => cuspDefiner_smooth.contMDiffOn
  fn_regular := fun _ x => Function.const (x ∈ cuspNear) (cuspDefiner_regular x)
  internal_eq := fun _ => cusp_internal_eq
  near_eq := fun _ => cusp_near_eq
  internalModelFace := fun _ => cuspModelFace true
  internalModelFace_eq := fun _ => rfl
  externalModelFace := fun _ => cuspModelFace false
  externalModelFace_eq := fun _ => rfl
  modelFace_cases := fun _ F => (cuspModelFace_cases F).elim Or.inr Or.inl

theorem radialCuspCores_piece : radialCuspCores.piece 0 = cuspPiece := rfl

theorem radialCuspCores_product : radialCuspCores.product 0 = cuspPieceProduct := rfl

end GC.GraphManifold.Assembly.FC39P0.X135Radial
