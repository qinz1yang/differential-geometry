import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.RadialTorusSlimFaces

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open GC.GraphManifold.Assembly.FC39P0
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0.X135Radial

local instance carrierCharts_SlimCoresX135 :
    ChartedSpace (EuclideanHalfSpace 3) carrier.Carrier := by
  change ChartedSpace (EuclideanHalfSpace 3) solidTorusSet.{0}
  exact inferInstance

local instance carrierSmooth_SlimCoresX135 : IsManifold (𝓡∂ 3) ∞ carrier.Carrier := by
  change IsManifold (𝓡∂ 3) ∞ solidTorusSet.{0}
  exact inferInstance

def radialZeros : ZeroDomains carrier where
  count := 0
  piece := fun i => Fin.elim0 i
  disjoint := fun i => Fin.elim0 i
  ratio := fun i => Fin.elim0 i
  near := fun i => Fin.elim0 i
  near_interior := fun i => Fin.elim0 i
  ratio_smooth := fun i => Fin.elim0 i
  ratio_regular := fun i => Fin.elim0 i
  zero_subset_near := fun i => Fin.elim0 i
  boundary_eq := fun i => Fin.elim0 i
  range_eq := fun i => Fin.elim0 i
  model := fun i => Fin.elim0 i

def slimModel : Assembly.SlimModel slimPiece := .torusInterval slimProduct

def slimLowerDefiner (p : carrier.Carrier) : ℝ := -(1 / 2 : ℝ) - height p

def slimLowerNear : TopologicalSpace.Opens carrier.Carrier :=
  ⟨{p | -(5 / 8 : ℝ) < height p ∧ height p < -(3 / 8 : ℝ)},
    (isOpen_lt continuous_const height_smooth.continuous).inter
      (isOpen_lt height_smooth.continuous continuous_const)⟩

theorem slimLowerNear_interior :
    (slimLowerNear : Set carrier.Carrier) ⊆ carrier.interior := by
  intro p hp
  exact (solidTorus_isInteriorPoint_iff p).mpr (hp.2.trans (by norm_num))

theorem slimLowerDefiner_smooth :
    ContMDiff (𝓡∂ 3) 𝓘(ℝ, ℝ) ∞ slimLowerDefiner := contMDiff_const.sub height_smooth

theorem slimLowerDefiner_regular (p : carrier.Carrier) (hp : slimLowerDefiner p = 0) :
    mfderiv (𝓡∂ 3) 𝓘(ℝ, ℝ) slimLowerDefiner p ≠ 0 := by
  have hh : height p = -(1 / 2 : ℝ) := by
    change -(1 / 2 : ℝ) - height p = 0 at hp
    linarith
  have hreg := carrier_mvfderiv_height_regular p (by rw [hh]; norm_num)
  intro hzero
  have hz : mvfderiv (𝓡∂ 3) slimLowerDefiner p = 0 := by
    simp only [mvfderiv, hzero, ContinuousLinearMap.comp_zero]
  change mvfderiv (𝓡∂ 3) (fun p => -(1 / 2 : ℝ) - height p) p = 0 at hz
  rw [mvfderiv_fun_sub (g := fun _ => -(1 / 2 : ℝ)) (g' := height)
    mdifferentiableAt_const (height_smooth.mdifferentiableAt (by simp)),
    mvfderiv_const, zero_sub] at hz
  exact hreg (neg_eq_zero.mp hz)

theorem slimLower_near_eq : range slimPiece.map ∩ slimLowerNear =
    {p | p ∈ slimLowerNear ∧ slimLowerDefiner p ≤ 0} := by
  change range slimToCarrier ∩ slimLowerNear =
    {p | p ∈ slimLowerNear ∧ slimLowerDefiner p ≤ 0}
  rw [slimToCarrier_range]
  ext p
  change ((-(1 / 2 : ℝ) ≤ height p ∧ height p ≤ -(1 / 4 : ℝ)) ∧
    (-(5 / 8 : ℝ) < height p ∧ height p < -(3 / 8 : ℝ))) ↔
    ((-(5 / 8 : ℝ) < height p ∧ height p < -(3 / 8 : ℝ)) ∧
      -(1 / 2 : ℝ) - height p ≤ 0)
  constructor
  · intro hp
    exact ⟨hp.2, by linarith [hp.1.1]⟩
  · intro hp
    exact ⟨⟨by linarith [hp.2], by linarith [hp.1.2]⟩, hp.1⟩

theorem slimEnd_map_range (b : Bool) :
    range (fun t => slimToCarrier (slimEnd b t)) =
      {p | height p = if b then -(1 / 2 : ℝ) else -(1 / 4 : ℝ)} := by
  ext p
  constructor
  · rintro ⟨t, rfl⟩
    exact slimEnd_height b t
  · intro hp
    have hband : -(1 / 2 : ℝ) ≤ height p ∧ height p ≤ -(1 / 4 : ℝ) := by
      rw [hp]
      cases b <;> norm_num
    let q : slimSet := ⟨p.val, (bandDefiner_nonpos_iff (by norm_num)).mpr hband⟩
    have hq : q ∈ range (slimEnd b) := by
      rw [slimEnd_range]
      exact hp
    obtain ⟨t, ht⟩ := hq
    exact ⟨t, by change slimToCarrier (slimEnd b t) = p; rw [ht]; exact Subtype.ext rfl⟩

theorem slim_cusp_shared : slimPiece.map '' (slimModelFace false).1 =
    cuspPiece.map '' (radialCuspCores.internalModelFace 0).1 := by
  change slimToCarrier '' range (slimEnd false) = cuspToCarrier '' range (cuspEnd true)
  rw [← range_comp, ← range_comp]
  change range (fun t => slimToCarrier (slimEnd false t)) =
    range (fun t => cuspToCarrier (cuspEnd true t))
  rw [slimEnd_map_range]
  change {p | height p = -(1 / 4 : ℝ)} =
    range (fun t => cuspPiece.map (cuspEnd true t))
  rw [cuspEnd_map_range]
  rfl

def radialSlimModel (_ : Fin 1) : Assembly.SlimModel slimPiece := slimModel

def radialSlimKind (e : SlimEnd radialSlimModel) : Option (NeighbourFace radialZeros
    radialCuspCores) :=
  if e.1.2 then none else some (.inr ⟨0, ⟨radialCuspCores.internalModelFace 0, rfl⟩⟩)

theorem radialSlim_new_true (e : {e : SlimEnd radialSlimModel // radialSlimKind e = none}) :
    e.1.1.2 = true := by
  have he := e.property
  cases hb : e.1.1.2
  · simp [radialSlimKind, hb] at he
  · rfl

theorem slimLower_level : slimPiece.map '' slimModelEnd slimModel true =
    {p | p ∈ slimLowerNear ∧ slimLowerDefiner p = 0} := by
  change slimToCarrier '' range (slimEnd true) = _
  rw [← range_comp]
  change range (fun t => slimToCarrier (slimEnd true t)) = _
  rw [slimEnd_map_range]
  ext p
  change (height p = -(1 / 2 : ℝ)) ↔
    ((-(5 / 8 : ℝ) < height p ∧ height p < -(3 / 8 : ℝ)) ∧
      -(1 / 2 : ℝ) - height p = 0)
  constructor
  · intro hp
    rw [hp]
    norm_num
  · intro hp
    linarith [hp.2]

def radialSlims : SlimPiecesV2 carrier radialZeros radialCuspCores where
  count := 1
  piece := fun _ => slimPiece
  model := radialSlimModel
  disjoint := by
    intro j j' hne
    exact (hne (Subsingleton.elim j j')).elim
  endFace := fun e => slimModelFace e.1.2
  endFace_eq := fun _ => rfl
  endFace_exhausted := by
    intro j F
    rcases slimModelFace_cases F with hfalse | htrue
    · exact ⟨false, trivial, hfalse.symm⟩
    · exact ⟨true, trivial, htrue.symm⟩
  endKind := radialSlimKind
  endFn := fun _ => slimLowerDefiner
  endNear := fun _ => slimLowerNear
  endNear_interior := fun _ => slimLowerNear_interior
  endFn_smooth := fun _ => slimLowerDefiner_smooth.contMDiffOn
  endFn_regular := fun _ p => Function.const (p ∈ slimLowerNear) (slimLowerDefiner_regular p)
  endFn_level := by
    intro e
    change slimPiece.map '' slimModelEnd slimModel e.1.1.2 = _
    rw [radialSlim_new_true]
    exact slimLower_level
  endFn_eq := fun _ => slimLower_near_eq

end GC.GraphManifold.Assembly.FC39P0.X135Radial
