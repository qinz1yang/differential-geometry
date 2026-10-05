import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.SphereCutFactorMaps
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.PlugSideCapping

/-!
The original plug cut supplies the actual factor inclusions and the original reindexed ports.
Their positive fold and exclusive port ownership feed the same final two-port quotient.
-/

set_option autoImplicit false
noncomputable section
open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Seifert
open scoped Manifold ContDiff Topology
universe u
namespace GC.Seifert.ElementaryPresentation
open SplitTube

variable {W : CompactCarrier.{u}} (E : ElementaryPresentation W)
  {j : Fin E.toTorus.pairing.count} {b : Bool} (h : E.IsSplitSeam j b)
  (hlin : E.IsLinearSeam j)
  (d : PartialDiffeomorph sphereSignedCollarModel W.model
    (ClosureSphere.{u} × ℝ) W.Carrier ∞) (hs : d.source = sphereSignedCollarSource)
  (hI : d.target ⊆ W.interior)
  (heq : ∀ z s, d (z, s) = E.boundedSplitTubeMap h hlin (z.down, s))
  (hc : E.toTorus.components.count = 2) (hn : E.toTorus.pairing.count = 1)
  {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
  (havρ : ∀ r, Disjoint ((E.toTorus.external.shrink hρ hρ1).collar r).target d.target)

local notation "c₀" => boundedPlugCutCollars d
local notation "hs₀" => boundedPlugCutCollars_source d hs
local notation "hd₀" => boundedPlugCutCollars_disjoint d
local notation "D₀" => E.fibrePlugCutComponents h hlin hc hn d hs heq
local notation "Cᵢ" i => E.plugComponentCutCarrier h hlin d hs heq hc hn i
local notation "Bᵢ" i => E.plugSideBoundary h hlin d hs hI heq hc hn hρ hρ1 havρ i
local notation "B₀" => E.fibrePlugCutBoundary d hs hρ hρ1 hI havρ

def plugCutFactor (i : Fin 2) : C((Cᵢ i).Carrier, W.Carrier) :=
  ⟨fun x => sphereCutFold (c₀) x.val,
    (sphereCutFold_continuous (c₀)).comp continuous_subtype_val⟩

def plugCutFactorZero (i : Fin 2) (z : ClosureSphere.{u}) : (Cᵢ i).Carrier :=
  ⟨sphereCutZero (c₀) 0 (sphereCutBoundarySide i) z,
    (E.fibrePlugCutComponents_zero_mem h hlin hc hn d hs heq
      i (sphereCutBoundarySide i) z).mpr rfl⟩

def plugCutBoundaryPorts : BoundaryTori W 2 where
  collar i := (E.toTorus.external.shrink hρ hρ1).collar (E.fibrePlugCutPortEquiv h hc hn i)
  source_eq i := (E.toTorus.external.shrink hρ hρ1).source_eq (E.fibrePlugCutPortEquiv h hc hn i)
  boundary_zero i := (E.toTorus.external.shrink hρ hρ1).boundary_zero
    (E.fibrePlugCutPortEquiv h hc hn i)
  disjoint i k hik := @BoundaryTori.disjoint W E.toTorus.externalCount
    (E.toTorus.external.shrink hρ hρ1) (E.fibrePlugCutPortEquiv h hc hn i)
    (E.fibrePlugCutPortEquiv h hc hn k)
    (fun he => hik ((E.fibrePlugCutPortEquiv h hc hn).injective he))

theorem plugCutFactor_injective (i : Fin 2) :
    Injective (E.plugCutFactor h hlin d hs heq hc hn i) := by
  intro x y hxy
  rcases (sphereCutFold_fibre_relation (c₀) (hs₀) (hd₀) x.val y.val).mp hxy with
    he | ⟨z, hz | hz⟩
  · exact Subtype.ext he
  · have hx := x.property
    have hy := y.property
    rw [hz.1] at hx
    rw [hz.2] at hy
    have hx' := (E.fibrePlugCutComponents_zero_mem h hlin hc hn d hs heq i false z).mp hx
    have hy' := (E.fibrePlugCutComponents_zero_mem h hlin hc hn d hs heq i true z).mp hy
    exact (Bool.false_ne_true (hx'.trans hy'.symm)).elim
  · have hx := x.property
    have hy := y.property
    rw [hz.1] at hx
    rw [hz.2] at hy
    have hx' := (E.fibrePlugCutComponents_zero_mem h hlin hc hn d hs heq i true z).mp hx
    have hy' := (E.fibrePlugCutComponents_zero_mem h hlin hc hn d hs heq i false z).mp hy
    exact (Bool.false_ne_true (hy'.trans hx'.symm)).elim

section Cross
variable {E h hlin d hs heq hc hn}

theorem plugCutFactor_cross
    {x : (Cᵢ(0 : Fin 2)).Carrier} {y : (Cᵢ(1 : Fin 2)).Carrier} :
    E.plugCutFactor h hlin d hs heq hc hn 0 x = E.plugCutFactor h hlin d hs heq hc hn 1 y ↔
      ∃ z, x = E.plugCutFactorZero h hlin d hs heq hc hn 0 z ∧
        y = E.plugCutFactorZero h hlin d hs heq hc hn 1 z := by
  constructor
  · intro hxy
    rcases (sphereCutFold_fibre_relation (c₀) (hs₀) (hd₀) x.val y.val).mp hxy with
      he | ⟨z, hz | hz⟩
    · exact (disjoint_left.mp ((D₀).disjoint (by decide : (0 : Fin 2) ≠ 1))
        x.property (he.symm ▸ y.property)).elim
    · exact ⟨z, Subtype.ext hz.1, Subtype.ext hz.2⟩
    · have hx := x.property
      rw [hz.1] at hx
      have hf := (E.fibrePlugCutComponents_zero_mem h hlin hc hn d hs heq 0 true z).mp hx
      exact (Bool.false_ne_true hf.symm).elim
  · rintro ⟨z, rfl, rfl⟩
    change sphereCutFold (c₀) (sphereCutZero (c₀) 0 false z) =
      sphereCutFold (c₀) (sphereCutZero (c₀) 0 true z)
    rw [sphereCutZero_fold, sphereCutZero_fold]

end Cross

theorem plugCutFactor_covers (y : W.Carrier) :
    (∃ x, E.plugCutFactor h hlin d hs heq hc hn 0 x = y) ∨
      ∃ x, E.plugCutFactor h hlin d hs heq hc hn 1 x = y := by
  obtain ⟨x, hx⟩ := sphereCut_projection_surjective (c₀) y
  have hm : x ∈ ⋃ i, ((D₀).piece i : Set (boundedPlugCutCarrier d hs).Carrier) :=
    (D₀).covers.symm ▸ mem_univ x
  obtain ⟨i, hi⟩ := mem_iUnion.mp hm
  fin_cases i
  · exact Or.inl ⟨⟨x, hi⟩, hx⟩
  · exact Or.inr ⟨⟨x, hi⟩, hx⟩

theorem plugCutFactor_smooth (i : Fin 2) :
    ContMDiff (Cᵢ i).model W.model ∞ (E.plugCutFactor h hlin d hs heq hc hn i) := by
  have hf : ContMDiff (boundedPlugCutCarrier d hs).model W.model ∞
      (fun x : (boundedPlugCutCarrier d hs).Carrier => sphereCutFold (c₀) x) :=
    sphereCutFold_smooth (c₀) (hs₀) (hd₀)
  have hv : ContMDiff (Cᵢ i).model (boundedPlugCutCarrier d hs).model ∞
      (fun x : (Cᵢ i).Carrier => x.val) :=
    contMDiff_subtype_val (I := (boundedPlugCutCarrier d hs).model) (U := (D₀).piece i)
  exact hf.comp hv

theorem plugCutFactor_positive (i : Fin 2) :
    IsOrientedFold (E.plugCutFactor h hlin d hs heq hc hn i) := by
  have hf : IsOrientedFold (C := boundedPlugCutCarrier d hs) (W := W) (sphereCutFold (c₀)) := by
    intro x
    let := sphereCutChartedSpace (c₀) (hs₀) (hd₀)
    refine ⟨(sphereCutFoldTangentEquiv (c₀) (hs₀) (hd₀) x).toLinearEquiv, ?_,
      sphereCutFold_orientation_map (c₀) (hs₀) (hd₀) x⟩
    intro v
    exact DifferentialGeometry.Topology.Manifold.differentialEquivOfBijective_apply
      (𝓡∂ 3) W.model (sphereCutFold (c₀))
      (sphereCutFold_mfderiv_bijective (c₀) (hs₀) (hd₀)) x v
  exact hf.restrict (sphereCutFold_smooth (c₀) (hs₀) (hd₀)) ((D₀).piece i)

theorem plugCutFactor_collar (i : Fin 2) (p : Torus × EuclideanHalfSpace 1)
    (hp : p ∈ halfCollarSource) :
    E.plugCutFactor h hlin d hs heq hc hn i ((Bᵢ i).tori.collar 0 p) =
      (E.plugCutBoundaryPorts h hc hn hρ hρ1).collar i p := by
  change sphereCutFold (c₀) _ = _
  rw [E.plugSideBoundary_torus_apply h hlin d hs hI heq hc hn hρ hρ1 havρ i p hp]
  exact sphereCutRetainedCollar_fold (c₀) (hs₀) (hd₀)
    (E.toTorus.external.shrink hρ hρ1) (fun r k => havρ r)
    (E.fibrePlugCutPortEquiv h hc hn i) p hp

theorem plugCutFactor_port (i : Fin 2) (t : Torus) :
    E.plugCutFactor h hlin d hs heq hc hn i ((Bᵢ i).tori.torusMap 0 t) =
      (E.plugCutBoundaryPorts h hc hn hρ hρ1).torusMap i t :=
  E.plugCutFactor_collar h hlin d hs hI heq hc hn hρ hρ1 havρ i
    (t, halfZero) (zero_mem_halfCollarSource t)

include hI havρ in
theorem plugCutFactor_port_exclusive (i k : Fin 2) (hik : i ≠ k) (t : Torus) :
    (E.plugCutBoundaryPorts h hc hn hρ hρ1).torusMap i t ∉
      range (E.plugCutFactor h hlin d hs heq hc hn k) := by
  rintro ⟨y, hy⟩
  let a := (B₀).tori.torusMap (E.fibrePlugCutPortEquiv h hc hn i) t
  have ha : sphereCutFold (c₀) a =
      (E.plugCutBoundaryPorts h hc hn hρ hρ1).torusMap i t :=
    sphereCutRetainedCollar_fold (c₀) (hs₀) (hd₀)
      (E.toTorus.external.shrink hρ hρ1) (fun r j => havρ r)
      (E.fibrePlugCutPortEquiv h hc hn i) (t, halfZero) (zero_mem_halfCollarSource t)
  have hoff : (E.plugCutBoundaryPorts h hc hn hρ hρ1).torusMap i t ∉
      sphereCutAmbientZero (c₀) :=
    sphereCutOldPoint_offZero (c₀) (hs₀) (E.toTorus.external.shrink hρ hρ1)
      (fun r j => havρ r) (E.fibrePlugCutPortEquiv h hc hn i)
      (((E.toTorus.external.shrink hρ hρ1).source_eq _).symm.subset
        (zero_mem_halfCollarSource t))
  have hya : y.val = a := by
    rcases (sphereCutFold_fibre_relation (c₀) (hs₀) (hd₀) y.val a).mp
      (hy.trans ha.symm) with he | ⟨z, hz | hz⟩
    · exact he
    · have hz' := congrArg (sphereCutFold (c₀)) hz.1
      rw [sphereCutZero_fold] at hz'
      exact (hoff (mem_iUnion.mpr ⟨0, z, hz'.symm.trans hy⟩)).elim
    · have hz' := congrArg (sphereCutFold (c₀)) hz.1
      rw [sphereCutZero_fold] at hz'
      exact (hoff (mem_iUnion.mpr ⟨0, z, hz'.symm.trans hy⟩)).elim
  have hm : a ∈ (D₀).piece k := hya ▸ y.property
  have hi := (E.fibrePlugCutComponents_torus_mem_iff h hlin hc hn d hs heq hρ hρ1 hI havρ
    (E.fibrePlugCutPortEquiv h hc hn i) k t).mp hm
  exact hik ((E.fibrePlugCutPortEquiv h hc hn).injective hi)

end GC.Seifert.ElementaryPresentation
