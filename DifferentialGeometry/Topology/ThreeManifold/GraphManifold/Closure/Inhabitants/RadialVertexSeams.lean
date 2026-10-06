import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.RadialSharedCollar

set_option autoImplicit false
noncomputable section
open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology
namespace GC.GraphManifold.Assembly.FC39P0.X135Radial

def radialVertexIndex : Fin 2 ≃ radialSlims.RowIndex where
  toFun k := if k = 0 then radialCuspRow else radialSlimRow
  invFun i := match i with
    | .inl j => Fin.elim0 j
    | .inr (.inl _) => 0
    | .inr (.inr _) => 1
  left_inv k := by fin_cases k <;> rfl
  right_inv i := by
    rcases i with j | b | j
    · exact Fin.elim0 j
    · have hb : b = (0 : Fin 1) := Subsingleton.elim _ _
      subst b
      rfl
    · have hj : j = (0 : Fin 1) := @Subsingleton.elim (Fin 1) inferInstance j 0
      subst j
      rfl

def radialVertices : VertexLayer carrier where
  vertexCount := 2
  vertex k := radialRows.rowVertex (radialVertexIndex k)

def radialVertexLink : VertexModelLink radialRows radialVertices where
  index := radialVertexIndex
  vertex_eq _ := rfl

def radialPorts : PortLayer carrier boundary radialVertices where
  external_exhausted := boundary_exhausted
  externalOwner _ := (0 : Fin 2)
  external_owned i := by
    change (boundary.collar i).target ⊆ range cuspToCarrier
    exact radialCuspCores.collar_owned i

theorem radial_port_model : PortModelLink radialRows radialVertexLink radialPorts where
  owner_index i := by
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    subst i
    rfl

def radialSeams : SeamLayer carrier radialVertices radialCircleRegion where
  torusSeamCount := 1
  torusSeam _ := radialTorusSeam
  torusSide _ b := some (if b then (1 : Fin 2) else (0 : Fin 2))
  torusSide_neg c t s hlo hhi := by
    change radialSharedCollar (t, s) ∈ range slimToCarrier
    rw [slimToCarrier_range]
    have hs : (t, s) ∈ signedCollarSource := ⟨hlo, by linarith⟩
    have hh := radialSharedCollar_height (t, s) hs
    change -(1 / 2 : ℝ) ≤ height (radialSharedCollar (t, s)) ∧
      height (radialSharedCollar (t, s)) ≤ -(1 / 4 : ℝ)
    constructor <;> linarith
  torusSide_pos c t s hlo hhi := by
    change radialSharedCollar (t, s) ∈ range cuspToCarrier
    rw [cuspToCarrier_range]
    have hs : (t, s) ∈ signedCollarSource := ⟨by linarith, hhi⟩
    have hh := radialSharedCollar_height (t, s) hs
    change -(1 / 4 : ℝ) ≤ height (radialSharedCollar (t, s))
    linarith
  torusSeam_disjoint c d hn := (hn (Subsingleton.elim c d)).elim
  sphereSeamCount := 0
  sphereSeam c := Fin.elim0 c
  sphereSide c := Fin.elim0 c
  sphereSide_neg c := Fin.elim0 c
  sphereSide_pos c := Fin.elim0 c
  sphereSeam_disjoint c := Fin.elim0 c
  sphere_torus_seam_disjoint c := Fin.elim0 c

end GC.GraphManifold.Assembly.FC39P0.X135Radial
