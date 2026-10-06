import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.RadialFaceModels

set_option autoImplicit false
noncomputable section
open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology
namespace GC.GraphManifold.Assembly.FC39P0.X135Radial
local instance carrierCharts_FaceLayerX135 :
    ChartedSpace (EuclideanHalfSpace 3) carrier.Carrier := by
  change ChartedSpace (EuclideanHalfSpace 3) solidTorusSet.{0}
  exact inferInstance

def radialFaceHeight (f : Fin 4) : ℝ :=
  if f = 0 then 0 else if f = 3 then -(1 / 2 : ℝ) else -(1 / 4 : ℝ)

def radialFaceSet (f : Fin 4) : Set carrier.Carrier := {p | height p = radialFaceHeight f}

def radialFaceOwner (f : Fin 4) : Fin 2 := if f.val < 2 then 0 else 1

def radialFaceKind (f : Fin 4) : Assembly.FaceKind 1 1 0 :=
  if f = 0 then .external 0 else if f = 1 then .torusSeam 0 false else
    if f = 2 then .torusSeam 0 true else .partitioned

def radialFaceHomeo (f : Fin 4) : radialFaceSet f ≃ₜ Torus := by
  by_cases h0 : f = 0
  · subst f
    exact radialCuspFaceHomeo false
  by_cases h1 : f = 1
  · subst f
    exact radialCuspFaceHomeo true
  by_cases h2 : f = 2
  · subst f
    exact radialSlimFaceHomeo false
  have h3 : f = 3 := by omega
  subst f
  exact radialSlimFaceHomeo true

theorem radialFace_exhausted (k : Fin 2) :
    (⋃ (f : Fin 4) (_ : radialFaceOwner f = k), radialFaceSet f) =
      (radialVertices.vertex k).boundaryImage := by
  fin_cases k
  · apply Eq.trans (b := {p | height p = (0 : ℝ)} ∪
      {p | height p = -(1 / 4 : ℝ)}) ?_ radialCusp_boundary_height.symm
    ext p
    simp only [mem_iUnion, mem_union]
    constructor
    · rintro ⟨f, hf, hp⟩
      fin_cases f
      · exact Or.inl hp
      · exact Or.inr hp
      · norm_num [radialFaceOwner] at hf
      · norm_num [radialFaceOwner] at hf
    · rintro (hp | hp)
      · exact ⟨(0 : Fin 4), rfl, hp⟩
      · exact ⟨(1 : Fin 4), rfl, hp⟩
  · apply Eq.trans (b := {p | height p = -(1 / 4 : ℝ)} ∪
      {p | height p = -(1 / 2 : ℝ)}) ?_ radialSlim_boundary_height.symm
    ext p
    simp only [mem_iUnion, mem_union]
    constructor
    · rintro ⟨f, hf, hp⟩
      fin_cases f
      · norm_num [radialFaceOwner] at hf
      · norm_num [radialFaceOwner] at hf
      · exact Or.inl hp
      · exact Or.inr hp
    · rintro (hp | hp)
      · exact ⟨(2 : Fin 4), rfl, hp⟩
      · exact ⟨(3 : Fin 4), rfl, hp⟩

theorem radialFace_disjoint (f g : Fin 4) (hn : f ≠ g)
    (ht : ∀ c b, ¬ (radialFaceKind f = .torusSeam c b ∧
      radialFaceKind g = .torusSeam c (!b))) : Disjoint (radialFaceSet f) (radialFaceSet g) := by
  fin_cases f <;> fin_cases g
  all_goals first | exact (hn rfl).elim | skip
  all_goals first
    | exact (ht (0 : Fin 1) false ⟨rfl, rfl⟩).elim
    | exact (ht (0 : Fin 1) true ⟨rfl, rfl⟩).elim
    | skip
  all_goals rw [disjoint_left]
  all_goals intro p hp hq
  all_goals norm_num [radialFaceSet, radialFaceHeight] at hp hq
  all_goals linarith

theorem radial_external_range : range (boundary.torusMap (0 : Fin 1)) =
    {p : carrier.Carrier | height p = (0 : ℝ)} := by
  have hi : range (boundary.torusMap (0 : Fin 1)) = boundary.image := by
    ext p
    constructor
    · intro hp
      exact mem_iUnion.mpr ⟨0, hp⟩
    · intro hp
      obtain ⟨i, hi⟩ := mem_iUnion.mp hp
      have he : i = (0 : Fin 1) := Subsingleton.elim _ _
      subst i
      exact hi
  rw [hi, ← boundary_exhausted]
  ext p
  change (𝓡∂ 3).IsBoundaryPoint p ↔ height p = 0
  exact solidTorus_isBoundaryPoint_iff p

def radialFaces : FaceLayer carrier boundary radialVertices radialSeams radialPorts where
  faceCount := 4
  face := radialFaceSet
  faceOwner := radialFaceOwner
  faceModel f := .inr (radialFaceHomeo f)
  face_exhausted := radialFace_exhausted
  faceKind := radialFaceKind
  face_disjoint f g hn _ ht := radialFace_disjoint f g hn ht
  face_external f i hk := by
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    subst i
    fin_cases f
    · exact ⟨radial_external_range.symm, rfl⟩
    · cases hk
    · cases hk
    · cases hk
  external_face i := by
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    subst i
    exact ⟨(0 : Fin 4), rfl⟩
  face_torusSeam f c b hk := by
    have hc : c = (0 : Fin 1) := @Subsingleton.elim (Fin 1) inferInstance c 0
    subst c
    fin_cases f
    · cases hk
    · have hb : b = false := by
        change Assembly.FaceKind.torusSeam (0 : Fin 1) false = .torusSeam 0 b at hk
        injection hk with hindex hbool
        exact hbool.symm
      subst b
      exact ⟨radialSharedCollar_zero.symm, rfl⟩
    · have hb : b = true := by
        change Assembly.FaceKind.torusSeam (0 : Fin 1) true = .torusSeam 0 b at hk
        injection hk with hindex hbool
        exact hbool.symm
      subst b
      exact ⟨radialSharedCollar_zero.symm, rfl⟩
    · cases hk
  torusSeam_face c b k hk := by
    have hc : c = (0 : Fin 1) := @Subsingleton.elim (Fin 1) inferInstance c 0
    subst c
    change some (if b then (1 : Fin 2) else (0 : Fin 2)) = some k at hk
    have he := Option.some.inj hk
    subst k
    cases b
    · exact ⟨(1 : Fin 4), rfl, rfl⟩
    · exact ⟨(2 : Fin 4), rfl, rfl⟩
  face_sphereSeam f c := Fin.elim0 c
  sphereSeam_face c := Fin.elim0 c

end GC.GraphManifold.Assembly.FC39P0.X135Radial
