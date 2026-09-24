import DifferentialGeometry.Topology.ThreeManifold.CoreBoundaryCollar
import DifferentialGeometry.Topology.ThreeManifold.RadialTube
import DifferentialGeometry.Topology.Manifold.SphereCollarCoordinates

noncomputable section

open Set Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.SphericalCapping

universe u
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "S2" => Metric.sphere (0 : E3) 1
local notation "Half" => Ico (0 : ℝ) (1 / 2)

local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩
local instance : Fact ((-2 : ℝ) < 2) := ⟨by norm_num⟩

variable {M N : ClosedOrientedManifold.{u} 3} {T : SphericalTubeSystem M}
  (C : SphericalCapping M N T) (b : T.Boundary)

def coreBoundaryExtension
    (e : SmoothTwoSidedCollar (𝓡 2) (𝓡 3) (C.cap b ∘ sphereToClosedCell)) (v : S2) :
    N.Carrier → M.Carrier :=
  (T.radialTube b.1 (C.attaching b) b.2 v) ∘ (e.reverse.radialPartialDiffeomorph v).symm

theorem isLocalDiffeomorphAt_coreBoundaryExtension
    (e : SmoothTwoSidedCollar (𝓡 2) (𝓡 3) (C.cap b ∘ sphereToClosedCell)) (v z : S2) :
    IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ (coreBoundaryExtension C b e v)
      (C.cap b (sphereToClosedCell z)) := by
  let P := e.reverse.radialPartialDiffeomorph v
  have hz : z.val ∈ P.source := e.reverse.sphere_subset_radialPartialDiffeomorph_source v z.property
  have hPz : P z.val = C.cap b (sphereToClosedCell z) := e.reverse.radialPartialDiffeomorph_sphere v z
  have hlocal := P.symm.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ (hPz ▸ P.map_source hz)
  have hsymm : P.symm (C.cap b (sphereToClosedCell z)) = z.val :=
    hPz ▸ P.left_inv hz
  have ht := T.isLocalDiffeomorphAt_radialTube b.1 (C.attaching b) b.2 v
    (by rw [norm_eq_of_mem_sphere]; norm_num : 0 < ‖z.val‖)
    (by rw [norm_eq_of_mem_sphere]; norm_num : ‖z.val‖ < 2)
  exact hlocal.comp (𝓡 3) M.Carrier (hsymm ▸ ht)

theorem coreBoundaryExtension_radial
    (e : SmoothTwoSidedCollar (𝓡 2) (𝓡 3) (C.cap b ∘ sphereToClosedCell)) (v : S2)
    (x : E3) (hx : x ∈ (e.reverse.radialPartialDiffeomorph v).source) :
    C.coreBoundaryExtension b e v (e.reverse.radialPartialDiffeomorph v x) =
      T.radialTube b.1 (C.attaching b) b.2 v x := by
  change T.radialTube b.1 (C.attaching b) b.2 v
    ((e.reverse.radialPartialDiffeomorph v).symm (e.reverse.radialPartialDiffeomorph v x)) = _
  exact congrArg (T.radialTube b.1 (C.attaching b) b.2 v)
    ((e.reverse.radialPartialDiffeomorph v).left_inv hx)

private theorem coreBoundaryExtension_core
    (e : SmoothTwoSidedCollar (𝓡 2) (𝓡 3) (C.cap b ∘ sphereToClosedCell)) (v : S2)
    (he : e.radius ≤ 1 / 2)
    (heq : ∀ (p : S2 × symmetricOpenInterval e.radius) (hp : 0 ≤ p.2.val),
      e.toFun p = C.coreInclusionHalfCollar b
        (p.1, ⟨p.2.val, hp, p.2.property.2.trans_le he⟩))
    (q : S2 × Half) (hq : q.2.val < e.radius) :
    coreBoundaryExtension C b e v (C.coreInclusionHalfCollar b q) =
      (C.coreBoundaryHalfCollar b q).val := by
  let p : S2 × symmetricOpenInterval e.radius :=
    (q.1, ⟨q.2.val, by constructor <;> linarith [q.2.property.1, e.radius_pos]⟩)
  have hp : e.toFun p = C.coreInclusionHalfCollar b q := heq p q.2.property.1
  have ht : 1 - (1 + q.2.val) ∈ Ioo (-e.reverse.radius) e.reverse.radius := by
    change -e.radius < 1 - (1 + q.2.val) ∧ 1 - (1 + q.2.val) < e.radius
    constructor <;> linarith [e.radius_pos, q.2.property.1]
  have hrad : e.reverse.radialPartialDiffeomorph v ((1 + q.2.val) • q.1.val) = e.toFun p := by
    rw [e.reverse.radialPartialDiffeomorph_apply v q.1 (1 + q.2.val) (by linarith [q.2.property.1]) ht]
    erw [e.reverse_toFun]
    apply congrArg e.toFun
    apply Prod.ext
    · rfl
    · apply Subtype.ext; dsimp [p]; ring
  have hsrc := e.reverse.mem_radialPartialDiffeomorph_source v q.1 (1 + q.2.val)
    (by linarith [q.2.property.1]) ht
  have hsymm : (e.reverse.radialPartialDiffeomorph v).symm (C.coreInclusionHalfCollar b q) =
      (1 + q.2.val) • q.1.val := by
    rw [← hp, ← hrad]
    exact (e.reverse.radialPartialDiffeomorph v).left_inv hsrc
  change T.radialTube b.1 (C.attaching b) b.2 v _ = _
  rw [hsymm]
  have hn : ‖(1 + q.2.val) • q.1.val‖ = 1 + q.2.val := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith [q.2.property.1]), norm_eq_of_mem_sphere, mul_one]
  rw [T.radialTube_apply b.1 (C.attaching b) b.2 v (by rw [hn]; linarith [q.2.property.2]),
    Manifold.sphereDirection_pos_smul v q.1 (by linarith [q.2.property.1]),
    C.coreBoundaryHalfCollar_val]
  apply congrArg (T.tube b.1)
  apply Prod.ext
  · rfl
  apply Subtype.ext
  change (if b.2 then ‖(1 + q.2.val) • q.1.val‖ else -‖(1 + q.2.val) • q.1.val‖) =
    (SphericalTubeSystem.coreCollarParameter b.2 q.2).val
  rw [SphericalTubeSystem.coreCollarParameter_val, hn]
  cases b.2 <;> simp [SphericalTubeSystem.boundaryLevel]
  ring

theorem exists_capBoundary_extension (v : S2) :
    ∃ (G : N.Carrier → M.Carrier) (ε : ℝ), 0 < ε ∧ ε ≤ 1 / 2 ∧
      (∀ z : S2, IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ G (C.cap b (sphereToClosedCell z))) ∧
      ∀ q : S2 × Half, q.2.val < ε →
        G (C.coreInclusionHalfCollar b q) = (C.coreBoundaryHalfCollar b q).val := by
  obtain ⟨e, he, heq⟩ := C.exists_coreBoundaryCollar b
  exact ⟨coreBoundaryExtension C b e v, e.radius, e.radius_pos, he,
    isLocalDiffeomorphAt_coreBoundaryExtension C b e v,
    coreBoundaryExtension_core C b e v he heq⟩

end DifferentialGeometry.Topology.SphericalCapping
