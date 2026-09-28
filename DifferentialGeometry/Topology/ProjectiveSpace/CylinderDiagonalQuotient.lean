import DifferentialGeometry.Topology.ProjectiveSpace.SphereAntipodalQuotient
import DifferentialGeometry.Topology.ProjectiveSpace.CylinderQuotient

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

local notation "SphereTwo" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
local notation "Cylinder" => SphereTwo × ℝ

abbrev cylinderDiagonalSetoid : Setoid Cylinder :=
  MulAction.orbitRel Geometry.cylinderDiagonalGroup Cylinder

abbrev CylinderDiagonalQuotient := Geometry.CylinderDiagonalQuotient

namespace CylinderDiagonalQuotient

def proj : Cylinder → CylinderDiagonalQuotient := Geometry.cylinderDiagonalQuotientMap

theorem proj_eq_iff (p q : Cylinder) : proj p = proj q ↔ q = p ∨ q = (-p.1, -p.2) := by
  change Geometry.cylinderDiagonalQuotientMap p = Geometry.cylinderDiagonalQuotientMap q ↔ _
  rw [eq_comm, Geometry.cylinderDiagonalQuotientMap_eq_iff]
  rfl

theorem continuous_proj : Continuous proj :=
  Geometry.cylinderDiagonalQuotientMap_isLocalDiffeomorph.contMDiff.continuous

theorem surjective_proj : Function.Surjective proj :=
  Geometry.cylinderDiagonalQuotientMap_surjective

theorem isOpenMap_proj : IsOpenMap proj :=
  Geometry.cylinderDiagonalQuotientMap_isLocalDiffeomorph.isOpenMap

theorem exists_homeomorph {M : Type*} [TopologicalSpace M]
    (pi : Cylinder → M) (hcontinuous : Continuous pi) (hopen : IsOpenMap pi)
    (hsurjective : Function.Surjective pi)
    (hfibres : ∀ p q : Cylinder, pi p = pi q ↔ q = p ∨ q = (-p.1, -p.2)) :
    ∃ d : CylinderDiagonalQuotient ≃ₜ M, ∀ p : Cylinder, d (proj p) = pi p := by
  let f : C(Cylinder, M) := ⟨pi, hcontinuous⟩
  have hquotient : _root_.Topology.IsQuotientMap f :=
    hopen.isQuotientMap hcontinuous hsurjective
  have hker (p q : Cylinder) : cylinderDiagonalSetoid p q ↔ Setoid.ker f p q := by
    have hproj : cylinderDiagonalSetoid p q ↔ proj p = proj q :=
      ⟨Quotient.sound, Quotient.exact⟩
    exact hproj.trans ((proj_eq_iff p q).trans (hfibres p q).symm)
  let e : CylinderDiagonalQuotient ≃ₜ Quotient (Setoid.ker f) :=
    Homeomorph.Quotient.congrRight hker
  exact ⟨e.trans hquotient.homeomorph, fun _ => rfl⟩

end CylinderDiagonalQuotient

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
