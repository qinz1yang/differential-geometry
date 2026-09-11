import DifferentialGeometry.Topology.ProjectiveSpace.CylinderDiagonalQuotient
import DifferentialGeometry.Topology.Manifold.Involution.QuotientProjection
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Set Manifold
open scoped ContDiff

local notation "SphereTwo" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
local notation "SphereI" => 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))
local notation "Cylinder" => SphereTwo × ℝ
local notation "CylinderI" => ModelWithCorners.prod 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, ℝ)

private local instance cylinderQuotientSmoothDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

def sphereAntipodalDiffeomorph : SphereTwo ≃ₘ⟮SphereI, SphereI⟯ SphereTwo where
  toEquiv := {
    toFun := fun x => -x
    invFun := fun x => -x
    left_inv := neg_neg
    right_inv := neg_neg }
  contMDiff_toFun := contMDiff_neg_sphere (n := 2) (m := ∞)
  contMDiff_invFun := contMDiff_neg_sphere (n := 2) (m := ∞)

theorem sphereAntipodalDiffeomorph_ne_self (x : SphereTwo) :
    sphereAntipodalDiffeomorph x ≠ x := by
  intro h
  have hzero : (x : EuclideanSpace ℝ (Fin 3)) = 0 := by
    ext i
    have hi := congrArg (fun y : SphereTwo => (y : EuclideanSpace ℝ (Fin 3)) i) h
    change -(x : EuclideanSpace ℝ (Fin 3)) i = (x : EuclideanSpace ℝ (Fin 3)) i at hi
    change (x : EuclideanSpace ℝ (Fin 3)) i = 0
    linarith
  have hnorm : ‖(x : EuclideanSpace ℝ (Fin 3))‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using x.property
  rw [hzero, norm_zero] at hnorm
  norm_num at hnorm

private def cylinderLineNegation : ℝ ≃ₘ[ℝ] ℝ where
  toEquiv := {
    toFun := fun s => -s
    invFun := fun s => -s
    left_inv := neg_neg
    right_inv := neg_neg }
  contMDiff_toFun := contDiff_neg.contMDiff
  contMDiff_invFun := contDiff_neg.contMDiff

def cylinderDiagonalDiffeomorph : Cylinder ≃ₘ⟮CylinderI, CylinderI⟯ Cylinder :=
  sphereAntipodalDiffeomorph.prodCongr cylinderLineNegation

theorem cylinderDiagonalDiffeomorph_ne_self (p : Cylinder) :
    cylinderDiagonalDiffeomorph p ≠ p := by
  intro h
  exact sphereAntipodalDiffeomorph_ne_self p.1 (congrArg Prod.fst h)

private theorem twoPointQuotient_t2Space
    {X Q : Type*} [TopologicalSpace X] [T2Space X] [TopologicalSpace Q]
    (tau : X → X) (htau : Continuous tau) (pi : X → Q)
    (hlocal : IsLocalHomeomorph pi) (hsurj : Function.Surjective pi)
    (hfibres : ∀ x y : X, pi x = pi y ↔ y = x ∨ y = tau x) : T2Space Q := by
  have hopen : IsOpenQuotientMap pi := ⟨hsurj, hlocal.continuous, hlocal.isOpenMap⟩
  apply (t2Space_iff_of_isOpenQuotientMap hopen).mpr
  have hrel : {p : X × X | pi p.1 = pi p.2} =
      {p : X × X | p.2 = p.1} ∪ {p : X × X | p.2 = tau p.1} := by
    ext p
    exact hfibres p.1 p.2
  rw [hrel]
  exact (isClosed_eq continuous_snd continuous_fst).union
    (isClosed_eq continuous_snd (htau.comp continuous_fst))

namespace SphereAntipodalQuotient

theorem isLocalHomeomorph_proj : IsLocalHomeomorph proj :=
  isLocalHomeomorph_of_free_two_point_fibres sphereAntipodalDiffeomorph
    sphereAntipodalDiffeomorph.continuous sphereAntipodalDiffeomorph_ne_self
    proj continuous_proj isOpenMap_proj proj_eq_iff

instance instChartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin 2)) SphereAntipodalQuotient :=
  isLocalHomeomorph_proj.chartedSpace surjective_proj

instance instIsManifold : IsManifold SphereI ∞ SphereAntipodalQuotient :=
  involutionQuotient_isManifold sphereAntipodalDiffeomorph
    sphereAntipodalDiffeomorph_ne_self proj proj_eq_iff isLocalHomeomorph_proj surjective_proj

instance instT2Space : T2Space SphereAntipodalQuotient :=
  twoPointQuotient_t2Space sphereAntipodalDiffeomorph sphereAntipodalDiffeomorph.continuous
    proj isLocalHomeomorph_proj surjective_proj proj_eq_iff

theorem isLocalDiffeomorph_proj : IsLocalDiffeomorph SphereI SphereI ∞ proj :=
  involutionQuotient_projection_isLocalDiffeomorph sphereAntipodalDiffeomorph
    sphereAntipodalDiffeomorph_ne_self proj proj_eq_iff isLocalHomeomorph_proj surjective_proj

end SphereAntipodalQuotient

namespace CylinderDiagonalQuotient

theorem isLocalHomeomorph_proj : IsLocalHomeomorph proj :=
  isLocalHomeomorph_of_free_two_point_fibres cylinderDiagonalDiffeomorph
    cylinderDiagonalDiffeomorph.continuous cylinderDiagonalDiffeomorph_ne_self
    proj continuous_proj isOpenMap_proj proj_eq_iff

instance instChartedSpace :
    ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin 2)) ℝ) CylinderDiagonalQuotient :=
  isLocalHomeomorph_proj.chartedSpace surjective_proj

instance instIsManifold : IsManifold CylinderI ∞ CylinderDiagonalQuotient :=
  involutionQuotient_isManifold cylinderDiagonalDiffeomorph
    cylinderDiagonalDiffeomorph_ne_self proj proj_eq_iff isLocalHomeomorph_proj surjective_proj

instance instT2Space : T2Space CylinderDiagonalQuotient :=
  twoPointQuotient_t2Space cylinderDiagonalDiffeomorph cylinderDiagonalDiffeomorph.continuous
    proj isLocalHomeomorph_proj surjective_proj proj_eq_iff

theorem isLocalDiffeomorph_proj : IsLocalDiffeomorph CylinderI CylinderI ∞ proj :=
  involutionQuotient_projection_isLocalDiffeomorph cylinderDiagonalDiffeomorph
    cylinderDiagonalDiffeomorph_ne_self proj proj_eq_iff isLocalHomeomorph_proj surjective_proj

end CylinderDiagonalQuotient

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
