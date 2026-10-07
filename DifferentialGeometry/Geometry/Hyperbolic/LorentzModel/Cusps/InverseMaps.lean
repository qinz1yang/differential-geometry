/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Cusps.MatchedTruncations

noncomputable section

open DifferentialGeometry.ProjectiveOrthogonalGroup

namespace DifferentialGeometry.MatchedCusps

open Hyperbolic HyperbolicAction HyperbolicBoundary CuspCrossSections CuspMaps

variable {n : ℕ} {hn : 1 ≤ n} {Γ Λ : Subgroup (PO n 1)} {f : Γ ≃* Λ} {r : ℝ}

structure InverseLocalData (T : MatchedTruncation hn Γ Λ f r) (η : T.target.centers) where
  sourceCenter : T.source.centers
  center_eq : T.centersEquiv sourceCenter = η
  iso : endStabilizer hn Λ {η.val} ≃* endStabilizer hn Γ {sourceCenter.val}
  coe_iso : ∀ g : endStabilizer hn Λ {η.val},
    (iso g : PO n 1) = (f.symm ⟨g, g.property.1⟩ : PO n 1)
  map : CuspMap hn iso η.val sourceCenter.val
  inverse_eq : map.toEquiv = (T.cuspMap sourceCenter).toEquiv.symm
  level_match : T.source.level sourceCenter = T.target.level η + map.shift

theorem exists_inverseLocalData (T : MatchedTruncation hn Γ Λ f r) (η : T.target.centers) :
    Nonempty (InverseLocalData T η) := by
  obtain ⟨i, rfl⟩ := T.centersEquiv.surjective η
  refine ⟨
    { sourceCenter := i
      center_eq := rfl
      iso := (T.peripheralIso i).symm
      coe_iso := ?_
      map := (T.cuspMap i).symm
      inverse_eq := rfl
      level_match := ?_ }⟩
  · intro g
    have he := T.peripheralIso_coe i ((T.peripheralIso i).symm g)
    rw [MulEquiv.apply_symm_apply] at he
    have he' : f ⟨(T.peripheralIso i).symm g, ((T.peripheralIso i).symm g).property.1⟩ =
        ⟨g, g.property.1⟩ := Subtype.ext he.symm
    have hi := congrArg f.symm he'
    rw [MulEquiv.symm_apply_apply] at hi
    exact congrArg (fun x : Γ => (x : PO n 1)) hi
  · change T.source.level i = T.target.level (T.centersEquiv i) + -(T.cuspMap i).shift
    rw [T.level_match]
    ring

def inverseLocalData (T : MatchedTruncation hn Γ Λ f r) (η : T.target.centers) :
    InverseLocalData T η := Classical.choice (exists_inverseLocalData T η)

theorem inverseLocalData_center_eq (T : MatchedTruncation hn Γ Λ f r) (η : T.target.centers) :
    (inverseLocalData T η).sourceCenter = T.centersEquiv.symm η :=
  T.centersEquiv.injective ((inverseLocalData T η).center_eq.trans
    (T.centersEquiv.apply_symm_apply η).symm)

def inverseCentersEquiv (T : MatchedTruncation hn Γ Λ f r) :
    T.target.centers ≃ T.source.centers where
  toFun η := (inverseLocalData T η).sourceCenter
  invFun := T.centersEquiv
  left_inv η := (inverseLocalData T η).center_eq
  right_inv i := T.centersEquiv.injective (inverseLocalData T (T.centersEquiv i)).center_eq

def MatchedTruncation.symm (T : MatchedTruncation hn Γ Λ f r) :
    MatchedTruncation hn Λ Γ f.symm r where
  source := T.target
  target := T.source
  centersEquiv := inverseCentersEquiv T
  peripheralIso := fun η => (inverseLocalData T η).iso
  peripheralIso_coe := fun η => (inverseLocalData T η).coe_iso
  cuspMap := fun η => (inverseLocalData T η).map
  level_match := fun η => (inverseLocalData T η).level_match

theorem MatchedTruncation.symm_cuspMap (T : MatchedTruncation hn Γ Λ f r)
    (η : T.target.centers) :
    (T.symm.cuspMap η).toEquiv = (T.cuspMap (T.centersEquiv.symm η)).toEquiv.symm :=
  (inverseLocalData T η).inverse_eq.trans
    (congrArg (fun i => (T.cuspMap i).toEquiv.symm) (inverseLocalData_center_eq T η))

end DifferentialGeometry.MatchedCusps
