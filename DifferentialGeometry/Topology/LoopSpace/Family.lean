import DifferentialGeometry.Topology.LoopSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.ProperSpace.Real










noncomputable section

open ContinuousMap

namespace DifferentialGeometry.Topology


abbrev familySphere := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1


abbrev loopFamilyClass (Q : Type*) [TopologicalSpace Q] :=
  ZerothHomotopy C(familySphere, contractibleLoop Q)

namespace LoopFamily

variable {P Q R K : Type*} [TopologicalSpace P] [TopologicalSpace Q]
  [TopologicalSpace R] [TopologicalSpace K]


def classOf (Γ : C(familySphere, contractibleLoop Q)) : loopFamilyClass Q := .mk Γ


theorem classOf_eq_iff (Γ Δ : C(familySphere, contractibleLoop Q)) :
    classOf Γ = classOf Δ ↔ Γ.Homotopic Δ := by
  change Quotient.mk _ Γ = Quotient.mk _ Δ ↔ _
  rw [Quotient.eq]
  exact (DifferentialGeometry.Topology.homotopic_iff_joined Γ Δ).symm



theorem exists_representative (ξ : loopFamilyClass Q) :
    ∃ Γ : C(familySphere, contractibleLoop Q), classOf Γ = ξ :=
  ZerothHomotopy.mk_surjective ξ


def postcompose (f : C(P, Q)) : loopFamilyClass P → loopFamilyClass Q :=
  ZerothHomotopy.lift (fun Γ => classOf ((ContractibleLoop.postcompose f).comp Γ))
    (fun {_ _} p => ZerothHomotopy.sound (p.map (continuous_postcomp (ContractibleLoop.postcompose f))))

@[simp] theorem postcompose_classOf (f : C(P, Q)) (Γ : C(familySphere, contractibleLoop P)) :
    postcompose f (classOf Γ) = classOf ((ContractibleLoop.postcompose f).comp Γ) := rfl

@[simp] theorem postcompose_id (ξ : loopFamilyClass Q) : postcompose (.id Q) ξ = ξ := by
  induction ξ using ZerothHomotopy.rec with
  | mk Γ => rfl

theorem postcompose_comp (g : C(Q, R)) (f : C(P, Q)) (ξ : loopFamilyClass P) :
    postcompose (g.comp f) ξ = postcompose g (postcompose f ξ) := by
  induction ξ using ZerothHomotopy.rec with
  | mk Γ => rfl


def constants (f : C(K, Q)) : C(K, contractibleLoop Q) := ContractibleLoop.constants.comp f




theorem constants_nullhomotopic_iff (f : C(K, Q)) : (constants f).Nullhomotopic ↔ f.Nullhomotopic := by
  constructor
  · rintro ⟨γ, hγ⟩
    exact ⟨ContractibleLoop.evaluation γ,
      (ContinuousMap.Homotopic.refl ContractibleLoop.evaluation).comp hγ⟩
  · exact fun hf => hf.comp_right ContractibleLoop.constants


def nullClass (q : Q) : loopFamilyClass Q :=
  classOf (.const familySphere (ContractibleLoop.constants q))

@[simp] theorem postcompose_nullClass (f : C(P, Q)) (p : P) :
    postcompose f (nullClass p) = nullClass (f p) := rfl


theorem nullClass_eq [PathConnectedSpace Q] (q r : Q) : nullClass q = nullClass r := by
  apply (classOf_eq_iff _ _).mpr
  exact ⟨((PathConnectedSpace.somePath q r).map ContractibleLoop.constants.continuous).toHomotopyConst⟩

end LoopFamily

end DifferentialGeometry.Topology
