import DifferentialGeometry.Topology.LoopSpace.Family
import DifferentialGeometry.Analysis.Calculus.Periodic.Affine










noncomputable section

open ContinuousMap Function

namespace DifferentialGeometry.Topology

namespace ContractibleLoop

variable {Q : Type*} [TopologicalSpace Q]


def precompose (ψ : C(loopCircle, loopCircle)) : C(contractibleLoop Q, contractibleLoop Q) :=
  ⟨fun γ => ⟨γ.val.comp ψ, γ.property.comp_left ψ⟩,
    ((continuous_precomp ψ).comp continuous_subtype_val).subtype_mk _⟩

@[simp] theorem precompose_apply (ψ : C(loopCircle, loopCircle))
    (γ : contractibleLoop Q) (θ : loopCircle) :
    (precompose ψ γ).val θ = γ.val (ψ θ) := rfl

@[simp] theorem precompose_id : precompose (Q := Q) (.id loopCircle) = .id _ := rfl


theorem precompose_comp (ψ χ : C(loopCircle, loopCircle)) :
    precompose (Q := Q) (ψ.comp χ) = (precompose χ).comp (precompose ψ) := rfl


@[simp] theorem precompose_constants (ψ : C(loopCircle, loopCircle)) (q : Q) :
    precompose ψ (constants q) = constants q := rfl



def precomposeHomotopy {ψ χ : C(loopCircle, loopCircle)} (H : ψ.Homotopy χ) :
    (precompose (Q := Q) ψ).Homotopy (precompose χ) where
  toFun p := ⟨p.2.val.comp (H.curry p.1), p.2.property.comp_left (H.curry p.1)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_of_continuous_uncurry
    exact continuous_eval.comp
      ((continuous_subtype_val.comp continuous_fst.snd).prodMk
        (H.continuous.comp (continuous_fst.fst.prodMk continuous_snd)))
  map_zero_left γ := by apply Subtype.ext; ext θ; exact congrArg γ.val (H.apply_zero θ)
  map_one_left γ := by apply Subtype.ext; ext θ; exact congrArg γ.val (H.apply_one θ)

end ContractibleLoop

namespace LoopFamily

variable {Q : Type*} [TopologicalSpace Q]


def precompose (ψ : C(loopCircle, loopCircle)) : loopFamilyClass Q → loopFamilyClass Q :=
  ZerothHomotopy.lift (fun Γ => classOf ((ContractibleLoop.precompose ψ).comp Γ))
    (fun {_ _} h => ZerothHomotopy.sound
      (h.map (continuous_postcomp (ContractibleLoop.precompose ψ))))

@[simp] theorem precompose_classOf (ψ : C(loopCircle, loopCircle))
    (Γ : C(familySphere, contractibleLoop Q)) :
    precompose ψ (classOf Γ) = classOf ((ContractibleLoop.precompose ψ).comp Γ) := rfl

@[simp] theorem precompose_id (ξ : loopFamilyClass Q) : precompose (.id loopCircle) ξ = ξ := by
  induction ξ using ZerothHomotopy.rec with
  | mk Γ => rfl

theorem precompose_comp (ψ χ : C(loopCircle, loopCircle)) (ξ : loopFamilyClass Q) :
    precompose (ψ.comp χ) ξ = precompose χ (precompose ψ ξ) := by
  induction ξ using ZerothHomotopy.rec with
  | mk Γ => rfl

@[simp] theorem precompose_nullClass (ψ : C(loopCircle, loopCircle)) (q : Q) :
    precompose ψ (nullClass q) = nullClass q := rfl


theorem precompose_postcompose {P : Type*} [TopologicalSpace P]
    (ψ : C(loopCircle, loopCircle)) (f : C(P, Q)) (ξ : loopFamilyClass P) :
    precompose ψ (postcompose f ξ) = postcompose f (precompose ψ ξ) := by
  induction ξ using ZerothHomotopy.rec with
  | mk Γ => rfl



theorem precompose_eq_of_homotopic {ψ χ : C(loopCircle, loopCircle)}
    (h : ψ.Homotopic χ) (ξ : loopFamilyClass Q) : precompose ψ ξ = precompose χ ξ := by
  obtain ⟨H⟩ := h
  induction ξ using ZerothHomotopy.rec with
  | mk Γ =>
    exact (classOf_eq_iff _ _).mpr
      ⟨(ContractibleLoop.precomposeHomotopy H).compContinuousMap Γ⟩

end LoopFamily



theorem circleMap_homotopic_id_of_degree_one_lift
    (ψ : C(loopCircle, loopCircle)) {f : ℝ → ℝ} (hf : Continuous f)
    (hp : ∀ t, f (t + 1) = f t + 1)
    (hl : ∀ t : ℝ, (f t : loopCircle) = ψ (t : loopCircle)) :
    ψ.Homotopic (.id loopCircle) := by
  let δ : C(loopCircle, ℝ) :=
    ⟨(DifferentialGeometry.Analysis.affinePeriodic_sub_id hp).lift,
      (hf.sub continuous_id).quotient_liftOn' _⟩
  have hδ (t : ℝ) : δ (t : loopCircle) = f t - t := rfl
  let H : (.id loopCircle : C(loopCircle, loopCircle)).Homotopy ψ := {
    toFun := fun p => p.2 + ((p.1 : ℝ) * δ p.2 : ℝ)
    continuous_toFun := by fun_prop
    map_zero_left := fun θ => by simp
    map_one_left := fun θ => by
      obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective θ
      change (t : loopCircle) + ((1 : ℝ) * δ (t : loopCircle) : ℝ) = ψ (t : loopCircle)
      rw [one_mul, hδ, ← hl]
      simp }
  exact ⟨H.symm⟩




theorem LoopFamily.precompose_eq_of_degree_one_lift
    {Q : Type*} [TopologicalSpace Q] (ψ : C(loopCircle, loopCircle))
    {f : ℝ → ℝ} (hf : Continuous f) (hp : ∀ t, f (t + 1) = f t + 1)
    (hl : ∀ t : ℝ, (f t : loopCircle) = ψ (t : loopCircle)) (ξ : loopFamilyClass Q) :
    LoopFamily.precompose ψ ξ = ξ :=
  (LoopFamily.precompose_eq_of_homotopic
    (circleMap_homotopic_id_of_degree_one_lift ψ hf hp hl) ξ).trans (LoopFamily.precompose_id ξ)

end DifferentialGeometry.Topology
