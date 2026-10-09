import DifferentialGeometry.Topology.ThreeManifold.TorusCut.TorusCylinder
import DifferentialGeometry.Topology.FundamentalGroup.BasepointChange
import DifferentialGeometry.Topology.FundamentalGroup.MarkedMapComposition
import DifferentialGeometry.Topology.FundamentalGroup.CirclePowerDegree
import DifferentialGeometry.Topology.LoopSpace.CircleDegree
import DifferentialGeometry.Topology.LoopSpace.PrimitiveCircleLift
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.PrimitiveCurveJordanHomotopy

/-!
# Class of a circle loop from a real lift (lane CP1-P2, group G2)
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry.Topology GC.Topology
namespace GC.LongTime.CuspP1

theorem circleFG_conj_eq_CPP2 {a b : FundamentalGroup Circle (1 : Circle)}
    (h : ConjClasses.mk a = ConjClasses.mk b) : a = b := by
  obtain ⟨c, hc⟩ := isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp h)
  apply fundamentalGroupCircleEquivInt.injective
  rw [← hc]
  simp only [map_mul, map_inv]
  rw [mul_comm (fundamentalGroupCircleEquivInt c), mul_assoc, mul_inv_cancel, mul_one]

theorem mk_changeBasepoint_loopDegreeClass_CPP2 {X : Type*} [TopologicalSpace X]
    [PathConnectedSpace X] (u : freeLoop X) (x : X) (β : Path x (u 0)) :
    ConjClasses.mk (fundamentalGroupChangeBasepoint β (loopDegreeClass u 1)) =
      FreeLoop.conjugacyClass u x := by
  have h := FreeLoop.conjugacyClass_eq_mk_loopRepresentativeAlong β (⟨u, rfl⟩ : basedCircleLoop (u 0))
  rw [h]
  congr 1
  unfold loopRepresentativeAlong basedCircleFundamentalGroupClass loopDegreeClass
  rw [intLoop_one]

private theorem phi_zero_CPP2 :
    AddCircle.homeomorphCircle (one_ne_zero : (1 : ℝ) ≠ 0) (0 : loopCircle) = 1 := by
  rw [AddCircle.homeomorphCircle_apply]
  exact AddCircle.toCircle_zero

/-- The standard loop `θ ↦ exp(2πiθ)` has class `1 ∈ ℤ`. -/
theorem standardLoop_class_CPP2 :
    fundamentalGroupCircleEquivInt
      (basedCircleFundamentalGroupClass
        (⟨((AddCircle.homeomorphCircle (one_ne_zero : (1 : ℝ) ≠ 0) : loopCircle ≃ₜ Circle) :
            C(loopCircle, Circle)), phi_zero_CPP2⟩ :
          basedCircleLoop (1 : Circle))) = Multiplicative.ofAdd (1 : ℤ) := by
  have h : basedCircleFundamentalGroupClass
        (⟨((AddCircle.homeomorphCircle (one_ne_zero : (1 : ℝ) ≠ 0) : loopCircle ≃ₜ Circle) :
            C(loopCircle, Circle)), phi_zero_CPP2⟩ : basedCircleLoop (1 : Circle)) =
      FundamentalGroup.mapOfEq
        ((AddCircle.homeomorphCircle (show (1 : ℝ) ≠ 0 from one_ne_zero)) : C(loopCircle, Circle))
        phi_zero_CPP2
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk circleGeneratorPath)) := by
    rw [FundamentalGroup.mapOfEq_apply]
    unfold basedCircleFundamentalGroupClass
    apply congrArg Path.Homotopic.Quotient.mk
    ext t
    rfl
  rw [h, fundamentalGroupCircleEquivInt_map_addCircle,
    fundamentalGroupUnitAddCircleEquivInt_generator]

/-- Class of a circle loop with real lift of shift `p`, read through any path from `1`. -/
theorem circleClass_of_lift_CPP2 (u : C(loopCircle, Circle)) (F : ℝ → ℝ) (hF : Continuous F)
    (p : ℤ) (hlift : ∀ t : ℝ, u (t : loopCircle) = Circle.exp (2 * Real.pi * F t))
    (hshift : ∀ t, F (t + 1) = F t + p) (β : Path (1 : Circle) (u 0)) :
    fundamentalGroupCircleEquivInt (fundamentalGroupChangeBasepoint β (loopDegreeClass u 1)) =
      Multiplicative.ofAdd p := by
  let φ : loopCircle ≃ₜ Circle := AddCircle.homeomorphCircle (one_ne_zero : (1 : ℝ) ≠ 0)
  let ρ : C(loopCircle, loopCircle) := (φ.symm : C(Circle, loopCircle)).comp u
  have huρ : u = (φ : C(loopCircle, Circle)).comp ρ := by
    refine ContinuousMap.ext fun θ => ?_
    change u θ = φ (φ.symm (u θ))
    rw [φ.apply_symm_apply]
  have hρlift : ∀ t : ℝ, ((F t : ℝ) : loopCircle) = ρ ((t : ℝ) : loopCircle) := by
    intro t
    change _ = φ.symm (u t)
    rw [hlift t, ← coe_mk_eq_exp_CPP2]
    exact (φ.symm_apply_apply _).symm
  have hconj := FreeLoop.conjugacyClass_comp_of_lift_intShift
    (φ : C(loopCircle, Circle)) ρ F hF p hρlift (fun t => by rw [hshift]) (1 : Circle)
  rw [← huρ] at hconj
  have h1 : ConjClasses.mk (fundamentalGroupChangeBasepoint β (loopDegreeClass u 1)) =
      ConjClasses.mk (FreeLoop.fundamentalGroupRepresentative (φ : C(loopCircle, Circle)) 1 ^ p) := by
    rw [mk_changeBasepoint_loopDegreeClass_CPP2, hconj]
  have h2 := circleFG_conj_eq_CPP2 h1
  have hg : FreeLoop.fundamentalGroupRepresentative (φ : C(loopCircle, Circle)) 1 =
      basedCircleFundamentalGroupClass
        (⟨(φ : C(loopCircle, Circle)), phi_zero_CPP2⟩ : basedCircleLoop (1 : Circle)) := by
    apply circleFG_conj_eq_CPP2
    have := FreeLoop.conjugacyClass_eq_mk_circleToPath (φ : C(loopCircle, Circle)) (1 : Circle)
      (⟨(φ : C(loopCircle, Circle)), phi_zero_CPP2⟩ : basedCircleLoop (1 : Circle))
      (ContinuousMap.Homotopic.refl _)
    exact this
  rw [h2, hg, map_zpow, standardLoop_class_CPP2, ← ofAdd_zsmul]
  simp

/-- Existence of a real lift with integer shift of a circle-valued loop. -/
theorem exists_lift_CPP2 (u : C(loopCircle, Circle)) :
    ∃ (F : ℝ → ℝ) (p : ℤ), Continuous F ∧
      (∀ t : ℝ, u (t : loopCircle) = Circle.exp (2 * Real.pi * F t)) ∧
      ∀ t, F (t + 1) = F t + p := by
  let φ : loopCircle ≃ₜ Circle := AddCircle.homeomorphCircle (one_ne_zero : (1 : ℝ) ≠ 0)
  obtain ⟨F, p, hF, hs⟩ := exists_real_lift_with_integer_shift
    ((φ.symm : C(Circle, loopCircle)).comp u)
  refine ⟨F, p, F.continuous, fun t => ?_, hs⟩
  have := hF t
  change (F t : loopCircle) = φ.symm (u t) at this
  rw [← coe_mk_eq_exp_CPP2]
  rw [this]
  exact (φ.apply_symm_apply (u t)).symm

private theorem map_loopDegreeClass_CPP2 {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (γ : freeLoop X) :
    FundamentalGroup.map f (γ 0) (loopDegreeClass γ 1) = loopDegreeClass (f.comp γ) 1 := by
  unfold loopDegreeClass
  rw [intLoop_one, intLoop_one]
  rfl

/-- Class of a loop in the torus read off from real lifts of its two coordinates. -/
theorem torusClass_of_lifts_CPP2 (γ : freeLoop Torus) (F₁ F₂ : ℝ → ℝ)
    (hF₁ : Continuous F₁) (hF₂ : Continuous F₂) (p q : ℤ)
    (hl₁ : ∀ t : ℝ, (γ (t : loopCircle)).1 = Circle.exp (2 * Real.pi * F₁ t))
    (hl₂ : ∀ t : ℝ, (γ (t : loopCircle)).2 = Circle.exp (2 * Real.pi * F₂ t))
    (hs₁ : ∀ t, F₁ (t + 1) = F₁ t + p) (hs₂ : ∀ t, F₂ (t + 1) = F₂ t + q)
    (β : Path ((1 : Circle), (1 : Circle)) (γ 0)) :
    torusFundamentalGroup (fundamentalGroupChangeBasepoint β (loopDegreeClass γ 1)) =
      (Multiplicative.ofAdd p, Multiplicative.ofAdd q) := by
  have key : ∀ (f : C(Torus, Circle)) (F : ℝ → ℝ) (hF : Continuous F) (n : ℤ),
      (∀ t : ℝ, f (γ (t : loopCircle)) = Circle.exp (2 * Real.pi * F t)) →
      (∀ t, F (t + 1) = F t + n) → (β' : Path (1 : Circle) (f (γ 0))) →
      fundamentalGroupCircleEquivInt
        (fundamentalGroupChangeBasepoint β' (FundamentalGroup.map f (γ 0) (loopDegreeClass γ 1))) =
          Multiplicative.ofAdd n := by
    intro f F hF n hl hs β'
    rw [map_loopDegreeClass_CPP2]
    exact circleClass_of_lift_CPP2 (f.comp γ) F hF n hl hs β'
  have h1 := key ContinuousMap.fst F₁ hF₁ p hl₁ hs₁ (β.map continuous_fst)
  have h2 := key ContinuousMap.snd F₂ hF₂ q hl₂ hs₂ (β.map continuous_snd)
  have nat₁ := congrArg (fun m => m (loopDegreeClass γ 1))
    (fundamentalGroupChangeBasepoint_naturality (ContinuousMap.fst : C(Circle × Circle, Circle)) β)
  have nat₂ := congrArg (fun m => m (loopDegreeClass γ 1))
    (fundamentalGroupChangeBasepoint_naturality (ContinuousMap.snd : C(Circle × Circle, Circle)) β)
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at nat₁ nat₂
  refine Prod.ext ?_ ?_
  · change fundamentalGroupCircleEquivInt
      (FundamentalGroup.map ContinuousMap.fst (1, 1)
        (fundamentalGroupChangeBasepoint β (loopDegreeClass γ 1))) = _
    rw [nat₁]
    exact h1
  · change fundamentalGroupCircleEquivInt
      (FundamentalGroup.map ContinuousMap.snd (1, 1)
        (fundamentalGroupChangeBasepoint β (loopDegreeClass γ 1))) = _
    rw [nat₂]
    exact h2

end GC.LongTime.CuspP1
