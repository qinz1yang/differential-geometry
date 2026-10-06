import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.PrimitiveCurveJordanCore
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.PrimitiveCurveJordanLink
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.PrimitiveCurveReduction
import DifferentialGeometry.Topology.LoopSpace.PeriodicDescent

/-!
# An embedded essential loop on the torus has coprime class (lane CP1-P2, group G3)

Discharges the explicit hypothesis `hcop` of `primitive_of_coprime_CPP`.
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry.Topology GC.Topology
namespace GC.LongTime.CuspP1

theorem addcomm_aux_CPP2 {A : Type*} [AddCommGroup A] (x y : A) (a b p q : ℤ)
    (hab : a * p + b * q = 1) :
    x = p • (a • x + b • y) + (-b) • ((-q) • x + p • y) ∧
    y = q • (a • x + b • y) + a • ((-q) • x + p • y) := by
  constructor
  · linear_combination (norm := module) (-hab) • x
  · linear_combination (norm := module) (-hab) • y

theorem circle_aux_CPP2 (z1 z2 : Circle) (a b p q : ℤ) (hab : a * p + b * q = 1) :
    z1 = (z1 ^ a * z2 ^ b) ^ p * (z1 ^ (-q) * z2 ^ p) ^ (-b) ∧
    z2 = (z1 ^ a * z2 ^ b) ^ q * (z1 ^ (-q) * z2 ^ p) ^ a :=
  addcomm_aux_CPP2 (Additive.ofMul z1) (Additive.ofMul z2) a b p q hab

/-- A loop in the torus with both real lifts periodic is nullhomotopic. -/
theorem nullhomotopic_of_periodic_lifts_CPP2 (γ : freeLoop GC.Endpoint.Torus) (F₁ F₂ : ℝ → ℝ)
    (hF₁ : Continuous F₁) (hF₂ : Continuous F₂)
    (hl₁ : ∀ t : ℝ, (γ (t : loopCircle)).1 = Circle.exp (2 * Real.pi * F₁ t))
    (hl₂ : ∀ t : ℝ, (γ (t : loopCircle)).2 = Circle.exp (2 * Real.pi * F₂ t))
    (hs₁ : ∀ t, F₁ (t + 1) = F₁ t) (hs₂ : ∀ t, F₂ (t + 1) = F₂ t) :
    γ.Nullhomotopic := by
  let f₁ : freeLoop ℝ := periodicLoop F₁ hs₁ hF₁
  let f₂ : freeLoop ℝ := periodicLoop F₂ hs₂ hF₂
  refine ⟨(1, 1), ⟨{
    toFun := fun sθ => (Circle.exp (2 * Real.pi * ((1 - (sθ.1 : ℝ)) * f₁ sθ.2)),
      Circle.exp (2 * Real.pi * ((1 - (sθ.1 : ℝ)) * f₂ sθ.2)))
    continuous_toFun := by
      have h1 : Continuous (fun sθ : unitInterval × loopCircle => f₁ sθ.2) :=
        f₁.continuous.comp continuous_snd
      have h2 : Continuous (fun sθ : unitInterval × loopCircle => f₂ sθ.2) :=
        f₂.continuous.comp continuous_snd
      have hs : Continuous (fun sθ : unitInterval × loopCircle => (1 - (sθ.1 : ℝ))) :=
        continuous_const.sub (continuous_subtype_val.comp continuous_fst)
      exact (Circle.exp.continuous.comp (continuous_const.mul (hs.mul h1))).prodMk
        (Circle.exp.continuous.comp (continuous_const.mul (hs.mul h2)))
    map_zero_left := by
      intro θ
      obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective θ
      refine Prod.ext ?_ ?_
      · simp only [f₁, hl₁, sub_zero, Set.Icc.coe_zero, one_mul]
        rfl
      · simp only [f₂, hl₂, sub_zero, Set.Icc.coe_zero, one_mul]
        rfl
    map_one_left := by
      intro θ
      refine Prod.ext ?_ ?_ <;> simp }⟩⟩

/-- **`hcop`.**  An embedded non-nullhomotopic loop on the torus has coprime class. -/
theorem hcop_CPP2 :
    ∀ γ : freeLoop GC.Endpoint.Torus, Topology.IsEmbedding γ → ¬ γ.Nullhomotopic →
      ∀ β : Path ((1 : Circle), (1 : Circle)) (γ 0),
        IsCoprime
          (torusFundamentalGroup
            (fundamentalGroupChangeBasepoint β (loopDegreeClass γ 1))).1.toAdd
          (torusFundamentalGroup
            (fundamentalGroupChangeBasepoint β (loopDegreeClass γ 1))).2.toAdd := by
  intro γ hemb hnn β
  obtain ⟨F₁, p, hF₁, hl₁, hs₁⟩ := exists_lift_CPP2 ((ContinuousMap.fst : C(Circle × Circle, Circle)).comp γ)
  obtain ⟨F₂, q, hF₂, hl₂, hs₂⟩ := exists_lift_CPP2 ((ContinuousMap.snd : C(Circle × Circle, Circle)).comp γ)
  rw [torusClass_of_lifts_CPP2 γ F₁ F₂ hF₁ hF₂ p q hl₁ hl₂ hs₁ hs₂ β]
  change IsCoprime p q
  by_contra hnc
  by_cases h00 : p = 0 ∧ q = 0
  · obtain ⟨rfl, rfl⟩ := h00
    exact hnn (nullhomotopic_of_periodic_lifts_CPP2 γ F₁ F₂ hF₁ hF₂ hl₁ hl₂
      (fun t => by simpa using hs₁ t) (fun t => by simpa using hs₂ t))
  · -- non-primitive, non-zero class
    have hg0 : 0 < Int.gcd p q := Nat.pos_of_ne_zero (fun h => h00 (Int.gcd_eq_zero_iff.mp h))
    have hg1 : Int.gcd p q ≠ 1 := fun h => hnc (Int.isCoprime_iff_gcd_eq_one.mpr h)
    set g : ℤ := (Int.gcd p q : ℤ) with hg
    have hg2 : 2 ≤ g := by
      have : 2 ≤ Int.gcd p q := by omega
      rw [hg]
      exact_mod_cast this
    obtain ⟨p', hp'⟩ : g ∣ p := Int.gcd_dvd_left p q
    obtain ⟨q', hq'⟩ : g ∣ q := Int.gcd_dvd_right p q
    have hcop' : IsCoprime p' q' := by
      have := Int.isCoprime_iff_gcd_eq_one.mpr (Int.gcd_div_gcd_div_gcd hg0)
      have e1 : p / g = p' := by rw [hp']; exact Int.mul_ediv_cancel_left _ (by omega)
      have e2 : q / g = q' := by rw [hq']; exact Int.mul_ediv_cancel_left _ (by omega)
      rwa [e1, e2] at this
    obtain ⟨a, b, hab⟩ := hcop'
    -- the two integral combinations of the coordinate lifts
    let Fu : ℝ → ℝ := fun t => a * F₁ t + b * F₂ t
    let Fv : ℝ → ℝ := fun t => -q' * F₁ t + p' * F₂ t
    have hFuc : Continuous Fu := (continuous_const.mul hF₁).add (continuous_const.mul hF₂)
    have hFvc : Continuous Fv := (continuous_const.mul hF₁).add (continuous_const.mul hF₂)
    have hFu_shift : ∀ t, Fu (t + 1) = Fu t + (g : ℝ) := by
      intro t
      have h1 := hs₁ t
      have h2 := hs₂ t
      have hp'' : (p : ℝ) = g * p' := by exact_mod_cast hp'
      have hq'' : (q : ℝ) = g * q' := by exact_mod_cast hq'
      have hab' : (a : ℝ) * p' + b * q' = 1 := by exact_mod_cast hab
      simp only [Fu, h1, h2, hp'', hq'']
      linear_combination (g : ℝ) * hab'
    have hFv_shift : ∀ t, Fv (t + 1) = Fv t := by
      intro t
      have h1 := hs₁ t
      have h2 := hs₂ t
      have hp'' : (p : ℝ) = g * p' := by exact_mod_cast hp'
      have hq'' : (q : ℝ) = g * q' := by exact_mod_cast hq'
      simp only [Fv, h1, h2, hp'', hq'']
      ring
    let u : C(loopCircle, Circle) :=
      ⟨fun θ => (γ θ).1 ^ a * (γ θ).2 ^ b, by
        have h1 : Continuous fun θ => (γ θ).1 := continuous_fst.comp γ.continuous
        have h2 : Continuous fun θ => (γ θ).2 := continuous_snd.comp γ.continuous
        exact ((continuous_zpow a).comp h1).mul ((continuous_zpow b).comp h2)⟩
    let h : C(loopCircle, ℝ) := periodicLoop Fv hFv_shift hFvc
    have hlift_u : ∀ t : ℝ, u (t : loopCircle) = Circle.exp (2 * Real.pi * Fu t) := by
      intro t
      change (γ t).1 ^ a * (γ t).2 ^ b = _
      have e1 := hl₁ t
      have e2 := hl₂ t
      change (γ (t : loopCircle)).1 = _ at e1
      change (γ (t : loopCircle)).2 = _ at e2
      rw [e1, e2, ← Circle.exp_intCast_mul, ← Circle.exp_intCast_mul, ← Circle.exp_add]
      congr 1
      simp only [Fu]
      ring
    have hlift_v : ∀ t : ℝ, (γ (t : loopCircle)).1 ^ (-q') * (γ (t : loopCircle)).2 ^ p' =
        Circle.exp (2 * Real.pi * Fv t) := by
      intro t
      have e1 := hl₁ t
      have e2 := hl₂ t
      change (γ (t : loopCircle)).1 = _ at e1
      change (γ (t : loopCircle)).2 = _ at e2
      rw [e1, e2, ← Circle.exp_intCast_mul, ← Circle.exp_intCast_mul, ← Circle.exp_add]
      congr 1
      simp only [Fv]
      push_cast
      ring
    have hinj : Function.Injective fun θ => (u θ, h θ) := by
      intro θ θ' hθ
      obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective θ
      obtain ⟨t', rfl⟩ := QuotientAddGroup.mk_surjective θ'
      have hu : u (t : loopCircle) = u (t' : loopCircle) := congrArg Prod.fst hθ
      have hh : Fv t = Fv t' := congrArg Prod.snd hθ
      have hv : (γ (t : loopCircle)).1 ^ (-q') * (γ (t : loopCircle)).2 ^ p' =
          (γ (t' : loopCircle)).1 ^ (-q') * (γ (t' : loopCircle)).2 ^ p' := by
        rw [hlift_v, hlift_v, hh]
      have hu' : (γ (t : loopCircle)).1 ^ a * (γ (t : loopCircle)).2 ^ b =
          (γ (t' : loopCircle)).1 ^ a * (γ (t' : loopCircle)).2 ^ b := hu
      have c1 := circle_aux_CPP2 (γ (t : loopCircle)).1 (γ (t : loopCircle)).2 a b p' q' hab
      have c2 := circle_aux_CPP2 (γ (t' : loopCircle)).1 (γ (t' : loopCircle)).2 a b p' q' hab
      have hγ : γ (t : loopCircle) = γ (t' : loopCircle) := by
        refine Prod.ext ?_ ?_
        · rw [c1.1, c2.1, hu', hv]
        · rw [c1.2, c2.2, hu', hv]
      exact hemb.injective hγ
    have hcases := degree_cases_of_embedded_annulus_CPP2 u h hinj Fu hFuc g hlift_u
      (fun t => by rw [hFu_shift])
    omega

/-- `hprim` with no remaining hypothesis: an embedded essential loop on the torus is primitive. -/
theorem exists_primitive_of_embedded_CPP2 :
    ∀ γ : freeLoop GC.Endpoint.Torus, Topology.IsEmbedding γ → ¬ γ.Nullhomotopic →
      ∃ e : FundamentalGroup GC.Endpoint.Torus (γ 0) ≃* Multiplicative ℤ × Multiplicative ℤ,
        e (loopDegreeClass γ 1) = (Multiplicative.ofAdd 1, 1) :=
  primitive_of_coprime_CPP hcop_CPP2

end GC.LongTime.CuspP1
