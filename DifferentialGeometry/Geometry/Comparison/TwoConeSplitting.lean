import DifferentialGeometry.Geometry.Metric.TwoConeApices
import DifferentialGeometry.Geometry.Comparison.LineSplitting
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false

noncomputable section
open scoped NNReal

namespace GC.MetricGeometry.RadialConeData

open Set DifferentialGeometry.Geometry.Comparison.Toponogov

universe u
variable {X : Type u} [MetricSpace X] [ProperSpace X] {p q : X}

theorem exists_pointed_product_at_second_apex
    (H : RadialConeData p) (K : RadialConeData q) (hpq : p ≠ q)
    (hs : fourPointComparison 0 (univ : Set X))
    (hsegments : ∀ a b : X, ∃ f : unitInterval → X,
      Continuous f ∧ f 0 = a ∧ f 1 = b ∧
      ∀ s t, dist (f s) (f t) = dist a b * dist s t) :
    ∃ (Y : Type u) (m : MetricSpace Y), letI := m
      ∃ (w : Y) (e : X ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin 1) × Y)),
        e q = WithLp.toLp 2 (0, w) ∧
        e p = WithLp.toLp 2 (PiLp.single 2 0 (-dist p q), w) ∧
        (∀ t : ℝ, e (H.twoApexLine K t) =
          WithLp.toLp 2 (PiLp.single 2 0 (t - dist p q), w)) ∧
        ProperSpace Y ∧ CompleteSpace Y ∧ fourPointComparison 0 (univ : Set Y) ∧
        (∀ a b : Y, ∃ f : unitInterval → Y,
          Continuous f ∧ f 0 = a ∧ f 1 = b ∧
          ∀ s t, dist (f s) (f t) = dist a b * dist s t) ∧
        dimH (univ : Set Y) ≤ dimH (univ : Set X) := by
  obtain ⟨Y, m, w, a, ha, hpY, hcY, hsY, hgY, hdY⟩ :=
    exists_isometryEquiv_real_prod hs (H.twoApexLine_isometry K hpq) hsegments
  let := m
  let L := dist p q
  let r : ℝ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 1) := (OrthonormalBasis.singleton (Fin 1) ℝ).repr
  have hr (t : ℝ) : r t = PiLp.single 2 0 t := by
    ext j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    change (OrthonormalBasis.singleton (Fin 1) ℝ).repr t 0 = _
    simp only [OrthonormalBasis.singleton_repr, PiLp.single_apply, ite_true]
  let e : X ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin 1) × Y) :=
    a.trans (IsometryEquiv.withLpProdCongr 2
      ((IsometryEquiv.subRight L).trans r.toIsometryEquiv) (IsometryEquiv.refl Y))
  have he (t : ℝ) : e (H.twoApexLine K t) =
      WithLp.toLp 2 (PiLp.single 2 0 (t - L), w) := by
    change WithLp.toLp 2 (r ((a (H.twoApexLine K t)).fst - L),
      (a (H.twoApexLine K t)).snd) = _
    rw [ha]
    change WithLp.toLp 2 (r (t - L), w) = _
    rw [hr]
  have hq : e q = WithLp.toLp 2 (0, w) := by
    have hh := he L
    rw [H.twoApexLine_through K hpq, sub_self] at hh
    rwa [(PiLp.single_eq_zero_iff 2 0).mpr rfl] at hh
  have hp : e p = WithLp.toLp 2 (PiLp.single 2 0 (-dist p q), w) := by
    have hh := he 0
    rwa [H.twoApexLine_zero, zero_sub] at hh
  exact ⟨Y, m, w, e, hq, hp, he, hpY, hcY, hsY, hgY, hdY⟩

end GC.MetricGeometry.RadialConeData
