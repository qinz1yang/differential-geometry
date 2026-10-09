import DifferentialGeometry.Topology.MetricSpace.RealBallCharts
import DifferentialGeometry.Geometry.Metric.ProductBallIsometry
import DifferentialGeometry.Geometry.Metric.Approximation.TargetBallIsometry
import DifferentialGeometry.Geometry.Comparison.GlobalOneDimensionalModels

set_option autoImplicit false

open Set Metric
open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace GC.MetricGeometry

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y] [CompleteSpace Y]
variable {p : X} {q : Y} {ε β Δ : ℝ}

theorem exists_nearby_endpoint_of_no_plane_approximation
    (f : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), q)) ε)
    (hβ : 0 < β) (hβsmall : β < 1 / 100) (hΔ : 100 / β < Δ)
    (hε : ε < β / 100)
    (hno : ¬ Nonempty (KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), (0 : ℝ))) β))
    (hcurves : ∀ a b : Y, ∀ η : ℝ, 0 < η →
      ∃ c : unitInterval → Y, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + η))
    (hcomp : fourPointComparison 0 (univ : Set Y))
    (hdim : dimH (univ : Set Y) ≤ 1)
    (hlarge : ∃ a b : Y, 500 * Δ < dist a b) :
    (∃ L : ℝ, 500 * Δ < L ∧ ∃ e : Y ≃ᵢ Icc (0 : ℝ) L, (e q).val < Δ / 2) ∨
      (∃ e : Y ≃ᵢ Ici (0 : ℝ), (e q).val < Δ / 2) := by
  have hΔ0 : 0 < Δ := (div_pos (by norm_num) hβ).trans hΔ
  let R := Δ / 4
  have hR : 0 < R := by dsimp [R]; positivity
  have hβ1 : β < 1 := by linarith
  have hε1 : ε < 1 := by linarith
  have hβi : 1 < β⁻¹ := (one_lt_inv₀ hβ).mpr hβ1
  have hi : 100 * β⁻¹ < ε⁻¹ := by
    have h := (inv_lt_inv₀ (div_pos hβ (by norm_num : (0 : ℝ) < 100)) f.error_pos).mpr hε
    simpa only [div_eq_mul_inv, mul_inv_rev, inv_inv] using h
  have hbudget : 3 * ε ≤ β := by linarith
  have hdomain : β⁻¹ + 2 * ε ≤ ε⁻¹ := by linarith
  have hchart : β⁻¹ + ε < R := by
    have hd : 100 * β⁻¹ < Δ := by simpa only [div_eq_mul_inv] using hΔ
    dsimp [R]
    linarith
  have hnochart (e : ball q R ≃ᵢ ball (0 : ℝ) R)
      (he : (e ⟨q, mem_ball_self hR⟩).val = 0) : False := by
    exact hno ⟨f.mapTargetBallIsometry hR (e.l2ProductBall hR he (0 : ℝ))
      (e.l2ProductBall_basepoint hR he 0) hbudget hβ1 hdomain hchart⟩
  have hsubsetchart {s : Set ℝ} (e : Y ≃ᵢ s)
      (hs : ball (e q).val R ⊆ s) : False := by
    let c := (e.ballCongr q R).trans (IsometryEquiv.realSubsetBall (e q) R hs)
    apply hnochart c
    change (e q).val - (e q).val = 0
    exact sub_self _
  rcases exists_pointed_one_dimensional_model hcurves hcomp hdim q with
    ⟨e, _⟩ | ⟨e, he⟩ | ⟨a, _, e, _⟩ | ⟨L, hL, a, _, e, _⟩ | ⟨L, hL, e, he⟩
  · obtain ⟨a, b, hab⟩ := hlarge
    have hd := e.dist_eq a b
    rw [Subsingleton.elim (e a) (e b), dist_self] at hd
    exact False.elim (by linarith)
  · have hc : ∃ c : ball q R ≃ᵢ ball (0 : ℝ) R,
        (c ⟨q, mem_ball_self hR⟩).val = 0 := by
      refine ⟨e.ballCongrAt q 0 he R, ?_⟩
      simpa only [IsometryEquiv.ballCongrAt_apply] using he
    obtain ⟨c, hc⟩ := hc
    exact False.elim (hnochart c hc)
  · by_cases ha : (e q).val < Δ / 2
    · exact Or.inr ⟨e, ha⟩
    · apply False.elim
      apply hsubsetchart e
      intro x hx
      have hx' := (abs_lt.mp (show |x - (e q).val| < R from hx)).1
      change 0 ≤ x
      dsimp [R] at hx'
      linarith
  · have hlen : 500 * Δ < L := by
      obtain ⟨x, y, hxy⟩ := hlarge
      have hd := e.dist_eq x y
      change |(e x).val - (e y).val| = dist x y at hd
      have hb : |(e x).val - (e y).val| ≤ L := by
        rw [abs_le]
        constructor <;> linarith [(e x).property.1, (e x).property.2,
          (e y).property.1, (e y).property.2]
      linarith
    by_cases ha : (e q).val < Δ / 2
    · exact Or.inl ⟨L, hlen, e, ha⟩
    by_cases hb : L - (e q).val < Δ / 2
    · exact Or.inl ⟨L, hlen, e.trans (IsometryEquiv.reflectIcc L), hb⟩
    apply False.elim
    apply hsubsetchart e
    intro x hx
    have hx' := abs_lt.mp (show |x - (e q).val| < R from hx)
    change 0 ≤ x ∧ x ≤ L
    dsimp [R] at hx'
    constructor <;> linarith
  · have hlen : 1000 * Δ < L := by
      obtain ⟨x, y, hxy⟩ := hlarge
      have hd := e.dist_eq x y
      have hb := AddCircle.norm_le_half_period L (x := e x - e y) hL.ne'
      rw [abs_of_pos hL, ← dist_eq_norm] at hb
      linarith
    have hfour : 4 * R ≤ L := by dsimp [R]; linarith
    have hc : ∃ c : ball q R ≃ᵢ ball (0 : AddCircle L) R,
        (c ⟨q, mem_ball_self hR⟩).val = 0 := by
      refine ⟨e.ballCongrAt q 0 he R, ?_⟩
      simpa only [IsometryEquiv.ballCongrAt_apply] using he
    obtain ⟨c, hc⟩ := hc
    let ec := AddCircle.realBallIsometry hL hfour
    have hzero : ec ⟨0, mem_ball_self hR⟩ = ⟨0, mem_ball_self hR⟩ := by
      apply Subtype.ext
      change ((0 : ℝ) : AddCircle L) = 0
      simp
    apply False.elim
    apply hnochart (c.trans ec.symm)
    have hc0 : c ⟨q, mem_ball_self hR⟩ = ⟨0, mem_ball_self hR⟩ := Subtype.ext hc
    change (ec.symm (c ⟨q, mem_ball_self hR⟩)).val = 0
    rw [hc0, ← hzero, ec.symm_apply_apply]

end GC.MetricGeometry
