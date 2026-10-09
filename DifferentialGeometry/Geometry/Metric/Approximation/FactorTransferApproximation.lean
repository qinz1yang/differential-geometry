import DifferentialGeometry.Geometry.Metric.Approximation.SmallErrorKleinerLott

set_option autoImplicit false


namespace GC.MetricGeometry

variable {Aᵢ A Bᵢ B E : Type*} [MetricSpace Aᵢ] [MetricSpace A]
variable [MetricSpace Bᵢ] [MetricSpace B] [MetricSpace E]
variable {aᵢ : Aᵢ} {a : A} {bᵢ : Bᵢ} {b : B} {u : E} {R ε : ℝ}

theorem exists_factor_transfer_approximation
    (g : PointedBallApprox aᵢ a (8 * R) ε)
    (h : PointedBallApprox bᵢ b (8 * R) ε)
    (H : WithLp 2 (E × B) ≃ᵢ A) (hH : H (WithLp.toLp 2 (u, b)) = a)
    (hε : 14 * ε < 2 * R) :
    ∃ F : PointedBallApprox (WithLp.toLp 2 (u, bᵢ)) aᵢ (2 * R) (14 * ε),
      ∀ x : BallCarrier (WithLp.toLp 2 (u, bᵢ)) (2 * R),
        dist (F.toFun x) aᵢ ≤ 8 * R ∧
        ∀ (hx : dist (F.toFun x) aᵢ ≤ 8 * R)
          (hy : dist x.val.snd bᵢ ≤ 8 * R),
          dist (g.toFun ⟨F.toFun x, hx⟩)
            (H (WithLp.toLp 2 (x.val.fst, h.toFun ⟨x.val.snd, hy⟩))) < ε := by
  subst a
  have he := g.error_pos
  have hR : 0 < R := by linarith
  let J := (h.l2Product u (by linarith : 3 * ε < 8 * R)).mapTargetIsometry H
  have h4 : 4 * R + ε ≤ 8 * R := by linarith
  let t := g.quasiInverse (s := 4 * R) (by linarith : 4 * ε < 4 * R) h4
  let F : PointedBallApprox (WithLp.toLp 2 (u, bᵢ)) aᵢ (2 * R) (14 * ε) :=
    (J.comp t (s := 2 * R) (by linarith) (by linarith) (by linarith)).enlargeError
      (by linarith) hε
  refine ⟨F, fun x => ?_⟩
  let x8 : BallCarrier (WithLp.toLp 2 (u, bᵢ)) (8 * R) :=
    ⟨x.val, by linarith [x.property]⟩
  have hJx : dist (J.toFun x8) (H (WithLp.toLp 2 (u, b))) ≤ 4 * R := by
    have hr := J.radial_upper x8
    dsimp only [x8] at hr
    linarith [x.property]
  let y : BallCarrier (H (WithLp.toLp 2 (u, b))) (4 * R) := ⟨J.toFun x8, hJx⟩
  have hFx : F.toFun x = (g.inverseLift h4 y).val := rfl
  refine ⟨by rw [hFx]; exact (g.inverseLift h4 y).property, ?_⟩
  intro hx hy
  have hh := g.inverseLift_spec h4 y
  rw [dist_comm] at hh
  have hz : (⟨F.toFun x, hx⟩ : BallCarrier aᵢ (8 * R)) = g.inverseLift h4 y :=
    Subtype.ext hFx
  rw [hz]
  change dist (g.toFun (g.inverseLift h4 y)) (J.toFun x8) < ε
  exact hh

theorem exists_factor_transfer_kleinerLott_approximation {τ : ℝ}
    (g : PointedBallApprox aᵢ a (8 * (τ⁻¹ + 2)) ε)
    (h : PointedBallApprox bᵢ b (8 * (τ⁻¹ + 2)) ε)
    (H : WithLp 2 (E × B) ≃ᵢ A) (hH : H (WithLp.toLp 2 (u, b)) = a)
    (hτ : 0 < τ) (hτone : τ < 1) (hε : ε < τ / 100) :
    ∃ F : KleinerLottApprox (WithLp.toLp 2 (u, bᵢ)) aᵢ τ,
      ∀ x : BallCarrier (WithLp.toLp 2 (u, bᵢ)) (2 * (τ⁻¹ + 2)),
        dist (F.toFun x.val) aᵢ ≤ 8 * (τ⁻¹ + 2) ∧
        ∀ (hx : dist (F.toFun x.val) aᵢ ≤ 8 * (τ⁻¹ + 2))
          (hy : dist x.val.snd bᵢ ≤ 8 * (τ⁻¹ + 2)),
          dist (g.toFun ⟨F.toFun x.val, hx⟩)
            (H (WithLp.toLp 2 (x.val.fst, h.toFun ⟨x.val.snd, hy⟩))) < ε := by
  have hi : 0 < τ⁻¹ := inv_pos.mpr hτ
  have hsmall : 14 * ε < 2 * (τ⁻¹ + 2) := by linarith
  obtain ⟨F, hF⟩ := exists_factor_transfer_approximation g h H hH hsmall
  have hR : τ⁻¹ ≤ 2 * (τ⁻¹ + 2) := by linarith
  have herror : 2 * (14 * ε) ≤ τ := by linarith
  refine ⟨F.toKleinerLottOfSmallError hτ hτone hR herror, ?_⟩
  intro x
  simpa only [F.toKleinerLottOfSmallError_apply hτ hτone hR herror x.val x.property] using hF x

end GC.MetricGeometry
