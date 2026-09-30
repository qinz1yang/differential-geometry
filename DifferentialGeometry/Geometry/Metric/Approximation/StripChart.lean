import DifferentialGeometry.Geometry.Metric.Approximation.ProductFactorComposition

set_option autoImplicit false
open Set Metric

namespace GC.MetricGeometry.KleinerLottApprox

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
variable {p : X} {q : Y} {C b s S : ℝ} {hC : 0 ≤ C}

def stripMap {o : Icc (0 : ℝ) C} (F : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), q)) b)
    (G : KleinerLottApprox q o s)
    (x : X) : WithLp 2 (ℝ × ℝ) :=
  WithLp.toLp 2 ((F.toFun x).fst, (G.toFun (F.toFun x).snd).val)

@[simp] theorem stripMap_basepoint
    (F : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), q)) b)
    (G : KleinerLottApprox q (⟨0, le_rfl, hC⟩ : Icc (0 : ℝ) C) s) :
    F.stripMap G p = 0 := by
  unfold stripMap
  rw [F.basepoint]
  change WithLp.toLp 2 ((0 : ℝ), (G.toFun q).val) = 0
  rw [G.basepoint]
  rfl

theorem stripMap_height
    (F : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), q)) b)
    (G : KleinerLottApprox q (⟨0, le_rfl, hC⟩ : Icc (0 : ℝ) C) s) (x : X) :
    (F.stripMap G x).snd ∈ Icc 0 C := (G.toFun (F.toFun x).snd).property

theorem stripMap_estimates
    (F : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), q)) b)
    (G : KleinerLottApprox q (⟨0, le_rfl, hC⟩ : Icc (0 : ℝ) C) s)
    (hbuffer : S + 10 * (b + s) < min b⁻¹ s⁻¹) :
    (∀ x ∈ ball p S, ∀ y ∈ ball p S,
      |dist (F.stripMap G x) (F.stripMap G y) - dist x y| ≤ b + s) ∧
    ∀ z : WithLp 2 (ℝ × ℝ), z.snd ∈ Icc 0 C → ‖z‖ ≤ S - 4 * (b + s) →
      ∃ x ∈ ball p S, dist (F.stripMap G x) z < 3 * (b + s) ∧
        dist x p < ‖z‖ + 3 * (b + s) := by
  let J : WithLp 2 (ℝ × Icc (0 : ℝ) C) → WithLp 2 (ℝ × ℝ) :=
    fun z => WithLp.toLp 2 (z.fst, z.snd.val)
  have hJ : Isometry J := isometry_id.withLpProdMap 2 isometry_subtype_coe
  let Q : X → WithLp 2 (ℝ × Icc (0 : ℝ) C) :=
    fun x => WithLp.toLp 2 ((F.toFun x).fst, G.toFun (F.toFun x).snd)
  have hQ : ∀ x, J (Q x) = F.stripMap G x := fun _ => rfl
  have h0 : J (WithLp.toLp 2 ((0 : ℝ), (⟨0, le_rfl, hC⟩ : Icc (0 : ℝ) C))) = 0 := rfl
  obtain ⟨hd, hc⟩ := F.product_factor_composition_estimates G hbuffer
  refine ⟨?_, ?_⟩
  · intro x hx y hy
    simpa only [← hQ, hJ.dist_eq] using hd x hx y hy
  · intro z hz hr
    let z' : WithLp 2 (ℝ × Icc (0 : ℝ) C) := WithLp.toLp 2 (z.fst, ⟨z.snd, hz⟩)
    have hz' : J z' = z := rfl
    have hnorm : dist z' (WithLp.toLp 2 ((0 : ℝ), (⟨0, le_rfl, hC⟩ : Icc (0 : ℝ) C))) = ‖z‖ := by
      rw [← hJ.dist_eq, hz', h0, dist_zero_right]
    obtain ⟨x, hx, hclose, hrad⟩ := hc z' (by rwa [hnorm])
    refine ⟨x, hx, ?_, ?_⟩
    · change dist (J (Q x)) (J z') < _
      rw [hJ.dist_eq]
      exact hclose
    · rwa [hnorm] at hrad

end GC.MetricGeometry.KleinerLottApprox
