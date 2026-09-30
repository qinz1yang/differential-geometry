import DifferentialGeometry.Geometry.Metric.Approximation.EdgeCoarseBorder
import DifferentialGeometry.Geometry.Metric.Approximation.IsometricKleinerLottApproximation
import DifferentialGeometry.Geometry.Metric.Scaling.RescaleComposition

set_option autoImplicit false
open Set Metric GC.MetricGeometry
universe u v

private abbrev Factor := Icc (0 : ℝ) 201
private abbrev Strip := WithLp 2 (ℝ × Factor)
private def origin : Factor := ⟨0, by norm_num⟩
private def stripCenter : Strip := WithLp.toLp 2 ((0 : ℝ), origin)
private def embedding (x : Strip) : WithLp 2 (ℝ × ℝ) := WithLp.toLp 2 (x.fst, x.snd.val)

example (t : ℝ) (ht : |t| ≤ 100) :
    ∃ a : Strip, isEdgePoint.{0, 0} a 1 (1 / 10^16) (1 / 10^16) ∧
      dist (embedding a) (WithLp.toLp 2 (t, (0 : ℝ))) < 1 / 100000 := by
  let F : KleinerLottApprox stripCenter (WithLp.toLp 2 ((0 : ℝ), origin)) (1 / 10^28) :=
    (IsometryEquiv.refl Strip).toKleinerLottApprox rfl (by norm_num) (by norm_num)
  let G : KleinerLottApprox origin (⟨0, by norm_num⟩ : Factor) (1 / 10^22) :=
    (IsometryEquiv.refl Factor).toKleinerLottApprox rfl (by norm_num) (by norm_num)
  have hρ : LipschitzWith (0 : NNReal) (fun _ : Strip => (1 : ℝ)) := LipschitzWith.const 1
  have h := F.coarse_border_of_lipschitz_scale (Δ := 1) (τ := 1 / 100000)
    (b' := 1 / 10^16) (s' := 1 / 10^16) (hC := by norm_num) G hρ
    (fun _ => by norm_num) rfl (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  obtain ⟨a, ha, hclose⟩ := h.2.2.2.2.2.2.2 t (by simpa using ht)
  refine ⟨a, ?_, ?_⟩
  · have ha' := ha.1
    have hm : (inferInstance : MetricSpace Strip).rescale (1 : ℝ)⁻¹ (by positivity) =
        (inferInstance : MetricSpace Strip) := by simp only [inv_one, MetricSpace.rescale_one]
    rw [hm] at ha'
    exact ha'
  · have hemb : F.stripMap G a = embedding a := rfl
    rw [hemb, mul_one] at hclose
    exact hclose

example {X : Type u} [m : MetricSpace X] (ρ : X → ℝ) (hρpos : ∀ x, 0 < ρ x)
    (p : X) (Δ b s : ℝ) :
    let normalizedMetric := m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
    let normalizedScale := fun x => ρ x / ρ p
    {x | @isEdgePoint.{u, v} X (normalizedMetric.rescale (normalizedScale x)⁻¹
        (inv_pos.mpr (div_pos (hρpos x) (hρpos p)))) x Δ b s} =
      {x | @isEdgePoint.{u, v} X (m.rescale (ρ x)⁻¹ (inv_pos.mpr (hρpos x))) x Δ b s} := by
  dsimp only
  ext x
  simp only [mem_ofPred_eq]
  rw [MetricSpace.rescale_inv_ratio m (hρpos p) (hρpos x)]

