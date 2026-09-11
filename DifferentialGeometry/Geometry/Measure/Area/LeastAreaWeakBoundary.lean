import DifferentialGeometry.Geometry.Measure.Area.LeastAreaAnnulus
import DifferentialGeometry.Geometry.Measure.Area.LeastAreaReparametrization
import DifferentialGeometry.Geometry.Metric.LoopLengthReparametrization
import DifferentialGeometry.Topology.LoopSpace.MonotoneLiftApproximation









noncomputable section

open Bundle Manifold Set DifferentialGeometry Function
open DifferentialGeometry.Topology
open scoped Topology Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T3Space M] [PreconnectedSpace M] [Nonempty M]




theorem leastSpanningArea_comp_monotone_lift (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (γ δ : lipschitzContractibleLoop g) {ψ : ℝ → ℝ}
    (hc : Continuous ψ) (hm : Monotone ψ) (hp : ∀ t, ψ (t + 1) = ψ t + 1)
    (htrace : δ.val.val = γ.val.val.comp (affineCircleMap ψ hc hp)) :
    leastSpanningArea g δ = leastSpanningArea g γ := by
  obtain ⟨ρ, C, hρ, _, hann⟩ := exists_leastSpanningArea_annulus_bound g
  obtain ⟨Lγ, hγ⟩ := γ.property
  obtain ⟨Lδ, hδ⟩ := δ.property
  let l := riemannianCurveLength g (fun t => γ.val.val (t : loopCircle)) 0 1
  have hl : 0 ≤ l := riemannianCurveLength_nonneg g _ _ _
  have hδ' : ∀ x y, riemannianEDistOf g (γ.val.val (affineCircleMap ψ hc hp x))
      (γ.val.val (affineCircleMap ψ hc hp y)) ≤ (Lδ : ℝ≥0∞) * edist x y := by
    intro x y
    simpa only [htrace, ContinuousMap.comp_apply] using hδ x y
  have hlenδ : riemannianCurveLength g (fun t => δ.val.val (t : loopCircle)) 0 1 = l := by
    simp only [htrace, ContinuousMap.comp_apply]
    exact loop_length_comp_affineCircleMap g γ.val.val hγ hc hm hp hδ'
  let B : ℝ := (C : ℝ) * (2 * l)
  have hB : 0 ≤ B := mul_nonneg C.coe_nonneg (by positivity)
  apply sub_eq_zero.mp
  apply abs_eq_zero.mp
  apply le_antisymm ?_ (abs_nonneg _)
  apply le_of_forall_pos_le_add
  intro ε hε
  let d : ℝ := min ((ρ : ℝ) / 2) (ε / (2 * (B + 1)))
  have hd : 0 < d := lt_min (by exact half_pos (by exact_mod_cast hρ)) (by positivity)
  have hdρ : d < (ρ : ℝ) :=
    (min_le_left _ _).trans_lt (half_lt_self (by exact_mod_cast hρ))
  have hdB : B * d < ε := by
    have h := (le_div_iff₀ (by positivity : 0 < 2 * (B + 1))).mp
      (min_le_right ((ρ : ℝ) / 2) (ε / (2 * (B + 1))))
    change d * (2 * (B + 1)) ≤ ε at h
    nlinarith
  let η : ℝ≥0 := ⟨d / ((Lγ : ℝ) + 1), by positivity⟩
  have hη : 0 < (η : ℝ) := by
    change 0 < d / ((Lγ : ℝ) + 1)
    exact div_pos hd (by positivity)
  obtain ⟨F, hpF, K, L, hF, hFm, hK, hL, herr⟩ :=
    exists_affineCircleHomeomorph_approximation hc hm hp hη
  let Φ := affineCircleHomeomorph F hpF
  let γn := precomposeLipschitzContractibleLoop g γ ⟨Φ, Φ.continuous⟩ hK
  obtain ⟨Ln, hn⟩ := γn.property
  have hlenn : riemannianCurveLength g (fun t => γn.val.val (t : loopCircle)) 0 1 = l := by
    exact loop_length_comp_affineCircleMap g γ.val.val hγ F.continuous hFm.monotone hpF hn
  have hdist : (riemannianLoopDistance g γn.val.val δ.val.val : ℝ) ≤ d := by
    have h := loopDistance_precompose_le g γ.val.val hγ
      (⟨Φ, Φ.continuous⟩ : C(loopCircle, loopCircle)) (affineCircleMap ψ hc hp)
      (fun θ => (herr θ).le)
    have hntrace : γn.val.val = γ.val.val.comp (⟨Φ, Φ.continuous⟩ : C(loopCircle, loopCircle)) := rfl
    rw [← htrace, ← hntrace] at h
    have h' : (riemannianLoopDistance g γn.val.val δ.val.val : ℝ) ≤ (Lγ : ℝ) * η := by
      exact_mod_cast h
    apply h'.trans
    calc
      (Lγ : ℝ) * η ≤ ((Lγ : ℝ) + 1) * η := by gcongr; linarith
      _ = d := by
        change ((Lγ : ℝ) + 1) * (d / ((Lγ : ℝ) + 1)) = d
        exact mul_div_cancel₀ d (by positivity)
  have hnear : riemannianLoopDistance g γn.val.val δ.val.val < ρ := by
    exact_mod_cast hdist.trans_lt hdρ
  have ha := hann γn δ hnear
  have hA : leastSpanningArea g γn = leastSpanningArea g γ :=
    leastSpanningArea_precompose g γ Φ hK hL
  rw [hA, hlenn, hlenδ, abs_sub_comm] at ha
  have hbound : (C : ℝ) * riemannianLoopDistance g γn.val.val δ.val.val * (l + l) ≤ B * d := by
    dsimp only [B]
    calc
      (C : ℝ) * riemannianLoopDistance g γn.val.val δ.val.val * (l + l)
          = (C : ℝ) * (2 * l) * riemannianLoopDistance g γn.val.val δ.val.val := by ring
      _ ≤ (C : ℝ) * (2 * l) * d := mul_le_mul_of_nonneg_left hdist hB
  linarith [ha.trans hbound]

end DifferentialGeometry.Geometry
