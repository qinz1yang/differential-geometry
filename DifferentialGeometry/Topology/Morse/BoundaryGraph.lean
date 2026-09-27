import DifferentialGeometry.Analysis.Calculus.SmoothMax
import DifferentialGeometry.Topology.Diffeomorph.LocalizedGraph
import Mathlib.Tactic.FunProp

open scoped ContDiff Manifold

namespace DifferentialGeometry.Topology.Morse

theorem exists_isotopy_rounded_boundaryMorse_sublevel {n : ℕ}
    (a : Fin n → ℝ) (b : ContDiffBump (0 : Fin n → ℝ)) (c t₀ t₁ : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    let q : (Fin n → ℝ) → ℝ := fun x => c + ∑ i, a i * x i ^ 2
    let g : ℝ × (Fin n → ℝ) → ℝ := fun p =>
      Real.smoothMax ε 0 (q p.2 - (t₀ + b p.2 * p.1 * (t₁ - t₀)))
    (∀ s x, g (s, x) - max 0 (q x - (t₀ + b x * s * (t₁ - t₀))) ∈ Set.Icc 0 ε) ∧
    (∀ s x, ε ≤ |q x - (t₀ + b x * s * (t₁ - t₀))| →
      g (s, x) = max 0 (q x - (t₀ + b x * s * (t₁ - t₀)))) ∧
    (∀ s x, ‖x‖ ≤ b.rIn →
      g (s, x) = Real.smoothMax ε 0 (q x - (t₀ + s * (t₁ - t₀)))) ∧
    ∃ H : ℝ → (((Fin n → ℝ) × ℝ) ≃ₘ[ℝ] ((Fin n → ℝ) × ℝ)),
      ContDiff ℝ ∞ (fun z : ℝ × ((Fin n → ℝ) × ℝ) => H z.1 z.2) ∧
      ContDiff ℝ ∞ (fun z : ℝ × ((Fin n → ℝ) × ℝ) => (H z.1).symm z.2) ∧
      H 0 = Diffeomorph.refl 𝓘(ℝ, (Fin n → ℝ) × ℝ) ((Fin n → ℝ) × ℝ) ∞ ∧
      (∀ t (p : (Fin n → ℝ) × ℝ), (H t p).1 = p.1) ∧
      (∀ t x, H t (x, g (0, x)) = (x, g (Real.smoothTransition t, x))) ∧
      (∀ t (p : (Fin n → ℝ) × ℝ), g (0, p.1) = g (Real.smoothTransition t, p.1) →
        H t p = p ∧ (H t).symm p = p) ∧
      (∀ t (p : (Fin n → ℝ) × ℝ), b.rOut ≤ ‖p.1‖ →
        H t p = p ∧ (H t).symm p = p) ∧
      (∀ t (s : Set (Fin n → ℝ)), H t '' Set.graphOn (fun x => g (0, x)) s =
        Set.graphOn (fun x => g (Real.smoothTransition t, x)) s) ∧
      (∀ t (s : Set (Fin n → ℝ)),
        H t '' {p : (Fin n → ℝ) × ℝ | p.1 ∈ s ∧ g (0, p.1) ≤ p.2} =
          {p : (Fin n → ℝ) × ℝ | p.1 ∈ s ∧ g (Real.smoothTransition t, p.1) ≤ p.2}) ∧
      (∀ t (s : Set (Fin n → ℝ)),
        H t '' {p : (Fin n → ℝ) × ℝ | p.1 ∈ s ∧ g (0, p.1) < p.2} =
          {p : (Fin n → ℝ) × ℝ | p.1 ∈ s ∧ g (Real.smoothTransition t, p.1) < p.2}) ∧
      ∃ J : Set ((Fin n → ℝ) × ℝ), IsCompact J ∧ ∀ t : ℝ,
        Set.EqOn (H t) id Jᶜ ∧ Set.EqOn (H t).symm id Jᶜ := by
  intro q g
  have hq : ContDiff ℝ ∞ q := by
    dsimp only [q]
    fun_prop
  have hg : ContDiff ℝ ∞ g :=
    (Real.smoothMax.contDiff ε).comp
      (contDiff_const.prodMk ((hq.comp contDiff_snd).sub
        (contDiff_const.add
          (((b.contDiff.comp contDiff_snd).mul contDiff_fst).mul contDiff_const))))
  have hzero : ∀ x, b.rOut ≤ ‖x‖ → b x = 0 := by
    intro x hx
    exact b.zero_of_le_dist (by simpa only [dist_zero_right] using hx)
  have hfixed : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ∀ x ∉ Metric.closedBall (0 : Fin n → ℝ) b.rOut, g (s, x) = g (0, x) := by
    intro s hs x hx
    have hx' : b.rOut ≤ ‖x‖ :=
      (lt_of_not_ge (by simpa only [Metric.mem_closedBall, dist_zero_right] using hx)).le
    simp only [g, hzero x hx', zero_mul, add_zero]
  obtain ⟨H, hforward, hinverse, hstart, hfst, hgraph, hfiber, himage, hepi, hstrict, hcompact⟩ :=
    Diffeomorph.exists_isotopy_graphOn_family hg
      (isCompact_closedBall (0 : Fin n → ℝ) b.rOut) hfixed
  refine ⟨?_, ?_, ?_, H, hforward, hinverse, hstart, hfst, hgraph, hfiber, ?_,
    himage, hepi, hstrict, hcompact⟩
  · intro s x
    exact Real.smoothMax.sub_max_mem_Icc hε 0 (q x - (t₀ + b x * s * (t₁ - t₀)))
  · intro s x hx
    exact Real.smoothMax.eq_max_of_le hε (by simpa only [zero_sub, abs_neg] using hx)
  · intro s x hx
    have hb : b x = 1 :=
      b.one_of_mem_closedBall (by simpa only [Metric.mem_closedBall, dist_zero_right] using hx)
    simp only [g, hb, one_mul]
  · intro t p hp
    apply hfiber t p
    simp only [g, hzero p.1 hp, zero_mul, add_zero]

end DifferentialGeometry.Topology.Morse
