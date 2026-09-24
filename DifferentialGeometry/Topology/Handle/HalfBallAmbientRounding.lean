import DifferentialGeometry.Topology.Handle.HalfBallRounding
import DifferentialGeometry.Topology.Manifold.AmbientCornerRounding

open Set Metric
open scoped ContDiff Manifold

namespace OpenPartialHomeomorph

theorem halfBallCorner_closedBall_subset_target
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : ℝ) (v : sphere (0 : E) 1) {ε : ℝ} (hε : ε + ε ^ 2 < r ^ 2) :
    (univ : Set (sphere (0 : E) 1)) ×ˢ closedBall (0 : ℝ × ℝ) ε ⊆
      (halfBallCorner r v).target := by
  intro p hp
  have hb := hp.2
  rw [mem_closedBall_zero_iff, Prod.norm_def, max_le_iff,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_le, abs_le] at hb
  change 0 < r ^ 2 - p.2.1 - p.2.2 ^ 2
  nlinarith [mul_nonneg (sub_nonneg.mpr hb.2.2) (by linarith [hb.2.1] : 0 ≤ ε + p.2.2)]

end OpenPartialHomeomorph

namespace DifferentialGeometry.Topology.Handle

theorem halfBallRounding_eq_smoothAbsCorner
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : ℝ) (v : sphere (0 : E) 1) {ε : ℝ} (hε : 0 < ε) {p : E × ℝ}
    (hp : ‖p.1‖ ^ 2 + p.2 ^ 2 ≤ r ^ 2 ∧ 0 ≤ p.2)
    (hboundary : ‖p.1‖ ^ 2 + p.2 ^ 2 = r ^ 2 ∨ p.2 = 0) (hx : p.1 ≠ 0) :
    halfBallRounding r ε p = (OpenPartialHomeomorph.halfBallCorner r v).symm
      (((OpenPartialHomeomorph.halfBallCorner r v) p).1,
        Homeomorph.smoothAbsCorner hε ((OpenPartialHomeomorph.halfBallCorner r v) p).2) := by
  let e := OpenPartialHomeomorph.halfBallCorner r v
  have hps : p ∈ e.source := hx
  let q : {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2} := ⟨(e p).2, by
    change 0 ≤ r ^ 2 - ‖p.1‖ ^ 2 - p.2 ^ 2 ∧ 0 ≤ p.2
    exact ⟨by linarith [hp.1], hp.2⟩⟩
  have hq : q.val.1 = 0 ∨ q.val.2 = 0 := by
    rcases hboundary with h | h
    · left
      change r ^ 2 - ‖p.1‖ ^ 2 - p.2 ^ 2 = 0
      linarith
    · exact Or.inr h
  have heq := Homeomorph.smoothAbsCorner_eq_smoothAbsQuadrant hε q hq
  have h := halfBallRounding_halfBallCorner_symm r ε v (e.map_source hps)
  change halfBallRounding r ε (e.symm (e p)) =
    e.symm ((e p).1, (Homeomorph.smoothAbsQuadrant hε q).val) at h
  rw [e.left_inv hps, ← heq] at h
  exact h

theorem exists_homeomorph_halfBall_corner_rounding
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]
    (r : ℝ) (v : sphere (0 : E) 1) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) (hsmall : ε + ε ^ 2 < r ^ 2) :
    ∃ H : (E × ℝ) ≃ₜ (E × ℝ),
      H '' {p : E × ℝ | ‖p.1‖ ^ 2 + p.2 ^ 2 ≤ r ^ 2 ∧ 0 ≤ p.2} =
        {p | Real.smoothMax ε (‖p.1‖ ^ 2 + p.2 ^ 2 - r ^ 2) (-p.2) ≤ 0} ∧
      (∀ x : E, ‖x‖ ^ 2 ≤ r ^ 2 → H (x, 0) = halfBallRounding r ε (x, 0)) ∧
      ∀ p : E × ℝ, ¬(‖p.1‖ ^ 2 = r ^ 2 ∧ p.2 = 0) →
        IsLocalDiffeomorphAt 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E × ℝ) ∞ H p ∧
          IsLocalDiffeomorphAt 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E × ℝ) ∞ H.symm (H p) := by
  let _ : FiniteDimensional ℝ E := FiniteDimensional.of_finrank_pos (by
    rw [(Fact.out : Module.finrank ℝ E = n + 1)]
    omega)
  let e := PartialDiffeomorph.halfBallCorner (n := n) r v
  have ht : (univ : Set (sphere (0 : E) 1)) ×ˢ closedBall (0 : ℝ × ℝ) ε ⊆ e.target :=
    OpenPartialHomeomorph.halfBallCorner_closedBall_subset_target r v hsmall
  obtain ⟨H, hH, _, _, hKs, hfix, _, hquad, _, hloc⟩ := e.exists_homeomorph_smoothAbs_corner hε ht
  have hεr : ε < min 1 (r ^ 2) := lt_min hε1 (by nlinarith [sq_nonneg ε])
  refine ⟨H, ?_, ?_, ?_⟩
  · rw [hquad _ (fun p hp => OpenPartialHomeomorph.halfBallCorner_symm_mem_halfBall r v hp)]
    exact OpenPartialHomeomorph.smoothAbsQuadrantSet_halfBallCorner r v hε hεr
  · intro x hx
    by_cases hx0 : x = 0
    · subst x
      rw [halfBallRounding_zero_fst]
      apply hfix
      intro h
      exact hKs h rfl
    · rw [hH (x, 0) hx0]
      exact (halfBallRounding_eq_smoothAbsCorner r v hε
        (p := (x, 0)) (by simpa using And.intro hx (le_refl (0 : ℝ))) (Or.inr rfl) hx0).symm
  · intro p hp
    apply hloc p
    rintro ⟨⟨θ, z⟩, ⟨_, hz⟩, rfl⟩
    have hz' : z = 0 := hz
    subst z
    apply hp
    change ‖Real.sqrt (r ^ 2 - 0 - 0 ^ 2) • θ.val‖ ^ 2 = r ^ 2 ∧ (0 : ℝ) = 0
    simp only [zero_pow two_ne_zero, sub_zero, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), norm_eq_of_mem_sphere, mul_one,
      Real.sq_sqrt (sq_nonneg r), and_self]

end DifferentialGeometry.Topology.Handle
