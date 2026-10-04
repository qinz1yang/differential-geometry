import DifferentialGeometry.Topology.Ehresmann.CircleFibreTransport

/-!
# Fibre bundles over the circle: two opposite slabs

Consumer of `CircleFibreTransport.lean` (lane ASM-L3). The cut map of a fibre bundle over the
circle gives two slabs `A, P : F × ℝ ⇀ M`, each a partial diffeomorphism on `F × (-1/2, 3/2)`:
`P (z, s) = Ψ (z, -1/4 + s/2)` covers the arc `[-1/4, 1/4]` and `A (z, s) = Ψ (z, 1/4 + s/2)` the
arc `[1/4, 3/4]`. They meet exactly along the two end fibres, `A (z, 0) = P (z, 1)` and
`A (z, 1) = P (φ z, 0)` with the monodromy `φ`, and cover `M`. This is the input shape of the
double-slab recognition `DoubleCylinder.nonempty_diffeomorph_sphereTwoTimesCircle_of_oriented_opposite_slabs`
used for `S²`-bundles (L3-S²).
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.Ehresmann.CircleFibre

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
  {EF HF F : Type*} [NormedAddCommGroup EF] [NormedSpace ℝ EF]
  [TopologicalSpace HF] {IF : ModelWithCorners ℝ EF HF}
  [TopologicalSpace F] [ChartedSpace HF F] [Nonempty F]

/-- **Two opposite slabs** of a fibre bundle over the circle, meeting along two whole fibres. -/
theorem exists_circleSlabs (p : M → Circle) (hp : ContMDiff I (𝓡 1) ∞ p)
    (hsub : ∀ x, Surjective (mfderiv I (𝓡 1) p x)) (f : F → M)
    (hf : IsSmoothEmbedding IF I ∞ f) (hr : range f = p ⁻¹' {1}) :
    ∃ (A P : PartialDiffeomorph (IF.prod 𝓘(ℝ, ℝ)) I (F × ℝ) M ∞) (φ : F ≃ₘ⟮IF, IF⟯ F),
      univ ×ˢ Icc (0 : ℝ) 1 ⊆ A.source ∧ univ ×ˢ Icc (0 : ℝ) 1 ⊆ P.source ∧
      (∀ z, A (z, 0) = P (z, 1)) ∧ (∀ z, A (z, 1) = P (φ z, 0)) ∧
      A '' (univ ×ˢ Icc (0 : ℝ) 1) ∩ P '' (univ ×ˢ Icc (0 : ℝ) 1) ⊆
        P '' (univ ×ˢ ({0} : Set ℝ)) ∪ P '' (univ ×ˢ ({1} : Set ℝ)) ∧
      A '' (univ ×ˢ Icc (0 : ℝ) 1) ∪ P '' (univ ×ˢ Icc (0 : ℝ) 1) = univ := by
  obtain ⟨Ψ, φ, -, -, -, hper, hinj, hsurj, hchart⟩ := exists_circleCut p hp hsub f hf hr
  obtain ⟨A, hAs, hAf⟩ := hchart (1 / 4) (1 / 2) (-(1 / 2)) (3 / 2) (by norm_num) (by norm_num)
  obtain ⟨P, hPs, hPf⟩ := hchart (-(1 / 4)) (1 / 2) (-(1 / 2)) (3 / 2) (by norm_num) (by norm_num)
  have hA (q : F × ℝ) : A q = Ψ (q.1, 1 / 4 + 1 / 2 * q.2) := congrFun hAf q
  have hP (q : F × ℝ) : P q = Ψ (q.1, -(1 / 4) + 1 / 2 * q.2) := congrFun hPf q
  have hIcc : (univ : Set F) ×ˢ Icc (0 : ℝ) 1 ⊆ univ ×ˢ Ioo (-(1 / 2)) (3 / 2) := by
    rintro q ⟨-, h₁, h₂⟩
    exact ⟨mem_univ _, by linarith, by linarith⟩
  have hPlow (z : F) {s : ℝ} (hs : s < 1) :
      P (z, s) = Ψ (φ.symm z, 3 / 4 + 1 / 2 * s) := by
    rw [hP, show (3 / 4 : ℝ) + 1 / 2 * s = (-(1 / 4) + 1 / 2 * s) + 1 by ring, hper,
      φ.apply_symm_apply]
  refine ⟨A, P, φ, hAs ▸ hIcc, hPs ▸ hIcc, fun z => ?_, fun z => ?_, ?_, ?_⟩
  · rw [hA, hP]
    norm_num
  · rw [hA, hP, show (1 / 4 : ℝ) + 1 / 2 * 1 = (-(1 / 4) + 1 / 2 * 0) + 1 by ring, hper]
  · rintro x ⟨⟨⟨z, s⟩, ⟨-, hs₀, hs₁⟩, rfl⟩, ⟨⟨z', s'⟩, ⟨-, hs₀', hs₁'⟩, hx⟩⟩
    rcases eq_or_lt_of_le hs₁' with h1 | h1
    · right
      exact ⟨(z', s'), ⟨mem_univ _, h1⟩, hx⟩
    · left
      refine ⟨(z', s'), ⟨mem_univ _, ?_⟩, hx⟩
      rw [hPlow z' h1, hA] at hx
      have hq := hinj (1 / 4) ⟨mem_univ _, by constructor <;> linarith⟩
        ⟨mem_univ _, by constructor <;> linarith⟩ hx
      have h2 := congrArg Prod.snd hq
      simp only at h2
      change s' = 0
      linarith
  · refine eq_univ_of_forall fun x => ?_
    obtain ⟨z, t, ht, rfl⟩ := hsurj (-(1 / 4)) x
    by_cases h : t ≤ 1 / 4
    · right
      refine ⟨(z, 2 * t + 1 / 2), ⟨mem_univ _, by constructor <;> linarith [ht.1]⟩, ?_⟩
      rw [hP]
      congr 2
      ring
    · left
      refine ⟨(z, 2 * t - 1 / 2), ⟨mem_univ _, by constructor <;> linarith [ht.2]⟩, ?_⟩
      rw [hA]
      congr 2
      ring

end DifferentialGeometry.Topology.Ehresmann.CircleFibre
