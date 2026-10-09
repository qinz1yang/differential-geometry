import DifferentialGeometry.Topology.Manifold.SmoothApproximation.Boundary.RelativeOpenness
import DifferentialGeometry.Topology.Manifold.SmoothApproximation.Boundary.NormalDerivative
import DifferentialGeometry.Geometry.Boundary.Manifold.Basic

/-!
# W3: relative smooth approximation of diffeomorphisms of manifolds with boundary

`exists_smooth_diffeomorph_seq_rel_boundary` (collar form of W1 + W2, with the four clauses of
the external review §3.2): a `C^k` diffeomorphism `h` (`1 ≤ k`) of compact manifolds with
boundary (model `𝓡∂ (n + 1)`), already smooth on an open `O ⊇ ∂A`, is the limit of SMOOTH
diffeomorphisms of manifolds with boundary `Φ j : A ≃ₘ⟮𝓡∂, 𝓡∂⟯ B` which
(i) agree with `h` on one fixed smaller open `O' ⊇ ∂A` (relative fixedness on a smaller collar),
(ii) preserve the boundary,
(iii) have positive inward normal derivative along `∂A` for every defining function of `∂B` and
every strictly inward field, and
(iv) converge to `h` chart-wise in `C^k` on compact subsets of chart targets in the interior of the
half-space.

Assembly: `exists_smooth_seq_rel_chart_tendsto` (relative approximation, fixed on `O'`),
`eventually_exists_diffeomorph_of_rel_chart_tendsto` (openness relative to the boundary, using that
`h` is smooth with smooth inverse near `∂A`, `InverseSmooth.lean`), Mathlib's
`IsLocalDiffeomorphAt.isBoundaryPoint_iff` for (ii), and `pos_mfderiv_comp_of_diffeomorph` (A3-b)
for (iii).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open scoped Manifold Topology ContDiff
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

namespace DifferentialGeometry.Topology.Manifold.SmoothApproximation

open DifferentialGeometry.CheegerGromovCompactness

variable {n : ℕ}
  {A : Type*} [TopologicalSpace A] [ChartedSpace (EuclideanHalfSpace (n + 1)) A]
  [IsManifold (𝓡∂ (n + 1)) ∞ A] [T2Space A] [CompactSpace A]
  {B : Type*} [TopologicalSpace B] [ChartedSpace (EuclideanHalfSpace (n + 1)) B]
  [IsManifold (𝓡∂ (n + 1)) ∞ B]

/-- **W3 (relative boundary form of W1 + W2).** -/
theorem exists_smooth_diffeomorph_seq_rel_boundary {k : ℕ} (hk : 1 ≤ k)
    (h : A ≃ₘ^k⟮𝓡∂ (n + 1), 𝓡∂ (n + 1)⟯ B) {O : Set A} (hO : IsOpen O)
    (hbO : (𝓡∂ (n + 1)).boundary A ⊆ O)
    (hsmooth : ContMDiffOn (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) ∞ h O) :
    ∃ (O' : Set A) (Φ : ℕ → A ≃ₘ⟮𝓡∂ (n + 1), 𝓡∂ (n + 1)⟯ B),
      IsOpen O' ∧ (𝓡∂ (n + 1)).boundary A ⊆ O' ∧ O' ⊆ O ∧
      (∀ j, EqOn (Φ j) h O') ∧
      (∀ j x, (𝓡∂ (n + 1)).IsBoundaryPoint (Φ j x) ↔ (𝓡∂ (n + 1)).IsBoundaryPoint x) ∧
      (∀ j (r : B → ℝ), ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ) ∞ r → (∀ y, 0 ≤ r y) →
        (∀ y, r y = 0 ↔ (𝓡∂ (n + 1)).IsBoundaryPoint y) →
        (∀ y, (𝓡∂ (n + 1)).IsBoundaryPoint y → mfderiv (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ) r y ≠ 0) →
        ∀ V : (x : A) → TangentSpace (𝓡∂ (n + 1)) x,
        (∀ p : BoundaryManifold (𝓡∂ (n + 1)) A,
          0 < (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (n + 1))) (V p)) →
        ∀ p : BoundaryManifold (𝓡∂ (n + 1)) A,
          (0 : ℝ) < (mfderiv (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ) (r ∘ Φ j) p (V p) : ℝ)) ∧
      ∀ (p : A) (q : B) (K : Set (EuclideanSpace ℝ (Fin (n + 1)))), IsCompact K →
        K ⊆ (extChartAt (𝓡∂ (n + 1)) p).target → K ⊆ interior (range (𝓡∂ (n + 1))) →
        MapsTo (fun y => h ((extChartAt (𝓡∂ (n + 1)) p).symm y)) K
          (extChartAt (𝓡∂ (n + 1)) q).source →
        (∀ᶠ j in atTop, MapsTo (fun y => Φ j ((extChartAt (𝓡∂ (n + 1)) p).symm y)) K
          (extChartAt (𝓡∂ (n + 1)) q).source) ∧
        MapCPConvergenceOn K k
          (fun j y => extChartAt (𝓡∂ (n + 1)) q (Φ j ((extChartAt (𝓡∂ (n + 1)) p).symm y)))
          (fun y => extChartAt (𝓡∂ (n + 1)) q (h ((extChartAt (𝓡∂ (n + 1)) p).symm y))) := by
  have hk' : (1 : ℕ∞ω) ≤ (k : ℕ∞ω) := by exact_mod_cast hk
  have hk0 : (k : ℕ∞ω) ≠ 0 := (lt_of_lt_of_le zero_lt_one hk').ne'
  have : T2Space B := h.toHomeomorph.symm.isEmbedding.t2Space
  have : CompactSpace B := h.toHomeomorph.compactSpace
  have hint : ∀ x, (𝓡∂ (n + 1)).IsInteriorPoint x → (𝓡∂ (n + 1)).IsInteriorPoint (h x) :=
    fun x hx => ((h.isLocalDiffeomorph x).isInteriorPoint_iff hk0).mp hx
  obtain ⟨O', hs, hO', hbO', hO'O, hssm, hsO', hLU, hconv⟩ :=
    exists_smooth_seq_rel_chart_tendsto k h.contMDiff hO hbO hsmooth hint
  have hev := eventually_exists_diffeomorph_of_rel_chart_tendsto hk' h hk hO' hbO'
    (hsmooth.mono hO'O) hssm hsO' hLU hconv
  obtain ⟨j₀, hj₀⟩ := eventually_atTop.mp hev
  choose Φ hΦ using fun j : ℕ => hj₀ (j + j₀) (Nat.le_add_left j₀ j)
  have hshift : StrictMono fun j : ℕ => j + j₀ := fun a b hab => Nat.add_lt_add_right hab j₀
  refine ⟨O', Φ, hO', hbO', hO'O, fun j x hx => ?_, fun j x => ?_, ?_, ?_⟩
  · rw [hΦ j]
    exact hsO' (j + j₀) hx
  · exact (((Φ j).isLocalDiffeomorph x).isBoundaryPoint_iff (by simp)).symm
  · intro j r hr hrn hrzero hrd V hV p
    exact pos_mfderiv_comp_of_diffeomorph (k := ∞) (by exact_mod_cast le_top) (Φ j)
      (hr.of_le (by exact_mod_cast le_top)) hrn (fun y hy => (hrzero y).mpr hy) hrd p.2 (V p)
      (hV p)
  · intro p q K hK hKt hKi hKmap
    obtain ⟨hmap, hcv⟩ := hconv p q K hK hKt hKi hKmap
    refine ⟨?_, ?_⟩
    · filter_upwards [(tendsto_add_atTop_nat j₀).eventually hmap] with j hj
      rw [hΦ j]
      exact hj
    · have h2 := hcv.comp_subseq hshift
      simp only [hΦ]
      exact h2

end DifferentialGeometry.Topology.Manifold.SmoothApproximation
