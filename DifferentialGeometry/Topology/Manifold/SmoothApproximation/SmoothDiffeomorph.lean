import DifferentialGeometry.Topology.Manifold.SmoothApproximation.ManifoldValued
import DifferentialGeometry.Topology.Manifold.SmoothApproximation.DiffeomorphOpenness

/-!
# `C^k`-diffeomorphic compact manifolds are smoothly diffeomorphic (W1 + W2)

`exists_smooth_diffeomorph_seq_chart_tendsto`: a `C^k` diffeomorphism (`1 ≤ k`) between compact
Hausdorff manifolds with boundaryless models is the chart-wise `C^k` limit (in the sense of W1) of
smooth diffeomorphisms. `nonempty_diffeomorph_of_diffeomorph`: in particular the two manifolds
are smoothly diffeomorphic. Compactness and the Hausdorff property of the target are inherited
from the source along `h`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Topology.Manifold.SmoothApproximation

open DifferentialGeometry.CheegerGromovCompactness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {A : Type*} [TopologicalSpace A] [ChartedSpace H A] [IsManifold I ∞ A]
  [T2Space A] [CompactSpace A]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [J.Boundaryless]
  {B : Type*} [TopologicalSpace B] [ChartedSpace H' B] [IsManifold J ∞ B]

/-- **W1 + W2.** A `C^k` diffeomorphism (`1 ≤ k`) of compact boundaryless manifolds is the
chart-wise `C^k` limit of smooth diffeomorphisms `Φ j`: for all charts `φ_p`, `ψ_q` and every
compact `K ⊆ target φ_p` with `h (φ_p⁻¹ K) ⊆ source ψ_q`, eventually
`Φ j (φ_p⁻¹ K) ⊆ source ψ_q`, and `ψ_q ∘ Φ j ∘ φ_p⁻¹ → ψ_q ∘ h ∘ φ_p⁻¹` in `C^k` on `K`. -/
theorem exists_smooth_diffeomorph_seq_chart_tendsto
    (k : ℕ) (hk : 1 ≤ k) (h : A ≃ₘ^k⟮I, J⟯ B) :
    ∃ Φ : ℕ → A ≃ₘ⟮I, J⟯ B,
      ∀ (p : A) (q : B) (K : Set E), IsCompact K → K ⊆ (extChartAt I p).target →
        MapsTo (fun y => h ((extChartAt I p).symm y)) K (extChartAt J q).source →
        (∀ᶠ j in atTop, MapsTo (fun y => Φ j ((extChartAt I p).symm y)) K
            (extChartAt J q).source) ∧
          MapCPConvergenceOn K k (fun j y => extChartAt J q (Φ j ((extChartAt I p).symm y)))
            (fun y => extChartAt J q (h ((extChartAt I p).symm y))) := by
  have : T2Space B := h.toHomeomorph.symm.isEmbedding.t2Space
  have : CompactSpace B := h.toHomeomorph.compactSpace
  obtain ⟨hs, hsm, hconv⟩ := exists_smooth_seq_chart_tendsto k h.contMDiff
  have hev := eventually_exists_diffeomorph_of_chart_tendsto (n := (k : ℕ∞ω))
    (by exact_mod_cast hk) h (r := ⊤) le_top hk hsm hconv
  obtain ⟨j₀, hj₀⟩ := eventually_atTop.mp hev
  choose Φ hΦ using fun j : ℕ => hj₀ (j + j₀) (Nat.le_add_left j₀ j)
  have hshift : StrictMono fun j : ℕ => j + j₀ := fun a b hab => Nat.add_lt_add_right hab j₀
  refine ⟨Φ, fun p q K hK hKt hKmap => ?_⟩
  obtain ⟨hev', hcv⟩ := hconv p q K hK hKt hKmap
  refine ⟨?_, ?_⟩
  · filter_upwards [(tendsto_add_atTop_nat j₀).eventually hev'] with j hj
    rw [hΦ j]
    exact hj
  · have h' := hcv.comp_subseq hshift
    simp only [← hΦ] at h'
    exact h'

/-- **`C^k`-diffeomorphic compact boundaryless manifolds are smoothly diffeomorphic** (`1 ≤ k`). -/
theorem nonempty_diffeomorph_of_diffeomorph (k : ℕ) (hk : 1 ≤ k) (h : A ≃ₘ^k⟮I, J⟯ B) :
    Nonempty (A ≃ₘ⟮I, J⟯ B) :=
  ⟨(exists_smooth_diffeomorph_seq_chart_tendsto k hk h).choose 0⟩

end DifferentialGeometry.Topology.Manifold.SmoothApproximation
