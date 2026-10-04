import DifferentialGeometry.Analysis.Calculus.Compactness.CountableFiniteJet.Mixed
import DifferentialGeometry.Geometry.Metric.Isometry.CompactImageFiniteJetBounds


set_option autoImplicit false
noncomputable section
open Filter Topology Set
open scoped ContDiff
namespace DifferentialGeometry.CheegerGromovCompactness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

private noncomputable local instance atlasBilinearNormedGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance atlasBilinearNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace

theorem exists_normalized_atlas_finite_subsequence
    {ι κ : Type*} [Countable ι] [Countable κ]
    (K : ℕ) (hK : 1 ≤ K) (source target : κ → ι)
    {V : ι → Set E} {W : κ → Set E}
    (hV : ∀ a, IsOpen (V a)) (hW : ∀ j, IsOpen (W j))
    (hWV : ∀ j, W j ⊆ V (source j))
    (B : ι → ℕ → E → E →L[ℝ] E →L[ℝ] ℝ)
    (Φ : κ → ℕ → E → E) (T : κ → E → E) (A : ι → ℝ)
    (hB : ∀ a, ∀ᶠ i in atTop, ContDiffOn ℝ K (B a i) (V a))
    (hsymm : ∀ a, ∀ᶠ i in atTop, ∀ x ∈ V a, ∀ v w,
      B a i x v w = B a i x w v)
    (hell : ∀ a, ∀ᶠ i in atTop, ∀ x ∈ V a, ∀ v,
      (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ B a i x v v ∧ B a i x v v ≤ 2 * ‖v‖ ^ 2)
    (hjets : ∀ a, ∀ᶠ i in atTop, ∀ r : ℕ, r ≤ K → ∀ x ∈ V a,
      ‖iteratedFDeriv ℝ r (B a i) x‖ ≤ A a)
    (hΦ : ∀ j, ∀ᶠ i in atTop, ContDiffOn ℝ (K + 1 : ℕ) (Φ j i) (W j))
    (hbuffer : ∀ j, ∃ Q : Set E, IsCompact Q ∧ Q ⊆ V (target j) ∧
      ∀ᶠ i in atTop, MapsTo (Φ j i) (W j) Q)
    (hpull : ∀ j, ∀ᶠ i in atTop, ∀ x ∈ W j,
      B (source j) i x = (B (target j) i (Φ j i x)).bilinearComp
        (fderiv ℝ (Φ j i) x) (fderiv ℝ (Φ j i) x))
    (hT : ∀ j x, x ∈ W j → Tendsto (fun i => Φ j i x) atTop (𝓝 (T j x))) :
    ∃ (σ : ℕ → ℕ) (b : ι → E → E →L[ℝ] E →L[ℝ] ℝ), StrictMono σ ∧
      (∀ a, ContDiffOn ℝ (K - 1 : ℕ) (b a) (V a) ∧
        ∀ D : Set E, IsCompact D → D ⊆ V a →
          MapCPConvergenceOn D (K - 1) (fun i => B a (σ i)) (b a)) ∧
      (∀ j, ContDiffOn ℝ K (T j) (W j) ∧
        ∀ D : Set E, IsCompact D → D ⊆ W j →
          MapCPConvergenceOn D K (fun i => Φ j (σ i)) (T j)) := by
  have horder : K - 1 + 1 = K := Nat.sub_add_cancel hK
  have htransition : ∀ j, ∃ L : ℝ, ∀ᶠ i in atTop, ∀ r, r ≤ K + 1 →
      ∀ x ∈ W j, ‖iteratedFDeriv ℝ r (Φ j i) x‖ ≤ L := by
    intro j
    obtain ⟨Q, hQ, hQV, hmap⟩ := hbuffer j
    refine MetricIsometry.exists_eventual_finite_isometry_jet_bound_of_compact_image
      K (B (source j)) (B (target j)) (Φ j) (hW j) (hV (target j)) hQ hQV
      ((hB (source j)).mono fun _ hi => hi.mono (hWV j))
      (hB (target j)) (hΦ j) hmap ?_ (hsymm (target j)) ?_ ?_
      (fun _ => A (source j)) (fun _ => A (target j)) ?_ ?_
    · filter_upwards [hpull j] with i hi
      intro x hx v w
      exact congrArg (fun C : E →L[ℝ] E →L[ℝ] ℝ => C v w) (hi x hx)
    · exact (hell (source j)).mono fun _ hi x hx v => hi x (hWV j hx) v
    · exact (hell (target j)).mono fun _ hi y hy v => (hi y hy v).1
    · intro q _ hq
      exact (hjets (source j)).mono fun _ hi x hx => hi q hq x (hWV j hx)
    · intro q _ hq
      exact (hjets (target j)).mono fun _ hi y hy => hi q hq y hy
  apply exists_mixed_finite_order_subsequence_with_prescribed_limits (K - 1) K
    hV hW B Φ T
  · simpa only [horder] using hB
  · exact hΦ
  · intro a D _ hDV q hq
    refine ⟨A a, ?_⟩
    exact (hjets a).mono fun _ hi x hx => hi q (horder ▸ hq) x (hDV hx)
  · intro j D _ hDW q hq
    obtain ⟨L, hL⟩ := htransition j
    exact ⟨L, hL.mono fun _ hi x hx => hi q hq x (hDW hx)⟩
  · exact hT

end DifferentialGeometry.CheegerGromovCompactness
