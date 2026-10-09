import DifferentialGeometry.Geometry.Metric.Isometry.FiniteJetBounds


set_option autoImplicit false

namespace DifferentialGeometry.CheegerGromovCompactness.MetricIsometry

open Filter Topology
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

private noncomputable local instance finiteTransitionBilinearNormedGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup

private noncomputable local instance finiteTransitionBilinearNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace

theorem exists_eventual_finite_isometry_jet_bound_of_compact_image
    (N : ℕ)
    (B C : ℕ → E → E →L[ℝ] E →L[ℝ] ℝ) (Φ : ℕ → E → E)
    {U V : Set E} (hU : IsOpen U) (hV : IsOpen V)
    {Q : Set E} (hQ : IsCompact Q) (hQV : Q ⊆ V)
    (hB : ∀ᶠ k in atTop, ContDiffOn ℝ (N : WithTop ℕ∞) (B k) U)
    (hC : ∀ᶠ k in atTop, ContDiffOn ℝ (N : WithTop ℕ∞) (C k) V)
    (hΦ : ∀ᶠ k in atTop, ContDiffOn ℝ ((N + 1 : ℕ) : WithTop ℕ∞) (Φ k) U)
    (hmap : ∀ᶠ k in atTop, Set.MapsTo (Φ k) U Q)
    (hiso : ∀ᶠ k in atTop, ∀ x, x ∈ U → ∀ v w,
      B k x v w = C k (Φ k x) (fderiv ℝ (Φ k) x v) (fderiv ℝ (Φ k) x w))
    (hsymm : ∀ᶠ k in atTop, ∀ y, y ∈ V → ∀ v w, C k y v w = C k y w v)
    (hBequiv : ∀ᶠ k in atTop, ∀ x, x ∈ U → ∀ v,
      (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ B k x v v ∧ B k x v v ≤ 2 * ‖v‖ ^ 2)
    (hClower : ∀ᶠ k in atTop, ∀ y, y ∈ V → ∀ v, (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ C k y v v)
    (CB CC : ℕ → ℝ)
    (hBjets : ∀ q, 1 ≤ q → q ≤ N → ∀ᶠ k in atTop, ∀ x ∈ U,
      ‖iteratedFDeriv ℝ q (B k) x‖ ≤ CB q)
    (hCjets : ∀ q, 1 ≤ q → q ≤ N → ∀ᶠ k in atTop, ∀ y ∈ V,
      ‖iteratedFDeriv ℝ q (C k) y‖ ≤ CC q) :
    ∃ M : ℝ, ∀ᶠ k in atTop, ∀ q, q ≤ N + 1 → ∀ x ∈ U,
      ‖iteratedFDeriv ℝ q (Φ k) x‖ ≤ M := by
  classical
  let D : ℝ := 1 + ∑ i ∈ Finset.range (N + 1), (max (CB i) 0 + max (CC i) 0)
  have hD1 : 1 ≤ D := by
    have hs : 0 ≤ ∑ i ∈ Finset.range (N + 1), (max (CB i) 0 + max (CC i) 0) :=
      Finset.sum_nonneg fun i _ => add_nonneg (le_max_right _ _) (le_max_right _ _)
    dsimp only [D]
    linarith
  have hCD : ∀ i, i ≤ N → CB i ≤ D ∧ CC i ≤ D := by
    intro i hi
    have hm : i ∈ Finset.range (N + 1) := Finset.mem_range.mpr (by omega)
    have hs := Finset.single_le_sum
      (fun j (_ : j ∈ Finset.range (N + 1)) =>
        add_nonneg (le_max_right (CB j) 0) (le_max_right (CC j) 0)) hm
    dsimp only [D]
    constructor <;> linarith [le_max_left (CB i) 0, le_max_left (CC i) 0,
      le_max_right (CB i) 0, le_max_right (CC i) 0]
  have htail : ∀ᶠ k in atTop, ∀ i : Fin (N + 1), 1 ≤ (i : ℕ) →
      (∀ x ∈ U, ‖iteratedFDeriv ℝ (i : ℕ) (B k) x‖ ≤ CB i) ∧
      (∀ y ∈ V, ‖iteratedFDeriv ℝ (i : ℕ) (C k) y‖ ≤ CC i) := by
    apply Filter.eventually_all.mpr
    intro i
    by_cases hi : 1 ≤ (i : ℕ)
    · exact ((hBjets i hi (by omega)).and (hCjets i hi (by omega))).mono fun _ h _ => h
    · exact Eventually.of_forall fun _ h => False.elim (hi h)
  obtain ⟨M, hM⟩ := exists_isometry_jet_bound_of_finite_metric_bounds (E0 := E) N D
  obtain ⟨Z, hZ⟩ := hQ.isBounded.exists_norm_le
  refine ⟨max Z M, ?_⟩
  filter_upwards [htail, hB, hC, hΦ, hmap, hiso, hsymm, hBequiv, hClower]
    with k hk hkB hkC hkΦ hkmap hkiso hksymm hkBequiv hkClower
  intro q hq x hx
  rcases q with _ | q
  · rw [norm_iteratedFDeriv_zero]
    exact (hZ (Φ k x) (hkmap hx)).trans (le_max_left _ _)
  · apply le_trans ?_ (le_max_right Z M)
    apply hM (B k) (C k) (Φ k) U V hU hV hkB hkC hkΦ
      (fun z hz => hQV (hkmap hz)) hkiso hksymm hkBequiv hkClower _ _
      (q + 1) (by omega) hq x hx
    · intro i hi hiN z hz
      exact ((hk ⟨i, by omega⟩ hi).1 z hz).trans
        ((hCD i hiN).1.trans (le_self_pow₀ hD1 (by omega)))
    · intro i hi hiN z hz
      exact ((hk ⟨i, by omega⟩ hi).2 z hz).trans
        ((hCD i hiN).2.trans (le_self_pow₀ hD1 (by omega)))

end DifferentialGeometry.CheegerGromovCompactness.MetricIsometry
