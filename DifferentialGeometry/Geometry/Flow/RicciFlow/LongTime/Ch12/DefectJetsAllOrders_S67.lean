import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.DefectJetsLandau_S67

set_option autoImplicit false

/-!
# CH12-S67 / G2b: all orders `j ≤ N` at once

`defectJet_small_of_landau_S67` gives order `N` only; `ckErr_window_lt_S57` needs the defect-jet bound
`η r` for every order `j ≤ k` on the same set `K`.  Taking the minimum of the finitely many `η₀_j`
gives `defectJet_small_all_orders_S67` (conclusion on `K N ⊆ K j`).
-/

noncomputable section
open Set Bundle Manifold DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff Topology
namespace GC.LongTime.Ch12

section Pure

variable {M : Type*}

theorem landau_small_all_S67 (d : ℕ → ℝ → M → ℝ) (R : Set ℝ) (hR : ∀ r ∈ R, 0 < r)
    (K : ℕ → Set M) (hKm : ∀ j, K (j + 1) ⊆ K j) (N : ℕ) {C B : ℝ} (hC : 1 ≤ C) (hB : 1 ≤ B)
    (hstep : ∀ j, j < N → ∀ r ∈ R, ∀ α β : ℝ, 0 ≤ α → 0 ≤ β →
      (∀ x ∈ K j, d j r x ≤ α) → (∀ x ∈ K j, d (j + 2) r x ≤ β) →
      ∀ x ∈ K (j + 1), d (j + 1) r x ≤ C * (Real.sqrt (α * β) + α))
    (hcrude : ∀ j ≤ N + 1, ∀ r ∈ R, ∀ x ∈ K 0, d j r x ≤ B * r) (η : ℝ) (hη : 0 < η) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ((∀ r ∈ R, ∀ x ∈ K 0, d 0 r x ≤ η₀ * r) →
      ∀ j ≤ N, ∀ x ∈ K N, ∀ r ∈ R, d j r x ≤ η * r) := by
  have hanti : ∀ i j, i ≤ j → K j ⊆ K i := by
    intro i j hij
    exact antitone_nat_of_succ_le hKm hij
  have each : ∀ j ≤ N, ∃ e : ℝ, 0 < e ∧ ((∀ r ∈ R, ∀ x ∈ K 0, d 0 r x ≤ e * r) →
      ∀ x ∈ K j, ∀ r ∈ R, d j r x ≤ η * r) := by
    intro j hj
    exact landau_small_S67 d R hR K hKm j hC hB (fun i hi => hstep i (by omega))
      (fun i hi => hcrude i (by omega)) η hη
  have comb : ∀ m ≤ N, ∃ e : ℝ, 0 < e ∧ ∀ j ≤ m, ((∀ r ∈ R, ∀ x ∈ K 0, d 0 r x ≤ e * r) →
      ∀ x ∈ K j, ∀ r ∈ R, d j r x ≤ η * r) := by
    intro m
    induction m with
    | zero =>
      intro hm
      obtain ⟨e, he, h⟩ := each 0 hm
      exact ⟨e, he, fun j hj => by
        have : j = 0 := by omega
        subst this
        exact h⟩
    | succ m ih =>
      intro hm
      obtain ⟨e1, he1, h1⟩ := ih (by omega)
      obtain ⟨e2, he2, h2⟩ := each (m + 1) hm
      have mono : ∀ e e' : ℝ, e' ≤ e → (∀ r ∈ R, ∀ x ∈ K 0, d 0 r x ≤ e' * r) →
          ∀ r ∈ R, ∀ x ∈ K 0, d 0 r x ≤ e * r :=
        fun e e' hee' h0 r hr x hx =>
          (h0 r hr x hx).trans (mul_le_mul_of_nonneg_right hee' (hR r hr).le)
      refine ⟨min e1 e2, lt_min he1 he2, fun j hj h0 => ?_⟩
      by_cases hjm : j ≤ m
      · exact h1 j hjm (mono e1 _ (min_le_left _ _) h0)
      · have : j = m + 1 := by omega
        subst this
        exact h2 (mono e2 _ (min_le_right _ _) h0)
  obtain ⟨e, he, hall⟩ := comb N le_rfl
  exact ⟨e, he, fun h0 j hj x hx r hr => hall j hj h0 x (hanti j N hj hx) r hr⟩

end Pure

section Concrete

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

omit [I.Boundaryless] in
/-- **W-B2 reduced, all orders `j ≤ N`** — the shape of the `hdef` clause of `ckErr_window_lt_S57`
(`R = Ioo t u`, `K := K N`). -/
theorem defectJet_small_all_orders_S67 {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (h : SmoothRiemannianMetric I M)
    (R : Set ℝ) (hR : ∀ r ∈ R, 0 < r) (K : ℕ → Set M) (hKm : ∀ j, K (j + 1) ⊆ K j) (N : ℕ)
    {C B : ℝ} (hC : 1 ≤ C) (hB : 1 ≤ B)
    (hstep : ∀ j, j < N → ∀ r ∈ R, ∀ α β : ℝ, 0 ≤ α → 0 ≤ β →
      (∀ x ∈ K j, Real.sqrt (normSq0S h x (j + 2) (defectJet_S57 S h j r x)) ≤ α) →
      (∀ x ∈ K j, Real.sqrt (normSq0S h x (j + 2 + 2) (defectJet_S57 S h (j + 2) r x)) ≤ β) →
      ∀ x ∈ K (j + 1),
        Real.sqrt (normSq0S h x (j + 1 + 2) (defectJet_S57 S h (j + 1) r x)) ≤
          C * (Real.sqrt (α * β) + α))
    (hcrude : ∀ j ≤ N + 1, ∀ r ∈ R, ∀ x ∈ K 0,
      Real.sqrt (normSq0S h x (j + 2) (defectJet_S57 S h j r x)) ≤ B * r)
    (η : ℝ) (hη : 0 < η) :
    ∃ η₀ : ℝ, 0 < η₀ ∧
      ((∀ r ∈ R, ∀ x ∈ K 0, Real.sqrt (normSq0S h x (0 + 2) (defectJet_S57 S h 0 r x)) ≤ η₀ * r) →
      ∀ j ≤ N, ∀ x ∈ K N, ∀ r ∈ R,
        Real.sqrt (normSq0S h x (j + 2) (defectJet_S57 S h j r x)) ≤ η * r) :=
  landau_small_all_S67 (fun j r x => Real.sqrt (normSq0S h x (j + 2) (defectJet_S57 S h j r x)))
    R hR K hKm N hC hB hstep hcrude η hη

end Concrete

end GC.LongTime.Ch12
