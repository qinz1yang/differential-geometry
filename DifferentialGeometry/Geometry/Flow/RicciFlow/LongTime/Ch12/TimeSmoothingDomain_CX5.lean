import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TimeSmoothingGlue_CX5

set_option autoImplicit false

/-! # H2 source space-time domains

The ambient domain is the union of late open cylinders, as in HPS04. Its
slices have a genuine space-time neighbourhood at every point; they are not
defined using the stepwise accuracy or its advertised balls.
-/

noncomputable section
open Set Filter Topology
open scoped Manifold ContDiff

namespace GC.LongTime.Ch12

variable {M N : Type*}

theorem dyadicSmoothing_tail_CX5 {T : ℝ} (hT : 0 < T) (θ : ℝ → ℝ)
    (f : ℕ → M → N) (E : ℕ → ℝ × M → M) (N₀ : ℕ) {q : ℝ × M}
    (hq : dyadicTime_CX5 T N₀ ≤ q.1) :
    dyadicSmoothing_CX5 T θ f E q =
      dyadicSmoothing_CX5 (dyadicTime_CX5 T N₀) θ
        (fun j => f (N₀ + j)) (fun j => E (N₀ + j)) q := by
  let j := dyadicIndex_CX5 (dyadicTime_CX5 T N₀) q.1
  have hj := dyadicIndex_mem_CX5 (dyadicTime_pos_CX5 hT N₀) hq
  change q.1 ∈ Ico (dyadicTime_CX5 (dyadicTime_CX5 T N₀) j)
    (dyadicTime_CX5 (dyadicTime_CX5 T N₀) (j + 1)) at hj
  have hj' : q.1 ∈ Ico (dyadicTime_CX5 T (N₀ + j)) (dyadicTime_CX5 T (N₀ + j + 1)) := by
    simpa only [dyadicTime_add_CX5, Nat.add_assoc] using hj
  rw [dyadicSmoothing_eq_CX5 hT θ f E hj',
    dyadicSmoothing_eq_CX5 (dyadicTime_pos_CX5 hT N₀) θ _ _ hj, dyadicTime_add_CX5]

section Domain
variable [TopologicalSpace M]

def exhaustionSpaceTime_CX5 (U : ℕ → TopologicalSpace.Opens M) (τ : ℕ → ℝ) :
    TopologicalSpace.Opens (ℝ × M) :=
  ⟨⋃ n, Ioi (τ n) ×ˢ (U n : Set M), isOpen_iUnion fun n => isOpen_Ioi.prod (U n).isOpen⟩

def sourceSlice_CX5 (Ω : TopologicalSpace.Opens (ℝ × M)) (t : ℝ) :
    TopologicalSpace.Opens M :=
  ⟨{p | (t, p) ∈ Ω}, Ω.isOpen.preimage (continuous_const.prodMk continuous_id)⟩

theorem exhaustionSpaceTime_contains_CX5 (U : ℕ → TopologicalSpace.Opens M)
    (τ : ℕ → ℝ) (n : ℕ) {t : ℝ} {p : M} (ht : τ n < t) (hp : p ∈ U n) :
    p ∈ sourceSlice_CX5 (exhaustionSpaceTime_CX5 U τ) t :=
  mem_iUnion.mpr ⟨n, ht, hp⟩

/-- Every source point has a common space-time box, with positive lower endpoint
and upper endpoint inside a prescribed history horizon. -/
theorem exists_sourceBox_CX5 (Ω : TopologicalSpace.Opens (ℝ × M))
    {t₀ τ : ℝ} {p₀ : M} (ht₀ : 0 < t₀) (hτ : t₀ < τ) (hq : (t₀, p₀) ∈ Ω) :
    ∃ (a b : ℝ) (U : TopologicalSpace.Opens M),
      0 ≤ a ∧ a < t₀ ∧ t₀ < b ∧ b ≤ τ ∧ p₀ ∈ U ∧
      ∀ t ∈ Ioo a b, (U : Set M) ⊆ sourceSlice_CX5 Ω t := by
  obtain ⟨S, V, hS, htS, hV, hpV, hsub⟩ := mem_nhds_prod_iff'.mp (Ω.isOpen.mem_nhds hq)
  obtain ⟨a, b, ht, hab⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hS.mem_nhds htS)
  refine ⟨max a 0, min b τ, ⟨V, hV⟩, le_max_right _ _,
    max_lt ht.1 ht₀, lt_min ht.2 hτ, min_le_right _ _, hpV, ?_⟩
  intro t ht' p hp
  exact hsub ⟨hab ⟨(le_max_left _ _).trans_lt ht'.1,
    ht'.2.trans_le (min_le_left _ _)⟩, hp⟩

end Domain

section Smooth
variable {V W HM HN : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [TopologicalSpace HM] [TopologicalSpace HN]
  {I : ModelWithCorners ℝ V HM} {J : ModelWithCorners ℝ W HN}
  [TopologicalSpace M] [ChartedSpace HM M] [TopologicalSpace N] [ChartedSpace HN N]

/-- Different compact source regions may start at different dyadic indices.
Their late cylinders still carry the same formula, hence one joint smooth map. -/
theorem contMDiffOn_exhaustionSmoothing_CX5 {T : ℝ} (hT : 0 < T)
    {θ : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ) (hθrange : ∀ s, θ s ∈ Icc (0 : ℝ) 1)
    (hθ0 : ∀ s, s ≤ 7 / 4 → θ s = 0) (hθ1 : ∀ s, 15 / 8 ≤ s → θ s = 1)
    (f : ℕ → M → N) (E : ℕ → ℝ × M → M)
    (U : ℕ → TopologicalSpace.Opens M) (N₀ : ℕ → ℕ) (A : ℕ → ℕ → Set M)
    (hf : ∀ n j, ContMDiffOn I J ∞ (f (N₀ n + j)) (A n j))
    (hE : ∀ n j, ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (E (N₀ n + j)))
    (himage : ∀ n j μ, μ ∈ Icc (0 : ℝ) 1 → ∀ p ∈ U n, E (N₀ n + j) (μ, p) ∈ A n j)
    (hE0 : ∀ n j p, p ∈ U n → E (N₀ n + j) (0, p) = p)
    (hjoin : ∀ n j p, p ∈ U n →
      f (N₀ n + j) (E (N₀ n + j) (1, p)) = f (N₀ n + (j + 1)) p) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) J ∞ (dyadicSmoothing_CX5 T θ f E)
      (exhaustionSpaceTime_CX5 U (fun n => dyadicTime_CX5 T (N₀ n))) := by
  apply ContMDiffOn.iUnion_of_isOpen
  · intro n
    have hs := contMDiffOn_dyadicSmoothing_CX5 (dyadicTime_pos_CX5 hT (N₀ n))
      hθ hθrange hθ0 hθ1 (fun j => f (N₀ n + j)) (fun j => E (N₀ n + j))
      (U n).isOpen (A n) (hf n) (hE n) (himage n) (hE0 n) (hjoin n)
    exact hs.congr (fun q hq => dyadicSmoothing_tail_CX5 hT θ f E (N₀ n) hq.1.le)
  · intro n
    exact isOpen_Ioi.prod (U n).isOpen

end Smooth
end GC.LongTime.Ch12
