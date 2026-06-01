import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.Bijective.ChartCoverBijective

namespace DifferentialGeometry.PDE.RicciFlow.ODE

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

omit [T2Space M] [SigmaCompactSpace M] in
/--
**Uniform horizon extraction from open-cover-local properties on a compact
space.** Given a property `P : ℝ → M → Prop` that is witnessed on an open
cover of a compact `M` by per-element positive time horizons, compactness
extracts a single positive `T` that works for all `x : M` simultaneously.

Concretely, for each `α : M` there is an open neighborhood `U α ∋ α` and
a positive horizon `S α` such that `P s x` holds for all `x ∈ U α` and
`s ∈ [0, S α)`. Compactness of `M` yields a finite subcover; `T` is the
minimum of the finitely many `S α` values.
-/
theorem compact_uniform_horizon_extraction
    (U : M → Set M) (S : M → ℝ) (P : ℝ → M → Prop)
    (hU_open : ∀ α : M, IsOpen (U α))
    (hU_mem : ∀ α : M, α ∈ U α)
    (hS_pos : ∀ α : M, 0 < S α)
    (hP : ∀ α : M, ∀ x ∈ U α, ∀ s ∈ Set.Ico (0 : ℝ) (S α), P s x) :
    ∃ T : ℝ, 0 < T ∧ ∀ s ∈ Set.Ico (0 : ℝ) T, ∀ x : M, P s x := by
  have hCover : (Set.univ : Set M) ⊆ ⋃ α : M, U α := by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x, hU_mem x⟩
  obtain ⟨Sfin, hSfin⟩ :=
    isCompact_univ.elim_finite_subcover U hU_open hCover
  rcases Sfin.eq_empty_or_nonempty with hSempty | hSnonempty
  · refine ⟨1, one_pos, ?_⟩
    intro s _ x
    have : x ∈ ⋃ α ∈ Sfin, U α := hSfin (Set.mem_univ x)
    rw [hSempty] at this
    simp at this
  · let Tmin : ℝ := Sfin.image S |>.min' (by
      rw [Finset.image_nonempty]; exact hSnonempty)
    have hTmin_pos : 0 < Tmin := by
      have hmem : Tmin ∈ Sfin.image S := Finset.min'_mem _ _
      rcases Finset.mem_image.mp hmem with ⟨α₀, _, hα₀_eq⟩
      rw [← hα₀_eq]; exact hS_pos α₀
    have hTmin_le : ∀ α ∈ Sfin, Tmin ≤ S α := by
      intro α hα
      apply Finset.min'_le
      exact Finset.mem_image.mpr ⟨α, hα, rfl⟩
    refine ⟨Tmin, hTmin_pos, ?_⟩
    intro s hs x
    have hx_cover : x ∈ ⋃ α ∈ Sfin, U α := hSfin (Set.mem_univ x)
    rcases Set.mem_iUnion₂.mp hx_cover with ⟨α, hαS, hxU⟩
    have hs_α : s ∈ Set.Ico (0 : ℝ) (S α) :=
      ⟨hs.1, lt_of_lt_of_le hs.2 (hTmin_le α hαS)⟩
    exact hP α x hxU s hs_α

/--
**Uniform two-sided bijectivity of the chart-cover flow on a compact manifold.**

Given chart-local Picard data for `X` and for `-X` at every base point,
together with global flows `Φ` (for `X`) and `Ψ` (for `-X`) satisfying
chart-α-coord representation identities, and per-chart manifold-level
two-sided composition identities on positive time horizons, compactness
of `M` extracts a single uniform positive `T` on which the two-sided
invertibility `Ψ s ∘ Φ s = id` and `Φ s ∘ Ψ s = id` holds simultaneously
for all `x : M` and all `s ∈ [0, T)`.

The per-chart bijectivity hypothesis `hBijPerChart` is the genuine
mathematical content: for each chart base point `α`, there exists a positive
horizon `S_α` such that the composition identities `Ψ s (Φ s x) = x` and
`Φ s (Ψ s x) = x` hold for all `x` in the chart neighborhood
`(hper α).U ∩ (hperNeg α).U` and all `s ∈ [0, S_α)`. This is supplied by
a downstream Grönwall uniqueness argument combining
`chart_cover_flow_bijective_two_sided_on_short_time` with chart-overlap
uniqueness for the global flows. The present theorem performs the purely
topological compactness extraction step: finite subcover of M by the chart
neighborhoods, minimum of the finitely many horizons S_α.
-/
theorem chart_cover_flow_bijective_two_sided_uniform_horizon
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (hper : ∀ α : M, ChartLocalPicardData X α)
    (hperNeg : ∀ α : M, ChartLocalPicardData (fun t x => -(X t x)) α)
    (Φ Ψ : ℝ → M → M)
    (_hΦ_init : ∀ x, Φ 0 x = x)
    (_hΨ_init : ∀ x, Ψ 0 x = x)
    (_hΦ_repr : ∀ x : M, ∃ α : M, ∀ s : ℝ,
      Φ s x = (chartAt H α).symm (I.symm ((hper α).flow (I ((chartAt H α) x)) s)))
    (_hΨ_repr : ∀ x : M, ∃ α : M, ∀ s : ℝ,
      Ψ s x = (chartAt H α).symm (I.symm ((hperNeg α).flow (I ((chartAt H α) x)) s)))
    (hBijPerChart : ∀ α : M,
      ∃ S_α : ℝ, 0 < S_α ∧
        ∀ x ∈ (hper α).U ∩ (hperNeg α).U,
          ∀ s ∈ Set.Ico (0 : ℝ) S_α,
            Ψ s (Φ s x) = x ∧ Φ s (Ψ s x) = x) :
    ∃ T : ℝ, 0 < T ∧
      (∀ s ∈ Set.Ico (0 : ℝ) T, ∀ x : M, Ψ s (Φ s x) = x) ∧
      (∀ s ∈ Set.Ico (0 : ℝ) T, ∀ x : M, Φ s (Ψ s x) = x) := by
  classical
  have hExtracted := compact_uniform_horizon_extraction
    (fun α => (hper α).U ∩ (hperNeg α).U)
    (fun α => (hBijPerChart α).choose)
    (fun s x => Ψ s (Φ s x) = x ∧ Φ s (Ψ s x) = x)
    (fun α => (hper α).isOpen_U.inter (hperNeg α).isOpen_U)
    (fun α => ⟨(hper α).mem_U_self, (hperNeg α).mem_U_self⟩)
    (fun α => (hBijPerChart α).choose_spec.1)
    (fun α x hx s hs => (hBijPerChart α).choose_spec.2 x hx s hs)
  obtain ⟨T, hT_pos, hT_bij⟩ := hExtracted
  exact ⟨T, hT_pos, fun s hs x => (hT_bij s hs x).1, fun s hs x => (hT_bij s hs x).2⟩

end DifferentialGeometry.PDE.RicciFlow.ODE
