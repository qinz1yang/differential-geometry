import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.InverseJets_S126

/-!
# CH12-S126 G3: the `Function.invFunOn` forms of `inverse_jets_S126`

For `Ψ̃ = id + u` with `ApproximatesLinearOn Ψ̃ id V (1/2)` on an open `V`:

* `isOpen_image_id_add_S126`: `Ψ̃ '' V` is open;
* `invFunOn_smooth_S126`: `Function.invFunOn Ψ̃ V` is `C^∞` on `Ψ̃ '' V`;
* `invFunOn_ckClose_S126`: `C^k`-closeness of `invFunOn Ψ̃ V` to `id` on `Ψ̃ '' V`, with the
  threshold `η` depending only on `(k, ε, E)`.

These are the `W := Ψ̃ '' V`, `Φ := invFunOn Ψ̃ V` instances of the frozen R-E statement.
-/

set_option autoImplicit false

open Set Filter Topology
open scoped ContDiff NNReal

namespace GC.LongTime.Ch12

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The image of an open set under `id + u` (with `‖Du‖ ≤ 1/2`) is open. -/
theorem isOpen_image_id_add_S126 {u : E → E} {V : Set E} (hV : IsOpen V)
    (hu : ContDiffOn ℝ ∞ u V)
    (hA : ApproximatesLinearOn (fun y => y + u y)
      ((ContinuousLinearEquiv.refl ℝ E : E ≃L[ℝ] E) : E →L[ℝ] E) V (1 / 2 : ℝ≥0)) :
    IsOpen ((fun y => y + u y) '' V) := by
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨e, he⟩ := exists_equiv_one_add_S126 (fderiv ℝ u y)
    (norm_fderiv_le_half_S126 hV hA y hy)
  have hua : ContDiffAt ℝ ∞ u y := hu.contDiffAt (hV.mem_nhds hy)
  have hΨ : ContDiffAt ℝ ∞ (fun y => y + u y) y := contDiffAt_id.add hua
  have hf' : HasFDerivAt (fun y => y + u y) (e : E →L[ℝ] E) y := by
    rw [he, ContinuousLinearMap.one_def]
    exact (hasFDerivAt_id y).add (hua.differentiableAt (by simp)).hasFDerivAt
  have hs := hΨ.hasStrictFDerivAt' hf' (by simp)
  rw [← hs.map_nhds_eq_of_equiv]
  exact Filter.image_mem_map (hV.mem_nhds hy)

/-- `Function.invFunOn (id + u) V` is `C^∞` on the (open) image `(id + u) '' V`. -/
theorem invFunOn_smooth_S126 {u : E → E} {V : Set E} (hV : IsOpen V)
    (hu : ContDiffOn ℝ ∞ u V)
    (hA : ApproximatesLinearOn (fun y => y + u y)
      ((ContinuousLinearEquiv.refl ℝ E : E ≃L[ℝ] E) : E →L[ℝ] E) V (1 / 2 : ℝ≥0)) :
    IsOpen ((fun y => y + u y) '' V) ∧
      ContDiffOn ℝ ∞ (Function.invFunOn (fun y => y + u y) V) ((fun y => y + u y) '' V) := by
  have hW := isOpen_image_id_add_S126 hV hu hA
  refine ⟨hW, contDiffOn_inverse_S126 hV hW hu hA fun x hx => ?_⟩
  have hx' : ∃ a ∈ V, (fun y => y + u y) a = x := by
    obtain ⟨a, ha, rfl⟩ := hx
    exact ⟨a, ha, rfl⟩
  exact ⟨Function.invFunOn_mem hx', Function.invFunOn_eq hx'⟩

/-- `C^k`-closeness of `Function.invFunOn (id + u) V` to `id`, uniformly in `(u, V)`. -/
theorem invFunOn_ckClose_S126 (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ (u : E → E) (V : Set E), IsOpen V → ContDiffOn ℝ ∞ u V →
      ApproximatesLinearOn (fun y => y + u y) ((ContinuousLinearEquiv.refl ℝ E : E ≃L[ℝ] E) :
        E →L[ℝ] E) V (1 / 2 : ℝ≥0) →
      (∀ j : ℕ, j ≤ k → ∀ y ∈ V, ‖iteratedFDeriv ℝ j u y‖ ≤ η) →
      ∀ j : ℕ, j ≤ k → ∀ x ∈ (fun y => y + u y) '' V,
        ‖iteratedFDeriv ℝ j (fun z => Function.invFunOn (fun y => y + u y) V z - z) x‖ < ε := by
  obtain ⟨η, hη, h⟩ := inverse_jets_S126 (E := E) k ε hε
  refine ⟨η, hη, fun u V hV hu hA hj => ?_⟩
  have hW := isOpen_image_id_add_S126 hV hu hA
  exact (h u (Function.invFunOn (fun y => y + u y) V) V _ hV hW hu hA hj fun x hx => by
    have hx' : ∃ a ∈ V, (fun y => y + u y) a = x := by
      obtain ⟨a, ha, rfl⟩ := hx
      exact ⟨a, ha, rfl⟩
    exact ⟨Function.invFunOn_mem hx', Function.invFunOn_eq hx'⟩).2

end GC.LongTime.Ch12
