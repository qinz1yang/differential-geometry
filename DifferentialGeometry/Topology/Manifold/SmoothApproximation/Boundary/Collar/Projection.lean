import DifferentialGeometry.Topology.Manifold.Boundary.DefiningCollar

/-!
# Collar coordinates as smooth functions on the manifold

From the smooth collar of `exists_definingFunction_sublevel_collar` (a closed embedding
`c : ∂M × [0, a] → M` with `r ∘ c = t`, and a diffeomorphism `d : {t < a} ≅ {r < a}` agreeing with
`c`), `exists_collar_projection` extracts the collar projection `π : M → ∂M`, smooth on `{r < a}`,
with `π (c q) = q.1` for `q.2 < a` and `c (π x, r x) = x` for `r x < a`.
-/

set_option autoImplicit false

noncomputable section

open Set Function TopologicalSpace
open scoped Manifold Topology ContDiff
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

namespace DifferentialGeometry.Topology.Manifold.SmoothApproximation

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [IsManifold (𝓡∂ (n + 1)) ∞ M]

/-- The collar projection of a smooth collar given by a diffeomorphism `d` of open sets. -/
theorem exists_collar_projection [Nonempty (BoundaryManifold (𝓡∂ (n + 1)) M)] {r : M → ℝ}
    (hr0 : ∀ x, 0 ≤ r x) {a : ℝ} [Fact ((0 : ℝ) < a)]
    {c : BoundaryManifold (𝓡∂ (n + 1)) M × Icc (0 : ℝ) a → M} (hrc : ∀ q, r (c q) = q.2.val)
    (U : Opens (BoundaryManifold (𝓡∂ (n + 1)) M × Icc (0 : ℝ) a))
    (hU : (U : Set (BoundaryManifold (𝓡∂ (n + 1)) M × Icc (0 : ℝ) a)) = {q | q.2.val < a})
    (Y : Opens M) (hY : (Y : Set M) = {x | r x < a})
    (d : Diffeomorph ((HasSmoothBoundary.boundaryModel (𝓡∂ (n + 1))).prod (𝓡∂ 1))
      (𝓡∂ (n + 1)) U Y ∞) (hd : ∀ q : U, (d q).val = c q.val) :
    ∃ π : M → BoundaryManifold (𝓡∂ (n + 1)) M,
      ContMDiffOn (𝓡∂ (n + 1)) (HasSmoothBoundary.boundaryModel (𝓡∂ (n + 1))) ∞ π
        {x | r x < a} ∧
      (∀ q : BoundaryManifold (𝓡∂ (n + 1)) M × Icc (0 : ℝ) a, q.2.val < a → π (c q) = q.1) ∧
      ∀ x (hx : r x < a), c (π x, ⟨r x, hr0 x, hx.le⟩) = x := by
  classical
  let π : M → BoundaryManifold (𝓡∂ (n + 1)) M := fun x =>
    if hx : x ∈ Y then (d.symm ⟨x, hx⟩).val.1 else Classical.arbitrary _
  have hπY : ∀ (x : M) (hx : x ∈ Y), π x = (d.symm ⟨x, hx⟩).val.1 := fun x hx => dite_eq_left hx
  have hdsymm : ∀ (x : M) (hx : x ∈ Y), c (d.symm ⟨x, hx⟩).val = x := by
    intro x hx
    have h := hd (d.symm ⟨x, hx⟩)
    rw [d.apply_symm_apply] at h
    exact h.symm
  refine ⟨π, ?_, ?_, ?_⟩
  · intro x hx
    have hxY : x ∈ Y := by rw [← SetLike.mem_coe, hY]; exact hx
    have hloc : ContMDiffAt (𝓡∂ (n + 1)) (HasSmoothBoundary.boundaryModel (𝓡∂ (n + 1))) ∞
        (fun y : Y => π y) ⟨x, hxY⟩ := by
      have hfun : (fun y : Y => π y) = fun y : Y => (d.symm y).val.1 := by
        funext y
        exact hπY y.1 y.2
      rw [hfun]
      exact (contMDiff_fst.comp (contMDiff_subtype_val.comp d.symm.contMDiff)) ⟨x, hxY⟩
    exact (contMDiffAt_subtype_iff.mp hloc).contMDiffWithinAt
  · intro q hq
    have hqU : q ∈ U := by rw [← SetLike.mem_coe, hU]; exact hq
    have hcY : c q ∈ Y := by
      rw [← hd ⟨q, hqU⟩]
      exact (d ⟨q, hqU⟩).2
    rw [hπY _ hcY]
    have h : (⟨c q, hcY⟩ : Y) = d ⟨q, hqU⟩ := Subtype.ext (hd ⟨q, hqU⟩).symm
    rw [h, d.symm_apply_apply]
  · intro x hx
    have hxY : x ∈ Y := by rw [← SetLike.mem_coe, hY]; exact hx
    set q := (d.symm ⟨x, hxY⟩).val with hq
    have hqr : q.2.val = r x := by
      have h := hrc q
      rw [hq, hdsymm x hxY] at h
      exact h.symm
    have hqe : q = (π x, ⟨r x, hr0 x, hx.le⟩) := by
      refine Prod.ext ?_ (Subtype.ext hqr)
      rw [hπY x hxY]
    rw [← hqe, hq, hdsymm x hxY]

end DifferentialGeometry.Topology.Manifold.SmoothApproximation
