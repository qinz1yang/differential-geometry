import Mathlib.Geometry.Manifold.Diffeomorph

open scoped Manifold

namespace ChartedSpace

variable {H H' M : Type*} [TopologicalSpace H] [TopologicalSpace H']
  [TopologicalSpace M] [ChartedSpace H M]

@[instance_reducible]
def transHomeomorph (e : H ≃ₜ H') : ChartedSpace H' M where
  atlas := (fun c : OpenPartialHomeomorph M H => c.transHomeomorph e) '' atlas H M
  chartAt x := (chartAt H x).transHomeomorph e
  mem_chart_source x := mem_chart_source H x
  chart_mem_atlas x := ⟨chartAt H x, chart_mem_atlas H x, rfl⟩

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E H'}
  {n : WithTop ℕ∞}

theorem isManifold_transHomeomorph [IsManifold I n M] (e : H ≃ₜ H')
    (h : ∀ x : H, J (e x) = I x) :
    letI := transHomeomorph (M := M) e
    IsManifold J n M := by
  have hrange : Set.range J = Set.range I := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨e.symm x, by simpa only [e.apply_symm_apply] using (h (e.symm x)).symm⟩
    · rintro ⟨x, rfl⟩
      exact ⟨e x, h x⟩
  have hsymm (y : E) (hy : y ∈ Set.range J) : e.symm (J.symm y) = I.symm y := by
    apply I.injective
    rw [← h, e.apply_symm_apply, J.right_inv hy, I.right_inv (hrange ▸ hy)]
  let := transHomeomorph (M := M) e
  apply isManifold_of_contDiffOn J n M
  rintro _ _ ⟨c, hc, rfl⟩ ⟨c', hc', rfl⟩
  have hd := ((contDiffGroupoid n I).compatible hc hc').1
  apply hd.congr_mono
  · intro y hy
    change J (e (c' (c.symm (e.symm (J.symm y))))) = I (c' (c.symm (I.symm y)))
    rw [h, hsymm y hy.2]
  · intro y hy
    change I.symm y ∈ (c.symm ≫ₕ c').source ∧ y ∈ Set.range I
    refine ⟨?_, hrange ▸ hy.2⟩
    have hyr := hy.2
    have hys := hy.1
    change e.symm (J.symm y) ∈ c.target ∧
      c.symm (e.symm (J.symm y)) ∈ c'.source at hys
    rw [hsymm y hyr] at hys
    exact hys

end ChartedSpace

namespace ChartedSpace

variable {𝕜 E E' H H' G M N : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace G]
  [TopologicalSpace M] [TopologicalSpace N] [ChartedSpace H M] [ChartedSpace G N]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E H'}
  {K : ModelWithCorners 𝕜 E' G} {n : WithTop ℕ∞}

theorem contMDiffAt_transHomeomorph_left (e : H ≃ₜ H')
    (h : ∀ x : H, J (e x) = I x) {f : M → N} {x : M} :
    letI := transHomeomorph (M := M) e
    ContMDiffAt J K n f x ↔ ContMDiffAt I K n f x := by
  have hrange : Set.range J = Set.range I := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨e.symm x, by simpa only [e.apply_symm_apply] using (h (e.symm x)).symm⟩
    · rintro ⟨x, rfl⟩
      exact ⟨e x, h x⟩
  have hsymm (y : E) (hy : y ∈ Set.range J) : e.symm (J.symm y) = I.symm y := by
    apply I.injective
    rw [← h, e.apply_symm_apply, J.right_inv hy, I.right_inv (hrange ▸ hy)]
  let := transHomeomorph (M := M) e
  have hext : extChartAt J x x = extChartAt I x x := h _
  have hchart (y : E) (hy : y ∈ Set.range I) :
      (extChartAt J x).symm y = (extChartAt I x).symm y := by
    change (chartAt H x).symm (e.symm (J.symm y)) = (chartAt H x).symm (I.symm y)
    rw [hsymm y (hrange.symm ▸ hy)]
  simp only [contMDiffAt_iff, hrange, hext]
  apply and_congr_right
  intro _
  have heq : Set.EqOn
      (extChartAt K (f x) ∘ f ∘ (extChartAt J x).symm)
      (extChartAt K (f x) ∘ f ∘ (extChartAt I x).symm) (Set.range I) := by
    intro y hy
    simp only [Function.comp_apply, hchart y hy]
  have hx : extChartAt I x x ∈ Set.range I := ⟨chartAt H x x, rfl⟩
  exact ⟨fun hf => hf.congr_of_mem heq.symm hx, fun hf => hf.congr_of_mem heq hx⟩

theorem contMDiff_transHomeomorph_left (e : H ≃ₜ H')
    (h : ∀ x : H, J (e x) = I x) {f : M → N} :
    letI := transHomeomorph (M := M) e
    ContMDiff J K n f ↔ ContMDiff I K n f := by
  let := transHomeomorph (M := M) e
  exact forall_congr' fun _ => contMDiffAt_transHomeomorph_left e h

theorem contMDiffAt_transHomeomorph_right (e : H ≃ₜ H')
    (h : ∀ x : H, J (e x) = I x) {f : N → M} {x : N} :
    letI := transHomeomorph (M := M) e
    ContMDiffAt K J n f x ↔ ContMDiffAt K I n f x := by
  let := transHomeomorph (M := M) e
  have hext : (extChartAt J (f x) : M → E) = extChartAt I (f x) :=
    funext fun _ => h _
  simp only [contMDiffAt_iff, hext]

theorem contMDiff_transHomeomorph_right (e : H ≃ₜ H')
    (h : ∀ x : H, J (e x) = I x) {f : N → M} :
    letI := transHomeomorph (M := M) e
    ContMDiff K J n f ↔ ContMDiff K I n f := by
  let := transHomeomorph (M := M) e
  exact forall_congr' fun _ => contMDiffAt_transHomeomorph_right e h

end ChartedSpace

namespace ChartedSpace

variable {𝕜 E H H' M : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [TopologicalSpace H] [TopologicalSpace H']
  [TopologicalSpace M] [ChartedSpace H M]
  (I : ModelWithCorners 𝕜 E H) (J : ModelWithCorners 𝕜 E H')

def transHomeomorphDiffeomorph (e : H ≃ₜ H') (h : ∀ x : H, J (e x) = I x)
    (n : WithTop ℕ∞) :
    letI := transHomeomorph (M := M) e
    M ≃ₘ^n⟮I, J⟯ M := by
  letI := transHomeomorph (M := M) e
  exact
    { toEquiv := Equiv.refl M
      contMDiff_toFun := (contMDiff_transHomeomorph_right e h).mpr contMDiff_id
      contMDiff_invFun := (contMDiff_transHomeomorph_left e h).mpr contMDiff_id }

end ChartedSpace
