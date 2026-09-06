import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

noncomputable section

open Bundle Set
open scoped Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  {V₁ V₂ : M → Type*}
  [TopologicalSpace (TotalSpace F₁ V₁)] [TopologicalSpace (TotalSpace F₂ V₂)]
  [∀ x, NormedAddCommGroup (V₁ x)] [∀ x, NormedSpace 𝕜 (V₁ x)]
  [∀ x, NormedAddCommGroup (V₂ x)] [∀ x, NormedSpace 𝕜 (V₂ x)]
  [FiberBundle F₁ V₁] [VectorBundle 𝕜 F₁ V₁]
  [FiberBundle F₂ V₂] [VectorBundle 𝕜 F₂ V₂]
  {P : Type*} [NormedAddCommGroup P] [NormedSpace 𝕜 P] {n : ℕ∞ω}

theorem ContMDiffOn.contDiffOn_fiberwise
    {A : P → ∀ x : M, V₁ x → V₂ x} {S : Set P}
    (hA : ContMDiffOn (𝓘(𝕜, P).prod (I.prod 𝓘(𝕜, F₁))) (I.prod 𝓘(𝕜, F₂)) n
      (fun q : P × TotalSpace F₁ V₁ =>
        (⟨q.2.proj, A q.1 q.2.proj q.2.2⟩ : TotalSpace F₂ V₂)) (S ×ˢ univ))
    (x : M) : ContDiffOn 𝕜 n (fun q : P × V₁ x => A q.1 x q.2) (S ×ˢ univ) := by
  let e₁ := trivializationAt F₁ V₁ x
  let e₂ := trivializationAt F₂ V₂ x
  have he₁ : x ∈ e₁.baseSet := mem_baseSet_trivializationAt F₁ V₁ x
  have he₂ : x ∈ e₂.baseSet := mem_baseSet_trivializationAt F₂ V₂ x
  intro q hq
  have hin : ContMDiffWithinAt 𝓘(𝕜, P × V₁ x) (I.prod 𝓘(𝕜, F₁)) n
      (fun r : P × V₁ x => (⟨x, r.2⟩ : TotalSpace F₁ V₁)) (S ×ˢ univ) q := by
    rw [Bundle.contMDiffWithinAt_totalSpace]
    refine ⟨contMDiffWithinAt_const, ?_⟩
    have h : ContDiff 𝕜 n (fun r : P × V₁ x => e₁.continuousLinearMapAt 𝕜 x r.2) :=
      (e₁.continuousLinearMapAt 𝕜 x).contDiff.comp contDiff_snd
    apply h.contDiffWithinAt.contMDiffWithinAt.congr
    · intro r _
      exact (e₁.continuousLinearMapAt_apply_of_mem 𝕜 he₁ r.2).symm
    · exact (e₁.continuousLinearMapAt_apply_of_mem 𝕜 he₁ q.2).symm
  have hfst : ContMDiffWithinAt 𝓘(𝕜, P × V₁ x) 𝓘(𝕜, P) n
      (fun r : P × V₁ x => r.1) (S ×ˢ univ) q :=
    contDiff_fst.contDiffWithinAt.contMDiffWithinAt
  have ha := (hA (q.1, (⟨x, q.2⟩ : TotalSpace F₁ V₁)) ⟨hq.1, mem_univ _⟩).comp q
    (hfst.prodMk hin) (fun (r : P × V₁ x) (hr : r ∈ S ×ˢ univ) =>
      show (r.1, (⟨x, r.2⟩ : TotalSpace F₁ V₁)) ∈ S ×ˢ univ from ⟨hr.1, mem_univ _⟩)
  have hcoord := (Bundle.contMDiffWithinAt_totalSpace.mp ha).2
  have hcoord' : ContDiffWithinAt 𝕜 n
      (fun r : P × V₁ x => e₂.continuousLinearMapAt 𝕜 x (A r.1 x r.2)) (S ×ˢ univ) q := by
    apply ContMDiffWithinAt.contDiffWithinAt
    apply hcoord.congr
    · intro r _
      exact e₂.continuousLinearMapAt_apply_of_mem 𝕜 he₂ (A r.1 x r.2)
    · exact e₂.continuousLinearMapAt_apply_of_mem 𝕜 he₂ (A q.1 x q.2)
  have hresult := (e₂.symmL 𝕜 x).contDiff.contDiffAt.comp_contDiffWithinAt q hcoord'
  exact hresult.congr (fun r _ => (e₂.symmL_continuousLinearMapAt he₂ (A r.1 x r.2)).symm)
    (e₂.symmL_continuousLinearMapAt he₂ (A q.1 x q.2)).symm
