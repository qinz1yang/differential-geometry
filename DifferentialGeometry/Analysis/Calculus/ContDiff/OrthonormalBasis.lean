import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Sqrt

noncomputable section

open scoped ContDiff

namespace ContDiffOn

@[instance_reducible]
private def bilinearInnerProductCore
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hsym : ∀ v w, B v w = B w v)
    (hpos : ∀ v, v ≠ 0 → 0 < B v v) : InnerProductSpace.Core ℝ E where
  inner := fun v w => B v w
  conj_inner_symm v w := by simpa only [conj_trivial] using hsym w v
  re_inner_nonneg v := by
    change 0 ≤ B v v
    by_cases hv : v = 0
    · simp only [hv, map_zero, le_refl]
    · exact (hpos v hv).le
  add_left v w z := by simp only [map_add, add_apply]
  smul_left v w r := by simp only [map_smul, smul_apply, smul_eq_mul, conj_trivial]
  definite v hv := by
    by_contra hn
    exact (hpos v hn).ne' hv

private theorem exists_gramSchmidt_basis
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {d : ℕ}
    (e : Module.Basis (Fin d) ℝ E) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hsym : ∀ v w, B v w = B w v) (hpos : ∀ v, v ≠ 0 → 0 < B v v) :
    ∃ (v : Fin d → E) (b : Module.Basis (Fin d) ℝ E),
      (∀ i, v i ≠ 0) ∧
      (∀ i, v i = e i - ∑ j ∈ Finset.Iio i, (B (v j) (e i) / B (v j) (v j)) • v j) ∧
      (∀ i, b i = (Real.sqrt (B (v i) (v i)))⁻¹ • v i) ∧
      ∀ i j, B (b i) (b j) = if i = j then 1 else 0 := by
  let : Module ℝ E := inferInstance
  let core := bilinearInnerProductCore B hsym hpos
  let := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ) (F := E)
  let : InnerProductSpace ℝ E := InnerProductSpace.ofCore inferInstance
  let v : Fin d → E := InnerProductSpace.gramSchmidt ℝ e
  let w : Fin d → E := InnerProductSpace.gramSchmidtNormed ℝ e
  have hspan : Submodule.span ℝ (Set.range w) = ⊤ :=
    (InnerProductSpace.span_gramSchmidtNormed_range (𝕜 := ℝ) e).trans
      ((InnerProductSpace.span_gramSchmidt ℝ e).trans e.span_eq)
  let b : Module.Basis (Fin d) ℝ E := Module.Basis.mk
    (InnerProductSpace.gramSchmidtNormed_linearIndependent e.linearIndependent) hspan.ge
  have hb : (b : Fin d → E) = w := Module.Basis.coe_mk _ _
  refine ⟨v, b, fun i => InnerProductSpace.gramSchmidt_ne_zero i e.linearIndependent, ?_, ?_, ?_⟩
  · intro i
    have he := InnerProductSpace.gramSchmidt_def'' ℝ e i
    have hnorm (j : Fin d) : ‖v j‖ ^ 2 = B (v j) (v j) := (real_inner_self_eq_norm_sq _).symm
    simp only [← hnorm] at ⊢
    exact eq_sub_of_add_eq he.symm
  · intro i
    change b i = _
    rw [show b i = w i from congrFun hb i]
    change ‖v i‖⁻¹ • v i = _
    rw [norm_eq_sqrt_real_inner]
    rfl
  · intro i j
    change inner ℝ (b i) (b j) = _
    rw [congrFun hb i, congrFun hb j]
    exact orthonormal_iff_ite.mp (InnerProductSpace.gramSchmidtNormed_orthonormal e.linearIndependent) i j

private theorem exists_orthonormal_basis_fin
    {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {d : ℕ} {n : ℕ∞ω}
    {s : Set P} {B : P → E →L[ℝ] E →L[ℝ] ℝ}
    (hB : ContDiffOn ℝ n B s) (e : Module.Basis (Fin d) ℝ E)
    (hsym : ∀ x ∈ s, ∀ v w, B x v w = B x w v)
    (hpos : ∀ x ∈ s, ∀ v, v ≠ 0 → 0 < B x v v) :
    ∃ b : P → Module.Basis (Fin d) ℝ E,
      (∀ i, ContDiffOn ℝ n (fun x => b x i) s) ∧
      ∀ x ∈ s, ∀ i j, B x (b x i) (b x j) = if i = j then 1 else 0 := by
  classical
  have hex (x : P) : ∃ (v : Fin d → E) (b : Module.Basis (Fin d) ℝ E),
      x ∈ s → (∀ i, v i ≠ 0) ∧
        (∀ i, v i = e i - ∑ j ∈ Finset.Iio i, (B x (v j) (e i) / B x (v j) (v j)) • v j) ∧
        (∀ i, b i = (Real.sqrt (B x (v i) (v i)))⁻¹ • v i) ∧
        ∀ i j, B x (b i) (b j) = if i = j then 1 else 0 := by
    by_cases hx : x ∈ s
    · obtain ⟨v, b, hv⟩ := exists_gramSchmidt_basis e (B x) (hsym x hx) (hpos x hx)
      exact ⟨v, b, fun _ => hv⟩
    · exact ⟨fun _ => 0, e, fun h => False.elim (hx h)⟩
  choose v b h using hex
  have hCv (i : Fin d) : ContDiffOn ℝ n (fun x => v x i) s := by
    induction i using WellFoundedLT.induction with
    | ind i ih =>
      have hsum : ContDiffOn ℝ n
          (fun x => ∑ j ∈ Finset.Iio i, (B x (v x j) (e i) / B x (v x j) (v x j)) • v x j) s := by
        apply ContDiffOn.sum
        intro j hj
        have hjv := ih j (Finset.mem_Iio.mp hj)
        exact (((hB.clm_apply hjv).clm_apply contDiffOn_const).div
          ((hB.clm_apply hjv).clm_apply hjv)
          (fun x hx => (hpos x hx (v x j) ((h x hx).1 j)).ne')).smul hjv
      exact (contDiffOn_const.sub hsum).congr (fun x hx => (h x hx).2.1 i)
  refine ⟨b, ?_, fun x hx => (h x hx).2.2.2⟩
  intro i
  have hq := (hB.clm_apply (hCv i)).clm_apply (hCv i)
  have hp (x : P) (hx : x ∈ s) : 0 < B x (v x i) (v x i) :=
    hpos x hx (v x i) ((h x hx).1 i)
  have hn := (hq.sqrt (fun x hx => (hp x hx).ne')).inv
    (fun x hx => (Real.sqrt_pos.mpr (hp x hx)).ne')
  exact (hn.smul (hCv i)).congr (fun x hx => (h x hx).2.2.1 i)

theorem exists_orthonormal_basis
    {P E ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [Finite ι] {n : ℕ∞ω}
    {s : Set P} {B : P → E →L[ℝ] E →L[ℝ] ℝ}
    (hB : ContDiffOn ℝ n B s) (e : Module.Basis ι ℝ E)
    (hsym : ∀ x ∈ s, ∀ v w, B x v w = B x w v)
    (hpos : ∀ x ∈ s, ∀ v, v ≠ 0 → 0 < B x v v) :
    ∃ b : P → Module.Basis ι ℝ E,
      (∀ i, ContDiffOn ℝ n (fun x => b x i) s) ∧
      ∀ x ∈ s, (∀ i, B x (b x i) (b x i) = 1) ∧
        ∀ i j, i ≠ j → B x (b x i) (b x j) = 0 := by
  classical
  let := Fintype.ofFinite ι
  let a := Fintype.equivFin ι
  obtain ⟨b, hb, horth⟩ := exists_orthonormal_basis_fin hB (e.reindex a) hsym hpos
  refine ⟨fun x => (b x).reindex a.symm, ?_, ?_⟩
  · intro i
    simpa only [Module.Basis.reindex_apply, Equiv.symm_symm] using hb (a i)
  · intro x hx
    constructor
    · intro i
      simpa only [Module.Basis.reindex_apply, Equiv.symm_symm, ite_true] using horth x hx (a i) (a i)
    · intro i j hij
      simpa only [Module.Basis.reindex_apply, Equiv.symm_symm, a.injective.eq_iff, ite_eq_right hij]
        using horth x hx (a i) (a j)

end ContDiffOn
