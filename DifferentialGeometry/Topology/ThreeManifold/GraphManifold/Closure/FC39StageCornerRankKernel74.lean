import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import DifferentialGeometry.Topology.Manifold.OpenSubtype

/-!
# Draft 74, D74-14 layer 2 (kernel): rank two of `(T, b ∘ q)` from rank two of `(q, T)`

Lane S-JUNCTIONS2 (suffix `_JN74`). D74-14: "rank (`h_F = b_e ∘ f₂`, `db_e ≠ 0`, EDP04's `d(f₂, T)`
rank two ⟹ descended differential invertible)". The abstract kernel: if `(q, T)` has a surjective
differential at `x`, `b` has a nonzero differential at `q x` and `r = b ∘ q` near `x`, then the
differential of the pair `(T, r)` into `ℝ × ℝ` is surjective at `x`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0

section Kernel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- The differential of `f - c` is the differential of `f`. -/
theorem mfderiv_sub_const_JN74 {f : M → ℝ} {x : M} (c : ℝ) :
    mfderiv I 𝓘(ℝ, ℝ) (fun z => f z - c) x = mfderiv I 𝓘(ℝ, ℝ) f x := by
  by_cases hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x
  · have h := (hf.hasMFDerivAt.sub (hasMFDerivAt_const (I := I) (I' := 𝓘(ℝ, ℝ)) c x)).mfderiv
    exact h.trans (sub_zero _)
  · have hg : ¬ MDifferentiableAt I 𝓘(ℝ, ℝ) (fun z => f z - c) x := by
      intro hg
      apply hf
      refine (hg.add (mdifferentiableAt_const (c := c))).congr_of_eventuallyEq ?_
      exact Filter.Eventually.of_forall fun z => by simp
    rw [mfderiv_zero_of_not_mdifferentiableAt hf, mfderiv_zero_of_not_mdifferentiableAt hg]
    rfl

/-- A nonzero continuous linear functional onto `ℝ` is surjective. -/
theorem surjective_of_ne_zero_JN74 {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
    {L : F →L[ℝ] ℝ} (hL : L ≠ 0) : Surjective L := by
  obtain ⟨w, hw⟩ : ∃ w, L w ≠ 0 := by
    by_contra h
    exact hL (ContinuousLinearMap.ext fun w => by_contra fun hw => h ⟨w, hw⟩)
  intro c
  refine ⟨(c / L w) • w, ?_⟩
  rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hw]

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] {HB : Type*}
  [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {B : Type*} [TopologicalSpace B]
  [ChartedSpace HB B]

/-- **The rank kernel (D74-14, layer 2).** If `v ↦ (dq v, dT v)` is onto at `x`, `db ≠ 0` at
`q x` and `r = b ∘ q` near `x`, then `v ↦ d(T, r) v` is onto `ℝ × ℝ`. -/
theorem surjective_mfderiv_pair_JN74 {q : M → B} {T r : M → ℝ} {b : B → ℝ} {x : M}
    (hq : MDifferentiableAt I IB q x) (hT : MDifferentiableAt I 𝓘(ℝ, ℝ) T x)
    (hb : MDifferentiableAt IB 𝓘(ℝ, ℝ) b (q x))
    (hbne : mfderiv IB 𝓘(ℝ, ℝ) b (q x) ≠ 0) (hr : r =ᶠ[𝓝 x] b ∘ q)
    (hrank : Surjective fun v : TangentSpace I x =>
      (mfderiv I IB q x v, mfderiv I 𝓘(ℝ, ℝ) T x v)) :
    Surjective (mfderiv I 𝓘(ℝ, ℝ × ℝ) (fun z => (T z, r z)) x) := by
  have hbq : MDifferentiableAt I 𝓘(ℝ, ℝ) (b ∘ q) x := hb.comp x hq
  have hr' : MDifferentiableAt I 𝓘(ℝ, ℝ) r x := hbq.congr_of_eventuallyEq hr
  have hmr : mfderiv I 𝓘(ℝ, ℝ) r x = (mfderiv IB 𝓘(ℝ, ℝ) b (q x)).comp (mfderiv I IB q x) := by
    rw [hr.mfderiv_eq]
    exact mfderiv_comp x hb hq
  have hF : MDifferentiableAt I 𝓘(ℝ, ℝ × ℝ) (fun z => (T z, r z)) x := hT.prodMk_space hr'
  have hfst : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ) (Prod.fst : ℝ × ℝ → ℝ)
      (T x, r x) := differentiableAt_fst.mdifferentiableAt
  have hsnd : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ) (Prod.snd : ℝ × ℝ → ℝ)
      (T x, r x) := differentiableAt_snd.mdifferentiableAt
  have h1 := mfderiv_comp x hfst hF
  have h2 := mfderiv_comp x hsnd hF
  have e1 : mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ) (Prod.fst : ℝ × ℝ → ℝ) (T x, r x) =
      ContinuousLinearMap.fst ℝ ℝ ℝ := by
    rw [mfderiv_eq_fderiv]
    exact fderiv_fst
  have e2 : mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ) (Prod.snd : ℝ × ℝ → ℝ) (T x, r x) =
      ContinuousLinearMap.snd ℝ ℝ ℝ := by
    rw [mfderiv_eq_fderiv]
    exact fderiv_snd
  rw [e1] at h1
  rw [e2] at h2
  have h1' : mfderiv I 𝓘(ℝ, ℝ) T x =
      (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (mfderiv I 𝓘(ℝ, ℝ × ℝ) (fun z => (T z, r z)) x) := h1
  have h2' : mfderiv I 𝓘(ℝ, ℝ) r x =
      (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (mfderiv I 𝓘(ℝ, ℝ × ℝ) (fun z => (T z, r z)) x) := h2
  intro ac
  obtain ⟨a, c⟩ := ac
  obtain ⟨u, hu⟩ := surjective_of_ne_zero_JN74 hbne c
  obtain ⟨v, hv⟩ := hrank (u, a)
  have hv1 : mfderiv I IB q x v = u := congrArg Prod.fst hv
  have hv2 : mfderiv I 𝓘(ℝ, ℝ) T x v = a := congrArg Prod.snd hv
  have h2v : mfderiv I 𝓘(ℝ, ℝ) r x v = c := by
    rw [hmr]
    change mfderiv IB 𝓘(ℝ, ℝ) b (q x) (mfderiv I IB q x v) = c
    rw [hv1]
    exact hu
  refine ⟨v, Prod.ext ?_ ?_⟩
  · exact (congrArg (fun L => L v) h1').symm.trans hv2
  · exact (congrArg (fun L => L v) h2').symm.trans h2v

end Kernel

end GC.GraphManifold.Assembly.FC39P0
