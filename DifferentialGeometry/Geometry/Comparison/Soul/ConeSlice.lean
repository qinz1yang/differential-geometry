import DifferentialGeometry.Geometry.Comparison.Soul.ImmersedSlice
import Mathlib.Analysis.Calculus.LocalExtr.Basic

set_option autoImplicit false
noncomputable section

open Set Filter Manifold
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Geometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]


def coneDeriv (L : F →L[ℝ] E) (v : E) (t : ℝ) : F × ℝ →L[ℝ] E :=
  t • (L.comp (ContinuousLinearMap.fst ℝ F ℝ)) +
    (ContinuousLinearMap.snd ℝ F ℝ).smulRight v


theorem hasFDerivAt_cone {f : F → E} {L : F →L[ℝ] E} {a : F} {t : ℝ}
    (hf : HasFDerivAt f L a) :
    HasFDerivAt (fun z : F × ℝ => z.2 • f z.1) (coneDeriv L (f a) t) (a, t) := by
  convert! (ContinuousLinearMap.snd ℝ F ℝ).hasFDerivAt.smul
    (hf.comp (a, t) (ContinuousLinearMap.fst ℝ F ℝ).hasFDerivAt) using 1

theorem coneDeriv_injective {L : F →L[ℝ] E} {v : E} {t : ℝ}
    (hL : Function.Injective L) (ht : t ≠ 0) (htrans : v ∉ L.range) :
    Function.Injective (coneDeriv L v t) := by
  have hker (z : F × ℝ) (hz : coneDeriv L v t z = 0) : z = 0 := by
    have heq : t • L z.1 + z.2 • v = 0 := hz
    have hz2 : z.2 = 0 := by
      by_contra hn
      have hscaled : z.2 • v ∈ L.range := by
        have hh : z.2 • v = -(t • L z.1) := by
          apply eq_neg_of_add_eq_zero_left
          simpa only [add_comm] using heq
        rw [hh]
        exact L.range.neg_mem (L.range.smul_mem t (L.mem_range_self z.1))
      have hh := L.range.smul_mem z.2⁻¹ hscaled
      exact htrans (by simpa only [smul_smul, inv_mul_cancel₀ hn, one_smul] using hh)
    have hz1 : z.1 = 0 := by
      rw [hz2, zero_smul, add_zero] at heq
      apply hL
      simpa only [map_zero] using (smul_eq_zero.mp heq).resolve_left ht
    exact Prod.ext hz1 hz2
  intro z w hzw
  exact sub_eq_zero.1 (hker (z - w) (by rw [map_sub, hzw, sub_self]))

theorem radial_not_mem_range_of_quad_min
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hpos : ∀ v : E, v ≠ 0 → 0 < B v v)
    {f : F → E} {a : F} (hf : DifferentiableAt ℝ f a)
    (hmin : IsLocalMin (fun x => B (f x) (f x)) a) (hfa : f a ≠ 0) :
    f a ∉ (fderiv ℝ f a).range := by
  rintro ⟨v, hv⟩
  change (fderiv ℝ f a) v = f a at hv
  have hd := (B.hasFDerivAt.comp a hf.hasFDerivAt).clm_apply hf.hasFDerivAt
  have hz := congrArg (fun L : F →L[ℝ] ℝ => L v) (hmin.hasFDerivAt_eq_zero hd)
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, zero_apply, Function.comp_apply, hv] at hz
  linarith [hpos (f a) hfa]

theorem exists_cone_slice [CompleteSpace E] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : F → E} {U : Set F} {a : F} {J : Set ℝ} {t : ℝ}
    (hU : IsOpen U) (ha : a ∈ U) (hJ : IsOpen J) (htJ : t ∈ J)
    (hf : ContDiffOn ℝ ∞ f U) (hinj : Function.Injective (fderiv ℝ f a))
    (ht : t ≠ 0) (htrans : f a ∉ (fderiv ℝ f a).range) :
    ∃ V : Set (F × ℝ), IsOpen V ∧ (a, t) ∈ V ∧ V ⊆ U ×ˢ J ∧
      InjOn (fun z : F × ℝ => z.2 • f z.1) V ∧
      IsEmbeddedSlice 𝓘(ℝ, E) (Module.finrank ℝ F + 1)
        ((fun z : F × ℝ => z.2 • f z.1) '' V) := by
  have hd := hasFDerivAt_cone
    ((hf.contDiffAt (hU.mem_nhds ha)).differentiableAt (by simp)).hasFDerivAt (t := t)
  obtain ⟨V, hV, haV, hVU, hVi, hVS⟩ := exists_slice_image (a := (a, t))
    (f := fun z : F × ℝ => z.2 • f z.1) (hU.prod hJ) ⟨ha, htJ⟩
    (contDiffOn_snd.smul (hf.comp contDiffOn_fst fun _ hz => hz.1))
    (by rw [hd.fderiv]; exact coneDeriv_injective hinj ht htrans)
  exact ⟨V, hV, haV, hVU, hVi, by simpa only [Module.finrank_prod, Module.finrank_self] using hVS⟩

theorem exists_cone_image [CompleteSpace E] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {f : F → E} {U : Set F} {a : F} {J : Set ℝ} {t : ℝ}
    (B : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞)
    (hU : IsOpen U) (ha : a ∈ U) (hJ : IsOpen J) (htJ : t ∈ J)
    (hf : ContDiffOn ℝ ∞ f U) (hinj : Function.Injective (fderiv ℝ f a))
    (ht : t ≠ 0) (htrans : f a ∉ (fderiv ℝ f a).range) (hbase : t • f a ∈ B.source) :
    ∃ V : Set (F × ℝ), IsOpen V ∧ (a, t) ∈ V ∧ V ⊆ U ×ˢ J ∧
      (fun z : F × ℝ => z.2 • f z.1) '' V ⊆ B.source ∧
      IsEmbeddedSlice I (Module.finrank ℝ F + 1)
        (B '' ((fun z : F × ℝ => z.2 • f z.1) '' V)) := by
  let cone : F × ℝ → E := fun z => z.2 • f z.1
  have hs : ContDiffOn ℝ ∞ cone (U ×ˢ J) :=
    contDiffOn_snd.smul (hf.comp contDiffOn_fst fun _ hz => hz.1)
  let W : Set (F × ℝ) := (U ×ˢ J) ∩ cone ⁻¹' B.source
  have hW : IsOpen W := hs.continuousOn.isOpen_inter_preimage (hU.prod hJ) B.open_source
  have hd := hasFDerivAt_cone
    ((hf.contDiffAt (hU.mem_nhds ha)).differentiableAt (by simp)).hasFDerivAt (t := t)
  obtain ⟨V, hV, haV, hVW, _, hVS⟩ := exists_slice_image hW ⟨⟨ha, htJ⟩, hbase⟩
    (hs.mono inter_subset_left) (by rw [hd.fderiv]; exact coneDeriv_injective hinj ht htrans)
  have hVB : cone '' V ⊆ B.source := by rintro _ ⟨z, hz, rfl⟩; exact (hVW hz).2
  refine ⟨V, hV, haV, hVW.trans inter_subset_left, hVB, ?_⟩
  simpa only [Module.finrank_prod, Module.finrank_self] using hVS.image B hVB

end DifferentialGeometry.Geometry
