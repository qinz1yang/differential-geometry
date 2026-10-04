import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.SaddleSlabProof.TwoArc
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.SaddleSlabProof.Matching

/-!
# One-saddle strips with a connected lower level

Lane RG03c (MD2b). When the lower level `f ⁻¹' {a}` of a one-saddle strip `D` is connected it is
one circle, parametrised by `ι` (`exists_circle_connected`), and both attaching arcs
`t ↦ invFun ι (arc D σ t)`, `σ = ±1`, are disjoint immersed arcs on it (`arcs_disjoint`); so they
have an attaching type `s = ±1` (`HasArcType`). `exists_levelMatching_connected`: two such strips
of the same model radius and the same type have maps `h`, `h'` between their lower levels with all
the properties of `exists_levelMatching` (inverse to each other, matching both attaching arcs,
`h ∘ π_a` smooth within the slab), built from one circle diffeomorphism
`exists_addCircle_diffeo_twoArc`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Topology DifferentialGeometry.Topology.Morse

namespace GC.Seifert.SaddleSlabProof

variable {H : Type} [TopologicalSpace H] {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ (MorseModel 2) H} [IsManifold I ∞ M] [T2Space M] [I.Boundaryless]
  {f : M → ℝ} {a b : ℝ} {p : M}

def arcT (D : GradientLikeStrip I f a b {p}) : ℝ := Real.sqrt (3 * eps D)

def arcT₁ (D : GradientLikeStrip I f a b {p}) : ℝ := Real.sqrt (2 * eps D)

def arcT₂ (D : GradientLikeStrip I f a b {p}) : ℝ := (arcT₁ D + arcT D) / 2

omit [T2Space M] [I.Boundaryless] in
theorem arcT_bounds (D : GradientLikeStrip I f a b {p}) :
    0 ≤ arcT₁ D ∧ arcT₁ D < arcT₂ D ∧ arcT₂ D < arcT D := by
  have hε := eps_pos D
  have h1 : arcT₁ D < arcT D := Real.sqrt_lt_sqrt (by linarith) (by linarith)
  refine ⟨Real.sqrt_nonneg _, ?_, ?_⟩ <;> unfold arcT₂ <;> linarith

theorem arc_circle_props (D : GradientLikeStrip I f a b {p}) (hrm : 8 * (ch D).r₀ ≤ rmD D)
    {ι : AddCircle (1 : ℝ) → M} (hι : ContMDiff 𝓘(ℝ, ℝ) I ∞ ι)
    (hinv : ∀ x ∈ range ι, ContMDiffWithinAt I 𝓘(ℝ, ℝ) ∞ (invFun ι) (range ι) x) {σ : ℝ}
    (hσ : σ ^ 2 = 1) (harcmem : ∀ t, t ^ 2 ≤ 3 * eps D → arc D σ t ∈ range ι) :
    (∀ t ∈ Ioo (-arcT D) (arcT D),
        ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun s => invFun ι (arc D σ s)) t) ∧
      InjOn (fun s => invFun ι (arc D σ s)) (Ioo (-arcT D) (arcT D)) ∧
      ∀ t ∈ Ioo (-arcT D) (arcT D),
        mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s => invFun ι (arc D σ s)) t ≠ 0 := by
  have hε := eps_pos D
  set T := arcT D with hT
  have hIoo : ∀ t ∈ Ioo (-T) T, t ^ 2 ≤ 3 * eps D := fun t ht =>
    (sq_lt_of_mem_Ioo (by linarith) ht).le
  have hsm : ∀ t ∈ Ioo (-T) T,
      ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun s => invFun ι (arc D σ s)) t := by
    intro t ht
    have h1 : ContMDiffWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (invFun ι ∘ arc D σ) (Ioo (-T) T) t :=
      (hinv _ (harcmem t (hIoo t ht))).comp t
        (contMDiffAt_arc D hrm hσ (hIoo t ht)).contMDiffWithinAt
        fun s hs => harcmem s (hIoo s hs)
    exact h1.contMDiffAt (isOpen_Ioo.mem_nhds ht)
  refine ⟨hsm, ?_, ?_⟩
  · intro t ht t' ht' htt
    have h1 := congrArg ι htt
    simp only [invFun_eq (harcmem t (hIoo t ht)), invFun_eq (harcmem t' (hIoo t' ht'))] at h1
    exact arc_injOn D hrm hσ (hIoo t ht) (hIoo t' ht') h1
  · intro t ht h0
    apply mfderiv_arc_ne_zero D hrm hσ (hIoo t ht)
    have hev : (ι ∘ fun s => invFun ι (arc D σ s)) =ᶠ[𝓝 t] arc D σ :=
      eventually_of_mem (isOpen_Ioo.mem_nhds ht) fun s hs => invFun_eq (harcmem s (hIoo s hs))
    have hβ : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s => invFun ι (arc D σ s)) t :=
      (hsm t ht).mdifferentiableAt (by simp)
    have hιd : MDifferentiableAt 𝓘(ℝ, ℝ) I ι (invFun ι (arc D σ t)) :=
      hι.contMDiffAt.mdifferentiableAt (by simp)
    have hc := mfderiv_comp t hιd hβ
    have h2 : mfderiv 𝓘(ℝ, ℝ) I (arc D σ) t = 0 := by
      refine (hev.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := I)).symm.trans (hc.trans ?_)
      rw [h0, ContinuousLinearMap.comp_zero]
      rfl
    rw [h2]
    rfl

theorem arc_ne_arc (D : GradientLikeStrip I f a b {p}) (hrm : 8 * (ch D).r₀ ≤ rmD D) {t t' : ℝ}
    (ht : t ^ 2 ≤ 3 * eps D) (ht' : t' ^ 2 ≤ 3 * eps D) : arc D (-1) t ≠ arc D 1 t' := by
  intro h
  unfold arc at h
  have h1 := GradientLikeStrip.flow_injective D _ h
  have h2 := (ch D).χ.injOn ((ch D).hball (footPt_mem_ball D hrm (by norm_num) ht))
    ((ch D).hball (footPt_mem_ball D hrm (by norm_num) ht')) h1
  have h3 := congrFun h2 0
  simp only [footPt_zero] at h3
  have hs1 := Real.sqrt_pos.mpr (show 0 < 2 * eps D + t ^ 2 by linarith [eps_pos D, sq_nonneg t])
  have hs2 := Real.sqrt_pos.mpr (show 0 < 2 * eps D + t' ^ 2 by
    linarith [eps_pos D, sq_nonneg t'])
  linarith

theorem exists_circle_connected (D : GradientLikeStrip I f a b {p})
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hk : (ch D).k = 1) (hrm : 8 * (ch D).r₀ ≤ rmD D)
    (ha : a < f p - 2 * eps D) (hb : f p + 2 * eps D < b)
    (hreg : ∀ x, f x = a ∨ f x = b → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0)
    (hcpt : IsCompact (f ⁻¹' Icc a b)) (hlowc : IsPreconnected (f ⁻¹' {a})) :
    ∃ ι : AddCircle (1 : ℝ) → M, ContMDiff 𝓘(ℝ, ℝ) I ∞ ι ∧ Injective ι ∧
      range ι = connectedComponentIn (f ⁻¹' {a}) (arc D 1 0) ∧ range ι = f ⁻¹' {a} ∧
      (∀ x ∈ range ι, ContMDiffWithinAt I 𝓘(ℝ, ℝ) ∞ (invFun ι) (range ι) x) ∧
      ∀ σ : ℝ, σ ^ 2 = 1 → ∀ t, t ^ 2 ≤ 3 * eps D → arc D σ t ∈ range ι := by
  have hε := eps_pos D
  obtain ⟨ι, hι, hιi, hr, hinv, -, -, -, -⟩ :=
    exists_circle D hf hk hrm ha hb hreg hcpt (σ := 1) (by norm_num)
  have h0 : (0 : ℝ) ^ 2 ≤ 3 * eps D := by linarith
  have hr' : range ι = f ⁻¹' {a} := by
    rw [hr]
    exact hlowc.connectedComponentIn
      (f_arc D hf hk hrm (by linarith) (by linarith) (by norm_num) h0)
  refine ⟨ι, hι, hιi, hr, hr', hinv, fun σ hσ t ht => ?_⟩
  rw [hr']
  exact f_arc D hf hk hrm (by linarith) (by linarith) hσ ht

variable {H' : Type} [TopologicalSpace H'] {M' : Type*} [TopologicalSpace M']
  [ChartedSpace H' M'] {I' : ModelWithCorners ℝ (MorseModel 2) H'} [IsManifold I' ∞ M']
  [T2Space M'] [I'.Boundaryless] {f' : M' → ℝ} {a' b' : ℝ} {p' : M'}

theorem exists_levelMatching_connected (D : GradientLikeStrip I f a b {p})
    (D' : GradientLikeStrip I' f' a' b' {p'}) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hf' : ContMDiff I' 𝓘(ℝ, ℝ) ∞ f') (hr : (ch D').r₀ = (ch D).r₀) (hrm : 8 * (ch D).r₀ ≤ rmD D)
    (hrm' : 8 * (ch D').r₀ ≤ rmD D') (hab : a < b) (hab' : a' < b')
    (hreg : ∀ x, f x = a ∨ f x = b → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0)
    (hreg' : ∀ x, f' x = a' ∨ f' x = b' → mfderiv I' 𝓘(ℝ, ℝ) f' x ≠ 0)
    {ι : AddCircle (1 : ℝ) → M} {ι' : AddCircle (1 : ℝ) → M'} (hι : ContMDiff 𝓘(ℝ, ℝ) I ∞ ι)
    (hι' : ContMDiff 𝓘(ℝ, ℝ) I' ∞ ι') (hιi : Injective ι) (hιi' : Injective ι')
    (hrc : range ι = connectedComponentIn (f ⁻¹' {a}) (arc D 1 0))
    (hrc' : range ι' = connectedComponentIn (f' ⁻¹' {a'}) (arc D' 1 0))
    (hra : range ι = f ⁻¹' {a}) (hra' : range ι' = f' ⁻¹' {a'})
    (hinv : ∀ x ∈ range ι, ContMDiffWithinAt I 𝓘(ℝ, ℝ) ∞ (invFun ι) (range ι) x)
    (hinv' : ∀ x ∈ range ι', ContMDiffWithinAt I' 𝓘(ℝ, ℝ) ∞ (invFun ι') (range ι') x)
    (harc : ∀ σ : ℝ, σ ^ 2 = 1 → ∀ t, t ^ 2 ≤ 3 * eps D → arc D σ t ∈ range ι)
    (harc' : ∀ σ : ℝ, σ ^ 2 = 1 → ∀ t, t ^ 2 ≤ 3 * eps D' → arc D' σ t ∈ range ι') {s : ℝ}
    (hs : s ^ 2 = 1)
    (htype : HasArcType (fun t => invFun ι (arc D 1 t)) (fun t => invFun ι (arc D (-1) t))
      (arcT₂ D) s)
    (htype' : HasArcType (fun t => invFun ι' (arc D' 1 t)) (fun t => invFun ι' (arc D' (-1) t))
      (arcT₂ D') s) :
    ∃ (h : M → M') (h' : M' → M), (∀ z, f z = a → f' (h z) = a') ∧
      (∀ z, f' z = a' → f (h' z) = a) ∧ (∀ z, f z = a → h' (h z) = z) ∧
      (∀ z, f' z = a' → h (h' z) = z) ∧
      (∀ σ t, σ ^ 2 = 1 → t ^ 2 ≤ 2 * eps D → h (arc D σ t) = arc D' σ t) ∧
      (∀ σ t, σ ^ 2 = 1 → t ^ 2 ≤ 2 * eps D → h' (arc D' σ t) = arc D σ t) ∧
      (∀ x ∈ lowDomain D, f x ∈ Icc a b →
        ContMDiffWithinAt I I' ∞ (fun y => h (D.π a y)) (f ⁻¹' Icc a b) x) ∧
      ∀ x ∈ lowDomain D', f' x ∈ Icc a' b' →
        ContMDiffWithinAt I' I ∞ (fun y => h' (D'.π a' y)) (f' ⁻¹' Icc a' b') x := by
  have hε := eps_pos D
  have hε' := eps_eq D D' hr
  have hT₂ : arcT₂ D' = arcT₂ D := by unfold arcT₂ arcT₁ arcT; rw [hε']
  rw [hT₂] at htype'
  rw [hε'] at harc'
  obtain ⟨hT₁0, hT₁₂, hT₂T⟩ := arcT_bounds D
  have hsub : Icc (-arcT₂ D) (arcT₂ D) ⊆ Ioo (-arcT D) (arcT D) := fun t ht =>
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hsq : ∀ t ∈ Icc (-arcT₂ D) (arcT₂ D), t ^ 2 ≤ 3 * eps D := fun t ht =>
    (sq_lt_of_mem_Ioo (by linarith) (hsub ht)).le
  obtain ⟨-, hinj₁, -⟩ := arc_circle_props (σ := 1) D hrm hι hinv (by norm_num)
    (harc 1 (by norm_num))
  obtain ⟨-, hinj'₁, -⟩ := arc_circle_props (σ := 1) D' hrm' hι' hinv' (by norm_num) (by
    rw [← hε'] at harc'; exact harc' 1 (by norm_num))
  have hT' : arcT D' = arcT D := by unfold arcT; rw [hε']
  rw [hT'] at hinj'₁
  have hdisj : ∀ t ∈ Icc (-arcT₂ D) (arcT₂ D), ∀ t' ∈ Icc (-arcT₂ D) (arcT₂ D),
      invFun ι (arc D (-1) t) ≠ invFun ι (arc D 1 t') := by
    intro t ht t' ht' h
    have h1 := congrArg ι h
    rw [invFun_eq (harc (-1) (by norm_num) t (hsq t ht)),
      invFun_eq (harc 1 (by norm_num) t' (hsq t' ht'))] at h1
    exact arc_ne_arc D hrm (hsq t ht) (hsq t' ht') h1
  have hdisj' : ∀ t ∈ Icc (-arcT₂ D) (arcT₂ D), ∀ t' ∈ Icc (-arcT₂ D) (arcT₂ D),
      invFun ι' (arc D' (-1) t) ≠ invFun ι' (arc D' 1 t') := by
    intro t ht t' ht' h
    have h1 := congrArg ι' h
    rw [invFun_eq (harc' (-1) (by norm_num) t (hsq t ht)),
      invFun_eq (harc' 1 (by norm_num) t' (hsq t' ht'))] at h1
    exact arc_ne_arc D' hrm' (by rw [hε']; exact hsq t ht) (by rw [hε']; exact hsq t' ht') h1
  obtain ⟨k, hk₀⟩ := exists_addCircle_diffeo_twoArc hT₁0 hT₁₂ hs htype htype'
    (hinj₁.mono hsub) (hinj'₁.mono hsub) hdisj hdisj'
  have hIcc : ∀ t, t ^ 2 ≤ 2 * eps D → t ∈ Icc (-arcT₁ D) (arcT₁ D) := fun t ht =>
    abs_le.mp (Real.abs_le_sqrt ht)
  have h23 : ∀ t, t ^ 2 ≤ 2 * eps D → t ^ 2 ≤ 3 * eps D := fun t ht => by linarith
  set h : M → M' := fun x => ι' (k (invFun ι x)) with hhdef
  set h' : M' → M := fun x => ι (k.symm (invFun ι' x)) with hh'def
  have hab₀ : f (arc D 1 0) = a := by
    have := harc 1 (by norm_num) 0 (by linarith)
    rw [hra] at this
    exact this
  have hab₀' : f' (arc D' 1 0) = a' := by
    have := harc' 1 (by norm_num) 0 (by linarith)
    rw [hra'] at this
    exact this
  refine ⟨h, h', fun z _ => ?_, fun z _ => ?_, fun z hz => ?_, fun z hz => ?_, ?_, ?_, ?_, ?_⟩
  · have := mem_range_self (f := ι') (k (invFun ι z))
    rw [hra'] at this
    exact this
  · have := mem_range_self (f := ι) (k.symm (invFun ι' z))
    rw [hra] at this
    exact this
  · have hz' : z ∈ range ι := by rw [hra]; exact hz
    simp only [hhdef, hh'def]
    rw [leftInverse_invFun hιi', Diffeomorph.symm_apply_apply, invFun_eq hz']
  · have hz' : z ∈ range ι' := by rw [hra']; exact hz
    simp only [hhdef, hh'def]
    rw [leftInverse_invFun hιi, Diffeomorph.apply_symm_apply, invFun_eq hz']
  · intro σ t hσ ht
    simp only [hhdef]
    rcases sq_eq_one_cases hσ with rfl | rfl
    · rw [(hk₀ t (hIcc t ht)).1, invFun_eq (harc' 1 (by norm_num) t (h23 t ht))]
    · rw [(hk₀ t (hIcc t ht)).2, invFun_eq (harc' (-1) (by norm_num) t (h23 t ht))]
  · intro σ t hσ ht
    simp only [hh'def]
    rcases sq_eq_one_cases hσ with rfl | rfl
    · rw [← (hk₀ t (hIcc t ht)).1, Diffeomorph.symm_apply_apply,
        invFun_eq (harc 1 (by norm_num) t (h23 t ht))]
    · rw [← (hk₀ t (hIcc t ht)).2, Diffeomorph.symm_apply_apply,
        invFun_eq (harc (-1) (by norm_num) t (h23 t ht))]
  · intro x hx hxS
    have hz : D.π a x ∈ range ι := by rw [hra]; exact f_π_of_lowDomain D hf hxS hx
    exact contMDiffWithinAt_branch D hf hrm hab hreg hι' k hinv hab₀ hrc
      (fun z _ => rfl) hx hz
  · intro x hx hxS
    have hz : D'.π a' x ∈ range ι' := by rw [hra']; exact f_π_of_lowDomain D' hf' hxS hx
    exact contMDiffWithinAt_branch D' hf' hrm' hab' hreg' hι k.symm hinv' hab₀' hrc'
      (fun z _ => rfl) hx hz

end GC.Seifert.SaddleSlabProof
