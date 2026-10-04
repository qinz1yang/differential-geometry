import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.SaddleSlabProof.TwoArcGlue
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.SaddleSlabModels

/-!
# One-saddle slabs with a connected lower level

Lane RG03c (MD2b). For a one-saddle slab with connected lower level both attaching arcs lie on
the one lower circle and have an attaching type, coherent or twisted (`HasArcType`).
`exists_prepared` builds, for every small model radius, a gradient-like strip, a circle
parametrisation of the lower level and the type of the two attaching arcs.
`exists_slabDiffeo_of_sameType`: two such slabs prepared with the same radius and the same type
are diffeomorphic by a level-preserving map (`exists_levelMatching_connected` and
`exists_slabDiffeo_of_matching`). `oneSaddleSlab_connectedLower_cases_of_models`: if two model
slabs `M₁`, `M₂` with connected lower levels have a disconnected, resp. connected, upper level,
then every one-saddle slab with connected lower level is diffeomorphic to `M₁` or to `M₂`,
preserving the levels: the two models cannot have the same type (a level-preserving
diffeomorphism would identify their upper levels, `isPreconnected_upper_of_diffeo`), so the type
of the slab is the type of one of them.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open scoped Manifold ContDiff Topology
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Topology.Morse
open GC.Seifert.SaddleSlabProof

universe uN uN' u₁ u₂

namespace GC.Seifert

theorem isPreconnected_upper_of_diffeo {E H : Type} {N : Type uN} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H] [TopologicalSpace N]
    [ChartedSpace H N] [T2Space N] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    [IsManifold I ∞ N] {E' H' : Type} {N' : Type uN'} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [FiniteDimensional ℝ E'] [TopologicalSpace H'] [TopologicalSpace N'] [ChartedSpace H' N']
    [T2Space N'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless] [IsManifold I' ∞ N']
    (hdim : Module.finrank ℝ E = 2) (hdim' : Module.finrank ℝ E' = 2) {f : N → ℝ}
    {f' : N' → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hf' : ContMDiff I' 𝓘(ℝ, ℝ) ∞ f')
    {a b a' b' : ℝ} (hab : a < b) (hab' : a' < b')
    (hreg : ∀ x, f x = a ∨ f x = b → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0)
    (hreg' : ∀ x, f' x = a' ∨ f' x = b' → mfderiv I' 𝓘(ℝ, ℝ) f' x ≠ 0) :
    letI := (slabAtlas hdim hf hab hreg).toChartedSpace
    letI := (slabAtlas hdim' hf' hab' hreg').toChartedSpace
    ∀ e : slabSet f a b ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ slabSet f' a' b',
      (∀ x : slabSet f a b, f x = b ↔ f' (e x) = b') →
      IsPreconnected (f' ⁻¹' {b'}) → IsPreconnected (f ⁻¹' {b}) := by
  let := (slabAtlas hdim hf hab hreg).toChartedSpace
  let := (slabAtlas hdim' hf' hab' hreg').toChartedSpace
  intro e he h'
  set A : Set (slabSet f' a' b') := {y | f' y.val = b'} with hA
  have hA' : Subtype.val '' A = f' ⁻¹' {b'} := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz
    · intro hy
      exact ⟨⟨y, (mem_slabSet_iff hab'.le y).mpr ⟨(show f' y = b' from hy) ▸ hab'.le,
        (show f' y = b' from hy).le⟩⟩, hy, rfl⟩
  have hApre : IsPreconnected A := by
    rw [← Topology.IsInducing.subtypeVal.isPreconnected_image, hA']
    exact h'
  have hB : e.symm '' A = {x : slabSet f a b | f x.val = b} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have h1 := (he (e.symm y)).mpr
      rw [Diffeomorph.apply_symm_apply] at h1
      exact h1 hy
    · intro hx
      exact ⟨e x, (he x).mp hx, e.symm_apply_apply x⟩
  have hBpre : IsPreconnected {x : slabSet f a b | f x.val = b} := by
    rw [← hB]
    exact hApre.image _ e.symm.continuous.continuousOn
  have hC : Subtype.val '' {x : slabSet f a b | f x.val = b} = f ⁻¹' {b} := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz
    · intro hy
      exact ⟨⟨y, (mem_slabSet_iff hab.le y).mpr ⟨(show f y = b from hy) ▸ hab.le,
        (show f y = b from hy).le⟩⟩, hy, rfl⟩
  rw [← hC]
  exact hBpre.image _ continuous_subtype_val.continuousOn

theorem exists_prepared {E H : Type} {N : Type uN} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H] [TopologicalSpace N]
    [ChartedSpace H N] [T2Space N] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    [IsManifold I ∞ N] (hdim : Module.finrank ℝ E = 2) {f : N → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ} (hab : a < b)
    (hreg : ∀ x, f x = a ∨ f x = b → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0) {p : N}
    (hp : f p ∈ Ioo a b) (hnd : IsNondegenerateCriticalPointAt I f p)
    (hidx : sigNeg (chartHessianAt (fun y => f ((extChartAt I p).symm y))
      (extChartAt I p p)) = 1)
    (huniq : ∀ x, f x ∈ Icc a b → IsCriticalPointAt I f x → x = p)
    (hcpt : IsCompact (f ⁻¹' Icc a b))
    (hlowc : IsPreconnected (f ⁻¹' {a})) :
    ∃ R > 0, ∀ r : ℝ, 0 < r → 16 * r < R → 2 * r ^ 2 < f p - a → 2 * r ^ 2 < b - f p →
      ∃ D : GradientLikeStrip (modelJ I hdim) f a b {p}, (ch D).k = 1 ∧ (ch D).r₀ = r ∧
        8 * (ch D).r₀ ≤ rmD D ∧ a < f p - 2 * eps D ∧ f p + 2 * eps D < b ∧
        ∃ ι : AddCircle (1 : ℝ) → N, ContMDiff 𝓘(ℝ, ℝ) (modelJ I hdim) ∞ ι ∧ Injective ι ∧
          range ι = connectedComponentIn (f ⁻¹' {a}) (arc D 1 0) ∧ range ι = f ⁻¹' {a} ∧
          (∀ x ∈ range ι, ContMDiffWithinAt (modelJ I hdim) 𝓘(ℝ, ℝ) ∞ (invFun ι) (range ι) x) ∧
          (∀ σ : ℝ, σ ^ 2 = 1 → ∀ t, t ^ 2 ≤ 3 * eps D → arc D σ t ∈ range ι) ∧
          ∃ s : ℝ, s ^ 2 = 1 ∧ HasArcType (fun t => invFun ι (arc D 1 t))
            (fun t => invFun ι (arc D (-1) t)) (arcT₂ D) s := by
  obtain ⟨c, hck, hcO⟩ := exists_saddleChart hdim hf hab hreg hp hnd hidx huniq hcpt
  refine ⟨c.R, c.R_pos, fun r hr hrR hra hrb => ?_⟩
  obtain ⟨D, hk, hrD, hrm, ha, hb⟩ := exists_strip_of_radius hdim hf hab hreg hp hnd huniq hcpt
    c hck hcO hr hrR (by linarith) (by linarith)
  have hfJ : ContMDiff (modelJ I hdim) 𝓘(ℝ, ℝ) ∞ f :=
    (ContinuousLinearEquiv.contMDiff_transContinuousLinearEquiv_left _).mpr hf
  have hregJ : ∀ x, f x = a ∨ f x = b → mfderiv (modelJ I hdim) 𝓘(ℝ, ℝ) f x ≠ 0 :=
    fun x hx hc =>
      hreg x hx ((isCriticalPointAt_transContinuousLinearEquiv_iff I (modelL hdim) f x).mp hc)
  obtain ⟨ι, hι, hιi, hrc, hra', hinv, harc⟩ :=
    exists_circle_connected D hfJ hk hrm ha hb hregJ hcpt hlowc
  obtain ⟨hsm₁, -, himm₁⟩ := arc_circle_props (σ := 1) D hrm hι hinv (by norm_num)
    (harc 1 (by norm_num))
  obtain ⟨hsm₂, -, himm₂⟩ := arc_circle_props (σ := -1) D hrm hι hinv (by norm_num)
    (harc (-1) (by norm_num))
  obtain ⟨hT₁0, hT₁₂, hT₂T⟩ := arcT_bounds D
  obtain ⟨s, hs, htype⟩ := exists_hasArcType (by linarith) hT₂T hsm₁ himm₁ hsm₂ himm₂
  exact ⟨D, hk, hrD, hrm, ha, hb, ι, hι, hιi, hrc, hra', hinv, harc, s, hs, htype⟩

theorem exists_slabDiffeo_of_sameType {E H : Type} {N : Type uN} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H] [TopologicalSpace N]
    [ChartedSpace H N] [T2Space N] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    [IsManifold I ∞ N] {E' H' : Type} {N' : Type uN'} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [FiniteDimensional ℝ E'] [TopologicalSpace H'] [TopologicalSpace N'] [ChartedSpace H' N']
    [T2Space N'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless] [IsManifold I' ∞ N']
    (hdim : Module.finrank ℝ E = 2) (hdim' : Module.finrank ℝ E' = 2) {f : N → ℝ}
    {f' : N' → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hf' : ContMDiff I' 𝓘(ℝ, ℝ) ∞ f')
    {a b a' b' : ℝ} (hab : a < b) (hab' : a' < b')
    (hreg : ∀ x, f x = a ∨ f x = b → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0)
    (hreg' : ∀ x, f' x = a' ∨ f' x = b' → mfderiv I' 𝓘(ℝ, ℝ) f' x ≠ 0) {p : N} {p' : N'}
    (D : GradientLikeStrip (modelJ I hdim) f a b {p})
    (D' : GradientLikeStrip (modelJ I' hdim') f' a' b' {p'}) (hk : (ch D).k = 1)
    (hk' : (ch D').k = 1) (hr₀ : (ch D').r₀ = (ch D).r₀) (hrm : 8 * (ch D).r₀ ≤ rmD D)
    (hrm' : 8 * (ch D').r₀ ≤ rmD D') (ha : a < f p - 2 * eps D) (hb : f p + 2 * eps D < b)
    (ha' : a' < f' p' - 2 * eps D') (hb' : f' p' + 2 * eps D' < b')
    {ι : AddCircle (1 : ℝ) → N} {ι' : AddCircle (1 : ℝ) → N'}
    (hι : ContMDiff 𝓘(ℝ, ℝ) (modelJ I hdim) ∞ ι) (hι' : ContMDiff 𝓘(ℝ, ℝ) (modelJ I' hdim') ∞ ι')
    (hιi : Injective ι) (hιi' : Injective ι')
    (hrc : range ι = connectedComponentIn (f ⁻¹' {a}) (arc D 1 0))
    (hrc' : range ι' = connectedComponentIn (f' ⁻¹' {a'}) (arc D' 1 0))
    (hra : range ι = f ⁻¹' {a}) (hra' : range ι' = f' ⁻¹' {a'})
    (hinv : ∀ x ∈ range ι, ContMDiffWithinAt (modelJ I hdim) 𝓘(ℝ, ℝ) ∞ (invFun ι) (range ι) x)
    (hinv' : ∀ x ∈ range ι',
      ContMDiffWithinAt (modelJ I' hdim') 𝓘(ℝ, ℝ) ∞ (invFun ι') (range ι') x)
    (harc : ∀ σ : ℝ, σ ^ 2 = 1 → ∀ t, t ^ 2 ≤ 3 * eps D → arc D σ t ∈ range ι)
    (harc' : ∀ σ : ℝ, σ ^ 2 = 1 → ∀ t, t ^ 2 ≤ 3 * eps D' → arc D' σ t ∈ range ι') {s : ℝ}
    (hs : s ^ 2 = 1)
    (htype : HasArcType (fun t => invFun ι (arc D 1 t)) (fun t => invFun ι (arc D (-1) t))
      (arcT₂ D) s)
    (htype' : HasArcType (fun t => invFun ι' (arc D' 1 t)) (fun t => invFun ι' (arc D' (-1) t))
      (arcT₂ D') s) :
    letI := (slabAtlas hdim hf hab hreg).toChartedSpace
    letI := (slabAtlas hdim' hf' hab' hreg').toChartedSpace
    ∃ e : slabSet f a b ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ slabSet f' a' b',
      ∀ x : slabSet f a b, (f x = a ↔ f' (e x) = a') ∧ (f x = b ↔ f' (e x) = b') := by
  have hfJ : ContMDiff (modelJ I hdim) 𝓘(ℝ, ℝ) ∞ f :=
    (ContinuousLinearEquiv.contMDiff_transContinuousLinearEquiv_left _).mpr hf
  have hfJ' : ContMDiff (modelJ I' hdim') 𝓘(ℝ, ℝ) ∞ f' :=
    (ContinuousLinearEquiv.contMDiff_transContinuousLinearEquiv_left _).mpr hf'
  have hregJ : ∀ x, f x = a ∨ f x = b → mfderiv (modelJ I hdim) 𝓘(ℝ, ℝ) f x ≠ 0 :=
    fun x hx hc =>
      hreg x hx ((isCriticalPointAt_transContinuousLinearEquiv_iff I (modelL hdim) f x).mp hc)
  have hregJ' : ∀ x, f' x = a' ∨ f' x = b' → mfderiv (modelJ I' hdim') 𝓘(ℝ, ℝ) f' x ≠ 0 :=
    fun x hx hc =>
      hreg' x hx ((isCriticalPointAt_transContinuousLinearEquiv_iff I' (modelL hdim') f' x).mp hc)
  have hε' : eps D' = eps D := eps_eq D D' hr₀
  obtain ⟨h, h', hL, hL', hh, hh', hH, hH', hsm, hsm'⟩ := exists_levelMatching_connected D D' hfJ
    hfJ' hr₀ hrm hrm' hab hab' hregJ hregJ' hι hι' hιi hιi' hrc hrc' hra hra' hinv hinv' harc
    harc' hs htype htype'
  exact exists_slabDiffeo_of_matching hdim hdim' hf hf' hab hab' hreg hreg' D D' hk hk' hr₀ hrm
    hrm' ha hb (by rw [← hε']; exact ha') (by rw [← hε']; exact hb') hL hL' hh hh' hH hH' hsm
    hsm'

private theorem exists_radius₃ {R R₁ R₂ δ : ℝ} (hR : 0 < R) (hR₁ : 0 < R₁) (hR₂ : 0 < R₂)
    (hδ : 0 < δ) :
    ∃ r : ℝ, 0 < r ∧ 16 * r < R ∧ 16 * r < R₁ ∧ 16 * r < R₂ ∧ 2 * r ^ 2 < δ := by
  set r := min (min (R / 32) (min (R₁ / 32) (R₂ / 32))) (min 1 (δ / 4)) with hr
  have hm1 := min_le_left (min (R / 32) (min (R₁ / 32) (R₂ / 32))) (min 1 (δ / 4))
  have hm2 := min_le_right (min (R / 32) (min (R₁ / 32) (R₂ / 32))) (min 1 (δ / 4))
  have h1 := min_le_left (R / 32) (min (R₁ / 32) (R₂ / 32))
  have h2 := min_le_right (R / 32) (min (R₁ / 32) (R₂ / 32))
  have h3 := min_le_left (R₁ / 32) (R₂ / 32)
  have h4 := min_le_right (R₁ / 32) (R₂ / 32)
  have h5 := min_le_left (1 : ℝ) (δ / 4)
  have h6 := min_le_right (1 : ℝ) (δ / 4)
  have hr0 : 0 < r := lt_min (lt_min (by linarith) (lt_min (by linarith) (by linarith)))
    (lt_min one_pos (by linarith))
  refine ⟨r, hr0, by linarith, by linarith, by linarith, ?_⟩
  have hr1 : r ≤ 1 := hm2.trans h5
  have hr2 : r ≤ δ / 4 := hm2.trans h6
  nlinarith

theorem oneSaddleSlab_connectedLower_cases_of_models {E H : Type} {N : Type uN}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H] [TopologicalSpace N]
    [ChartedSpace H N] [T2Space N] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    [IsManifold I ∞ N] (hdim : Module.finrank ℝ E = 2) {f : N → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ} (hab : a < b)
    (hreg : ∀ x, f x = a ∨ f x = b → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0) {p : N}
    (hp : f p ∈ Ioo a b) (hnd : IsNondegenerateCriticalPointAt I f p)
    (hidx : sigNeg (chartHessianAt (fun y => f ((extChartAt I p).symm y))
      (extChartAt I p p)) = 1)
    (huniq : ∀ x, f x ∈ Icc a b → IsCriticalPointAt I f x → x = p)
    (hcpt : IsCompact (f ⁻¹' Icc a b))
    (hlowc : IsPreconnected (f ⁻¹' {a})) {E₁ H₁ : Type} {N₁ : Type u₁} [NormedAddCommGroup E₁]
    [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁] [TopologicalSpace H₁] [TopologicalSpace N₁]
    [ChartedSpace H₁ N₁] [T2Space N₁] {I₁ : ModelWithCorners ℝ E₁ H₁} [I₁.Boundaryless]
    [IsManifold I₁ ∞ N₁] (hdim₁ : Module.finrank ℝ E₁ = 2) {f₁ : N₁ → ℝ}
    (hf₁ : ContMDiff I₁ 𝓘(ℝ, ℝ) ∞ f₁) {a₁ b₁ : ℝ} (hab₁ : a₁ < b₁)
    (hreg₁ : ∀ x, f₁ x = a₁ ∨ f₁ x = b₁ → mfderiv I₁ 𝓘(ℝ, ℝ) f₁ x ≠ 0) {p₁ : N₁}
    (hp₁ : f₁ p₁ ∈ Ioo a₁ b₁) (hnd₁ : IsNondegenerateCriticalPointAt I₁ f₁ p₁)
    (hidx₁ : sigNeg (chartHessianAt (fun y => f₁ ((extChartAt I₁ p₁).symm y))
      (extChartAt I₁ p₁ p₁)) = 1)
    (huniq₁ : ∀ x, f₁ x ∈ Icc a₁ b₁ → IsCriticalPointAt I₁ f₁ x → x = p₁)
    (hcpt₁ : IsCompact (f₁ ⁻¹' Icc a₁ b₁))
    (hlowc₁ : IsPreconnected (f₁ ⁻¹' {a₁})) (hup₁ : ¬ IsPreconnected (f₁ ⁻¹' {b₁}))
    {E₂ H₂ : Type} {N₂ : Type u₂} [NormedAddCommGroup E₂]
    [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂] [TopologicalSpace H₂] [TopologicalSpace N₂]
    [ChartedSpace H₂ N₂] [T2Space N₂] {I₂ : ModelWithCorners ℝ E₂ H₂} [I₂.Boundaryless]
    [IsManifold I₂ ∞ N₂] (hdim₂ : Module.finrank ℝ E₂ = 2) {f₂ : N₂ → ℝ}
    (hf₂ : ContMDiff I₂ 𝓘(ℝ, ℝ) ∞ f₂) {a₂ b₂ : ℝ} (hab₂ : a₂ < b₂)
    (hreg₂ : ∀ x, f₂ x = a₂ ∨ f₂ x = b₂ → mfderiv I₂ 𝓘(ℝ, ℝ) f₂ x ≠ 0) {p₂ : N₂}
    (hp₂ : f₂ p₂ ∈ Ioo a₂ b₂) (hnd₂ : IsNondegenerateCriticalPointAt I₂ f₂ p₂)
    (hidx₂ : sigNeg (chartHessianAt (fun y => f₂ ((extChartAt I₂ p₂).symm y))
      (extChartAt I₂ p₂ p₂)) = 1)
    (huniq₂ : ∀ x, f₂ x ∈ Icc a₂ b₂ → IsCriticalPointAt I₂ f₂ x → x = p₂)
    (hcpt₂ : IsCompact (f₂ ⁻¹' Icc a₂ b₂))
    (hlowc₂ : IsPreconnected (f₂ ⁻¹' {a₂})) (hup₂ : IsPreconnected (f₂ ⁻¹' {b₂})) :
    letI := (slabAtlas hdim hf hab hreg).toChartedSpace
    letI := (slabAtlas hdim₁ hf₁ hab₁ hreg₁).toChartedSpace
    letI := (slabAtlas hdim₂ hf₂ hab₂ hreg₂).toChartedSpace
    (∃ e : slabSet f a b ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ slabSet f₁ a₁ b₁,
      ∀ x : slabSet f a b, (f x = a ↔ f₁ (e x) = a₁) ∧ (f x = b ↔ f₁ (e x) = b₁)) ∨
    (∃ e : slabSet f a b ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ slabSet f₂ a₂ b₂,
      ∀ x : slabSet f a b, (f x = a ↔ f₂ (e x) = a₂) ∧ (f x = b ↔ f₂ (e x) = b₂)) := by
  obtain ⟨R, hR, hP⟩ := exists_prepared hdim hf hab hreg hp hnd hidx huniq hcpt hlowc
  obtain ⟨R₁, hR₁, hP₁⟩ := exists_prepared hdim₁ hf₁ hab₁ hreg₁ hp₁ hnd₁ hidx₁ huniq₁ hcpt₁
    hlowc₁
  obtain ⟨R₂, hR₂, hP₂⟩ := exists_prepared hdim₂ hf₂ hab₂ hreg₂ hp₂ hnd₂ hidx₂ huniq₂ hcpt₂
    hlowc₂
  set δ := min (min (min (f p - a) (b - f p)) (min (f₁ p₁ - a₁) (b₁ - f₁ p₁)))
    (min (f₂ p₂ - a₂) (b₂ - f₂ p₂)) with hδ
  have hδ0 : 0 < δ := lt_min (lt_min (lt_min (by linarith [hp.1]) (by linarith [hp.2]))
    (lt_min (by linarith [hp₁.1]) (by linarith [hp₁.2])))
    (lt_min (by linarith [hp₂.1]) (by linarith [hp₂.2]))
  obtain ⟨r, hr, hrR, hrR₁, hrR₂, hrδ⟩ := exists_radius₃ hR hR₁ hR₂ hδ0
  have g1 := min_le_left (min (min (f p - a) (b - f p)) (min (f₁ p₁ - a₁) (b₁ - f₁ p₁)))
    (min (f₂ p₂ - a₂) (b₂ - f₂ p₂))
  have g2 := min_le_right (min (min (f p - a) (b - f p)) (min (f₁ p₁ - a₁) (b₁ - f₁ p₁)))
    (min (f₂ p₂ - a₂) (b₂ - f₂ p₂))
  have g3 := min_le_left (min (f p - a) (b - f p)) (min (f₁ p₁ - a₁) (b₁ - f₁ p₁))
  have g4 := min_le_right (min (f p - a) (b - f p)) (min (f₁ p₁ - a₁) (b₁ - f₁ p₁))
  have g5 := min_le_left (f p - a) (b - f p)
  have g6 := min_le_right (f p - a) (b - f p)
  have g7 := min_le_left (f₁ p₁ - a₁) (b₁ - f₁ p₁)
  have g8 := min_le_right (f₁ p₁ - a₁) (b₁ - f₁ p₁)
  have g9 := min_le_left (f₂ p₂ - a₂) (b₂ - f₂ p₂)
  have g10 := min_le_right (f₂ p₂ - a₂) (b₂ - f₂ p₂)
  obtain ⟨D, hk, hrD, hrm, ha, hb, ι, hι, hιi, hrc, hra, hinv, harc, s, hs, htype⟩ :=
    hP r hr hrR (by linarith) (by linarith)
  obtain ⟨D₁, hk₁, hrD₁, hrm₁, ha₁, hb₁, ι₁, hι₁, hιi₁, hrc₁, hra₁, hinv₁, harc₁, s₁, hs₁,
    htype₁⟩ := hP₁ r hr hrR₁ (by linarith) (by linarith)
  obtain ⟨D₂, hk₂, hrD₂, hrm₂, ha₂, hb₂, ι₂, hι₂, hιi₂, hrc₂, hra₂, hinv₂, harc₂, s₂, hs₂,
    htype₂⟩ := hP₂ r hr hrR₂ (by linarith) (by linarith)
  have hne : s₁ ≠ s₂ := by
    intro h12
    rw [h12] at htype₁
    obtain ⟨e, he⟩ := exists_slabDiffeo_of_sameType hdim₁ hdim₂ hf₁ hf₂ hab₁ hab₂ hreg₁ hreg₂ D₁
      D₂ hk₁ hk₂ (hrD₂.trans hrD₁.symm) hrm₁ hrm₂ ha₁ hb₁ ha₂ hb₂ hι₁ hι₂ hιi₁ hιi₂ hrc₁ hrc₂
      hra₁ hra₂ hinv₁ hinv₂ harc₁ harc₂ hs₂ htype₁ htype₂
    exact hup₁ (isPreconnected_upper_of_diffeo hdim₁ hdim₂ hf₁ hf₂ hab₁ hab₂ hreg₁ hreg₂ e
      (fun x => (he x).2) hup₂)
  have hcase : s = s₁ ∨ s = s₂ := by
    rcases sq_eq_one_cases hs with rfl | rfl <;> rcases sq_eq_one_cases hs₁ with rfl | rfl <;>
      rcases sq_eq_one_cases hs₂ with rfl | rfl <;>
      first | exact Or.inl rfl | exact Or.inr rfl | exact absurd rfl hne
  rcases hcase with h1 | h2
  · left
    rw [← h1] at htype₁
    exact exists_slabDiffeo_of_sameType hdim hdim₁ hf hf₁ hab hab₁ hreg hreg₁ D D₁ hk hk₁
      (hrD₁.trans hrD.symm) hrm hrm₁ ha hb ha₁ hb₁ hι hι₁ hιi hιi₁ hrc hrc₁ hra hra₁ hinv hinv₁
      harc harc₁ hs htype htype₁
  · right
    rw [← h2] at htype₂
    exact exists_slabDiffeo_of_sameType hdim hdim₂ hf hf₂ hab hab₂ hreg hreg₂ D D₂ hk hk₂
      (hrD₂.trans hrD.symm) hrm hrm₂ ha hb ha₂ hb₂ hι hι₂ hιi hιi₂ hrc hrc₂ hra hra₂ hinv hinv₂
      harc harc₂ hs htype htype₂

theorem oneSaddleSlab_connectedLower_cases
    {E H : Type} {N : Type uN} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] [TopologicalSpace N] [ChartedSpace H N] [T2Space N]
    (I : ModelWithCorners ℝ E H) [I.Boundaryless] [IsManifold I ∞ N]
    (hdim : Module.finrank ℝ E = 2) {f : N → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ}
    (hab : a < b) (hreg : ∀ x, f x = a ∨ f x = b → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0) {p : N}
    (hp : f p ∈ Ioo a b) (hnd : IsNondegenerateCriticalPointAt I f p)
    (hidx : sigNeg (chartHessianAt (fun y => f ((extChartAt I p).symm y))
      (extChartAt I p p)) = 1)
    (huniq : ∀ x, f x ∈ Icc a b → IsCriticalPointAt I f x → x = p)
    (hcpt : IsCompact (f ⁻¹' Icc a b)) (hconn : IsConnected (f ⁻¹' Icc a b))
    (hlow : IsPreconnected (f ⁻¹' {a})) :
    letI := (slabAtlas hdim hf hab hreg).toChartedSpace
    letI := (slabAtlas Complex.finrank_real_complex contMDiff_negPantsHeight
      (show (-1 : ℝ) < 0 by norm_num) negPantsHeight_regular_endpoints).toChartedSpace
    letI := (slabAtlas (show Module.finrank ℝ (ℝ × ℝ) = 2 by simp) contMDiff_mobiusHeight
      (show (0 : ℝ) < 2 by norm_num) mobiusHeight_regular_endpoints).toChartedSpace
    (∃ e : slabSet f a b ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ slabSet negPantsHeight (-1) 0,
      ∀ x : slabSet f a b,
        (f x = a ↔ negPantsHeight (e x) = -1) ∧ (f x = b ↔ negPantsHeight (e x) = 0)) ∨
    (∃ e : slabSet f a b ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ slabSet mobiusHeight 0 2,
      ∀ x : slabSet f a b,
        (f x = a ↔ mobiusHeight (e x) = 0) ∧ (f x = b ↔ mobiusHeight (e x) = 2)) := by
  have hconn' := hconn.isPreconnected
  have hp₁ : negPantsHeight 0 ∈ Ioo (-1 : ℝ) 0 := by
    unfold negPantsHeight
    rw [pantsHeight_zero]
    constructor <;> norm_num
  have hp₂ : mobiusHeight mobiusSaddle ∈ Ioo (0 : ℝ) 2 := by
    change mobiusHeightLift ((0 : ℝ), (0 : ℝ)) ∈ Ioo (0 : ℝ) 2
    simp only [mobiusHeightLift, mul_zero, Real.cos_zero]
    constructor <;> norm_num
  exact oneSaddleSlab_connectedLower_cases_of_models hdim hf hab hreg hp hnd hidx huniq hcpt hlow
    Complex.finrank_real_complex contMDiff_negPantsHeight (show (-1 : ℝ) < 0 by norm_num)
    negPantsHeight_regular_endpoints hp₁ isNondegenerateCriticalPointAt_negPantsHeight_zero
    sigNeg_chartHessianAt_negPantsHeight_zero
    (fun z hz hc => (isCriticalPointAt_negPantsHeight_iff hz).mp hc)
    isCompact_negPantsHeight_preimage_Icc isPreconnected_negPantsHeight_neg_one
    not_isPreconnected_negPantsHeight_zero (show Module.finrank ℝ (ℝ × ℝ) = 2 by simp)
    contMDiff_mobiusHeight (show (0 : ℝ) < 2 by norm_num) mobiusHeight_regular_endpoints hp₂
    isNondegenerateCriticalPointAt_mobiusHeight_saddle sigNeg_chartHessianAt_mobiusHeight_saddle
    (fun x hx hc => (isCriticalPointAt_mobiusHeight_iff hx).mp hc)
    isCompact_mobiusHeight_preimage_Icc isPreconnected_mobiusHeight_zero
    isPreconnected_mobiusHeight_two

end GC.Seifert
