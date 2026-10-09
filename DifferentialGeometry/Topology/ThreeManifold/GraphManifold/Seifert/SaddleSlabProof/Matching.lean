import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.SaddleSlabProof.Inverse
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.SaddleSlabProof.CircleArc

/-!
# Matching the lower levels of two one-saddle strips

Lane RG03c. `mfderiv_arc_ne_zero`: the attaching arcs `t ↦ arc D σ t` are immersed, being a
flow diffeomorphism after a chart after the curve `footPt`. In the setting of
`OneSaddleSlabUniqueness` the lower level `f ⁻¹' {a}` has exactly two components, the ones of
`arc D 1 0` and `arc D (-1) 0`; on each we read the arcs in a circle parametrisation and match
them by `exists_addCircle_diffeo_arc`. This gives `exists_levelMatching`: maps `h`, `h'` between
the lower levels, inverse to each other, with `h (arc D σ t) = arc D' σ t` for `t² ≤ 2 ε`, and
with `h ∘ π_a` smooth within the slab at the points of `lowDomain D`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Topology DifferentialGeometry.Topology.Morse
open DifferentialGeometry.Topology.Morse.CellAttachment (morseNorm morseNormalForm)

namespace GC.Seifert.SaddleSlabProof

theorem injective_mfderiv_of_leftInverse {E F H G X Y : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
    [TopologicalSpace G] {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
    [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace Y] [ChartedSpace G Y]
    {g : X → Y} {l : Y → X} {x : X} (hg : MDifferentiableAt I J g x)
    (hl : MDifferentiableAt J I l (g x)) (hlg : l ∘ g =ᶠ[𝓝 x] id) :
    Injective (mfderiv I J g x) := by
  have h1 := mfderiv_comp x hl hg
  rw [hlg.mfderiv_eq, mfderiv_id] at h1
  intro v w hvw
  have h2 := congrArg (fun L => L v) h1
  have h3 := congrArg (fun L => L w) h1
  simp only [ContinuousLinearMap.coe_comp, comp_apply, ContinuousLinearMap.coe_id', id_eq]
    at h2 h3
  exact (tangentSpaceCast I x (l (g x))).injective (h2.trans ((congrArg _ hvw).trans h3.symm))

theorem deriv_footPt_ne_zero {ε : ℝ} (hε : 0 < ε) (σ t : ℝ) : deriv (footPt ε σ) t ≠ 0 := by
  intro h0
  have hd : HasDerivAt (footPt ε σ) (deriv (footPt ε σ) t) t :=
    ((contDiff_footPt hε σ).differentiable (by simp) t).hasDerivAt
  have h1 := (hasDerivAt_pi.mp hd) 1
  have h2 : HasDerivAt (fun s => footPt ε σ s 1) 1 t := by
    simp only [footPt_one]
    exact hasDerivAt_id t
  have h3 := h1.unique h2
  rw [h0] at h3
  simp at h3

variable {H : Type} [TopologicalSpace H] {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ (MorseModel 2) H} [IsManifold I ∞ M] [T2Space M] [I.Boundaryless]
  {f : M → ℝ} {a b : ℝ} {p : M}

theorem mfderiv_arc_ne_zero (D : GradientLikeStrip I f a b {p}) (hrm : 8 * (ch D).r₀ ≤ rmD D)
    {σ t : ℝ} (hσ : σ ^ 2 = 1) (ht : t ^ 2 ≤ 3 * eps D) :
    mfderiv 𝓘(ℝ, ℝ) I (arc D σ) t 1 ≠ 0 := by
  have hε := eps_pos D
  have hball := footPt_mem_ball D hrm hσ ht
  set y := footPt (eps D) σ t with hy
  have hfoot : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, MorseModel 2) (footPt (eps D) σ) t :=
    ((contDiff_footPt hε σ).contMDiff.contMDiffAt).mdifferentiableAt (by simp)
  have hχ : MDifferentiableAt 𝓘(ℝ, MorseModel 2) I (ch D).χ y :=
    (ch D).mdifferentiableAt_chart hball
  have hχs : MDifferentiableAt I 𝓘(ℝ, MorseModel 2) (ch D).χ.symm ((ch D).χ y) :=
    (ch D).mdifferentiableAt_symm (mem_image_of_mem _ hball)
  have hfl : MDifferentiableAt I I (D.flow (f p - eps D - a)) ((ch D).χ y) :=
    (D.contMDiff_flow _).contMDiffAt.mdifferentiableAt (by simp)
  have hfl' : MDifferentiableAt I I (D.flow (-(f p - eps D - a)))
      (D.flow (f p - eps D - a) ((ch D).χ y)) :=
    (D.contMDiff_flow _).contMDiffAt.mdifferentiableAt (by simp)
  have hinjχ : Injective (mfderiv 𝓘(ℝ, MorseModel 2) I (ch D).χ y) :=
    injective_mfderiv_of_leftInverse hχ hχs (eventually_of_mem
      (Metric.isOpen_ball.mem_nhds hball) fun z hz => (ch D).χ.left_inv ((ch D).hball hz))
  have hinjfl : Injective (mfderiv I I (D.flow (f p - eps D - a)) ((ch D).χ y)) :=
    injective_mfderiv_of_leftInverse hfl hfl' (Eventually.of_forall fun z =>
      GradientLikeStrip.flow_neg_flow D z _)
  have hcomp : mfderiv 𝓘(ℝ, ℝ) I (arc D σ) t =
      (mfderiv I I (D.flow (f p - eps D - a)) ((ch D).χ y)).comp
        ((mfderiv 𝓘(ℝ, MorseModel 2) I (ch D).χ y).comp
          (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, MorseModel 2) (footPt (eps D) σ) t)) := by
    have h1 := mfderiv_comp t hχ hfoot
    have h2 := mfderiv_comp t hfl (hχ.comp t hfoot)
    exact h2.trans (congrArg (ContinuousLinearMap.comp _) h1)
  have hfd : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, MorseModel 2) (footPt (eps D) σ) t 1 ≠ 0 := by
    rw [mfderiv_eq_fderiv]
    change fderiv ℝ (footPt (eps D) σ) t 1 ≠ 0
    rw [fderiv_apply_one_eq_deriv]
    exact deriv_footPt_ne_zero hε σ t
  rw [hcomp]
  intro h0
  apply hfd
  apply hinjχ
  rw [map_zero]
  apply hinjfl
  rw [map_zero]
  exact h0

theorem sq_lt_of_mem_Ioo {e t : ℝ} (he : 0 ≤ e) (ht : t ∈ Ioo (-Real.sqrt e) (Real.sqrt e)) :
    t ^ 2 < e := by
  have h := sq_lt_sq' ht.1 ht.2
  rwa [Real.sq_sqrt he] at h

theorem arc_injOn (D : GradientLikeStrip I f a b {p}) (hrm : 8 * (ch D).r₀ ≤ rmD D) {σ : ℝ}
    (hσ : σ ^ 2 = 1) {t t' : ℝ} (ht : t ^ 2 ≤ 3 * eps D) (ht' : t' ^ 2 ≤ 3 * eps D)
    (h : arc D σ t = arc D σ t') : t = t' := by
  unfold arc at h
  have h1 := GradientLikeStrip.flow_injective D _ h
  have h2 := (ch D).χ.injOn ((ch D).hball (footPt_mem_ball D hrm hσ ht))
    ((ch D).hball (footPt_mem_ball D hrm hσ ht')) h1
  have h3 := congrFun h2 1
  simpa [footPt_one] using h3

theorem continuousOn_arc (D : GradientLikeStrip I f a b {p}) (hrm : 8 * (ch D).r₀ ≤ rmD D)
    {σ : ℝ} (hσ : σ ^ 2 = 1) :
    ContinuousOn (arc D σ) (Icc (-Real.sqrt (3 * eps D)) (Real.sqrt (3 * eps D))) := by
  intro t ht
  have ht2 : t ^ 2 ≤ 3 * eps D := by
    have h := abs_le.mpr ⟨ht.1, ht.2⟩
    have := sq_le_sq' (abs_le.mp h).1 (abs_le.mp h).2
    rwa [Real.sq_sqrt (by linarith [eps_pos D])] at this
  exact (contMDiffAt_arc D hrm hσ ht2).continuousAt.continuousWithinAt

theorem exists_circle (D : GradientLikeStrip I f a b {p}) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hk : (ch D).k = 1) (hrm : 8 * (ch D).r₀ ≤ rmD D) (ha : a < f p - 2 * eps D)
    (hb : f p + 2 * eps D < b) (hreg : ∀ x, f x = a ∨ f x = b → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0)
    (hcpt : IsCompact (f ⁻¹' Icc a b)) {σ : ℝ} (hσ : σ ^ 2 = 1) :
    ∃ ι : AddCircle (1 : ℝ) → M, ContMDiff 𝓘(ℝ, ℝ) I ∞ ι ∧ Injective ι ∧
      range ι = connectedComponentIn (f ⁻¹' {a}) (arc D σ 0) ∧
      (∀ x ∈ range ι, ContMDiffWithinAt I 𝓘(ℝ, ℝ) ∞ (invFun ι) (range ι) x) ∧
      (∀ t, t ^ 2 ≤ 3 * eps D → arc D σ t ∈ range ι) ∧
      (∀ t ∈ Ioo (-Real.sqrt (3 * eps D)) (Real.sqrt (3 * eps D)),
        ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun s => invFun ι (arc D σ s)) t) ∧
      InjOn (fun s => invFun ι (arc D σ s)) (Ioo (-Real.sqrt (3 * eps D)) (Real.sqrt (3 * eps D)))
      ∧ ∀ t ∈ Ioo (-Real.sqrt (3 * eps D)) (Real.sqrt (3 * eps D)),
        mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s => invFun ι (arc D σ s)) t ≠ 0 := by
  have hε := eps_pos D
  have hab : a < b := by linarith
  have h0 : (0 : ℝ) ^ 2 ≤ 3 * eps D := by linarith
  obtain ⟨ι, hι, hιinj, hrange, hinv⟩ := exists_levelCircle (Module.finrank_fin_fun ℝ) hf hab
    hreg hcpt (f_arc D hf hk hrm (by linarith) (by linarith) hσ h0)
  set T := Real.sqrt (3 * eps D) with hT
  have hmemI : ∀ t, t ^ 2 ≤ 3 * eps D → t ∈ Icc (-T) T := fun t ht =>
    abs_le.mp (Real.abs_le_sqrt ht)
  have hsqI : ∀ t ∈ Icc (-T) T, t ^ 2 ≤ 3 * eps D := fun t ht => by
    have := sq_le_sq' ht.1 ht.2
    rwa [hT, Real.sq_sqrt (by linarith)] at this
  have harcmem : ∀ t, t ^ 2 ≤ 3 * eps D → arc D σ t ∈ range ι := by
    intro t ht
    rw [hrange]
    have hpre : IsPreconnected (arc D σ '' Icc (-T) T) :=
      isPreconnected_Icc.image _ (continuousOn_arc D hrm hσ)
    refine hpre.subset_connectedComponentIn ⟨0, hmemI 0 h0, rfl⟩ ?_ ⟨t, hmemI t ht, rfl⟩
    rintro _ ⟨s, hs, rfl⟩
    exact f_arc D hf hk hrm (by linarith) (by linarith) hσ (hsqI s hs)
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
  refine ⟨ι, hι, hιinj, hrange, hinv, harcmem, hsm, ?_, ?_⟩
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

omit [T2Space M] in
theorem exists_open_inter_eq_component (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hab : a < b)
    (hreg : ∀ x, f x = a ∨ f x = b → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0) {y : M} (hy : f y = a) :
    ∃ V : Set M, IsOpen V ∧ V ∩ f ⁻¹' {a} = connectedComponentIn (f ⁻¹' {a}) y := by
  have := locallyConnectedSpace_level (Module.finrank_fin_fun ℝ) hf hab hreg
  obtain ⟨V, hV, hVeq⟩ := isOpen_induced_iff.mp
    (isOpen_connectedComponent (x := (⟨y, hy⟩ : f ⁻¹' {a})))
  refine ⟨V, hV, ?_⟩
  rw [connectedComponentIn_eq_image (show y ∈ f ⁻¹' {a} from hy)]
  ext x
  constructor
  · rintro ⟨hxV, hxa⟩
    refine ⟨⟨x, hxa⟩, ?_, rfl⟩
    rw [← hVeq]
    exact hxV
  · rintro ⟨z, hz, rfl⟩
    rw [← hVeq] at hz
    exact ⟨hz, z.2⟩

theorem component_cases (D : GradientLikeStrip I f a b {p}) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hk : (ch D).k = 1) (hrm : 8 * (ch D).r₀ ≤ rmD D) (ha : a < f p - 2 * eps D)
    (hb : f p + 2 * eps D < b) (hreg : ∀ x, f x = a ∨ f x = b → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0)
    (hcpt : IsCompact (f ⁻¹' Icc a b)) (hconn : IsPreconnected (f ⁻¹' Icc a b))
    (hlow : ¬ IsPreconnected (f ⁻¹' {a})) :
    (∀ y, f y = a → y ∈ connectedComponentIn (f ⁻¹' {a}) (arc D 1 0) ∨
      y ∈ connectedComponentIn (f ⁻¹' {a}) (arc D (-1) 0)) ∧
    Disjoint (connectedComponentIn (f ⁻¹' {a}) (arc D 1 0))
      (connectedComponentIn (f ⁻¹' {a}) (arc D (-1) 0)) := by
  have hε := eps_pos D
  have hcover : ∀ y, f y = a → y ∈ connectedComponentIn (f ⁻¹' {a}) (arc D 1 0) ∨
      y ∈ connectedComponentIn (f ⁻¹' {a}) (arc D (-1) 0) := by
    intro y hy
    rcases connectedComponentIn_eq_arc D hf hk hrm (by linarith) (by linarith) hreg hcpt hconn hy
      with h | h
    · left
      rw [← connectedComponentIn_eq h]
      exact mem_connectedComponentIn (show y ∈ f ⁻¹' {a} from hy)
    · right
      rw [← connectedComponentIn_eq h]
      exact mem_connectedComponentIn (show y ∈ f ⁻¹' {a} from hy)
  refine ⟨hcover, Set.disjoint_left.mpr fun z hz1 hz2 => hlow ?_⟩
  have heq : connectedComponentIn (f ⁻¹' {a}) (arc D 1 0) =
      connectedComponentIn (f ⁻¹' {a}) (arc D (-1) 0) :=
    (connectedComponentIn_eq hz1).trans (connectedComponentIn_eq hz2).symm
  have hall : f ⁻¹' {a} = connectedComponentIn (f ⁻¹' {a}) (arc D 1 0) := by
    refine Subset.antisymm (fun y hy => ?_) (connectedComponentIn_subset _ _)
    rcases hcover y hy with h | h
    · exact h
    · rw [heq]
      exact h
  rw [hall]
  exact isPreconnected_connectedComponentIn

theorem contMDiffWithinAt_branch (D : GradientLikeStrip I f a b {p})
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hrm : 8 * (ch D).r₀ ≤ rmD D) (hab : a < b)
    (hreg : ∀ x, f x = a ∨ f x = b → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0) {H'' : Type}
    [TopologicalSpace H''] {M'' : Type*} [TopologicalSpace M''] [ChartedSpace H'' M'']
    {I'' : ModelWithCorners ℝ (MorseModel 2) H''} {ι : AddCircle (1 : ℝ) → M}
    {κ : AddCircle (1 : ℝ) → M''} (hκ : ContMDiff 𝓘(ℝ, ℝ) I'' ∞ κ)
    (k : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)) (AddCircle (1 : ℝ)) ∞)
    (hinv : ∀ x ∈ range ι, ContMDiffWithinAt I 𝓘(ℝ, ℝ) ∞ (invFun ι) (range ι) x) {y₀ : M}
    (hy₀ : f y₀ = a) (hrange : range ι = connectedComponentIn (f ⁻¹' {a}) y₀) {F : M → M''}
    (hF : ∀ z ∈ range ι, F z = κ (k (invFun ι z))) {x : M} (hx : x ∈ lowDomain D)
    (hz : D.π a x ∈ range ι) :
    ContMDiffWithinAt I I'' ∞ (fun y => F (D.π a y)) (f ⁻¹' Icc a b) x := by
  obtain ⟨V, hV, hVeq⟩ := exists_open_inter_eq_component hf hab hreg hy₀
  rw [← hrange] at hVeq
  set W := lowDomain D ∩ D.π a ⁻¹' V with hW
  have hWo : IsOpen W := (isOpen_lowDomain D hf.continuous hrm).inter
    (hV.preimage (D.continuous_π hf a))
  have hxW : x ∈ W := ⟨hx, (hVeq ▸ hz : D.π a x ∈ V ∩ f ⁻¹' {a}).1⟩
  have hmaps : MapsTo (D.π a) (f ⁻¹' Icc a b ∩ W) (range ι) := fun y hy => by
    rw [← hVeq]
    exact ⟨hy.2.2, f_π_of_lowDomain D hf hy.1 hy.2.1⟩
  rw [← contMDiffWithinAt_inter' (inter_mem_nhdsWithin _ (hWo.mem_nhds hxW) |>
    Filter.mem_of_superset <| inter_subset_right)]
  have hc := (hκ.comp k.contMDiff).contMDiffAt.comp_contMDiffWithinAt x
    ((hinv (D.π a x) hz).comp x ((D.contMDiff_π hf a).contMDiffAt.contMDiffWithinAt) hmaps)
  exact hc.congr (fun y hy => hF _ (hmaps hy)) (hF _ hz)

variable {H' : Type} [TopologicalSpace H'] {M' : Type*} [TopologicalSpace M']
  [ChartedSpace H' M'] {I' : ModelWithCorners ℝ (MorseModel 2) H'} [IsManifold I' ∞ M']
  [T2Space M'] [I'.Boundaryless] {f' : M' → ℝ} {a' b' : ℝ} {p' : M'}

open Classical in
theorem exists_levelMatching (D : GradientLikeStrip I f a b {p})
    (D' : GradientLikeStrip I' f' a' b' {p'}) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hf' : ContMDiff I' 𝓘(ℝ, ℝ) ∞ f')
    (hk : (ch D).k = 1) (hk' : (ch D').k = 1) (hr : (ch D').r₀ = (ch D).r₀)
    (hrm : 8 * (ch D).r₀ ≤ rmD D) (hrm' : 8 * (ch D').r₀ ≤ rmD D')
    (ha : a < f p - 2 * eps D) (hb : f p + 2 * eps D < b)
    (ha' : a' < f' p' - 2 * eps D) (hb' : f' p' + 2 * eps D < b')
    (hreg : ∀ x, f x = a ∨ f x = b → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0)
    (hreg' : ∀ x, f' x = a' ∨ f' x = b' → mfderiv I' 𝓘(ℝ, ℝ) f' x ≠ 0)
    (hcpt : IsCompact (f ⁻¹' Icc a b)) (hcpt' : IsCompact (f' ⁻¹' Icc a' b'))
    (hconn : IsPreconnected (f ⁻¹' Icc a b)) (hconn' : IsPreconnected (f' ⁻¹' Icc a' b'))
    (hlow : ¬ IsPreconnected (f ⁻¹' {a})) (hlow' : ¬ IsPreconnected (f' ⁻¹' {a'})) :
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
  have ha'' : a' < f' p' - 2 * eps D' := by rw [hε']; exact ha'
  have hb'' : f' p' + 2 * eps D' < b' := by rw [hε']; exact hb'
  have h1 : (1 : ℝ) ^ 2 = 1 := by norm_num
  have h2 : (-1 : ℝ) ^ 2 = 1 := by norm_num
  obtain ⟨ι₁, hι₁, hι₁i, hr₁, hinv₁, harc₁, hsm₁, hinj₁, himm₁⟩ :=
    exists_circle D hf hk hrm ha hb hreg hcpt h1
  obtain ⟨ι₂, hι₂, hι₂i, hr₂, hinv₂, harc₂, hsm₂, hinj₂, himm₂⟩ :=
    exists_circle D hf hk hrm ha hb hreg hcpt h2
  obtain ⟨κ₁, hκ₁, hκ₁i, hs₁, hinvκ₁, harcκ₁, hsmκ₁, hinjκ₁, himmκ₁⟩ :=
    exists_circle D' hf' hk' hrm' ha'' hb'' hreg' hcpt' h1
  obtain ⟨κ₂, hκ₂, hκ₂i, hs₂, hinvκ₂, harcκ₂, hsmκ₂, hinjκ₂, himmκ₂⟩ :=
    exists_circle D' hf' hk' hrm' ha'' hb'' hreg' hcpt' h2
  obtain ⟨hcov, hdisj⟩ := component_cases D hf hk hrm ha hb hreg hcpt hconn hlow
  obtain ⟨hcov', hdisj'⟩ := component_cases D' hf' hk' hrm' ha'' hb'' hreg' hcpt' hconn' hlow'
  rw [← hr₁, ← hr₂] at hcov hdisj
  rw [← hs₁, ← hs₂] at hcov' hdisj'
  rw [hε'] at harcκ₁ harcκ₂ hsmκ₁ hsmκ₂ hinjκ₁ hinjκ₂ himmκ₁ himmκ₂
  set T₁ := Real.sqrt (2 * eps D) with hT₁
  set T := Real.sqrt (3 * eps D) with hT
  have hT₁0 : 0 ≤ T₁ := Real.sqrt_nonneg _
  have hT₁T : T₁ < T := Real.sqrt_lt_sqrt (by linarith) (by linarith)
  obtain ⟨k₁, hk₁⟩ := exists_addCircle_diffeo_arc hT₁0 hT₁T hsm₁ hsmκ₁ hinj₁ hinjκ₁ himm₁ himmκ₁
  obtain ⟨k₂, hk₂⟩ := exists_addCircle_diffeo_arc hT₁0 hT₁T hsm₂ hsmκ₂ hinj₂ hinjκ₂ himm₂ himmκ₂
  have hIcc : ∀ t, t ^ 2 ≤ 2 * eps D → t ∈ Icc (-T₁) T₁ := fun t ht =>
    abs_le.mp (Real.abs_le_sqrt ht)
  have h23 : ∀ t, t ^ 2 ≤ 2 * eps D → t ^ 2 ≤ 3 * eps D := fun t ht => by linarith
  have hlevel : ∀ {ι : AddCircle (1 : ℝ) → M} {σ : ℝ}, σ ^ 2 = 1 →
      range ι = connectedComponentIn (f ⁻¹' {a}) (arc D σ 0) → ∀ z ∈ range ι, f z = a := by
    intro ι σ _ hr z hz
    rw [hr] at hz
    exact (connectedComponentIn_subset (f ⁻¹' {a}) (arc D σ 0) hz : z ∈ f ⁻¹' {a})
  have hlevel' : ∀ {κ : AddCircle (1 : ℝ) → M'} {σ : ℝ}, σ ^ 2 = 1 →
      range κ = connectedComponentIn (f' ⁻¹' {a'}) (arc D' σ 0) → ∀ z ∈ range κ, f' z = a' := by
    intro κ σ _ hr z hz
    rw [hr] at hz
    exact (connectedComponentIn_subset (f' ⁻¹' {a'}) (arc D' σ 0) hz : z ∈ f' ⁻¹' {a'})
  set h : M → M' := fun x => if x ∈ range ι₁ then κ₁ (k₁ (invFun ι₁ x))
    else κ₂ (k₂ (invFun ι₂ x)) with hhdef
  set h' : M' → M := fun x => if x ∈ range κ₁ then ι₁ (k₁.symm (invFun κ₁ x))
    else ι₂ (k₂.symm (invFun κ₂ x)) with hh'def
  have hh1 : ∀ z ∈ range ι₁, h z = κ₁ (k₁ (invFun ι₁ z)) := fun z hz => by
    simp only [hhdef, hz, ite_true]
  have hh2 : ∀ z ∈ range ι₂, h z = κ₂ (k₂ (invFun ι₂ z)) := fun z hz => by
    simp only [hhdef, Set.disjoint_right.mp hdisj hz, ite_false]
  have hh'1 : ∀ z ∈ range κ₁, h' z = ι₁ (k₁.symm (invFun κ₁ z)) := fun z hz => by
    simp only [hh'def, hz, ite_true]
  have hh'2 : ∀ z ∈ range κ₂, h' z = ι₂ (k₂.symm (invFun κ₂ z)) := fun z hz => by
    simp only [hh'def, Set.disjoint_right.mp hdisj' hz, ite_false]
  have hab : a < b := by linarith
  have hab' : a' < b' := by linarith
  have hf₁ : f (arc D 1 0) = a := hlevel h1 hr₁ _ (harc₁ 0 (by linarith))
  have hf₂ : f (arc D (-1) 0) = a := hlevel h2 hr₂ _ (harc₂ 0 (by linarith))
  have hf₁' : f' (arc D' 1 0) = a' := hlevel' h1 hs₁ _ (harcκ₁ 0 (by linarith))
  have hf₂' : f' (arc D' (-1) 0) = a' := hlevel' h2 hs₂ _ (harcκ₂ 0 (by linarith))
  refine ⟨h, h', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    rcases hcov z hz with hz1 | hz2
    · rw [hh1 z hz1]
      exact hlevel' h1 hs₁ _ (mem_range_self _)
    · rw [hh2 z hz2]
      exact hlevel' h2 hs₂ _ (mem_range_self _)
  · intro z hz
    rcases hcov' z hz with hz1 | hz2
    · rw [hh'1 z hz1]
      exact hlevel h1 hr₁ _ (mem_range_self _)
    · rw [hh'2 z hz2]
      exact hlevel h2 hr₂ _ (mem_range_self _)
  · intro z hz
    rcases hcov z hz with hz1 | hz2
    · rw [hh1 z hz1, hh'1 _ (mem_range_self _), leftInverse_invFun hκ₁i,
        Diffeomorph.symm_apply_apply, invFun_eq hz1]
    · rw [hh2 z hz2, hh'2 _ (mem_range_self _), leftInverse_invFun hκ₂i,
        Diffeomorph.symm_apply_apply, invFun_eq hz2]
  · intro z hz
    rcases hcov' z hz with hz1 | hz2
    · rw [hh'1 z hz1, hh1 _ (mem_range_self _), leftInverse_invFun hι₁i,
        Diffeomorph.apply_symm_apply, invFun_eq hz1]
    · rw [hh'2 z hz2, hh2 _ (mem_range_self _), leftInverse_invFun hι₂i,
        Diffeomorph.apply_symm_apply, invFun_eq hz2]
  · intro σ t hσ ht
    rcases sq_eq_one_cases hσ with rfl | rfl
    · have hk := hk₁ t (hIcc t ht)
      rw [hh1 _ (harc₁ t (h23 t ht)), hk, invFun_eq (harcκ₁ t (h23 t ht))]
    · have hk := hk₂ t (hIcc t ht)
      rw [hh2 _ (harc₂ t (h23 t ht)), hk, invFun_eq (harcκ₂ t (h23 t ht))]
  · intro σ t hσ ht
    rcases sq_eq_one_cases hσ with rfl | rfl
    · have hk := hk₁ t (hIcc t ht)
      rw [hh'1 _ (harcκ₁ t (h23 t ht)), ← hk, Diffeomorph.symm_apply_apply,
        invFun_eq (harc₁ t (h23 t ht))]
    · have hk := hk₂ t (hIcc t ht)
      rw [hh'2 _ (harcκ₂ t (h23 t ht)), ← hk, Diffeomorph.symm_apply_apply,
        invFun_eq (harc₂ t (h23 t ht))]
  · intro x hx hxS
    rcases hcov _ (f_π_of_lowDomain D hf hxS hx) with hz1 | hz2
    · exact contMDiffWithinAt_branch D hf hrm hab hreg hκ₁ k₁ hinv₁ hf₁ hr₁ hh1 hx hz1
    · exact contMDiffWithinAt_branch D hf hrm hab hreg hκ₂ k₂ hinv₂ hf₂ hr₂ hh2 hx hz2
  · intro x hx hxS
    rcases hcov' _ (f_π_of_lowDomain D' hf' hxS hx) with hz1 | hz2
    · exact contMDiffWithinAt_branch D' hf' hrm' hab' hreg' hι₁ k₁.symm hinvκ₁ hf₁' hs₁ hh'1
        hx hz1
    · exact contMDiffWithinAt_branch D' hf' hrm' hab' hreg' hι₂ k₂.symm hinvκ₂ hf₂' hs₂ hh'2
        hx hz2

end GC.Seifert.SaddleSlabProof
