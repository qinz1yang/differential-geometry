import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.PullbackFieldConstruction
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Bundle
open scoped Manifold ContDiff

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
variable {N : Type u} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]

section CodRestrict

omit [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] in
omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem contMDiffAt_codRestr {N' : Type u} [TopologicalSpace N'] [ChartedSpace H N']
    {V' : TopologicalSpace.Opens N'} {f : M → N'}
    (hmem : ∀ y, f y ∈ V') {x : M}
    (hf : ContMDiffAt I I (∞ : WithTop ℕ∞) f x) :
    ContMDiffAt I I (∞ : WithTop ℕ∞) (fun y => (⟨f y, hmem y⟩ : V')) x := by
  rw [contMDiffAt_iff] at hf ⊢
  obtain ⟨hcont, hdiff⟩ := hf
  refine ⟨Topology.IsInducing.subtypeVal.continuousAt_iff.mpr
    (by simpa [Function.comp_def] using hcont), ?_⟩
  convert hdiff using 2

end CodRestrict

section OpensDiffeo

open TopologicalSpace Topology

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
    [IsManifold I ∞ N] in
theorem image_opens_isOpen (Φ : PartialDiffeomorph I I M N (∞ : WithTop ℕ∞))
    {V : Opens M} (hV : (V : Set M) ⊆ Φ.source) :
    IsOpen ((Φ : M → N) '' (V : Set M)) := by
  have himg : (Φ : M → N) '' (V : Set M)
      = Φ.target ∩ ((Φ.symm : N → M) ⁻¹' (V : Set M)) := by
    ext y
    constructor
    · rintro ⟨v, hv, rfl⟩
      refine ⟨Φ.map_source' (hV hv), ?_⟩
      have hl : (Φ.symm : N → M) ((Φ : M → N) v) = v := Φ.left_inv' (hV hv)
      change (Φ.symm : N → M) ((Φ : M → N) v) ∈ (V : Set M)
      rw [hl]
      exact hv
    · rintro ⟨hy1, hy2⟩
      exact ⟨(Φ.symm : N → M) y, hy2, Φ.right_inv' hy1⟩
  rw [himg]
  exact Φ.symm.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage Φ.open_target V.2

noncomputable def PartialDiffeomorph.toOpensDiffeo
    (Φ : PartialDiffeomorph I I M N (∞ : WithTop ℕ∞))
    {V : Opens M} (hV : (V : Set M) ⊆ Φ.source) :
    Diffeomorph I I V (⟨(Φ : M → N) '' (V : Set M), image_opens_isOpen Φ hV⟩ : Opens N)
      (∞ : WithTop ℕ∞) where
  toFun p := ⟨(Φ : M → N) p.1, ⟨p.1, p.2, rfl⟩⟩
  invFun q := ⟨(Φ.symm : N → M) q.1, by
    obtain ⟨v, hv, hveq⟩ := q.2
    rw [← hveq]
    have hl : (Φ.symm : N → M) ((Φ : M → N) v) = v := Φ.left_inv' (hV hv)
    change (Φ.symm : N → M) ((Φ : M → N) v) ∈ V
    rw [hl]
    exact hv⟩
  left_inv p := by
    apply Subtype.ext
    exact Φ.left_inv' (hV p.2)
  right_inv q := by
    apply Subtype.ext
    obtain ⟨v, hv, hveq⟩ := q.2
    have hyt : (q : N) ∈ Φ.target := by
      rw [← hveq]; exact Φ.map_source' (hV hv)
    exact Φ.right_inv' hyt
  contMDiff_toFun := by
    intro p
    have hbase : ContMDiffAt I I (∞ : WithTop ℕ∞) (fun p : V => (Φ : M → N) p.1) p := by
      rw [contMDiffAt_subtype_iff]
      exact Φ.contMDiffOn_toFun.contMDiffAt (Φ.open_source.mem_nhds (hV p.2))
    exact contMDiffAt_codRestr
      (V' := (⟨(Φ : M → N) '' (V : Set M), image_opens_isOpen Φ hV⟩ : Opens N))
      (f := fun p : V => (Φ : M → N) p.1)
      (fun y => ⟨y.1, y.2, rfl⟩) hbase
  contMDiff_invFun := by
    intro q
    have hmem : ∀ y : (⟨(Φ : M → N) '' (V : Set M), image_opens_isOpen Φ hV⟩ : Opens N),
        (Φ.symm : N → M) y.1 ∈ V := by
      intro y
      obtain ⟨v, hv, hveq⟩ := y.2
      rw [← hveq]
      have hl : (Φ.symm : N → M) ((Φ : M → N) v) = v := Φ.left_inv' (hV hv)
      change (Φ.symm : N → M) ((Φ : M → N) v) ∈ V
      rw [hl]
      exact hv
    have hbase : ContMDiffAt I I (∞ : WithTop ℕ∞)
        (fun y : (⟨(Φ : M → N) '' (V : Set M), image_opens_isOpen Φ hV⟩ : Opens N) =>
          (Φ.symm : N → M) y.1) q := by
      rw [contMDiffAt_subtype_iff]
      obtain ⟨v, hv, hveq⟩ := q.2
      have hqt : (q : N) ∈ Φ.target := by
        rw [← hveq]; exact Φ.map_source' (hV hv)
      exact Φ.symm.contMDiffOn_toFun.contMDiffAt (Φ.open_target.mem_nhds hqt)
    exact contMDiffAt_codRestr hmem hbase

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
    [IsManifold I ∞ N] in
theorem PartialDiffeomorph.opensDiffeo_mfderiv
    (Φ : PartialDiffeomorph I I M N (∞ : WithTop ℕ∞))
    {U : Opens M} (hU : (U : Set M) ⊆ Φ.source) (p : U) (v : TangentSpace I p) :
    mfderiv I I
        (PartialDiffeomorph.toOpensDiffeo Φ hU : U →
          (⟨(Φ : M → N) '' (U : Set M), image_opens_isOpen Φ hU⟩ : Opens N)) p v
      = mfderiv I I (Φ : M → N) (p : M) v := by
  let W : Opens N := ⟨(Φ : M → N) '' (U : Set M), image_opens_isOpen Φ hU⟩
  let F : Diffeomorph I I U W (∞ : WithTop ℕ∞) :=
    PartialDiffeomorph.toOpensDiffeo Φ hU
  have hFd : MDifferentiableAt I I (F : U → W) p :=
    F.contMDiff.contMDiffAt.mdifferentiableAt (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have hvalW : MDifferentiableAt I I (Subtype.val : W → N) (F p) :=
    ((contMDiff_subtype_val (I := I) (U := W)).contMDiffAt).mdifferentiableAt
      (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have hvalU : MDifferentiableAt I I (Subtype.val : U → M) p :=
    ((contMDiff_subtype_val (I := I) (U := U)).contMDiffAt).mdifferentiableAt
      (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have hΦd : MDifferentiableAt I I (Φ : M → N) (p : M) :=
    (Φ.contMDiffOn_toFun.contMDiffAt
      (Φ.open_source.mem_nhds (hU p.2))).mdifferentiableAt
      (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have h1 : mfderiv I I (fun y : U => ((F y : W) : N)) p
      = (mfderiv I I (Subtype.val : W → N) (F p)).comp
          (mfderiv I I (F : U → W) p) :=
    mfderiv_comp p hvalW hFd
  have h2 : mfderiv I I (fun y : U => (Φ : M → N) (y : M)) p
      = (mfderiv I I (Φ : M → N) (p : M)).comp
          (mfderiv I I (Subtype.val : U → M) p) :=
    mfderiv_comp p hΦd hvalU
  have happ := DFunLike.congr_fun (h1.symm.trans h2) v
  simpa only [F, ContinuousLinearMap.comp_apply,
    mfderiv_subtype_val (I := I) W (F p), mfderiv_subtype_val (I := I) U p] using happ

noncomputable def PartialDiffeomorph.opensMap
    (Φ : PartialDiffeomorph I I M N (∞ : WithTop ℕ∞))
    {U : Opens M} {V : Opens N} (_hU : (U : Set M) ⊆ Φ.source)
    (hUV : (Φ : M → N) '' (U : Set M) ⊆ (V : Set N)) : U → V :=
  fun x => ⟨(Φ : M → N) x, hUV ⟨x, x.2, rfl⟩⟩


omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
    [IsManifold I ∞ N] in
theorem PartialDiffeomorph.opensMap_isOpenEmb
    (Φ : PartialDiffeomorph I I M N (∞ : WithTop ℕ∞))
    {U : Opens M} {V : Opens N} (hU : (U : Set M) ⊆ Φ.source)
    (hUV : (Φ : M → N) '' (U : Set M) ⊆ (V : Set N)) :
    IsOpenEmbedding (PartialDiffeomorph.opensMap Φ hU hUV) := by
  let W : Opens N := ⟨(Φ : M → N) '' (U : Set M), image_opens_isOpen Φ hU⟩
  have hWV : W ≤ V := hUV
  let F : Diffeomorph I I U W (∞ : WithTop ℕ∞) :=
    PartialDiffeomorph.toOpensDiffeo Φ hU
  have hinc : IsOpenEmbedding (Opens.inclusion hWV : W → V) :=
    Opens.isOpenEmbedding_of_le hWV
  have hfun : PartialDiffeomorph.opensMap Φ hU hUV =
      (Opens.inclusion hWV : W → V) ∘ F := rfl
  rw [hfun]
  exact hinc.comp F.toHomeomorph.isOpenEmbedding


omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
    [IsManifold I ∞ N] in
theorem PartialDiffeomorph.opensMap_contMDiff
    (Φ : PartialDiffeomorph I I M N (∞ : WithTop ℕ∞))
    {U : Opens M} {V : Opens N} (hU : (U : Set M) ⊆ Φ.source)
    (hUV : (Φ : M → N) '' (U : Set M) ⊆ (V : Set N)) :
    ContMDiff I I ∞ (PartialDiffeomorph.opensMap Φ hU hUV) := by
  let W : Opens N := ⟨(Φ : M → N) '' (U : Set M), image_opens_isOpen Φ hU⟩
  have hWV : W ≤ V := hUV
  let F : Diffeomorph I I U W (∞ : WithTop ℕ∞) :=
    PartialDiffeomorph.toOpensDiffeo Φ hU
  have hfun : PartialDiffeomorph.opensMap Φ hU hUV =
      (Opens.inclusion hWV : W → V) ∘ F := rfl
  rw [hfun]
  exact (contMDiff_inclusion hWV).comp F.contMDiff

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
    [IsManifold I ∞ N] in
theorem PartialDiffeomorph.opensMap_mfderiv
    (Φ : PartialDiffeomorph I I M N (∞ : WithTop ℕ∞))
    {U : Opens M} {V : Opens N} (hU : (U : Set M) ⊆ Φ.source)
    (hUV : (Φ : M → N) '' (U : Set M) ⊆ (V : Set N))
    (p : U) (v : TangentSpace I p) :
    mfderiv I I (PartialDiffeomorph.opensMap Φ hU hUV) p v =
      mfderiv I I (Φ : M → N) (p : M) v := by
  let F : U → V := PartialDiffeomorph.opensMap Φ hU hUV
  have hFd : MDifferentiableAt I I F p :=
    ((PartialDiffeomorph.opensMap_contMDiff Φ hU hUV).contMDiffAt).mdifferentiableAt
      (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have hvalV : MDifferentiableAt I I (Subtype.val : V → N) (F p) :=
    ((contMDiff_subtype_val (I := I) (U := V)).contMDiffAt).mdifferentiableAt
      (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have hvalU : MDifferentiableAt I I (Subtype.val : U → M) p :=
    ((contMDiff_subtype_val (I := I) (U := U)).contMDiffAt).mdifferentiableAt
      (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have hΦd : MDifferentiableAt I I (Φ : M → N) (p : M) :=
    (Φ.contMDiffOn_toFun.contMDiffAt
      (Φ.open_source.mem_nhds (hU p.2))).mdifferentiableAt
      (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have h1 : mfderiv I I (fun y : U => ((F y : V) : N)) p =
      (mfderiv I I (Subtype.val : V → N) (F p)).comp (mfderiv I I F p) :=
    mfderiv_comp p hvalV hFd
  have h2 : mfderiv I I (fun y : U => (Φ : M → N) (y : M)) p =
      (mfderiv I I (Φ : M → N) (p : M)).comp
        (mfderiv I I (Subtype.val : U → M) p) :=
    mfderiv_comp p hΦd hvalU
  have happ := DFunLike.congr_fun (h1.symm.trans h2) v
  simpa only [F, ContinuousLinearMap.comp_apply,
    mfderiv_subtype_val (I := I) V (F p), mfderiv_subtype_val (I := I) U p] using happ


omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
    [IsManifold I ∞ N] in
theorem PartialDiffeomorph.opensMap_inv_mdiff
    (Φ : PartialDiffeomorph I I M N (∞ : WithTop ℕ∞))
    {U : Opens M} {V : Opens N} [Nonempty U] (hU : (U : Set M) ⊆ Φ.source)
    (hUV : (Φ : M → N) '' (U : Set M) ⊆ (V : Set N)) :
    ContMDiffOn I I ∞ (Function.invFun (PartialDiffeomorph.opensMap Φ hU hUV))
      (Set.range (PartialDiffeomorph.opensMap Φ hU hUV)) := by
  let W : Opens N := ⟨(Φ : M → N) '' (U : Set M), image_opens_isOpen Φ hU⟩
  letI : Nonempty W := by
    obtain ⟨x⟩ := (inferInstance : Nonempty U)
    exact ⟨⟨(Φ : M → N) x, ⟨x, x.2, rfl⟩⟩⟩
  have hWV : W ≤ V := hUV
  let inc : W → V := Opens.inclusion hWV
  let F : Diffeomorph I I U W (∞ : WithTop ℕ∞) :=
    PartialDiffeomorph.toOpensDiffeo Φ hU
  have hinc : IsOpenEmbedding inc := by
    exact Opens.isOpenEmbedding_of_le hWV
  have htotal : Function.Injective (inc ∘ F) := hinc.injective.comp F.injective
  have hinvInc : ContMDiffOn I I ∞ (Function.invFun inc) (Set.range inc) := by
    intro y hy
    have hamb : ContMDiffAt I I ∞
        (fun z : V => ((Function.invFun inc z : W) : N)) y := by
      refine ((contMDiff_subtype_val (I := I) (U := V)).contMDiffAt).congr_of_eventuallyEq ?_
      filter_upwards [hinc.isOpen_range.mem_nhds hy] with z hz
      obtain ⟨w, rfl⟩ := hz
      exact congrArg Subtype.val (Function.leftInverse_invFun hinc.injective w)
    exact (contMDiffAt_codRestr (fun z => (Function.invFun inc z).2) hamb).contMDiffWithinAt
  have hfun : PartialDiffeomorph.opensMap Φ hU hUV = inc ∘ F := rfl
  rw [hfun]
  have hsub : Set.range (inc ∘ F) ⊆ Set.range inc := by
    rintro y ⟨x, rfl⟩
    exact ⟨F x, rfl⟩
  have hFsmooth : ContMDiffOn I I ∞ F.symm (Set.univ : Set W) :=
    F.symm.contMDiff.contMDiffOn
  have hsmooth : ContMDiffOn I I ∞ (F.symm ∘ Function.invFun inc)
      (Set.range (inc ∘ F)) :=
    hFsmooth.comp (hinvInc.mono hsub) (fun _ _ => Set.mem_univ _)
  refine hsmooth.congr (fun y hy => ?_)
  obtain ⟨x, rfl⟩ := hy
  simp only [Function.comp_apply]
  rw [Function.leftInverse_invFun hinc.injective, F.symm_apply_apply]
  change Function.invFun (inc ∘ F) ((inc ∘ F) x) = x
  exact Function.leftInverse_invFun htotal x

omit [IsManifold I ∞ N] in
omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem invSubtype_mdiff (U : Opens N) [Nonempty U] :
    ContMDiffOn I I ∞ (Function.invFun (Subtype.val : U → N))
      (Set.range (Subtype.val : U → N)) := by
  intro y hy
  have hamb : ContMDiffAt I I ∞
      (fun z : N => ((Function.invFun (Subtype.val : U → N) z : U) : N)) y := by
    refine contMDiffAt_id.congr_of_eventuallyEq ?_
    filter_upwards [U.isOpenEmbedding'.isOpen_range.mem_nhds hy] with z hz
    obtain ⟨u, rfl⟩ := hz
    exact congrArg Subtype.val
      (Function.leftInverse_invFun U.isOpenEmbedding'.injective u)
  exact (contMDiffAt_codRestr
    (fun z => (Function.invFun (Subtype.val : U → N) z).2) hamb).contMDiffWithinAt

noncomputable def PartialDiffeomorph.liftTargetOpen
    {U : Opens N} [Nonempty U] (Φ : PartialDiffeomorph I I M U (∞ : WithTop ℕ∞))
    (htarget : Φ.target = Set.univ) :
    PartialDiffeomorph I I M N (∞ : WithTop ℕ∞) where
  toFun := fun x => (Φ x : N)
  invFun := fun y => Φ.toPartialEquiv.invFun
    (Function.invFun (Subtype.val : U → N) y)
  source := Φ.source
  target := U
  map_source' := fun x hx => (Φ x).2
  map_target' := by
    intro y hy
    let u : U := ⟨y, hy⟩
    have hinv : Function.invFun (Subtype.val : U → N) y = u := by
      exact Function.leftInverse_invFun U.isOpenEmbedding'.injective u
    rw [hinv]
    exact Φ.map_target' (htarget.symm ▸ Set.mem_univ u)
  left_inv' := by
    intro x hx
    rw [Function.leftInverse_invFun U.isOpenEmbedding'.injective]
    exact Φ.left_inv' hx
  right_inv' := by
    intro y hy
    let u : U := ⟨y, hy⟩
    have hinv : Function.invFun (Subtype.val : U → N) y = u := by
      exact Function.leftInverse_invFun U.isOpenEmbedding'.injective u
    change ((Φ (Φ.toPartialEquiv.invFun
      (Function.invFun (Subtype.val : U → N) y)) : U) : N) = y
    rw [hinv, Φ.right_inv' (htarget.symm ▸ Set.mem_univ u)]
  open_source := Φ.open_source
  open_target := U.isOpen
  contMDiffOn_toFun := by
    intro x hx
    exact ((contMDiff_subtype_val (I := I) (U := U)).contMDiffAt.comp x
      (Φ.contMDiffOn_toFun.contMDiffAt
        (Φ.open_source.mem_nhds hx))).contMDiffWithinAt
  contMDiffOn_invFun := by
    intro y hy
    let u : U := ⟨y, hy⟩
    have hyrange : y ∈ Set.range (Subtype.val : U → N) := ⟨u, rfl⟩
    have hinvAt : ContMDiffAt I I ∞
        (Function.invFun (Subtype.val : U → N)) y :=
      (invSubtype_mdiff (I := I) U).contMDiffAt
        (U.isOpenEmbedding'.isOpen_range.mem_nhds hyrange)
    have hinv : Function.invFun (Subtype.val : U → N) y = u := by
      exact Function.leftInverse_invFun U.isOpenEmbedding'.injective u
    have hΦAt : ContMDiffAt I I ∞ Φ.toPartialEquiv.invFun
        (Function.invFun (Subtype.val : U → N) y) := by
      rw [hinv]
      exact Φ.contMDiffOn_invFun.contMDiffAt
        (Φ.open_target.mem_nhds (htarget.symm ▸ Set.mem_univ u))
    exact (hΦAt.comp y hinvAt).contMDiffWithinAt


omit [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] in
omit [IsManifold I ∞ N] in
omit [FiniteDimensional ℝ E] [CompleteSpace E] in
@[simp] theorem PartialDiffeomorph.liftOpen_source
    {U : Opens N} [Nonempty U] (Φ : PartialDiffeomorph I I M U (∞ : WithTop ℕ∞))
    (htarget : Φ.target = Set.univ) :
    (PartialDiffeomorph.liftTargetOpen Φ htarget).source = Φ.source := rfl


omit [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] in
omit [IsManifold I ∞ N] in
omit [FiniteDimensional ℝ E] [CompleteSpace E] in
@[simp] theorem PartialDiffeomorph.liftOpen_target
    {U : Opens N} [Nonempty U] (Φ : PartialDiffeomorph I I M U (∞ : WithTop ℕ∞))
    (htarget : Φ.target = Set.univ) :
    (PartialDiffeomorph.liftTargetOpen Φ htarget).target = (U : Set N) := rfl


omit [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] in
omit [IsManifold I ∞ N] in
omit [FiniteDimensional ℝ E] [CompleteSpace E] in
@[simp] theorem PartialDiffeomorph.liftOpen_apply
    {U : Opens N} [Nonempty U] (Φ : PartialDiffeomorph I I M U (∞ : WithTop ℕ∞))
    (htarget : Φ.target = Set.univ) (x : M) :
    PartialDiffeomorph.liftTargetOpen Φ htarget x = (Φ x : N) := rfl

omit [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] in
omit [IsManifold I ∞ N] in
omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem PartialDiffeomorph.liftOpen_mfderiv
    {U : Opens N} [Nonempty U] (Φ : PartialDiffeomorph I I M U (∞ : WithTop ℕ∞))
    (htarget : Φ.target = Set.univ) {x : M} (hx : x ∈ Φ.source)
    (v : TangentSpace I x) :
    mfderiv I I (PartialDiffeomorph.liftTargetOpen Φ htarget : M → N) x v =
      mfderiv I I (Φ : M → U) x v := by
  have hΦd : MDifferentiableAt I I (Φ : M → U) x :=
    (Φ.contMDiffOn_toFun.contMDiffAt
      (Φ.open_source.mem_nhds hx)).mdifferentiableAt
        (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have hval : MDifferentiableAt I I (Subtype.val : U → N) (Φ x) :=
    ((contMDiff_subtype_val (I := I) (U := U)).contMDiffAt).mdifferentiableAt
      (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have hcomp := mfderiv_comp x hval hΦd
  have happ := DFunLike.congr_fun hcomp v
  change mfderiv I I (fun y : M => ((Φ y : U) : N)) x v = _
  simpa only [ContinuousLinearMap.comp_apply,
    mfderiv_subtype_val (I := I) U (Φ x)] using happ

end OpensDiffeo

end HCGCompactness
end DifferentialGeometry
