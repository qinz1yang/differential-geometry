import DifferentialGeometry.Topology.Manifold.OpenSubtype
import Mathlib.Geometry.Manifold.LocalDiffeomorph

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry

open Set Topology TopologicalSpace
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
variable {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners Real F H'}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
variable {n : WithTop ℕ∞}

omit [IsManifold I ∞ M] [IsManifold J ∞ N] in
theorem codRestr_contMDiffAt
    {N' : Type*} [TopologicalSpace N'] [ChartedSpace H' N']
    {V : Opens N'} {f : M → N'} (hmem : ∀ y, f y ∈ V) {x : M}
    (hf : ContMDiffAt I J (∞ : WithTop ℕ∞) f x) :
    ContMDiffAt I J (∞ : WithTop ℕ∞)
      (fun y ↦ (⟨f y, hmem y⟩ : V)) x := by
  rw [contMDiffAt_iff] at hf ⊢
  obtain ⟨hcont, hdiff⟩ := hf
  refine ⟨Topology.IsInducing.subtypeVal.continuousAt_iff.mpr
    (by simpa [Function.comp_def] using hcont), ?_⟩
  convert hdiff using 2
  funext y
  rfl

omit [IsManifold I ∞ M] [IsManifold J ∞ N] in
theorem image_opens_isOpen
    (Φ : PartialDiffeomorph I J M N n)
    {U : Opens M} (hU : (U : Set M) ⊆ Φ.source) :
    IsOpen ((Φ : M → N) '' (U : Set M)) := by
  have himg : (Φ : M → N) '' (U : Set M) =
      Φ.target ∩ ((Φ.symm : N → M) ⁻¹' (U : Set M)) := by
    ext y
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨Φ.map_source' (hU hu), ?_⟩
      have hleft : (Φ.symm : N → M) ((Φ : M → N) u) = u :=
        Φ.left_inv' (hU hu)
      change (Φ.symm : N → M) ((Φ : M → N) u) ∈ (U : Set M)
      rw [hleft]
      exact hu
    · rintro ⟨hy, hu⟩
      exact ⟨(Φ.symm : N → M) y, hu, Φ.right_inv' hy⟩
  rw [himg]
  exact Φ.symm.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage
    Φ.open_target U.2

namespace PartialDiffeomorph

noncomputable def toOpensDiffeo
    (Φ : PartialDiffeomorph I J M N (∞ : WithTop ℕ∞))
    {U : Opens M} (hU : (U : Set M) ⊆ Φ.source) :
    Diffeomorph I J U
      (⟨(Φ : M → N) '' (U : Set M), image_opens_isOpen Φ hU⟩ : Opens N)
      (∞ : WithTop ℕ∞) where
  toFun p := ⟨(Φ : M → N) p.1, ⟨p.1, p.2, rfl⟩⟩
  invFun q := ⟨(Φ.symm : N → M) q.1, by
    obtain ⟨u, hu, hueq⟩ := q.2
    rw [← hueq]
    have hleft : (Φ.symm : N → M) ((Φ : M → N) u) = u :=
      Φ.left_inv' (hU hu)
    change (Φ.symm : N → M) ((Φ : M → N) u) ∈ U
    rw [hleft]
    exact hu⟩
  left_inv p := by
    apply Subtype.ext
    exact Φ.left_inv' (hU p.2)
  right_inv q := by
    apply Subtype.ext
    obtain ⟨u, hu, hueq⟩ := q.2
    apply Φ.right_inv'
    rw [← hueq]
    exact Φ.map_source' (hU hu)
  contMDiff_toFun := by
    intro p
    have hbase : ContMDiffAt I J (∞ : WithTop ℕ∞)
        (fun p : U ↦ (Φ : M → N) p.1) p := by
      rw [contMDiffAt_subtype_iff]
      exact Φ.contMDiffOn_toFun.contMDiffAt
        (Φ.open_source.mem_nhds (hU p.2))
    exact codRestr_contMDiffAt
      (V := (⟨(Φ : M → N) '' (U : Set M), image_opens_isOpen Φ hU⟩ : Opens N))
      (f := fun p : U ↦ (Φ : M → N) p.1)
      (fun y ↦ ⟨y.1, y.2, rfl⟩) hbase
  contMDiff_invFun := by
    intro q
    let V : Opens N :=
      ⟨(Φ : M → N) '' (U : Set M), image_opens_isOpen Φ hU⟩
    have hmem : ∀ y : V, (Φ.symm : N → M) y.1 ∈ U := by
      intro y
      obtain ⟨u, hu, hueq⟩ := y.2
      rw [← hueq]
      have hleft : (Φ.symm : N → M) ((Φ : M → N) u) = u :=
        Φ.left_inv' (hU hu)
      change (Φ.symm : N → M) ((Φ : M → N) u) ∈ U
      rw [hleft]
      exact hu
    have hbase : ContMDiffAt J I (∞ : WithTop ℕ∞)
        (fun y : V ↦ (Φ.symm : N → M) y.1) q := by
      rw [contMDiffAt_subtype_iff]
      obtain ⟨u, hu, hueq⟩ := q.2
      have hqt : (q : N) ∈ Φ.target := by
        rw [← hueq]
        exact Φ.map_source' (hU hu)
      exact Φ.symm.contMDiffOn_toFun.contMDiffAt
        (Φ.open_target.mem_nhds hqt)
    exact codRestr_contMDiffAt (I := J) (J := I) hmem hbase

omit [IsManifold I ∞ M] [IsManifold J ∞ N] in
theorem mfderiv_toOpensDiffeo
    (Φ : PartialDiffeomorph I J M N (∞ : WithTop ℕ∞))
    {U : Opens M} (hU : (U : Set M) ⊆ Φ.source)
    (p : U) (v : TangentSpace I p) :
    mfderiv I J
        (toOpensDiffeo Φ hU : U →
          (⟨(Φ : M → N) '' (U : Set M), image_opens_isOpen Φ hU⟩ : Opens N)) p v =
      mfderiv I J (Φ : M → N) (p : M) v := by
  let V : Opens N :=
    ⟨(Φ : M → N) '' (U : Set M), image_opens_isOpen Φ hU⟩
  let Ψ : Diffeomorph I J U V (∞ : WithTop ℕ∞) :=
    toOpensDiffeo Φ hU
  have hΨd : MDifferentiableAt I J (Ψ : U → V) p :=
    Ψ.contMDiff.contMDiffAt.mdifferentiableAt
      (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have hvalV : MDifferentiableAt J J (Subtype.val : V → N) (Ψ p) :=
    ((contMDiff_subtype_val (I := J) (U := V)).contMDiffAt).mdifferentiableAt
      (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have hvalU : MDifferentiableAt I I (Subtype.val : U → M) p :=
    ((contMDiff_subtype_val (I := I) (U := U)).contMDiffAt).mdifferentiableAt
      (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have hΦd : MDifferentiableAt I J (Φ : M → N) (p : M) :=
    (Φ.contMDiffOn_toFun.contMDiffAt
      (Φ.open_source.mem_nhds (hU p.2))).mdifferentiableAt
        (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have hleft : mfderiv I J (fun y : U ↦ ((Ψ y : V) : N)) p =
      (mfderiv J J (Subtype.val : V → N) (Ψ p)).comp
        (mfderiv I J (Ψ : U → V) p) :=
    mfderiv_comp p hvalV hΨd
  have hright : mfderiv I J (fun y : U ↦ (Φ : M → N) (y : M)) p =
      (mfderiv I J (Φ : M → N) (p : M)).comp
        (mfderiv I I (Subtype.val : U → M) p) :=
    mfderiv_comp p hΦd hvalU
  have hmap := hleft.symm.trans hright
  have hleft_id :
      (mfderiv J J (Subtype.val : V → N) (Ψ p)).comp
          (mfderiv I J (Ψ : U → V) p) = mfderiv I J (Ψ : U → V) p := by
    ext w
    exact mfderiv_subtype_val_apply (I := J) V (Ψ p) _
  have hright_id :
      (mfderiv I J (Φ : M → N) (p : M)).comp
          (mfderiv I I (Subtype.val : U → M) p) =
        mfderiv I J (Φ : M → N) (p : M) := by
    ext w
    change mfderiv I J (Φ : M → N) (p : M)
        (mfderiv I I (Subtype.val : U → M) p w) = _
    rw [mfderiv_subtype_val_apply (I := I) U p]
    rfl
  rw [hleft_id, hright_id] at hmap
  exact DFunLike.congr_fun hmap v

noncomputable def opensMap
    (Φ : PartialDiffeomorph I J M N (∞ : WithTop ℕ∞))
    {U : Opens M} {V : Opens N}
    (hUV : (Φ : M → N) '' (U : Set M) ⊆ (V : Set N)) : U → V :=
  fun x => ⟨(Φ : M → N) x, hUV ⟨x, x.2, rfl⟩⟩

omit [IsManifold I ∞ M] [IsManifold J ∞ N] in
theorem opensMap_isOpenEmb
    (Φ : PartialDiffeomorph I J M N (∞ : WithTop ℕ∞))
    {U : Opens M} {V : Opens N} (hU : (U : Set M) ⊆ Φ.source)
    (hUV : (Φ : M → N) '' (U : Set M) ⊆ (V : Set N)) :
    IsOpenEmbedding (opensMap Φ hUV) := by
  let W : Opens N := ⟨(Φ : M → N) '' (U : Set M), image_opens_isOpen Φ hU⟩
  have hWV : W ≤ V := hUV
  let F : Diffeomorph I J U W (∞ : WithTop ℕ∞) :=
    toOpensDiffeo Φ hU
  have hinc : IsOpenEmbedding (Opens.inclusion hWV : W → V) :=
    Opens.isOpenEmbedding_of_le hWV
  have hfun : opensMap Φ hUV =
      (Opens.inclusion hWV : W → V) ∘ F := rfl
  rw [hfun]
  exact hinc.comp F.toHomeomorph.isOpenEmbedding

omit [IsManifold I ∞ M] [IsManifold J ∞ N] in
theorem opensMap_contMDiff
    (Φ : PartialDiffeomorph I J M N (∞ : WithTop ℕ∞))
    {U : Opens M} {V : Opens N} (hU : (U : Set M) ⊆ Φ.source)
    (hUV : (Φ : M → N) '' (U : Set M) ⊆ (V : Set N)) :
    ContMDiff I J ∞ (opensMap Φ hUV) := by
  let W : Opens N := ⟨(Φ : M → N) '' (U : Set M), image_opens_isOpen Φ hU⟩
  have hWV : W ≤ V := hUV
  let F : Diffeomorph I J U W (∞ : WithTop ℕ∞) :=
    toOpensDiffeo Φ hU
  have hfun : opensMap Φ hUV =
      (Opens.inclusion hWV : W → V) ∘ F := rfl
  rw [hfun]
  exact (contMDiff_inclusion hWV).comp F.contMDiff

omit [IsManifold I ∞ M] [IsManifold J ∞ N] in
theorem opensMap_mfderiv
    (Φ : PartialDiffeomorph I J M N (∞ : WithTop ℕ∞))
    {U : Opens M} {V : Opens N} (hU : (U : Set M) ⊆ Φ.source)
    (hUV : (Φ : M → N) '' (U : Set M) ⊆ (V : Set N))
    (p : U) (v : TangentSpace I p) :
    mfderiv I J (opensMap Φ hUV) p v =
      mfderiv I J (Φ : M → N) (p : M) v := by
  let F : U → V := opensMap Φ hUV
  have hFd : MDifferentiableAt I J F p :=
    ((opensMap_contMDiff Φ hU hUV).contMDiffAt).mdifferentiableAt
      (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have hvalV : MDifferentiableAt J J (Subtype.val : V → N) (F p) :=
    ((contMDiff_subtype_val (I := J) (U := V)).contMDiffAt).mdifferentiableAt
      (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have hvalU : MDifferentiableAt I I (Subtype.val : U → M) p :=
    ((contMDiff_subtype_val (I := I) (U := U)).contMDiffAt).mdifferentiableAt
      (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have hΦd : MDifferentiableAt I J (Φ : M → N) (p : M) :=
    (Φ.contMDiffOn_toFun.contMDiffAt
      (Φ.open_source.mem_nhds (hU p.2))).mdifferentiableAt
      (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have h1 : mfderiv I J (fun y : U => ((F y : V) : N)) p =
      (mfderiv J J (Subtype.val : V → N) (F p)).comp (mfderiv I J F p) :=
    mfderiv_comp p hvalV hFd
  have h2 : mfderiv I J (fun y : U => (Φ : M → N) (y : M)) p =
      (mfderiv I J (Φ : M → N) (p : M)).comp
        (mfderiv I I (Subtype.val : U → M) p) :=
    mfderiv_comp p hΦd hvalU
  have hmap := h1.symm.trans h2
  rw [mfderiv_subtype_val (I := J) V (F p),
    mfderiv_subtype_val (I := I) U p] at hmap
  exact DFunLike.congr_fun hmap v

omit [IsManifold I ∞ M] [IsManifold J ∞ N] in
theorem opensMap_invFun_contMDiffOn
    (Φ : PartialDiffeomorph I J M N (∞ : WithTop ℕ∞))
    {U : Opens M} {V : Opens N} [Nonempty U] (hU : (U : Set M) ⊆ Φ.source)
    (hUV : (Φ : M → N) '' (U : Set M) ⊆ (V : Set N)) :
    ContMDiffOn J I ∞ (Function.invFun (opensMap Φ hUV))
      (Set.range (opensMap Φ hUV)) := by
  let W : Opens N := ⟨(Φ : M → N) '' (U : Set M), image_opens_isOpen Φ hU⟩
  let : Nonempty W := by
    obtain ⟨x⟩ := (inferInstance : Nonempty U)
    exact ⟨⟨(Φ : M → N) x, ⟨x, x.2, rfl⟩⟩⟩
  have hWV : W ≤ V := hUV
  let inc : W → V := Opens.inclusion hWV
  let F : Diffeomorph I J U W (∞ : WithTop ℕ∞) :=
    toOpensDiffeo Φ hU
  have hinc : IsOpenEmbedding inc := by
    exact Opens.isOpenEmbedding_of_le hWV
  have htotal : Function.Injective (inc ∘ F) := hinc.injective.comp F.injective
  have hinvInc : ContMDiffOn J J ∞ (Function.invFun inc) (Set.range inc) := by
    intro y hy
    have hamb : ContMDiffAt J J ∞
        (fun z : V => ((Function.invFun inc z : W) : N)) y := by
      refine ((contMDiff_subtype_val (I := J) (U := V)).contMDiffAt).congr_of_eventuallyEq ?_
      filter_upwards [hinc.isOpen_range.mem_nhds hy] with z hz
      obtain ⟨w, rfl⟩ := hz
      exact congrArg Subtype.val (Function.leftInverse_invFun hinc.injective w)
    exact (codRestr_contMDiffAt
      (fun z => (Function.invFun inc z).2) hamb).contMDiffWithinAt
  have hfun : opensMap Φ hUV = inc ∘ F := rfl
  rw [hfun]
  have hsub : Set.range (inc ∘ F) ⊆ Set.range inc := by
    rintro y ⟨x, rfl⟩
    exact ⟨F x, rfl⟩
  have hFsmooth : ContMDiffOn J I ∞ F.symm (Set.univ : Set W) :=
    F.symm.contMDiff.contMDiffOn
  have hsmooth : ContMDiffOn J I ∞ (F.symm ∘ Function.invFun inc)
      (Set.range (inc ∘ F)) :=
    hFsmooth.comp (hinvInc.mono hsub) (fun _ _ => Set.mem_univ _)
  refine hsmooth.congr (fun y hy => ?_)
  obtain ⟨x, rfl⟩ := hy
  simp only [Function.comp_apply]
  rw [Function.leftInverse_invFun hinc.injective, F.symm_apply_apply]
  change Function.invFun (inc ∘ F) ((inc ∘ F) x) = x
  exact Function.leftInverse_invFun htotal x

end PartialDiffeomorph

omit [IsManifold J ∞ N] in
theorem contMDiffOn_invFun_subtypeVal
    (U : Opens N) [Nonempty U] :
    ContMDiffOn J J ∞ (Function.invFun (Subtype.val : U → N))
      (Set.range (Subtype.val : U → N)) := by
  intro y hy
  have hamb : ContMDiffAt J J ∞
      (fun z : N => ((Function.invFun (Subtype.val : U → N) z : U) : N)) y := by
    refine contMDiffAt_id.congr_of_eventuallyEq ?_
    filter_upwards [U.isOpenEmbedding'.isOpen_range.mem_nhds hy] with z hz
    obtain ⟨u, rfl⟩ := hz
    exact congrArg Subtype.val
      (Function.leftInverse_invFun U.isOpenEmbedding'.injective u)
  exact (codRestr_contMDiffAt
    (fun z => (Function.invFun (Subtype.val : U → N) z).2) hamb).contMDiffWithinAt

namespace PartialDiffeomorph

noncomputable def liftTargetOpen
    {U : Opens N} [Nonempty U] (Φ : PartialDiffeomorph I J M U (∞ : WithTop ℕ∞))
    (htarget : Φ.target = Set.univ) :
    PartialDiffeomorph I J M N (∞ : WithTop ℕ∞) where
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
    exact ((contMDiff_subtype_val (I := J) (U := U)).contMDiffAt.comp x
      (Φ.contMDiffOn_toFun.contMDiffAt
        (Φ.open_source.mem_nhds hx))).contMDiffWithinAt
  contMDiffOn_invFun := by
    intro y hy
    let u : U := ⟨y, hy⟩
    have hyrange : y ∈ Set.range (Subtype.val : U → N) := ⟨u, rfl⟩
    have hinvAt : ContMDiffAt J J ∞
        (Function.invFun (Subtype.val : U → N)) y :=
      (contMDiffOn_invFun_subtypeVal U).contMDiffAt
        (U.isOpenEmbedding'.isOpen_range.mem_nhds hyrange)
    have hinv : Function.invFun (Subtype.val : U → N) y = u := by
      exact Function.leftInverse_invFun U.isOpenEmbedding'.injective u
    have hΦAt : ContMDiffAt J I ∞ Φ.toPartialEquiv.invFun
        (Function.invFun (Subtype.val : U → N) y) := by
      rw [hinv]
      exact Φ.contMDiffOn_invFun.contMDiffAt
        (Φ.open_target.mem_nhds (htarget.symm ▸ Set.mem_univ u))
    exact (hΦAt.comp y hinvAt).contMDiffWithinAt

omit [IsManifold I ∞ M] [IsManifold J ∞ N] in
@[simp] theorem liftTargetOpen_source
    {U : Opens N} [Nonempty U] (Φ : PartialDiffeomorph I J M U (∞ : WithTop ℕ∞))
    (htarget : Φ.target = Set.univ) :
    (liftTargetOpen Φ htarget).source = Φ.source := rfl

omit [IsManifold I ∞ M] [IsManifold J ∞ N] in
@[simp] theorem liftTargetOpen_target
    {U : Opens N} [Nonempty U] (Φ : PartialDiffeomorph I J M U (∞ : WithTop ℕ∞))
    (htarget : Φ.target = Set.univ) :
    (liftTargetOpen Φ htarget).target = (U : Set N) := rfl

omit [IsManifold I ∞ M] [IsManifold J ∞ N] in
@[simp] theorem liftTargetOpen_apply
    {U : Opens N} [Nonempty U] (Φ : PartialDiffeomorph I J M U (∞ : WithTop ℕ∞))
    (htarget : Φ.target = Set.univ) (x : M) :
    liftTargetOpen Φ htarget x = (Φ x : N) := rfl

omit [IsManifold I ∞ M] [IsManifold J ∞ N] in
theorem mfderiv_liftTargetOpen
    {U : Opens N} [Nonempty U] (Φ : PartialDiffeomorph I J M U (∞ : WithTop ℕ∞))
    (htarget : Φ.target = Set.univ) {x : M} (hx : x ∈ Φ.source)
    (v : TangentSpace I x) :
    mfderiv I J (liftTargetOpen Φ htarget : M → N) x v =
      mfderiv I J (Φ : M → U) x v := by
  have hΦd : MDifferentiableAt I J (Φ : M → U) x :=
    (Φ.contMDiffOn_toFun.contMDiffAt
      (Φ.open_source.mem_nhds hx)).mdifferentiableAt
        (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have hval : MDifferentiableAt J J (Subtype.val : U → N) (Φ x) :=
    ((contMDiff_subtype_val (I := J) (U := U)).contMDiffAt).mdifferentiableAt
      (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have hcomp := mfderiv_comp x hval hΦd
  change mfderiv I J (fun y : M => ((Φ y : U) : N)) x v = _
  rw [mfderiv_subtype_val (I := J) U (Φ x)] at hcomp
  exact DFunLike.congr_fun hcomp v

end PartialDiffeomorph
end DifferentialGeometry
