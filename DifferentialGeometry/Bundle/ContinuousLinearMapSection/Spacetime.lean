import DifferentialGeometry.Bundle.Section
import Mathlib.Geometry.Manifold.VectorBundle.Pullback

set_option autoImplicit false

open scoped Manifold Topology ContDiff
open Bundle

section FixedSpatialPullback

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  {n : WithTop ℕ∞} [ContMDiffVectorBundle n F V I]

def ContMDiffOnSpacetimeEndomorphism
    (A : ℝ → (x : M) → V x →L[ℝ] V x) (U : Set (ℝ × M)) : Prop :=
  let c : C^n⟮𝓘(ℝ, ℝ).prod I, ℝ × M; I, M⟯ := ContMDiffMap.snd
  let _ : TopologicalSpace (TotalSpace F (fun p : ℝ × M => V p.2)) := by
    change TopologicalSpace (TotalSpace F (c *ᵖ V)); infer_instance
  let _ : FiberBundle F (fun p : ℝ × M => V p.2) := by
    change FiberBundle F (c *ᵖ V); infer_instance
  let _ : VectorBundle ℝ F (fun p : ℝ × M => V p.2) := by
    change VectorBundle ℝ F (c *ᵖ V); infer_instance
  let _ : ContMDiffVectorBundle n F (fun p : ℝ × M => V p.2)
      (𝓘(ℝ, ℝ).prod I) := by
    change ContMDiffVectorBundle n F (c *ᵖ V) (𝓘(ℝ, ℝ).prod I); infer_instance
  ContMDiffOn (𝓘(ℝ, ℝ).prod I)
    ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, F →L[ℝ] F)) n
    (fun p => TotalSpace.mk' (F →L[ℝ] F) p (A p.1 p.2) :
      ℝ × M → TotalSpace (F →L[ℝ] F)
        (fun p => V p.2 →L[ℝ] V p.2)) U

theorem contMDiffOnSpacetimeEndomorphism_of_contMDiffOn_hom_bundle
    {A : ℝ → (x : M) → V x →L[ℝ] V x} {U : Set (ℝ × M)}
    (hA : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, F →L[ℝ] F)) n
      (fun p : ℝ × M =>
        (TotalSpace.mk' (F →L[ℝ] F) p.2 (A p.1 p.2) :
          TotalSpace (F →L[ℝ] F) (fun x => V x →L[ℝ] V x))) U) :
    ContMDiffOnSpacetimeEndomorphism (I := I) (F := F)
      (V := V) (n := n) A U := by
  let c : C^n⟮𝓘(ℝ, ℝ).prod I, ℝ × M; I, M⟯ := ContMDiffMap.snd
  let _ : TopologicalSpace (TotalSpace F (fun p : ℝ × M => V p.2)) := by
    change TopologicalSpace (TotalSpace F (c *ᵖ V)); infer_instance
  let _ : FiberBundle F (fun p : ℝ × M => V p.2) := by
    change FiberBundle F (c *ᵖ V); infer_instance
  let _ : VectorBundle ℝ F (fun p : ℝ × M => V p.2) := by
    change VectorBundle ℝ F (c *ᵖ V); infer_instance
  let _ : ContMDiffVectorBundle n F (fun p : ℝ × M => V p.2)
      (𝓘(ℝ, ℝ).prod I) := by
    change ContMDiffVectorBundle n F (c *ᵖ V) (𝓘(ℝ, ℝ).prod I)
    infer_instance
  change ContMDiffOn (𝓘(ℝ, ℝ).prod I)
    ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, F →L[ℝ] F)) n
    (fun p => TotalSpace.mk' (F →L[ℝ] F) p (A p.1 p.2) :
      ℝ × M → TotalSpace (F →L[ℝ] F)
        (fun p => V p.2 →L[ℝ] V p.2)) U
  intro p hp
  have hc := hA p hp
  rw [contMDiffWithinAt_hom_bundle] at hc ⊢
  refine ⟨contMDiffWithinAt_id, ?_⟩
  convert hc.2 using 1
  funext q
  ext v
  simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply,
    Trivialization.continuousLinearMapAt_apply]
  change ((trivializationAt F V p.2).pullback c).linearMapAt ℝ q
      (A q.1 q.2 (((trivializationAt F V p.2).pullback c).symmL ℝ q v)) =
    (trivializationAt F V p.2).linearMapAt ℝ q.2
      (A q.1 q.2 ((trivializationAt F V p.2).symmL ℝ q.2 v))
  by_cases hq : q.2 ∈ (trivializationAt F V p.2).baseSet
  · rw [Trivialization.symmL_apply _ hq,
      Trivialization.symmL_apply _ (show q ∈ ((trivializationAt F V p.2).pullback c).baseSet from hq)]
    rw [Trivialization.coe_linearMapAt_of_mem _ hq,
      Trivialization.coe_linearMapAt_of_mem _ (show q ∈ ((trivializationAt F V p.2).pullback c).baseSet from hq)]
    rw [Trivialization.symm_apply _ (show q ∈ ((trivializationAt F V p.2).pullback c).baseSet from hq)]
    rfl
  · rw [Trivialization.linearMapAt_def_of_notMem _ hq,
      Trivialization.linearMapAt_def_of_notMem _ (show q ∉ ((trivializationAt F V p.2).pullback c).baseSet from hq)]
    rfl

theorem ContMDiffOnSpacetimeEndomorphism.mono
    {A : ℝ → (x : M) → V x →L[ℝ] V x} {U W : Set (ℝ × M)}
    (hA : ContMDiffOnSpacetimeEndomorphism (I := I) (F := F)
      (V := V) (n := n) A U)
    (hWU : W ⊆ U) :
    ContMDiffOnSpacetimeEndomorphism (I := I) (F := F)
      (V := V) (n := n) A W := by
  let c : C^n⟮𝓘(ℝ, ℝ).prod I, ℝ × M; I, M⟯ := ContMDiffMap.snd
  let _ : TopologicalSpace (TotalSpace F (fun p : ℝ × M => V p.2)) := by
    change TopologicalSpace (TotalSpace F (c *ᵖ V)); infer_instance
  let _ : FiberBundle F (fun p : ℝ × M => V p.2) := by
    change FiberBundle F (c *ᵖ V); infer_instance
  let _ : VectorBundle ℝ F (fun p : ℝ × M => V p.2) := by
    change VectorBundle ℝ F (c *ᵖ V); infer_instance
  let _ : ContMDiffVectorBundle n F (fun p : ℝ × M => V p.2)
      (𝓘(ℝ, ℝ).prod I) := by
    change ContMDiffVectorBundle n F (c *ᵖ V) (𝓘(ℝ, ℝ).prod I)
    infer_instance
  change ContMDiffOn (𝓘(ℝ, ℝ).prod I)
    ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, F →L[ℝ] F)) n
    (fun p => TotalSpace.mk' (F →L[ℝ] F) p (A p.1 p.2) :
      ℝ × M → TotalSpace (F →L[ℝ] F)
        (fun p => V p.2 →L[ℝ] V p.2)) U at hA
  change ContMDiffOn (𝓘(ℝ, ℝ).prod I)
    ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, F →L[ℝ] F)) n
    (fun p => TotalSpace.mk' (F →L[ℝ] F) p (A p.1 p.2) :
      ℝ × M → TotalSpace (F →L[ℝ] F)
        (fun p => V p.2 →L[ℝ] V p.2)) W
  exact hA.mono hWU

theorem ContMDiffOnSpacetimeEndomorphism.congr
    {A B : ℝ → (x : M) → V x →L[ℝ] V x} {U : Set (ℝ × M)}
    (hA : ContMDiffOnSpacetimeEndomorphism (I := I) (F := F)
      (V := V) (n := n) A U)
    (hBA : ∀ p ∈ U, B p.1 p.2 = A p.1 p.2) :
    ContMDiffOnSpacetimeEndomorphism (I := I) (F := F)
      (V := V) (n := n) B U := by
  let c : C^n⟮𝓘(ℝ, ℝ).prod I, ℝ × M; I, M⟯ := ContMDiffMap.snd
  let _ : TopologicalSpace (TotalSpace F (fun p : ℝ × M => V p.2)) := by
    change TopologicalSpace (TotalSpace F (c *ᵖ V)); infer_instance
  let _ : FiberBundle F (fun p : ℝ × M => V p.2) := by
    change FiberBundle F (c *ᵖ V); infer_instance
  let _ : VectorBundle ℝ F (fun p : ℝ × M => V p.2) := by
    change VectorBundle ℝ F (c *ᵖ V); infer_instance
  let _ : ContMDiffVectorBundle n F (fun p : ℝ × M => V p.2)
      (𝓘(ℝ, ℝ).prod I) := by
    change ContMDiffVectorBundle n F (c *ᵖ V) (𝓘(ℝ, ℝ).prod I)
    infer_instance
  unfold ContMDiffOnSpacetimeEndomorphism at hA ⊢
  exact hA.congr (fun p hp => congrArg (TotalSpace.mk' (F →L[ℝ] F) p) (hBA p hp))

theorem ContMDiffOnSpacetimeEndomorphism.continuousOn_hom_bundle
    {A : ℝ → (x : M) → V x →L[ℝ] V x} {U : Set (ℝ × M)}
    (hA : ContMDiffOnSpacetimeEndomorphism (I := I) (F := F)
      (V := V) (n := n) A U) :
    ContinuousOn (fun p : ℝ × M =>
      (TotalSpace.mk' (F →L[ℝ] F) p.2 (A p.1 p.2) :
        TotalSpace (F →L[ℝ] F) (fun x => V x →L[ℝ] V x))) U := by
  let c : C^n⟮𝓘(ℝ, ℝ).prod I, ℝ × M; I, M⟯ := ContMDiffMap.snd
  let _ : TopologicalSpace (TotalSpace F (fun p : ℝ × M => V p.2)) := by
    change TopologicalSpace (TotalSpace F (c *ᵖ V)); infer_instance
  let _ : FiberBundle F (fun p : ℝ × M => V p.2) := by
    change FiberBundle F (c *ᵖ V); infer_instance
  let _ : VectorBundle ℝ F (fun p : ℝ × M => V p.2) := by
    change VectorBundle ℝ F (c *ᵖ V); infer_instance
  let _ : ContMDiffVectorBundle n F (fun p : ℝ × M => V p.2)
      (𝓘(ℝ, ℝ).prod I) := by
    change ContMDiffVectorBundle n F (c *ᵖ V) (𝓘(ℝ, ℝ).prod I)
    infer_instance
  change ContMDiffOn (𝓘(ℝ, ℝ).prod I)
    ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, F →L[ℝ] F)) n
    (fun p => TotalSpace.mk' (F →L[ℝ] F) p (A p.1 p.2) :
      ℝ × M → TotalSpace (F →L[ℝ] F)
        (fun p => V p.2 →L[ℝ] V p.2)) U at hA
  intro p hp
  have hc := hA.continuousOn p hp
  rw [continuousWithinAt_hom_bundle] at hc ⊢
  refine ⟨continuous_snd.continuousWithinAt, ?_⟩
  convert hc.2 using 1
  funext q
  ext v
  simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply,
    Trivialization.continuousLinearMapAt_apply]
  change (trivializationAt F V p.2).linearMapAt ℝ q.2
      (A q.1 q.2 ((trivializationAt F V p.2).symmL ℝ q.2 v)) =
    ((trivializationAt F V p.2).pullback c).linearMapAt ℝ q
      (A q.1 q.2 (((trivializationAt F V p.2).pullback c).symmL ℝ q v))
  by_cases hq : q.2 ∈ (trivializationAt F V p.2).baseSet
  · rw [Trivialization.symmL_apply _ hq,
      Trivialization.symmL_apply _ (show q ∈ ((trivializationAt F V p.2).pullback c).baseSet from hq)]
    rw [Trivialization.coe_linearMapAt_of_mem _ hq,
      Trivialization.coe_linearMapAt_of_mem _ (show q ∈ ((trivializationAt F V p.2).pullback c).baseSet from hq)]
    rw [Trivialization.symm_apply _ (show q ∈ ((trivializationAt F V p.2).pullback c).baseSet from hq)]
    rfl
  · rw [Trivialization.linearMapAt_def_of_notMem _ hq,
      Trivialization.linearMapAt_def_of_notMem _ (show q ∉ ((trivializationAt F V p.2).pullback c).baseSet from hq)]
    rfl


theorem contDiffOn_fixed_spatial_of_contMDiffOn_pullback_section
    {w : (p : ℝ × M) → V p.2} {U : Set (ℝ × M)} (hU : IsOpen U)
    (hw : ContMDiffOn (𝓘(ℝ, ℝ).prod I)
      ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, F)) n
      (fun p => TotalSpace.mk' F p (w p) : ℝ × M →
        TotalSpace F ((ContMDiffMap.snd :
          C^n⟮𝓘(ℝ, ℝ).prod I, ℝ × M; I, M⟯) *ᵖ V)) U)
    {x : M} {s : Set ℝ} (hsU : ∀ t ∈ s, (t, x) ∈ U) :
    ContDiffOn ℝ n (fun t : ℝ => (show V x from w (t, x))) s := by
  classical
  let c : C^n⟮𝓘(ℝ, ℝ).prod I, ℝ × M; I, M⟯ := ContMDiffMap.snd
  let e₀ := trivializationAt F V x
  let e := e₀.pullback c
  have hx : x ∈ e₀.baseSet := mem_baseSet_trivializationAt F V x
  let U' : Set (ℝ × M) := U ∩ Prod.snd ⁻¹' e₀.baseSet
  have hU' : IsOpen U' := hU.inter (e₀.open_baseSet.preimage continuous_snd)
  have hU'e : U' ⊆ e.baseSet := by
    intro p hp
    change p.2 ∈ e₀.baseSet
    exact hp.2
  have hsU' : ∀ t ∈ s, (t, x) ∈ U' := by
    intro t ht
    exact ⟨hsU t ht, hx⟩
  let _ : MemTrivializationAtlas e := ⟨by
    exact ⟨e₀, inferInstance, rfl⟩⟩
  have hw' : ContMDiffOn (𝓘(ℝ, ℝ).prod I)
      ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, F)) n
      (fun p => TotalSpace.mk' F p (w p) : ℝ × M → TotalSpace F (c *ᵖ V)) U := by
    simpa [c] using hw
  have hcoord : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, F) n
      (fun p => (e ⟨p, w p⟩).2) U' :=
    (e.contMDiffOn_section_iff hU' hU'e).mp (hw'.mono Set.inter_subset_left)
  have hincl : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod I) n
      (fun t : ℝ => (t, x)) := contMDiff_id.prodMk contMDiff_const
  have hcoordTime : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, F) n
      (fun t => (e ⟨(t, x), w (t, x)⟩).2) s :=
    hcoord.comp hincl.contMDiffOn hsU'
  have hcoordTime' : ContDiffOn ℝ n
      (fun t => e₀.continuousLinearMapAt ℝ x (w (t, x))) s := by
    rw [← contMDiffOn_iff_contDiffOn]
    convert hcoordTime using 1
    funext t
    rw [Bundle.Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) e₀ hx]
    rfl
  have hback := (e₀.symmL ℝ x).contDiff.comp_contDiffOn hcoordTime'
  exact hback.congr fun t ht =>
    (e₀.symmL_continuousLinearMapAt hx (w (t, x))).symm

theorem contMDiffOn_fixed_time_of_contMDiffOn_pullback_section
    {w : (p : ℝ × M) → V p.2} {U : Set (ℝ × M)}
    (hw : ContMDiffOn (𝓘(ℝ, ℝ).prod I)
      ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, F)) n
      (fun p => TotalSpace.mk' F p (w p) : ℝ × M →
        TotalSpace F ((ContMDiffMap.snd :
          C^n⟮𝓘(ℝ, ℝ).prod I, ℝ × M; I, M⟯) *ᵖ V)) U)
    {t : ℝ} {s : Set M} (hsU : ∀ x ∈ s, (t, x) ∈ U) :
    ContMDiffOn I (I.prod 𝓘(ℝ, F)) n
      (fun x => TotalSpace.mk' F x (w (t, x))) s := by
  intro x hx
  let c : C^n⟮𝓘(ℝ, ℝ).prod I, ℝ × M; I, M⟯ := ContMDiffMap.snd
  let e₀ := trivializationAt F V x
  let e := e₀.pullback c
  have hx₀ : x ∈ e₀.baseSet := mem_baseSet_trivializationAt F V x
  have hxe : (t, x) ∈ e.baseSet := hx₀
  let _ : MemTrivializationAtlas e := ⟨by
    exact ⟨e₀, inferInstance, rfl⟩⟩
  have hcoord : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, F) n
      (fun p => (e ⟨p, w p⟩).2) U (t, x) :=
    (e.contMDiffWithinAt_section U hxe).mp (hw (t, x) (hsU x hx))
  have hslice : ContMDiffWithinAt I (𝓘(ℝ, ℝ).prod I) n
      (fun y : M => (t, y)) s x :=
    contMDiffWithinAt_const.prodMk contMDiffWithinAt_id
  have hcoordSlice := hcoord.comp x hslice hsU
  apply (e₀.contMDiffWithinAt_section s hx₀).mpr
  convert hcoordSlice using 1
  funext y
  rfl

end FixedSpatialPullback
