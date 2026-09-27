import Mathlib.Topology.VectorBundle.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Operations

noncomputable section

open Bundle Filter Set
open scoped Topology

variable {k B F W : Type*} [NontriviallyNormedField k] [CompleteSpace k] [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace k F]
  [NormedAddCommGroup W] [NormedSpace k W] [FiniteDimensional k W]
  {V : B → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module k (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle k F V]

theorem ContinuousLinearMap.continuousOn_bundle_apply_of_pointwise
    (φ : ∀ x, W →L[k] V x) {U : Set B}
    (hq : ∀ w : W, ContinuousOn (fun x => (⟨x, φ x w⟩ : TotalSpace F V)) U) :
    ContinuousOn (fun z : B × W => (⟨z.1, φ z.1 z.2⟩ : TotalSpace F V))
      (U ×ˢ univ) := by
  rintro ⟨x, w⟩ hx
  rw [FiberBundle.continuousWithinAt_totalSpace]
  refine ⟨continuousWithinAt_fst, ?_⟩
  let t := trivializationAt F V x
  let A (y : B) : W →L[k] F :=
    (t.continuousLinearMapAt k y).comp (φ y)
  have hA : ContinuousWithinAt A U x := by
    apply continuousWithinAt_clm_apply.mpr
    intro v
    have h := hq v x hx.1
    rw [FiberBundle.continuousWithinAt_totalSpace] at h
    apply h.2.congr_of_eventuallyEq_of_mem _ hx.1
    filter_upwards [Filter.mem_inf_of_left (t.open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt F V x))] with y hy
    exact t.continuousLinearMapAt_apply_of_mem k hy _
  have hb : ContinuousWithinAt (fun z : B × W => z.1) (U ×ˢ univ) (x, w) :=
    continuousWithinAt_fst
  have hc : ContinuousWithinAt (fun z : B × W => A z.1) (U ×ˢ univ) (x, w) :=
    ContinuousWithinAt.comp (g := A) (f := fun z : B × W => z.1) hA hb (fun _ hz => hz.1)
  have hval := hc.clm_apply (continuousWithinAt_snd (p := (x, w)))
  apply hval.congr_of_eventuallyEq_of_mem _ hx
  filter_upwards [Filter.mem_inf_of_left
    (continuous_fst.continuousAt.preimage_mem_nhds (t.open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt F V x)))] with z hz
  exact (t.continuousLinearMapAt_apply_of_mem k hz _).symm

theorem ContinuousLinearEquiv.continuousOn_bundle_apply_of_symm
    (q : ∀ x, V x ≃L[k] W) {U : Set B}
    (hq : ∀ w : W, ContinuousOn (fun x => (⟨x, (q x).symm w⟩ : TotalSpace F V)) U) :
    ContinuousOn (fun z : TotalSpace F V => (z.proj, q z.proj z.snd))
      (TotalSpace.proj ⁻¹' U) := by
  intro z hz
  let := FiniteDimensional.complete k W
  let t := trivializationAt F V z.proj
  have ht : z.proj ∈ t.baseSet := mem_baseSet_trivializationAt F V z.proj
  let A (y : B) : W →L[k] F :=
    (t.continuousLinearMapAt k y).comp ((q y).symm : W →L[k] V y)
  have hA : ContinuousWithinAt A U z.proj := by
    apply continuousWithinAt_clm_apply.mpr
    intro v
    have h := hq v z.proj hz
    rw [FiberBundle.continuousWithinAt_totalSpace] at h
    apply h.2.congr_of_eventuallyEq_of_mem _ hz
    filter_upwards [Filter.mem_inf_of_left (t.open_baseSet.mem_nhds ht)] with y hy
    exact t.continuousLinearMapAt_apply_of_mem k hy _
  have hAeq (y : B) (hy : y ∈ t.baseSet) :
      A y = (((q y).symm.trans
        (t.continuousLinearEquivAt k y hy)) : W →L[k] F) := by
    dsimp only [A]
    rw [← t.coe_continuousLinearEquivAt_eq' (R := k) hy]
    rfl
  have hinv : (A z.proj).IsInvertible := by
    rw [hAeq z.proj ht]
    exact ⟨_, rfl⟩
  have hAi : ContinuousWithinAt (fun y => (A y).inverse) U z.proj :=
    (hinv.contDiffAt_map_inverse (n := 0)).continuousAt.comp_continuousWithinAt hA
  have hb : ContinuousWithinAt (TotalSpace.proj : TotalSpace F V → B)
      (TotalSpace.proj ⁻¹' U) z := (FiberBundle.continuous_proj F V).continuousWithinAt
  have hc : ContinuousWithinAt (fun p : TotalSpace F V => (A p.proj).inverse)
      (TotalSpace.proj ⁻¹' U) z :=
    ContinuousWithinAt.comp (g := fun y => (A y).inverse) hAi hb (mapsTo_preimage _ _)
  have hv : ContinuousWithinAt (fun p : TotalSpace F V => (t p).2)
      (TotalSpace.proj ⁻¹' U) z :=
    ((t.toOpenPartialHomeomorph.continuousAt (t.mem_source.mpr ht)).snd).continuousWithinAt
  have h := hb.prodMk (hc.clm_apply hv)
  apply h.congr_of_eventuallyEq_of_mem _ hz
  filter_upwards [Filter.mem_inf_of_left (t.open_source.mem_nhds (t.mem_source.mpr ht))] with p hp
  refine Prod.ext rfl ?_
  have hp' := t.mem_source.mp hp
  rw [hAeq p.proj hp', ContinuousLinearMap.inverse_equiv]
  change q p.proj p.snd = q p.proj
    ((t.continuousLinearEquivAt k p.proj hp').symm (t p).2)
  have hpval : (t p).2 = (t.continuousLinearEquivAt k p.proj hp') p.snd :=
    (congrFun (t.continuousLinearEquivAt_apply k p.proj hp') p.snd).symm
  rw [hpval, ContinuousLinearEquiv.symm_apply_apply]


theorem ContinuousLinearEquiv.continuousOn_bundle_trans_of_symm
    (q r : ∀ x, V x ≃L[k] W) {U U' : Set B}
    (hq : ∀ w : W, ContinuousOn (fun x => (⟨x, (q x).symm w⟩ : TotalSpace F V)) U)
    (hr : ∀ w : W, ContinuousOn (fun x => (⟨x, (r x).symm w⟩ : TotalSpace F V)) U') :
    ContinuousOn (fun x => (((q x).symm.trans (r x)) : W →L[k] W)) (U ∩ U') := by
  apply continuousOn_clm_apply.mpr
  intro w
  have h := ContinuousLinearEquiv.continuousOn_bundle_apply_of_symm r hr
  have hi := (hq w).mono (t := U ∩ U') inter_subset_left
  have hm : MapsTo (fun x => (⟨x, (q x).symm w⟩ : TotalSpace F V)) (U ∩ U')
      (TotalSpace.proj ⁻¹' U') := fun _ hx => hx.2
  exact (h.comp hi hm).snd
