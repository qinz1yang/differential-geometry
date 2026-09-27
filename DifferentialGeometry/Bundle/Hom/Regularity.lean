import DifferentialGeometry.Bundle.Equiv
import DifferentialGeometry.Bundle.Hom

open Bundle Filter Set
open scoped Manifold ContDiff Topology

variable {k : Type*} [NontriviallyNormedField k] [CompleteSpace k]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace k E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners k E H}
  {B : Type*} [TopologicalSpace B] [ChartedSpace H B]
  {FV FW : Type*} [NormedAddCommGroup FV] [NormedSpace k FV] [FiniteDimensional k FV]
  [NormedAddCommGroup FW] [NormedSpace k FW]
  {V W : B → Type*} [TopologicalSpace (TotalSpace FV V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module k (V x)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle FV V] [VectorBundle k FV V]
  [TopologicalSpace (TotalSpace FW W)]
  [∀ x, AddCommGroup (W x)] [∀ x, Module k (W x)] [∀ x, TopologicalSpace (W x)]
  [∀ x, IsTopologicalAddGroup (W x)] [∀ x, ContinuousSMul k (W x)]
  [FiberBundle FW W] [VectorBundle k FW W]
  {n : ℕ∞ω} {φ : ∀ x, V x →L[k] W x} {s : Set B} {x : B}

theorem contMDiffWithinAt_clm_bundle_of_map
    (hφ : ∀ v : V x, ContMDiffWithinAt (I.prod 𝓘(k, FV)) (I.prod 𝓘(k, FW)) n
      (fun z : TotalSpace FV V => (⟨z.proj, φ z.proj z.snd⟩ : TotalSpace FW W))
      (TotalSpace.proj ⁻¹' s) (⟨x, v⟩ : TotalSpace FV V)) :
    ContMDiffWithinAt I (I.prod 𝓘(k, FV →L[k] FW)) n
      (fun y => (⟨y, φ y⟩ : TotalSpace (FV →L[k] FW) (fun y => V y →L[k] W y))) s x := by
  rw [contMDiffWithinAt_hom_bundle]
  refine ⟨contMDiffWithinAt_id, ?_⟩
  apply contMDiffWithinAt_clm_of_pointwise
  intro v
  let e := trivializationAt FV V x
  let f := trivializationAt FW W x
  have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt FV V x
  have hxf : x ∈ f.baseSet := mem_baseSet_trivializationAt FW W x
  let σ (y : B) := e.symmL k y v
  have hσ : ContMDiffAt I (I.prod 𝓘(k, FV)) n (T% σ) x := by
    rw [contMDiffAt_section]
    apply (contMDiffAt_const (c := v)).congr_of_eventuallyEq
    filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
    rw [← Trivialization.continuousLinearMapAt_apply_of_mem k e hy]
    exact e.continuousLinearMapAt_symmL hy v
  have h : ContMDiffWithinAt I (I.prod 𝓘(k, FW)) n
      (fun y => (⟨y, φ y (σ y)⟩ : TotalSpace FW W)) s x :=
    (hφ (σ x)).comp x hσ.contMDiffWithinAt (fun y hy => hy)
  rw [contMDiffWithinAt_totalSpace] at h
  have heq (y : B) (hy : y ∈ f.baseSet) :
      ContinuousLinearMap.inCoordinates FV V FW W x y x y (φ y) v =
        (f (⟨y, φ y (σ y)⟩ : TotalSpace FW W)).2 := by
    simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply]
    exact Trivialization.continuousLinearMapAt_apply_of_mem k f hy _
  apply h.2.congr_of_eventuallyEq _ (heq x hxf)
  filter_upwards [mem_nhdsWithin_of_mem_nhds (f.open_baseSet.mem_nhds hxf)] with y hy
  exact heq y hy

theorem contMDiffAt_clm_bundle_of_map
    (hφ : ∀ v : V x, ContMDiffAt (I.prod 𝓘(k, FV)) (I.prod 𝓘(k, FW)) n
      (fun z : TotalSpace FV V => (⟨z.proj, φ z.proj z.snd⟩ : TotalSpace FW W))
      (⟨x, v⟩ : TotalSpace FV V)) :
    ContMDiffAt I (I.prod 𝓘(k, FV →L[k] FW)) n
      (fun y => (⟨y, φ y⟩ : TotalSpace (FV →L[k] FW) (fun y => V y →L[k] W y))) x := by
  simpa only [preimage_univ, contMDiffWithinAt_univ] using
    contMDiffWithinAt_clm_bundle_of_map (s := univ) (fun v => (hφ v).contMDiffWithinAt)

theorem ContMDiff.clm_bundle_of_map
    (hφ : ContMDiff (I.prod 𝓘(k, FV)) (I.prod 𝓘(k, FW)) n
      (fun z : TotalSpace FV V => (⟨z.proj, φ z.proj z.snd⟩ : TotalSpace FW W))) :
    ContMDiff I (I.prod 𝓘(k, FV →L[k] FW)) n
      (fun y => (⟨y, φ y⟩ : TotalSpace (FV →L[k] FW) (fun y => V y →L[k] W y))) :=
  fun x => contMDiffAt_clm_bundle_of_map (fun v => hφ ⟨x, v⟩)


theorem ContMDiffOn.clm_bundle_of_map
    (hφ : ContMDiffOn (I.prod 𝓘(k, FV)) (I.prod 𝓘(k, FW)) n
      (fun z : TotalSpace FV V => (⟨z.proj, φ z.proj z.snd⟩ : TotalSpace FW W))
      (TotalSpace.proj ⁻¹' s)) :
    ContMDiffOn I (I.prod 𝓘(k, FV →L[k] FW)) n
      (fun y => (⟨y, φ y⟩ : TotalSpace (FV →L[k] FW) (fun y => V y →L[k] W y))) s :=
  fun x hx => contMDiffWithinAt_clm_bundle_of_map (fun v => hφ ⟨x, v⟩ hx)

theorem contMDiffWithinAt_clm_bundle_map_iff :
    (∀ v : V x, ContMDiffWithinAt (I.prod 𝓘(k, FV)) (I.prod 𝓘(k, FW)) n
      (fun z : TotalSpace FV V => (⟨z.proj, φ z.proj z.snd⟩ : TotalSpace FW W))
      (TotalSpace.proj ⁻¹' s) (⟨x, v⟩ : TotalSpace FV V)) ↔
    ContMDiffWithinAt I (I.prod 𝓘(k, FV →L[k] FW)) n
      (fun y => (⟨y, φ y⟩ : TotalSpace (FV →L[k] FW) (fun y => V y →L[k] W y))) s x :=
  ⟨contMDiffWithinAt_clm_bundle_of_map, fun h _ => h.clm_bundle_map⟩

theorem contMDiffAt_clm_bundle_map_iff :
    (∀ v : V x, ContMDiffAt (I.prod 𝓘(k, FV)) (I.prod 𝓘(k, FW)) n
      (fun z : TotalSpace FV V => (⟨z.proj, φ z.proj z.snd⟩ : TotalSpace FW W))
      (⟨x, v⟩ : TotalSpace FV V)) ↔
    ContMDiffAt I (I.prod 𝓘(k, FV →L[k] FW)) n
      (fun y => (⟨y, φ y⟩ : TotalSpace (FV →L[k] FW) (fun y => V y →L[k] W y))) x :=
  ⟨contMDiffAt_clm_bundle_of_map, fun h _ => h.clm_bundle_map⟩

theorem contMDiffOn_clm_bundle_map_iff :
    ContMDiffOn (I.prod 𝓘(k, FV)) (I.prod 𝓘(k, FW)) n
      (fun z : TotalSpace FV V => (⟨z.proj, φ z.proj z.snd⟩ : TotalSpace FW W))
      (TotalSpace.proj ⁻¹' s) ↔
    ContMDiffOn I (I.prod 𝓘(k, FV →L[k] FW)) n
      (fun y => (⟨y, φ y⟩ : TotalSpace (FV →L[k] FW) (fun y => V y →L[k] W y))) s :=
  ⟨ContMDiffOn.clm_bundle_of_map, ContMDiffOn.clm_bundle_map⟩

theorem contMDiff_clm_bundle_map_iff :
    ContMDiff (I.prod 𝓘(k, FV)) (I.prod 𝓘(k, FW)) n
      (fun z : TotalSpace FV V => (⟨z.proj, φ z.proj z.snd⟩ : TotalSpace FW W)) ↔
    ContMDiff I (I.prod 𝓘(k, FV →L[k] FW)) n
      (fun y => (⟨y, φ y⟩ : TotalSpace (FV →L[k] FW) (fun y => V y →L[k] W y))) :=
  ⟨ContMDiff.clm_bundle_of_map, ContMDiff.clm_bundle_map⟩
