import Mathlib.Geometry.Manifold.LocalDiffeomorph

set_option autoImplicit false
noncomputable section
open Set Function Manifold Topology Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry

theorem IsLocalDiffeomorphAt.of_eventuallyEq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
    {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] {n : WithTop ℕ∞}
    {f g : M → N} {x : M} (h : f =ᶠ[𝓝 x] g)
    (hg : IsLocalDiffeomorphAt I J n g x) : IsLocalDiffeomorphAt I J n f x := by
  obtain ⟨φ, hx, hφ⟩ := hg
  obtain ⟨W, hWsub, hWopen, hxW⟩ := mem_nhds_iff.mp h
  have hsm : ∀ y ∈ φ.toPartialEquiv.source ∩ W, f y = φ.toPartialEquiv.toFun y :=
    fun y hy => (hWsub hy.2).trans (hφ hy.1)
  refine ⟨{ toFun := f,
            invFun := φ.toPartialEquiv.invFun,
            source := φ.toPartialEquiv.source ∩ W,
            target := φ.toPartialEquiv.toFun '' (φ.toPartialEquiv.source ∩ W),
            map_source' := fun y hy => ⟨y, hy, (hsm y hy).symm⟩,
            map_target' := fun y hy => by
              obtain ⟨z, hz, rfl⟩ := hy
              rw [φ.toPartialEquiv.left_inv' hz.1]
              exact hz,
            left_inv' := fun y hy => by
              rw [hsm y hy]
              exact φ.toPartialEquiv.left_inv' hy.1,
            right_inv' := fun y hy => by
              obtain ⟨z, hz, rfl⟩ := hy
              rw [φ.toPartialEquiv.left_inv' hz.1]
              exact hsm z hz,
            open_source := φ.open_source.inter hWopen,
            open_target := φ.toOpenPartialHomeomorph.isOpen_image_of_subset_source
              (φ.open_source.inter hWopen) inter_subset_left,
            contMDiffOn_toFun := (φ.contMDiffOn_toFun.mono inter_subset_left).congr
              (fun y hy => hsm y hy),
            contMDiffOn_invFun := φ.contMDiffOn_invFun.mono
              (by rintro z ⟨w, hw, rfl⟩; exact φ.map_source hw.1) },
    ⟨hx, hxW⟩, fun y hy => rfl⟩

theorem OpenPartialHomeomorph.isLocalDiffeomorphAt_of_contMDiffOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
    {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] {n : WithTop ℕ∞}
    {e : OpenPartialHomeomorph M N}
    (he : ContMDiffOn I J n e e.source) (he' : ContMDiffOn J I n e.symm e.target)
    {x : M} (hx : x ∈ e.source) : IsLocalDiffeomorphAt I J n e x :=
  ⟨{ toPartialEquiv := e.toPartialEquiv,
     open_source := e.open_source,
     open_target := e.open_target,
     contMDiffOn_toFun := he,
     contMDiffOn_invFun := he' }, hx, fun _ _ => rfl⟩

theorem IsLocalDiffeomorphOn.exists_partialDiffeomorph_of_injOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
    {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] {n : WithTop ℕ∞}
    {f : M → N} {U : Set M}
    (hf : IsLocalDiffeomorphOn I J n f U) (hU : IsOpen U) (hne : U.Nonempty)
    (hinj : Set.InjOn f U) :
    ∃ Φ : PartialDiffeomorph I J M N n,
      Φ.toPartialEquiv.source = U ∧ Φ.toPartialEquiv.target = f '' U ∧ Φ.toFun = f := by
  classical
  let g : N → M := fun y =>
    if h : ∃ x ∈ U, f x = y then Classical.choose h else Classical.choose hne
  have hg_val : ∀ {y : N} (h : ∃ x ∈ U, f x = y), g y = Classical.choose h :=
    fun h => dif_pos h
  have hg_mem : ∀ {y : N} (h : ∃ x ∈ U, f x = y), g y ∈ U := fun h =>
    hg_val h ▸ (Classical.choose_spec h).1
  have hg_of : ∀ {y : N} (h : ∃ x ∈ U, f x = y), f (g y) = y := fun h =>
    hg_val h ▸ (Classical.choose_spec h).2
  have hleft : ∀ x ∈ U, g (f x) = x := by
    intro x hx
    have h : ∃ x' ∈ U, f x' = f x := ⟨x, hx, rfl⟩
    exact hinj (hg_mem h) hx (hg_of h)
  refine ⟨{ toFun := f,
             invFun := g,
             source := U,
             target := f '' U,
             map_source' := fun x hx => ⟨x, hx, rfl⟩,
             map_target' := fun y hy => hg_mem hy,
             left_inv' := fun x hx => hleft x hx,
             right_inv' := fun y hy => hg_of hy,
             open_source := hU,
             open_target := ?_,
             contMDiffOn_toFun := hf.contMDiffOn,
             contMDiffOn_invFun := ?_ }, rfl, rfl, rfl⟩
  · refine isOpen_iff_mem_nhds.mpr fun y hy => ?_
    obtain ⟨x, hxU, rfl⟩ := hy
    obtain ⟨Φ, hxΦ, hEq⟩ := hf ⟨x, hxU⟩
    have hV : x ∈ U ∩ Φ.source := ⟨hxU, hxΦ⟩
    have himg : f '' (U ∩ Φ.source) = Φ.toFun '' (U ∩ Φ.source) := by
      apply Set.image_congr
      intro w hw
      exact hEq hw.2
    have hnhds : f '' (U ∩ Φ.source) ∈ 𝓝 (f x) := by
      rw [himg]
      exact (Φ.toOpenPartialHomeomorph.isOpen_image_of_subset_source
        (hU.inter Φ.open_source) inter_subset_right).mem_nhds
        ⟨x, hV, (hEq hxΦ).symm⟩
    exact Filter.mem_of_superset hnhds (by
      rintro z ⟨w, hw, rfl⟩
      exact ⟨w, hw.1, rfl⟩)
  · intro y hy
    obtain ⟨x, hxU, rfl⟩ := hy
    have hloc := hf ⟨x, hxU⟩
    have hcont : ContinuousAt hloc.localInverse (f x) :=
      hloc.localInverse_contMDiffAt.continuousAt
    have hmemU : hloc.localInverse (f x) ∈ U := by
      rw [hloc.localInverse_left_inv hloc.localInverse_mem_target]
      exact hxU
    have hZ : {z : N | hloc.localInverse z ∈ U} ∈ 𝓝 (f x) :=
      hcont.preimage_mem_nhds (hU.mem_nhds hmemU)
    have hZsrc : hloc.localInverse.source ∈ 𝓝 (f x) :=
      hloc.localInverse_open_source.mem_nhds hloc.localInverse_mem_source
    have heq : g =ᶠ[𝓝 (f x)] hloc.localInverse := by
      filter_upwards [hZ, hZsrc] with z hzU hzsrc
      have hrep : f (hloc.localInverse z) = z := hloc.localInverse_right_inv hzsrc
      have h1 : g z ∈ U := hg_mem ⟨hloc.localInverse z, hzU, hrep⟩
      exact hinj h1 hzU (by rw [hg_of ⟨hloc.localInverse z, hzU, hrep⟩, hrep])
    exact (heq.contMDiffAt_iff.mpr hloc.localInverse_contMDiffAt).contMDiffWithinAt

end DifferentialGeometry
