import DifferentialGeometry.Topology.Manifold.SmoothTransverseSection

set_option autoImplicit false

open Bundle Filter Function Manifold Set Topology
open scoped Bundle Manifold ContDiff

noncomputable section

namespace DifferentialGeometry.Topology.SmoothEmbeddingRealNormalAtlas

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : Type*} [TopologicalSpace G]
    {B : Type*} [TopologicalSpace B] [ChartedSpace H B]
    {A : Type*} [TopologicalSpace A] [ChartedSpace G A]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
    [IsManifold J ∞ A] {m : ℕ∞} {f : B → A}

/-- A smooth tangent field along an injective hypersurface with smooth normal
charts extends to an ambient tangent field near each image point. The extension
agrees with the original field at every image point in that neighborhood. -/
theorem exists_local_ambientSection
    (C : SmoothEmbeddingRealNormalAtlas I J ∞ f) (hf : Injective f)
    (s : ∀ x, TangentSpace J (f x))
    (hs : ContMDiff I J.tangent (m : ℕ∞ω)
      (fun x ↦ (⟨f x, s x⟩ : TangentBundle J A))) (x : B) :
    ∃ U : Set A, IsOpen U ∧ f x ∈ U ∧
      ∃ l : ∀ a, TangentSpace J a,
        ContMDiffOn J J.tangent (m : ℕ∞ω)
          (fun a ↦ (⟨a, l a⟩ : TangentBundle J A)) U ∧
        ∀ y, f y ∈ U → l (f y) = s y := by
  let R := C.toEmbeddingRealNormalAtlas
  let c := R.chart x
  let r : A → B := fun a ↦ (c.symm a).1
  have hx := R.mem_baseSet_self x
  have hfx : f x ∈ c.target := by
    rw [← R.apply_zero x hx]
    exact c.map_source (R.zero_mem_source x hx)
  have hrx : r (f x) = x := by
    dsimp [r]
    rw [← R.apply_zero x hx, c.left_inv (R.zero_mem_source x hx)]
  have hr : ContMDiffOn J I (m : ℕ∞ω) r c.target := by
    intro a ha
    exact contMDiffAt_fst.comp_contMDiffWithinAt a
      (((C.contMDiffOn_chart_symm x) a ha).of_le (by simp))
  let e := trivializationAt F (TangentSpace J) (f x)
  let g : B → F := fun y ↦ (e ⟨f y, s y⟩).2
  have hg : ContMDiffOn I 𝓘(ℝ, F) (m : ℕ∞ω) g (f ⁻¹' e.baseSet) := by
    exact ((e.contMDiffOn_iff
      (f := fun y ↦ (⟨f y, s y⟩ : TangentBundle J A))
      (s := f ⁻¹' e.baseSet) (fun y hy ↦ e.mem_source.mpr hy)).mp hs.contMDiffOn).2
  let U := c.target ∩ r ⁻¹' R.baseSet x ∩ e.baseSet ∩ r ⁻¹' (f ⁻¹' e.baseSet)
  have hxe : f x ∈ e.baseSet := mem_baseSet_trivializationAt F (TangentSpace J) (f x)
  have hrcont : ContinuousAt r (f x) :=
    (hr.contMDiffAt (c.open_target.mem_nhds hfx)).continuousAt
  have hU : U ∈ nhds (f x) := by
    apply inter_mem
    · apply inter_mem
      · exact inter_mem (c.open_target.mem_nhds hfx)
          (hrcont.preimage_mem_nhds
            (by rw [hrx]; exact (R.isOpen_baseSet x).mem_nhds hx))
      · exact e.open_baseSet.mem_nhds hxe
    · exact hrcont.preimage_mem_nhds
        (by
          rw [hrx]
          exact C.contMDiff.continuous.continuousAt.preimage_mem_nhds
            (e.open_baseSet.mem_nhds hxe))
  let l (a : A) : TangentSpace J a := e.symm a (g (r a))
  have hl : ContMDiffOn J J.tangent (m : ℕ∞ω)
      (fun a ↦ (⟨a, l a⟩ : TangentBundle J A)) U := by
    intro a ha
    rw [e.contMDiffWithinAt_section U ha.1.2]
    have hgr : ContMDiffOn J 𝓘(ℝ, F) (m : ℕ∞ω) (fun b ↦ g (r b)) U :=
      hg.comp (hr.mono (fun _ hb ↦ hb.1.1.1)) (fun _ hb ↦ hb.2)
    apply (hgr a ha).congr
    · intro b hb
      change (e ⟨b, e.symm b (g (r b))⟩).2 = g (r b)
      rw [e.apply_mk_symm hb.1.2]
    · change (e ⟨a, e.symm a (g (r a))⟩).2 = g (r a)
      rw [e.apply_mk_symm ha.1.2]
  have heq : ∀ y, f y ∈ U → l (f y) = s y := by
    intro y hy
    have hzero : (c.symm (f y)).2 = 0 := by
      apply (R.range_iff_zero x (c.symm (f y)) (c.map_target hy.1.1.1)).mp
      rw [c.right_inv hy.1.1.1]
      exact mem_range_self y
    have hfr : f (r (f y)) = f y := by
      calc
        f (r (f y)) = c (r (f y), 0) := (R.apply_zero x hy.1.1.2).symm
        _ = c (c.symm (f y)) := by congr 1; exact Prod.ext rfl hzero.symm
        _ = f y := c.right_inv hy.1.1.1
    have hry : r (f y) = y := hf hfr
    change e.symm (f y) (e ⟨f (r (f y)), s (r (f y))⟩).2 = s y
    rw [hry]
    exact e.symm_apply_apply_mk hy.1.2 _
  obtain ⟨O, hOU, hO, hxO⟩ := mem_nhds_iff.mp hU
  exact ⟨O, hO, hxO, l, hl.mono hOU, fun y hy ↦ heq y (hOU hy)⟩

end DifferentialGeometry.Topology.SmoothEmbeddingRealNormalAtlas
