import DifferentialGeometry.Topology.PiecewiseLinear.Manifold

open Set Topology
open scoped Manifold

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {n m p : ℕ} {M N P : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
  [TopologicalSpace P] [ChartedSpace (EuclideanSpace ℝ (Fin p)) P]

theorem IsPLAt.comp_isPLWithinAt {f : M → N} {g : N → P} {s : Set M} {x : M}
    (hg : IsPLAt m p g (f x)) (hf : IsPLWithinAt n m f s x) :
    IsPLWithinAt n p (g ∘ f) s x := by
  let e := chartAt (EuclideanSpace ℝ (Fin n)) x
  let e' := chartAt (EuclideanSpace ℝ (Fin m)) (f x)
  let e'' := chartAt (EuclideanSpace ℝ (Fin p)) (g (f x))
  have hx : x ∈ e.source := mem_chart_source _ _
  have hfx : f x ∈ e'.source := mem_chart_source _ _
  have hgc : ContinuousAt g (f x) := by
    have hc := hg.continuousWithinAt
    rw [continuousWithinAt_univ] at hc
    exact hc
  refine ⟨hgc.comp_continuousWithinAt hf.continuousWithinAt, ?_⟩
  have hgcoord : IsPiecewiseAffineWithinAt (e'' ∘ g ∘ e'.symm) univ (e' (f x)) := by
    have hc := hg.prop
    simp only [preimage_univ] at hc
    exact hc
  have hpoint : (e' ∘ f ∘ e.symm) (e x) = e' (f x) := by
    change e' (f (e.symm (e x))) = e' (f x)
    rw [e.left_inv hx]
  rw [← hpoint] at hgcoord
  have hcomp := hgcoord.comp hf.prop
  rw [preimage_univ, inter_univ] at hcomp
  have hfc : ContinuousWithinAt f s (e.symm (e x)) := by
    rw [e.left_inv hx]
    exact hf.continuousWithinAt
  have hc : ContinuousWithinAt (f ∘ e.symm) (e.symm ⁻¹' s) (e x) :=
    hfc.comp (e.continuousAt_symm (e.map_source hx)).continuousWithinAt (fun _ hz => hz)
  have hneigh : e'.source ∈ 𝓝 (f (e.symm (e x))) := by
    rw [e.left_inv hx]
    exact e'.open_source.mem_nhds hfx
  have hevent : ∀ᶠ z in 𝓝[e.symm ⁻¹' s] (e x), f (e.symm z) ∈ e'.source :=
    hc.preimage_mem_nhdsWithin hneigh
  refine piecewiseAffineProperty_localInvariantProp.congr_nhdsWithin ?_ ?_ hcomp
  · filter_upwards [hevent] with z hz
    change e'' (g (e'.symm (e' (f (e.symm z))))) = e'' (g (f (e.symm z)))
    rw [e'.left_inv hz]
  · change e'' (g (e'.symm (e' (f (e.symm (e x)))))) = e'' (g (f (e.symm (e x))))
    rw [e.left_inv hx, e'.left_inv hfx]

theorem IsPL.comp_isPLOn {f : M → N} {g : N → P} {s : Set M}
    (hg : IsPL m p g) (hf : IsPLOn n m f s) : IsPLOn n p (g ∘ f) s :=
  fun x hx => IsPLAt.comp_isPLWithinAt (hg (f x)) (hf x hx)

theorem IsPL.comp {f : M → N} {g : N → P} (hg : IsPL m p g) (hf : IsPL n m f) :
    IsPL n p (g ∘ f) := fun x => IsPLAt.comp_isPLWithinAt (hg (f x)) (hf x)

open Classical in
theorem IsPLOn.piecewise_postcomp_of_isClosed {f : M → N} {h : N → N} {A B : Set M}
    (hf : IsPLOn n m f (A ∪ B)) (hh : IsPL m m h) (hA : IsClosed A) (hB : IsClosed B)
    (hfix : ∀ x ∈ A ∩ B, ∀ᶠ y in 𝓝 (f x), h y = y) :
    IsPLOn n m (A.piecewise (h ∘ f) f) (A ∪ B) := by
  intro x hx
  by_cases hxA : x ∈ A
  · by_cases hxB : x ∈ B
    · have hevent : ∀ᶠ z in 𝓝[A ∪ B] x, h (f z) = f z :=
        (hf x hx).continuousWithinAt.eventually (hfix x ⟨hxA, hxB⟩)
      apply piecewiseAffineProperty_localInvariantProp.liftPropWithinAt_congr_of_eventuallyEq_of_mem
        (hf x hx) _ hx
      filter_upwards [hevent] with z hz
      by_cases hzA : z ∈ A
      · rw [piecewise_eq_of_mem A (h ∘ f) f hzA]
        exact hz
      · exact piecewise_eq_of_notMem A (h ∘ f) f hzA
    · apply piecewiseAffineProperty_localInvariantProp.liftPropWithinAt_congr_of_eventuallyEq_of_mem
        ((hh.comp_isPLOn hf) x hx) _ hx
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (hB.isOpen_compl.mem_nhds hxB)]
        with z hz hzB
      exact piecewise_eq_of_mem A (h ∘ f) f (hz.resolve_right hzB)
  · apply piecewiseAffineProperty_localInvariantProp.liftPropWithinAt_congr_of_eventuallyEq_of_mem
      (hf x hx) _ hx
    filter_upwards [mem_nhdsWithin_of_mem_nhds (hA.isOpen_compl.mem_nhds hxA)] with z hz
    exact piecewise_eq_of_notMem A (h ∘ f) f hz

end DifferentialGeometry.Topology.PiecewiseLinear
