import DifferentialGeometry.Topology.PiecewiseLinear.Map.Locality
import DifferentialGeometry.Topology.PiecewiseLinear.PLMap

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

section Composition

variable {n m p : ℕ} {M N P : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
  [TopologicalSpace P] [ChartedSpace (EuclideanSpace ℝ (Fin p)) P]

theorem IsPLWithinAt.comp {f : M → N} {g : N → P} {s : Set M} {t : Set N} {x : M}
    (hg : IsPLWithinAt m p g t (f x)) (hf : IsPLWithinAt n m f s x) (hst : MapsTo f s t) :
    IsPLWithinAt n p (g ∘ f) s x := by
  let e := chartAt (EuclideanSpace ℝ (Fin n)) x
  let e' := chartAt (EuclideanSpace ℝ (Fin m)) (f x)
  let e'' := chartAt (EuclideanSpace ℝ (Fin p)) (g (f x))
  have hx : x ∈ e.source := mem_chart_source _ _
  have hfx : f x ∈ e'.source := mem_chart_source _ _
  have hpre : f ⁻¹' e'.source ∈ 𝓝[s] x :=
    hf.continuousWithinAt.preimage_mem_nhdsWithin (e'.open_source.mem_nhds hfx)
  refine (piecewiseAffineProperty_localInvariantProp.liftPropWithinAt_inter' hpre).mp ?_
  have hsub : s ∩ f ⁻¹' e'.source ⊆ s := inter_subset_left
  have hnb : s ∩ f ⁻¹' e'.source ∈ 𝓝[s] x := Filter.inter_mem self_mem_nhdsWithin hpre
  have hf' : IsPLWithinAt n m f (s ∩ f ⁻¹' e'.source) x := hf.mono_of_mem_nhdsWithin hsub hnb
  refine ⟨hg.continuousWithinAt.comp hf'.continuousWithinAt (hst.mono_left hsub), ?_⟩
  have hgcoord : IsPiecewiseAffineWithinAt (e'' ∘ g ∘ e'.symm) (e'.symm ⁻¹' t) (e' (f x)) :=
    hg.prop
  have hpoint : (e' ∘ f ∘ e.symm) (e x) = e' (f x) := by
    change e' (f (e.symm (e x))) = e' (f x)
    rw [e.left_inv hx]
  rw [← hpoint] at hgcoord
  have hcomp := hgcoord.comp hf'.prop
  have hset : e.symm ⁻¹' (s ∩ f ⁻¹' e'.source) ∩
      (e' ∘ f ∘ e.symm) ⁻¹' (e'.symm ⁻¹' t) = e.symm ⁻¹' (s ∩ f ⁻¹' e'.source) := by
    refine inter_eq_left.mpr fun z hz => ?_
    change e'.symm (e' (f (e.symm z))) ∈ t
    rw [e'.left_inv hz.2]
    exact hst hz.1
  rw [hset] at hcomp
  refine piecewiseAffineProperty_localInvariantProp.congr_nhdsWithin ?_ ?_ hcomp
  · filter_upwards [self_mem_nhdsWithin] with z hz
    change e'' (g (e'.symm (e' (f (e.symm z))))) = e'' (g (f (e.symm z)))
    rw [e'.left_inv hz.2]
  · change e'' (g (e'.symm (e' (f (e.symm (e x)))))) = e'' (g (f (e.symm (e x))))
    rw [e.left_inv hx, e'.left_inv hfx]

theorem IsPLOn.comp_of_mapsTo {f : M → N} {g : N → P} {s : Set M} {t : Set N}
    (hg : IsPLOn m p g t) (hf : IsPLOn n m f s) (hst : MapsTo f s t) : IsPLOn n p (g ∘ f) s :=
  fun x hx => IsPLWithinAt.comp (hg (f x) (hst hx)) (hf x hx) hst

end Composition

end DifferentialGeometry.Topology.PiecewiseLinear
