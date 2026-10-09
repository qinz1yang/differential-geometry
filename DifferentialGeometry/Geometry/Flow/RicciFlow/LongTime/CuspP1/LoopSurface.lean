import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.LoopTamingMain
import DifferentialGeometry.Topology.PiecewiseLinear.ExistsCombinatorialTriangulation
import DifferentialGeometry.Topology.PiecewiseLinear.ComponentComplex

set_option autoImplicit false

/-!
# The PL-tamed torus family is a combinatorial 2-manifold (LT-R2)

Given the LT-P2 presentation `h : K.space ≃ₜ X`, a triangulation `L` of `val '' (h ⁻¹' range τ)`
is a combinatorial 2-manifold, because `ι × Torus ≃ₜ L.space`: each vertex lies in a component
homeomorphic to `S¹ × S¹`, and links are unchanged by restricting to a component.
-/

noncomputable section
open Set Topology
open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.Topology.PiecewiseLinear

namespace GC.LongTime.CuspP1
open GC.Topology
universe u

private def circleHomeoSphere_LTR2 :
    Circle ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 :=
  Complex.orthonormalBasisOneI.repr.toHomeomorph.subtype fun z => by
    change z ∈ Metric.sphere (0 : ℂ) 1 ↔
      Complex.orthonormalBasisOneI.repr z ∈ Metric.sphere 0 1
    rw [mem_sphere_zero_iff_norm, mem_sphere_zero_iff_norm,
      Complex.orthonormalBasisOneI.repr.norm_map]

theorem isCombinatorialManifold_two_of_homeomorph_family_torus_LTR2 {ι : Type}
    [TopologicalSpace ι] [DiscreteTopology ι] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (L : Geometry.SimplicialComplex ℝ E)
    [Finite L.faces] (g : (ι × Torus) ≃ₜ L.space) : IsCombinatorialManifold 2 L := by
  classical
  intro v hv
  have hvL : v ∈ L.space :=
    L.mem_space_iff.mpr ⟨_, hv, subset_convexHull ℝ _ (Finset.mem_singleton_self v)⟩
  obtain ⟨⟨j, t0⟩, ht0⟩ := g.surjective ⟨v, hvL⟩
  have hvZ : v ∈ connectedComponentIn L.space v := mem_connectedComponentIn hvL
  have hZ : connectedComponentIn L.space v = range (fun t : Torus => (g (j, t) : E)) := by
    apply Subset.antisymm
    · rw [connectedComponentIn_eq_image hvL]
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨⟨i, t⟩, rfl⟩ := g.surjective x
      have hf : Continuous fun y : L.space => (g.symm y).1 := continuous_fst.comp g.symm.continuous
      have h1 := hf.image_connectedComponent_eq_singleton (a := (⟨v, hvL⟩ : L.space))
      have h2 : (g.symm (g (i, t))).1 ∈ (fun y : L.space => (g.symm y).1) ''
          connectedComponent (⟨v, hvL⟩ : L.space) := ⟨_, hx, rfl⟩
      rw [h1] at h2
      have h3 : (g.symm ⟨v, hvL⟩).1 = j := by rw [← ht0]; simp
      simp only [mem_singleton_iff, Homeomorph.symm_apply_apply, h3] at h2
      exact ⟨t, by rw [h2]⟩
    · have hc : Continuous fun t : Torus => g (j, t) :=
        g.continuous.comp (Continuous.prodMk continuous_const continuous_id)
      have hpre : IsPreconnected (range fun t : Torus => (g (j, t) : E)) :=
        isPreconnected_range (continuous_subtype_val.comp hc)
      refine hpre.subset_connectedComponentIn ⟨t0, by show ((g (j, t0) : L.space) : E) = v; rw [ht0]⟩ ?_
      rintro _ ⟨t, rfl⟩
      exact (g (j, t)).2
  set Z' := restrict L (connectedComponentIn L.space v) with hZ'
  have hspace : Z'.space = connectedComponentIn L.space v := restrict_connectedComponentIn_space L v
  have hfin : Finite Z'.faces := (restrict_faces_finite L _).to_subtype
  have hmem : ∀ t : Torus, (g (j, t) : E) ∈ Z'.space := fun t => by
    rw [hspace, hZ]; exact ⟨t, rfl⟩
  let f : Torus → Z'.space := fun t => ⟨g (j, t), hmem t⟩
  have hfc : Continuous f :=
    (continuous_subtype_val.comp (g.continuous.comp
      (Continuous.prodMk continuous_const continuous_id))).subtype_mk _
  have hfi : Function.Injective f := fun s t hst => by
    have h2 : ((g (j, s) : L.space) : E) = (g (j, t) : L.space) := by
      have := congrArg Subtype.val hst
      exact this
    have := g.injective (Subtype.ext h2)
    simpa using this
  have hfs : Function.Surjective f := by
    rintro ⟨y, hy⟩
    have hy' := hy
    rw [hspace, hZ] at hy'
    obtain ⟨t, rfl⟩ := hy'
    exact ⟨t, rfl⟩
  let Ψ : Torus ≃ₜ Z'.space :=
    hfc.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f ⟨hfi, hfs⟩)
  have hM : IsCombinatorialManifold 2 Z' :=
    isCombinatorialManifold_two_of_homeomorph_sphere_prod Z'
      (Ψ.symm.trans (circleHomeoSphere_LTR2.prodCongr circleHomeoSphere_LTR2))
  have hvc : ({v} : Finset E) ∈ Z'.faces := by
    rw [hZ', mem_restrict_faces_iff]
    refine ⟨hv, ?_⟩
    simpa using hvZ
  have := hM v hvc
  rw [hZ', geometricLink_restrict_connectedComponentIn L hvZ] at this
  exact this

theorem hasPLPresentation_surface_of_openPartialHomeomorph_family_LTR2 {ι : Type} [Finite ι]
    [Nonempty ι] [TopologicalSpace ι] [DiscreteTopology ι] {X : Type u} [TopologicalSpace X]
    [T2Space X] [CompactSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
    (σ : OpenPartialHomeomorph ((ι × Torus) × ℝ) X) (hσ : σ.source = {p | -1 < p.2 ∧ p.2 < 1})
    (τ : ι × Torus → X) (hτ : ∀ x, τ x = σ (x, 0)) (hO : IsTriangulationOrientable X) :
    ∃ (N : ℕ) (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N)))
      (_ : Finite K.faces) (h : K.space ≃ₜ X), IsCombinatorialManifold 3 K ∧ IsOrientable 3 K ∧
        ∃ (L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N))) (_ : Finite L.faces),
          IsCombinatorialManifold 2 L ∧
            L.space = ((↑) : K.space → EuclideanSpace ℝ (Fin N)) '' (h ⁻¹' range τ) := by
  obtain ⟨N, K, hKf, h, hK, hKo, hpoly⟩ :=
    hasPLPresentation_of_openPartialHomeomorph_family_LTP2 σ hσ τ hτ hO
  obtain ⟨L, hLfin, hLspace⟩ := hpoly.exists_simplicialComplex
  have : Finite L.faces := hLfin.to_subtype
  have h0 : ∀ x : ι × Torus, (x, (0 : ℝ)) ∈ σ.source := fun x => by
    rw [hσ]; exact ⟨by norm_num, by norm_num⟩
  have hτc : Continuous τ := by
    have : Continuous (σ ∘ fun x : ι × Torus => (x, (0 : ℝ))) :=
      σ.continuousOn.comp_continuous (by fun_prop) h0
    convert this using 1
    funext x
    exact hτ x
  have hτi : Function.Injective τ := fun x y hxy => by
    rw [hτ, hτ] at hxy
    have := σ.injOn (h0 x) (h0 y) hxy
    exact (Prod.mk.inj this).1
  have hmem : ∀ x, ((h.symm (τ x) : K.space) : EuclideanSpace ℝ (Fin N)) ∈ L.space := fun x => by
    rw [hLspace]; exact ⟨h.symm (τ x), by simp, rfl⟩
  let f : ι × Torus → L.space := fun x => ⟨h.symm (τ x), hmem x⟩
  have hfc : Continuous f :=
    (continuous_subtype_val.comp (h.symm.continuous.comp hτc)).subtype_mk _
  have hfi : Function.Injective f := fun x y hxy =>
    hτi (h.symm.injective (Subtype.ext (by
      have h2 : ((h.symm (τ x) : K.space) : EuclideanSpace ℝ (Fin N)) = h.symm (τ y) := by
        have := congrArg Subtype.val hxy
        exact this
      exact h2)))
  have hfs : Function.Surjective f := by
    rintro ⟨y, hy⟩
    have hy' := hy
    rw [hLspace] at hy'
    obtain ⟨k, hk, rfl⟩ := hy'
    obtain ⟨x, hx⟩ := hk
    exact ⟨x, Subtype.ext (by simp [f, hx])⟩
  let g : (ι × Torus) ≃ₜ L.space := hfc.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f ⟨hfi, hfs⟩)
  exact ⟨N, K, hKf, h, hK, hKo, L, hLfin.to_subtype,
    isCombinatorialManifold_two_of_homeomorph_family_torus_LTR2 L g, hLspace⟩

end GC.LongTime.CuspP1
