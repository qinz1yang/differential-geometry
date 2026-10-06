import DifferentialGeometry.Topology.ThreeManifold.TorusCut.CompressionTransport
import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedralTorusBicollar
import DifferentialGeometry.Topology.Homeomorph.ExtendNearIdentity
import DifferentialGeometry.Topology.PiecewiseLinear.Approximation.Homeomorph
import DifferentialGeometry.Topology.PiecewiseLinear.Atlas.Compact
import DifferentialGeometry.Topology.InvarianceOfDomainManifold
set_option autoImplicit false

/-!
# Taming the seam tori of a smooth torus assembly

Let `σ` be a bicollar of a torus `τ` in a compact metric space `X` with a PL atlas, and let `Φ`
be the polyhedral bicollar of the square donut in Euclidean three-space. The composite
`σ ∘ Φ⁻¹` is a homeomorphism from an open subset of Euclidean space onto an open neighbourhood
`V ≠ X` of the torus. Viewing `V` as a PL manifold through the single chart `Φ ∘ σ⁻¹`, the
Moise approximation theorem gives a PL homeomorphism `f` of `V` onto itself that moves each
point by less than half its distance to the complement of `V`. Such a homeomorphism extends by
the identity to a homeomorphism `G` of `X`, the torus `G ∘ τ` is the PL image of the polyhedral
square donut, hence a PL piece, and pulling the atlas back along `G` makes `τ` a PL piece
(`hasPLPieceAtlas_of_bicollar`). Every compact topological 3-manifold carries a PL atlas and a
compatible metric, so every bicollared torus in it has a PL piece atlas. This applies to the
seam tori of a reconstruction of a smooth torus assembly, which removes the PL piece hypothesis
from the compressing disc criterion for incompressibility.
-/

noncomputable section
open Set Topology
open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.Topology.PiecewiseLinear

namespace GC.Topology
universe u

theorem isPLHomeomorphInto_comp_symm_of_singleton {M N : Type*} [TopologicalSpace M]
    [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))) (hc : c.source = univ) {f : M → N}
    (hf : letI := c.singletonChartedSpace hc; IsPLHomeomorphInto 3 f univ) :
    IsPLHomeomorphInto 3 (f ∘ c.symm) c.target := by
  let := c.singletonChartedSpace hc
  obtain ⟨hpl, hinj, hinv⟩ := hf
  have hch : ∀ x : M, chartAt (EuclideanSpace ℝ (Fin 3)) x = c := fun _ =>
    c.singletonChartedSpace_chartAt_eq hc
  have himg : (f ∘ c.symm) '' c.target = f '' univ := by
    rw [image_comp, c.symm_image_target_eq_source, hc]
  refine ⟨?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨hcont, hpa⟩ := hpl (c.symm y) (mem_univ _)
    change IsPiecewiseAffineWithinAt (chartAt (EuclideanSpace ℝ (Fin 3)) (f (c.symm y)) ∘ f ∘
      (chartAt (EuclideanSpace ℝ (Fin 3)) (c.symm y)).symm)
      ((chartAt (EuclideanSpace ℝ (Fin 3)) (c.symm y)).symm ⁻¹' univ)
      (chartAt (EuclideanSpace ℝ (Fin 3)) (c.symm y) (c.symm y)) at hpa
    rw [hch, c.right_inv hy, preimage_univ] at hpa
    refine ⟨(((continuousWithinAt_univ _ _).mp hcont).comp
      (c.continuousAt_symm hy)).continuousWithinAt, ?_⟩
    have h1 := hpa.inter_of_mem_nhds (c.open_target.mem_nhds hy)
    rw [univ_inter] at h1
    exact h1
  · exact (injOn_univ.mp hinj).comp_injOn c.symm.injOn
  · intro z hz
    rw [himg] at hz
    obtain ⟨k, hk, hkf⟩ := hinv z hz
    refine ⟨c ∘ k, ?_, ?_⟩
    · rw [himg]
      obtain ⟨hkc, hkpa⟩ := hk
      refine ⟨(c.continuousAt (by rw [hc]; trivial)).comp_continuousWithinAt hkc, ?_⟩
      change IsPiecewiseAffineWithinAt (chartAt (EuclideanSpace ℝ (Fin 3)) (k z) ∘ k ∘
        (chartAt (EuclideanSpace ℝ (Fin 3)) z).symm)
        ((chartAt (EuclideanSpace ℝ (Fin 3)) z).symm ⁻¹' (f '' univ))
        (chartAt (EuclideanSpace ℝ (Fin 3)) z z) at hkpa
      rw [hch] at hkpa
      exact hkpa
    · intro y hy
      change c (k (f (c.symm y))) = y
      rw [hkf (mem_univ _), c.right_inv hy]

theorem hasPLPieceAtlas_of_bicollar {X : Type u} [MetricSpace X] [CompactSpace X]
    (A : ChartedSpace (EuclideanSpace ℝ (Fin 3)) X) (hA : letI := A; HasGroupoid X (plGroupoid 3))
    (Φ : OpenPartialHomeomorph (Torus × ℝ) (EuclideanSpace ℝ (Fin 3)))
    (σ : OpenPartialHomeomorph (Torus × ℝ) X)
    (hΦ : Φ.source = {p | -1 < p.2 ∧ p.2 < 1}) (hσ : σ.source = {p | -1 < p.2 ∧ p.2 < 1})
    (hQ : IsPolyhedron (range fun t => Φ (t, 0))) (τ : C(Torus, X))
    (hτ : ∀ t, τ t = σ (t, 0)) : HasPLPieceAtlas τ := by
  let ψ := Φ.symm.trans σ
  have h0 : ∀ t : Torus, (t, (0 : ℝ)) ∈ σ.source := fun t => by
    rw [hσ]
    exact ⟨by norm_num, by norm_num⟩
  have h0Φ : ∀ t : Torus, (t, (0 : ℝ)) ∈ Φ.source := fun t => by
    rw [hΦ]
    exact ⟨by norm_num, by norm_num⟩
  have hτV : ∀ t, τ t ∈ ψ.target := fun t => by
    rw [hτ]
    refine ⟨σ.map_source (h0 t), ?_⟩
    change σ.symm (σ (t, 0)) ∈ Φ.source
    rw [σ.left_inv (h0 t)]
    exact h0Φ t
  have hψsymm : ∀ t, ψ.symm (τ t) = Φ (t, 0) := fun t => by
    rw [hτ]
    change Φ (σ.symm (σ (t, 0))) = Φ (t, 0)
    rw [σ.left_inv (h0 t)]
  have : Nonempty ψ.symm.source := ⟨⟨τ (1, 1), hτV _⟩⟩
  let c : OpenPartialHomeomorph ψ.target (EuclideanSpace ℝ (Fin 3)) :=
    ψ.symm.isOpenEmbedding_restrict.toOpenPartialHomeomorph _
  have hcs : c.source = univ :=
    IsOpenEmbedding.toOpenPartialHomeomorph_source _ ψ.symm.isOpenEmbedding_restrict
  have hcm : ∀ x, x ∈ c.source := fun x => by
    rw [hcs]
    exact mem_univ x
  have hVc : (ψ.target)ᶜ.Nonempty := by
    by_contra hne
    rw [not_nonempty_iff_eq_empty, compl_empty_iff] at hne
    have hVk : IsCompact ψ.target := by
      rw [hne]
      exact isCompact_univ
    have : CompactSpace ψ.target := isCompact_iff_compactSpace.mp hVk
    have hcomp : IsCompact c.target := by
      rw [← c.image_source_eq_target, hcs]
      exact isCompact_univ.image_of_continuousOn (hcs ▸ c.continuousOn)
    have hne' : c.target.Nonempty := ⟨_, c.map_source (hcm ⟨τ (1, 1), hτV _⟩)⟩
    exact noncompact_univ _ ((IsClopen.eq_univ ⟨hcomp.isClosed, c.open_target⟩ hne') ▸ hcomp)
  have hφpos : ∀ x : ψ.target, x ∈ (univ : Set ψ.target) →
      0 < Metric.infDist (x : X) (ψ.target)ᶜ / 2 := fun x _ =>
    half_pos ((ψ.open_target.isClosed_compl.notMem_iff_infDist_pos hVc).mp fun h => h x.2)
  let := A
  have : HasGroupoid X (plGroupoid 3) := hA
  let := c.singletonChartedSpace hcs
  have : HasGroupoid ψ.target (plGroupoid 3) := c.singleton_hasGroupoid hcs (plGroupoid 3)
  obtain ⟨f, hf, himage, hclose⟩ := exists_isPLHomeomorphInto_image_eq_dist_lt_of_isOpen_three
    (M₁ := ψ.target) (M₂ := X) isOpen_univ (h := Subtype.val)
    (IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal)
    (fun x => Metric.infDist (x : X) (ψ.target)ᶜ / 2)
    (((Metric.continuous_infDist_pt _).comp continuous_subtype_val).div_const 2).continuousOn
    hφpos
  have hfV : ∀ x : ψ.target, f x ∈ ψ.target := fun x => by
    have hx : f x ∈ f '' univ := mem_image_of_mem f (mem_univ x)
    rw [himage] at hx
    obtain ⟨y, -, hy⟩ := hx
    rw [← hy]
    exact y.2
  have hfc : Continuous f := continuousOn_univ.mp hf.continuousOn
  let g₀ : ψ.target → ψ.target := fun x => ⟨f x, hfV x⟩
  have hg₀c : Continuous g₀ := hfc.subtype_mk hfV
  have hg₀i : Function.Injective g₀ := fun x y hxy =>
    injOn_univ.mp hf.injOn (congrArg Subtype.val hxy)
  have hg₀s : Function.Surjective g₀ := fun y => by
    have hy : (y : X) ∈ f '' univ := by
      rw [himage]
      exact ⟨y, mem_univ _, rfl⟩
    obtain ⟨x, -, hx⟩ := hy
    exact ⟨x, Subtype.ext hx⟩
  let g : ψ.target ≃ₜ ψ.target :=
    (Equiv.ofBijective g₀ ⟨hg₀i, hg₀s⟩).toHomeomorphOfContinuousOpen hg₀c
      (isOpenMap_of_continuous_injective (E := EuclideanSpace ℝ (Fin 3)) hg₀c hg₀i)
  obtain ⟨Gh, hGV, -⟩ := exists_homeomorph_extend_of_dist_lt g fun x => hclose x (mem_univ x)
  have hcτ : ∀ t, c.symm (Φ (t, 0)) = ⟨τ t, hτV t⟩ := fun t => by
    rw [← hψsymm t]
    exact c.left_inv (hcm ⟨τ t, hτV t⟩)
  apply hasPLPieceAtlas_of_homeomorph Gh
  refine hasPLPieceAtlas_of_isPLHomeomorphInto A hA
    (isPLHomeomorphInto_comp_symm_of_singleton c hcs hf) hQ ?_ _ ?_
  · rintro _ ⟨t, rfl⟩
    change Φ (t, 0) ∈ c.target
    rw [← hψsymm t]
    exact c.map_source (hcm ⟨τ t, hτV t⟩)
  · rw [← range_comp]
    congr 1
    funext t
    change Gh (τ t) = f (c.symm (Φ (t, 0)))
    rw [hcτ t]
    exact hGV ⟨τ t, hτV t⟩

theorem hasPLPieceAtlas_of_openPartialHomeomorph {X : Type u} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
    (σ : OpenPartialHomeomorph (Torus × ℝ) X) (hσ : σ.source = {p | -1 < p.2 ∧ p.2 < 1})
    (τ : C(Torus, X)) (hτ : ∀ t, τ t = σ (t, 0)) : HasPLPieceAtlas τ := by
  obtain ⟨Φ, hΦ, hQ⟩ := exists_polyhedral_bicollar_model
  have : SecondCountableTopology X :=
    ChartedSpace.secondCountable_of_sigmaCompact (EuclideanSpace ℝ (Fin 3)) X
  have : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin 3)) X
  have := TopologicalSpace.metrizableSpace_of_t3_secondCountable X
  obtain ⟨B, hB⟩ := exists_chartedSpace_hasGroupoid_plGroupoid_three (X := X)
  let := TopologicalSpace.metrizableSpaceMetric X
  exact hasPLPieceAtlas_of_bicollar B hB Φ σ hΦ hσ hQ τ hτ

end GC.Topology

namespace GC.Endpoint
namespace SmoothAssembly
open GC.Topology
universe u
variable {C : CompactCarrier.{u}} {G : TorusGluing C}

theorem hasPLPieceAtlas_torusInPrime (A : SmoothAssembly G)
    {P : ConnectedClosedOrientedManifold.{u} 3} (r : A.Reconstruction P) (i : Fin G.count) :
    HasPLPieceAtlas (A.torusInPrime r i) :=
  hasPLPieceAtlas_of_openPartialHomeomorph (A.primeSeam r i).toOpenPartialHomeomorph
    (A.primeSeam_source r i) (A.torusInPrime r i) fun t => (A.primeSeam_zero r i t).symm

theorem incompressible_iff_of_isTriangulationOrientable (A : SmoothAssembly G)
    {P : ConnectedClosedOrientedManifold.{u} 3} (r : A.Reconstruction P)
    (hO : IsTriangulationOrientable P.Carrier) :
    A.Incompressible r ↔ ∀ i d, ¬ IsCompressingDisk (A.torusInPrime r i) d :=
  A.incompressible_iff_of_hasPLPieceAtlas r (A.hasPLPieceAtlas_torusInPrime r) hO

end SmoothAssembly
end GC.Endpoint
