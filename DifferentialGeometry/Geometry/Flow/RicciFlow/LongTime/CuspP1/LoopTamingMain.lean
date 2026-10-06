import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.LoopTamingModel
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.LoopTamingTransport

set_option autoImplicit false

/-!
# Taming finitely many bicollared tori at once (LT-P2)

`ι × Torus` version of `hasPLPieceAtlas_of_bicollar`, `hasPLPieceAtlas_of_openPartialHomeomorph`
and `hasPLPresentation_of_hasPLPieceAtlas`. The proof of the bicollar step is that of
`TorusCut/Taming` with the torus replaced by `ι × Torus`.
-/

noncomputable section
open Set Topology
open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.Topology.PiecewiseLinear

namespace GC.LongTime.CuspP1
open GC.Topology
universe u

theorem plPieceAtlas_of_bicollar_family_LTP2 {ι : Type} [TopologicalSpace ι] [Nonempty ι]
    {X : Type u} [MetricSpace X] [CompactSpace X]
    (A : ChartedSpace (EuclideanSpace ℝ (Fin 3)) X) (hA : letI := A; HasGroupoid X (plGroupoid 3))
    (Φ : OpenPartialHomeomorph ((ι × Torus) × ℝ) (EuclideanSpace ℝ (Fin 3)))
    (σ : OpenPartialHomeomorph ((ι × Torus) × ℝ) X)
    (hΦ : Φ.source = {p | -1 < p.2 ∧ p.2 < 1}) (hσ : σ.source = {p | -1 < p.2 ∧ p.2 < 1})
    (hQ : IsPolyhedron (range fun t => Φ (t, 0))) (τ : ι × Torus → X)
    (hτ : ∀ t, τ t = σ (t, 0)) :
    ∃ A : ChartedSpace (EuclideanSpace ℝ (Fin 3)) X,
      letI := A
      HasGroupoid X (plGroupoid 3) ∧
        ∃ N : ℕ, Nonempty (PLPieceIn (EuclideanSpace ℝ (Fin N)) 3 X (range τ)) := by
  let ψ := Φ.symm.trans σ
  have h0 : ∀ t : ι × Torus, (t, (0 : ℝ)) ∈ σ.source := fun t => by
    rw [hσ]
    exact ⟨by norm_num, by norm_num⟩
  have h0Φ : ∀ t : ι × Torus, (t, (0 : ℝ)) ∈ Φ.source := fun t => by
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
  have : Nonempty ψ.symm.source := ⟨⟨τ (Classical.arbitrary _), hτV _⟩⟩
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
    have hne' : c.target.Nonempty := ⟨_, c.map_source (hcm ⟨τ (Classical.arbitrary _), hτV _⟩)⟩
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
  refine plPieceAtlas_of_homeomorph_set_LTP2 Gh (Y' := range fun t => Gh (τ t)) ?_ ?_
  · ext x
    simp only [mem_preimage, mem_range]
    constructor
    · rintro ⟨t, ht⟩
      exact ⟨t, Gh.injective ht⟩
    · rintro ⟨t, rfl⟩
      exact ⟨t, rfl⟩
  refine plPieceAtlas_of_isPLHomeomorphInto_set_LTP2 A hA
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

theorem hasPLPieceAtlas_of_openPartialHomeomorph_family_LTP2 {ι : Type} [Finite ι] [Nonempty ι]
    [TopologicalSpace ι] [DiscreteTopology ι] {X : Type u} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
    (σ : OpenPartialHomeomorph ((ι × Torus) × ℝ) X) (hσ : σ.source = {p | -1 < p.2 ∧ p.2 < 1})
    (τ : ι × Torus → X) (hτ : ∀ x, τ x = σ (x, 0)) :
    ∃ A : ChartedSpace (EuclideanSpace ℝ (Fin 3)) X,
      letI := A
      HasGroupoid X (plGroupoid 3) ∧
        ∃ N : ℕ, Nonempty (PLPieceIn (EuclideanSpace ℝ (Fin N)) 3 X (range τ)) := by
  obtain ⟨Φ, hΦ, hQ⟩ := exists_polyhedral_bicollar_model_family_LTP2 (ι := ι)
  have : SecondCountableTopology X :=
    ChartedSpace.secondCountable_of_sigmaCompact (EuclideanSpace ℝ (Fin 3)) X
  have : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin 3)) X
  have := TopologicalSpace.metrizableSpace_of_t3_secondCountable X
  obtain ⟨B, hB⟩ := exists_chartedSpace_hasGroupoid_plGroupoid_three (X := X)
  let := TopologicalSpace.metrizableSpaceMetric X
  exact plPieceAtlas_of_bicollar_family_LTP2 B hB Φ σ hΦ hσ hQ τ hτ

theorem hasPLPresentation_of_openPartialHomeomorph_family_LTP2 {ι : Type} [Finite ι] [Nonempty ι]
    [TopologicalSpace ι] [DiscreteTopology ι] {X : Type u} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
    (σ : OpenPartialHomeomorph ((ι × Torus) × ℝ) X) (hσ : σ.source = {p | -1 < p.2 ∧ p.2 < 1})
    (τ : ι × Torus → X) (hτ : ∀ x, τ x = σ (x, 0)) (hO : IsTriangulationOrientable X) :
    ∃ (N : ℕ) (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N)))
      (_ : Finite K.faces) (h : K.space ≃ₜ X), IsCombinatorialManifold 3 K ∧ IsOrientable 3 K ∧
        IsPolyhedron (((↑) : K.space → EuclideanSpace ℝ (Fin N)) '' (h ⁻¹' range τ)) := by
  haveI : Nonempty X := ⟨τ (Classical.arbitrary _)⟩
  exact plPresentation_of_plPieceAtlas_set_LTP2
    (hasPLPieceAtlas_of_openPartialHomeomorph_family_LTP2 σ hσ τ hτ) hO

end GC.LongTime.CuspP1
