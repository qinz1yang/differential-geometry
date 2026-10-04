import DifferentialGeometry.Topology.Manifold.Submersion
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

/-! Honest compact-disc local product restrictions of the original smooth submersion. -/

set_option autoImplicit false
noncomputable section
open Set Metric Topology
open scoped ContDiff Manifold
namespace GC.MetricGeometry
universe u v

structure LocalCompactProductRestriction {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N] (F : Type u) [NormedAddCommGroup F]
    (p : M → N) (z : M) where
  centre : F
  radius : ℝ
  radius_pos : 0 < radius
  target : Set N
  target_open : IsOpen target
  target_mem : p z ∈ target
  source : Set M
  coordinates : OpenPartialHomeomorph M (N × F)
  source_eq : source = coordinates.source ∩
    coordinates ⁻¹' (target ×ˢ closedBall centre radius)
  coordinates_projection : EqOn (fun y => (coordinates y).1) p coordinates.source
  source_mem : z ∈ source
  mapsTo : MapsTo p source target
  fibre_compact : IsCompact (closedBall centre radius)
  productHomeomorph : source ≃ₜ target × closedBall centre radius
  projection_equation : ∀ y : source, (productHomeomorph y).1.val = p y.val

namespace LocalCompactProductRestriction
variable {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
  {F : Type u} [NormedAddCommGroup F] {p : M → N} {z : M}

def toTarget (R : LocalCompactProductRestriction F p z) : R.source → R.target :=
  fun y => ⟨p y, R.mapsTo y.property⟩

theorem isProperMap (R : LocalCompactProductRestriction F p z) : IsProperMap R.toTarget := by
  let : CompactSpace (closedBall R.centre R.radius) :=
    isCompact_iff_compactSpace.mp R.fibre_compact
  have heq : R.toTarget = Prod.fst ∘ R.productHomeomorph := by
    funext y
    exact Subtype.ext (R.projection_equation y).symm
  rw [heq]
  exact isProperMap_fst_of_compactSpace.comp R.productHomeomorph.isProperMap

theorem surjective (R : LocalCompactProductRestriction F p z) :
    Function.Surjective R.toTarget := by
  intro y
  let n : closedBall R.centre R.radius := ⟨R.centre, mem_closedBall_self R.radius_pos.le⟩
  refine ⟨R.productHomeomorph.symm (y, n), ?_⟩
  apply Subtype.ext
  change p (R.productHomeomorph.symm (y, n)).val = y.val
  rw [← R.projection_equation, R.productHomeomorph.apply_symm_apply]

end LocalCompactProductRestriction

variable {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
  {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem exists_localCompactProductRestriction_of_localProjection
    (p : M → N) (z : M) (e : OpenPartialHomeomorph M (N × F)) (hz : z ∈ e.source)
    (he : EqOn (fun y => (e y).1) p e.source) :
    Nonempty (LocalCompactProductRestriction F p z) := by
  have henhds := e.open_target.mem_nhds (e.map_source hz)
  obtain ⟨V, W, hV, hzV, hW, hzW, hVW⟩ := mem_nhds_prod_iff'.mp henhds
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hW.mem_nhds hzW)
  let K : Set F := closedBall (e z).2 (r / 2)
  have hK : K ⊆ W := by
    apply Subset.trans (closedBall_subset_ball (by linarith)) hball
  have hVK : V ×ˢ K ⊆ e.target := fun y hy => hVW ⟨hy.1, hK hy.2⟩
  let D : Set M := e.source ∩ e ⁻¹' (V ×ˢ K)
  have hDS : D ⊆ e.source := fun y hy => hy.1
  have himage : e '' D = V ×ˢ K := by
    apply Subset.antisymm
    · rintro y ⟨x, hx, rfl⟩
      exact hx.2
    · intro y hy
      exact ⟨e.symm y, ⟨e.map_target (hVK hy), by
          change e (e.symm y) ∈ V ×ˢ K
          rw [e.right_inv (hVK hy)]
          exact hy⟩,
        e.right_inv (hVK hy)⟩
  let E : D ≃ₜ V × K :=
    (e.homeomorphOfImageSubsetSource hDS himage).trans (Homeomorph.Set.prod V K)
  have hmap : MapsTo p D V := by
    intro y hy
    rw [← he hy.1]
    exact hy.2.1
  refine ⟨{
    centre := (e z).2
    radius := r / 2
    radius_pos := by linarith
    target := V
    target_open := hV
    target_mem := by rwa [← he hz]
    source := D
    coordinates := e
    source_eq := rfl
    coordinates_projection := he
    source_mem := ⟨hz, hzV, mem_closedBall_self (by linarith)⟩
    mapsTo := hmap
    fibre_compact := isCompact_closedBall _ _
    productHomeomorph := E
    projection_equation := ?_ }⟩
  intro y
  exact he y.property.1

theorem exists_localCompactProductRestriction_of_isSubmersionAt
    {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
    {k : ℕ} {Z : Set H} [ChartedSpace (Fin k → ℝ) Z]
    (Ω : TopologicalSpace.Opens H) (p : Ω → Z) (z : Ω)
    (hp : _root_.Manifold.IsSubmersionAt 𝓘(ℝ, H) 𝓘(ℝ, Fin k → ℝ) ∞ p z) :
    ∃ (F : Type u) (_instNorm : NormedAddCommGroup F) (_instSpace : NormedSpace ℝ F)
      (_instFinite : FiniteDimensional ℝ F), Nonempty (LocalCompactProductRestriction F p z) := by
  rcases hp with ⟨F, instNorm, instSpace, h⟩
  let A := h.equiv
  let φ := h.domChart
  let ψ := h.codChart
  let inF : F →L[ℝ] H := A.symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inr ℝ (Fin k → ℝ) F)
  have hinF : Function.Injective inF := by
    intro a b hab
    have hh := A.symm.injective hab
    exact congrArg Prod.snd hh
  let : FiniteDimensional ℝ F := FiniteDimensional.of_injective inF.toLinearMap hinF
  have hwritten (y : Ω) (hy : y ∈ φ.source) : ψ (p y) = (A (φ y)).1 := by
    have hh := h.writtenInCharts
      ((φ.extend 𝓘(ℝ, H)).map_source (by simpa using hy))
    simpa [Function.comp_def, OpenPartialHomeomorph.extend, φ, ψ, A,
      h.domChart.left_inv hy] using hh
  let e₀ : OpenPartialHomeomorph Ω ((Fin k → ℝ) × F) :=
    φ.trans A.toHomeomorph.toOpenPartialHomeomorph
  let e : OpenPartialHomeomorph Ω (Z × F) :=
    e₀.trans (ψ.symm.prod (OpenPartialHomeomorph.refl F))
  have hzφ : z ∈ φ.source := h.mem_domChart_source
  have hzψ : p z ∈ ψ.source := h.mem_codChart_source
  have hz : z ∈ e.source := by
    change z ∈ e₀.source ∧ e₀ z ∈ (ψ.symm.prod (OpenPartialHomeomorph.refl F)).source
    refine ⟨?_, ?_⟩
    · simpa [e₀, PartialEquiv.trans_source] using hzφ
    · change (A (φ z)).1 ∈ ψ.target ∧ (A (φ z)).2 ∈ Set.univ
      rw [← hwritten z hzφ]
      exact ⟨ψ.map_source hzψ, mem_univ _⟩
  have he : EqOn (fun y => (e y).1) p e.source := by
    intro y hy
    have hyφ : y ∈ φ.source := hy.1.1
    have hyp : p y ∈ ψ.source := h.source_subset_preimage_source hyφ
    change ψ.symm (A (φ y)).1 = p y
    rw [← hwritten y hyφ]
    exact ψ.left_inv hyp
  exact ⟨F, instNorm, instSpace, inferInstance,
    exists_localCompactProductRestriction_of_localProjection p z e hz he⟩

end GC.MetricGeometry
