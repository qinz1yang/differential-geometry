import DifferentialGeometry.Geometry.MinimalSurface.ExteriorDiskArea
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.MorreyAreaPositivity
import DifferentialGeometry.Geometry.Measure.Area.OpenTarget

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology Set MeasureTheory
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.MinimalSurface

private theorem diskArea_eq_of_inner_eq_on_range
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    (g h : SmoothRiemannianMetric 𝓘(ℝ, E) M) (u : closedDisk → M)
    (heq : ∀ x ∈ Set.range u, g.inner x = h.inner x) :
    riemannianDiskArea g u = riemannianDiskArea h u := by
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  unfold riemannianAreaDensity tangentTwoJacobian
  rw [heq (diskExtension u z) ⟨diskRetraction z, rfl⟩]

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [T3Space M]

/-- An actual Morrey disk in an open target compares with every original exterior
disk when the auxiliary metric agrees with the original metric on the exterior. -/
theorem area_le_exteriorDisk_of_isMorreyDisk_open
    (g : SmoothRiemannianMetric (𝓡 3) M) (U : TopologicalSpace.Opens M)
    (G : SmoothRiemannianMetric (𝓡 3) U) {W : Set M}
    (hWU : W ⊆ (U : Set M))
    (hmetric : ∀ x : U, (x : M) ∈ W → G.inner x = (g.restrictOpen U).inner x)
    {γ : freeLoop U} {u : C(closedDisk, U)} (hu : IsMorreyDisk G γ u)
    (huW : ∀ z : closedDisk, (u z : M) ∈ W)
    {v : C(closedDisk, M)}
    (hv : isExteriorSpanningDisk W
      ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)).comp γ) v) :
    riemannianDiskArea g (Subtype.val ∘ u) ≤ riemannianDiskArea g v := by
  let vU : C(closedDisk, U) :=
    ⟨fun z => ⟨v z, hWU (hv.2.2.2.1 (mem_range_self z))⟩,
      v.continuous.subtype_mk _⟩
  have hvU : DiskSmoothUpToBoundary (E := EuclideanSpace ℝ (Fin 3)) vU := by
    obtain ⟨V, hV, _⟩ := hv.2.2.2.2.2
    intro z hz
    apply (contMDiffWithinAt_subtypeVal_comp_iff U (diskExtension vU)
      (Metric.closedBall (0 : ℂ) 1) z).mp
    exact hV.smoothUpToBoundary z hz
  have htrace : diskTrace vU = γ := by
    ext θ
    exact congrArg (fun f : freeLoop M => f θ) hv.1
  have hareaU : riemannianDiskArea G u = riemannianDiskArea g (Subtype.val ∘ u) := by
    rw [diskArea_eq_of_inner_eq_on_range G (g.restrictOpen U) u]
    · exact riemannianDiskArea_restrictOpen g U u
    · rintro _ ⟨z, rfl⟩
      exact hmetric (u z) (huW z)
  have hareaV : riemannianDiskArea G vU = riemannianDiskArea g v := by
    rw [diskArea_eq_of_inner_eq_on_range G (g.restrictOpen U) vU]
    · exact riemannianDiskArea_restrictOpen g U vU
    · rintro _ ⟨z, rfl⟩
      exact hmetric (vU z) (hv.2.2.2.1 (mem_range_self z))
  rw [← hareaU, ← hareaV]
  exact hu.minimizesSmooth vU hvU htrace

/-- Area-preserving exact-trace replacement of the same confined Morrey disk
attains the positive exterior infimum for the original metric. -/
theorem isExteriorSpanningDisk.attains_positive_leastExteriorDiskArea_of_morrey_open
    (g : SmoothRiemannianMetric (𝓡 3) M) (U : TopologicalSpace.Opens M)
    (G : SmoothRiemannianMetric (𝓡 3) U) {W : Set M}
    (hWU : W ⊆ (U : Set M))
    (hmetric : ∀ x : U, (x : M) ∈ W → G.inner x = (g.restrictOpen U).inner x)
    {γ : freeLoop U} {u : C(closedDisk, U)} (hu : IsMorreyDisk G γ u)
    (hγ : IsSmoothEmbeddedLoop (E := EuclideanSpace ℝ (Fin 3)) γ)
    (huW : ∀ z : closedDisk, (u z : M) ∈ W)
    {q : C(closedDisk, M)}
    (hq : isExteriorSpanningDisk W
      ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)).comp γ) q)
    (harea : riemannianDiskArea g q = riemannianDiskArea g (Subtype.val ∘ u)) :
    riemannianDiskArea g q = leastExteriorDiskArea g W
      ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)).comp γ) ∧
    0 < leastExteriorDiskArea g W
      ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)).comp γ) := by
  have heq : riemannianDiskArea g q = leastExteriorDiskArea g W
      ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)).comp γ) := by
    apply le_antisymm
    · apply le_csInf (Set.Nonempty.image _ ⟨q, hq⟩)
      rintro _ ⟨v, hv, rfl⟩
      rw [harea]
      exact area_le_exteriorDisk_of_isMorreyDisk_open g U G hWU hmetric hu huW hv
    · exact leastExteriorDiskArea_le g W _ q hq
  refine ⟨heq, ?_⟩
  rw [← heq, harea, ← riemannianDiskArea_restrictOpen g U u,
    ← diskArea_eq_of_inner_eq_on_range G (g.restrictOpen U) u]
  · exact hu.area_pos hγ
  · rintro _ ⟨z, rfl⟩
    exact hmetric (u z) (huW z)

end DifferentialGeometry.Geometry.MinimalSurface
