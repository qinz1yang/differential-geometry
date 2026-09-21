import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Topology.OpenPartialHomeomorph.IsImage
import Mathlib.Geometry.Manifold.Instances.Sphere
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Opens

section

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace PartialDiffeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H H' : Type*} [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F H'}
  {M N : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace H' N] [T2Space N] {n : ℕ∞ω}

theorem image_frontier_of_isCompact (P : PartialDiffeomorph I J M N n)
    {K : Set M} (hK : IsCompact K) (hsrc : K ⊆ P.source) :
    P '' frontier K = frontier (P '' K) := by
  have himg : P.toOpenPartialHomeomorph.IsImage K (P '' K) := by
    apply OpenPartialHomeomorph.IsImage.of_image_eq
    change P '' (P.source ∩ K) = P.target ∩ (P '' K)
    have ht : P '' K ⊆ P.target := by
      rintro y ⟨x, hx, rfl⟩
      exact P.map_source' (hsrc hx)
    rw [inter_eq_right.mpr hsrc, inter_eq_right.mpr ht]
  have hcompact : IsCompact (P '' K) :=
    hK.image_of_continuousOn (P.contMDiffOn_toFun.continuousOn.mono hsrc)
  have hfs : frontier K ⊆ P.source := hK.isClosed.frontier_subset.trans hsrc
  have hft : frontier (P '' K) ⊆ P.target := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hcompact.isClosed.frontier_subset hy
    exact P.map_source' (hsrc hx)
  have h := himg.frontier.image_eq
  change P '' (P.source ∩ frontier K) = P.target ∩ frontier (P '' K) at h
  simpa only [inter_eq_right.mpr hfs, inter_eq_right.mpr hft] using h

end PartialDiffeomorph

end

section

set_option autoImplicit false

noncomputable section

open Set Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.Manifold

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {Z : Type*} [TopologicalSpace Z] [ChartedSpace E3 Z] [T2Space Z]

theorem closure_image_ball_of_partialDiffeomorph
    (b : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 Z ∞)
    (hb : closedBall (0 : E3) 1 ⊆ b.source) :
    closure (b '' ball (0 : E3) 1) = b '' closedBall (0 : E3) 1 := by
  have hcont := b.contMDiffOn_toFun.continuousOn.mono hb
  apply subset_antisymm
  · exact closure_minimal (image_mono ball_subset_closedBall)
      ((isCompact_closedBall (0 : E3) 1).image_of_continuousOn hcont).isClosed
  · have hcont' : ContinuousOn b (closure (ball (0 : E3) 1)) := by
      simpa only [closure_ball _ one_ne_zero] using hcont
    simpa only [closure_ball _ one_ne_zero] using hcont'.image_closure

theorem frontier_image_ball_of_partialDiffeomorph
    (b : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 Z ∞)
    (hb : closedBall (0 : E3) 1 ⊆ b.source) :
    frontier (b '' ball (0 : E3) 1) = b '' sphere (0 : E3) 1 := by
  have hbc := ball_subset_closedBall.trans hb
  have hcl := closure_image_ball_of_partialDiffeomorph b hb
  have ho : IsOpen (b '' ball (0 : E3) 1) := b.toOpenPartialHomeomorph.isOpen_image_of_subset_source isOpen_ball hbc
  rw [frontier, hcl, ho.interior_eq]
  apply subset_antisymm
  · rintro y ⟨⟨z, hz, rfl⟩, hnot⟩
    refine ⟨z, ?_, rfl⟩
    exact le_antisymm hz (not_lt.mp fun h => hnot (mem_image_of_mem b h))
  · rintro y ⟨z, hz, rfl⟩
    have hzc := sphere_subset_closedBall hz
    refine ⟨mem_image_of_mem b hzc, ?_⟩
    rintro ⟨w, hw, heq⟩
    have hwz : w = z := b.toPartialEquiv.injOn (hbc hw) (hb hzc) heq
    subst w
    exact (ne_of_lt hw) hz

theorem image_sphere_eq_frontier_of_ball_complement
    {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M] [T2Space M]
    (b : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 Z ∞)
    (P : PartialDiffeomorph (𝓡 3) (𝓡 3) Z M ∞)
    (hb : closedBall (0 : E3) 1 ⊆ b.source)
    (hK : IsCompact (b '' ball (0 : E3) 1)ᶜ)
    (hP : (b '' ball (0 : E3) 1)ᶜ ⊆ P.source) :
    P '' (b '' sphere (0 : E3) 1) = frontier (P '' (b '' ball (0 : E3) 1)ᶜ) := by
  rw [← P.image_frontier_of_isCompact hK hP, frontier_compl,
    frontier_image_ball_of_partialDiffeomorph b hb]

end DifferentialGeometry.Topology.Manifold

end

end
