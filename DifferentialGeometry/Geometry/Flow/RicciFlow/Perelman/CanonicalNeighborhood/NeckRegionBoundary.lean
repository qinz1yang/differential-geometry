import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornGeometry
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.OpenPartialHomeomorph.IsImage
import Mathlib.Topology.Order.DenselyOrdered

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff Topology

section ImageFrontier

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {H : Type*} [TopologicalSpace H]
variable {H' : Type*} [TopologicalSpace H']
variable {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E' H'}
variable {P : Type*} [TopologicalSpace P] [ChartedSpace H P]
variable {Q : Type*} [TopologicalSpace Q] [ChartedSpace H' Q]
variable {n : WithTop ℕ∞}

private theorem image_frontier_of_partialDiffeomorph (Φ : PartialDiffeomorph I J P Q n)
    {s : Set P} (hs : s ⊆ Φ.source) (hcs : IsClosed s) (hci : IsClosed (Φ '' s)) :
    Φ '' frontier s = frontier (Φ '' s) := by
  have hImage : Φ.toOpenPartialHomeomorph.IsImage s (Φ '' s) := by
    apply OpenPartialHomeomorph.IsImage.of_image_eq
    change Φ '' (Φ.source ∩ s) = Φ.target ∩ Φ '' s
    have ht : Φ '' s ⊆ Φ.target := by
      rintro y ⟨x, hx, rfl⟩
      exact Φ.map_source' (hs hx)
    rw [inter_eq_right.mpr hs, inter_eq_right.mpr ht]
  have hs0 : frontier s ⊆ Φ.source :=
    fun x hx => hs (hcs.closure_eq ▸ frontier_subset_closure hx)
  have ht0 : frontier (Φ '' s) ⊆ Φ '' s :=
    fun y hy => hci.closure_eq ▸ frontier_subset_closure hy
  have ht : frontier (Φ '' s) ⊆ Φ.target := by
    rintro y hy
    obtain ⟨x, hx, rfl⟩ := ht0 hy
    exact Φ.map_source' (hs hx)
  have h := hImage.frontier.image_eq
  change Φ '' (Φ.source ∩ frontier s) = Φ.target ∩ frontier (Φ '' s) at h
  simpa only [inter_eq_right.mpr hs0, inter_eq_right.mpr ht] using h

end ImageFrontier

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}

def StrongNeck.region {eps : ℝ} {x : M} {t : ℝ} (nk : StrongNeck S eps x t) : Set M :=
  nk.map '' (Set.univ ×ˢ Set.Icc (-10) 10)

theorem StrongNeck.frontier_region {eps : ℝ} {x : M} {t : ℝ} (nk : StrongNeck S eps x t) :
    frontier nk.region = nk.map '' (Set.univ ×ˢ ({-10, 10} : Set ℝ)) := by
  have h11 : (10 : ℝ) < eps⁻¹ := by
    have h : (1 / 11 : ℝ)⁻¹ < eps⁻¹ :=
      (inv_lt_inv₀ (by norm_num : (0 : ℝ) < 1 / 11) nk.eps_pos).2 nk.eps_small
    norm_num at h
    linarith
  have hsub : Set.univ ×ˢ Set.Icc (-10 : ℝ) 10 ⊆ nk.map.source := by
    intro y hy
    exact nk.domain ⟨trivial, ⟨by linarith [hy.2.1], by linarith [hy.2.2]⟩⟩
  have hclosed : IsClosed (Set.univ ×ˢ Set.Icc (-10 : ℝ) 10 : Set Cylinder) :=
    isClosed_univ.prod isClosed_Icc
  have hcompact : IsCompact (Set.univ ×ˢ Set.Icc (-10 : ℝ) 10 : Set Cylinder) :=
    isCompact_univ.prod isCompact_Icc
  have hclosedImage : IsClosed (nk.map '' (Set.univ ×ˢ Set.Icc (-10 : ℝ) 10)) :=
    (hcompact.image_of_continuousOn
      (nk.map.contMDiffOn_toFun.continuousOn.mono hsub)).isClosed
  have h := image_frontier_of_partialDiffeomorph nk.map hsub hclosed hclosedImage
  rw [frontier_univ_prod_eq, frontier_Icc (by norm_num : (-10 : ℝ) ≤ 10)] at h
  exact h.symm

def StrongNeck.toLocalNeck {eps : ℝ} {x : M} {t : ℝ} (nk : StrongNeck S eps x t) :
    LocalNeck S eps x t nk.region where
  strong := nk
  region_eq := rfl
  boundary_eq := nk.frontier_region

theorem canonicalAlternative_neck_of_strongNeck {eps : ℝ} {x : M} {t : ℝ} {C : ℝ}
    (nk : StrongNeck S eps x t) :
    Nonempty (CanonicalAlternative S eps C x t nk.region) :=
  ⟨CanonicalAlternative.neck nk.toLocalNeck⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
