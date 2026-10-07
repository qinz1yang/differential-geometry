import Mathlib.Geometry.Manifold.LocalDiffeomorph
import DifferentialGeometry.Topology.FirstExit

set_option autoImplicit false
noncomputable section

open Set Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.PartialDiffeomorph

variable {E E' H H' X Y : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'}
  [TopologicalSpace X] [ChartedSpace H X]
  [TopologicalSpace Y] [ChartedSpace H' Y]

/-- A C1 path leaving a closed image admits a C1 lift up to its first exit.
The inverse is needed only on the target of the supplied finite-order partial
diffeomorphism. A path starting on the frontier may have exit time `a`. -/
theorem exists_contMDiffOn_first_exit_lift_of_closed_image
    (F : _root_.PartialDiffeomorph I J X Y 1)
    (K : Set X) (hsource : K ⊆ F.source) (hclosed : IsClosed ((F : X → Y) '' K))
    (γ : ℝ → Y) {a b : ℝ}
    (hγ : ContMDiffOn 𝓘(ℝ) J 1 γ (Icc a b))
    (hstart : γ a ∈ (F : X → Y) '' K)
    (hexit : ¬ MapsTo γ (Icc a b) ((F : X → Y) '' K)) :
    ∃ (t : ℝ) (β : ℝ → X), t ∈ Ico a b ∧
      ContMDiffOn 𝓘(ℝ) I 1 β (Icc a t) ∧
      EqOn ((F : X → Y) ∘ β) γ (Icc a t) ∧
      MapsTo β (Icc a t) K ∧ MapsTo β (Ico a t) (interior K) ∧
      β t ∈ frontier K ∧ (γ a ∈ (F : X → Y) '' interior K → a < t) := by
  obtain ⟨t, ht, hstay, hbefore, hfront, hstrict⟩ :=
    DifferentialGeometry.exists_first_exit_frontier_Icc_of_mem_of_not_mapsTo
      hclosed hγ.continuousOn hstart hexit
  have himageTarget : (F : X → Y) '' K ⊆ F.target := by
    rintro y ⟨x, hx, rfl⟩
    exact F.map_source' (hsource hx)
  let β : ℝ → X := (F.symm : Y → X) ∘ γ
  have hβ : ContMDiffOn 𝓘(ℝ) I 1 β (Icc a t) :=
    F.symm.contMDiffOn_toFun.comp
      (hγ.mono (Icc_subset_Icc le_rfl ht.2.le))
      (fun s hs => himageTarget (hstay hs))
  have hβeq : EqOn ((F : X → Y) ∘ β) γ (Icc a t) := by
    intro s hs
    exact F.right_inv' (himageTarget (hstay hs))
  have hβK : MapsTo β (Icc a t) K := by
    intro s hs
    obtain ⟨x, hx, hFx⟩ := hstay hs
    change (F.symm : Y → X) (γ s) ∈ K
    have hleft : (F.symm : Y → X) ((F : X → Y) x) = x :=
      F.left_inv' (hsource hx)
    rw [← hFx, hleft]
    exact hx
  have himageInterior : (F : X → Y) '' interior K ⊆
      interior ((F : X → Y) '' K) :=
    interior_maximal (image_mono interior_subset)
      (F.toOpenPartialHomeomorph.isOpen_image_of_subset_source isOpen_interior
        (interior_subset.trans hsource))
  have hinverseInterior :
      F.source ∩ (F : X → Y) ⁻¹' interior ((F : X → Y) '' K) ⊆ interior K := by
    apply interior_maximal
    · rintro x ⟨hx, hFx⟩
      obtain ⟨y, hy, hFy⟩ := interior_subset hFx
      have hxy : x = y :=
        F.toOpenPartialHomeomorph.injOn hx (hsource hy) hFy.symm
      exact hxy.symm ▸ hy
    · exact F.toOpenPartialHomeomorph.isOpen_inter_preimage isOpen_interior
  refine ⟨t, β, ht, hβ, hβeq, hβK, ?_, ?_, ?_⟩
  · intro s hs
    have hscc : s ∈ Icc a t := ⟨hs.1, hs.2.le⟩
    apply hinverseInterior
    refine ⟨hsource (hβK hscc), ?_⟩
    change F (β s) ∈ interior ((F : X → Y) '' K)
    have hFs : F (β s) = γ s := hβeq hscc
    rw [hFs]
    exact hbefore hs
  · refine ⟨subset_closure (hβK ⟨ht.1, le_rfl⟩), ?_⟩
    intro hβint
    apply hfront.2
    have hFt := himageInterior ⟨β t, hβint, rfl⟩
    have hFtEq : F (β t) = γ t := hβeq ⟨ht.1, le_rfl⟩
    rwa [hFtEq] at hFt
  · exact fun ha => hstrict (himageInterior ha)

end DifferentialGeometry.Topology.PartialDiffeomorph
