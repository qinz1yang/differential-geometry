import DifferentialGeometry.Geometry.Collapse.SublevelCore.F5aApplications
import DifferentialGeometry.Topology.Manifold.OpenEmbedding
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.OpenCodRestrict

/-!
# The compact LC38 sublevel on the actual compact model

An equal-dimensional smooth embedding of a nonempty compact manifold into a connected manifold
is a diffeomorphism. The compact packet's strict radial bound makes every relevant sublevel open
and equal to the whole target. Its inherited charts and the displayed diffeomorphism use that
same sublevel and the original embedding, including every point of the compact model.
-/

set_option autoImplicit false

noncomputable section

open Set TopologicalSpace
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse

variable {E : Type*} [instE : NormedAddCommGroup E] [instER : NormedSpace ℝ E]
  [instEF : FiniteDimensional ℝ E]
  {H : Type*} [instH : TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [instIB : I.Boundaryless]
  {N M : Type*} [instN : TopologicalSpace N] [instNC : ChartedSpace H N]
  [instNM : IsManifold I ∞ N] [instNCompact : CompactSpace N] [instNNonempty : Nonempty N]
  [instM : TopologicalSpace M] [instMC : ChartedSpace H M] [instMM : IsManifold I ∞ M]
  [instMConnected : ConnectedSpace M] [instMT2 : T2Space M]

theorem exists_compact_model_diffeomorph (j : N → M) (hj : Manifold.IsSmoothEmbedding I I ∞ j) :
    ∃ d : Diffeomorph I I N M ∞, ∀ x, d x = j x := by
  have hloc := DifferentialGeometry.Topology.Manifold.isLocalDiffeomorph_of_injective_mfderiv
    j hj.contMDiff (hj.isImmersion.mfderiv_injective (by simp)) rfl
  have hrange : range j = univ := IsClopen.eq_univ
    ⟨by simpa only [image_univ] using
      (isCompact_univ.image hj.contMDiff.continuous).isClosed,
      hloc.isOpenMap.isOpen_range⟩ (Set.range_nonempty j)
  have hsurj : Function.Surjective j := Set.range_eq_univ.mp hrange
  exact ⟨hloc.diffeomorphOfBijective ⟨hj.isEmbedding.injective, hsurj⟩, fun x => rfl⟩

theorem lc38_compact_sublevel_diffeomorph (j : N → M)
    (hj : Manifold.IsSmoothEmbedding I I ∞ j) {η : M → ℝ}
    (hη : ∀ x, η x < 1 / 5) {ρ : ℝ} (hρ : 1 / 5 ≤ ρ) :
    ∃ hA : IsOpen {x : M | η x ≤ ρ},
      let A : Opens M := ⟨{x : M | η x ≤ ρ}, hA⟩
      ∃ d : Diffeomorph I I N A ∞,
        (∀ x, (d x).val = j x) ∧ (A : Set M) = univ := by
  have hset : {x : M | η x ≤ ρ} = univ :=
    sublevel_eq_univ_of_lt_fifth hη hρ
  have hA : IsOpen {x : M | η x ≤ ρ} := hset ▸ isOpen_univ
  let A : Opens M := ⟨{x : M | η x ≤ ρ}, hA⟩
  obtain ⟨d, hd⟩ := exists_compact_model_diffeomorph j hj
  have hmem (x : N) : d x ∈ A := (hη (d x)).le.trans hρ
  have hloc : IsLocalDiffeomorph I I ∞ (fun x => (⟨d x, hmem x⟩ : A)) :=
    fun x => DifferentialGeometry.isLocalDiffeomorphAt_subtypeCodRestrict hmem
      (d.isLocalDiffeomorph x)
  have hbij : Function.Bijective (fun x => (⟨d x, hmem x⟩ : A)) := by
    constructor
    · intro x y hxy
      exact d.injective (congrArg Subtype.val hxy)
    · intro y
      refine ⟨d.symm y.val, Subtype.ext (d.apply_symm_apply y.val)⟩
  exact ⟨hA, hloc.diffeomorphOfBijective hbij, hd, hset⟩

end DifferentialGeometry.Geometry.Collapse
