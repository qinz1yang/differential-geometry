import DifferentialGeometry.Topology.Sequences.EventualDiagonal
import DifferentialGeometry.Topology.Exhaustion
import Mathlib.Geometry.Manifold.LocalDiffeomorph

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace DifferentialGeometry.PartialDiffeomorph

variable {𝕜 E F H G X : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace X] [ChartedSpace H X]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F G}
  {r : ℕ∞ω}

private def restrictToOpen {Y : Type*} [TopologicalSpace Y] [ChartedSpace G Y]
    (φ : _root_.PartialDiffeomorph I J X Y r) (U : Set X) (hU : IsOpen U) :
    _root_.PartialDiffeomorph I J X Y r where
  __ := φ.toOpenPartialHomeomorph.restrOpen U hU
  contMDiffOn_toFun := φ.contMDiffOn_toFun.mono inter_subset_left
  contMDiffOn_invFun := φ.contMDiffOn_invFun.mono inter_subset_left

theorem exists_exhausting_restrictions
    {Y : ℕ → Type*} [∀ i, TopologicalSpace (Y i)] [∀ i, ChartedSpace G (Y i)]
    {U : ℕ → Set X} (hU : CheegerGromovCompactness.ExhaustsByOpen U)
    (φ : ℕ → ∀ i, _root_.PartialDiffeomorph I J X (Y i) r)
    (p : X) (q : ∀ i, Y i) (P : ℕ → ℕ → Prop)
    (hstage : ∀ k, ∀ᶠ i in atTop,
      U k ⊆ (φ k i).source ∧ φ k i p = q i ∧ P k i) :
    ∃ j : ℕ → ℕ, Tendsto j atTop atTop ∧
      ∃ ψ : ∀ i, _root_.PartialDiffeomorph I J X (Y i) r,
        (∀ i, (ψ i : X → Y i) = φ (j i) i) ∧
        (∀ i, ((ψ i).symm : Y i → X) = (φ (j i) i).symm) ∧
        (∀ i, (ψ i).source = (φ (j i) i).source ∩ U (j i)) ∧
        (∀ i, (ψ i).target = φ (j i) i '' (ψ i).source) ∧
        (∀ᶠ i in atTop, (ψ i).source = U (j i) ∧
          p ∈ (ψ i).source ∧ ψ i p = q i ∧ P (j i) i) ∧
        ∀ K : Set X, IsCompact K → ∀ᶠ i in atTop, K ⊆ (ψ i).source := by
  obtain ⟨j, hj, htail⟩ := Filter.exists_tendsto_atTop_eventually_diagonal hstage
  let ψ := fun i => restrictToOpen (φ (j i) i) (U (j i)) (hU.isOpen (j i))
  have hsource : ∀ᶠ i in atTop, (ψ i).source = U (j i) :=
    htail.mono fun i hi => inter_eq_right.mpr hi.1
  have hcompact : ∀ K : Set X, IsCompact K →
      ∀ᶠ i in atTop, K ⊆ (ψ i).source := by
    intro K hK
    obtain ⟨k, hk⟩ := hU.subset K hK
    filter_upwards [hsource, hj.eventually_ge_atTop k] with i hsi hji
    rw [hsi]
    exact hk (j i) hji
  refine ⟨j, hj, ψ, fun _ => rfl, fun _ => rfl, fun _ => rfl, ?_, ?_, hcompact⟩
  · intro i
    exact (ψ i).toPartialEquiv.image_source_eq_target.symm
  · filter_upwards [htail, hsource, hcompact {p} isCompact_singleton] with i hi hs hp
    exact ⟨hs, hp (mem_singleton p), hi.2.1, hi.2.2⟩

end DifferentialGeometry.PartialDiffeomorph
