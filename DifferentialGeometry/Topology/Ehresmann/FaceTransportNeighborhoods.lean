import DifferentialGeometry.Topology.Ehresmann.BandMargin
import Mathlib.Topology.Compactness.LocallyCompact

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Topology.Ehresmann

variable {E F H Y : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace Y] [ChartedSpace H Y] [IsManifold I ∞ Y]

/-- The actual compact face trace has compact neighbourhoods inside both spatial rank sets. -/
theorem exists_compact_faceTrace_rankNeighborhoods
    (h : Y × ℝ → F) (T : Y × ℝ → ℝ)
    (hh : ContMDiff (I.prod 𝓘(ℝ)) 𝓘(ℝ, F) ∞ h)
    (hT : ContMDiff (I.prod 𝓘(ℝ)) 𝓘(ℝ) ∞ T) (a : F) (c ε : ℝ) (hε : 0 < ε)
    (hreg : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ y, h (y, τ) = a → T (y, τ) ≤ c + ε →
      Surjective (mfderiv I 𝓘(ℝ, F) (fun z => h (z, τ)) y))
    (hface : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ y, h (y, τ) = a → |T (y, τ) - c| < ε →
      Surjective (mfderiv I 𝓘(ℝ, F × ℝ) (fun z => (h (z, τ), T (z, τ))) y))
    {Q : Set Y} (hQ : IsCompact Q)
    (hloc : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ y, h (y, τ) = a → T (y, τ) ≤ c + ε → y ∈ Q) :
    ∃ SA SB K : Set (Y × ℝ), IsCompact SA ∧ IsCompact SB ∧ IsCompact K ∧
      {x | x.2 ∈ Icc (0 : ℝ) 1 ∧ h x = a ∧ T x ≤ c} ⊆ interior SA ∧
      {x | x.2 ∈ Icc (0 : ℝ) 1 ∧ h x = a ∧ T x = c} ⊆ interior SB ∧
      SA ⊆ {x | Surjective (mfderiv I 𝓘(ℝ, F) (fun z => h (z, x.2)) x.1)} ∧
      SB ⊆ {x | Surjective (mfderiv I 𝓘(ℝ, F × ℝ)
        (fun z => (h (z, x.2), T (z, x.2))) x.1)} ∧ SA ∪ SB ⊆ interior K := by
  let : LocallyCompactSpace H := I.locallyCompactSpace
  let : LocallyCompactSpace Y := ChartedSpace.locallyCompactSpace H Y
  let A : Set (Y × ℝ) := {x | x.2 ∈ Icc (0 : ℝ) 1 ∧ h x = a ∧ T x ≤ c}
  let B : Set (Y × ℝ) := {x | x.2 ∈ Icc (0 : ℝ) 1 ∧ h x = a ∧ T x = c}
  have hAclosed : IsClosed A :=
    (isClosed_Icc.preimage continuous_snd).inter
      ((isClosed_eq hh.continuous continuous_const).inter
        (isClosed_le hT.continuous continuous_const))
  have hBclosed : IsClosed B :=
    (isClosed_Icc.preimage continuous_snd).inter
      ((isClosed_eq hh.continuous continuous_const).inter
        (isClosed_eq hT.continuous continuous_const))
  have hAc : IsCompact A := (hQ.prod isCompact_Icc).of_isClosed_subset hAclosed
    (fun x hx => ⟨hloc x.2 hx.1 x.1 hx.2.1 (hx.2.2.trans (by linarith)), hx.1⟩)
  have hBc : IsCompact B := hAc.of_isClosed_subset hBclosed
    (fun x hx => ⟨hx.1, hx.2.1, le_of_eq hx.2.2⟩)
  obtain ⟨SA, hSA, hASA, hSAR⟩ := exists_compact_between hAc
    (isOpen_spatial_surjective_mfderiv h hh)
    (fun x hx => hreg x.2 hx.1 x.1 hx.2.1 (hx.2.2.trans (by linarith)))
  obtain ⟨SB, hSB, hBSB, hSBR⟩ := exists_compact_between hBc
    (isOpen_spatial_surjective_mfderiv (fun x => (h x, T x)) (hh.prodMk_space hT))
    (fun x hx => hface x.2 hx.1 x.1 hx.2.1 (by rw [hx.2.2, sub_self, abs_zero]; exact hε))
  obtain ⟨K, hK, hSK, _hKU⟩ := exists_compact_between (hSA.union hSB) isOpen_univ
    (subset_univ (SA ∪ SB))
  exact ⟨SA, SB, K, hSA, hSB, hK, hASA, hBSB, hSAR, hSBR, hSK⟩

end DifferentialGeometry.Topology.Ehresmann
