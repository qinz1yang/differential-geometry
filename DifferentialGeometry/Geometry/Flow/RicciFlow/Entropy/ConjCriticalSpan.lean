import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.ScalarNonautSpan
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.ScalarPotentialPairing
import DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.ConjPotential

/-!
# Compact-span scalar critical estimate

This file combines the prescribed-length moving-Laplacian estimate with the
fixed-background scalar-potential estimate on a compact regular-time slab.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.Entropy

open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete Real E

/-- On every sufficiently short prescribed backward interval in a compact
regular-time slab, the scalar conjugate-heat perturbation has one
support-independent finite-core energy bound at every Sobolev order. -/
theorem scalar_crit_span
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {a b : Real} (hab : Set.Icc a b ⊆ D.regular) :
    ∃ ρ : Real, 0 < ρ ∧ ρ ≤ 1 ∧
      ∀ (T : D.RegularTime), (T : Real) ∈ Set.Icc a b →
        ∀ h : Real, 0 < h → h ≤ ρ → a ≤ (T : Real) - h →
          (∀ s ∈ Set.Icc (0 : Real) h, (T : Real) - s ∈ D.regular) ∧
          ∃ Cmid : ℕ → Real, (∀ n, 0 ≤ Cmid n) ∧
            ∀ (n : ℕ) s, s ∈ Set.Icc (0 : Real) h →
              ∀ (F : Finset
                  (DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
                    (I := I) (M := M) (S.family.metric (T : Real)) 0 0))
                (v : tensorHs (I := I) (M := M)
                  (S.family.metric (T : Real)) 0 0 0)
                (hv : (Function.support v.coeff).Finite),
                hv.toFinset ⊆ F →
                  2 * ∑ i ∈ F,
                      tensorSobolevWeight (I := I) (M := M) i (n : Real) *
                        (v.coeff i *
                          tensorL2Coeff (I := I) (M := M)
                            (tensorResolventL2_isCompactOperator
                              (I := I) (M := M)
                              (S.family.metric (T : Real)) 0 0)
                            (SmoothCcTensor.toL2
                              (scalarLapDiffCc (I := I)
                                  (S.family.metric (T : Real))
                                  (S.family.metric ((T : Real) - s))
                                  (tensorHsSmoothRepr (I := I) (M := M) v hv) +
                                scalarSmul (I := I) (M := M)
                                  (S.family.metric (T : Real)) 0 0
                                  (conjCoeff (I := I) (M := M) S
                                    ((T : Real) - s))
                                  (tensorHsSmoothRepr (I := I) (M := M) v hv))) i) ≤
                    ((23 : Real) / 12) *
                        (∑ i ∈ F,
                          tensorSobolevWeight (I := I) (M := M) i
                              ((n + 1 : ℕ) : Real) * (v.coeff i) ^ 2) +
                      Cmid n *
                        (∑ i ∈ F,
                          tensorSobolevWeight (I := I) (M := M) i (n : Real) *
                            (v.coeff i) ^ 2) := by
  classical
  obtain ⟨ρ, hρ, hρone, hA2span⟩ :=
    cc_a2_span (I := I) (M := M) S.family hS.smoothMetric hab
  refine ⟨ρ, hρ, hρone, ?_⟩
  intro T hT h hh hhρ hleft
  obtain ⟨hreg, hA2⟩ := hA2span T hT h hh hhρ hleft
  let K : Set Real := Set.Icc (0 : Real) h
  let R : Set Real := {s : Real | (T : Real) - s ∈ D.regular}
  let ζ : Real → C^∞⟮I, M; Real⟯ := fun s ↦
    conjCoeff (I := I) (M := M) S ((T : Real) - s)
  have hK : IsCompact K := by
    simpa only [K] using isCompact_Icc
  have hKR : K ⊆ R := by
    intro s hs
    simpa only [K, R] using hreg s hs
  have hζ : ContMDiffOn (I.prod 𝓘(Real, Real)) 𝓘(Real, Real) ∞
      (fun p : M × Real ↦ (ζ p.2 : M → Real) p.1)
      ((Set.univ : Set M) ×ˢ R) := by
    simpa only [ζ, R, conjCoeffRev] using conjCoeff_rev (I := I) S hS T
  choose C2 hC2_nn hC2 using hA2
  choose C1 hC1_nn hC1 using fun n : ℕ ↦
    cc_a1_unif (I := I) (M := M) (S.family.metric (T : Real)) ζ
      (R := R) (K := K) hK hKR hζ n
  refine ⟨hreg, fun n ↦ C2 n + C1 n,
    fun n ↦ add_nonneg (hC2_nn n) (hC1_nn n), ?_⟩
  intro n s hs F v hv hsub
  let U : SmoothCcTensor (S.family.metric (T : Real)) 0 0 :=
    tensorHsSmoothRepr (I := I) (M := M) v hv
  let A2 : SmoothCcTensor (S.family.metric (T : Real)) 0 0 :=
    scalarLapDiffCc (I := I) (S.family.metric (T : Real))
      (S.family.metric ((T : Real) - s)) U
  let A1 : SmoothCcTensor (S.family.metric (T : Real)) 0 0 :=
    scalarSmul (I := I) (M := M) (S.family.metric (T : Real)) 0 0
      (ζ s) U
  let L2 : Real :=
    ∑ i ∈ F, tensorSobolevWeight (I := I) (M := M) i (n : Real) *
      (v.coeff i * tensorL2Coeff (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M)
          (S.family.metric (T : Real)) 0 0)
        (SmoothCcTensor.toL2 A2) i)
  let L1 : Real :=
    ∑ i ∈ F, tensorSobolevWeight (I := I) (M := M) i (n : Real) *
      (v.coeff i * tensorL2Coeff (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M)
          (S.family.metric (T : Real)) 0 0)
        (SmoothCcTensor.toL2 A1) i)
  let L : Real :=
    ∑ i ∈ F, tensorSobolevWeight (I := I) (M := M) i (n : Real) *
      (v.coeff i * tensorL2Coeff (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M)
          (S.family.metric (T : Real)) 0 0)
        (SmoothCcTensor.toL2 (A2 + A1)) i)
  let Ehi : Real :=
    ∑ i ∈ F, tensorSobolevWeight (I := I) (M := M) i
      ((n + 1 : ℕ) : Real) * (v.coeff i) ^ 2
  let Elo : Real :=
    ∑ i ∈ F, tensorSobolevWeight (I := I) (M := M) i (n : Real) *
      (v.coeff i) ^ 2
  have h2 : 2 * L2 ≤ ((5 : Real) / 3) * Ehi + C2 n * Elo := by
    simpa only [L2, Ehi, Elo, A2, U] using hC2 n s hs F v hv hsub
  have h1 : 2 * L1 ≤ ((1 : Real) / 4) * Ehi + C1 n * Elo := by
    simpa only [L1, Ehi, Elo, A1, U, ζ, K] using
      hC1 n s hs F v hv hsub
  have htoL2 : SmoothCcTensor.toL2 (A2 + A1) =
      SmoothCcTensor.toL2 A2 + SmoothCcTensor.toL2 A1 := by
    exact map_add _ _ _
  have hsplit : L = L2 + L1 := by
    simp only [L, L2, L1]
    rw [htoL2]
    simp only [tensorL2Coeff_add, mul_add, Finset.sum_add_distrib]
  have htotal :
      2 * L ≤ ((23 : Real) / 12) * Ehi + (C2 n + C1 n) * Elo := by
    rw [hsplit]
    nlinarith [h2, h1]
  simpa only [L, Ehi, Elo, A2, A1, U, ζ] using htotal

end DifferentialGeometry.PDE.RicciFlow.Entropy

end
