import DifferentialGeometry.Analysis.Parabolic.Euclidean.OperatorLimit
import DifferentialGeometry.Analysis.Schauder.ParabolicJetCompactness

noncomputable section

open Filter Set Topology
open scoped NNReal

namespace DifferentialGeometry.Analysis.Parabolic.Euclidean

open DifferentialGeometry.Analysis.Schauder

private abbrev Euc (n : Type*) := EuclideanSpace Real n

variable {n F : Type*} [Fintype n]
  [NormedAddCommGroup F] [NormedSpace Real F] [FiniteDimensional Real F]

theorem exists_classical_nondivergence_solution_subseq_with_locally_holderOnWith
    {Q : Set (ParabolicPoint (Euc n))} (hQ : IsOpen Q)
    (aApprox : Nat → n → n → ParabolicPoint (Euc n) → Real)
    (bApprox : Nat → n → ParabolicPoint (Euc n) → Real)
    (cApprox : Nat → ParabolicPoint (Euc n) → Real)
    (uApprox dtimeUApprox sourceApprox : Nat → ParabolicPoint (Euc n) → F)
    (duApprox : Nat → ParabolicPoint (Euc n) → Euc n →L[Real] F)
    (d2uApprox : Nat → ParabolicPoint (Euc n) →
      Euc n →L[Real] Euc n →L[Real] F)
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (b : n → ParabolicPoint (Euc n) → Real)
    (c : ParabolicPoint (Euc n) → Real)
    (source : ParabolicPoint (Euc n) → F)
    {r : NNReal} (hr : 0 < r)
    (huHolder : ∀ K : Set Q, IsCompact K →
      ∃ C : NNReal, ∀ m, HolderOnWith C r (fun p : Q ↦ uApprox m p) K)
    (hdtimeUHolder : ∀ K : Set Q, IsCompact K →
      ∃ C : NNReal, ∀ m, HolderOnWith C r (fun p : Q ↦ dtimeUApprox m p) K)
    (hduHolder : ∀ K : Set Q, IsCompact K →
      ∃ C : NNReal, ∀ m, HolderOnWith C r (fun p : Q ↦ duApprox m p) K)
    (hd2uHolder : ∀ K : Set Q, IsCompact K →
      ∃ C : NNReal, ∀ m, HolderOnWith C r (fun p : Q ↦ d2uApprox m p) K)
    (huBound : ∀ p : Q, ∃ M : Real, ∀ m, ‖uApprox m p‖ ≤ M)
    (hdtimeUBound : ∀ p : Q, ∃ M : Real, ∀ m, ‖dtimeUApprox m p‖ ≤ M)
    (hduBound : ∀ p : Q, ∃ M : Real, ∀ m, ‖duApprox m p‖ ≤ M)
    (hd2uBound : ∀ p : Q, ∃ M : Real, ∀ m, ‖d2uApprox m p‖ ≤ M)
    (ha : ∀ p ∈ Q, ∀ i j,
      Tendsto (fun m ↦ aApprox m i j p) atTop (nhds (a i j p)))
    (hb : ∀ p ∈ Q, ∀ i,
      Tendsto (fun m ↦ bApprox m i p) atTop (nhds (b i p)))
    (hc : ∀ p ∈ Q, Tendsto (fun m ↦ cApprox m p) atTop (nhds (c p)))
    (hsource : ∀ p ∈ Q,
      Tendsto (fun m ↦ sourceApprox m p) atTop (nhds (source p)))
    (hrealize : ∀ m, ParabolicJetRealizesOn Q
      (uApprox m) (dtimeUApprox m) (duApprox m) (d2uApprox m))
    (hequation : ∀ m, Set.EqOn
      (parabolicNondivergenceOperator (aApprox m) (bApprox m) (cApprox m)
        (fun t x ↦ uApprox m (parabolicPoint t x))) (sourceApprox m) Q) :
    ∃ (phi : Nat → Nat)
        (u dtimeU : ParabolicPoint (Euc n) → F)
        (du : ParabolicPoint (Euc n) → Euc n →L[Real] F)
        (d2u : ParabolicPoint (Euc n) → Euc n →L[Real] Euc n →L[Real] F),
      StrictMono phi ∧
        TendstoLocallyUniformlyOn (fun m ↦ uApprox (phi m)) u atTop Q ∧
        TendstoLocallyUniformlyOn (fun m ↦ dtimeUApprox (phi m)) dtimeU atTop Q ∧
        TendstoLocallyUniformlyOn (fun m ↦ duApprox (phi m)) du atTop Q ∧
        TendstoLocallyUniformlyOn (fun m ↦ d2uApprox (phi m)) d2u atTop Q ∧
        ParabolicJetRealizesOn Q u dtimeU du d2u ∧
        IsParabolicC2On Q (fun t x ↦ u (parabolicPoint t x)) ∧
        Set.EqOn (parabolicNondivergenceOperator a b c
          (fun t x ↦ u (parabolicPoint t x))) source Q ∧
        ∀ K : Set Q, IsCompact K →
          ∃ Cu Ct Cd Cd2 : NNReal,
            HolderOnWith Cu r (fun p : Q ↦ u p) K ∧
            HolderOnWith Ct r (fun p : Q ↦ dtimeU p) K ∧
            HolderOnWith Cd r (fun p : Q ↦ du p) K ∧
            HolderOnWith Cd2 r (fun p : Q ↦ d2u p) K := by
  rcases exists_parabolic_jet_subseq_with_locally_holderOnWith hQ
      uApprox dtimeUApprox duApprox d2uApprox hr
      huHolder hdtimeUHolder hduHolder hd2uHolder
      huBound hdtimeUBound hduBound hd2uBound hrealize with
    ⟨phi, u, dtimeU, du, d2u, hphi, hu, hdtimeU, hdu, hd2u,
      hlimit, hclassical, hholder⟩
  have hphiTendsto : Tendsto phi atTop atTop := hphi.tendsto_atTop
  have hlimitEquation : Set.EqOn (parabolicNondivergenceOperator a b c
      (fun t x ↦ u (parabolicPoint t x))) source Q :=
    parabolic_nondivergence_equation_on_of_tendsto_locally_uniformly_on hQ
      (fun p hp i j ↦ (ha p hp i j).comp hphiTendsto)
      (fun p hp i ↦ (hb p hp i).comp hphiTendsto)
      (fun p hp ↦ (hc p hp).comp hphiTendsto)
      hu hdtimeU hdu hd2u
      (fun p hp ↦ (hsource p hp).comp hphiTendsto)
      (fun m ↦ hrealize (phi m))
      (Filter.Eventually.of_forall fun m ↦ hequation (phi m))
  exact ⟨phi, u, dtimeU, du, d2u, hphi, hu, hdtimeU, hdu, hd2u,
    hlimit, hclassical, hlimitEquation, hholder⟩

theorem exists_classical_nondivergence_solution_subseq_of_lower_jets_gauge
    {Q : Set (ParabolicPoint (Euc n))} (hQ : IsOpen Q)
    (aApprox : Nat → n → n → ParabolicPoint (Euc n) → Real)
    (bApprox : Nat → n → ParabolicPoint (Euc n) → Real)
    (cApprox : Nat → ParabolicPoint (Euc n) → Real)
    (uApprox dtimeUApprox sourceApprox : Nat → ParabolicPoint (Euc n) → F)
    (duApprox : Nat → ParabolicPoint (Euc n) → Euc n →L[Real] F)
    (d2uApprox : Nat → ParabolicPoint (Euc n) →
      Euc n →L[Real] Euc n →L[Real] F)
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (b : n → ParabolicPoint (Euc n) → Real)
    (c : ParabolicPoint (Euc n) → Real)
    (source : ParabolicPoint (Euc n) → F)
    {r : NNReal} (hr : 0 < r) (C : NNReal)
    (hgauge : ∀ m, eParabolicC2HolderGaugeWithLowerJetsOn r Q
      (fun t x ↦ uApprox m (parabolicPoint t x)) ≤ C)
    (ha : ∀ p ∈ Q, ∀ i j,
      Tendsto (fun m ↦ aApprox m i j p) atTop (nhds (a i j p)))
    (hb : ∀ p ∈ Q, ∀ i,
      Tendsto (fun m ↦ bApprox m i p) atTop (nhds (b i p)))
    (hc : ∀ p ∈ Q, Tendsto (fun m ↦ cApprox m p) atTop (nhds (c p)))
    (hsource : ∀ p ∈ Q,
      Tendsto (fun m ↦ sourceApprox m p) atTop (nhds (source p)))
    (hrealize : ∀ m, ParabolicJetRealizesOn Q
      (uApprox m) (dtimeUApprox m) (duApprox m) (d2uApprox m))
    (hequation : ∀ m, Set.EqOn
      (parabolicNondivergenceOperator (aApprox m) (bApprox m) (cApprox m)
        (fun t x ↦ uApprox m (parabolicPoint t x))) (sourceApprox m) Q) :
    ∃ (phi : Nat → Nat)
        (u dtimeU : ParabolicPoint (Euc n) → F)
        (du : ParabolicPoint (Euc n) → Euc n →L[Real] F)
        (d2u : ParabolicPoint (Euc n) → Euc n →L[Real] Euc n →L[Real] F),
      StrictMono phi ∧
        TendstoLocallyUniformlyOn (fun m ↦ uApprox (phi m)) u atTop Q ∧
        TendstoLocallyUniformlyOn (fun m ↦ dtimeUApprox (phi m)) dtimeU atTop Q ∧
        TendstoLocallyUniformlyOn (fun m ↦ duApprox (phi m)) du atTop Q ∧
        TendstoLocallyUniformlyOn (fun m ↦ d2uApprox (phi m)) d2u atTop Q ∧
        ParabolicJetRealizesOn Q u dtimeU du d2u ∧
        IsParabolicC2On Q (fun t x ↦ u (parabolicPoint t x)) ∧
        Set.EqOn (parabolicNondivergenceOperator a b c
          (fun t x ↦ u (parabolicPoint t x))) source Q ∧
        ∀ K : Set Q, IsCompact K →
          ∃ Cu Ct Cd Cd2 : NNReal,
            HolderOnWith Cu r (fun p : Q ↦ u p) K ∧
            HolderOnWith Ct r (fun p : Q ↦ dtimeU p) K ∧
            HolderOnWith Cd r (fun p : Q ↦ du p) K ∧
            HolderOnWith Cd2 r (fun p : Q ↦ d2u p) K := by
  rcases exists_parabolic_jet_subseq_of_lower_jets_gauge hQ
      uApprox dtimeUApprox duApprox d2uApprox hr C hgauge hrealize with
    ⟨phi, u, dtimeU, du, d2u, hphi, hu, hdtimeU, hdu, hd2u,
      hlimit, hclassical, hholder⟩
  have hphiTendsto : Tendsto phi atTop atTop := hphi.tendsto_atTop
  have hlimitEquation : Set.EqOn (parabolicNondivergenceOperator a b c
      (fun t x ↦ u (parabolicPoint t x))) source Q :=
    parabolic_nondivergence_equation_on_of_tendsto_locally_uniformly_on hQ
      (fun p hp i j ↦ (ha p hp i j).comp hphiTendsto)
      (fun p hp i ↦ (hb p hp i).comp hphiTendsto)
      (fun p hp ↦ (hc p hp).comp hphiTendsto)
      hu hdtimeU hdu hd2u
      (fun p hp ↦ (hsource p hp).comp hphiTendsto)
      (fun m ↦ hrealize (phi m))
      (Filter.Eventually.of_forall fun m ↦ hequation (phi m))
  exact ⟨phi, u, dtimeU, du, d2u, hphi, hu, hdtimeU, hdu, hd2u,
    hlimit, hclassical, hlimitEquation, hholder⟩

theorem exists_classical_nondivergence_solution_subseq_of_locally_holderOnWith
    {Q : Set (ParabolicPoint (Euc n))} (hQ : IsOpen Q)
    (aApprox : Nat → n → n → ParabolicPoint (Euc n) → Real)
    (bApprox : Nat → n → ParabolicPoint (Euc n) → Real)
    (cApprox : Nat → ParabolicPoint (Euc n) → Real)
    (uApprox dtimeUApprox sourceApprox : Nat → ParabolicPoint (Euc n) → F)
    (duApprox : Nat → ParabolicPoint (Euc n) → Euc n →L[Real] F)
    (d2uApprox : Nat → ParabolicPoint (Euc n) →
      Euc n →L[Real] Euc n →L[Real] F)
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (b : n → ParabolicPoint (Euc n) → Real)
    (c : ParabolicPoint (Euc n) → Real)
    (source : ParabolicPoint (Euc n) → F)
    {r : NNReal} (hr : 0 < r)
    (huHolder : ∀ K : Set Q, IsCompact K →
      ∃ C : NNReal, ∀ m, HolderOnWith C r (fun p : Q ↦ uApprox m p) K)
    (hdtimeUHolder : ∀ K : Set Q, IsCompact K →
      ∃ C : NNReal, ∀ m, HolderOnWith C r (fun p : Q ↦ dtimeUApprox m p) K)
    (hduHolder : ∀ K : Set Q, IsCompact K →
      ∃ C : NNReal, ∀ m, HolderOnWith C r (fun p : Q ↦ duApprox m p) K)
    (hd2uHolder : ∀ K : Set Q, IsCompact K →
      ∃ C : NNReal, ∀ m, HolderOnWith C r (fun p : Q ↦ d2uApprox m p) K)
    (huBound : ∀ p : Q, ∃ M : Real, ∀ m, ‖uApprox m p‖ ≤ M)
    (hdtimeUBound : ∀ p : Q, ∃ M : Real, ∀ m, ‖dtimeUApprox m p‖ ≤ M)
    (hduBound : ∀ p : Q, ∃ M : Real, ∀ m, ‖duApprox m p‖ ≤ M)
    (hd2uBound : ∀ p : Q, ∃ M : Real, ∀ m, ‖d2uApprox m p‖ ≤ M)
    (ha : ∀ p ∈ Q, ∀ i j,
      Tendsto (fun m ↦ aApprox m i j p) atTop (nhds (a i j p)))
    (hb : ∀ p ∈ Q, ∀ i,
      Tendsto (fun m ↦ bApprox m i p) atTop (nhds (b i p)))
    (hc : ∀ p ∈ Q, Tendsto (fun m ↦ cApprox m p) atTop (nhds (c p)))
    (hsource : ∀ p ∈ Q,
      Tendsto (fun m ↦ sourceApprox m p) atTop (nhds (source p)))
    (hrealize : ∀ m, ParabolicJetRealizesOn Q
      (uApprox m) (dtimeUApprox m) (duApprox m) (d2uApprox m))
    (hequation : ∀ m, Set.EqOn
      (parabolicNondivergenceOperator (aApprox m) (bApprox m) (cApprox m)
        (fun t x ↦ uApprox m (parabolicPoint t x))) (sourceApprox m) Q) :
    ∃ (phi : Nat → Nat)
        (u dtimeU : ParabolicPoint (Euc n) → F)
        (du : ParabolicPoint (Euc n) → Euc n →L[Real] F)
        (d2u : ParabolicPoint (Euc n) → Euc n →L[Real] Euc n →L[Real] F),
      StrictMono phi ∧
        TendstoLocallyUniformlyOn (fun m ↦ uApprox (phi m)) u atTop Q ∧
        TendstoLocallyUniformlyOn (fun m ↦ dtimeUApprox (phi m)) dtimeU atTop Q ∧
        TendstoLocallyUniformlyOn (fun m ↦ duApprox (phi m)) du atTop Q ∧
        TendstoLocallyUniformlyOn (fun m ↦ d2uApprox (phi m)) d2u atTop Q ∧
        ParabolicJetRealizesOn Q u dtimeU du d2u ∧
        IsParabolicC2On Q (fun t x ↦ u (parabolicPoint t x)) ∧
        Set.EqOn (parabolicNondivergenceOperator a b c
          (fun t x ↦ u (parabolicPoint t x))) source Q := by
  rcases exists_classical_nondivergence_solution_subseq_with_locally_holderOnWith
      hQ aApprox bApprox cApprox uApprox dtimeUApprox sourceApprox
      duApprox d2uApprox a b c source hr
      huHolder hdtimeUHolder hduHolder hd2uHolder
      huBound hdtimeUBound hduBound hd2uBound
      ha hb hc hsource hrealize hequation with
    ⟨phi, u, dtimeU, du, d2u, hphi, hu, hdtimeU, hdu, hd2u,
      hlimit, hclassical, hlimitEquation, _⟩
  exact ⟨phi, u, dtimeU, du, d2u, hphi, hu, hdtimeU, hdu, hd2u,
    hlimit, hclassical, hlimitEquation⟩

end DifferentialGeometry.Analysis.Parabolic.Euclidean

end
