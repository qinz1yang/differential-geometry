import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.MetricLapDiffSpan
import DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.ConjCriticalSpan
import DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.ConjGalerkinLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.ConjGalerkinOn
import DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.ConjPotentialSpan
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature

/-!
# Compact-span scalar Galerkin compactness

This file assembles the prescribed-interval moving-operator, finite-dimensional
ODE, energy, and compactness producers on a compact regular-time slab.
-/

noncomputable section

open Bundle Filter MeasureTheory Set
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Entropy

open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Spectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete Real E

/-- A compact regular-time slab has one backward radius such that every
requested shorter interval supports a full scalar Galerkin subsequence. -/
theorem gal_span
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {a b : Real} (hab : Set.Icc a b ⊆ D.regular) :
    ∃ ρ : Real, 0 < ρ ∧ ρ ≤ 1 ∧
      ∀ (T : D.RegularTime), (T : Real) ∈ Set.Icc a b →
        ∀ h : Real, ∀ _hh : 0 < h, h ≤ ρ → a ≤ (T : Real) - h →
          (∀ s ∈ Set.Icc (0 : Real) h, (T : Real) - s ∈ D.regular) ∧
          ∀ u0 : SmoothCcTensor (S.family.metric (T : Real)) 0 0,
            ∃ V : Nat → Real →
                TensorEigenIdx (I := I) (M := M)
                  (S.family.metric (T : Real)) 0 0 → Real,
            ∃ phi : Nat → Nat,
            ∃ ulim : Real → TensorEigenIdx (I := I) (M := M)
                (S.family.metric (T : Real)) 0 0 → Real,
              IsConjGalSubseq (I := I) (M := M) S T h u0 V phi ulim := by
  classical
  obtain ⟨ρ2, hρ2, hρ2one, hA2⟩ :=
    lapA20_span (I := I) (M := M) S.family hS.smoothMetric hab
  obtain ⟨ρc, hρc, hρcone, hcritSpan⟩ :=
    scalar_crit_span (I := I) (M := M) S hS hab
  let ρ : Real := min ρ2 ρc
  have hρ : 0 < ρ := lt_min hρ2 hρc
  have hρone : ρ ≤ 1 := (min_le_left ρ2 ρc).trans hρ2one
  refine ⟨ρ, hρ, hρone, ?_⟩
  intro T hT h hh hhρ hleft
  have hh2 : h ≤ ρ2 := hhρ.trans (min_le_left ρ2 ρc)
  have hhc : h ≤ ρc := hhρ.trans (min_le_right ρ2 ρc)
  obtain ⟨hreg, hcont2, _C2, _hbound2, hcore⟩ :=
    hA2 T hT h hh hh2 hleft
  obtain ⟨_hreg', Cmid, hCmid, hcrit⟩ :=
    hcritSpan T hT h hh hhc hleft
  obtain ⟨_C1, hcont1, _hbound1⟩ :=
    conjA1_on (I := I) (M := M) S hS T hreg
  let q : SmoothRiemannianMetric I M := S.family.metric (T : Real)
  let Inc : tensorHs (I := I) (M := M) q 0 0 2 →L[Real]
      tensorHs (I := I) (M := M) q 0 0 1 :=
    tensorHsInclusion (I := I) (M := M)
      (g := q) (r := 0) (s := 0) (show (1 : Real) ≤ 2 by norm_num)
  have hPot := hcont1.clm_comp
    (continuousOn_const : ContinuousOn (fun _ : Real => Inc) (Set.Icc 0 h))
  have hpert : ContinuousOn
      (fun s : Real ↦ scalarGalPert (I := I) (M := M) S T s)
      (Set.Icc (0 : Real) h) := by
    simpa only [scalarGalPert, q, Inc] using hcont2.add hPot
  have hG : IsConjGalTime (I := I) (M := M) S T ⟨h⟩ :=
    gal_exists_on (I := I) (M := M) S T hh (hhρ.trans hρone) hpert
  have hbound := gal_bound_on (I := I) (M := M) S T hG
    Cmid hCmid hcrit hcore
  have hsub := gal_subseq_on (I := I) (M := M) S T hh hbound hpert
  exact ⟨hreg, hsub⟩

/-- A compact regular-time slab has one backward radius such that every
requested shorter interval carries a Galerkin subsequence and its classical
heat-potential reconstruction on exactly that interval. -/
theorem gallim_span
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {a b : Real} (hab : Set.Icc a b ⊆ D.regular) :
    ∃ ρ : Real, 0 < ρ ∧ ρ ≤ 1 ∧
      ∀ (T : D.RegularTime), (T : Real) ∈ Set.Icc a b →
        ∀ h : Real, ∀ hh : 0 < h, h ≤ ρ → a ≤ (T : Real) - h →
          ∀ u0 : SmoothCcTensor (S.family.metric (T : Real)) 0 0,
            ∃ V : Nat → Real →
                TensorEigenIdx (I := I) (M := M)
                  (S.family.metric (T : Real)) 0 0 → Real,
            ∃ phi : Nat → Nat,
            ∃ ulim : Real → TensorEigenIdx (I := I) (M := M)
                (S.family.metric (T : Real)) 0 0 → Real,
              IsConjGalSubseq (I := I) (M := M) S T h u0 V phi ulim ∧
              DifferentialGeometry.Analysis.Parabolic.IsHeatPotOn
                (RealTimeInterval.closed 0 h hh.le)
                (reverseFamily (I := I) (M := M)
                  (flowG (I := I) S) (T : Real))
                (fun s x =>
                  (conjCoeff (I := I) (M := M)
                    S ((T : Real) - s) : M → Real) x)
                (fun s x =>
                  scalarSpecSum (I := I) (M := M)
                    (S.family.metric (T : Real))
                    (fun i r => ulim r i) s x) := by
  classical
  obtain ⟨ρg, hρg, hρgone, hgal⟩ :=
    gal_span (I := I) (M := M) S hS hab
  obtain ⟨ρa, hρa, hρaone, hA20⟩ :=
    lapA20_span (I := I) (M := M) S.family hS.smoothMetric hab
  let ρ : Real := min ρg ρa
  have hρ : 0 < ρ := lt_min hρg hρa
  have hρone : ρ ≤ 1 := (min_le_left ρg ρa).trans hρgone
  refine ⟨ρ, hρ, hρone, ?_⟩
  intro T hT h hh hhρ hleft u0
  have hhg : h ≤ ρg := hhρ.trans (min_le_left ρg ρa)
  have hha : h ≤ ρa := hhρ.trans (min_le_right ρg ρa)
  obtain ⟨_hregG, hsub⟩ :=
    hgal T hT h hh hhg hleft
  obtain ⟨V, phi, ulim, hlim⟩ := hsub u0
  obtain ⟨hreg, _hcont, _C2, _hbound, hcore⟩ :=
    hA20 T hT h hh hha hleft
  refine ⟨V, phi, ulim, hlim, ?_⟩
  exact gallim_on (I := I) (M := M) hS hh hlim hreg hcore

/-- Unless the manifold is empty, a compact regular-time slab has one
backward radius on which every requested shorter interval carries a positive
unit-mass classical conjugate heat potential. -/
theorem gallim_unit_span
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {a b : Real} (hab : Set.Icc a b ⊆ D.regular) :
    IsEmpty M ∨
      ∃ ρ : Real, 0 < ρ ∧ ρ ≤ 1 ∧
        ∀ (T : D.RegularTime), (T : Real) ∈ Set.Icc a b →
          ∀ h : Real, ∀ hh : 0 < h, h ≤ ρ → a ≤ (T : Real) - h →
            ∃ u : Real → M → Real,
              DifferentialGeometry.Analysis.Parabolic.IsHeatPotOn
                (RealTimeInterval.closed 0 h hh.le)
                (reverseFamily (I := I) (M := M)
                  (flowG (I := I) S) (T : Real))
                (fun s x =>
                  (conjCoeff (I := I) (M := M)
                    S ((T : Real) - s) : M → Real) x)
                u ∧
              (∀ s ∈ Set.Icc (0 : Real) h, ∀ x : M, 0 < u s x) ∧
              ∀ s ∈ Set.Icc (0 : Real) h,
                (∫ x, u s x ∂(volumeMeasureFamily (I := I) (M := M)
                  (reverseFamily (I := I) (M := M)
                    (flowG (I := I) S) (T : Real)) s)) = 1 := by
  classical
  rcases isEmpty_or_nonempty M with hM | hM
  · exact Or.inl hM
  · right
    letI : Nonempty M := hM
    obtain ⟨ρ, hρ, hρone, hspan⟩ :=
      gallim_span (I := I) (M := M) S hS hab
    refine ⟨ρ, hρ, hρone, ?_⟩
    intro T hT h hh hhρ hleft
    rcases unit_init_or_empty (I := I) (M := M)
        (S.family.metric (T : Real)) with hEmpty | ⟨u0, hinit, hunit⟩
    · exact (hEmpty.false (Classical.choice hM)).elim
    · obtain ⟨V, phi, ulim, hlim, hpot⟩ :=
        hspan T hT h hh hhρ hleft u0
      let u : Real → M → Real := fun s x =>
        scalarSpecSum (I := I) (M := M) (S.family.metric (T : Real))
          (fun i r => ulim r i) s x
      have hpos : ∀ s ∈ Set.Icc (0 : Real) h, ∀ x : M, 0 < u s x := by
        simpa only [u] using
          gallim_pos_on (I := I) (M := M) S hS hab T hT hh hleft
            hlim hpot hinit
      have hreg : ∀ s ∈ Set.Icc (0 : Real) h,
          (T : Real) - s ∈ D.regular := by
        intro s hs
        apply hab
        constructor <;> linarith [hs.1, hs.2, hT.1, hT.2]
      have hmass := heatpot_mass_on (I := I) (M := M)
        S hS T hh hpot hreg
      have hmass0 :
          (∫ x, u 0 x ∂(volumeMeasureFamily (I := I) (M := M)
            (reverseFamily (I := I) (M := M)
              (flowG (I := I) S) (T : Real)) 0)) = 1 := by
        dsimp only [u]
        rw [galLim_initial (I := I) (M := M) hlim]
        simpa only [volumeMeasureFamily, metricFamilyForMeasure,
          riemannianMeasureFamily, reverseFamily, flowG, sub_zero] using hunit
      refine ⟨u, ?_, hpos, ?_⟩
      · simpa only [u] using hpot
      · intro s hs
        exact (hmass s hs).trans hmass0

end DifferentialGeometry.PDE.RicciFlow.Entropy

end
