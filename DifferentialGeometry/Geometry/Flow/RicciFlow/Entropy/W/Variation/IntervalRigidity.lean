import DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.W.Variation.Rigidity
import DifferentialGeometry.Analysis.Calculus.Derivative.IntervalConstancy

set_option autoImplicit false

open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Connection
namespace DifferentialGeometry.PDE.RicciFlow.Entropy

noncomputable section

open Bundle Filter MeasureTheory DifferentialGeometry.Tensor0SBundle

open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff Topology

universe u uE uH

section Along

variable {M : Type*} [MeasurableSpace M]
variable {mu : Real -> Measure M} {n : Nat} {tau : Real -> Real}
variable {scalarCurvature gradPotentialNormSq potential : Real -> M -> Real}

theorem wFunctionalAlong_eq_of_hasFirstVariationAt_zero_on_Icc
    {a b : Real} (hab : a ≤ b)
    (hcont : ContinuousOn
      (wFunctionalAlong mu n tau scalarCurvature gradPotentialNormSq potential)
      (Set.Icc a b))
    (hzero : ∀ s ∈ Set.Ioo a b,
      WEntropyHasFirstVariationAt mu n tau scalarCurvature gradPotentialNormSq
        potential s 0) :
    ∀ s ∈ Set.Icc a b,
      wFunctionalAlong mu n tau scalarCurvature gradPotentialNormSq potential s =
        wFunctionalAlong mu n tau scalarCurvature gradPotentialNormSq potential a :=
  DifferentialGeometry.eq_of_hasDerivAt_zero_on_Icc hab hcont hzero

end Along

variable {M : Type u}

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete Real E
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem wFunctionalAlong_eq_of_firstVariation_eq_zero_on_Icc
    [I.Boundaryless] [CompactSpace M]
    {D Dr : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    (u : Real -> M -> Real)
    (hu : DifferentialGeometry.Analysis.Parabolic.IsHeatPotOn Dr
      (reverseFamily (I := I) (M := M) (flowG (I := I) S) T)
      (fun r x =>
        (conjCoeff (I := I) (M := M) S (T - r) : M -> Real) x) u)
    (hpos : ∀ r : Real, r ∈ Dr.regular ∩ Set.Ioi (0 : Real) ->
      ∀ x : M, 0 < u r x)
    {a b : Real} (ha : 0 < a) (hab : a ≤ b)
    (hreg : Set.Icc a b ⊆ Dr.regular)
    (hD : ∀ r ∈ Set.Icc a b, T - r ∈ D.regular) :
    let n := Module.finrank Real E
    let G := reverseFamily (I := I) (M := M) (flowG (I := I) S) T
    let f : Real -> M -> Real := fun r => perelmanPotential n r (u r)
    let R : Real -> M -> Real := fun r x => S.scalar (T - r) x
    let q : Real -> M -> Real := fun r x =>
      (G.metric r).inner x
        (gradientFun (I := I) (G.metric r) (f r) x)
        (gradientFun (I := I) (G.metric r) (f r) x)
    (∀ s ∈ Set.Ioo a b,
      wEntropyFirstVariation
        (volumeMeasureFamily (I := I) (M := M) G)
        n (fun r : Real => r) R q f s = 0) ->
    ∀ s ∈ Set.Icc a b,
      wFunctionalAlong
          (volumeMeasureFamily (I := I) (M := M) G)
          n (fun r : Real => r) R q f s =
        wFunctionalAlong
          (volumeMeasureFamily (I := I) (M := M) G)
          n (fun r : Real => r) R q f a := by
  classical
  dsimp only
  intro hzero
  let n := Module.finrank Real E
  let G := reverseFamily (I := I) (M := M) (flowG (I := I) S) T
  let f : Real -> M -> Real := fun r => perelmanPotential n r (u r)
  let R : Real -> M -> Real := fun r x => S.scalar (T - r) x
  let q : Real -> M -> Real := fun r x =>
    (G.metric r).inner x
      (gradientFun (I := I) (G.metric r) (f r) x)
      (gradientFun (I := I) (G.metric r) (f r) x)
  let W : Real -> Real :=
    wFunctionalAlong (volumeMeasureFamily (I := I) (M := M) G)
      n (fun r : Real => r) R q f
  have hderiv (s : Real) (hs : s ∈ Set.Icc a b) : HasDerivAt W _ s :=
    w_rev_square (I := I) S hS T u hu hpos
      (hreg hs) (ha.trans_le hs.1) (hD s hs)
  have hcont : ContinuousOn W (Set.Icc a b) := fun s hs =>
    (hderiv s hs).continuousAt.continuousWithinAt
  have hgeom : ∀ s ∈ Set.Ioo a b, HasDerivAt W 0 s := by
    intro s hs
    have hsI : s ∈ Set.Icc a b := Set.Ioo_subset_Icc_self hs
    have hz : deriv W s = 0 := hzero s hs
    have h := (hderiv s hsI).differentiableAt.hasDerivAt
    rwa [hz] at h
  exact DifferentialGeometry.eq_of_hasDerivAt_zero_on_Icc hab hcont hgeom

theorem wEntropy_soliton_equation_on_Ioo_of_firstVariation_eq_zero
    [I.Boundaryless] [CompactSpace M]
    {D Dr : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    (u : Real -> M -> Real)
    (hu : DifferentialGeometry.Analysis.Parabolic.IsHeatPotOn Dr
      (reverseFamily (I := I) (M := M) (flowG (I := I) S) T)
      (fun r x =>
        (conjCoeff (I := I) (M := M) S (T - r) : M -> Real) x) u)
    (hpos : ∀ r : Real, r ∈ Dr.regular ∩ Set.Ioi (0 : Real) ->
      ∀ x : M, 0 < u r x)
    {a b : Real} (ha : 0 < a)
    (hreg : Set.Ioo a b ⊆ Dr.regular)
    (hD : ∀ r ∈ Set.Ioo a b, T - r ∈ D.regular) :
    let n := Module.finrank Real E
    let G := reverseFamily (I := I) (M := M) (flowG (I := I) S) T
    let f : Real -> M -> Real := fun r => perelmanPotential n r (u r)
    let R : Real -> M -> Real := fun r x => S.scalar (T - r) x
    let q : Real -> M -> Real := fun r x =>
      (G.metric r).inner x
        (gradientFun (I := I) (G.metric r) (f r) x)
        (gradientFun (I := I) (G.metric r) (f r) x)
    (∀ s ∈ Set.Ioo a b,
      wEntropyFirstVariation
        (volumeMeasureFamily (I := I) (M := M) G)
        n (fun r : Real => r) R q f s = 0) ->
    ∀ s (hs : s ∈ Set.Ioo a b) (x : M),
      metricRicciAt (I := I) (M := M) (G.metric s) x +
        hessianSec (I := I)
          (metricCov (I := I) (M := M) (G.metric s))
          (metricCov_smooth (I := I) (M := M) (G.metric s))
          (f s)
          (by
            simpa only [f] using
              potential_slice (I := I) Dr G
                (fun r x =>
                  (conjCoeff (I := I) (M := M) S (T - r) : M -> Real) x)
                u n hu (hreg hs) (ha.trans hs.1)
                (hpos s ⟨hreg hs, ha.trans hs.1⟩)) x =
        (1 / (2 * s)) • metricTensor0S (I := I) (G.metric s) x := by
  classical
  dsimp only
  intro hzero s hs x
  let n := Module.finrank Real E
  let G := reverseFamily (I := I) (M := M) (flowG (I := I) S) T
  let f : Real -> M -> Real := fun r => perelmanPotential n r (u r)
  let R : Real -> M -> Real := fun r x => S.scalar (T - r) x
  let q : Real -> M -> Real := fun r x =>
    (G.metric r).inner x
      (gradientFun (I := I) (G.metric r) (f r) x)
      (gradientFun (I := I) (G.metric r) (f r) x)
  exact (wEntropyFirstVariation_eq_zero_iff_soliton_equation (I := I) S hS T
    u hu hpos (hreg hs) (ha.trans hs.1) (hD s hs)).mp
    (hzero s hs) x

theorem wFunctionalAlong_eq_iff_soliton_equation_on_Ioo
    [I.Boundaryless] [CompactSpace M]
    {D Dr : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    (u : Real -> M -> Real)
    (hu : DifferentialGeometry.Analysis.Parabolic.IsHeatPotOn Dr
      (reverseFamily (I := I) (M := M) (flowG (I := I) S) T)
      (fun r x =>
        (conjCoeff (I := I) (M := M) S (T - r) : M -> Real) x) u)
    (hpos : ∀ r : Real, r ∈ Dr.regular ∩ Set.Ioi (0 : Real) ->
      ∀ x : M, 0 < u r x)
    {a b : Real} (ha : 0 < a) (hab : a ≤ b)
    (hreg : Set.Icc a b ⊆ Dr.regular)
    (hD : ∀ r ∈ Set.Icc a b, T - r ∈ D.regular) :
    let n := Module.finrank Real E
    let G := reverseFamily (I := I) (M := M) (flowG (I := I) S) T
    let f : Real -> M -> Real := fun r => perelmanPotential n r (u r)
    let R : Real -> M -> Real := fun r x => S.scalar (T - r) x
    let q : Real -> M -> Real := fun r x =>
      (G.metric r).inner x
        (gradientFun (I := I) (G.metric r) (f r) x)
        (gradientFun (I := I) (G.metric r) (f r) x)
    (∀ s ∈ Set.Icc a b,
      wFunctionalAlong
          (volumeMeasureFamily (I := I) (M := M) G)
          n (fun r : Real => r) R q f s =
        wFunctionalAlong
          (volumeMeasureFamily (I := I) (M := M) G)
          n (fun r : Real => r) R q f a) ↔
    ∀ s (hs : s ∈ Set.Ioo a b) (x : M),
      metricRicciAt (I := I) (M := M) (G.metric s) x +
        hessianSec (I := I)
          (metricCov (I := I) (M := M) (G.metric s))
          (metricCov_smooth (I := I) (M := M) (G.metric s))
          (f s)
          (by
            simpa only [f] using
              potential_slice (I := I) Dr G
                (fun r x =>
                  (conjCoeff (I := I) (M := M) S (T - r) : M -> Real) x)
                u n hu (hreg (Set.Ioo_subset_Icc_self hs))
                (ha.trans hs.1)
                (hpos s ⟨hreg (Set.Ioo_subset_Icc_self hs),
                  ha.trans hs.1⟩)) x =
        (1 / (2 * s)) • metricTensor0S (I := I) (G.metric s) x := by
  classical
  dsimp only
  let n := Module.finrank Real E
  let G := reverseFamily (I := I) (M := M) (flowG (I := I) S) T
  let f : Real -> M -> Real := fun r => perelmanPotential n r (u r)
  let R : Real -> M -> Real := fun r x => S.scalar (T - r) x
  let q : Real -> M -> Real := fun r x =>
    (G.metric r).inner x
      (gradientFun (I := I) (G.metric r) (f r) x)
      (gradientFun (I := I) (G.metric r) (f r) x)
  let W : Real -> Real :=
    wFunctionalAlong (volumeMeasureFamily (I := I) (M := M) G)
      n (fun r : Real => r) R q f
  constructor
  · intro hconst s hs x
    have hloc : W =ᶠ[𝓝 s] fun _ => W a := by
      filter_upwards [isOpen_Ioo.mem_nhds hs] with z hz
      exact hconst z (Set.Ioo_subset_Icc_self hz)
    have h0 : HasDerivAt W 0 s :=
      (hasDerivAt_const s (W a)).congr_of_eventuallyEq hloc
    have hzero : wEntropyFirstVariation
        (volumeMeasureFamily (I := I) (M := M) G)
        n (fun r : Real => r) R q f s = 0 := h0.deriv
    exact (wEntropyFirstVariation_eq_zero_iff_soliton_equation (I := I) S hS T
      u hu hpos (hreg (Set.Ioo_subset_Icc_self hs))
      (ha.trans hs.1) (hD s (Set.Ioo_subset_Icc_self hs))).mp
      hzero x
  · intro hsol
    refine wFunctionalAlong_eq_of_firstVariation_eq_zero_on_Icc
      (I := I) S hS T u hu hpos ha hab hreg hD ?_
    intro s hs
    exact (wEntropyFirstVariation_eq_zero_iff_soliton_equation (I := I) S hS T
      u hu hpos (hreg (Set.Ioo_subset_Icc_self hs))
      (ha.trans hs.1) (hD s (Set.Ioo_subset_Icc_self hs))).mpr
      (hsol s hs)

end

end DifferentialGeometry.PDE.RicciFlow.Entropy
