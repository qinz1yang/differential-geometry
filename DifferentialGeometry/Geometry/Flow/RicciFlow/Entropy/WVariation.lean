import DifferentialGeometry.Analysis.Integration.Measure.FamilyLocal
import DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.ConjGalerkinClassical
import DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.ConjPotential
import DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.FlowVariation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.PotentialGeometry
import DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.WeightedHessian
import Mathlib.Analysis.Calculus.Deriv.MeanValue

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Perelman's W variation along reversed Ricci flow

This file assembles the actual reverse-flow metric, scalar-curvature,
gradient-square, and reconstructed-potential paths into a local first
variation of `W`.  The pointwise geometric derivatives live in
`FlowVariation`; this module is only their moving-volume assembly.
-/

namespace DifferentialGeometry.PDE.RicciFlow.Entropy

noncomputable section

open Bundle Filter MeasureTheory Tensor0SBundle
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
open scoped Manifold ContDiff Topology

universe u uE uH

variable {M : Type u}

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete Real E
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- The actual reversed Ricci-flow metric, scalar curvature, squared gradient,
and positive conjugate-heat potential have a local first variation of
Perelman's `W` functional. -/
theorem w_rev_hasDerivAt
    [I.Boundaryless] [CompactSpace M]
    {D Dr : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (n : Nat)
    (u : Real -> M -> Real)
    (hu : DifferentialGeometry.Analysis.Parabolic.IsHeatPotOn Dr
      (reverseFamily (I := I) (M := M) (flowG (I := I) S) T)
      (fun r x =>
        (conjCoeff (I := I) (M := M) S (T - r) : M -> Real) x) u)
    (hpos : ∀ r : Real, r ∈ Dr.regular ∩ Set.Ioi (0 : Real) ->
      ∀ x : M, 0 < u r x)
    {s : Real} (hs : s ∈ Dr.regular) (hspos : 0 < s)
    (hTs : T - s ∈ D.regular) :
    let G := reverseFamily (I := I) (M := M) (flowG (I := I) S) T
    let f : Real -> M -> Real := fun r => perelmanPotential n r (u r)
    let R : Real -> M -> Real := fun r x => S.scalar (T - r) x
    let q : Real -> M -> Real := fun r x =>
      (G.metric r).inner x
        (gradientFun (I := I) (G.metric r) (f r) x)
        (gradientFun (I := I) (G.metric r) (f r) x)
    let ft : M -> Real := fun x =>
      laplacianAt (I := I) G s (f s) x - q s x + R s x -
        (n : Real) / (2 * s)
    let Rt : M -> Real := fun x =>
      -(laplacianAt (I := I) G s (R s) x +
        2 * normSq0S (I := I) (G.metric s) x 2 (S.ricci (T - s) x))
    let qt : M -> Real := fun x =>
      (-2 : Real) * S.ricciAt (T - s) x
          (vec2
            (gradientFun (I := I) (G.metric s) (f s) x)
            (gradientFun (I := I) (G.metric s) (f s) x)) +
        2 * (G.metric s).inner x
          (gradientFun (I := I) (G.metric s) ft x)
          (gradientFun (I := I) (G.metric s) (f s) x)
    WEntropyHasFirstVariationAt
      (volumeMeasureFamily (I := I) (M := M) G) n (fun r : Real => r)
      R q f s
      (∫ x,
        wEntropyWeightedIntegralVariationIntegrand n s 1
          (f s) ft (fun y => 2 * R s y)
          (wEntropyBracket n s (R s) (q s) (f s))
          (wEntropyBracketVariation s 1 (R s) Rt (q s) qt ft) x
        ∂(volumeMeasureFamily (I := I) (M := M) G s)) := by
  dsimp only
  let G := reverseFamily (I := I) (M := M) (flowG (I := I) S) T
  have huScalar : DifferentialGeometry.Analysis.Parabolic.IsHeatPotOn Dr G
      (fun r x => -S.scalar (T - r) x) u := by
    simpa only [G, conjCoeff_apply] using hu
  let f : Real -> M -> Real := fun r => perelmanPotential n r (u r)
  let R : Real -> M -> Real := fun r x => S.scalar (T - r) x
  let q : Real -> M -> Real := fun r x =>
    (G.metric r).inner x
      (gradientFun (I := I) (G.metric r) (f r) x)
      (gradientFun (I := I) (G.metric r) (f r) x)
  let ft : M -> Real := fun x =>
    laplacianAt (I := I) G s (f s) x - q s x + R s x -
      (n : Real) / (2 * s)
  let Rt : M -> Real := fun x =>
    -(laplacianAt (I := I) G s (R s) x +
      2 * normSq0S (I := I) (G.metric s) x 2 (S.ricci (T - s) x))
  let qt : M -> Real := fun x =>
    (-2 : Real) * S.ricciAt (T - s) x
        (vec2
          (gradientFun (I := I) (G.metric s) (f s) x)
          (gradientFun (I := I) (G.metric s) (f s) x)) +
      2 * (G.metric s).inner x
        (gradientFun (I := I) (G.metric s) ft x)
        (gradientFun (I := I) (G.metric s) (f s) x)
  let U : Set Real :=
    (Dr.regular ∩ Set.Ioi (0 : Real)) ∩ {r : Real | T - r ∈ D.regular}
  have hUo : IsOpen U := by
    dsimp only [U]
    exact (Dr.regular_isOpen.inter isOpen_Ioi).inter
      (D.regular_isOpen.preimage (continuous_const.sub continuous_id))
  have hsU : s ∈ U := ⟨⟨hs, hspos⟩, hTs⟩
  have hUmap : Set.MapsTo (fun r : Real => T - r) U D.regular := by
    intro r hr
    exact hr.2
  have hgram (x₀ : M) (i j : Fin (Module.finrank Real E)) :
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M =>
          chartGramMatrix (I := I) (G.metric p.1) x₀ p.2 i j)
        (U ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := by
    simpa only [G] using
      revGram_smooth (I := I) (M := M) (S := S) hS T hUmap x₀ i j
  have hf :
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => f p.1 p.2) (U ×ˢ Set.univ) := by
    have h := potential_joint (I := I) Dr G
      (fun r x => -S.scalar (T - r) x) u n huScalar hpos
    simpa only [f] using h.mono
      (Set.prod_mono (fun _ hr => hr.1) Set.Subset.rfl)
  have hrev :
      ContMDiff (𝓘(Real, Real).prod I) (𝓘(Real, Real).prod I) ∞
        (fun p : Real × M => (T - p.1, p.2)) :=
    (contMDiff_const.sub contMDiff_fst).prodMk contMDiff_snd
  have hR :
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => R p.1 p.2) (U ×ˢ Set.univ) := by
    have h := (scalar_joint (I := I) S hS).comp hrev.contMDiffOn
      (fun p (hp : p ∈ U ×ˢ Set.univ) =>
        ⟨hUmap hp.1, Set.mem_univ p.2⟩)
    simpa only [R, Function.comp_apply] using h
  have hq :
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => q p.1 p.2) (U ×ˢ Set.univ) := by
    simpa only [q] using
      gradSq_joint (I := I) G hUo hgram f hf
  have huU :
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => u p.1 p.2) (U ×ˢ Set.univ) :=
    huScalar.jointSmooth.mono
      (Set.prod_mono (fun _ hr => hr.1.1) Set.Subset.rfl)
  have hdens :
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => perelmanDensity n p.1 (f p.1) p.2)
        (U ×ˢ Set.univ) := by
    refine huU.congr ?_
    intro p hp
    have heq := density_potential n (u p.1) hp.1.1.2 (hpos p.1 hp.1.1)
    simpa only [f] using congrFun heq p.2
  have htau :
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => p.1) (U ×ˢ Set.univ) :=
    contMDiffOn_fst
  have hn :
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun _ : Real × M => (n : Real)) (U ×ˢ Set.univ) :=
    contMDiffOn_const
  have hbracket :
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M =>
          wEntropyBracket n p.1 (R p.1) (q p.1) (f p.1) p.2)
        (U ×ˢ Set.univ) := by
    simpa only [wEntropyBracket] using
      ((htau.mul (hR.add hq)).add hf).sub hn
  have hintegrand :
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M =>
          perelmanDensity n p.1 (f p.1) p.2 *
            wEntropyBracket n p.1 (R p.1) (q p.1) (f p.1) p.2)
        (U ×ˢ Set.univ) :=
    hdens.mul hbracket
  have hft (x : M) :
      HasDerivAt (fun r : Real => f r x) (ft x) s := by
    simpa only [f, ft, q, R, G, sub_neg_eq_add] using
      potential_pde (I := I) Dr G
        (fun r y => -S.scalar (T - r) y) u n huScalar hs hspos
        (hpos s ⟨hs, hspos⟩) x
  have hRt (x : M) :
      HasDerivAt (fun r : Real => R r x) (Rt x) s := by
    simpa only [R, Rt, G] using
      revScalar_time (I := I) S hS T s hTs x
  have hqt (x : M) :
      HasDerivAt (fun r : Real => q r x) (qt x) s := by
    simpa only [q, qt, f, ft, R, G, sub_neg_eq_add] using
      revGradSq_time (I := I) S hS T
        (fun r y => -S.scalar (T - r) y) u n huScalar hpos hs hspos hTs x
  have htrace (x : M) :
      traceTimeDerivMetricAt (I := I) G s x = 2 * R s x := by
    simpa only [G, R] using
      revTrace_eq (I := I) (M := M) (S := S) hS T s hTs x
  have hbaseEq :
      (fun r : Real =>
        wFunctional (volumeMeasureFamily (I := I) (M := M) G r) n r
          (R r) (q r) (f r)) =ᶠ[nhds s]
        (fun r : Real =>
          ∫ x, perelmanDensity n r (f r) x *
            wEntropyBracket n r (R r) (q r) (f r) x
          ∂(volumeMeasureFamily (I := I) (M := M) G r)) := by
    filter_upwards [hUo.mem_nhds hsU] with r hr
    have hdensity : perelmanDensity n r (f r) = u r := by
      simpa only [f] using
        density_potential n (u r) hr.1.2 (hpos r hr.1)
    have hcont : Continuous (perelmanDensity n r (f r)) := by
      rw [hdensity]
      exact (huScalar.sliceSmooth r (Dr.regular_subset hr.1.1)).continuous
    have hmeas : AEMeasurable
        (fun x : M => ENNReal.ofReal (perelmanDensity n r (f r) x))
        (volumeMeasureFamily (I := I) (M := M) G r) :=
      (ENNReal.continuous_ofReal.comp hcont).aemeasurable
    exact wFunctional_base
      (volumeMeasureFamily (I := I) (M := M) G r) n r
      (R r) (q r) (f r) hr.1.2.le hmeas
  have hvar := first_var_joint (I := I) (M := M)
    (g_fam := G.metric)
    (f := fun r x => perelmanDensity n r (f r) x *
      wEntropyBracket n r (R r) (q r) (f r) x)
    hUo hsU hgram hintegrand
  have hbase :
      HasDerivAt
        (fun r : Real =>
          ∫ x, perelmanDensity n r (f r) x *
            wEntropyBracket n r (R r) (q r) (f r) x
          ∂(volumeMeasureFamily (I := I) (M := M) G r))
        (∫ x,
          wEntropyWeightedIntegralVariationIntegrand n s 1
            (f s) ft (fun y => 2 * R s y)
            (wEntropyBracket n s (R s) (q s) (f s))
            (wEntropyBracketVariation s 1 (R s) Rt (q s) qt ft) x
          ∂(volumeMeasureFamily (I := I) (M := M) G s)) s := by
    refine hvar.congr_deriv ?_
    apply integral_congr_ae
    filter_upwards with x
    have hdensDeriv := perelmanDensity_hasDerivAt
      (M := M) (n := n) (tauPath := fun r : Real => r)
      (potentialPath := f) (s0 := s) (tau := s) (tauVariation := 1)
      rfl hspos (hasDerivAt_id (x := s)) hft x
    have hbracketDeriv := wEntropyBracket_hasDerivAt
      (M := M) (n := n) (tauPath := fun r : Real => r)
      (scalarCurvaturePath := R) (gradPotentialNormSqPath := q)
      (potentialPath := f) (s0 := s) (tau := s) (tauVariation := 1)
      rfl (hasDerivAt_id (x := s)) hRt hqt hft x
    have hderiv := (hdensDeriv.mul hbracketDeriv).deriv
    change
      deriv
          ((fun r : Real => perelmanDensity n r (f r) x) *
            fun r : Real => wEntropyBracket n r (R r) (q r) (f r) x) s +
          (1 / 2) * traceTimeDerivMetricAt (I := I) G s x *
            (perelmanDensity n s (f s) x *
              wEntropyBracket n s (R s) (q s) (f s) x) =
        wEntropyWeightedIntegralVariationIntegrand n s 1
          (f s) ft (fun y => 2 * R s y)
          (wEntropyBracket n s (R s) (q s) (f s))
          (wEntropyBracketVariation s 1 (R s) Rt (q s) qt ft) x
    rw [hderiv, htrace x]
    unfold wEntropyWeightedIntegralVariationIntegrand
      wEntropyWeightedMeasureVariationFactor
    ring
  have hout := WEntropyHasFirstVariationAt_of_baseIntegral_hasDerivAt
    (M := M)
    (muPath := volumeMeasureFamily (I := I) (M := M) G)
    (n := n) (tauPath := fun r : Real => r)
    (scalarCurvaturePath := R) (gradPotentialNormSqPath := q)
    (potentialPath := f) (s0 := s)
    hbaseEq hbase
  simpa only [G, f, R, q, ft, Rt, qt] using hout

/-- Along reversed Ricci flow, the first variation of Perelman's `W` functional
is the negative weighted square of `Ric + Hess f - g / (2s)`. -/
theorem w_rev_square
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
    {s : Real} (hs : s ∈ Dr.regular) (hspos : 0 < s)
    (hTs : T - s ∈ D.regular) :
    let n := Module.finrank Real E
    let G := reverseFamily (I := I) (M := M) (flowG (I := I) S) T
    let f : Real -> M -> Real := fun r => perelmanPotential n r (u r)
    let R : Real -> M -> Real := fun r x => S.scalar (T - r) x
    let q : Real -> M -> Real := fun r x =>
      (G.metric r).inner x
        (gradientFun (I := I) (G.metric r) (f r) x)
        (gradientFun (I := I) (G.metric r) (f r) x)
    let hf : ContMDiff I 𝓘(Real, Real) ∞ (f s) := by
      simpa only [f] using
        potential_slice (I := I) Dr G
          (fun r x =>
            (conjCoeff (I := I) (M := M) S (T - r) : M -> Real) x)
          u n hu hs hspos (hpos s ⟨hs, hspos⟩)
    let Sq : M -> Real := fun x =>
      normSq0S (I := I) (G.metric s) x 2
        (metricRicciAt (I := I) (M := M) (G.metric s) x +
          hessianSec (I := I)
            (metricCov (I := I) (M := M) (G.metric s))
            (metricCov_smooth (I := I) (M := M) (G.metric s))
            (f s) hf x -
          (1 / (2 * s)) • metricTensor0S (I := I) (G.metric s) x)
    WEntropyHasFirstVariationAt
      (volumeMeasureFamily (I := I) (M := M) G)
      n (fun r : Real => r) R q f s
      (-2 * s *
        ∫ x, perelmanDensity n s (f s) x * Sq x
          ∂(volumeMeasureFamily (I := I) (M := M) G s)) := by
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
  have hf : ContMDiff I 𝓘(Real, Real) ∞ (f s) := by
    simpa only [f] using
      potential_slice (I := I) Dr G
        (fun r x =>
          (conjCoeff (I := I) (M := M) S (T - r) : M -> Real) x)
        u n hu hs hspos (hpos s ⟨hs, hspos⟩)
  let ft : M -> Real := fun x =>
    laplacianAt (I := I) G s (f s) x - q s x + R s x -
      (n : Real) / (2 * s)
  let Rt : M -> Real := fun x =>
    -(laplacianAt (I := I) G s (R s) x +
      2 * normSq0S (I := I) (G.metric s) x 2 (S.ricci (T - s) x))
  let qt : M -> Real := fun x =>
    (-2 : Real) * S.ricciAt (T - s) x
        (vec2
          (gradientFun (I := I) (G.metric s) (f s) x)
          (gradientFun (I := I) (G.metric s) (f s) x)) +
      2 * (G.metric s).inner x
        (gradientFun (I := I) (G.metric s) ft x)
        (gradientFun (I := I) (G.metric s) (f s) x)
  let μ := volumeMeasureFamily (I := I) (M := M) G s
  have hraw :
      WEntropyHasFirstVariationAt
        (volumeMeasureFamily (I := I) (M := M) G)
        n (fun r : Real => r) R q f s
        (∫ x,
          wEntropyWeightedIntegralVariationIntegrand n s 1
            (f s) ft (fun y => 2 * R s y)
            (wEntropyBracket n s (R s) (q s) (f s))
            (wEntropyBracketVariation s 1 (R s) Rt (q s) qt ft) x ∂μ) := by
    simpa only [G, f, R, q, ft, Rt, qt, μ] using
      w_rev_hasDerivAt (I := I) S hS T n u hu hpos hs hspos hTs
  let g := G.metric s
  let R0 : M -> Real := metricScalarAt (I := I) (M := M) g
  let q0 : M -> Real := fun x =>
    g.inner x (gradientFun (I := I) g (f s) x)
      (gradientFun (I := I) g (f s) x)
  let L0 : M -> Real := Δ_g (I := I) g hf
  let ft0 : M -> Real := fun x =>
    L0 x - q0 x + R0 x - (n : Real) / (2 * s)
  let Rt0 : M -> Real := fun x =>
    -(Δ_g (I := I) g (metricScalar_smooth (I := I) (M := M) g) x +
      2 * normSq0S (I := I) g x 2
        (metricRicciAt (I := I) (M := M) g x))
  let qt0 : M -> Real := fun x =>
    (-2 : Real) * metricRicciAt (I := I) (M := M) g x
        (vec2 (I := I) (gradientFun (I := I) g (f s) x)
          (gradientFun (I := I) g (f s) x)) +
      2 * g.inner x (gradientFun (I := I) g ft0 x)
        (gradientFun (I := I) g (f s) x)
  let A0 : M -> Real := fun x =>
    R0 x + q0 x + s * (Rt0 x + qt0 x) + ft0 x +
      (s * (R0 x + q0 x) + f s x - (n : Real)) *
        (-((n : Real) / (2 * s)) - ft0 x + R0 x)
  let Sq : M -> Real := fun x =>
    normSq0S (I := I) g x 2
      (metricRicciAt (I := I) (M := M) g x +
        hessianSec (I := I) (metricCov (I := I) (M := M) g)
          (metricCov_smooth (I := I) (M := M) g) (f s) hf x -
        (1 / (2 * s)) • metricTensor0S (I := I) g x)
  let μw := expNegPotentialWeightedMeasure μ (f s)
  have hconn : G.connection s = LeviCivita (I := I) g := by
    rfl
  have hR : ContMDiff I 𝓘(Real, Real) ∞ (R s) := by
    change ContMDiff I 𝓘(Real, Real) ∞
      (metricScalarAt (I := I) (M := M) g)
    exact metricScalar_smooth (I := I) (M := M) g
  have hLf (x : M) :
      laplacianAt (I := I) G s (f s) x = Δ_g (I := I) g hf x := by
    exact laplacianAt_eq_delta (I := I) G s hf hconn x
  have hLR (x : M) :
      laplacianAt (I := I) G s (R s) x = Δ_g (I := I) g hR x := by
    exact laplacianAt_eq_delta (I := I) G s hR hconn x
  have hric (x : M) :
      S.ricci (T - s) x = metricRicciAt (I := I) (M := M) g x := by
    calc
      S.ricci (T - s) x = S.ricciAt (T - s) x := by
        simpa only [SolutionOn.ricci, SolutionOn.ricciAt] using
          SolutionFamily.ricci_apply S.base (T - s) x
      _ = metricRicciAt (I := I) (M := M) g x := by rfl
  have hricAt (x : M) :
      S.ricciAt (T - s) x = metricRicciAt (I := I) (M := M) g x := by
    rfl
  have hREq : R s = R0 := by
    rfl
  have hqEq : q s = q0 := by
    rfl
  have hftEq : ft = ft0 := by
    funext x
    dsimp only [ft, ft0, L0]
    rw [hLf x, hREq, hqEq]
  have hRproof :
      hR = metricScalar_smooth (I := I) (M := M) g :=
    Subsingleton.elim _ _
  have hRtEq : Rt = Rt0 := by
    funext x
    dsimp only [Rt, Rt0, g]
    rw [hLR x, hric x, hRproof]
    rfl
  have hqtEq : qt = qt0 := by
    funext x
    dsimp only [qt, qt0]
    rw [hftEq, hricAt x]
  have hA (x : M) :
      R s x + q s x + s * (Rt x + qt x) + ft x +
          (s * (R s x + q s x) + f s x - (n : Real)) *
            (-((n : Real) / (2 * s)) - ft x + R s x) = A0 x := by
    rw [hREq, hqEq, hRtEq, hqtEq, hftEq]
  have hmeas :
      AEMeasurable
        (fun x => ENNReal.ofReal (expNegPotentialDensity (f s) x)) μ :=
    (ENNReal.continuous_ofReal.comp
      (expNegPotentialDensity_contMDiff (I := I) hf).continuous).aemeasurable
  have hperel (a : M -> Real) :
      (∫ x, perelmanDensity n s (f s) x * a x ∂μ) =
        perelmanDensityPrefactor n s * ∫ x, a x ∂μw := by
    rw [expNegPotentialWeightedMeasure_integral_eq_base μ (f s) a hmeas]
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    simp only [perelmanDensity, expNegPotentialDensity]
    ring
  have hsquare :
      (∫ x, A0 x ∂μw) = -2 * s * ∫ x, Sq x ∂μw := by
    simpa only [A0, R0, q0, L0, ft0, Rt0, qt0, Sq, g, μw, μ, n] using
      weighted_w_square (I := I) g hf hspos
  refine hraw.congr_deriv ?_
  calc
    (∫ x,
        wEntropyWeightedIntegralVariationIntegrand n s 1
          (f s) ft (fun y => 2 * R s y)
          (wEntropyBracket n s (R s) (q s) (f s))
          (wEntropyBracketVariation s 1 (R s) Rt (q s) qt ft) x ∂μ) =
        ∫ x, perelmanDensity n s (f s) x * A0 x ∂μ := by
      apply integral_congr_ae
      filter_upwards with x
      rw [← hA x]
      simp only [wEntropyWeightedIntegralVariationIntegrand,
        wEntropyWeightedMeasureVariationFactor, wEntropyBracketVariation,
        wEntropyBracket]
      ring
    _ = perelmanDensityPrefactor n s * ∫ x, A0 x ∂μw := hperel A0
    _ = perelmanDensityPrefactor n s *
          (-2 * s * ∫ x, Sq x ∂μw) := by rw [hsquare]
    _ = -2 * s *
          ∫ x, perelmanDensity n s (f s) x * Sq x ∂μ := by
      rw [hperel Sq]
      ring

/-- Along reversed Ricci flow, Perelman's `W` first variation is nonpositive. -/
theorem w_rev_deriv_nonpos
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
    {s : Real} (hs : s ∈ Dr.regular) (hspos : 0 < s)
    (hTs : T - s ∈ D.regular) :
    let n := Module.finrank Real E
    let G := reverseFamily (I := I) (M := M) (flowG (I := I) S) T
    let f : Real -> M -> Real := fun r => perelmanPotential n r (u r)
    let R : Real -> M -> Real := fun r x => S.scalar (T - r) x
    let q : Real -> M -> Real := fun r x =>
      (G.metric r).inner x
        (gradientFun (I := I) (G.metric r) (f r) x)
        (gradientFun (I := I) (G.metric r) (f r) x)
    wEntropyFirstVariation
      (volumeMeasureFamily (I := I) (M := M) G)
      n (fun r : Real => r) R q f s ≤ 0 := by
  classical
  dsimp only
  rw [wEntropyFirstVariation_eq_of_hasFirstVariationAt
    (w_rev_square (I := I) S hS T u hu hpos hs hspos hTs)]
  refine mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (by norm_num) hspos.le) ?_
  exact integral_nonneg fun x =>
    mul_nonneg
      (by
        unfold perelmanDensity perelmanDensityPrefactor
        exact mul_nonneg
          (Real.rpow_nonneg
            (mul_nonneg
              (mul_nonneg (by norm_num) Real.pi_pos.le)
              hspos.le) _)
          (Real.exp_pos _).le)
      (normSq0S_nonneg (I := I) _ x 2 _)

private theorem le_zero_of_right
    {W : Real → Real} {b : Real} (hb : 0 < b)
    (hcont : ContinuousOn W (Set.Icc (0 : Real) b))
    (hanti : AntitoneOn W (Set.Ioc (0 : Real) b)) :
    ∀ s ∈ Set.Icc (0 : Real) b, W s ≤ W 0 := by
  intro s hs
  rcases eq_or_lt_of_le hs.1 with rfl | hspos
  · exact le_rfl
  have hW0 : Tendsto W (𝓝[>] (0 : Real)) (𝓝 (W 0)) :=
    (hcont 0 ⟨le_rfl, hb.le⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsGT hb)
  apply ge_of_tendsto hW0
  filter_upwards [Ioc_mem_nhdsGT hspos] with r hr
  exact hanti ⟨hr.1, hr.2.trans hs.2⟩ ⟨hspos, hs.2⟩ hr.2

/-- The Galerkin W path is continuous through its smooth initial density after
shrinking to a nontrivial regular reverse-time interval. -/
theorem gallim_w_cont
    [NeZero (Module.finrank Real E)] [I.Boundaryless]
    [BoundarylessManifold I M] [CompactSpace M]
    {D : RealTimeInterval} {S : SolutionOn (I := I) (M := M) D}
    {T : D.RegularTime} {tau : Real}
    {u0 : SmoothCcTensor (S.family.metric (T : Real)) 0 0}
    {V : Nat → Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    {phi : Nat → Nat}
    {ulim : Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    (hS : IsSolutionOn (I := I) S)
    (hDim : Module.finrank Real E = 3) (hτ : 0 < tau)
    (hlim : IsConjGalSubseq (I := I) (M := M)
      S T tau u0 V phi ulim)
    {a : Real} (ha : 0 < a)
    (hpos : ∀ q ∈ Set.Icc (0 : Real) tau, ∀ x : M,
      0 < scalarSpecSum (I := I) (M := M)
        (S.family.metric (T : Real)) (fun i s => ulim s i) q x) :
    ∃ tau' : Real, 0 < tau' ∧ tau' ≤ tau ∧
      ContinuousOn
        (fun q : Real =>
          let n := Module.finrank Real E
          let G := reverseFamily (I := I) (M := M)
            (flowG (I := I) S) (T : Real)
          let u : Real → M → Real := fun s x =>
            scalarSpecSum (I := I) (M := M)
              (S.family.metric (T : Real)) (fun i r => ulim r i) s x
          let f : Real → M → Real := fun s =>
            perelmanPotential n (a + s) (u s)
          let R : Real → M → Real := fun s x => S.scalar ((T : Real) - s) x
          let Q : Real → M → Real := fun s x =>
            (G.metric s).inner x
              (gradientFun (I := I) (G.metric s) (f s) x)
              (gradientFun (I := I) (G.metric s) (f s) x)
          wFunctional (volumeMeasureFamily (I := I) (M := M) G q)
            n (a + q) (R q) (Q q) (f q))
        (Set.Icc (0 : Real) tau') := by
  classical
  let n := Module.finrank Real E
  let G := reverseFamily (I := I) (M := M)
    (flowG (I := I) S) (T : Real)
  let u : Real → M → Real := fun s x =>
    scalarSpecSum (I := I) (M := M) (S.family.metric (T : Real))
      (fun i r => ulim r i) s x
  let f : Real → M → Real := fun s => perelmanPotential n (a + s) (u s)
  let R : Real → M → Real := fun s x => S.scalar ((T : Real) - s) x
  let dU : Real → M → Real := fun s x =>
    (G.metric s).inner x
      (gradientFun (I := I) (G.metric s) (u s) x)
      (gradientFun (I := I) (G.metric s) (u s) x)
  let Q : Real → M → Real := fun s x =>
    (G.metric s).inner x
      (gradientFun (I := I) (G.metric s) (f s) x)
      (gradientFun (I := I) (G.metric s) (f s) x)
  let Qbase : Real → M → Real := fun s x => (u s x ^ 2)⁻¹ * dU s x
  let Wpath : Real → Real := fun s =>
    wFunctional (volumeMeasureFamily (I := I) (M := M) G s)
      n (a + s) (R s) (Q s) (f s)
  obtain ⟨tauG, htauG, _htauG_tau, hgrad⟩ :=
    galLim_grad_cont (I := I) (M := M) hS hDim hτ hlim
  obtain ⟨tauH, htauH, _htauH_tau, hheat⟩ :=
    heatpot_of_gallim (I := I) (M := M) hS hτ hlim
  let Wr : Set Real := (fun r : Real => (T : Real) - r) ⁻¹' D.regular
  have hWro : IsOpen Wr :=
    D.regular_isOpen.preimage (continuous_const.sub continuous_id)
  have h0Wr : (0 : Real) ∈ Wr := by
    change (T : Real) - 0 ∈ D.regular
    simpa only [sub_zero] using T.2
  obtain ⟨l, w, h0lw, hlw⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp (hWro.mem_nhds h0Wr)
  let tau' : Real := min tauG (min tauH (min tau (w / 2)))
  have htau' : 0 < tau' := by
    dsimp only [tau']
    exact lt_min htauG (lt_min htauH (lt_min hτ (half_pos h0lw.2)))
  have htau'_G : tau' ≤ tauG := min_le_left _ _
  have htau'_H : tau' ≤ tauH :=
    (min_le_right _ _).trans (min_le_left _ _)
  have htau'_tau : tau' ≤ tau :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hmap : Set.MapsTo (fun r : Real => (T : Real) - r)
      (Set.Icc (0 : Real) tau') D.regular := by
    intro r hr
    apply hlw
    refine ⟨h0lw.1.trans_le hr.1, ?_⟩
    exact lt_of_le_of_lt
      (hr.2.trans ((min_le_right tauG (min tauH (min tau (w / 2)))).trans
        ((min_le_right tauH (min tau (w / 2))).trans
          (min_le_right tau (w / 2)))))
      (half_lt_self h0lw.2)
  let K : Set (Real × M) := Set.Icc (0 : Real) tau' ×ˢ (Set.univ : Set M)
  have hKtau : K ⊆ Set.Icc (0 : Real) tau ×ˢ (Set.univ : Set M) := by
    rintro ⟨s, x⟩ hsx
    exact ⟨⟨hsx.1.1, hsx.1.2.trans htau'_tau⟩, hsx.2⟩
  have hKtauG : K ⊆ Set.Icc (0 : Real) tauG ×ˢ (Set.univ : Set M) := by
    rintro ⟨s, x⟩ hsx
    exact ⟨⟨hsx.1.1, hsx.1.2.trans htau'_G⟩, hsx.2⟩
  have hu : ContinuousOn (fun p : Real × M => u p.1 p.2) K := by
    simpa only [u, K] using
      (galLim_joint_cont (I := I) (M := M) hτ hlim).mono hKtau
  have hdU : ContinuousOn (fun p : Real × M => dU p.1 p.2) K := by
    simpa only [dU, G, u, K] using hgrad.mono hKtauG
  have hgram (x₀ : M) (i j : Fin (Module.finrank Real E)) :
      ContinuousOn
        (fun p : Real × M =>
          chartGramMatrix (I := I) (G.metric p.1) x₀ p.2 i j)
        (Set.Icc (0 : Real) tau' ×ˢ
          (trivializationAt E (TangentSpace I) x₀).baseSet) := by
    simpa only [G] using
      (revGram_smooth (I := I) (M := M) (S := S) hS (T : Real)
        hmap x₀ i j).continuousOn
  have hrev : ContMDiff (𝓘(Real, Real).prod I)
      (𝓘(Real, Real).prod I) ∞
      (fun p : Real × M => ((T : Real) - p.1, p.2)) :=
    (contMDiff_const.sub contMDiff_fst).prodMk contMDiff_snd
  have hR : ContinuousOn (fun p : Real × M => R p.1 p.2) K := by
    have hRs := (scalar_joint (I := I) S hS).comp hrev.contMDiffOn
      (fun (p : Real × M) (hp : p ∈ K) =>
        ⟨hmap hp.1, Set.mem_univ p.2⟩)
    simpa only [R, K, Function.comp_apply] using hRs.continuousOn
  have hscale : ContinuousOn (fun p : Real × M => a + p.1) K :=
    continuousOn_const.add continuousOn_fst
  have hscale_pos (p : Real × M) (hp : p ∈ K) : 0 < a + p.1 :=
    add_pos_of_pos_of_nonneg ha hp.1.1
  have hpref : ContinuousOn
      (fun p : Real × M => perelmanDensityPrefactor n (a + p.1)) K := by
    unfold perelmanDensityPrefactor
    exact ((continuousOn_const.mul continuousOn_const).mul hscale).rpow_const
      (fun p hp => Or.inl (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
        (hscale_pos p hp).ne'))
  have hf : ContinuousOn (fun p : Real × M => f p.1 p.2) K := by
    unfold f perelmanPotential
    exact (hu.div hpref (fun p hp =>
      (prefactor_pos n (hscale_pos p hp)).ne')).log (fun p hp =>
        div_ne_zero (hpos p.1 (hKtau hp).1 p.2).ne'
          (prefactor_pos n (hscale_pos p hp)).ne') |>.neg
  have hQbase : ContinuousOn (fun p : Real × M => Qbase p.1 p.2) K := by
    exact ((hu.pow 2).inv₀ (fun p hp => pow_ne_zero 2
      (hpos p.1 (hKtau hp).1 p.2).ne')).mul hdU
  have hn : ContinuousOn (fun _ : Real × M => (n : Real)) K :=
    continuousOn_const
  let baseInt : Real → M → Real := fun s x =>
    u s x * wEntropyBracket n (a + s) (R s) (Qbase s) (f s) x
  have hbaseInt : ContinuousOn (fun p : Real × M => baseInt p.1 p.2) K := by
    dsimp only [baseInt, wEntropyBracket]
    exact hu.mul (((hscale.mul (hR.add hQbase)).add hf).sub hn)
  have hWbase (s : Real) (hs : s ∈ Set.Icc (0 : Real) tau') :
      Wpath s = ∫ x, baseInt s x
        ∂(volumeMeasureFamily (I := I) (M := M) G s) := by
    have hsTau : s ∈ Set.Icc (0 : Real) tau :=
      ⟨hs.1, hs.2.trans htau'_tau⟩
    have hsH : s ∈ Set.Icc (0 : Real) tauH :=
      ⟨hs.1, hs.2.trans htau'_H⟩
    have husmooth := hheat.sliceSmooth s hsH
    have hspos : 0 < a + s := add_pos_of_pos_of_nonneg ha hs.1
    have hdensity := density_potential n (u s) hspos (hpos s hsTau)
    have humeas : AEMeasurable
        (fun x : M => ENNReal.ofReal (perelmanDensity n (a + s) (f s) x))
        (volumeMeasureFamily (I := I) (M := M) G s) := by
      rw [show perelmanDensity n (a + s) (f s) = u s by
        simpa only [f] using hdensity]
      exact (ENNReal.continuous_ofReal.comp husmooth.continuous).aemeasurable
    rw [show Wpath s = wFunctional
      (volumeMeasureFamily (I := I) (M := M) G s) n (a + s)
        (R s) (Q s) (f s) by rfl]
    rw [wFunctional_base _ _ _ _ _ _ hspos.le humeas]
    apply integral_congr_ae
    filter_upwards with x
    rw [show perelmanDensity n (a + s) (f s) x = u s x by
      simpa only [f] using congrFun hdensity x]
    have hQeq : Q s = Qbase s := by
      funext y
      simpa only [Q, Qbase, dU, f] using
        potential_grad_sq (I := I) (G.metric s) n husmooth
          (hpos s hsTau) hspos y
    rw [hQeq]
  have hIntegral : ContinuousOn
      (fun s : Real => ∫ x, baseInt s x
        ∂(volumeMeasureFamily (I := I) (M := M) G s))
      (Set.Icc (0 : Real) tau') := by
    simpa only [volumeMeasureFamily, metricFamilyForMeasure, K] using
      integral_family_cont (I := I) (M := M) isCompact_Icc hgram hbaseInt
  refine ⟨tau', htau', htau'_tau, ?_⟩
  simpa only [Wpath, n, G, u, f, R, Q] using
    hIntegral.congr hWbase

/-- Perelman's `W` functional is antitone on every positive closed reverse-time
interval contained in the two regular-time domains. -/
theorem w_rev_antitone
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
    (hDr : Set.Icc a b ⊆ Dr.regular)
    (hD : ∀ r ∈ Set.Icc a b, T - r ∈ D.regular) :
    let n := Module.finrank Real E
    let G := reverseFamily (I := I) (M := M) (flowG (I := I) S) T
    let f : Real -> M -> Real := fun r => perelmanPotential n r (u r)
    let R : Real -> M -> Real := fun r x => S.scalar (T - r) x
    let q : Real -> M -> Real := fun r x =>
      (G.metric r).inner x
        (gradientFun (I := I) (G.metric r) (f r) x)
        (gradientFun (I := I) (G.metric r) (f r) x)
    AntitoneOn
      (wFunctionalAlong
        (volumeMeasureFamily (I := I) (M := M) G)
        n (fun r : Real => r) R q f)
      (Set.Icc a b) := by
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
    wFunctionalAlong
      (volumeMeasureFamily (I := I) (M := M) G)
      n (fun r : Real => r) R q f
  change AntitoneOn W (Set.Icc a b)
  have hrpos (r : Real) (hr : r ∈ Set.Icc a b) : 0 < r :=
    lt_of_lt_of_le ha hr.1
  have hcont : ContinuousOn W (Set.Icc a b) := by
    intro r hr
    have hsq := w_rev_square (I := I) S hS T u hu hpos
      (s := r) (hDr hr) (hrpos r hr) (hD r hr)
    change HasDerivAt W _ r at hsq
    exact hsq.continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn Real W (interior (Set.Icc a b)) := by
    intro r hr
    have hrI : r ∈ Set.Icc a b := interior_subset hr
    have hsq := w_rev_square (I := I) S hS T u hu hpos
      (s := r) (hDr hrI) (hrpos r hrI) (hD r hrI)
    change HasDerivAt W _ r at hsq
    exact hsq.differentiableAt.differentiableWithinAt
  refine antitoneOn_of_deriv_nonpos (convex_Icc a b) hcont hdiff ?_
  intro r hr
  have hrI : r ∈ Set.Icc a b := interior_subset hr
  change
    wEntropyFirstVariation
      (volumeMeasureFamily (I := I) (M := M) G)
      n (fun z : Real => z) R q f r ≤ 0
  exact w_rev_deriv_nonpos (I := I) S hS T u hu hpos
    (s := r) (hDr hrI) (hrpos r hrI) (hD r hrI)

/-- On a nontrivial short Galerkin interval, every positive-time W value is at
most the value of the prescribed smooth density at reverse time zero. -/
theorem gallim_w_le
    [NeZero (Module.finrank Real E)] [I.Boundaryless]
    [BoundarylessManifold I M] [CompactSpace M]
    {D : RealTimeInterval} {S : SolutionOn (I := I) (M := M) D}
    {T : D.RegularTime} {tau : Real}
    {u0 : SmoothCcTensor (S.family.metric (T : Real)) 0 0}
    {V : Nat → Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    {phi : Nat → Nat}
    {ulim : Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    (hS : IsSolutionOn (I := I) S)
    (hDim : Module.finrank Real E = 3) (hτ : 0 < tau)
    (hlim : IsConjGalSubseq (I := I) (M := M)
      S T tau u0 V phi ulim)
    {a : Real} (ha : 0 < a)
    (hpos : ∀ q ∈ Set.Icc (0 : Real) tau, ∀ x : M,
      0 < scalarSpecSum (I := I) (M := M)
        (S.family.metric (T : Real)) (fun i s => ulim s i) q x) :
    ∃ tau' : Real, 0 < tau' ∧ tau' ≤ tau ∧
      ∀ q ∈ Set.Icc (0 : Real) tau',
        (let n := Module.finrank Real E
         let G := reverseFamily (I := I) (M := M)
           (flowG (I := I) S) (T : Real)
         let u : Real → M → Real := fun s x =>
           scalarSpecSum (I := I) (M := M)
             (S.family.metric (T : Real)) (fun i r => ulim r i) s x
         let f : Real → M → Real := fun s =>
           perelmanPotential n (a + s) (u s)
         let R : Real → M → Real := fun s x => S.scalar ((T : Real) - s) x
         let Q : Real → M → Real := fun s x =>
           (G.metric s).inner x
             (gradientFun (I := I) (G.metric s) (f s) x)
             (gradientFun (I := I) (G.metric s) (f s) x)
         wFunctional (volumeMeasureFamily (I := I) (M := M) G q)
           n (a + q) (R q) (Q q) (f q)) ≤
        (let n := Module.finrank Real E
         let G := reverseFamily (I := I) (M := M)
           (flowG (I := I) S) (T : Real)
         let u : Real → M → Real := fun s x =>
           scalarSpecSum (I := I) (M := M)
             (S.family.metric (T : Real)) (fun i r => ulim r i) s x
         let f : Real → M → Real := fun s =>
           perelmanPotential n (a + s) (u s)
         let R : Real → M → Real := fun s x => S.scalar ((T : Real) - s) x
         let Q : Real → M → Real := fun s x =>
           (G.metric s).inner x
             (gradientFun (I := I) (G.metric s) (f s) x)
             (gradientFun (I := I) (G.metric s) (f s) x)
         wFunctional (volumeMeasureFamily (I := I) (M := M) G 0)
           n a (R 0) (Q 0) (f 0)) := by
  classical
  let n := Module.finrank Real E
  let G := reverseFamily (I := I) (M := M)
    (flowG (I := I) S) (T : Real)
  let u : Real → M → Real := fun s x =>
    scalarSpecSum (I := I) (M := M) (S.family.metric (T : Real))
      (fun i r => ulim r i) s x
  let f : Real → M → Real := fun s => perelmanPotential n (a + s) (u s)
  let R : Real → M → Real := fun s x => S.scalar ((T : Real) - s) x
  let Q : Real → M → Real := fun s x =>
    (G.metric s).inner x
      (gradientFun (I := I) (G.metric s) (f s) x)
      (gradientFun (I := I) (G.metric s) (f s) x)
  let W : Real → Real := fun s =>
    wFunctional (volumeMeasureFamily (I := I) (M := M) G s)
      n (a + s) (R s) (Q s) (f s)
  obtain ⟨tauC, htauC, _htauC_tau, hcontC⟩ :=
    gallim_w_cont (I := I) (M := M) hS hDim hτ hlim ha hpos
  obtain ⟨tauH, htauH, htauH_tau, hheat⟩ :=
    heatpot_of_gallim (I := I) (M := M) hS hτ hlim
  let Wr : Set Real := (fun r : Real => (T : Real) - r) ⁻¹' D.regular
  have hWro : IsOpen Wr :=
    D.regular_isOpen.preimage (continuous_const.sub continuous_id)
  have h0Wr : (0 : Real) ∈ Wr := by
    change (T : Real) - 0 ∈ D.regular
    simpa only [sub_zero] using T.2
  obtain ⟨l, w, h0lw, hlw⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp (hWro.mem_nhds h0Wr)
  let rho : Real := min tauC (min tauH (min tau (w / 2)))
  have hrho : 0 < rho := by
    dsimp only [rho]
    exact lt_min htauC (lt_min htauH (lt_min hτ (half_pos h0lw.2)))
  let tau' : Real := rho / 2
  have htau' : 0 < tau' := by
    exact half_pos hrho
  have htau'_rho : tau' < rho := by
    exact half_lt_self hrho
  have htau'_C : tau' ≤ tauC :=
    htau'_rho.le.trans (min_le_left _ _)
  have htau'_H : tau' < tauH :=
    htau'_rho.trans_le ((min_le_right tauC _).trans (min_le_left _ _))
  have htau'_tau : tau' ≤ tau :=
    htau'_rho.le.trans ((min_le_right tauC _).trans
      ((min_le_right tauH _).trans (min_le_left _ _)))
  have hmap : Set.MapsTo (fun r : Real => (T : Real) - r)
      (Set.Icc (0 : Real) tau') D.regular := by
    intro r hr
    apply hlw
    refine ⟨h0lw.1.trans_le hr.1, ?_⟩
    have hrw : r ≤ w / 2 :=
      hr.2.trans (htau'_rho.le.trans ((min_le_right tauC _).trans
        ((min_le_right tauH _).trans (min_le_right tau (w / 2)))))
    exact lt_of_le_of_lt hrw (half_lt_self h0lw.2)
  have hcont : ContinuousOn W (Set.Icc (0 : Real) tau') := by
    simpa only [W, n, G, u, f, R, Q] using
      hcontC.mono (Set.Icc_subset_Icc_right htau'_C)
  let Dr := RealTimeInterval.closed 0 tauH htauH.le
  let uShift : Real → M → Real := fun r x => u (r - a) x
  have hheatShift :
      DifferentialGeometry.Analysis.Parabolic.IsHeatPotOn
        (Dr.timeShift (-a))
        (reverseFamily (I := I) (M := M) (flowG (I := I) S) ((T : Real) + a))
        (fun r x =>
          (conjCoeff (I := I) (M := M) S ((T : Real) + a - r) : M → Real) x)
        uShift := by
    have hraw := heat_pot_add (I := I) (M := M) Dr
      (flowG (I := I) S)
      (fun r x =>
        (conjCoeff (I := I) (M := M) S ((T : Real) - r) : M → Real) x)
      u (T : Real) a hheat
    have hcoeff :
        (fun r x =>
          (conjCoeff (I := I) (M := M) S ((T : Real) - (r - a)) : M → Real) x) =
        fun r x =>
          (conjCoeff (I := I) (M := M) S ((T : Real) + a - r) : M → Real) x := by
      funext r x
      congr 2
      ring
    rw [hcoeff] at hraw
    simpa only [uShift] using hraw
  have hposShift : ∀ r : Real,
      r ∈ (Dr.timeShift (-a)).regular ∩ Set.Ioi (0 : Real) →
      ∀ x : M, 0 < uShift r x := by
    intro r hr x
    have hrOld : r - a ∈ Set.Ioo (0 : Real) tauH := by
      simpa only [Dr, RealTimeInterval.timeShift_regular, Set.mem_setOf_eq,
        RealTimeInterval.closed, sub_eq_add_neg] using hr.1
    exact hpos (r - a)
      ⟨hrOld.1.le, hrOld.2.le.trans htauH_tau⟩ x
  let GShift := reverseFamily (I := I) (M := M)
    (flowG (I := I) S) ((T : Real) + a)
  let fShift : Real → M → Real := fun r =>
    perelmanPotential n r (uShift r)
  let RShift : Real → M → Real := fun r x =>
    S.scalar ((T : Real) + a - r) x
  let QShift : Real → M → Real := fun r x =>
    (GShift.metric r).inner x
      (gradientFun (I := I) (GShift.metric r) (fShift r) x)
      (gradientFun (I := I) (GShift.metric r) (fShift r) x)
  let WShift : Real → Real :=
    wFunctionalAlong
      (volumeMeasureFamily (I := I) (M := M) GShift)
      n (fun r : Real => r) RShift QShift fShift
  have hWShift (q : Real) : WShift (a + q) = W q := by
    have hmetric : GShift.metric (a + q) = G.metric q := by
      change S.family.metric ((T : Real) + a - (a + q)) =
        S.family.metric ((T : Real) - q)
      rw [show (T : Real) + a - (a + q) = (T : Real) - q by ring]
    have huq : uShift (a + q) = u q := by
      funext x
      simp only [uShift, add_sub_cancel_left]
    have hfq : fShift (a + q) = f q := by
      dsimp only [fShift, f]
      rw [huq]
    have hRq : RShift (a + q) = R q := by
      funext x
      change S.scalar ((T : Real) + a - (a + q)) x =
        S.scalar ((T : Real) - q) x
      rw [show (T : Real) + a - (a + q) = (T : Real) - q by ring]
    have hQq : QShift (a + q) = Q q := by
      funext x
      dsimp only [QShift, Q]
      rw [hmetric, hfq]
    have hmu :
        volumeMeasureFamily (I := I) (M := M) GShift (a + q) =
          volumeMeasureFamily (I := I) (M := M) G q := by
      change riemannianVolumeMeasure (I := I) (M := M) (GShift.metric (a + q)) =
        riemannianVolumeMeasure (I := I) (M := M) (G.metric q)
      rw [hmetric]
    dsimp only [WShift, wFunctionalAlong]
    rw [hmu, hRq, hQq, hfq]
  have hanti : AntitoneOn W (Set.Ioc (0 : Real) tau') := by
    intro r hr s hs hrs
    have hDr : Set.Icc (a + r) (a + s) ⊆ (Dr.timeShift (-a)).regular := by
      intro z hz
      change z - a ∈ Set.Ioo (0 : Real) tauH
      constructor
      · rw [sub_pos]
        exact (lt_add_of_pos_right a hr.1).trans_le hz.1
      · have hsH : s < tauH := hs.2.trans_lt htau'_H
        linarith [hz.2]
    have hD : ∀ z ∈ Set.Icc (a + r) (a + s),
        (T : Real) + a - z ∈ D.regular := by
      intro z hz
      have hz' : z - a ∈ Set.Icc (0 : Real) tau' := by
        constructor
        · linarith [hr.1, hz.1]
        · linarith [hz.2, hs.2]
      rw [show (T : Real) + a - z = (T : Real) - (z - a) by ring]
      exact hmap hz'
    have hmono : AntitoneOn WShift (Set.Icc (a + r) (a + s)) := by
      simpa only [WShift, GShift, fShift, RShift, QShift] using
        w_rev_antitone (I := I) S hS ((T : Real) + a)
          uShift hheatShift hposShift (add_pos ha hr.1) hDr hD
    have hleft : a + r ∈ Set.Icc (a + r) (a + s) :=
      ⟨le_rfl, add_le_add_right hrs a⟩
    have hright : a + s ∈ Set.Icc (a + r) (a + s) :=
      ⟨add_le_add_right hrs a, le_rfl⟩
    have hle := hmono hleft hright (add_le_add_right hrs a)
    rw [hWShift s, hWShift r] at hle
    exact hle
  refine ⟨tau', htau', htau'_tau, ?_⟩
  intro q hq
  simpa only [W, n, G, u, f, R, Q, add_zero] using
    le_zero_of_right htau' hcont hanti q hq

end

end DifferentialGeometry.PDE.RicciFlow.Entropy
