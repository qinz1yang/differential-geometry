import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SurfaceEntropyContinuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SurfaceEntropyDerivative
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SurfaceEntropySquares
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CompactPoisson
import DifferentialGeometry.Geometry.Metric.Family.Continuity
import Mathlib.Analysis.Calculus.Deriv.MeanValue

set_option autoImplicit false

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.Tensor.Coordinates

noncomputable section

open Bundle Filter MeasureTheory
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Tensor0SBundle
open CanonicalNeighborhood
open scoped Manifold ContDiff _root_.Topology

private theorem surfaceFlow_continuousOn_Iic_of_slabs
    {f : Real → Real}
    (hf : ∀ a : Real, a ≤ 0 → ContinuousOn f (Set.Icc a 0)) :
    ContinuousOn f (Set.Iic 0) := by
  intro t ht
  change t ≤ 0 at ht
  have hlt : t - 1 < t := sub_lt_self t zero_lt_one
  have hleft : t - 1 ≤ 0 := hlt.le.trans ht
  have hlocal : Set.Icc (t - 1) 0 ∈ 𝓝[Set.Iic 0] t := by
    have hnb : Set.Ioi (t - 1) ∈ 𝓝 t := isOpen_Ioi.mem_nhds hlt
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hnb] with s hs hsl
    exact ⟨hsl.le, hs⟩
  exact ((hf (t - 1) hleft) t ⟨hlt.le, ht⟩).mono_of_mem_nhdsWithin hlocal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [IsManifold I 1 M] [T2Space M] [CompactSpace M]
variable {D : RealTimeInterval}

local instance surfaceFlowMeasurable : MeasurableSpace M := borel M
local instance surfaceFlowBorel : BorelSpace M := ⟨rfl⟩

omit [CompactSpace M] in
theorem surfaceFlow_chartGram_continuousOn
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (x₀ : M) (i j : Fin (Module.finrank Real E)) :
    ContinuousOn
      (fun p : Real × M => chartGramMatrix (I := I) (S.family.metric p.1) x₀ p.2 i j)
      (D.carrier ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := by
  classical
  let U := D.carrier ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet
  let b : U → M := fun p => p.1.2
  let v : Fin 2 → (p : U) → TangentSpace I (b p) :=
    fun a p => chartBasisVecFiber (I := I) x₀ (if a = 0 then i else j) p.1.2
  have hb : Continuous b := continuous_snd.comp continuous_subtype_val
  have hv : ∀ a : Fin 2, Continuous (fun p : U =>
      TotalSpace.mk' E (E := fun x : M => TangentSpace I x) (b p) (v a p)) := by
    intro a
    exact (chartBasisVec_contMDiffOn (I := I) x₀
      (if a = 0 then i else j)).continuousOn.comp_continuous
      hb (fun p => p.2.2)
  have heval := hS.smoothMetric.metricTensor_cont.eval_continuous
    (P := U) (τ := fun p => p.1.1) (b := b)
    (continuous_fst.comp continuous_subtype_val) (fun p => p.2.1) hb hv
  rw [continuousOn_iff_continuous_domRestrict]
  refine heval.congr ?_
  intro p
  change metricTensorField (I := I) (S.family.metric p.1.1) (b p)
      (fun a : Fin 2 => v a p) =
    chartGramMatrix (I := I) (S.family.metric p.1.1) x₀ p.1.2 i j
  rw [metricTensorField_apply, chartGramMatrix_apply]
  simp [v, b]

section FlowContinuity

variable [Nonempty M]

theorem surfaceFlow_integrals_continuousOn_compact
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {K : Set Real} (hK : IsCompact K) (hKD : K ⊆ D.carrier) :
    ContinuousOn (fun t => surfaceArea (S.family.metric t)) K ∧
      ContinuousOn (fun t => totalScalarCurvature (S.family.metric t)) K ∧
      ContinuousOn (fun t => surfaceEntropy (S.family.metric t)) K := by
  have hGram : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContinuousOn
        (fun p : Real × M => chartGramMatrix (I := I) (S.family.metric p.1) x₀ p.2 i j)
        (K ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := by
    intro x₀ i j
    exact (surfaceFlow_chartGram_continuousOn S hS x₀ i j).mono
      (Set.prod_mono hKD (Set.Subset.refl _))
  have hScalar : ContinuousOn
      (fun p : Real × M => metricScalarAt (I := I) (S.family.metric p.1) p.2)
      (K ×ˢ Set.univ) :=
    hS.scalarCont.mono (Set.prod_mono hKD (Set.Subset.refl _))
  exact ⟨surfaceArea_continuousOn hK hGram,
    totalScalarCurvature_continuousOn hK hGram hScalar,
    surfaceEntropy_continuousOn hK hGram hScalar⟩

theorem ancientSurfaceFlow_integrals_continuousOn
    (S : SolutionOn (I := I) (M := M) ancientTimeInterval) (hS : IsSolutionOn S) :
    ContinuousOn (fun t => surfaceArea (S.family.metric t)) (Set.Iic 0) ∧
      ContinuousOn (fun t => totalScalarCurvature (S.family.metric t)) (Set.Iic 0) ∧
      ContinuousOn (fun t => surfaceEntropy (S.family.metric t)) (Set.Iic 0) := by
  have hslab (a : Real) :
      ContinuousOn (fun t => surfaceArea (S.family.metric t)) (Set.Icc a 0) ∧
        ContinuousOn (fun t => totalScalarCurvature (S.family.metric t)) (Set.Icc a 0) ∧
        ContinuousOn (fun t => surfaceEntropy (S.family.metric t)) (Set.Icc a 0) :=
    surfaceFlow_integrals_continuousOn_compact S hS isCompact_Icc (fun _ ht => ht.2)
  exact ⟨surfaceFlow_continuousOn_Iic_of_slabs (fun a _ => (hslab a).1),
    surfaceFlow_continuousOn_Iic_of_slabs (fun a _ => (hslab a).2.1),
    surfaceFlow_continuousOn_Iic_of_slabs (fun a _ => (hslab a).2.2)⟩

end FlowContinuity

section ConservedQuantities

variable [I.Boundaryless] [Nonempty M]

theorem ancientSurfaceFlow_totalScalar_eq_terminal
    (S : SolutionOn (I := I) (M := M) ancientTimeInterval) (hS : IsSolutionOn S)
    (hdim : Module.finrank Real E = 2) {t : Real} (ht : t ≤ 0) :
    totalScalarCurvature (S.family.metric t) = totalScalarCurvature (S.family.metric 0) := by
  have hcont : ContinuousOn (fun s => totalScalarCurvature (S.family.metric s))
      (Set.Icc t 0) :=
    (ancientSurfaceFlow_integrals_continuousOn S hS).2.1.mono (fun _ hs => hs.2)
  have hconstant := constant_of_has_deriv_right_zero hcont (fun s hs =>
    (totalScalarCurvature_hasDerivAt_zero S hS hdim hs.2).hasDerivWithinAt)
  exact (hconstant 0 ⟨ht, le_rfl⟩).symm

theorem ancientSurfaceFlow_area_eq_terminal_sub
    (S : SolutionOn (I := I) (M := M) ancientTimeInterval) (hS : IsSolutionOn S)
    (hdim : Module.finrank Real E = 2) {t : Real} (ht : t ≤ 0) :
    surfaceArea (S.family.metric t) = surfaceArea (S.family.metric 0) -
      totalScalarCurvature (S.family.metric 0) * t := by
  let C := totalScalarCurvature (S.family.metric 0)
  let A := fun s : Real => surfaceArea (S.family.metric s)
  have hcontA : ContinuousOn A (Set.Icc t 0) :=
    (ancientSurfaceFlow_integrals_continuousOn S hS).1.mono (fun _ hs => hs.2)
  have hcont : ContinuousOn (fun s : Real => A s + C * s) (Set.Icc t 0) :=
    hcontA.add (continuous_const.mul continuous_id).continuousOn
  have hderiv : ∀ s ∈ Set.Ico t 0,
      HasDerivWithinAt (fun u : Real => A u + C * u) 0 (Set.Ici s) s := by
    intro s hs
    have hA := surfaceArea_hasDerivAt S hS hs.2
    have hlinear : HasDerivAt (fun u : Real => C * u) C s :=
      hasDerivAt_const_mul (x := s) C
    have hc : totalScalarCurvature (S.family.metric s) = C :=
      ancientSurfaceFlow_totalScalar_eq_terminal S hS hdim hs.2.le
    exact ((hA.add hlinear).congr_deriv (by rw [hc]; ring)).hasDerivWithinAt
  have hconstant := constant_of_has_deriv_right_zero hcont hderiv
  have hterminal := hconstant 0 ⟨ht, le_rfl⟩
  change A t = A 0 - C * t
  change A 0 + C * 0 = A t + C * t at hterminal
  linarith

end ConservedQuantities

section EntropyFlow

variable [I.Boundaryless] [ConnectedSpace M]

theorem surfaceEntropy_exists_meanZero_poisson
    (g : SmoothRiemannianMetric I M) :
    ∃ f : C^∞⟮I, M; Real⟯,
      (∫ x, f x ∂(riemannianVolumeMeasure (I := I) (M := M) g)) = 0 ∧
        ∀ x : M, ΔG (I := I) g f x =
          meanScalarCurvature g - metricScalarAt (I := I) g x := by
  let q := fun x : M => meanScalarCurvature g - metricScalarAt (I := I) g x
  have hqSmooth : ContMDiff I 𝓘(Real, Real) ∞ q :=
    contMDiff_const.sub (metricScalar_smooth g)
  have hqMean : (∫ x, q x ∂(riemannianVolumeMeasure (I := I) (M := M) g)) = 0 :=
    surfaceEntropy_poisson_rhs_integral_zero g
  obtain ⟨f, hf, _⟩ := existsUnique_meanZero_smooth_poisson g ⟨q, hqSmooth⟩ hqMean
  exact ⟨f, hf.1, hf.2⟩

theorem surfaceEntropy_hasDerivAt_two_squares
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hdim : Module.finrank Real E = 2)
    (hpositive : ∀ s ∈ D.regular, ∀ x : M, 0 < S.scalar s x)
    {t : Real} (ht : t ∈ D.regular) :
    let g := S.family.metric t
    let μ := riemannianVolumeMeasure (I := I) (M := M) g
    let R := S.scalar t
    ∃ f : C^∞⟮I, M; Real⟯,
      (∫ x, f x ∂μ) = 0 ∧
      (∀ x : M, ΔG (I := I) g f x = meanScalarCurvature g - R x) ∧
      HasDerivAt (fun s => surfaceEntropy (S.family.metric s))
        (-(∫ x, R x * g.inner x
            (gradFun (I := I) g (fun y => Real.log (R y)) x - gradFun (I := I) g f x)
            (gradFun (I := I) g (fun y => Real.log (R y)) x - gradFun (I := I) g f x) ∂μ) -
          2 * ∫ x, normSq0S (I := I) g x 2
            (hessTensorAt (I := I) g f x -
              (ΔG (I := I) g f x / 2) • metricTensor0S (I := I) g x) ∂μ) t := by
  let g := S.family.metric t
  obtain ⟨f, hfMean, hfEquation⟩ := surfaceEntropy_exists_meanZero_poisson g
  refine ⟨f, hfMean, hfEquation, ?_⟩
  have hd := surfaceEntropy_hasDerivAt_first S hS hdim hpositive ht
  exact hd.congr_deriv
    (surfaceEntropy_static_two_squares g hdim (hpositive t ht) f hfEquation)

theorem surfaceEntropy_deriv_nonpos
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hdim : Module.finrank Real E = 2)
    (hpositive : ∀ s ∈ D.regular, ∀ x : M, 0 < S.scalar s x)
    {t : Real} (ht : t ∈ D.regular) :
    deriv (fun s => surfaceEntropy (S.family.metric s)) t ≤ 0 := by
  obtain ⟨f, _, hfEquation⟩ := surfaceEntropy_exists_meanZero_poisson (S.family.metric t)
  rw [(surfaceEntropy_hasDerivAt_first S hS hdim hpositive ht).deriv]
  exact surfaceEntropy_static_first_variation_nonpos (S.family.metric t)
    hdim (hpositive t ht) f hfEquation

theorem ancientSurfaceEntropy_antitoneOn
    (S : SolutionOn (I := I) (M := M) ancientTimeInterval) (hS : IsSolutionOn S)
    (hdim : Module.finrank Real E = 2)
    (hpositive : ∀ s ≤ 0, ∀ x : M, 0 < S.scalar s x) :
    AntitoneOn (fun s => surfaceEntropy (S.family.metric s)) (Set.Iic 0) := by
  have hregularPositive : ∀ s ∈ ancientTimeInterval.regular, ∀ x : M,
      0 < S.scalar s x := fun s hs => hpositive s (le_of_lt hs)
  have hcont := (ancientSurfaceFlow_integrals_continuousOn S hS).2.2
  apply antitoneOn_of_deriv_nonpos (convex_Iic (0 : Real)) hcont
  · intro t ht
    have htneg : t < 0 := by simpa only [interior_Iic, Set.mem_Iio] using ht
    have hd := surfaceEntropy_hasDerivAt_first S hS hdim hregularPositive htneg
    exact hd.differentiableAt.differentiableWithinAt
  · intro t ht
    have htneg : t < 0 := by simpa only [interior_Iic, Set.mem_Iio] using ht
    exact surfaceEntropy_deriv_nonpos S hS hdim hregularPositive htneg

end EntropyFlow

end

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
