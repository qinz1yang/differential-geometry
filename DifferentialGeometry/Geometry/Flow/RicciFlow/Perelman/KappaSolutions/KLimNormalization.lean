import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.HarnackPointSelection
import DifferentialGeometry.Geometry.Operator.Scalar.Calculus

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Tensor0SBundle
open CanonicalNeighborhood
open scoped _root_.Manifold ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)

local instance klimNormTopology : TopologicalSpace F.M := F.topology
local instance klimNormCharted : ChartedSpace H F.M := F.charted
local instance klimNormSmooth : IsManifold I ∞ F.M := F.smooth
local instance klimNormC1 : IsManifold I 1 F.M :=
  IsManifold.of_le (n := ∞) (by decide)
local instance klimNormT2 : T2Space F.M := F.t2
local instance klimNormSigma : SigmaCompactSpace F.M := F.sigmaCompact

variable {kappa : ℝ}

private theorem normalized_trace_harnack (hK : KLim kappa F)
    (t0 Q : ℝ) (hQ : 0 < Q) (ht0 : t0 ∈ D.carrier)
    (s : ℝ) (hs : s ≤ 0) (x : F.M) (V : TangentSpace I x) :
    let S := curvatureNormalizedSolution F.S t0 Q hQ ht0
    0 ≤ derivWithin (fun u : ℝ => S.scalar u x) ancientTimeInterval.carrier s +
      2 * (S.base.metric s).inner x
        (gradientAt (I := I) (flowG (I := I) S) s (S.scalar s) x) V +
      2 * metricRicci (I := I) (M := F.M) (S.base.metric s) x (vec2 V V) := by
  let S := curvatureNormalizedSolution F.S t0 Q hQ ht0
  have ht0le : t0 ≤ 0 := by simpa only [hK.carrier_eq, Set.mem_Iic] using ht0
  have hmaps : Set.MapsTo (parabolicTime t0 Q) (Set.Iic 0) D.carrier := by
    intro u hu
    rw [hK.carrier_eq]
    exact parabolicTime_nonpos ht0le hQ hu
  have hmem : parabolicTime t0 Q s ∈ D.carrier := hmaps hs
  have htime : HasDerivAt (parabolicTime t0 Q) Q⁻¹ s := by
    change HasDerivAt (fun u : ℝ => t0 + u / Q) Q⁻¹ s
    convert ((hasDerivAt_id s).div_const Q).const_add t0 using 1 <;>
      first | rfl | simp only [one_div]
  have hdSource := (F.isSolution.scalarTime (K := D.carrier) hmem
    (fun _ hu => hu) x).hasDerivWithinAt
  have hderiv : derivWithin (fun u : ℝ => S.scalar u x) (Set.Iic 0) s =
      Q⁻¹ * (derivWithin (fun u : ℝ => F.S.scalar u x) D.carrier
        (parabolicTime t0 Q s) * Q⁻¹) := by
    change derivWithin (fun u : ℝ =>
      (curvatureNormalizedSolution F.S t0 Q hQ ht0).scalar u x) (Set.Iic 0) s = _
    rw [curvatureNormalizedSolution_scalar]
    exact ((hdSource.comp s htime.hasDerivWithinAt hmaps).const_mul Q⁻¹).derivWithin
      (uniqueDiffOn_Iic 0 s hs)
  have hscalar : S.scalar s = fun y => Q⁻¹ * F.S.scalar (parabolicTime t0 Q s) y := by
    change (curvatureNormalizedSolution F.S t0 Q hQ ht0).scalar s = _
    rw [curvatureNormalizedSolution_scalar]
  have hgradient : (S.base.metric s).inner x
      (gradientAt (I := I) (flowG (I := I) S) s (S.scalar s) x) V =
      Q⁻¹ * (F.S.base.metric (parabolicTime t0 Q s)).inner x
        (gradientAt (I := I) (flowG (I := I) F.S) (parabolicTime t0 Q s)
          (F.S.scalar (parabolicTime t0 Q s)) x) V := by
    change (S.base.metric s).inner x
      (gradientFun (I := I) (S.base.metric s) (S.scalar s) x) V =
      Q⁻¹ * (F.S.base.metric (parabolicTime t0 Q s)).inner x
        (gradientFun (I := I) (F.S.base.metric (parabolicTime t0 Q s))
          (F.S.scalar (parabolicTime t0 Q s)) x) V
    rw [inner_gradientFun, inner_gradientFun, hscalar]
    exact mvfderiv_const_mul_apply (I := I) Q⁻¹ V
      ((scalarSmoothOfSolution F.S (parabolicTime t0 Q s)).contMDiffAt.mdifferentiableAt (by simp))
  have hricci : metricRicci (I := I) (M := F.M) (S.base.metric s) =
      metricRicci (I := I) (M := F.M) (F.S.base.metric (parabolicTime t0 Q s)) := by
    change (parabolicSolution F.S t0 Q hQ ht0).base.ricci s =
      F.S.base.ricci (parabolicTime t0 Q s)
    exact congrFun (parabolicSolution_ricci F.S t0 Q hQ ht0) s
  have htrace := hK.traceHarnack (parabolicTime t0 Q s) hmem x (Q • V)
  have hinner : (F.S.base.metric (parabolicTime t0 Q s)).inner x
      (gradientAt (I := I) (flowG (I := I) F.S) (parabolicTime t0 Q s)
        (F.S.scalar (parabolicTime t0 Q s)) x) (Q • V) =
      Q * (F.S.base.metric (parabolicTime t0 Q s)).inner x
        (gradientAt (I := I) (flowG (I := I) F.S) (parabolicTime t0 Q s)
          (F.S.scalar (parabolicTime t0 Q s)) x) V := by
    rw [map_smul]
    simp only [smul_eq_mul]
  have hricScale : metricRicci (I := I) (M := F.M)
      (F.S.base.metric (parabolicTime t0 Q s)) x (vec2 (Q • V) (Q • V)) =
      Q ^ 2 * metricRicci (I := I) (M := F.M)
        (F.S.base.metric (parabolicTime t0 Q s)) x (vec2 V V) := by
    have hvectors : vec2 (I := I) (Q • V) (Q • V) =
        fun j : Fin 2 => Q • vec2 (I := I) V V j := by
      funext j
      fin_cases j <;> rfl
    rw [hvectors]
    have h := (metricRicci (I := I) (M := F.M)
      (F.S.base.metric (parabolicTime t0 Q s)) x).map_smul_univ
        (fun _ : Fin 2 => Q) (vec2 (I := I) V V)
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] using h
  rw [hinner, hricScale] at htrace
  have hscaled := mul_nonneg (sq_nonneg Q⁻¹) htrace
  change 0 ≤ derivWithin (fun u : ℝ => S.scalar u x) (Set.Iic 0) s +
    2 * (S.base.metric s).inner x
      (gradientAt (I := I) (flowG (I := I) S) s (S.scalar s) x) V +
    2 * metricRicci (I := I) (M := F.M) (S.base.metric s) x (vec2 V V)
  have halgebra (a b c : ℝ) :
      Q⁻¹ * (a * Q⁻¹) + 2 * (Q⁻¹ * b) + 2 * c =
        Q⁻¹ ^ 2 * (a + 2 * (Q * b) + 2 * (Q ^ 2 * c)) := by
    calc
      Q⁻¹ * (a * Q⁻¹) + 2 * (Q⁻¹ * b) + 2 * c =
          Q⁻¹ ^ 2 * a + 2 * (Q⁻¹ * b) + 2 * ((Q⁻¹ * Q) ^ 2 * c) := by
        rw [inv_mul_cancel₀ hQ.ne']
        ring
      _ = Q⁻¹ ^ 2 * (a + 2 * (Q * b) + 2 * (Q ^ 2 * c)) := by
        have hmid : Q⁻¹ * b = Q⁻¹ ^ 2 * Q * b := by
          calc
            Q⁻¹ * b = Q⁻¹ * (Q⁻¹ * Q) * b := by rw [inv_mul_cancel₀ hQ.ne', mul_one]
            _ = Q⁻¹ ^ 2 * Q * b := by ring
        rw [hmid]
        ring
  rw [hderiv, hgradient, hricci, halgebra]
  exact hscaled

theorem KLim.curvatureRescaledFlow (hK : KLim kappa F)
    (t0 Q : ℝ) (hQ : 0 < Q) (ht0 : t0 ∈ D.carrier)
    (x0 : F.M) (hscalar : F.S.scalar t0 x0 ≠ 0) :
    KLim kappa
      (curvatureNormalizedFlow F hK.carrier_eq hK.regular_eq t0 Q hQ ht0 x0) := by
  have ht0le : t0 ≤ 0 := by simpa only [hK.carrier_eq, Set.mem_Iic] using ht0
  have hmem (s : ℝ) (hs : s ∈ ancientTimeInterval.carrier) :
      parabolicTime t0 Q s ∈ D.carrier := by
    rw [hK.carrier_eq]
    exact parabolicTime_nonpos ht0le hQ hs
  refine
    { dimension_ge_two := hK.dimension_ge_two
      kappa_pos := hK.kappa_pos
      carrier_eq := rfl
      regular_eq := rfl
      connected := hK.connected
      complete := ?_
      nonnegativeCurvatureOperator := ?_
      noncollapsed := ?_
      notFlat := ?_
      traceHarnack := ?_ }
  · intro s hs
    have hsource : RiemannianMetricComplete (I := I)
        (F.S.base.metric (parabolicTime t0 Q s)) :=
      ⟨hK.complete (parabolicTime t0 Q s) (hmem s hs)⟩
    exact (curvatureNormalizedSolution_complete F.S t0 Q hQ ht0 s hsource).complete
  · intro s hs
    exact curvatureNormalizedFlow_nonnegativeCurvatureOperator
      F hK.carrier_eq hK.regular_eq t0 Q hQ ht0 x0 s
      (hK.nonnegativeCurvatureOperator (parabolicTime t0 Q s) (hmem s hs))
  · exact curvatureNormalizedSolution_noncollapsed
      F.S hK.carrier_eq t0 Q hQ ht0 kappa hK.noncollapsed
  · apply pointedFlowNotFlat_of_scalar_ne_zero
      (curvatureNormalizedFlow F hK.carrier_eq hK.regular_eq t0 Q hQ ht0 x0)
      (t := 0) (by simp) x0
    change (curvatureNormalizedSolution F.S t0 Q hQ ht0).scalar 0 x0 ≠ 0
    rw [curvatureNormalizedSolution_scalar]
    change Q⁻¹ * F.S.scalar (parabolicTime t0 Q 0) x0 ≠ 0
    rw [parabolicTime_zero]
    exact mul_ne_zero (inv_ne_zero hQ.ne') hscalar
  · intro s hs x V
    exact normalized_trace_harnack F hK t0 Q hQ ht0 s hs x V

theorem KLim.curvatureNormalizedFlow (hK : KLim kappa F)
    (t0 Q : ℝ) (hQ : 0 < Q) (ht0 : t0 ∈ D.carrier)
    (x0 : F.M) (hvalue : F.S.scalar t0 x0 = Q) :
    KLim kappa
      (curvatureNormalizedFlow F hK.carrier_eq hK.regular_eq t0 Q hQ ht0 x0) := by
  exact KLim.curvatureRescaledFlow F hK t0 Q hQ ht0 x0
    (by simpa only [hvalue] using hQ.ne')

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
