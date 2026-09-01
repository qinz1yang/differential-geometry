import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.RicciNorm

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

namespace ScalarSTContOn

omit [SigmaCompactSpace M] [T2Space M] in
theorem timeShift
    {D : RealTimeInterval} {S : SolutionOn (I := I) (M := M) D}
    (hreg : ScalarSTContOn (I := I) (M := M) S) (τ : Real) :
    ScalarSTContOn (I := I) (M := M) (S.timeShift τ) where
  scalar_continuousOn := by
    have hmap : Continuous (fun q : Real × M => (q.1 + τ, q.2)) :=
      (continuous_fst.add continuous_const).prodMk continuous_snd
    have hmaps : Set.MapsTo (fun q : Real × M => (q.1 + τ, q.2))
        ((D.timeShift τ).carrier ×ˢ (Set.univ : Set M))
        (D.carrier ×ˢ (Set.univ : Set M)) := by
      intro q hq
      exact ⟨by simpa [RealTimeInterval.timeShift_carrier] using hq.1, Set.mem_univ q.2⟩
    have hcomp := hreg.scalar_continuousOn.comp hmap.continuousOn hmaps
    simpa [Function.comp_def, SolutionOn.timeShift_scalar] using hcomp

end ScalarSTContOn

namespace CanonicalScalarRegularOn

omit [SigmaCompactSpace M] [T2Space M] in
theorem timeShift
    {D : RealTimeInterval} {S : SolutionOn (I := I) (M := M) D}
    (hreg : CanonicalScalarRegularOn (I := I) (M := M) S) (τ : Real) :
    CanonicalScalarRegularOn (I := I) (M := M) (S.timeShift τ) where
  scalar_continuousOn := (hreg.toScalarSTCont.timeShift τ).scalar_continuousOn
  scalar_time_within := by
    intro K t ht hK x
    let shift : Real → Real := fun s => s + τ
    have ht' : shift t ∈ shift '' K := ⟨t, ht, rfl⟩
    have hK' : shift '' K ⊆ D.carrier := by
      rintro r ⟨s, hs, rfl⟩
      have hs' := hK hs
      simpa [shift, RealTimeInterval.timeShift_carrier] using hs'
    have hOld := hreg.scalar_time_within ht' hK' x
    have hshift : DifferentiableWithinAt Real shift K t := by
      simpa [shift] using ((differentiableAt_id.add_const τ).differentiableWithinAt)
    have hmaps : Set.MapsTo shift K (shift '' K) := fun s hs => ⟨s, hs, rfl⟩
    simpa [shift, Function.comp_def, SolutionOn.timeShift_scalar] using
      hOld.comp t hshift hmaps
  scalar_space := by
    intro t ht x
    exact hreg.scalar_space (t + τ)
      (by simpa [RealTimeInterval.timeShift_carrier] using ht) x
  scalar_grad := by
    intro t ht x
    simpa [SolutionOn.timeShift_family_metric, SolutionOn.timeShift_scalar] using
      hreg.scalar_grad (t + τ)
        (by simpa [RealTimeInterval.timeShift_carrier] using ht) x
  scalar_mul_grad := by
    intro t ht x
    simpa [SolutionOn.timeShift_family_metric, SolutionOn.timeShift_scalar] using
      hreg.scalar_mul_grad (t + τ)
        (by simpa [RealTimeInterval.timeShift_carrier] using ht) x
  scalar_sq_space := by
    intro t ht x
    exact hreg.scalar_sq_space (t + τ)
      (by simpa [RealTimeInterval.timeShift_carrier] using ht) x
  scalar_sq_grad := by
    intro t ht x
    simpa [SolutionOn.timeShift_family_metric, SolutionOn.timeShift_scalar] using
      hreg.scalar_sq_grad (t + τ)
        (by simpa [RealTimeInterval.timeShift_carrier] using ht) x
  scalar_sq_div_space := by
    intro t ht x
    exact hreg.scalar_sq_div_space (t + τ)
      (by simpa [RealTimeInterval.timeShift_carrier] using ht) x
  scalar_sq_div_grad := by
    intro t ht x
    simpa [SolutionOn.timeShift_family_metric, SolutionOn.timeShift_scalar] using
      hreg.scalar_sq_div_grad (t + τ)
        (by simpa [RealTimeInterval.timeShift_carrier] using ht) x
  scalar_grad_sub_const := by
    intro t ht c x
    simpa [SolutionOn.timeShift_family_metric, SolutionOn.timeShift_scalar] using
      hreg.scalar_grad_sub_const (t + τ)
        (by simpa [RealTimeInterval.timeShift_carrier] using ht) c x
  scalar_grad_const_mul_sub_const := by
    intro t ht a c x
    simpa [SolutionOn.timeShift_family_metric, SolutionOn.timeShift_scalar] using
      hreg.scalar_grad_const_mul_sub_const (t + τ)
        (by simpa [RealTimeInterval.timeShift_carrier] using ht) a c x

end CanonicalScalarRegularOn

namespace CanonicalRicciRegularOn

omit [SigmaCompactSpace M] in
theorem timeShift
    {D : RealTimeInterval} {S : SolutionOn (I := I) (M := M) D}
    (hreg : CanonicalRicciRegularOn (I := I) (M := M) S) (τ : Real) :
    CanonicalRicciRegularOn (I := I) (M := M) (S.timeShift τ) where
  ricci_cont := by
    have htime : Continuous (fun s : Real => s + τ) := continuous_id.add continuous_const
    have hmaps : Set.MapsTo (fun s : Real => s + τ) (D.timeShift τ).carrier D.carrier := by
      intro s hs
      simpa [RealTimeInterval.timeShift_carrier] using hs
    have hcomp := tensor0SFamilyContinuousOnSet.comp_time (I := I) (M := M)
      hreg.ricci_cont htime hmaps
    exact tensor0SFamilyContinuousOnSet.congr hcomp (fun _ _ _ => rfl)
  rm04_cont := by
    have htime : Continuous (fun s : Real => s + τ) := continuous_id.add continuous_const
    have hmaps : Set.MapsTo (fun s : Real => s + τ) (D.timeShift τ).carrier D.carrier := by
      intro s hs
      simpa [RealTimeInterval.timeShift_carrier] using hs
    have hcomp := tensor0SFamilyContinuousOnSet.comp_time (I := I) (M := M)
      hreg.rm04_cont htime hmaps
    exact tensor0SFamilyContinuousOnSet.congr hcomp (fun _ _ _ => rfl)
  ricci_norm_space := by
    intro t ht x
    change MDiffAt (ricciNorm (I := I) S (t + τ)) x
    exact hreg.ricci_norm_space (t + τ)
      (by simpa [RealTimeInterval.timeShift_carrier] using ht) x
  ricci_norm_grad := by
    intro t ht x
    change MDiffAt (T% fun y : M =>
      gradientFun (I := I) (S.family.metric (t + τ)) (ricciNorm (I := I) S (t + τ)) y) x
    exact hreg.ricci_norm_grad (t + τ)
      (by simpa [RealTimeInterval.timeShift_carrier] using ht) x

end CanonicalRicciRegularOn

namespace IsSmoothSolutionOn

private theorem hasDerivWithinAt_timeShift
    {D : RealTimeInterval} {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
    {f : Real → F} {f' : F} {t τ : Real}
    (h : HasDerivWithinAt f f' D.carrier (t + τ)) :
    HasDerivWithinAt (fun s => f (s + τ)) f' (D.timeShift τ).carrier t := by
  have hshift : HasDerivWithinAt (fun s : Real => s + τ) 1
      (D.timeShift τ).carrier t :=
    ((hasDerivAt_id t).add_const τ).hasDerivWithinAt
  have hmaps : Set.MapsTo (fun s : Real => s + τ) (D.timeShift τ).carrier D.carrier := by
    intro s hs
    simpa [RealTimeInterval.timeShift_carrier] using hs
  convert h.scomp t hshift hmaps using 1
  · rfl
  · simp

omit [SigmaCompactSpace M] [T2Space M] in
private theorem coordInv_timeShift
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (τ t : Real) (x0 x : M) (i j : Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E) :
    coordInv (I := I) (S.timeShift τ) x0 t x i j =
      coordInv (I := I) S x0 (t + τ) x i j := by
  rfl

omit [SigmaCompactSpace M] [T2Space M] in
private theorem ricciCompInFrame_timeShift
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (τ t : Real) (x0 x : M) (i j : Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E) :
    ricciCompInFrame (I := I) (S.timeShift τ)
        (Tensor.Coordinates.coordinateFrameAt (I := I) x0) t x i j =
      ricciCompInFrame (I := I) S
        (Tensor.Coordinates.coordinateFrameAt (I := I) x0) (t + τ) x i j := by
  rfl

omit [SigmaCompactSpace M] [T2Space M] in
private theorem raisedRicciCompInFrame_timeShift
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (τ t : Real) (x0 x : M) (i j : Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E) :
    raisedRicciCompInFrame
        (I := I) (S.timeShift τ) (coordInv (I := I) (S.timeShift τ) x0)
        (Tensor.Coordinates.coordinateFrameAt (I := I) x0) t x i j =
      raisedRicciCompInFrame
        (I := I) S (coordInv (I := I) S x0)
        (Tensor.Coordinates.coordinateFrameAt (I := I) x0) (t + τ) x i j := by
  rw [raisedRicciCompInFrame_apply, raisedRicciCompInFrame_apply]
  simp_rw [coordInv_timeShift, ricciCompInFrame_timeShift]

omit [SigmaCompactSpace M] [T2Space M] in
private theorem inverseMetricEvolutionRHSInFrame_timeShift
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (τ t : Real) (x0 x : M) (i j : Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E) :
    inverseMetricEvolutionRHSInFrame
        (I := I) (S.timeShift τ) (coordInv (I := I) (S.timeShift τ) x0)
        (Tensor.Coordinates.coordinateFrameAt (I := I) x0) t x i j =
      inverseMetricEvolutionRHSInFrame
        (I := I) S (coordInv (I := I) S x0)
        (Tensor.Coordinates.coordinateFrameAt (I := I) x0) (t + τ) x i j := by
  unfold inverseMetricEvolutionRHSInFrame
  rw [raisedRicciCompInFrame_timeShift]

omit [SigmaCompactSpace M] in
private theorem coordRoughRic_timeShift
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (τ t : Real) (x0 x : M) (i j : Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E) :
    coordRoughRic (I := I) (S.timeShift τ) x0
        (coordNab2Ric (I := I) (S.timeShift τ) x0) t x i j =
      coordRoughRic (I := I) S x0 (coordNab2Ric (I := I) S x0)
        (t + τ) x i j := by
  rfl

omit [SigmaCompactSpace M] in
private theorem rmRicciContractionCompInFrame_timeShift
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (τ t : Real) (x0 x : M) (i j : Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E) :
    rmRicciContractionCompInFrame
        (I := I) (S.timeShift τ) (S.timeShift τ).base.rm04
        (coordInv (I := I) (S.timeShift τ) x0)
        (Tensor.Coordinates.coordinateFrameAt (I := I) x0) t x i j =
      rmRicciContractionCompInFrame
        (I := I) S S.base.rm04 (coordInv (I := I) S x0)
        (Tensor.Coordinates.coordinateFrameAt (I := I) x0) (t + τ) x i j := by
  rw [rmRicciContractionCompInFrame_apply, rmRicciContractionCompInFrame_apply]
  simp_rw [raisedRicciCompInFrame_timeShift]
  rfl

omit [SigmaCompactSpace M] [T2Space M] in
private theorem ricciQuadraticCompInFrame_timeShift
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (τ t : Real) (x0 x : M) (i j : Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E) :
    ricciQuadraticCompInFrame
        (I := I) (S.timeShift τ) (coordInv (I := I) (S.timeShift τ) x0)
        (Tensor.Coordinates.coordinateFrameAt (I := I) x0) t x i j =
      ricciQuadraticCompInFrame
        (I := I) S (coordInv (I := I) S x0)
        (Tensor.Coordinates.coordinateFrameAt (I := I) x0) (t + τ) x i j := by
  rfl

omit [SigmaCompactSpace M] in
private theorem ricciEvolutionRHSInFrame_timeShift
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (τ t : Real) (x0 x : M) (i j : Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E) :
    ricciEvolutionRHSInFrame
        (I := I) (S.timeShift τ) (S.timeShift τ).base.rm04
        (coordInv (I := I) (S.timeShift τ) x0)
        (Tensor.Coordinates.coordinateFrameAt (I := I) x0)
        (coordRoughRic (I := I) (S.timeShift τ) x0
          (coordNab2Ric (I := I) (S.timeShift τ) x0)) t x i j =
      ricciEvolutionRHSInFrame
        (I := I) S S.base.rm04 (coordInv (I := I) S x0)
        (Tensor.Coordinates.coordinateFrameAt (I := I) x0)
        (coordRoughRic (I := I) S x0 (coordNab2Ric (I := I) S x0))
        (t + τ) x i j := by
  rw [ricciEvolutionRHSInFrame_apply, ricciEvolutionRHSInFrame_apply,
    coordRoughRic_timeShift, rmRicciContractionCompInFrame_timeShift,
    ricciQuadraticCompInFrame_timeShift]

omit [SigmaCompactSpace M] in
private theorem ricciNormLap_timeShift
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (τ t : Real) (x : M) :
    ricciNormLap (I := I) (S.timeShift τ) t x = ricciNormLap (I := I) S (t + τ) x := by
  rfl

omit [SigmaCompactSpace M] in
private theorem roughLapRicciInnerInFrame_timeShift
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (τ t : Real) (x : M) :
    roughLapRicciInnerInFrame
        (I := I) (S.timeShift τ)
        (coordRoughRic (I := I) (S.timeShift τ) x
          (coordNab2Ric (I := I) (S.timeShift τ) x))
        (coordInv (I := I) (S.timeShift τ) x)
        (Tensor.Coordinates.coordinateFrameAt (I := I) x) t x =
      roughLapRicciInnerInFrame
        (I := I) S (coordRoughRic (I := I) S x (coordNab2Ric (I := I) S x))
        (coordInv (I := I) S x)
        (Tensor.Coordinates.coordinateFrameAt (I := I) x) (t + τ) x := by
  rw [roughLapRicciInnerInFrame_apply, roughLapRicciInnerInFrame_apply]
  simp_rw [coordRoughRic_timeShift, raisedRicciCompInFrame_timeShift]

omit [SigmaCompactSpace M] in
private theorem ricciGradSq_timeShift
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (τ t : Real) (x : M) :
    ricciGradSq (I := I) (S.timeShift τ) t x = ricciGradSq (I := I) S (t + τ) x := by
  rfl

omit [SigmaCompactSpace M] in
private theorem scalarEvolution_timeShift
    {D : RealTimeInterval} {S : SolutionOn (I := I) (M := M) D}
    (hS : IsSmoothSolutionOn (I := I) (M := M) S) (τ : Real) :
    ∀ (G : MetricConnectionFamily (I := I) (M := M) Real),
      (∀ t : RealTimeInterval.RegularTime (D.timeShift τ),
        G.metric (t : Real) = (S.timeShift τ).family.metric (t : Real)) →
      (∀ t : RealTimeInterval.RegularTime (D.timeShift τ),
        G.connection (t : Real) = (S.timeShift τ).family.connection (t : Real)) →
      ∀ (t : RealTimeInterval.RegularTime (D.timeShift τ)) (x : M),
        HasDerivWithinAt
          (fun s : Real => (S.timeShift τ).scalar s x)
          (laplacianAt (I := I) G (t : Real) ((S.timeShift τ).scalar (t : Real)) x +
            2 * Tensor0SBundle.normSq0S (I := I)
              ((S.timeShift τ).family.metric (t : Real)) x 2
              ((S.timeShift τ).ricci (t : Real) x))
          (D.timeShift τ).carrier
          (t : Real) := by
  intro G hmetric hconnection t x
  let t' : RealTimeInterval.RegularTime D := ⟨(t : Real) + τ, t.2⟩
  have hOld := hS.scalarEvolution (flowG (I := I) S) (fun _ => rfl) (fun _ => rfl) t' x
  have hcomp := hasDerivWithinAt_timeShift hOld
  have hcomp' : HasDerivWithinAt (fun s => (S.timeShift τ).scalar s x)
      (laplacianAt (I := I) (flowG (I := I) S) ((t : Real) + τ)
          (S.scalar ((t : Real) + τ)) x +
        2 * Tensor0SBundle.normSq0S (I := I) (S.family.metric ((t : Real) + τ)) x 2
          (S.ricci ((t : Real) + τ) x))
      (D.timeShift τ).carrier (t : Real) := by
    simpa only [SolutionOn.timeShift_scalar] using hcomp
  apply hcomp'.congr_deriv
  unfold laplacianAt
  rw [hmetric t, hconnection t]
  rfl

omit [SigmaCompactSpace M] in
private theorem invEvol_timeShift
    {D : RealTimeInterval} {S : SolutionOn (I := I) (M := M) D}
    (hS : IsSmoothSolutionOn (I := I) (M := M) S) (τ : Real) :
    ∀ x0 : M,
      InverseMetricEvolutionEquationInFrame
        (I := I) (S.timeShift τ) (coordInv (I := I) (S.timeShift τ) x0)
        (Tensor.Coordinates.coordinateFrameAt (I := I) x0)
        (Tensor.Coordinates.coordinateFrameSet (I := I) x0) := by
  intro x0 t x hx i j
  let t' : RealTimeInterval.RegularTime D := ⟨(t : Real) + τ, t.2⟩
  have hOld := hS.invEvol x0 t' x hx i j
  have hcomp := hasDerivWithinAt_timeShift hOld
  have hfun :
      (fun s : Real => coordInv (I := I) (S.timeShift τ) x0 s x i j) =
        fun s : Real => coordInv (I := I) S x0 (s + τ) x i j := by
    funext s
    exact coordInv_timeShift S τ s x0 x i j
  rw [hfun, inverseMetricEvolutionRHSInFrame_timeShift]
  exact hcomp

omit [SigmaCompactSpace M] in
private theorem ricciEvol_timeShift
    {D : RealTimeInterval} {S : SolutionOn (I := I) (M := M) D}
    (hS : IsSmoothSolutionOn (I := I) (M := M) S) (τ : Real) :
    ∀ x0 : M, ∀ (t : RealTimeInterval.RegularTime (D.timeShift τ))
      (i j : Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E),
      HasDerivWithinAt
        (fun s : Real =>
          ricciCompInFrame (I := I) (S.timeShift τ)
            (Tensor.Coordinates.coordinateFrameAt (I := I) x0) s x0 i j)
        (ricciEvolutionRHSInFrame
          (I := I) (S.timeShift τ) (S.timeShift τ).base.rm04
          (coordInv (I := I) (S.timeShift τ) x0)
          (Tensor.Coordinates.coordinateFrameAt (I := I) x0)
          (coordRoughRic (I := I) (S.timeShift τ) x0
            (coordNab2Ric (I := I) (S.timeShift τ) x0))
          (t : Real) x0 i j)
        (D.timeShift τ).carrier
        (t : Real) := by
  intro x0 t i j
  let t' : RealTimeInterval.RegularTime D := ⟨(t : Real) + τ, t.2⟩
  have hOld := hS.ricciEvol x0 t' i j
  have hcomp := hasDerivWithinAt_timeShift hOld
  have hfun :
      (fun s : Real => ricciCompInFrame (I := I) (S.timeShift τ)
        (Tensor.Coordinates.coordinateFrameAt (I := I) x0) s x0 i j) =
        fun s : Real => ricciCompInFrame (I := I) S
          (Tensor.Coordinates.coordinateFrameAt (I := I) x0) (s + τ) x0 i j := by
    funext s
    exact ricciCompInFrame_timeShift S τ s x0 x0 i j
  rw [hfun, ricciEvolutionRHSInFrame_timeShift]
  exact hcomp

omit [SigmaCompactSpace M] in
theorem timeShift
    {D : RealTimeInterval} {S : SolutionOn (I := I) (M := M) D}
    (hS : IsSmoothSolutionOn (I := I) (M := M) S) (τ : Real) :
    IsSmoothSolutionOn (I := I) (M := M) (S.timeShift τ) where
  isSolution := isSolutionOn_timeShift (I := I) hS.isSolution τ
  scalarSTCont := hS.scalarSTCont.timeShift τ
  scalarRegular := hS.scalarRegular.timeShift τ
  ricciRegular := hS.ricciRegular.timeShift τ
  scalarEvolution := scalarEvolution_timeShift hS τ
  invEvol := invEvol_timeShift hS τ
  ricciEvol := ricciEvol_timeShift hS τ
  invSymm := by
    intro x0 t i j
    exact hS.invSymm x0 (t + τ) i j
  ricciSymm := by
    intro x0 t i j
    exact hS.ricciSymm x0 (t + τ) i j
  ricciLap := by
    intro t x
    rw [ricciNormLap_timeShift, roughLapRicciInnerInFrame_timeShift, ricciGradSq_timeShift]
    exact hS.ricciLap (t + τ) x

end IsSmoothSolutionOn

end DifferentialGeometry.PDE.RicciFlow
