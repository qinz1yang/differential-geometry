import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.CurvatureBridge
import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.Criterion
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Connection.TailRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extension.Regularity

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open scoped Manifold ContDiff BigOperators Topology

section NormedBase

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

section Quad

variable {Idx : Type*} [Fintype Idx] {u : Set M} {x : M}


omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem tri_expand {ι : Type*} [Fintype ι]
    (A : TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x →L[Real]
      TangentSpace I x)
    (b : Module.Basis ι Real (TangentSpace I x)) (X Y Z : TangentSpace I x) :
    ((A X) Y) Z =
      ∑ i, ∑ j, ∑ k, (b.repr X i * b.repr Y j * b.repr Z k) • ((A (b i)) (b j)) (b k) := by
  classical
  have hX : (∑ i, b.repr X i • b i) = X := b.sum_repr X
  have hY : (∑ j, b.repr Y j • b j) = Y := b.sum_repr Y
  have hZ : (∑ k, b.repr Z k • b k) = Z := b.sum_repr Z
  let : NormedAddCommGroup (TangentSpace I x →L[ℝ] TangentSpace I x) :=
    ContinuousLinearMap.toNormedAddCommGroup
  let : NormedAddCommGroup (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x) :=
    ContinuousLinearMap.toNormedAddCommGroup
  let : AddMonoidHomClass (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x)
      (TangentSpace I x) (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x) :=
    (SemilinearMapClass.distribMulActionSemiHomClass
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x)).toAddMonoidHomClass
  have step1 : ((A X) Y) Z = ∑ i, b.repr X i • (((A (b i)) Y) Z) := by
    conv_lhs => rw [← hX]
    simp only [map_sum, map_smul, sum_apply,
      smul_apply]
  have step2 : ∀ i : ι, ((A (b i)) Y) Z = ∑ j, b.repr Y j • (((A (b i)) (b j)) Z) := by
    intro i
    conv_lhs => rw [← hY]
    simp only [map_sum, map_smul, sum_apply,
      smul_apply]
  have step3 : ∀ i j : ι, ((A (b i)) (b j)) Z =
      ∑ k, b.repr Z k • (((A (b i)) (b j)) (b k)) := by
    intro i j
    conv_lhs => rw [← hZ]
    simp only [map_sum, map_smul]
  rw [step1]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [step2 i, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [step3 i j, Finset.smul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_smul, smul_smul]


def quadOfComp (b : Module.Basis Idx Real (TangentSpace I x))
    (c : Idx -> Idx -> Idx -> Idx -> Real) :
    TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x →L[Real]
      TangentSpace I x :=
  LinearMap.toContinuousLinearMap
    (b.constr Real fun i =>
      LinearMap.toContinuousLinearMap
        (b.constr Real fun j =>
          LinearMap.toContinuousLinearMap (b.constr Real fun k => ∑ l, c i j k l • b l)))

omit [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
@[simp]
theorem quadOfComp_basis (b : Module.Basis Idx Real (TangentSpace I x))
    (c : Idx -> Idx -> Idx -> Idx -> Real) (i j k : Idx) :
    ((quadOfComp (I := I) b c (b i)) (b j)) (b k) = ∑ l, c i j k l • b l := by
  have h1 : quadOfComp (I := I) b c (b i) =
      LinearMap.toContinuousLinearMap
        (b.constr Real fun j =>
          LinearMap.toContinuousLinearMap (b.constr Real fun k => ∑ l, c i j k l • b l)) := by
    change (b.constr Real fun i' =>
      LinearMap.toContinuousLinearMap
        (b.constr Real fun j =>
          LinearMap.toContinuousLinearMap
            (b.constr Real fun k => ∑ l, c i' j k l • b l))) (b i) = _
    rw [Module.Basis.constr_basis]
  rw [h1]
  have h2 : (LinearMap.toContinuousLinearMap
      (b.constr Real fun j' =>
        LinearMap.toContinuousLinearMap
          (b.constr Real fun k => ∑ l, c i j' k l • b l)) : TangentSpace I x →L[Real] _) (b j) =
      LinearMap.toContinuousLinearMap (b.constr Real fun k => ∑ l, c i j k l • b l) := by
    change (b.constr Real fun j' =>
      LinearMap.toContinuousLinearMap
        (b.constr Real fun k => ∑ l, c i j' k l • b l)) (b j) = _
    rw [Module.Basis.constr_basis]
  rw [h2]
  change (b.constr Real fun k' => ∑ l, c i j k' l • b l) (b k) = _
  rw [Module.Basis.constr_basis]


omit [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem quadOfComp_vec (b : Module.Basis Idx Real (TangentSpace I x))
    (V : Idx -> Idx -> Idx -> TangentSpace I x) (i j k : Idx) :
    ((quadOfComp (I := I) b (fun i j k l => b.repr (V i j k) l) (b i)) (b j)) (b k) =
      V i j k := by
  rw [quadOfComp_basis]
  exact b.sum_repr (V i j k)


omit [IsManifold I ∞ M] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem coeff_quadOfComp (frame : Idx -> (y : M) -> TangentSpace I y)
    (hframe : IsLocalFrameOn I E 1 frame u) (hx : x ∈ u)
    (c : Idx -> Idx -> Idx -> Idx -> Real) (i j k l : Idx) :
    hframe.coeff l x
        (((quadOfComp (I := I) (hframe.toBasisAt hx) c (frame i x)) (frame j x))
          (frame k x)) =
      c i j k l := by
  classical
  set b : Module.Basis Idx Real (TangentSpace I x) := hframe.toBasisAt hx with hbdef
  have hbcoe : ∀ m : Idx, b m = frame m x := fun m =>
    IsLocalFrameOn.toBasisAt_coe hframe hx m
  have hcoeff : ∀ (m : Idx) (w : TangentSpace I x),
      hframe.coeff m x w = b.repr w m := by
    intro m w
    simp [IsLocalFrameOn.coeff, hx, hbdef, Module.Basis.coord_apply]
  rw [← hbcoe i, ← hbcoe j, ← hbcoe k, hcoeff l, quadOfComp_basis]
  simp [Finsupp.single_apply]


omit [Fintype Idx] [IsManifold I 1 M] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] in
theorem rmDiffVec_hasDerivAt_of_basis [Finite Idx]
    (g₁ g₂ : Real -> SmoothRiemannianMetric I M)
    (b : Module.Basis Idx Real (TangentSpace I x))
    (Sdot : TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x →L[Real]
      TangentSpace I x)
    {t : Real}
    (hbasis : ∀ i j k : Idx,
      HasDerivAt (fun r : Real => ((rmDiffVec (I := I) (g₁ r) (g₂ r) x (b i)) (b j)) (b k))
        (((Sdot (b i)) (b j)) (b k)) t)
    (X Y Z : TangentSpace I x) :
    HasDerivAt (fun r : Real => ((rmDiffVec (I := I) (g₁ r) (g₂ r) x X) Y) Z)
      (((Sdot X) Y) Z) t := by
  classical
  have : Fintype Idx := Fintype.ofFinite Idx
  have hexp : ∀ r : Real,
      ((rmDiffVec (I := I) (g₁ r) (g₂ r) x X) Y) Z =
        ∑ i, ∑ j, ∑ k, (b.repr X i * b.repr Y j * b.repr Z k) •
          ((rmDiffVec (I := I) (g₁ r) (g₂ r) x (b i)) (b j)) (b k) := fun r =>
    tri_expand (I := I) _ b X Y Z
  have htgt : ((Sdot X) Y) Z =
      ∑ i, ∑ j, ∑ k, (b.repr X i * b.repr Y j * b.repr Z k) • ((Sdot (b i)) (b j)) (b k) :=
    tri_expand (I := I) Sdot b X Y Z
  rw [htgt]
  have hstep : HasDerivAt
      (fun r : Real =>
        ∑ i, ∑ j, ∑ k, (b.repr X i * b.repr Y j * b.repr Z k) •
          ((rmDiffVec (I := I) (g₁ r) (g₂ r) x (b i)) (b j)) (b k))
      (∑ i, ∑ j, ∑ k, (b.repr X i * b.repr Y j * b.repr Z k) •
        ((Sdot (b i)) (b j)) (b k)) t :=
    HasDerivAt.fun_sum fun i _ =>
      HasDerivAt.fun_sum fun j _ =>
        HasDerivAt.fun_sum fun k _ => (hbasis i j k).const_smul _
  simpa only [← hexp] using hstep

end Quad

section Collapse

variable {Idx : Type*} [Fintype Idx]


def uhlRaisedDeriv (g : Real -> SmoothRiemannianMetric I M)
    (basisAt : (y : M) -> Module.Basis Idx Real (TangentSpace I y))
    (Rm04 roughLapRm04 B : FourComp M Idx) (ricciOneUp : MatrixComp M Idx)
    (t : Real) (y : M) (i j k : Idx) : TangentSpace I y :=
  raiseAt (I := I) (g t) y (basisAt y)
    (fun l : Idx =>
      (roughLapRm04 t y i j k l -
          2 * (B t y i j k l - B t y i j l k + B t y i k j l - B t y i l j k) -
          riemann04RicciDriftInFrame ricciOneUp Rm04 t y i j k l) +
        2 * metricRicciAt (I := I) (g t) y
          (fun q : Fin 2 => if q = 0 then
            DifferentialGeometry.Geometry.Curvature.riemannOp (metricCov (I := I) (g t)) y
              (basisAt y i) (basisAt y j) (basisAt y k)
            else basisAt y l))


def uhlRmDiffSpeed (g₁ g₂ : Real -> SmoothRiemannianMetric I M)
    (basisAt : (y : M) -> Module.Basis Idx Real (TangentSpace I y))
    (Rm04₁ roughLapRm04₁ B₁ : FourComp M Idx) (ricciOneUp₁ : MatrixComp M Idx)
    (Rm04₂ roughLapRm04₂ B₂ : FourComp M Idx) (ricciOneUp₂ : MatrixComp M Idx)
    (t : Real) (y : M) :
    TangentSpace I y →L[Real] TangentSpace I y →L[Real] TangentSpace I y →L[Real]
      TangentSpace I y :=
  quadOfComp (I := I) (basisAt y)
    (fun i j k l =>
      (basisAt y).repr
        (uhlRaisedDeriv (I := I) g₁ basisAt Rm04₁ roughLapRm04₁ B₁ ricciOneUp₁ t y i j k -
          uhlRaisedDeriv (I := I) g₂ basisAt Rm04₂ roughLapRm04₂ B₂ ricciOneUp₂ t y i j k) l)


omit [IsManifold I 2 M] [SigmaCompactSpace M] in
theorem rm_of_uhlenbeck
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (g₁ g₂ : Real -> SmoothRiemannianMetric I M)
    (basisAt : (y : M) -> Module.Basis Idx Real (TangentSpace I y))
    (Rm04₁ roughLapRm04₁ B₁ : FourComp M Idx) (ricciOneUp₁ : MatrixComp M Idx)
    (Rm04₂ roughLapRm04₂ B₂ : FourComp M Idx) (ricciOneUp₂ : MatrixComp M Idx)
    {a b : Real} (hreg : Set.Ioo a b ⊆ D.regular)
    (hev₁ : Riemann04BTensorWithRicciDriftEvolutionInFrameOn (D := D)
      Rm04₁ roughLapRm04₁ B₁ ricciOneUp₁)
    (hev₂ : Riemann04BTensorWithRicciDriftEvolutionInFrameOn (D := D)
      Rm04₂ roughLapRm04₂ B₂ ricciOneUp₂)
    (hreal₁ : ∀ (r : Real) (y : M) (i j k l : Idx),
      Rm04₁ r y i j k l =
        metricRm04At (I := I) (g₁ r) y
          (DifferentialGeometry.Geometry.Curvature.vec4 (I := I)
            (basisAt y i) (basisAt y j) (basisAt y k) (basisAt y l)))
    (hreal₂ : ∀ (r : Real) (y : M) (i j k l : Idx),
      Rm04₂ r y i j k l =
        metricRm04At (I := I) (g₂ r) y
          (DifferentialGeometry.Geometry.Curvature.vec4 (I := I)
            (basisAt y i) (basisAt y j) (basisAt y k) (basisAt y l)))
    (hcont₁ : ∀ t ∈ Set.Ioo a b, ∀ (y : M) (i j k : Idx),
      ContinuousWithinAt
        (fun r : Real =>
          DifferentialGeometry.Geometry.Curvature.riemannOp (metricCov (I := I) (g₁ r)) y
            (basisAt y i) (basisAt y j) (basisAt y k))
        D.carrier t)
    (hcont₂ : ∀ t ∈ Set.Ioo a b, ∀ (y : M) (i j k : Idx),
      ContinuousWithinAt
        (fun r : Real =>
          DifferentialGeometry.Geometry.Curvature.riemannOp (metricCov (I := I) (g₂ r)) y
            (basisAt y i) (basisAt y j) (basisAt y k))
        D.carrier t)
    (hPDE₁ : ∀ t ∈ Set.Ioo a b, ∀ (y : M) (U W : TangentSpace I y),
      HasDerivWithinAt (fun r : Real => (g₁ r).inner y U W)
        ((-2 : Real) * metricRicciAt (I := I) (g₁ t) y
          (fun q : Fin 2 => if q = 0 then U else W)) D.carrier t)
    (hPDE₂ : ∀ t ∈ Set.Ioo a b, ∀ (y : M) (U W : TangentSpace I y),
      HasDerivWithinAt (fun r : Real => (g₂ r).inner y U W)
        ((-2 : Real) * metricRicciAt (I := I) (g₂ t) y
          (fun q : Fin 2 => if q = 0 then U else W)) D.carrier t) :
    ∀ t ∈ Set.Ioo a b, ∀ (y : M) (X Y Z : TangentSpace I y),
      HasDerivAt (fun r : Real => ((rmDiffVec (I := I) (g₁ r) (g₂ r) y X) Y) Z)
        (((uhlRmDiffSpeed (I := I) g₁ g₂ basisAt Rm04₁ roughLapRm04₁ B₁ ricciOneUp₁
            Rm04₂ roughLapRm04₂ B₂ ricciOneUp₂ t y X) Y) Z) t := by
  intro t ht y X Y Z
  have hnhds : D.carrier ∈ 𝓝 t := D.regular_mem_nhds (hreg ht)
  refine rmDiffVec_hasDerivAt_of_basis (I := I) g₁ g₂ (basisAt y) _ ?_ X Y Z
  intro i j k
  have hval :
      ((uhlRmDiffSpeed (I := I) g₁ g₂ basisAt Rm04₁ roughLapRm04₁ B₁ ricciOneUp₁
          Rm04₂ roughLapRm04₂ B₂ ricciOneUp₂ t y (basisAt y i)) (basisAt y j)) (basisAt y k) =
        uhlRaisedDeriv (I := I) g₁ basisAt Rm04₁ roughLapRm04₁ B₁ ricciOneUp₁ t y i j k -
          uhlRaisedDeriv (I := I) g₂ basisAt Rm04₂ roughLapRm04₂ B₂ ricciOneUp₂ t y i j k :=
    quadOfComp_vec (I := I) (basisAt y) _ i j k
  rw [hval]
  have h₁ := rmVecComp_deriv (I := I) (D := D) g₁ (basisAt y)
    Rm04₁ roughLapRm04₁ B₁ ricciOneUp₁ (metricRicciAt (I := I) (g₁ t) y) hev₁
    ⟨t, hreg ht⟩ i j k (hcont₁ t ht y i j k) (hPDE₁ t ht y) (fun r l => hreal₁ r y i j k l)
  have h₂ := rmVecComp_deriv (I := I) (D := D) g₂ (basisAt y)
    Rm04₂ roughLapRm04₂ B₂ ricciOneUp₂ (metricRicciAt (I := I) (g₂ t) y) hev₂
    ⟨t, hreg ht⟩ i j k (hcont₂ t ht y i j k) (hPDE₂ t ht y) (fun r l => hreal₂ r y i j k l)
  have hsub := (h₁.sub h₂).hasDerivAt hnhds
  exact hsub

end Collapse

end NormedBase

section Gamma

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
variable [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]

def solOfMetric {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (g : Real -> SmoothRiemannianMetric I M) : SolutionOn (I := I) (M := M) D :=
  ⟨⟨g⟩⟩

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I 1 M] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] in
@[simp]
theorem solOfMetric_metric {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (g : Real -> SmoothRiemannianMetric I M) (s : Real) :
    (solOfMetric (I := I) (D := D) g).base.metric s = g s := rfl

omit [NeZero (Module.finrank ℝ E)] [IsManifold I 2 M] [SigmaCompactSpace M] [T2Space M] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] in
theorem christoffel_symbol_in_frame_eq_solution_metric_christoffel
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {Idx : Type*} {u : Set M}
    (g : Real -> SmoothRiemannianMetric I M)
    (frame : Idx -> (y : M) -> TangentSpace I y)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (s : Real) (x : M) (i j k : Idx) :
    DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
        ((solOfMetric (I := I) (D := D) g).family.connection s) frame hframe x i j k =
      DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
        (metricCov (I := I) (g s)) frame hframe x i j k := rfl

def christoffelDiffSpeed
    (gInv₁ gInv₂ : M -> Real ->
      DifferentialGeometry.Integral.Connection.InverseMetricComponents M
        (Fin (Module.finrank Real E)))
    (nablaRic₁ nablaRic₂ : M -> Real -> M -> Fin (Module.finrank Real E) ->
      Fin (Module.finrank Real E) -> Fin (Module.finrank Real E) -> Real)
    (t : Real) (x : M) :
    TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x :=
  bilinOfComp (I := I) ((chartFrame_isFrame I x).toBasisAt (chartFrame_mem I x))
    (fun i j k =>
      christoffelEvolutionRHSInFrame (M := M) (gInv₁ x) (nablaRic₁ x) t x i j k -
        christoffelEvolutionRHSInFrame (M := M) (gInv₂ x) (nablaRic₂ x) t x i j k)

omit [NeZero (Module.finrank ℝ E)] [IsManifold I 2 M] [SigmaCompactSpace M] [T2Space M] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] in
theorem gamma_of_fields
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (g₁ g₂ : Real -> SmoothRiemannianMetric I M)
    (gInv₁ gInv₂ : M -> Real ->
      DifferentialGeometry.Integral.Connection.InverseMetricComponents M
        (Fin (Module.finrank Real E)))
    (nablaRic₁ nablaRic₂ : M -> Real -> M -> Fin (Module.finrank Real E) ->
      Fin (Module.finrank Real E) -> Fin (Module.finrank Real E) -> Real)
    {a b : Real} (hreg : Set.Ioo a b ⊆ D.regular)
    (hΓ₁ : ∀ x₀ : M, ChristoffelEvolutionEquationInFrameOn (I := I) (D := D)
      (solOfMetric (I := I) (D := D) g₁) (gInv₁ x₀)
      (chartFrame I x₀) (chartFrame_isFrame I x₀) (nablaRic₁ x₀))
    (hΓ₂ : ∀ x₀ : M, ChristoffelEvolutionEquationInFrameOn (I := I) (D := D)
      (solOfMetric (I := I) (D := D) g₂) (gInv₂ x₀)
      (chartFrame I x₀) (chartFrame_isFrame I x₀) (nablaRic₂ x₀)) :
    ∀ t ∈ Set.Ioo a b, ∀ x : M, ∀ i j k : Fin (Module.finrank Real E),
      HasDerivAt
        (fun r : Real =>
          DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
              (metricCov (I := I) (g₁ r)) (chartFrame I x) (chartFrame_isFrame I x) x i j k -
            DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
              (metricCov (I := I) (g₂ r)) (chartFrame I x) (chartFrame_isFrame I x) x i j k)
        ((chartFrame_isFrame I x).coeff k x
          ((christoffelDiffSpeed (I := I) gInv₁ gInv₂ nablaRic₁ nablaRic₂ t x
            (chartFrame I x j x)) (chartFrame I x i x))) t := by
  intro t ht x i j k
  have hnhds : D.carrier ∈ 𝓝 t := D.regular_mem_nhds (hreg ht)
  have hval :
      (chartFrame_isFrame I x).coeff k x
          ((christoffelDiffSpeed (I := I) gInv₁ gInv₂ nablaRic₁ nablaRic₂ t x
            (chartFrame I x j x)) (chartFrame I x i x)) =
        christoffelEvolutionRHSInFrame (M := M) (gInv₁ x) (nablaRic₁ x) t x i j k -
          christoffelEvolutionRHSInFrame (M := M) (gInv₂ x) (nablaRic₂ x) t x i j k :=
    coeff_bilinOfComp (I := I) (chartFrame I x) (chartFrame_isFrame I x) (chartFrame_mem I x) _
      i j k
  rw [hval]
  have hdiff := christoffelEvolutionDiffInFrameOn (I := I) (D := D)
    (solOfMetric (I := I) (D := D) g₁) (solOfMetric (I := I) (D := D) g₂)
    (gInv₁ x) (gInv₂ x) (chartFrame I x) (chartFrame_isFrame I x)
    (nablaRic₁ x) (nablaRic₂ x) (hΓ₁ x) (hΓ₂ x) ⟨t, hreg ht⟩ x (chartFrame_mem I x) i j k
  exact hdiff.hasDerivAt hnhds

variable (I) in
omit [NeZero (Module.finrank ℝ E)] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] in
theorem chartFrame_isFrameTop (x₀ : M) :
    IsLocalFrameOn I E (∞ : WithTop ℕ∞) (chartFrame I x₀)
      (trivializationAt E (TangentSpace I) x₀).baseSet :=
  (trivializationAt E (TangentSpace I) x₀).isLocalFrameOn_localFrame_baseSet I ∞
    (DifferentialGeometry.Integral.Measure.chartModelBasis E)

private def refInterval : DifferentialGeometry.Geometry.Curvature.RealTimeInterval :=
  DifferentialGeometry.Geometry.Curvature.RealTimeInterval.univ 0

def chartFrameInv (g : Real -> SmoothRiemannianMetric I M) (x₀ : M) :
    Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M
      (Fin (Module.finrank Real E)) :=
  localFrameInv (E := E) (I := I) (D := refInterval) (solOfMetric (I := I) g)
    (chartFrame I x₀) (chartFrame_isFrameTop I x₀)

def chartNablaRic (g : Real -> SmoothRiemannianMetric I M) (x₀ : M) :
    Real -> M -> Fin (Module.finrank Real E) -> Fin (Module.finrank Real E) ->
      Fin (Module.finrank Real E) -> Real :=
  fun t x d p q =>
    ricciCovDerivCompInFrame (I := I) (D := refInterval) (solOfMetric (I := I) g)
      (chartFrame I x₀) t x d p q

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I 2 M] [SigmaCompactSpace M] [CompactSpace M] in
theorem chrEvo_of_gram [FiniteDimensional ℝ E] (g : Real -> SmoothRiemannianMetric I M) {a b : Real} (hab : a < b)
    (hjoint : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real) ∞
        (fun p : Real × M =>
          DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (Set.Ico a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hpde : ∀ t ∈ Set.Ico a b, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun s : Real => (g s).inner x v w)
        ((-2 : Real) * DifferentialGeometry.Geometry.Curvature.ricciTensor (I := I) (g t) x v w)
        (Set.Ici a) t)
    (x₀ : M) {t₀ : Real} (ha : a < t₀) (hb : t₀ < b) :
    ChristoffelEvolutionEquationInFrameOn (I := I)
      (D := DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen t₀ b hb)
      (solOfMetric (I := I) g) (chartFrameInv (I := I) g x₀) (chartFrame I x₀)
      (chartFrame_isFrame I x₀) (chartNablaRic (I := I) g x₀) := by
  have hS : IsSolutionOn (I := I)
      (solOfMetric (I := I)
        (D := DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen a b hab) g) :=
    solutionOn_of_joint (I := I) hab g hjoint hpde
  obtain ⟨_, h⟩ := tailChristoffel (I := I) (Idx := Fin (Module.finrank Real E)) hS ha hb
    (chartFrame I x₀) (chartFrame_isFrameTop I x₀)
    (trivializationAt E (TangentSpace I) x₀).open_baseSet
  exact h

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I 2 M] [SigmaCompactSpace M] [CompactSpace M] in
theorem gamma_of_gram [FiniteDimensional ℝ E] (g₁ g₂ : Real -> SmoothRiemannianMetric I M) {a b : Real} (hab : a < b)
    (hjoint₁ : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real) ∞
        (fun p : Real × M =>
          DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (g₁ p.1) x₀ p.2 i j)
        (Set.Ico a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hjoint₂ : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real) ∞
        (fun p : Real × M =>
          DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (g₂ p.1) x₀ p.2 i j)
        (Set.Ico a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hpde₁ : ∀ t ∈ Set.Ico a b, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun s : Real => (g₁ s).inner x v w)
        ((-2 : Real) * DifferentialGeometry.Geometry.Curvature.ricciTensor (I := I) (g₁ t) x v w)
        (Set.Ici a) t)
    (hpde₂ : ∀ t ∈ Set.Ico a b, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun s : Real => (g₂ s).inner x v w)
        ((-2 : Real) * DifferentialGeometry.Geometry.Curvature.ricciTensor (I := I) (g₂ t) x v w)
        (Set.Ici a) t) :
    ∀ t ∈ Set.Ioo a b, ∀ x : M, ∀ i j k : Fin (Module.finrank Real E),
      HasDerivAt
        (fun r : Real =>
          DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
              (metricCov (I := I) (g₁ r)) (chartFrame I x) (chartFrame_isFrame I x) x i j k -
            DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
              (metricCov (I := I) (g₂ r)) (chartFrame I x) (chartFrame_isFrame I x) x i j k)
        ((chartFrame_isFrame I x).coeff k x
          ((christoffelDiffSpeed (I := I) (chartFrameInv (I := I) g₁)
            (chartFrameInv (I := I) g₂) (chartNablaRic (I := I) g₁) (chartNablaRic (I := I) g₂)
            t x (chartFrame I x j x)) (chartFrame I x i x))) t := by
  intro t ht x i j k
  have hat : a < t := ht.1
  have ha : a < (a + t) / 2 := by linarith
  have htt₀ : (a + t) / 2 < t := by linarith
  have hb : (a + t) / 2 < b := lt_trans htt₀ ht.2
  have hval :
      (chartFrame_isFrame I x).coeff k x
          ((christoffelDiffSpeed (I := I) (chartFrameInv (I := I) g₁)
            (chartFrameInv (I := I) g₂) (chartNablaRic (I := I) g₁) (chartNablaRic (I := I) g₂)
            t x (chartFrame I x j x)) (chartFrame I x i x)) =
        christoffelEvolutionRHSInFrame (M := M) (chartFrameInv (I := I) g₁ x)
            (chartNablaRic (I := I) g₁ x) t x i j k -
          christoffelEvolutionRHSInFrame (M := M) (chartFrameInv (I := I) g₂ x)
            (chartNablaRic (I := I) g₂ x) t x i j k :=
    coeff_bilinOfComp (I := I) (chartFrame I x) (chartFrame_isFrame I x) (chartFrame_mem I x) _
      i j k
  rw [hval]
  have hdiff := christoffelEvolutionDiffInFrameOn (I := I)
    (D := DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen
      ((a + t) / 2) b hb)
    (solOfMetric (I := I) g₁) (solOfMetric (I := I) g₂)
    (chartFrameInv (I := I) g₁ x) (chartFrameInv (I := I) g₂ x)
    (chartFrame I x) (chartFrame_isFrame I x)
    (chartNablaRic (I := I) g₁ x) (chartNablaRic (I := I) g₂ x)
    (chrEvo_of_gram (I := I) g₁ hab hjoint₁ hpde₁ x ha hb)
    (chrEvo_of_gram (I := I) g₂ hab hjoint₂ hpde₂ x ha hb)
    ⟨t, ⟨htt₀, ht.2⟩⟩ x (chartFrame_mem I x) i j k
  exact hdiff.hasDerivAt
    (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.regular_mem_nhds _
      (⟨htt₀, ht.2⟩ : t ∈ (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen
        ((a + t) / 2) b hb).regular))

end Gamma

end DifferentialGeometry.PDE.RicciFlow

end
