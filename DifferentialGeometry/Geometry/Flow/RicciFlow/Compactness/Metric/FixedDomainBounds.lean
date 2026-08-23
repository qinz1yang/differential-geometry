import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivativeBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Connection.Christoffel

open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry

attribute [local instance] Fintype.ofFinite
namespace HCGCompactness

open scoped Manifold ContDiff Topology

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}

section FixedDomain

variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]

local instance : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
  simpa using (inferInstance : IsManifold I (∞ : WithTop ℕ∞) M)
omit [T2Space M] [SigmaCompactSpace M] in
theorem gammaL2_le_of_christoffel
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {u : Set M}
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : DifferentialGeometry.PDE.RicciFlow.SolutionOn (I := I) (M := M) D)
    (gInv : Real -> DifferentialGeometry.Geometry.Curvature.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real)
    {x : M} (hx : x ∈ u)
    (baseGamma : Idx -> Idx -> Idx -> Real)
    {a b R : Real}
    (hsub : Set.uIcc a b ⊆ D.carrier)
    (hregular : forall s : Real, s ∈ Set.uIcc a b -> s ∈ D.regular)
    (hinv_id :
      forall s : Real, s ∈ Set.uIcc a b ->
        forall e l : Idx, gInv s x e l = if e = l then 1 else 0)
    (hevol :
      DifferentialGeometry.PDE.RicciFlow.ChristoffelEvolutionEquationInFrameOn
        (I := I) S gInv frame hframe nablaRic)
    (hRic :
      forall s : Real, s ∈ Set.uIcc a b ->
        Real.sqrt
          (DifferentialGeometry.Geometry.Connection.componentL2Sq3
            (fun i j k : Idx => nablaRic s x i j k)) <= R) :
    Real.sqrt
        (DifferentialGeometry.Geometry.Connection.componentL2Sq3
          (fun i j k : Idx =>
            DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
                (S.family.connection b) frame hframe x i j k -
              baseGamma i j k)) <=
      3 * R * |b - a| +
        Real.sqrt
          (DifferentialGeometry.Geometry.Connection.componentL2Sq3
            (fun i j k : Idx =>
              DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
                  (S.family.connection a) frame hframe x i j k -
                baseGamma i j k)) := by
  let Gamma : Real -> Idx -> Idx -> Idx -> Real :=
    fun s i j k =>
      DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
          (S.family.connection s) frame hframe x i j k -
        baseGamma i j k
  let dGamma : Real -> Idx -> Idx -> Idx -> Real :=
    fun s i j k =>
      DifferentialGeometry.PDE.RicciFlow.christoffelEvolutionRHSInFrame
        (M := M) gInv nablaRic s x i j k
  refine gammaL2_le_initial_add_regular
    (Gamma := Gamma) (dGamma := dGamma)
    (nablaRic := fun s i j k => nablaRic s x i j k)
    (D := D) (a := a) (b := b) (R := R)
    hsub hregular ?_ ?_ hRic
  · intro t p
    have h :=
      hevol t x hx p.1 p.2.1 p.2.2
    simpa [Gamma, dGamma] using
      h.sub_const (baseGamma p.1 p.2.1 p.2.2)
  · intro s hs i j k
    exact DifferentialGeometry.PDE.RicciFlow.christoffelRHS_id
      (M := M) gInv nablaRic (hinv_id s hs) i j k

omit [SigmaCompactSpace M] in
theorem covOne_le_christoffel
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {u K : Set M}
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : DifferentialGeometry.PDE.RicciFlow.SolutionOn (I := I) (M := M) D)
    (gRef : SmoothRiemannianMetric I M)
    (gInv : Real -> DifferentialGeometry.Geometry.Curvature.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u) (hxK : x ∈ K)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real)
    {a b R Ca Cb : Real}
    (hsub : Set.uIcc a b ⊆ D.carrier)
    (hregular : ∀ s : Real, s ∈ Set.uIcc a b -> s ∈ D.regular)
    (hinv_id :
      ∀ s : Real, s ∈ Set.uIcc a b ->
        ∀ e l : Idx, gInv s x e l = if e = l then 1 else 0)
    (hevol :
      DifferentialGeometry.PDE.RicciFlow.ChristoffelEvolutionEquationInFrameOn
        (I := I) S gInv frame (localFrameOneOfInf (I := I) frame hframe)
        nablaRic)
    (hRic :
      ∀ s : Real, s ∈ Set.uIcc a b ->
        Real.sqrt
          (DifferentialGeometry.Geometry.Connection.componentL2Sq3
            (fun i j k : Idx => nablaRic s x i j k)) <= R)
    (hEq_b :
      MetricUniformEquivalentOn (I := I) K gRef (S.family.metric b) Cb)
    (hinv_b :
      DifferentialGeometry.Geometry.Curvature.InverseMetricComponentsInFrame
        (I := I) (S.family.metric b) (gInv b) frame)
    (hEq_a :
      MetricUniformEquivalentOn (I := I) K gRef (S.family.metric a) Ca)
    (hinv_a :
      DifferentialGeometry.Geometry.Curvature.InverseMetricComponentsInFrame
        (I := I) (S.family.metric a) (gInv a) frame) :
    metricCovDerivNorm (I := I) 1 (S.family.metric b) gRef x <=
      Real.sqrt (Cb ^ 3) *
        (2 *
          (3 * R * |b - a| +
            (3 / 2 : Real) *
              (Real.sqrt (Ca ^ 3) *
                metricCovDerivNorm (I := I) 1 (S.family.metric a) gRef x))) := by
  let hframe1 := localFrameOneOfInf (I := I) frame hframe
  let baseGamma : Idx -> Idx -> Idx -> Real :=
    fun i j k =>
      DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
        (DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric (I := I) gRef)
        frame hframe1 x i j k
  have hgamma :=
    gammaL2_le_of_christoffel
      (I := I) S gInv frame hframe1 nablaRic hx baseGamma
      hsub hregular hinv_id hevol hRic
  have hsq_b_raw :=
    diffNormSq_eq_l2
      (I := I) (h := S.family.metric b) (gRef := gRef)
      (gInv := gInv b) frame hframe1 hu hx hinv_b
      (hinv_id b Set.right_mem_uIcc)
  have hsq_b :
      Tensor0SBundle.normSqRS
          (I := I) (g := S.family.metric b) (x := x) 1 2
          (Tensor0SBundle.connectionDifferenceTensorAt
            (I := I)
            (DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric
              (I := I) (S.family.metric b))
            (DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric (I := I) gRef) x)
              =
        DifferentialGeometry.Geometry.Connection.componentL2Sq3
          (fun i j k : Idx =>
            DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
                (S.family.connection b) frame hframe1 x i j k -
              baseGamma i j k) := by
    simpa [baseGamma, DifferentialGeometry.PDE.RicciFlow.SolutionOn.family,
      DifferentialGeometry.PDE.RicciFlow.SolutionFamily.connection] using hsq_b_raw
  have hsq_a_raw :=
    diffNormSq_eq_l2
      (I := I) (h := S.family.metric a) (gRef := gRef)
      (gInv := gInv a) frame hframe1 hu hx hinv_a
      (hinv_id a Set.left_mem_uIcc)
  have hsq_a :
      Tensor0SBundle.normSqRS
          (I := I) (g := S.family.metric a) (x := x) 1 2
          (Tensor0SBundle.connectionDifferenceTensorAt
            (I := I)
            (DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric
              (I := I) (S.family.metric a))
            (DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric (I := I) gRef) x)
              =
        DifferentialGeometry.Geometry.Connection.componentL2Sq3
          (fun i j k : Idx =>
            DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
                (S.family.connection a) frame hframe1 x i j k -
              baseGamma i j k) := by
    simpa [baseGamma, DifferentialGeometry.PDE.RicciFlow.SolutionOn.family,
      DifferentialGeometry.PDE.RicciFlow.SolutionFamily.connection] using hsq_a_raw
  have hinvBasis_a :
      Tensor0SBundle.MetricInverseInBasis
        (I := I) (S.family.metric a) x (hframe.toBasisAt hx)
        (Tensor0SBundle.identityInvMetric (Idx := Idx)) :=
    metricInvBasisId
      (I := I) (h := S.family.metric a) (gInv := gInv a)
      frame hframe hx hinv_a (hinv_id a Set.left_mem_uIcc)
  have hinvBasis_b :
      Tensor0SBundle.MetricInverseInBasis
        (I := I) (S.family.metric b) x (hframe.toBasisAt hx)
        (Tensor0SBundle.identityInvMetric (Idx := Idx)) :=
    metricInvBasisId
      (I := I) (h := S.family.metric b) (gInv := gInv b)
      frame hframe hx hinv_b (hinv_id b Set.right_mem_uIcc)
  have hinit_norm :=
    diff_le_covOne_basis_ref_lc
      (I := I) (K := K)
      (h := S.family.metric a) (gRef := gRef)
      hxK (C := Ca) hEq_a (hframe.toBasisAt hx) hinvBasis_a
  have hinit_component :
      Real.sqrt
          (DifferentialGeometry.Geometry.Connection.componentL2Sq3
            (fun i j k : Idx =>
              DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
                  (S.family.connection a) frame hframe1 x i j k -
                baseGamma i j k)) <=
        (3 / 2 : Real) *
          (Real.sqrt (Ca ^ 3) *
            metricCovDerivNorm (I := I) 1 (S.family.metric a) gRef x) := by
    rw [← hsq_a]
    exact hinit_norm
  have hconn :
      Real.sqrt
          (Tensor0SBundle.normSqRS
            (I := I) (g := S.family.metric b) (x := x) 1 2
            (Tensor0SBundle.connectionDifferenceTensorAt
              (I := I)
              (DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric
                (I := I) (S.family.metric b))
              (DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric (I := I) gRef)
                x)) <=
        3 * R * |b - a| +
          (3 / 2 : Real) *
            (Real.sqrt (Ca ^ 3) *
              metricCovDerivNorm (I := I) 1 (S.family.metric a) gRef x) := by
    rw [hsq_b]
    exact le_trans hgamma
      (by
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_left hinit_component (3 * R * |b - a|))
  have hcov :=
    covOne_le_diff_basis_ref_lc
      (I := I) (K := K)
      (h := S.family.metric b) (gRef := gRef)
      hxK (C := Cb) hEq_b (hframe.toBasisAt hx) hinvBasis_b
  exact le_trans hcov
    (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hconn (by norm_num : (0 : Real) <= 2))
      (Real.sqrt_nonneg _))

omit [SigmaCompactSpace M] in
theorem covOne_le_init
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {u K : Set M}
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : DifferentialGeometry.PDE.RicciFlow.SolutionOn (I := I) (M := M) D)
    (gRef : SmoothRiemannianMetric I M)
    (gInv : Real -> DifferentialGeometry.Geometry.Curvature.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u) (hxK : x ∈ K)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real)
    {a b R Ca Cb C1 : Real}
    (hsub : Set.uIcc a b ⊆ D.carrier)
    (hregular : ∀ s : Real, s ∈ Set.uIcc a b -> s ∈ D.regular)
    (hinv_id :
      ∀ s : Real, s ∈ Set.uIcc a b ->
        ∀ e l : Idx, gInv s x e l = if e = l then 1 else 0)
    (hevol :
      DifferentialGeometry.PDE.RicciFlow.ChristoffelEvolutionEquationInFrameOn
        (I := I) S gInv frame (localFrameOneOfInf (I := I) frame hframe)
        nablaRic)
    (hRic :
      ∀ s : Real, s ∈ Set.uIcc a b ->
        Real.sqrt
          (DifferentialGeometry.Geometry.Connection.componentL2Sq3
            (fun i j k : Idx => nablaRic s x i j k)) <= R)
    (hEq_b :
      MetricUniformEquivalentOn (I := I) K gRef (S.family.metric b) Cb)
    (hinv_b :
      DifferentialGeometry.Geometry.Curvature.InverseMetricComponentsInFrame
        (I := I) (S.family.metric b) (gInv b) frame)
    (hEq_a :
      MetricUniformEquivalentOn (I := I) K gRef (S.family.metric a) Ca)
    (hinv_a :
      DifferentialGeometry.Geometry.Curvature.InverseMetricComponentsInFrame
        (I := I) (S.family.metric a) (gInv a) frame)
    (hinit :
      metricCovDerivNorm (I := I) 1 (S.family.metric a) gRef x <= C1) :
    metricCovDerivNorm (I := I) 1 (S.family.metric b) gRef x <=
      Real.sqrt (Cb ^ 3) *
        (2 *
          (3 * R * |b - a| +
            (3 / 2 : Real) * (Real.sqrt (Ca ^ 3) * C1))) := by
  have hmain :=
    covOne_le_christoffel
      (I := I) (K := K) (u := u) S gRef gInv frame hframe hu hx hxK
      nablaRic hsub hregular hinv_id hevol hRic
      hEq_b hinv_b hEq_a hinv_a
  refine le_trans hmain ?_
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num : (0 : Real) <= 2)
  have hinit_scaled :
      (3 / 2 : Real) *
          (Real.sqrt (Ca ^ 3) *
            metricCovDerivNorm (I := I) 1 (S.family.metric a) gRef x) <=
        (3 / 2 : Real) * (Real.sqrt (Ca ^ 3) * C1) :=
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hinit (Real.sqrt_nonneg _))
      (by norm_num : (0 : Real) <= 3 / 2)
  simpa [add_comm, add_left_comm, add_assoc] using
    add_le_add_left hinit_scaled (3 * R * |b - a|)

end FixedDomain

end HCGCompactness
end DifferentialGeometry
