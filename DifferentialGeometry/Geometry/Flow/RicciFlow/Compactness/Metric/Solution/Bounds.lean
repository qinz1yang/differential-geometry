import DifferentialGeometry.Geometry.Metric.Convergence.Metric.Compactness

import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.Solution.WindowPrecompactness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Ricci.Tower
import DifferentialGeometry.Geometry.Operator.Laplacian.Rough
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator

set_option autoImplicit false

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open Bundle DifferentialGeometry.Tensor0SBundle
open scoped BigOperators Manifold ContDiff


noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [VectorBundle Real E (TangentSpace I : M -> Type _)]
variable [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]

def SolutionTimeDerivativeCommutation
    (gRef : SmoothRiemannianMetric I M)
    (D : Nat -> RealTimeInterval)
    (S : (i : Nat) -> SolutionOn (I := I) (M := M) (D i)) : Prop :=
  forall i : Nat, forall N p' : Nat, p' < N ->
    forall V : Fin (p' + 2) -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _), forall x0 : M,
    FixedBaseExtDerivTimeDerivativeOnRegular (I := I) (D i).carrier (D i).regular
      ({x0} : Set M)
      (fun r y => (covDerivOfField (I := I) gRef (solutionMetricField (I := I) (S i) r) p') y
        (fun a : Fin (p' + 2) => V a y))
      (fun r y => (covDerivOfField (I := I) gRef (solutionEvolutionField (I := I) (S i) r) p') y
        (fun a : Fin (p' + 2) => V a y))

structure SolutionCovariantDerivativeBounds
    (β ψ t0 : Real)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M)
    (D : Nat -> RealTimeInterval)
    (S : (i : Nat) -> SolutionOn (I := I) (M := M) (D i)) where
  pack : forall K' : Set M, IsCompact K' -> forall N : Nat, 1 <= N ->
    exists U : Set M, IsOpen U /\ K' ⊆ U /\
      exists B : Real -> Real, exists Bmax : Real, exists KShi : Real,
      exists initialC : Nat -> Real, exists timeRadius : Real,
        MetricUniformEquivalentOnWindow (I := I) U β ψ gRef gSeq B /\
        1 <= Bmax /\ (forall t, t ∈ Set.Icc β ψ -> B t <= Bmax) /\
        0 <= KShi /\
        (forall s : Nat, s <= N -> forall i : Nat,
          forall t : Real, t ∈ Set.Icc β ψ -> forall x : M, x ∈ U ->
            Real.sqrt
              (Tensor0SBundle.normSq0S (I := I) (gSeq i t) x (2 + s)
                (ricCovTower (I := I) (gSeq i t) (gSeq i t) s x)) <= KShi) /\
        t0 ∈ Set.Icc β ψ /\
        (forall i : Nat, forall {t : Real}, t ∈ (D i).regular -> (D i).regular ∈ nhds t) /\
        (forall r : Nat, 0 <= initialC r) /\
        (forall r : Nat, 1 <= r -> r <= N -> forall i : Nat, forall x, x ∈ U ->
          metricCovDerivNorm (I := I) r (gSeq i t0) gRef x <= initialC r) /\
        (forall t : Real, t ∈ Set.Icc β ψ -> |t - t0| <= timeRadius)

structure SolutionMetricLipschitzBounds
    (K : Set M) (β ψ : Real) (p : Nat)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M)
    (D : Nat -> RealTimeInterval)
    (S : (i : Nat) -> SolutionOn (I := I) (M := M) (D i)) where
  pack : forall a : Nat, 1 <= a -> a <= p ->
    exists U : Set M, IsOpen U /\ K ⊆ U /\
      exists B : Real -> Real, exists Bmax : Real, exists Cg : Nat -> Real,
      exists KShi : Real, exists CN : Real,
        MetricUniformEquivalentOnWindow (I := I) U β ψ gRef gSeq B /\
        1 <= Bmax /\ (forall t, t ∈ Set.Icc β ψ -> B t <= Bmax) /\
        (forall r : Nat, 1 <= r -> r < a ->
          MetricCovDerivOrderBoundOnWindow (I := I) U β ψ gSeq gRef r (Cg r)) /\
        0 <= KShi /\
        (forall s : Nat, s <= a -> forall i : Nat,
          forall t : Real, t ∈ Set.Icc β ψ -> forall x : M, x ∈ U ->
            Real.sqrt
              (Tensor0SBundle.normSq0S (I := I) (gSeq i t) x (2 + s)
                (ricCovTower (I := I) (gSeq i t) (gSeq i t) s x)) <= KShi) /\
        0 <= CN /\
        MetricCovDerivOrderBoundOnWindow (I := I) K β ψ gSeq gRef a CN

structure SolutionZeroOrderMetricBounds
    (K : Set M) (beta psiT : Real)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M) where
  U0 : Set M
  hKU0 : K ⊆ U0
  B0 : Real -> Real
  hequiv0 : MetricUniformEquivalentOnWindow (I := I) U0 beta psiT gRef gSeq B0
  Bmax0 : Real
  hBmax01 : 1 <= Bmax0
  hBmax0 : forall t, t ∈ Set.Icc beta psiT -> B0 t <= Bmax0
  KShi0 : Real
  hKShi00 : 0 <= KShi0
  hShi0 : forall i : Nat, forall t : Real, t ∈ Set.Icc beta psiT -> forall x : M,
    x ∈ U0 ->
      Real.sqrt
        (Tensor0SBundle.normSq0S (I := I) (gSeq i t) x 2
          (ricCovTower (I := I) (gSeq i t) (gSeq i t) 0 x)) <= KShi0

def SolutionSubsequenceMetricLowerBound
    (beta psiT : Real)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M) : Prop :=
  forall rho : Nat -> Nat, StrictMono rho -> forall t, t ∈ Set.Icc beta psiT ->
    exists c : Real, 0 < c /\ forall (k : Nat) (x : M) (v : TangentSpace I x),
      c * gRef.inner x v v <= (gSeq (rho k) t).inner x v v

inductive SolutionWindowCompactnessInput : Type _ where
  | mk
      (K : Set M) (hK : IsCompact K)
      (beta psiT t0 : Real) (hbeta : beta <= psiT) (p : Nat)
      (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
      (gRef : SmoothRiemannianMetric I M)
      (D : Nat -> RealTimeInterval)
      (S : (i : Nat) -> SolutionOn (I := I) (M := M) (D i))
      (hS : forall i : Nat, IsSolutionOn (I := I) (S i))
      (hmet : forall (i : Nat) (r : Real), (S i).family.metric r = gSeq i r)
      (hreg : forall i : Nat, Set.Icc beta psiT ⊆ (D i).regular)
      (H0 : SolutionZeroOrderMetricBounds (I := I) K beta psiT gSeq gRef)
      (hswap : SolutionTimeDerivativeCommutation (I := I) gRef D S)
      (Hcov : SolutionCovariantDerivativeBounds (I := I) beta psiT t0 gSeq gRef D S)
      (Hlip : SolutionMetricLipschitzBounds (I := I) K beta psiT p gSeq gRef D S)
      (hlow : SolutionSubsequenceMetricLowerBound (I := I) beta psiT gSeq gRef)

inductive WindowMetricPrecompactnessConclusion : Type _ where
  | intro
      (K : Set M) (beta psiT : Real) (p : Nat)
      (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
      (gRef : SmoothRiemannianMetric I M)
      (out : MetricWindowSubsequence (E := E) (H := H) (I := I) (M := M) K beta psiT p gSeq gRef)

omit [Module.Finite ℝ E] [CompleteSpace E] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    [IsManifold I 2 M] [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
private lemma metricTensorField_eq_metricTensor0S
    [Module.Finite ℝ E]
    (g : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SBundle.metricTensorField (I := I) g x =
      metricTensor0S (I := I) g x := by
  ext v
  rw [Tensor0SBundle.metricTensorField_apply, metricTensor0S_apply]

omit [Module.Finite ℝ E] in
omit [I.Boundaryless] [SigmaCompactSpace M] [IsManifold I 2 M]
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
theorem exists_uniform_zero_order_metric_covariant_derivative_bound
    [Module.Finite ℝ E]
    {K : Set M} {β ψ : Real}
    {gSeq : Nat -> Real -> SmoothRiemannianMetric I M}
    {gRef : SmoothRiemannianMetric I M}
    (B : Real -> Real)
    (hequiv : MetricUniformEquivalentOnWindow (I := I) K β ψ gRef gSeq B)
    (Bmax : Real) (hBmax1 : 1 <= Bmax)
    (hBmax : forall t, t ∈ Set.Icc β ψ -> B t <= Bmax) :
    exists C : Real, forall i : Nat, forall t, t ∈ Set.Icc β ψ -> forall z, z ∈ K ->
      metricCovDerivNorm (I := I) 0 (gSeq i t) gRef z <= C := by
  classical
  let n : Real := Fintype.card (Fin (Module.finrank Real E))
  refine ⟨Real.sqrt (Bmax ^ 2) * Real.sqrt n, fun i t ht z hz => ?_⟩
  have hEqBt := hequiv i t ht
  have hEqMax : MetricUniformEquivalentOn (I := I) K gRef (gSeq i t) Bmax :=
    metricUniformEquivalentOn_of_le (I := I) hEqBt (hBmax t ht)
  have hsymm := metricUniformEquivalentOn_symm (I := I) hEqMax
  have hcomp := sqrt_normSq0S_le_of_metric_equiv
    (I := I) (g := gSeq i t) (h := gRef) z 2 hBmax1
    (fun v => (hsymm.2 z hz v)) (metricTensor0S (I := I) (gSeq i t) z)
  obtain ⟨basis, hON⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis (I := I) (gSeq i t) z
  have hinv : Tensor0SBundle.MetricInverseInBasis (I := I) (gSeq i t) z basis
      (Tensor0SBundle.identityInvMetric
        (Idx := Fin (Module.finrank Real (TangentSpace I z)))) := by
    have h' := DifferentialGeometry.Tensor0SBundle.metricInverseInBasis_of_orthonormal (I := I) (gSeq i t) basis hON
    intro a b
    simpa [Tensor0SBundle.identityInvMetric, Tensor0SBundle.diagonalInvMetric] using h' a b
  have hself :
      Tensor0SBundle.normSq0S (I := I) (gSeq i t) z 2
          (metricTensor0S (I := I) (gSeq i t) z) = n := by
    have hcard := normSq0S_metricTensor0S_eq_card (I := I) (gSeq i t) basis
      (Tensor0SBundle.identityInvMetric
        (Idx := Fin (Module.finrank Real (TangentSpace I z)))) hinv
    have hfr : Module.finrank Real (TangentSpace I z) = Module.finrank Real E := rfl
    rw [Fintype.card_fin, hfr] at hcard
    simpa only [n, Fintype.card_fin] using hcard
  have hcov :
      metricCovDerivNorm (I := I) 0 (gSeq i t) gRef z =
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef z 2
          (metricTensor0S (I := I) (gSeq i t) z)) := by
    simp only [metricCovDerivNorm, metricCovDeriv_eq_covDerivOfField]
    change Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef z 2
        (Tensor0SBundle.metricTensorField (I := I) (gSeq i t) z)) =
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef z 2
        (metricTensor0S (I := I) (gSeq i t) z))
    rw [metricTensorField_eq_metricTensor0S]
  rw [hcov]
  exact le_trans hcomp (by rw [hself])

omit [Module.Finite ℝ E] in
omit [SigmaCompactSpace M] in
theorem exists_uniform_metric_covariant_derivative_bound_for_solution_subsequence
    [Module.Finite ℝ E]
    {β ψ t0 : Real}
    {gSeq : Nat -> Real -> SmoothRiemannianMetric I M}
    {gRef : SmoothRiemannianMetric I M}
    {D : Nat -> RealTimeInterval}
    {S : (i : Nat) -> SolutionOn (I := I) (M := M) (D i)}
    (hS : forall i : Nat, IsSolutionOn (I := I) (S i))
    (hmet : forall (i : Nat) (r : Real), (S i).family.metric r = gSeq i r)
    (hreg : forall i : Nat, Set.Icc β ψ ⊆ (D i).regular)
    (H : SolutionCovariantDerivativeBounds (I := I) β ψ t0 gSeq gRef D S) :
    forall rho : Nat -> Nat, forall t, t ∈ Set.Icc β ψ ->
      forall q : Nat, forall K' : Set M, IsCompact K' -> exists C : Real,
        forall k : Nat, forall z, z ∈ K' ->
          metricCovDerivNorm (I := I) q (gSeq (rho k) t) gRef z <= C := by
  intro rho t ht q K' hK'
  rcases q with _ | q
  · obtain ⟨U, hU, hK'U, B, Bmax, KShi, initialC, timeRadius, hequiv,
      hBmax1, hBmax, _hKShi0, _hShi, _ht0, _hDreg, _hinitC0, _hinit, _htime⟩ :=
      H.pack K' hK' 1 (by norm_num)
    obtain ⟨C, hC⟩ := exists_uniform_zero_order_metric_covariant_derivative_bound (I := I) B
      (metricUniformEquivalentOnWindow_mono (I := I) hK'U hequiv) Bmax hBmax1 hBmax
    exact ⟨C, fun k z hz => hC (rho k) t ht z hz⟩
  · have hq : 1 <= q.succ := Nat.succ_pos q
    obtain ⟨U, hU, hK'U, B, Bmax, KShi, initialC, timeRadius, hequiv,
      hBmax1, hBmax, hKShi0, hShi, ht0, hDreg, hinitC0, hinit, htime⟩ :=
      H.pack K' hK' q.succ hq
    have horders := covOrderBound_of_solution (I := I) hK' hU hK'U q.succ
      D S hS hmet hreg B hequiv Bmax hBmax1 hBmax KShi hKShi0 hShi ht0
      hDreg initialC hinitC0 hinit timeRadius htime
    obtain ⟨C, hC⟩ := horders q.succ hq le_rfl
    exact ⟨C, fun k z hz => hC (rho k) t ht z hz⟩

omit [Module.Finite ℝ E] in
omit [I.Boundaryless] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
omit [SigmaCompactSpace M] in
theorem hgLip0Solution
    [Module.Finite ℝ E]
    {K U : Set M} {β ψ : Real}
    {gSeq : Nat -> Real -> SmoothRiemannianMetric I M}
    {gRef : SmoothRiemannianMetric I M}
    (hKU : K ⊆ U)
    (B : Real -> Real)
    (hequiv : MetricUniformEquivalentOnWindow (I := I) U β ψ gRef gSeq B)
    (Bmax : Real) (hBmax1 : 1 <= Bmax)
    (hBmax : forall t, t ∈ Set.Icc β ψ -> B t <= Bmax)
    (KShi : Real) (hKShi0 : 0 <= KShi)
    (hShi : forall i : Nat, forall t : Real, t ∈ Set.Icc β ψ -> forall x : M, x ∈ U ->
      Real.sqrt
        (Tensor0SBundle.normSq0S (I := I) (gSeq i t) x 2
          (ricCovTower (I := I) (gSeq i t) (gSeq i t) 0 x)) <= KShi)
    (D : Nat -> RealTimeInterval)
    (S : (i : Nat) -> SolutionOn (I := I) (M := M) (D i))
    (hS : forall i : Nat, IsSolutionOn (I := I) (S i))
    (hmet : forall (i : Nat) (r : Real), (S i).family.metric r = gSeq i r)
    (hreg : forall i : Nat, Set.Icc β ψ ⊆ (D i).regular) :
    exists L : Real, 0 <= L /\
      forall i : Nat, forall s, s ∈ Set.Icc β ψ -> forall t, t ∈ Set.Icc β ψ ->
        forall x, x ∈ K ->
          metricDerivNorm (I := I) 0 (gSeq i s) (gSeq i t) gRef x <= L * |s - t| := by
  classical
  have hev := hevComp_of_solutions (I := I) (β := β) (ψ := ψ)
    (gSeq := gSeq) (gRef := gRef) (N := 0) D S hS hmet hreg
    (fun i p hp => False.elim (Nat.not_lt_zero p hp))
  refine ⟨2 * (Real.sqrt (Bmax ^ 2) * KShi), by positivity, fun i s hs t ht x hx => ?_⟩
  exact timeLipschitz_of_hasDerivAt (I := I) gRef 0 (gSeq i)
    (fun r x => (-2 : Real) • nablaRicReal (I := I) gSeq gRef 0 i r x)
    K β ψ (2 * (Real.sqrt (Bmax ^ 2) * KShi))
    (fun x _hx r hr v => hev i x r hr v)
    (fun x hx r hr => by
      rw [Tensor0SBundle.sqrt_normSq0S_smul]
      have habs : |(-2 : Real)| = 2 := by norm_num
      rw [habs]
      have hEqBt := hequiv i r hr
      have hEqMax : MetricUniformEquivalentOn (I := I) U gRef (gSeq i r) Bmax :=
        metricUniformEquivalentOn_of_le (I := I) hEqBt (hBmax r hr)
      have hsymm := metricUniformEquivalentOn_symm (I := I) hEqMax
      have hcomp := sqrt_normSq0S_le_of_metric_equiv
        (I := I) (g := gSeq i r) (h := gRef) x 2 hBmax1
        (fun v => (hsymm.2 x (hKU hx) v))
        (ricCovTower (I := I) (gSeq i r) (gSeq i r) 0 x)
      have hnabla :
          Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef x (0 + 2)
            (nablaRicReal (I := I) gSeq gRef 0 i r x)) <=
          Real.sqrt (Bmax ^ 2) *
            Real.sqrt (Tensor0SBundle.normSq0S (I := I) (gSeq i r) x 2
              (ricCovTower (I := I) (gSeq i r) (gSeq i r) 0 x)) := by
        rw [nablaRicReal_normSq]
        change Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef x 2
            (ricCovTower (I := I) (gSeq i r) (gSeq i r) 0 x)) ≤ _
        exact hcomp
      have hshi := hShi i r hr x (hKU hx)
      calc
        2 * Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef x (0 + 2)
            (nablaRicReal (I := I) gSeq gRef 0 i r x))
            <= 2 * (Real.sqrt (Bmax ^ 2) *
              Real.sqrt (Tensor0SBundle.normSq0S (I := I) (gSeq i r) x 2
                (ricCovTower (I := I) (gSeq i r) (gSeq i r) 0 x))) := by
              exact mul_le_mul_of_nonneg_left hnabla (by norm_num)
        _ <= 2 * (Real.sqrt (Bmax ^ 2) * KShi) := by
              exact mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hshi (Real.sqrt_nonneg _)) (by norm_num))
    s hs t ht x hx

omit [Module.Finite ℝ E] in
omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem hgLipFinSolution
    [Module.Finite ℝ E]
    {K : Set M} {β ψ : Real} {p : Nat}
    {gSeq : Nat -> Real -> SmoothRiemannianMetric I M}
    {gRef : SmoothRiemannianMetric I M}
    {D : Nat -> RealTimeInterval}
    {S : (i : Nat) -> SolutionOn (I := I) (M := M) (D i)}
    (hK : IsCompact K)
    (hS : forall i : Nat, IsSolutionOn (I := I) (S i))
    (hmet : forall (i : Nat) (r : Real), (S i).family.metric r = gSeq i r)
    (hreg : forall i : Nat, Set.Icc β ψ ⊆ (D i).regular)
    (hswap : SolutionTimeDerivativeCommutation (I := I) gRef D S)
    (h0 : exists L0 : Real, 0 <= L0 /\
      forall i : Nat, forall s, s ∈ Set.Icc β ψ -> forall t, t ∈ Set.Icc β ψ ->
        forall x, x ∈ K ->
          metricDerivNorm (I := I) 0 (gSeq i s) (gSeq i t) gRef x <= L0 * |s - t|)
    (H : SolutionMetricLipschitzBounds (I := I) K β ψ p gSeq gRef D S) :
    exists L : Real, 0 <= L /\
      forall i : Nat, forall s, s ∈ Set.Icc β ψ -> forall t, t ∈ Set.Icc β ψ ->
        forall a : Nat, a <= p -> forall x, x ∈ K ->
          metricDerivNorm (I := I) a (gSeq i s) (gSeq i t) gRef x <= L * |s - t| := by
  classical
  obtain ⟨L0, hL00, hLip0⟩ := h0
  have hLipPos : forall a : Nat, 1 <= a -> a <= p ->
      exists L : Real, 0 <= L /\
        forall i : Nat, forall s, s ∈ Set.Icc β ψ -> forall t, t ∈ Set.Icc β ψ ->
          forall x, x ∈ K ->
            metricDerivNorm (I := I) a (gSeq i s) (gSeq i t) gRef x <= L * |s - t| := by
    intro a ha1 hap
    obtain ⟨U, hU, hKU, B, Bmax, Cg, KShi, CN, hequiv,
      hBmax1, hBmax, hBprev, hKShi0, hShi, hCN0, hboundN⟩ :=
      H.pack a ha1 hap
    exact hgLip_orderN_of_solutions (I := I) hK hU hKU ha1 B hequiv
      Bmax hBmax1 hBmax Cg hBprev KShi hKShi0 hShi CN hCN0 hboundN
      D S hS hmet hreg (fun i p' hp => hswap i a p' hp)
  let Lof : Nat -> Real := fun a =>
    if hzero : a = 0 then L0
    else if hle : a <= p then Classical.choose (hLipPos a (Nat.pos_of_ne_zero hzero) hle)
    else 0
  let L : Real := (Finset.range (p + 1)).sup' (by refine ⟨0, ?_⟩; simp) Lof
  have hL0le : L0 <= L := by
    have hmem : 0 ∈ Finset.range (p + 1) := by simp
    have hsup := Finset.le_sup' Lof hmem
    simpa [L, Lof] using hsup
  have hL_nonneg : 0 <= L := le_trans hL00 hL0le
  refine ⟨L, hL_nonneg, fun i s hs t ht a ha x hx => ?_⟩
  have habs_nonneg : 0 <= |s - t| := abs_nonneg _
  by_cases hzero : a = 0
  · subst a
    exact le_trans (hLip0 i s hs t ht x hx)
      (mul_le_mul_of_nonneg_right hL0le habs_nonneg)
  · have ha1 : 1 <= a := Nat.pos_of_ne_zero hzero
    have hspec := Classical.choose_spec (hLipPos a ha1 ha)
    have hmem : a ∈ Finset.range (p + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le ha)
    have hLofle : Lof a <= L := by
      exact Finset.le_sup' Lof hmem
    have hchosen :
        Classical.choose (hLipPos a ha1 ha) <= L := by
      have hLof : Lof a = Classical.choose (hLipPos a ha1 ha) := by
        simp [Lof, hzero, ha]
      simpa [hLof] using hLofle
    exact le_trans (hspec.2 i s hs t ht x hx)
      (mul_le_mul_of_nonneg_right hchosen habs_nonneg)

theorem denseIccSeq {beta psiT : Real} (hbeta : beta <= psiT) :
    exists e : Nat -> Real,
      (forall n : Nat, e n ∈ Set.Icc beta psiT) /\
      forall t, t ∈ Set.Icc beta psiT -> forall delta : Real, 0 < delta ->
        exists n : Nat, |t - e n| < delta := by
  classical
  let X := {t : Real // t ∈ Set.Icc beta psiT}
  have hneX : Nonempty X := ⟨⟨beta, by exact ⟨le_rfl, hbeta⟩⟩⟩
  let eX : Nat -> X := TopologicalSpace.denseSeq X
  have hdenseX : DenseRange eX := TopologicalSpace.denseRange_denseSeq X
  refine ⟨fun n => (eX n).1, ?_, ?_⟩
  · intro n
    exact (eX n).2
  · intro t ht delta hdelta
    let tx : X := ⟨t, ht⟩
    obtain ⟨n, hn⟩ := hdenseX.exists_dist_lt tx hdelta
    refine ⟨n, ?_⟩
    simpa [tx, eX, X, Subtype.dist_eq, Real.dist_eq] using hn

omit [Module.Finite ℝ E] in
theorem metricWindowSubsequence_of_solution
    [Module.Finite ℝ E]
    (hne : Nonempty M)
    (K : Set M) (hK : IsCompact K) (beta psiT t0 : Real) (hbeta : beta <= psiT)
    (p : Nat)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M)
    (D : Nat -> RealTimeInterval)
    (S : (i : Nat) -> SolutionOn (I := I) (M := M) (D i))
    (hS : forall i : Nat, IsSolutionOn (I := I) (S i))
    (hmet : forall (i : Nat) (r : Real), (S i).family.metric r = gSeq i r)
    (hreg : forall i : Nat, Set.Icc beta psiT ⊆ (D i).regular)
    (H0 : SolutionZeroOrderMetricBounds (I := I) K beta psiT gSeq gRef)
    (hswap : SolutionTimeDerivativeCommutation (I := I) gRef D S)
    (Hcov : SolutionCovariantDerivativeBounds (I := I) beta psiT t0 gSeq gRef D S)
    (Hlip : SolutionMetricLipschitzBounds (I := I) K beta psiT p gSeq gRef D S)
    (hlow : SolutionSubsequenceMetricLowerBound (I := I) beta psiT gSeq gRef) :
    MetricWindowSubsequence (E := E) (H := H) (I := I) (M := M) K beta psiT p gSeq gRef := by
  classical
  obtain ⟨e, he, hdense⟩ := denseIccSeq hbeta
  have h0 := hgLip0Solution (I := I) H0.hKU0 H0.B0 H0.hequiv0 H0.Bmax0 H0.hBmax01
    H0.hBmax0 H0.KShi0 H0.hKShi00 H0.hShi0 D S hS hmet hreg
  obtain ⟨L, hL, hgLip⟩ :=
    hgLipFinSolution (I := I) hK hS hmet hreg hswap h0 Hlip
  have hlow' :
      forall rho : Nat -> Nat, StrictMono rho -> forall t, t ∈ Set.Icc beta psiT ->
        exists c : Real, 0 < c /\ forall (k : Nat) (x : M) (v : TangentSpace I x),
          c * gRef.inner x v v <= (gSeq (rho k) t).inner x v v := by
    simpa [SolutionSubsequenceMetricLowerBound] using hlow
  exact metricWindowSubsequence_of_bounds (E := E) (H := H) (I := I) (M := M)
    hne K hK beta psiT p gSeq gRef e he hdense
    L hL hgLip
    (fun rho _hrho =>
      exists_uniform_metric_covariant_derivative_bound_for_solution_subsequence
        (I := I) hS hmet hreg Hcov rho)
    hlow'

noncomputable def windowMetricPrecompactnessConclusion (hne : Nonempty M)
    (W : SolutionWindowCompactnessInput (I := I) (M := M)) :
    WindowMetricPrecompactnessConclusion (E := E) (H := H) (I := I) (M := M) := by
  classical
  cases W with
  | mk K hK beta psiT t0 hbeta p gSeq gRef D S hS hmet hreg H0 hswap Hcov Hlip hlow =>
      exact WindowMetricPrecompactnessConclusion.intro K beta psiT p gSeq gRef
        (metricWindowSubsequence_of_solution (I := I) hne K hK beta psiT t0 hbeta p gSeq gRef D S hS hmet
          hreg H0 hswap Hcov Hlip hlow)

end

end CheegerGromovCompactness
end DifferentialGeometry
