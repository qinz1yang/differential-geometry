import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Ricci.CoordinateRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.ConnectionBounds
import DifferentialGeometry.Analysis.Calculus.CurveDerivative
import DifferentialGeometry.Analysis.Calculus.MultilinearZero
import DifferentialGeometry.Geometry.Connection.ParallelTransport.CovariantDerivativeAlong
import DifferentialGeometry.Geometry.Operator.MetricSharpSmooth
import DifferentialGeometry.Geometry.Connection.TensorNabla.InducedConnection

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Filter DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Analysis.Calculus
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Tensor.Multilinear
open DifferentialGeometry.TensorLieDeriv
open scoped Manifold ContDiff Topology BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

omit [SigmaCompactSpace M] in
theorem connBack_pair
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T tau : Real)
    (ht : T - tau ∈ D.regular) (x : M)
    (X Y W : TangentSpace I x) :
    HasDerivAt
      (fun r : Real ↦
        (S.base.metric (T - tau)).inner x
          (CovariantDerivative.difference
            (metricCov (I := I) (S.base.metric (T - r)))
            (metricCov (I := I) (S.base.metric (T - tau))) x Y X)
          W)
      (let dRic := totalNabla0SFun (𝕜 := Real) (I := I)
          2 (S.base.connection (T - tau)) (S.ricci (T - tau)) x;
        dRic (vec3 X Y W) + dRic (vec3 Y X W) - dRic (vec3 W X Y))
      tau := by
  classical
  let frame := coordinateFrameAt (I := I) x
  let hframe := coordinateFrameAt_isLocalFrame_one (I := I) x
  let u := coordinateFrameSet (I := I) x
  have hx : x ∈ u := coordinateFrameAt_mem (I := I) x
  let b := hframe.toBasisAt hx
  let gInv := coordInv (I := I) S x
  let nr := nablaRicComp (I := I) S frame
  let rhs : CoordinateIdx (𝕜 := Real) E → CoordinateIdx (𝕜 := Real) E →
      CoordinateIdx (𝕜 := Real) E → Real :=
    fun i j k ↦ christoffelEvolutionRHSInFrame (M := M) gInv nr
      (T - tau) x i j k
  let Af : TangentSpace I x →L[Real]
      TangentSpace I x →L[Real] TangentSpace I x :=
    bilinOfComp (I := I) b rhs
  let A : TangentSpace I x →L[Real]
      TangentSpace I x →L[Real] TangentSpace I x := -Af
  let Adot : (y : M) →
      TangentSpace I y →L[Real] TangentSpace I y →L[Real] TangentSpace I y :=
    fun y ↦ dite (y = x) (fun h ↦ h.symm ▸ A) (fun _ ↦ 0)
  let g₁ : Real → SmoothRiemannianMetric I M :=
    fun r ↦ S.base.metric (T - r)
  let g₂ : Real → SmoothRiemannianMetric I M :=
    fun _ ↦ S.base.metric (T - tau)
  have hAat : Adot x = A := by
    simp [Adot]
  have hcoeff : ∀ i j k : CoordinateIdx (𝕜 := Real) E,
      hframe.coeff k x ((Adot x (frame j x)) (frame i x)) = -rhs i j k := by
    intro i j k
    rw [hAat]
    simp only [A, neg_apply, map_neg]
    rw [coeff_bilinOfComp (I := I) frame hframe hx rhs i j k]
  have hGamma : ∀ i j k : CoordinateIdx (𝕜 := Real) E,
      HasDerivAt
        (fun r : Real ↦
          christoffelSymbolInFrame
              (metricCov (I := I) (g₁ r)) frame hframe x i j k -
            christoffelSymbolInFrame
              (metricCov (I := I) (g₂ r)) frame hframe x i j k)
        (hframe.coeff k x ((Adot x (frame j x)) (frame i x))) tau := by
    intro i j k
    have hback := coordGammaBack (I := I) S hS x T tau ht x hx i j k
    have hsub := hback.sub_const
      (christoffelSymbolInFrame
        (metricCov (I := I) (S.base.metric (T - tau))) frame hframe x i j k)
    simpa [g₁, g₂, frame, hframe, rhs, gInv, nr,
      SolutionOn.family_connection, SolutionFamily.connection, metricCov,
      hcoeff i j k] using hsub
  have hvec := connectionDifferenceVec_hasDerivAt (I := I) g₁ g₂ frame hframe
    (coordinateFrameSet_open (I := I) x) hx Adot hGamma X Y
  have hpair := ((S.base.metric (T - tau)).inner x).flip W
    |>.hasFDerivAt.comp_hasDerivAt tau hvec
  let N : Tensor0SSpace 3 I x :=
    totalNabla0SFun (𝕜 := Real) (I := I)
      2 (S.base.connection (T - tau)) (S.ricci (T - tau)) x
  have hinv : MetricInverseInBasisGen (I := I)
      (S.base.metric (T - tau)) x b
      (fun i j ↦ gInv (T - tau) x i j) := by
    have hb : b = coordinateFrameAtBasis (I := I) x hx := by
      ext i
      simp [b]
    rw [hb]
    simpa [frame, gInv, u, coordInv] using
      (gInvBasisAt (I := I) (S.base.metric (T - tau)) x hx)
  have hnr : ∀ d a c : CoordinateIdx (𝕜 := Real) E,
      nr (T - tau) x d a c =
        component0S (I := I) b N
          (fun s : Fin 3 ↦ if s = 0 then d else if s = 1 then a else c) := by
    intro d a c
    simp only [nr, nablaRicComp_apply, N, component0S_apply]
    congr 1
    funext q
    fin_cases q <;> simp [vec3, b, frame]
  have hfwd := lower_connection_difference_eq_hamilton_combination
    (I := I) (S.base.metric (T - tau)) b
    (fun i j ↦ gInv (T - tau) x i j) hinv N
    (fun d a c ↦ nr (T - tau) x d a c) hnr
  have hspeed :
      (S.base.metric (T - tau)).inner x ((A Y) X) W =
        N (vec3 X Y W) + N (vec3 Y X W) - N (vec3 W X Y) := by
    have heval := congrArg
      (fun Q : Tensor0SSpace 3 I x ↦ Q (vec3 X Y W)) hfwd
    have hham : hamiltonConnectionDifferenceCombination (I := I) N (vec3 X Y W) =
        -N (vec3 X Y W) - N (vec3 Y X W) + N (vec3 W X Y) := by
      change Tensor0SSpace.eval (hamiltonConnectionDifferenceCombination (I := I) N)
        (vec3 X Y W) = _
      unfold hamiltonConnectionDifferenceCombination
      simp only [Tensor0SSpace.eval_add, Tensor0SSpace.eval_smul,
        reindexCovariantThreeTensor_apply, smul_eq_mul]
      have hswap :
          (fun q : Fin 3 ↦ vec3 X Y W (Equiv.swap (0 : Fin 3) 1 q)) =
            vec3 Y X W := by
        funext q
        fin_cases q <;> rfl
      rw [hswap]
      ring_nf
      congr 1
      apply congrArg N
      funext q
      fin_cases q <;> rfl
    change lowerBilin (I := I)
        (metricTensorField (I := I) (S.base.metric (T - tau)) x) Af
          (vec3 X Y W) = hamiltonConnectionDifferenceCombination (I := I) N (vec3 X Y W) at heval
    change Tensor0SSpace.eval
        (lowerBilin (I := I)
          (metricTensorField (I := I) (S.base.metric (T - tau)) x) Af)
          (vec3 X Y W) =
        Tensor0SSpace.eval (hamiltonConnectionDifferenceCombination (I := I) N)
          (vec3 X Y W) at heval
    rw [lowerBilin_apply, metricTensorField_eval] at heval
    change Tensor0SSpace.eval (hamiltonConnectionDifferenceCombination (I := I) N)
      (vec3 X Y W) = _ at hham
    rw [hham] at heval
    have heval' :
        (S.base.metric (T - tau)).inner x ((Af Y) X) W =
          -N (vec3 X Y W) - N (vec3 Y X W) + N (vec3 W X Y) := by
      simpa [vec3] using heval
    simp only [A, neg_apply, map_neg]
    linarith [heval']
  have hspeed' :
      ((S.base.metric (T - tau)).inner x).flip W ((Adot x Y) X) =
        N (vec3 X Y W) + N (vec3 Y X W) - N (vec3 W X Y) := by
    rw [hAat]
    exact hspeed
  have hpair' := hpair.congr_deriv hspeed'
  convert hpair' using 1 <;> rfl

omit [SigmaCompactSpace M] in
private theorem connBack_frame_sq
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    (alpha : Real → M) (s : Real)
    (ht : T - s ^ 2 ∈ D.regular)
    (halpha : MDifferentiableAt 𝓘(Real, Real) I alpha s)
    (K : Fin 3 → CoordinateIdx (𝕜 := Real) E) :
    HasDerivAt
      (fun r : Real ↦
        (S.base.metric (T - s ^ 2)).inner (alpha r)
          (CovariantDerivative.difference
            (metricCov (I := I) (S.base.metric (T - r ^ 2)))
            (metricCov (I := I) (S.base.metric (T - s ^ 2)))
            (alpha r)
            (coordinateFrameAt (I := I) (alpha s) (K 1) (alpha r))
            (coordinateFrameAt (I := I) (alpha s) (K 0) (alpha r)))
          (coordinateFrameAt (I := I) (alpha s) (K 2) (alpha r)))
      ((2 * s) *
        (let N := totalNabla0SFun (𝕜 := Real) (I := I)
            2 (S.base.connection (T - s ^ 2))
              (S.ricci (T - s ^ 2)) (alpha s)
         N (vec3
              (coordinateFrameAt (I := I) (alpha s) (K 0) (alpha s))
              (coordinateFrameAt (I := I) (alpha s) (K 1) (alpha s))
              (coordinateFrameAt (I := I) (alpha s) (K 2) (alpha s))) +
         N (vec3
              (coordinateFrameAt (I := I) (alpha s) (K 1) (alpha s))
              (coordinateFrameAt (I := I) (alpha s) (K 0) (alpha s))
              (coordinateFrameAt (I := I) (alpha s) (K 2) (alpha s))) -
         N (vec3
              (coordinateFrameAt (I := I) (alpha s) (K 2) (alpha s))
              (coordinateFrameAt (I := I) (alpha s) (K 0) (alpha s))
              (coordinateFrameAt (I := I) (alpha s) (K 1) (alpha s)))))
      s := by
  classical
  let x₀ := alpha s
  let q := S.base.metric (T - s ^ 2)
  let frame := coordinateFrameAt (I := I) x₀
  let hframe := coordinateFrameAt_isLocalFrame_one (I := I) x₀
  let u := coordinateFrameSet (I := I) x₀
  have hu : IsOpen u := coordinateFrameSet_open (I := I) x₀
  have hx₀ : x₀ ∈ u := coordinateFrameAt_mem (I := I) x₀
  let F : Real → M → Real := fun r x ↦
    q.inner x
      (CovariantDerivative.difference
        (metricCov (I := I) (S.base.metric (T - r ^ 2)))
        (metricCov (I := I) q) x (frame (K 1) x) (frame (K 0) x))
      (frame (K 2) x)
  have htime : ContMDiffAt (𝓘(Real, Real).prod I)
      (𝓘(Real, Real).prod I) ∞
      (fun p : Real × M ↦ (T - p.1 ^ 2, p.2)) (s, x₀) := by
    exact (contMDiffAt_const.sub (contMDiffAt_fst.pow 2)).prodMk
      contMDiffAt_snd
  have hfrozen : ContMDiffAt (𝓘(Real, Real).prod I)
      (𝓘(Real, Real).prod I) ∞
      (fun p : Real × M ↦ (T - s ^ 2, p.2)) (s, x₀) :=
    contMDiffAt_const.prodMk contMDiffAt_snd
  have hsum : ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) 1
      (fun p : Real × M ↦
        ∑ k : CoordinateIdx (𝕜 := Real) E,
          (christoffelSymbolInFrame
                (S.family.connection (T - p.1 ^ 2)) frame hframe p.2
                (K 0) (K 1) k -
            christoffelSymbolInFrame
                (S.family.connection (T - s ^ 2)) frame hframe p.2
                (K 0) (K 1) k) *
            q.inner p.2 (frame k p.2) (frame (K 2) p.2))
      (s, x₀) := by
    refine ContMDiffAt.sum fun k _ ↦ ?_
    have hvar : ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) 1
        (fun p : Real × M ↦ christoffelSymbolInFrame
          (S.family.connection (T - p.1 ^ 2)) frame hframe p.2
          (K 0) (K 1) k) (s, x₀) :=
      ((coordGammaSmoothInf (I := I) S hS x₀
        ⟨T - s ^ 2, ht⟩ x₀ hx₀ (K 0) (K 1) k).of_le
          (by norm_num)).comp (s, x₀) (htime.of_le (by norm_num))
    have hbase : ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) 1
        (fun p : Real × M ↦ christoffelSymbolInFrame
          (S.family.connection (T - s ^ 2)) frame hframe p.2
          (K 0) (K 1) k) (s, x₀) :=
      ((coordGammaSmoothInf (I := I) S hS x₀
        ⟨T - s ^ 2, ht⟩ x₀ hx₀ (K 0) (K 1) k).of_le
          (by norm_num)).comp (s, x₀) (hfrozen.of_le (by norm_num))
    have hmetric : ContMDiffAt I 𝓘(Real, Real) 1
        (fun x : M ↦ q.inner x (frame k x) (frame (K 2) x)) x₀ :=
      DifferentialGeometry.Geometry.Curvature.CovariantDerivative.metric_inner_contMDiffAt
        q (hframe.contMDiffAt hu hx₀ k)
          (hframe.contMDiffAt hu hx₀ (K 2)) (by simp)
    exact (hvar.sub hbase).mul
      (hmetric.comp (s, x₀) contMDiffAt_snd)
  have hFjoint : MDifferentiableAt (𝓘(Real, Real).prod I)
      𝓘(Real, Real) (fun p : Real × M ↦ F p.1 p.2) (s, x₀) := by
    have heq : (fun p : Real × M ↦ F p.1 p.2) =ᶠ[𝓝 (s, x₀)]
        fun p : Real × M ↦
          ∑ k : CoordinateIdx (𝕜 := Real) E,
            (christoffelSymbolInFrame
                  (S.family.connection (T - p.1 ^ 2)) frame hframe p.2
                  (K 0) (K 1) k -
              christoffelSymbolInFrame
                  (S.family.connection (T - s ^ 2)) frame hframe p.2
                  (K 0) (K 1) k) *
              q.inner p.2 (frame k p.2) (frame (K 2) p.2) := by
      have hmem : ∀ᶠ p : Real × M in 𝓝 (s, x₀), p.2 ∈ u :=
        (continuous_snd.tendsto (s, x₀)).eventually (hu.mem_nhds hx₀)
      filter_upwards [hmem] with p hp
      rw [show F p.1 p.2 = q.inner p.2
          (CovariantDerivative.difference
            (metricCov (I := I) (S.base.metric (T - p.1 ^ 2)))
            (metricCov (I := I) q) p.2 (frame (K 1) p.2)
              (frame (K 0) p.2)) (frame (K 2) p.2) from rfl]
      rw [christoffelSymbolDifference_expansion
        (metricCov (I := I) (S.base.metric (T - p.1 ^ 2)))
        (metricCov (I := I) q) frame hframe hp (K 0) (K 1)]
      simp only [map_sum, map_smul, FunLike.coe_sum,
        Finset.sum_apply, smul_apply, smul_eq_mul]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [christoffelSymbolDifferenceInFrame_eq_sub]
      · rfl
      · exact (hframe.contMDiffAt hu hp (K 1)).mdifferentiableAt
          one_ne_zero
    exact (hsum.congr_of_eventuallyEq heq).mdifferentiableAt
      (by simp)
  have hzero : (fun x : M ↦ F s x) =ᶠ[𝓝 x₀] fun _ ↦ 0 := by
    filter_upwards [hu.mem_nhds hx₀] with x hx
    rw [show F s x = q.inner x
        (CovariantDerivative.difference
          (metricCov (I := I) q) (metricCov (I := I) q) x
          (frame (K 1) x) (frame (K 0) x)) (frame (K 2) x) from rfl]
    rw [christoffelSymbolDifference_expansion
      (metricCov (I := I) q) (metricCov (I := I) q)
      frame hframe hx (K 0) (K 1)]
    simp only [map_sum, map_smul, FunLike.coe_sum,
      Finset.sum_apply, smul_apply, smul_eq_mul]
    apply Finset.sum_eq_zero
    intro k _
    rw [christoffelSymbolDifferenceInFrame_eq_sub]
    · simp
    · exact (hframe.contMDiffAt hu hx (K 1)).mdifferentiableAt
        one_ne_zero
  have hfixed : HasDerivAt (fun r : Real ↦ F r x₀)
      ((2 * s) *
        (let N := totalNabla0SFun (𝕜 := Real) (I := I)
            2 (S.base.connection (T - s ^ 2))
              (S.ricci (T - s ^ 2)) x₀
         N (vec3 (frame (K 0) x₀) (frame (K 1) x₀)
              (frame (K 2) x₀)) +
         N (vec3 (frame (K 1) x₀) (frame (K 0) x₀)
              (frame (K 2) x₀)) -
         N (vec3 (frame (K 2) x₀) (frame (K 0) x₀)
              (frame (K 1) x₀)))) s := by
    have houter := connBack_pair (I := I) S hS T (s ^ 2) ht x₀
      (frame (K 0) x₀) (frame (K 1) x₀) (frame (K 2) x₀)
    have hsquare : HasDerivAt (fun r : Real ↦ r ^ 2) (2 * s) s := by
      simpa using hasDerivAt_pow 2 s
    have hcomp := houter.comp_of_eq s hsquare (by rfl)
    simpa [F, q, Function.comp_def, mul_comm] using hcomp
  have hdiag := hasDerivAt_diag0 hFjoint halpha hzero hfixed
  simpa only [F, q, frame, x₀, SolutionOn.family_connection] using hdiag

omit [SigmaCompactSpace M] in
private theorem connBack_low_sq_diff
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    (alpha : Real → M) (s : Real)
    (ht : T - s ^ 2 ∈ D.regular)
    (halpha : MDifferentiableAt 𝓘(Real, Real) I alpha s) :
    DifferentiableAt Real
      (fun r ↦ tensor0SModelAt (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        3 (alpha s) (alpha r)
        (lowerBilin (I := I)
          (metricTensorField (I := I) (S.base.metric (T - s ^ 2)) (alpha r))
          (CovariantDerivative.difference
            (metricCov (I := I) (S.base.metric (T - r ^ 2)))
            (metricCov (I := I) (S.base.metric (T - s ^ 2))) (alpha r)))) s := by
  classical
  let : CompleteSpace E := FiniteDimensional.complete Real E
  let : NormedAddCommGroup
      (ContinuousMultilinearMap Real (fun _ : Fin 3 => E) Real) :=
    ContinuousMultilinearMap.normedAddCommGroup
  let : NormedSpace Real
      (ContinuousMultilinearMap Real (fun _ : Fin 3 => E) Real) :=
    ContinuousMultilinearMap.normedSpace
  let x₀ := alpha s
  let q := S.base.metric (T - s ^ 2)
  let e := trivializationAt E (TangentSpace I : M → Type _) x₀
  let b := Module.finBasis Real E
  let b₃ := continuousMultilinearMapBasis (𝕜 := Real) (F := E) b 3
  let frame := coordinateFrameAt (I := I) x₀
  let C : (r : Real) → Tensor0SSpace 3 I (alpha r) := fun r ↦
    lowerBilin (I := I) (metricTensorField (I := I) q (alpha r))
      (CovariantDerivative.difference
        (metricCov (I := I) (S.base.metric (T - r ^ 2)))
        (metricCov (I := I) q) (alpha r))
  let Cm : Real → Tensor0SModel 3 Real E := fun r ↦
    tensor0SModelAt (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      3 x₀ (alpha r) (C r)
  let c : (Fin 3 → CoordinateIdx (𝕜 := Real) E) → Real → Real :=
    fun K r ↦ C r (fun i ↦ frame (K i) (alpha r))
  let B : Real → Tensor0SModel 3 Real E := fun r ↦
    ∑ K, c K r • b₃ K
  have hc : ∀ K, DifferentiableAt Real (c K) s := by
    intro K
    exact (connBack_frame_sq (I := I) S hS T alpha s ht halpha K).differentiableAt
  have hB : DifferentiableAt Real B s := by
    exact DifferentiableAt.fun_sum fun K _ ↦ (hc K).smul_const (b₃ K)
  have hx₀ : x₀ ∈ e.baseSet := by
    exact mem_baseSet_trivializationAt E (TangentSpace I : M → Type _) x₀
  have hbase : ∀ᶠ r in 𝓝 s, alpha r ∈ e.baseSet :=
    halpha.continuousAt (e.open_baseSet.mem_nhds hx₀)
  have hframe : ∀ (r : Real), alpha r ∈ e.baseSet → ∀ i,
      e.symmL Real (alpha r) (b i) = frame i (alpha r) := by
    intro r hr i
    change e.symmL Real (alpha r) (b i) = e.localFrame b i (alpha r)
    simp [Bundle.Trivialization.localFrame, hr, Bundle.Trivialization.basisAt]
  have hc_repr : ∀ (r : Real), alpha r ∈ e.baseSet → ∀ K,
      c K r = b₃.repr (Cm r) K := by
    intro r hr K
    rw [continuousMultilinearMap_basis_repr]
    have hslots : (fun i ↦ e.symmL Real (alpha r) (b (K i))) =
        fun i ↦ frame (K i) (alpha r) := by
      funext i
      exact hframe r hr (K i)
    have htriv := Tensor0SSpace.trivializationAt_apply
      (𝕜 := Real) (I := I) (x₀ := x₀) (x := alpha r) 3 (C r)
        (fun i ↦ b (K i))
    rw [hslots] at htriv
    simpa only [c, Cm, tensor0SModelAt, hslots] using htriv.symm
  have hBC : B =ᶠ[𝓝 s] Cm := by
    filter_upwards [hbase] with r hr
    calc
      B r = ∑ K, b₃.repr (Cm r) K • b₃ K := by
        apply Finset.sum_congr rfl
        intro K _
        rw [← hc_repr r hr K]
      _ = Cm r := b₃.sum_repr (Cm r)
  simpa only [x₀, q, C, Cm] using hB.congr_of_eventuallyEq hBC.symm

omit [SigmaCompactSpace M] in
theorem connBack_along_sq
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    (alpha : Real → M)
    (A Y W : ∀ r, TangentSpace I (alpha r)) (s : Real)
    (ht : T - s ^ 2 ∈ D.regular)
    (halpha : MDifferentiableAt 𝓘(Real, Real) I alpha s)
    (hA : DifferentiableAt Real (chartRepAt (I := I) alpha A s) s)
    (hY : DifferentiableAt Real (chartRepAt (I := I) alpha Y s) s)
    (hW : DifferentiableAt Real (chartRepAt (I := I) alpha W s) s) :
    HasDerivAt
      (fun r : Real ↦
        (S.base.metric (T - s ^ 2)).inner (alpha r)
          (CovariantDerivative.difference
            (metricCov (I := I) (S.base.metric (T - r ^ 2)))
            (metricCov (I := I) (S.base.metric (T - s ^ 2)))
            (alpha r) (Y r) (A r))
          (W r))
      ((2 * s) *
        (let N := totalNabla0SFun (𝕜 := Real) (I := I)
            2 (S.base.connection (T - s ^ 2))
              (S.ricci (T - s ^ 2)) (alpha s)
         N (vec3 (A s) (Y s) (W s)) +
         N (vec3 (Y s) (A s) (W s)) -
         N (vec3 (W s) (A s) (Y s))))
      s := by
  classical
  let : CompleteSpace E := FiniteDimensional.complete Real E
  let : NormedAddCommGroup
      (ContinuousMultilinearMap Real (fun _ : Fin 3 => E) Real) :=
    ContinuousMultilinearMap.normedAddCommGroup
  let : NormedSpace Real
      (ContinuousMultilinearMap Real (fun _ : Fin 3 => E) Real) :=
    ContinuousMultilinearMap.normedSpace
  let x₀ := alpha s
  let q := S.base.metric (T - s ^ 2)
  let e := trivializationAt E (TangentSpace I : M → Type _) x₀
  let b := Module.finBasis Real E
  let b₃ := continuousMultilinearMapBasis (𝕜 := Real) (F := E) b 3
  let frame := coordinateFrameAt (I := I) x₀
  let C : (r : Real) → Tensor0SSpace 3 I (alpha r) := fun r ↦
    lowerBilin (I := I) (metricTensorField (I := I) q (alpha r))
      (CovariantDerivative.difference
        (metricCov (I := I) (S.base.metric (T - r ^ 2)))
        (metricCov (I := I) q) (alpha r))
  let Cm : Real → Tensor0SModel 3 Real E := fun r ↦
    tensor0SModelAt (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      3 x₀ (alpha r) (C r)
  let c : (Fin 3 → CoordinateIdx (𝕜 := Real) E) → Real → Real :=
    fun K r ↦ C r (fun i ↦ frame (K i) (alpha r))
  let B : Real → Tensor0SModel 3 Real E := fun r ↦
    ∑ K, c K r • b₃ K
  let N : Tensor0SSpace 3 I x₀ :=
    totalNabla0SFun (𝕜 := Real) (I := I)
      2 (S.base.connection (T - s ^ 2)) (S.ricci (T - s ^ 2)) x₀
  let R : Tensor0SSpace 3 I x₀ := -hamiltonConnectionDifferenceCombination (I := I) N
  let B' : Tensor0SModel 3 Real E :=
    ∑ K, ((2 * s) * R (fun i ↦ frame (K i) x₀)) • b₃ K
  have hR : ∀ v : Fin 3 → TangentSpace I x₀,
      R v = N (vec3 (v 0) (v 1) (v 2)) +
        N (vec3 (v 1) (v 0) (v 2)) -
        N (vec3 (v 2) (v 0) (v 1)) := by
    intro v
    have hv : v = vec3 (v 0) (v 1) (v 2) := by
      funext a
      fin_cases a <;> rfl
    rw [hv]
    have hham : hamiltonConnectionDifferenceCombination (I := I) N
        (vec3 (v 0) (v 1) (v 2)) =
          -N (vec3 (v 0) (v 1) (v 2)) -
            N (vec3 (v 1) (v 0) (v 2)) +
            N (vec3 (v 2) (v 0) (v 1)) := by
      change Tensor0SSpace.eval (hamiltonConnectionDifferenceCombination (I := I) N)
        (vec3 (v 0) (v 1) (v 2)) = _
      unfold hamiltonConnectionDifferenceCombination
      simp only [Tensor0SSpace.eval_add, Tensor0SSpace.eval_smul,
        reindexCovariantThreeTensor_apply, smul_eq_mul]
      have hswap :
          (fun a : Fin 3 ↦
            vec3 (v 0) (v 1) (v 2) (Equiv.swap (0 : Fin 3) 1 a)) =
            vec3 (v 1) (v 0) (v 2) := by
        funext a
        fin_cases a <;> rfl
      rw [hswap]
      ring_nf
      congr 1
      apply congrArg N
      funext a
      fin_cases a <;> rfl
    simp only [R, Tensor0SSpace.neg_apply, hham]
    simp [vec3]
    ring
  have hc : ∀ K, HasDerivAt (c K)
      ((2 * s) * R (fun i ↦ frame (K i) x₀)) s := by
    intro K
    have h := connBack_frame_sq (I := I) S hS T alpha s ht halpha K
    apply h.congr_deriv
    rw [hR]
  have hB : HasDerivAt B B' s := by
    exact HasDerivAt.fun_sum fun K _ ↦ (hc K).smul_const (b₃ K)
  have hc0 : ∀ K, c K s = 0 := by
    intro K
    simp only [c, C, q]
    have hself := connectionDifferenceLowAt_self (I := I) q (alpha s)
    rw [connectionDifferenceLow_eq_lower] at hself
    rw [hself]
    rfl
  have hB0 : B s = 0 := by
    simp only [B, hc0, zero_smul, Finset.sum_const_zero]
  have hx₀ : x₀ ∈ e.baseSet := by
    exact mem_baseSet_trivializationAt E (TangentSpace I : M → Type _) x₀
  have hbase : ∀ᶠ r in 𝓝 s, alpha r ∈ e.baseSet :=
    halpha.continuousAt (e.open_baseSet.mem_nhds hx₀)
  have hframe : ∀ (r : Real), alpha r ∈ e.baseSet → ∀ i,
      e.symmL Real (alpha r) (b i) = frame i (alpha r) := by
    intro r hr i
    change e.symmL Real (alpha r) (b i) = e.localFrame b i (alpha r)
    simp [Bundle.Trivialization.localFrame, hr, Bundle.Trivialization.basisAt]
  have hc_repr : ∀ (r : Real), alpha r ∈ e.baseSet → ∀ K,
      c K r = b₃.repr (Cm r) K := by
    intro r hr K
    rw [continuousMultilinearMap_basis_repr]
    have hslots : (fun i ↦ e.symmL Real (alpha r) (b (K i))) =
        fun i ↦ frame (K i) (alpha r) := by
      funext i
      exact hframe r hr (K i)
    have htriv := Tensor0SSpace.trivializationAt_apply
      (𝕜 := Real) (I := I) (x₀ := x₀) (x := alpha r) 3 (C r)
        (fun i ↦ b (K i))
    rw [hslots] at htriv
    simpa only [c, Cm, tensor0SModelAt, hslots] using htriv.symm
  have hBC : ∀ᶠ r in 𝓝 s, B r = Cm r := by
    filter_upwards [hbase] with r hr
    calc
      B r = ∑ K, b₃.repr (Cm r) K • b₃ K := by
        apply Finset.sum_congr rfl
        intro K _
        rw [← hc_repr r hr K]
      _ = Cm r := b₃.sum_repr (Cm r)
  let V : Fin 3 → Real → E := fun i r ↦
    if i = 0 then chartRepAt (I := I) alpha A s r
    else if i = 1 then chartRepAt (I := I) alpha Y s r
    else chartRepAt (I := I) alpha W s r
  have hV : ∀ i, HasDerivAt (V i) (deriv (V i) s) s := by
    intro i
    fin_cases i
    · change HasDerivAt (chartRepAt (I := I) alpha A s)
        (deriv (chartRepAt (I := I) alpha A s) s) s
      exact hA.hasDerivAt
    · change HasDerivAt (chartRepAt (I := I) alpha Y s)
        (deriv (chartRepAt (I := I) alpha Y s) s) s
      exact hY.hasDerivAt
    · change HasDerivAt (chartRepAt (I := I) alpha W s)
        (deriv (chartRepAt (I := I) alpha W s) s) s
      exact hW.hasDerivAt
  have hmove := cml_deriv_zero hB hV hB0
  have heval : (fun r ↦ B r (fun i ↦ V i r)) =ᶠ[𝓝 s]
      fun r ↦ q.inner (alpha r)
        (CovariantDerivative.difference
          (metricCov (I := I) (S.base.metric (T - r ^ 2)))
          (metricCov (I := I) q) (alpha r) (Y r) (A r))
        (W r) := by
    filter_upwards [hbase, hBC] with r hr hBr
    rw [hBr]
    have hslot : ∀ i,
        e.symmL Real (alpha r) (V i r) =
          if i = 0 then A r else if i = 1 then Y r else W r := by
      intro i
      fin_cases i
      · change e.symmL Real (alpha r)
          (chartRepAt (I := I) alpha A s r) = A r
        simpa only [chartRepAt_apply, e, x₀] using
          e.symmL_continuousLinearMapAt (R := Real) hr (A r)
      · change e.symmL Real (alpha r)
          (chartRepAt (I := I) alpha Y s r) = Y r
        simpa only [chartRepAt_apply, e, x₀] using
          e.symmL_continuousLinearMapAt (R := Real) hr (Y r)
      · change e.symmL Real (alpha r)
          (chartRepAt (I := I) alpha W s r) = W r
        simpa only [chartRepAt_apply, e, x₀] using
          e.symmL_continuousLinearMapAt (R := Real) hr (W r)
    have htriv := Tensor0SSpace.trivializationAt_apply
      (𝕜 := Real) (I := I) (x₀ := x₀) (x := alpha r) 3 (C r)
        (fun i ↦ V i r)
    calc
      Cm r (fun i ↦ V i r) =
          C r (fun i ↦ e.symmL Real (alpha r) (V i r)) := by
        simpa only [Cm, tensor0SModelAt] using htriv
      _ = q.inner (alpha r)
          (CovariantDerivative.difference
            (metricCov (I := I) (S.base.metric (T - r ^ 2)))
            (metricCov (I := I) q) (alpha r) (Y r) (A r))
          (W r) := by
        have hslots : (fun i ↦ e.symmL Real (alpha r) (V i r)) =
            vec3 (A r) (Y r) (W r) := by
          funext i
          fin_cases i <;> simp only [vec3, hslot, Fin.zero_eta, Fin.mk_one,
            ↓reduceIte]
        rw [hslots]
        rfl
  have hB' : B' (fun i ↦ V i s) =
      (2 * s) *
        (N (vec3 (A s) (Y s) (W s)) +
          N (vec3 (Y s) (A s) (W s)) -
          N (vec3 (W s) (A s) (Y s))) := by
    let Rc := tensor0SSpaceFiberContinuousLinearEquiv (I := I) 3 x₀ R
    have hsum := b₃.sum_repr
      ((Rc.compContinuousLinearMap fun _ ↦ e.symmL Real x₀) :
        Tensor0SModel 3 Real E)
    have hrepr : ∀ K,
        b₃.repr
            ((Rc.compContinuousLinearMap fun _ ↦ e.symmL Real x₀) :
              Tensor0SModel 3 Real E) K =
          R (fun i ↦ frame (K i) x₀) := by
      intro K
      rw [continuousMultilinearMap_basis_repr]
      simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, Rc,
        tensor0SSpaceFiberContinuousLinearEquiv_apply_apply]
      congr 1
      funext i
      exact hframe s (by simpa only [x₀] using hx₀) (K i)
    have hB'eq : B' =
        (2 * s) •
          ((Rc.compContinuousLinearMap fun _ ↦ e.symmL Real x₀) :
            Tensor0SModel 3 Real E) := by
      change (∑ K, ((2 * s) * R (fun i ↦ frame (K i) x₀)) • b₃ K) = _
      apply ContinuousMultilinearMap.ext
      intro z
      simp only [sum_apply,
        smul_apply, smul_eq_mul]
      have heval := congrArg (fun L : Tensor0SModel 3 Real E ↦ L z) hsum
      simp only [sum_apply,
        smul_apply, smul_eq_mul] at heval
      rw [← heval, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro K _
      rw [hrepr]
      ring
    rw [hB'eq]
    simp only [smul_apply, smul_eq_mul,
      ContinuousMultilinearMap.compContinuousLinearMap_apply, Rc,
      tensor0SSpaceFiberContinuousLinearEquiv_apply_apply]
    have hslot0 : ∀ i,
        e.symmL Real x₀ (V i s) =
          if i = 0 then A s else if i = 1 then Y s else W s := by
      intro i
      fin_cases i
      · change e.symmL Real x₀ (chartRepAt (I := I) alpha A s s) = A s
        simpa only [e, x₀] using symmL_chartRepAt_self (I := I) alpha A s
      · change e.symmL Real x₀ (chartRepAt (I := I) alpha Y s s) = Y s
        simpa only [e, x₀] using symmL_chartRepAt_self (I := I) alpha Y s
      · change e.symmL Real x₀ (chartRepAt (I := I) alpha W s s) = W s
        simpa only [e, x₀] using symmL_chartRepAt_self (I := I) alpha W s
    have hslots : (fun i ↦ e.symmL Real x₀ (V i s)) =
        vec3 (A s) (Y s) (W s) := by
      funext i
      fin_cases i <;> simp only [vec3, hslot0, Fin.zero_eta, Fin.mk_one,
        ↓reduceIte]
    rw [hslots]
    congr 1
    exact hR (vec3 (A s) (Y s) (W s))
  apply (hmove.congr_of_eventuallyEq heval.symm).congr_deriv
  simpa only [q, N, x₀] using hB'

omit [SigmaCompactSpace M] in
theorem connBack_vec_sq
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    (alpha : Real → M)
    (A Y : ∀ r, TangentSpace I (alpha r)) (s : Real)
    (ht : T - s ^ 2 ∈ D.regular)
    (halpha : MDifferentiableAt 𝓘(Real, Real) I alpha s)
    (hA : DifferentiableAt Real (chartRepAt (I := I) alpha A s) s)
    (hY : DifferentiableAt Real (chartRepAt (I := I) alpha Y s) s) :
    DifferentiableAt Real
      (chartRepAt (I := I) alpha
        (fun r ↦ CovariantDerivative.difference
          (metricCov (I := I) (S.base.metric (T - r ^ 2)))
          (metricCov (I := I) (S.base.metric (T - s ^ 2)))
          (alpha r) (Y r) (A r)) s) s := by
  classical
  let : CompleteSpace E := FiniteDimensional.complete Real E
  let : NormedAddCommGroup
      (ContinuousMultilinearMap Real (fun _ : Fin 3 => E) Real) :=
    ContinuousMultilinearMap.normedAddCommGroup
  let : NormedSpace Real
      (ContinuousMultilinearMap Real (fun _ : Fin 3 => E) Real) :=
    ContinuousMultilinearMap.normedSpace
  let x₀ := alpha s
  let q := S.base.metric (T - s ^ 2)
  let C : ∀ r, TangentSpace I (alpha r) := fun r ↦
    CovariantDerivative.difference
      (metricCov (I := I) (S.base.metric (T - r ^ 2)))
      (metricCov (I := I) q) (alpha r) (Y r) (A r)
  let Cm : Real → Tensor0SModel 3 Real E := fun r ↦
    tensor0SModelAt (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      3 x₀ (alpha r)
      (lowerBilin (I := I) (metricTensorField (I := I) q (alpha r))
        (CovariantDerivative.difference
          (metricCov (I := I) (S.base.metric (T - r ^ 2)))
          (metricCov (I := I) q) (alpha r)))
  have hCm : DifferentiableAt Real Cm s := by
    simpa only [Cm, x₀, q] using connBack_low_sq_diff (I := I) S hS T alpha s ht halpha
  have hCm0 : Cm s = 0 := by
    simp only [Cm, x₀, q]
    have hself := connectionDifferenceLowAt_self (I := I) q (alpha s)
    rw [connectionDifferenceLow_eq_lower] at hself
    rw [hself]
    rfl
  let X : Real → E := chartRepAt (I := I) alpha A s
  let Z : Real → E := chartRepAt (I := I) alpha Y s
  let b := chartModelBasis E
  let v3 : E → E → E → Fin 3 → E := fun u v w i ↦
    if i = 0 then u else if i = 1 then v else w
  let f : Fin (Module.finrank Real E) → Real → Real := fun j r ↦
    Cm r (v3 (X r) (Z r) (b j))
  have hf : ∀ j, DifferentiableAt Real (f j) s := by
    intro j
    let V : Fin 3 → Real → E := fun i r ↦
      if i = 0 then X r else if i = 1 then Z r else b j
    have hV : ∀ i, HasDerivAt (V i) (deriv (V i) s) s := by
      intro i
      fin_cases i
      · change HasDerivAt X (deriv X s) s
        exact hA.hasDerivAt
      · change HasDerivAt Z (deriv Z s) s
        exact hY.hasDerivAt
      · change HasDerivAt (fun _ : Real ↦ b j) (deriv (fun _ : Real ↦ b j) s) s
        simpa using hasDerivAt_const s (b j)
    have hcomp := cml_deriv_zero (A' := deriv Cm s) hCm.hasDerivAt hV hCm0
    have hEq : (fun r ↦ Cm r (fun i ↦ V i r)) = f j := by
      funext r
      simp [f, V, X, Z, b, v3]
    rw [← hEq]
    exact hcomp.differentiableAt
  have hx₀ : x₀ ∈ (trivializationAt E (TangentSpace I : M → Type _) x₀).baseSet :=
    mem_baseSet_trivializationAt E (TangentSpace I : M → Type _) x₀
  have hbase : ∀ᶠ r in 𝓝 s,
      alpha r ∈ (trivializationAt E (TangentSpace I : M → Type _) x₀).baseSet :=
    halpha.continuousAt
      ((trivializationAt E (TangentSpace I : M → Type _) x₀).open_baseSet.mem_nhds hx₀)
  have hinv : ∀ i j : Fin (Module.finrank Real E),
      DifferentiableAt Real
        (fun r ↦ chartInvGramMatrix (I := I) q x₀ (alpha r) i j) s := by
    intro i j
    have hreg := (chartInvGramMatrix_entry_contMDiffOn (I := I) q x₀ i j).contMDiffAt
      ((trivializationAt E (TangentSpace I : M → Type _) x₀).open_baseSet.mem_nhds hx₀)
    exact mdifferentiableAt_iff_differentiableAt.mp
      ((hreg.mdifferentiableAt (by simp)).comp s halpha)
  let G : Real → E := fun r ↦
    ∑ i : Fin (Module.finrank Real E),
      (∑ j : Fin (Module.finrank Real E),
        chartInvGramMatrix (I := I) q x₀ (alpha r) i j * f j r) • b i
  have hG : DifferentiableAt Real G s := by
    refine DifferentiableAt.fun_sum fun i _ ↦ ?_
    refine (DifferentiableAt.fun_sum fun j _ ↦ ?_).smul_const (b i)
    exact (hinv i j).mul (hf j)
  have hCeq : C =ᶠ[𝓝 s] fun r ↦
      (trivializationAt E (TangentSpace I : M → Type _) x₀).symmL Real
        (alpha r) (G r) := by
    filter_upwards [hbase] with r hr
    rw [← (trivializationAt E (TangentSpace I : M → Type _) x₀).symmL_continuousLinearMapAt
      (R := Real) hr (C r)]
    congr 1
    let cv : ∀ x : M, TangentSpace I x →ₗ[Real] Real := fun x ↦
      if h : x = alpha r then
        h ▸ (q.inner (alpha r) (C r)).toLinearMap
      else 0
    have hsharp : metricSharp (I := I) q (alpha r) (cv (alpha r)) = C r := by
      apply metricFlatLinear_injective (I := I) q (alpha r)
      ext w
      simp only [metricFlatLinear_apply, inner_metricSharp]
      simp only [cv, dif_pos]
      rfl
    have hmodel := trivToE_metricSharp (I := I) q x₀ cv hr
    rw [← hsharp, hmodel]
    simp only [G, b]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    have htriv := Tensor0SSpace.trivializationAt_apply
      (𝕜 := Real) (I := I) (x₀ := x₀) (x := alpha r) 3
      (lowerBilin (I := I) (metricTensorField (I := I) q (alpha r))
        (CovariantDerivative.difference
          (metricCov (I := I) (S.base.metric (T - r ^ 2)))
          (metricCov (I := I) q) (alpha r)))
        (v3 (X r) (Z r) (b j))
    change cv (alpha r) (chartBasisVecFiber (I := I) x₀ j (alpha r)) = f j r
    simp only [cv, dif_pos]
    change q.inner (alpha r) (C r)
      (chartBasisVecFiber (I := I) x₀ j (alpha r)) = f j r
    rw [show chartBasisVecFiber (I := I) x₀ j (alpha r) =
        (trivializationAt E (TangentSpace I : M → Type _) x₀).symmL Real
          (alpha r) (b j) by rfl]
    calc
      q.inner (alpha r) (C r)
          ((trivializationAt E (TangentSpace I : M → Type _) x₀).symmL Real
            (alpha r) (b j)) =
          (lowerBilin (I := I) (metricTensorField (I := I) q (alpha r))
            (CovariantDerivative.difference
              (metricCov (I := I) (S.base.metric (T - r ^ 2)))
              (metricCov (I := I) q) (alpha r))
            (vec3 (A r) (Y r)
              ((trivializationAt E (TangentSpace I : M → Type _) x₀).symmL Real
                (alpha r) (b j)))) := by rfl
      _ = Cm r (v3 (X r) (Z r) (b j)) := by
        let e := trivializationAt E (TangentSpace I : M → Type _) x₀
        have hslots : (fun i ↦
            e.symmL Real (alpha r) (v3 (X r) (Z r) (b j) i)) =
            vec3 (A r) (Y r)
              (e.symmL Real (alpha r) (b j)) := by
          funext i
          fin_cases i
          · simpa [e, X, v3, vec3, chartRepAt_apply] using
              e.symmL_continuousLinearMapAt (R := Real) hr (A r)
          · simpa [e, Z, v3, vec3, chartRepAt_apply] using
              e.symmL_continuousLinearMapAt (R := Real) hr (Y r)
          · simp [v3, vec3]
        rw [hslots] at htriv
        simpa only [Cm, tensor0SModelAt] using htriv.symm
      _ = f j r := rfl
  have hGrep : (fun r ↦ chartRepAt (I := I) alpha C s r) =ᶠ[𝓝 s] G := by
    filter_upwards [hbase, hCeq] with r hrbase hr
    change trivToE (I := I) x₀ (alpha r) (C r) = G r
    rw [hr]
    exact (trivializationAt E (TangentSpace I : M → Type _) x₀).continuousLinearMapAt_symmL
      (R := Real) hrbase (G r)
  simpa only [C, q] using hG.congr_of_eventuallyEq hGrep

end DifferentialGeometry.PDE.RicciFlow
