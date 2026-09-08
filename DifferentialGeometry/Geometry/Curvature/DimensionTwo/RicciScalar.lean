import DifferentialGeometry.Geometry.Curvature.Bochner.OrthonormalFrameTrace
import DifferentialGeometry.Geometry.Curvature.CoordRm04Bridge
import DifferentialGeometry.Tensor.RSTensor.Product

set_option autoImplicit false

noncomputable section

open Bundle DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff BigOperators

namespace DifferentialGeometry.Geometry.Curvature

open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete Real E

private def metricPairing0312 : Equiv.Perm (Fin 4) where
  toFun i := ![0, 3, 1, 2] i
  invFun i := ![0, 2, 3, 1] i
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

private def metricPairing0213 : Equiv.Perm (Fin 4) where
  toFun i := ![0, 2, 1, 3] i
  invFun i := ![0, 2, 1, 3] i
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

omit [I.Boundaryless] [T2Space M] in
private theorem exists_metric_orthonormal_basis_two
    (g : SmoothRiemannianMetric I M) (x : M)
    (hdim : Module.finrank Real E = 2) :
    ∃ basis : Module.Basis (Fin 2) Real (TangentSpace I x),
      ∀ i j : Fin 2,
        g.inner x (basis i) (basis j) = if i = j then 1 else 0 := by
  have hdimT : Module.finrank Real (TangentSpace I x) = 2 :=
    (show Module.finrank Real (TangentSpace I x) = Module.finrank Real E from rfl).trans hdim
  let D := (tangentMetricDataGen (I := I) g x).metric
  let _ : InnerProductSpace.Core Real (TangentSpace I x) := D.toCore
  let _ : NormedAddCommGroup (TangentSpace I x) :=
    @InnerProductSpace.Core.toNormedAddCommGroup Real (TangentSpace I x) _ _ _
      D.toCore
  let _ : InnerProductSpace Real (TangentSpace I x) :=
    @InnerProductSpace.ofCore Real (TangentSpace I x) _ _ _ D.toCore.toCore
  let ob : OrthonormalBasis (Fin 2) Real (TangentSpace I x) :=
    (stdOrthonormalBasis Real (TangentSpace I x)).reindex (finCongr hdimT)
  let basis : Module.Basis (Fin 2) Real (TangentSpace I x) := ob.toBasis
  refine ⟨basis, ?_⟩
  intro i j
  have hinner : Inner.inner Real (ob i) (ob j) = D.inner (ob i) (ob j) :=
    MetricFiberData.toCore_inner D (ob i) (ob j)
  change D.inner (ob i) (ob j) = if i = j then 1 else 0
  rw [← hinner]
  exact ob.inner_eq_ite i j

theorem metricRicciAt_eq_half_metricScalarAt_smul_metric_of_finrank_eq_two
    (g : SmoothRiemannianMetric I M)
    (hdim : Module.finrank Real E = 2) (x : M) :
    metricRicciAt (I := I) (M := M) g x =
      (metricScalarAt (I := I) (M := M) g x / 2) •
        metricTensor0S (I := I) g x := by
  let _ : IsManifold I 1 M := IsManifold.of_le (I := I) (M := M)
    (n := (∞ : WithTop ℕ∞))
      (by simp : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  let _ : IsManifold I 2 M := IsManifold.of_le (I := I) (M := M)
    (n := (∞ : WithTop ℕ∞))
      (by decide : (2 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  let _ : IsManifold I 3 M := IsManifold.of_le (I := I) (M := M)
    (n := (∞ : WithTop ℕ∞))
      (by decide : (3 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  classical
  obtain ⟨basis, horth⟩ := exists_metric_orthonormal_basis_two
    (I := I) g x hdim
  let Rm := fun X Y Z W : TangentSpace I x =>
    metricRm04StdAt (I := I) (M := M) g x X Y Z W
  let K : Real := Rm (basis 1) (basis 0) (basis 0) (basis 1)
  have hinput : ∀ X Y Z W : TangentSpace I x,
      Rm Y X Z W = -Rm X Y Z W := by
    intro X Y Z W
    simpa [Rm, metricRm04StdAt_apply, metricRm04_apply] using
      (rm04InputSkewAt_of_leviCivita_realizes
        (I := I) g (metricRm04 (I := I) (M := M) g)
        (metricCurvData (I := I) (M := M) g).rm04Realizes X Y Z W)
  have houtput : ∀ X Y Z W : TangentSpace I x,
      Rm X Y Z W = -Rm X Y W Z := by
    intro X Y Z W
    simpa [Rm, metricRm04StdAt_apply, metricRm04_apply] using
      (rm04OutputSkewAt_of_leviCivita_realizes
        (I := I) g (metricRm04 (I := I) (M := M) g)
        (metricCurvData (I := I) (M := M) g).rm04Realizes X Y Z W)
  have hpair : ∀ X Y Z W : TangentSpace I x,
      Rm X Y Z W = Rm Z W X Y := by
    intro X Y Z W
    simpa [Rm, metricRm04StdAt_apply, metricRm04_apply] using
      (rm04PairSymmAt_of_leviCivita_realizes
        (I := I) g (metricRm04 (I := I) (M := M) g)
        (metricCurvData (I := I) (M := M) g).rm04Realizes X Y Z W)
  have htrace (v w : TangentSpace I x) :
      ricciTensor (I := I) g x v w =
        Rm (basis 0) v w (basis 0) +
          Rm (basis 1) v w (basis 1) := by
    let B : Fin (Module.finrank Real E) → TangentSpace I x :=
      fun i => basis (Fin.cast hdim i)
    have hB : ∀ i j : Fin (Module.finrank Real E),
        g.inner x (B i) (B j) = if i = j then 1 else 0 := by
      intro i j
      rw [horth]
      simp only [Fin.cast_inj]
    rw [ricciTensor_eq_orthonormal_trace (I := I) g x v w B hB]
    have hsum :
        (∑ i : Fin (Module.finrank Real E),
          g.inner x (riemannOp (LeviCivita (I := I) g) x (B i) v w) (B i)) =
        ∑ i : Fin 2,
          g.inner x (riemannOp (LeviCivita (I := I) g) x (basis i) v w) (basis i) := by
      exact Fintype.sum_equiv (finCongr hdim)
        (fun i => g.inner x (riemannOp (LeviCivita (I := I) g) x (B i) v w) (B i))
        (fun i => g.inner x (riemannOp (LeviCivita (I := I) g) x (basis i) v w) (basis i))
        (fun _ => rfl)
    rw [hsum, Fin.sum_univ_two]
    congr 1
    · rw [g.symm]
      exact (DifferentialGeometry.rm04_eq_inner_riem
        (I := I) g x (basis 0) v w (basis 0)).symm
    · rw [g.symm]
      exact (DifferentialGeometry.rm04_eq_inner_riem
        (I := I) g x (basis 1) v w (basis 1)).symm
  have hRicK : metricRicciAt (I := I) (M := M) g x =
      K • metricTensor0S (I := I) g x := by
    apply ext0S_basis (I := I) basis
    intro slots
    simp only [component0S_apply]
    have hslots : (fun a : Fin 2 => basis (slots a)) =
        vec2 (I := I) (basis (slots 0)) (basis (slots 1)) := by
      funext a
      fin_cases a <;> rfl
    rw [hslots, DifferentialGeometry.metricRicciAt_apply_eq_ricciTensor,
      Tensor0SSpace.smul_apply, metricTensor0S_apply, htrace]
    generalize h0 : slots 0 = i
    generalize h1 : slots 1 = j
    fin_cases i <;> fin_cases j
    · change Rm (basis 0) (basis 0) (basis 0) (basis 0) +
          Rm (basis 1) (basis 0) (basis 0) (basis 1) =
        K * g.inner x (basis 0) (basis 0)
      rw [horth 0 0, if_pos rfl]
      have hz := hinput (basis 0) (basis 0) (basis 0) (basis 0)
      have hzero : Rm (basis 0) (basis 0) (basis 0) (basis 0) = 0 := by
        linarith
      rw [hzero, zero_add]
      ring
    · change Rm (basis 0) (basis 0) (basis 1) (basis 0) +
          Rm (basis 1) (basis 0) (basis 1) (basis 1) =
        K * g.inner x (basis 0) (basis 1)
      rw [horth 0 1, if_neg (by decide)]
      have hz0 := hinput (basis 0) (basis 0) (basis 1) (basis 0)
      have hz1 := houtput (basis 1) (basis 0) (basis 1) (basis 1)
      have hzero0 : Rm (basis 0) (basis 0) (basis 1) (basis 0) = 0 := by
        linarith
      have hzero1 : Rm (basis 1) (basis 0) (basis 1) (basis 1) = 0 := by
        linarith
      rw [hzero0, hzero1]
      ring
    · change Rm (basis 0) (basis 1) (basis 0) (basis 0) +
          Rm (basis 1) (basis 1) (basis 0) (basis 1) =
        K * g.inner x (basis 1) (basis 0)
      rw [horth 1 0, if_neg (by decide)]
      have hz0 := houtput (basis 0) (basis 1) (basis 0) (basis 0)
      have hz1 := hinput (basis 1) (basis 1) (basis 0) (basis 1)
      have hzero0 : Rm (basis 0) (basis 1) (basis 0) (basis 0) = 0 := by
        linarith
      have hzero1 : Rm (basis 1) (basis 1) (basis 0) (basis 1) = 0 := by
        linarith
      rw [hzero0, hzero1]
      ring
    · change Rm (basis 0) (basis 1) (basis 1) (basis 0) +
          Rm (basis 1) (basis 1) (basis 1) (basis 1) =
        K * g.inner x (basis 1) (basis 1)
      rw [horth 1 1, if_pos rfl]
      have hz := hinput (basis 1) (basis 1) (basis 1) (basis 1)
      have hzero : Rm (basis 1) (basis 1) (basis 1) (basis 1) = 0 := by
        linarith
      rw [hzero, add_zero]
      rw [hpair (basis 0) (basis 1) (basis 1) (basis 0)]
      ring
  have hinv : MetricInverseInBasisGen (I := I) g x basis
      (identityInvMetric (Idx := Fin 2)) :=
    metricInverseInBasis_identity_of_orthonormal (I := I) g basis horth
  have htraceMetric :
      metricTracePair0SAt (I := I) g (metricTensor0S (I := I) g x) = 2 := by
    rw [metricTracePair0SAt_eq_sum_basis (I := I) g basis
      (identityInvMetric (Idx := Fin 2)) hinv]
    simp [identityInvMetric, diagonalInvMetric, metricTensor0S_apply,
      DifferentialGeometry.Geometry.Curvature.vec2, horth]
  have hscalar : metricScalarAt (I := I) (M := M) g x = 2 * K := by
    rw [metricScalarAt_def, hRicK, metricTracePair0SAt_smul, htraceMetric]
    ring
  rw [hRicK, hscalar]
  congr 1
  ring

theorem ricciTensor_eq_half_metricScalarAt_mul_inner_of_finrank_eq_two
    (g : SmoothRiemannianMetric I M)
    (hdim : Module.finrank Real E = 2) (x : M)
    (v w : TangentSpace I x) :
    ricciTensor (I := I) g x v w =
      metricScalarAt (I := I) (M := M) g x / 2 * g.inner x v w := by
  rw [← DifferentialGeometry.metricRicciAt_apply_eq_ricciTensor (I := I) g x v w,
    metricRicciAt_eq_half_metricScalarAt_smul_metric_of_finrank_eq_two
      (I := I) g hdim x, Tensor0SSpace.smul_apply, metricTensor0S_apply]
  rfl

theorem metricRm04StdAt_eq_scalar_div_two_of_finrank_eq_two
    (g : SmoothRiemannianMetric I M)
    (hdim : Module.finrank Real E = 2) (x : M)
    (v w z u : TangentSpace I x) :
    metricRm04StdAt (I := I) (M := M) g x v w z u =
      metricScalarAt (I := I) (M := M) g x / 2 *
        (g.inner x v u * g.inner x w z -
          g.inner x v z * g.inner x w u) := by
  classical
  obtain ⟨basis, horth⟩ := exists_metric_orthonormal_basis_two
    (I := I) g x hdim
  let Rm := fun X Y Z W : TangentSpace I x =>
    metricRm04StdAt (I := I) (M := M) g x X Y Z W
  have hinput : ∀ X Y Z W : TangentSpace I x,
      Rm Y X Z W = -Rm X Y Z W := by
    intro X Y Z W
    simpa [Rm, metricRm04StdAt_apply, metricRm04_apply] using
      (rm04InputSkewAt_of_leviCivita_realizes
        (I := I) g (metricRm04 (I := I) (M := M) g)
        (metricCurvData (I := I) (M := M) g).rm04Realizes X Y Z W)
  have houtput : ∀ X Y Z W : TangentSpace I x,
      Rm X Y Z W = -Rm X Y W Z := by
    intro X Y Z W
    simpa [Rm, metricRm04StdAt_apply, metricRm04_apply] using
      (rm04OutputSkewAt_of_leviCivita_realizes
        (I := I) g (metricRm04 (I := I) (M := M) g)
        (metricCurvData (I := I) (M := M) g).rm04Realizes X Y Z W)
  have hpair : ∀ X Y Z W : TangentSpace I x,
      Rm X Y Z W = Rm Z W X Y := by
    intro X Y Z W
    simpa [Rm, metricRm04StdAt_apply, metricRm04_apply] using
      (rm04PairSymmAt_of_leviCivita_realizes
        (I := I) g (metricRm04 (I := I) (M := M) g)
        (metricCurvData (I := I) (M := M) g).rm04Realizes X Y Z W)
  have htrace (a b : TangentSpace I x) :
      ricciTensor (I := I) g x a b =
        Rm (basis 0) a b (basis 0) +
          Rm (basis 1) a b (basis 1) := by
    let B : Fin (Module.finrank Real E) → TangentSpace I x :=
      fun i => basis (Fin.cast hdim i)
    have hB : ∀ i j : Fin (Module.finrank Real E),
        g.inner x (B i) (B j) = if i = j then 1 else 0 := by
      intro i j
      rw [horth]
      simp only [Fin.cast_inj]
    rw [ricciTensor_eq_orthonormal_trace (I := I) g x a b B hB]
    have hsum :
        (∑ i : Fin (Module.finrank Real E),
          g.inner x (riemannOp (LeviCivita (I := I) g) x (B i) a b) (B i)) =
        ∑ i : Fin 2,
          g.inner x (riemannOp (LeviCivita (I := I) g) x (basis i) a b) (basis i) := by
      exact Fintype.sum_equiv (finCongr hdim)
        (fun i => g.inner x (riemannOp (LeviCivita (I := I) g) x (B i) a b) (B i))
        (fun i => g.inner x (riemannOp (LeviCivita (I := I) g) x (basis i) a b) (basis i))
        (fun _ => rfl)
    rw [hsum, Fin.sum_univ_two]
    congr 1
    · rw [g.symm]
      exact (DifferentialGeometry.rm04_eq_inner_riem
        (I := I) g x (basis 0) a b (basis 0)).symm
    · rw [g.symm]
      exact (DifferentialGeometry.rm04_eq_inner_riem
        (I := I) g x (basis 1) a b (basis 1)).symm
  let K := Rm (basis 1) (basis 0) (basis 0) (basis 1)
  have hK : K = metricScalarAt (I := I) (M := M) g x / 2 := by
    have hric := ricciTensor_eq_half_metricScalarAt_mul_inner_of_finrank_eq_two
      (I := I) g hdim x (basis 0) (basis 0)
    rw [htrace, horth 0 0, if_pos rfl] at hric
    have hzero : Rm (basis 0) (basis 0) (basis 0) (basis 0) = 0 := by
      have hz := hinput (basis 0) (basis 0) (basis 0) (basis 0)
      linarith
    rw [hzero, zero_add] at hric
    simpa [K] using hric
  let G : Tensor0SSpace (I := I) 2 x :=
    (((continuousMultilinearCurryFin1 Real (TangentSpace I x) Real).symm.toContinuousLinearMap).comp
      (g.inner x)).uncurryLeft
  have hG (slots : Fin 2 → TangentSpace I x) :
      G slots = g.inner x (slots 0) (slots 1) := by
    change
      ((continuousMultilinearCurryFin1 Real (TangentSpace I x) Real).symm
        (g.inner x (slots 0))) (fun i : Fin 1 => slots i.succ) =
        g.inner x (slots 0) (slots 1)
    have htail : (fun i : Fin 1 => slots i.succ) = fun _ : Fin 1 => slots 1 := by
      funext i
      fin_cases i
      rfl
    rw [htail]
    rfl
  let P := Tensor0SSpace.product G G
  let A := P.domDomCongr metricPairing0312
  let B := P.domDomCongr metricPairing0213
  have hAapply (q : Fin 4 → TangentSpace I x) :
      A q = g.inner x (q 0) (q 3) * g.inner x (q 1) (q 2) := by
    change Tensor0SSpace.product G G (q ∘ metricPairing0312) = _
    rw [Tensor0SSpace.product_apply, hG, hG]
    rfl
  have hBapply (q : Fin 4 → TangentSpace I x) :
      B q = g.inner x (q 0) (q 2) * g.inner x (q 1) (q 3) := by
    change Tensor0SSpace.product G G (q ∘ metricPairing0213) = _
    rw [Tensor0SSpace.product_apply, hG, hG]
    rfl
  have htensor : metricRm04At (I := I) (M := M) g x =
      (metricScalarAt (I := I) (M := M) g x / 2) • (A - B) := by
    apply (tensor0SSpaceFiberContinuousLinearEquiv (I := I) 4 x).injective
    apply ContinuousMultilinearMap.toMultilinearMap_injective
    refine Module.Basis.ext_multilinear (e := fun _ : Fin 4 => basis) ?_
    intro slots
    change Rm (basis (slots 0)) (basis (slots 1))
        (basis (slots 2)) (basis (slots 3)) =
      (metricScalarAt (I := I) (M := M) g x / 2) *
        (A (fun i => basis (slots i)) - B (fun i => basis (slots i)))
    rw [hAapply, hBapply]
    have hinputZero (a c d : Fin 2) :
        Rm (basis a) (basis a) (basis c) (basis d) = 0 := by
      have hz := hinput (basis a) (basis a) (basis c) (basis d)
      linarith
    have houtputZero (a b c : Fin 2) :
        Rm (basis a) (basis b) (basis c) (basis c) = 0 := by
      have hz := houtput (basis a) (basis b) (basis c) (basis c)
      linarith
    have h0110 : Rm (basis 0) (basis 1) (basis 1) (basis 0) = K := by
      exact hpair (basis 0) (basis 1) (basis 1) (basis 0)
    have h0101 : Rm (basis 0) (basis 1) (basis 0) (basis 1) = -K := by
      rw [houtput (basis 0) (basis 1) (basis 0) (basis 1), h0110]
    have h1010 : Rm (basis 1) (basis 0) (basis 1) (basis 0) = -K := by
      rw [houtput (basis 1) (basis 0) (basis 1) (basis 0)]
    generalize h0 : slots 0 = i
    generalize h1 : slots 1 = j
    generalize h2 : slots 2 = k
    generalize h3 : slots 3 = l
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
      simp [horth, hinputZero, houtputZero, h0110, h0101, h1010, hK, K]
  have happly := congrArg
    (fun T : Tensor04At (I := I) (M := M) x =>
      T (vec4 (I := I) v w z u)) htensor
  rw [Tensor0SSpace.smul_apply, Tensor0SSpace.sub_apply,
    hAapply, hBapply] at happly
  simpa [metricRm04StdAt_apply,
    DifferentialGeometry.Geometry.Curvature.vec4] using happly


theorem riemannOp_eq_scalar_div_two_of_finrank_eq_two
    (g : SmoothRiemannianMetric I M) (hn : Module.finrank Real E = 2)
    (x : M) (v w z : TangentSpace I x) :
    riemannOp (LeviCivita g) x v w z =
      (metricScalarAt g x / 2) • (g.inner x w z • v - g.inner x v z • w) := by
  apply SmoothRiemannianMetric.eq_of_inner_eq g
  intro u
  rw [g.symm x (riemannOp (LeviCivita g) x v w z) u,
    ← DifferentialGeometry.rm04_eq_inner_riem g x v w z u,
    metricRm04StdAt_eq_scalar_div_two_of_finrank_eq_two g hn]
  simp only [map_smul, map_sub, smul_apply, sub_apply, smul_eq_mul]
  ring

end DifferentialGeometry.Geometry.Curvature
