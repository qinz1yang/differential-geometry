import DifferentialGeometry.Geometry.Curvature.Bochner.OrthonormalFrameTrace
import DifferentialGeometry.Geometry.Curvature.CoordRm04Bridge

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

end DifferentialGeometry.Geometry.Curvature
