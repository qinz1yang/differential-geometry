import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.PullbackCovariantNaturality
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Bundle
open scoped Manifold ContDiff

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
variable {N : Type u} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]

section PartialTrans

noncomputable def PartialDiffeomorph.trans {P : Type u} [TopologicalSpace P]
    [ChartedSpace H P] [IsManifold I ∞ P]
    (Φ : PartialDiffeomorph I I M N (∞ : WithTop ℕ∞))
    (Φ' : PartialDiffeomorph I I N P (∞ : WithTop ℕ∞)) :
    PartialDiffeomorph I I M P (∞ : WithTop ℕ∞) where
  toPartialEquiv := Φ.toPartialEquiv.trans Φ'.toPartialEquiv
  open_source := by
    have hsrc : (Φ.toPartialEquiv.trans Φ'.toPartialEquiv).source
        = Φ.source ∩ (Φ : M → N) ⁻¹' Φ'.source := rfl
    rw [hsrc]
    exact Φ.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage Φ.open_source
      Φ'.open_source
  open_target := by
    have htgt : (Φ.toPartialEquiv.trans Φ'.toPartialEquiv).target
        = Φ'.target ∩ (Φ'.symm : P → N) ⁻¹' Φ.target := by
      rw [PartialEquiv.trans_target]
      rfl
    rw [htgt]
    exact Φ'.symm.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage Φ'.open_target
      Φ.open_target
  contMDiffOn_toFun := by
    have hsrc : (Φ.toPartialEquiv.trans Φ'.toPartialEquiv).source
        = Φ.source ∩ (Φ : M → N) ⁻¹' Φ'.source := rfl
    rw [hsrc]
    exact Φ'.contMDiffOn_toFun.comp
      (Φ.contMDiffOn_toFun.mono Set.inter_subset_left)
      (fun y hy => hy.2)
  contMDiffOn_invFun := by
    have htgt : (Φ.toPartialEquiv.trans Φ'.toPartialEquiv).target
        = Φ'.target ∩ (Φ'.symm : P → N) ⁻¹' Φ.target := by
      rw [PartialEquiv.trans_target]
      rfl
    rw [htgt]
    exact Φ.symm.contMDiffOn_toFun.comp
      (Φ'.symm.contMDiffOn_toFun.mono Set.inter_subset_left)
      (fun y hy => hy.2)

end PartialTrans

section TowerZero

set_option backward.isDefEq.respectTransparency false in
omit [SigmaCompactSpace M] in
theorem covStep_zero (gRef : SmoothRiemannianMetric I M) (s : Nat)
    [SigmaCompactSpace M] :
    covStep (I := I) gRef s
        (0 : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) s)
      = 0 := by
  have h := (covStep_add (I := I) gRef s 0 0).symm
  rw [add_zero] at h
  have h2 : covStep (I := I) gRef s 0 + covStep (I := I) gRef s 0
      = covStep (I := I) gRef s 0 + 0 := by rw [add_zero]; exact h
  exact add_left_cancel h2

set_option backward.isDefEq.respectTransparency false in
theorem iterCov_metric_zero (g : SmoothRiemannianMetric I M) (a : Nat) :
    iterCov (I := I) g 2 (Tensor0SBundle.metricTensorField (I := I) g) (a + 1) = 0 := by
  induction a with
  | zero =>
      refine DFunLike.ext _ _ (fun x => ?_)
      refine ContinuousMultilinearMap.ext (fun slots => ?_)
      obtain ⟨X, hX⟩ := ContMDiffSection.exists_eq_at_gen (I := I) (F := E)
        (V := TangentSpace I) (n := (⊤ : ℕ∞)) x (slots 0)
      have hslots : slots = Fin.cons (X x) (Fin.tail slots) := by
        rw [hX]
        exact (Fin.cons_self_tail slots).symm
      rw [show iterCov (I := I) g 2 (Tensor0SBundle.metricTensorField (I := I) g) 1
          = covStep (I := I) g 2 (Tensor0SBundle.metricTensorField (I := I) g) from rfl]
      rw [covStep_apply, hslots,
        Tensor0SBundle.totalNabla0SFun_apply_section (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) 2 _ X (Tensor0SBundle.metricTensorField (I := I) g) x _,
        Tensor0SBundle.nabla_metric_zero (I := I) _ g
          (DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric_isMetricCompatible
            (I := I) g) X x]
      simp
  | succ a ih =>
      rw [show iterCov (I := I) g 2 (Tensor0SBundle.metricTensorField (I := I) g) (a + 1 + 1)
          = covStep (I := I) g (2 + (a + 1))
              (iterCov (I := I) g 2 (Tensor0SBundle.metricTensorField (I := I) g) (a + 1))
          from rfl]
      rw [ih, covStep_zero]

set_option backward.isDefEq.respectTransparency false in
omit [SigmaCompactSpace M] in
theorem iterCov_sub (gRef : SmoothRiemannianMetric I M) (r : Nat)
    (A0 B0 : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) r)
    (a : Nat) :
    iterCov (I := I) gRef r (A0 - B0) a
      = iterCov (I := I) gRef r A0 a - iterCov (I := I) gRef r B0 a := by
  have h := iterCov_add (I := I) gRef r (A0 - B0) B0 a
  rw [sub_add_cancel] at h
  rw [h]
  abel

set_option backward.isDefEq.respectTransparency false in
omit [SigmaCompactSpace M] in
theorem covDOF_zero (gRef : SmoothRiemannianMetric I M) (a : Nat) :
    covDerivOfField (I := I) gRef
        (0 : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2) a
      = 0 := by
  have h := covDerivOfField_sub (I := I) gRef 0 0 a
  simpa using h

set_option backward.isDefEq.respectTransparency false in
omit [SigmaCompactSpace M] in
theorem t02Norm_eq_iterCov [I.Boundaryless] {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (A : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (gRef : SmoothRiemannianMetric I M) (a : ℕ) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv : Tensor0SBundle.MetricInverseInBasis_gen (I := I) gRef x basis
      (Tensor0SBundle.identityInvMetric (Idx := Idx))) :
    tensor02CovDerivNormWith (I := I) a A gRef gRef x
      = Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef x (2 + a)
          (iterCov (I := I) gRef 2 A a x)) := by
  unfold tensor02CovDerivNormWith
  rw [tensor02_eq_covDOF, covDerivOfField_eq_iterCov]
  change Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef x (a + 2)
      (ContinuousMultilinearMap.domDomCongr (acEquiv a)
        (iterCov (I := I) gRef 2 A a x)))
    = Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef x (2 + a)
        (iterCov (I := I) gRef 2 A a x))
  rw [Tensor0SBundle.normSq0S_domDomCongr (I := I) gRef x basis hinv (acEquiv a)
      (iterCov (I := I) gRef 2 A a x)]

end TowerZero

section C0Equiv

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem inner_le_of_c0
    (Gm g : SmoothRiemannianMetric I M) {K : Set M} {ε : ℝ}
    (hc0 : ∀ x ∈ K, metricTensorErrorNorm (I := I)
      (Tensor0SBundle.metricTensorField (I := I) Gm) g x ≤ ε) :
    ∀ x ∈ K, ∀ v : TangentSpace I x,
      (1 - ε) * g.inner x v v ≤ Gm.inner x v v ∧
        Gm.inner x v v ≤ (1 + ε) * g.inner x v v := by
  classical
  intro x hx v
  obtain ⟨basis, hON⟩ :=
    DifferentialGeometry.Geometry.Curvature.exists_gOrthonormalBasis (I := I) g x
  have hCS := Tensor0SBundle.abs_apply_le_sqrt_normSq0S (I := I)
    g x 2 basis (fun i j => hON i j)
    ((Tensor0SBundle.metricTensorField (I := I) Gm) x
      - Tensor0SBundle.metricTensorField (I := I) g x)
    (fun _ => v)
  have hval : ((Tensor0SBundle.metricTensorField (I := I) Gm) x
      - Tensor0SBundle.metricTensorField (I := I) g x) (fun _ => v)
      = Gm.inner x v v - g.inner x v v := by
    calc
      ((Tensor0SBundle.metricTensorField (I := I) Gm) x -
          Tensor0SBundle.metricTensorField (I := I) g x) (fun _ => v) =
          Tensor0SBundle.metricTensorField (I := I) Gm x (fun _ => v) -
            Tensor0SBundle.metricTensorField (I := I) g x (fun _ => v) :=
        Tensor0SBundle.Tensor0SSpace.sub_apply 2 x _ _ _
      _ = Gm.inner x v v - g.inner x v v := by
        rw [Tensor0SBundle.metricTensorField_apply,
          Tensor0SBundle.metricTensorField_apply]
  have hnn : 0 ≤ g.inner x v v := by
    rcases eq_or_ne v 0 with hv | hv
    · simp [hv]
    · exact le_of_lt (g.pos x v hv)
  have hprod : (∏ _a : Fin 2, Real.sqrt (g.inner x v v)) = g.inner x v v := by
    rw [Fin.prod_univ_two, Real.mul_self_sqrt hnn]
  have habs : |Gm.inner x v v - g.inner x v v| ≤ ε * g.inner x v v := by
    have herr := hc0 x hx
    calc |Gm.inner x v v - g.inner x v v|
        = |((Tensor0SBundle.metricTensorField (I := I) Gm) x
            - Tensor0SBundle.metricTensorField (I := I) g x) (fun _ => v)| := by rw [hval]
      _ ≤ Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x 2
            ((Tensor0SBundle.metricTensorField (I := I) Gm) x
              - Tensor0SBundle.metricTensorField (I := I) g x))
            * ∏ _a : Fin 2, Real.sqrt (g.inner x v v) := hCS
      _ ≤ ε * g.inner x v v := by
          rw [hprod]
          exact mul_le_mul_of_nonneg_right herr hnn
  constructor
  · nlinarith [abs_le.mp habs]
  · nlinarith [abs_le.mp habs]

set_option backward.isDefEq.respectTransparency false in
omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem sqrt_normSq_two_le
    {K : Set M} {g h : SmoothRiemannianMetric I M} {C : Real}
    (hEq : MetricUniformEquivalentOn (I := I) K g h C)
    {x : M} (hx : x ∈ K)
    (A : Tensor0SBundle.Tensor0SSpace
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :
    Real.sqrt (Tensor0SBundle.normSq0S (I := I) h x 2 A) ≤
      Real.sqrt (C ^ 2) *
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x 2 A) := by
  obtain ⟨μ, basis, hginv, hhinv, hμ_nonneg, hμ_le⟩ :=
    exists_diagInv_of_metricUniformEquivalentOn
      (I := I) (K := K) (g := g) (h := h) (C := C) hEq hx
  have hle :
      Tensor0SBundle.normSq0S (I := I) h x 2 A ≤
        C ^ 2 * Tensor0SBundle.normSq0S (I := I) g x 2 A := by
    simpa using
      Tensor0SBundle.normSq0S_diag_le
        (I := I) (g := g) (h := h) (x := x) (s := 2)
        basis μ C hginv hhinv hμ_nonneg hμ_le A
  calc Real.sqrt (Tensor0SBundle.normSq0S (I := I) h x 2 A)
      ≤ Real.sqrt (C ^ 2 * Tensor0SBundle.normSq0S (I := I) g x 2 A) :=
        Real.sqrt_le_sqrt hle
    _ = Real.sqrt (C ^ 2) * Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x 2 A) :=
        Real.sqrt_mul (by positivity) _

end C0Equiv

end HCGCompactness
end DifferentialGeometry
