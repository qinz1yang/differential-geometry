import DifferentialGeometry.Geometry.Connection.ChartTensorNabla.Agreement.ChartTensor0SCovariantDerivativeAgreementSucc
import DifferentialGeometry.Geometry.Connection.TensorNabla.Tensor0SNabla
import DifferentialGeometry.Geometry.Connection.TensorNabla.Tensor0SPartialEval
import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.Regularity.Tensor0S
open DifferentialGeometry.Geometry.Curvature

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff BigOperators
open DifferentialGeometry.Tensor0SBundle

namespace DifferentialGeometry
namespace Geometry
namespace Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

open DifferentialGeometry.Tensor0SNabla
open DifferentialGeometry.Tensor0SPartialEval
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

private def SectionSmooth (s : ℕ) (T : Π b : M, Tensor0SSpace s I b) : Prop :=
  letI _h_top : TopologicalSpace (TotalSpace (Tensor0SModel s ℝ E)
      (fun x : M => Tensor0SSpace s I x)) :=
    tensor0SBundle_topology s
  ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) ∞
    (fun b : M => TotalSpace.mk' (Tensor0SModel s ℝ E)
      (E := fun x : M => Tensor0SSpace s I x) b (T b))

private def VecSmooth (Y : Π b : M, TangentSpace I b) : Prop :=
  ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
    (fun b : M => TotalSpace.mk' E (E := fun x : M => TangentSpace I x) b (Y b))

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma tensor0Iso_symm_apply_empty' (x : M) (a : ℝ) :
    (show ContinuousMultilinearMap ℝ (fun _ : Fin 0 => TangentSpace I x) ℝ from
        ((tensor0Iso (I := I) (M := M) x).symm a))
      (fun i => Fin.elim0 i) = a := by
  classical
  let T₀ : Π y : M, Tensor0SSpace 0 I y :=
    fun y => if h : y = x then h ▸ ((tensor0Iso (I := I) (M := M) x).symm a) else 0
  have hT0x : T₀ x = (tensor0Iso (I := I) (M := M) x).symm a := by simp [T₀]
  have hscalarFn :
      (show ContinuousMultilinearMap ℝ (fun _ : Fin 0 => TangentSpace I x) ℝ from
          T₀ x) (0 : Fin 0 → TangentSpace I x) = scalarFn I M T₀ x :=
    (scalarFn_eq_apply_zero (I := I) (M := M) T₀ x).symm
  have hscalar : scalarFn I M T₀ x = a := by
    change (tensor0Iso (I := I) (M := M) x) (T₀ x) = a
    rw [hT0x]
    exact (tensor0Iso (I := I) (M := M) x).apply_symm_apply a
  have h_inputs : (fun i : Fin 0 => Fin.elim0 i) = (0 : Fin 0 → TangentSpace I x) :=
    Subsingleton.elim _ _
  rw [h_inputs, ← hT0x, hscalarFn, hscalar]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma curry_symm_cons (s : ℕ) {b : M}
    (Φ : TangentSpace I b →L[ℝ] Tensor0SSpace s I b)
    (v : TangentSpace I b) (m : Fin s → TangentSpace I b) :
    (show ContinuousMultilinearMap ℝ
        (fun _ : Fin (s + 1) => TangentSpace I b) ℝ from
      (tensor0S_curry (I := I) (M := M) s b).symm Φ)
        (Fin.cons v m) =
      (show ContinuousMultilinearMap ℝ
          (fun _ : Fin s => TangentSpace I b) ℝ from Φ v) m := by
  classical
  set P : Tensor0SSpace (s + 1) I b :=
    (tensor0S_curry (I := I) (M := M) s b).symm Φ
  have hroundtrip : tensor0S_curry (I := I) (M := M) s b P = Φ :=
    (tensor0S_curry (I := I) (M := M) s b).apply_symm_apply Φ
  have hev := TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
    (T := P) (v0 := v) (vs := m)
  have hcur : (show ContinuousMultilinearMap ℝ
        (fun _ : Fin s => TangentSpace I b) ℝ from
      tensor0S_curry (I := I) (M := M) s b P v) m =
      (show ContinuousMultilinearMap ℝ
          (fun _ : Fin (s + 1) => TangentSpace I b) ℝ from P)
        (Fin.cons v m) := hev.symm
  rw [hroundtrip] at hcur
  exact hcur.symm

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma cmlm_cons_eq_curry (s : ℕ) {x : M}
    (T : Π b : M, Tensor0SSpace (s + 1) I b) (v0 : TangentSpace I x)
    (m : Fin s → TangentSpace I x) :
    (show ContinuousMultilinearMap ℝ
        (fun _ : Fin (s + 1) => TangentSpace I x) ℝ from T x)
      (Fin.cons v0 m) =
      (show ContinuousMultilinearMap ℝ
          (fun _ : Fin s => TangentSpace I x) ℝ from
        curriedSection I M T x v0) m := by
  change (show ContinuousMultilinearMap ℝ
        (fun _ : Fin (s + 1) => TangentSpace I x) ℝ from T x) (Fin.cons v0 m) =
    (show ContinuousMultilinearMap ℝ
        (fun _ : Fin s => TangentSpace I x) ℝ from
      tensor0S_curry (I := I) (M := M) s x (T x) v0) m
  exact (TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
    (T := T x) (v0 := v0) (vs := m)).symm

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M]
    [SigmaCompactSpace M] in
theorem abstractDerivEval_aux
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞] :
    ∀ (s : ℕ) (T : Π b : M, Tensor0SSpace s I b)
      (V : Fin s → Π b : M, TangentSpace I b)
      (X : Π b : M, TangentSpace I b)
      (_hT : SectionSmooth (I := I) s T)
      (_hV : ∀ a : Fin s, VecSmooth (I := I) (V a))
      (_hX : VecSmooth (I := I) X)
      (x : M),
      (show ContinuousMultilinearMap ℝ
          (fun _ : Fin s => TangentSpace I x) ℝ from
        tensor0SCovariantDerivative I M s cov T x (X x))
        (fun a : Fin s => V a x) =
      extDerivFun (I := I)
          (fun p : M => (show ContinuousMultilinearMap ℝ
              (fun _ : Fin s => TangentSpace I p) ℝ from T p)
            (fun a : Fin s => V a p)) x (X x) -
        ∑ a : Fin s,
          (show ContinuousMultilinearMap ℝ
              (fun _ : Fin s => TangentSpace I x) ℝ from T x)
            (Function.update (fun b : Fin s => V b x) a
              ((cov (V a) x) (X x))) := by
  intro s
  induction s with
  | zero =>
    intro T V X hT hV hX x
    have hempty : (fun a : Fin 0 => V a x) = (fun i : Fin 0 => Fin.elim0 i) := by
      funext i; exact i.elim0
    rw [hempty]
    rw [tensor0SCovariantDerivative_apply_zero (I := I) (M := M) cov T x (X x)]
    rw [tensor0Iso_symm_apply_empty' (I := I) (M := M) x
        (extDerivFun (I := I) (scalarFn I M T) x (X x))]
    have hscalar_eq :
        scalarFn I M T =
          (fun p : M => (show ContinuousMultilinearMap ℝ
              (fun _ : Fin 0 => TangentSpace I p) ℝ from T p)
            (fun a : Fin 0 => V a p)) := by
      funext p
      rw [scalarFn_eq_apply_zero (I := I) (M := M) T p]
      congr 1
      funext i; exact i.elim0
    rw [hscalar_eq]
    simp
  | succ s ih =>
    intro T V X hT hV hX x
    have hX_at : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
        (fun b : M => TotalSpace.mk' E (E := fun x : M => TangentSpace I x) b (X b)) x :=
      hX.contMDiffAt.mdifferentiableAt (by simp)
    have hV0_at : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
        (fun b : M => TotalSpace.mk' E (E := fun x : M => TangentSpace I x) b (V 0 b)) x :=
      (hV 0).contMDiffAt.mdifferentiableAt (by simp)
    have hT_at : TensorSectionMDiffAt (I := I) (s + 1) T x :=
      hT.contMDiffAt.mdifferentiableAt (by simp)
    have hτ_at := mdifferentiableAt_curriedSection_of_section (I := I) (M := M) s T hT_at
    set PT : Π b : M, Tensor0SSpace s I b :=
      tensor0SPartialEval I M T (V 0) with hPT_def
    have hPT : SectionSmooth (I := I) s PT :=
      contMDiff_tensor0SPartialEval (I := I) (M := M) (s := s) T hT (V 0) (hV 0)
    have htuple : (fun a : Fin (s + 1) => V a x) =
        Fin.cons (V 0 x) (fun i : Fin s => V i.succ x) := by
      funext a
      refine Fin.cases ?_ ?_ a
      · simp
      · intro i; simp
    conv_lhs => rw [htuple]
    rw [tensor0SCovariantDerivative_succ_eq (I := I) (M := M) (s := s) (cov := cov)]
    rw [tensor0SCovariantDerivative_succ_apply (I := I) (M := M) (s := s)
        (cov_TM := cov) (cov_s := tensor0SCovariantDerivative I M s cov) T x (X x)]
    rw [curry_symm_cons (I := I) (M := M) s
        (Φ := HomConnection.homBundleCovariantDerivativeFun I M
          (Tensor0SModel s ℝ E) (fun x : M => Tensor0SSpace s I x) cov
          (tensor0SCovariantDerivative I M s cov) (curriedSection I M T) x (X x))
        (V 0 x) (fun i : Fin s => V i.succ x)]
    have hPsi := HomConnection.homBundleCovariantDerivativeFun_apply_eq
      (I := I) (M := M) (F := Tensor0SModel s ℝ E)
      (V := fun x : M => Tensor0SSpace s I x)
      (cov_TM := cov) (cov_V := tensor0SCovariantDerivative I M s cov)
      (τ := curriedSection I M T) (x := x) hτ_at
      (V_field := X) (Y := V 0) hX_at hV0_at
    rw [show HomConnection.homBundleCovariantDerivativeFun I M
          (Tensor0SModel s ℝ E) (fun x : M => Tensor0SSpace s I x) cov
          (tensor0SCovariantDerivative I M s cov) (curriedSection I M T) x (X x) (V 0 x) =
        (tensor0SCovariantDerivative I M s cov)
            (fun y : M => (curriedSection I M T) y (V 0 y)) x (X x) -
          curriedSection I M T x (cov (V 0) x (X x)) from hPsi]
    have hpair : (fun y : M => (curriedSection I M T) y (V 0 y)) = PT := by
      funext y; rw [hPT_def]; rfl
    rw [hpair]
    rw [ContinuousMultilinearMap.sub_apply]
    have hIH := ih PT (fun i : Fin s => V i.succ) X hPT
      (fun i => hV i.succ) hX x
    rw [hIH]
    have hintr :
        (fun p : M => (show ContinuousMultilinearMap ℝ
            (fun _ : Fin s => TangentSpace I p) ℝ from PT p)
          (fun i : Fin s => V i.succ p)) =
        (fun p : M => (show ContinuousMultilinearMap ℝ
            (fun _ : Fin (s + 1) => TangentSpace I p) ℝ from T p)
          (fun a : Fin (s + 1) => V a p)) := by
      funext p
      have hcp : (fun a : Fin (s + 1) => V a p) =
          Fin.cons (V 0 p) (fun i : Fin s => V i.succ p) := by
        funext a
        refine Fin.cases ?_ ?_ a
        · simp
        · intro i; simp
      rw [hcp, hPT_def, tensor0SPartialEval_eq_curriedSection]
      exact (cmlm_cons_eq_curry (I := I) (M := M) s T (V 0 p)
        (fun i : Fin s => V i.succ p)).symm
    rw [hintr]
    have hslot0 :
        (show ContinuousMultilinearMap ℝ
            (fun _ : Fin s => TangentSpace I x) ℝ from
          curriedSection I M T x (cov (V 0) x (X x)))
          (fun i : Fin s => V i.succ x) =
        (show ContinuousMultilinearMap ℝ
            (fun _ : Fin (s + 1) => TangentSpace I x) ℝ from T x)
          (Fin.cons (cov (V 0) x (X x)) (fun i : Fin s => V i.succ x)) :=
      (cmlm_cons_eq_curry (I := I) (M := M) s T (cov (V 0) x (X x))
        (fun i : Fin s => V i.succ x)).symm
    rw [hslot0]
    have htail :
        ∀ i : Fin s,
          (show ContinuousMultilinearMap ℝ
              (fun _ : Fin s => TangentSpace I x) ℝ from PT x)
            (Function.update (fun j : Fin s => V j.succ x) i ((cov (V i.succ) x) (X x))) =
          (show ContinuousMultilinearMap ℝ
              (fun _ : Fin (s + 1) => TangentSpace I x) ℝ from T x)
            (Fin.cons (V 0 x)
              (Function.update (fun j : Fin s => V j.succ x) i
                ((cov (V i.succ) x) (X x)))) := by
      intro i
      rw [hPT_def, tensor0SPartialEval_eq_curriedSection]
      exact (cmlm_cons_eq_curry (I := I) (M := M) s T (V 0 x)
        (Function.update (fun j : Fin s => V j.succ x) i
          ((cov (V i.succ) x) (X x)))).symm
    simp only [htail]
    rw [Fin.sum_univ_succ (f := fun a : Fin (s + 1) =>
      (show ContinuousMultilinearMap ℝ
          (fun _ : Fin (s + 1) => TangentSpace I x) ℝ from T x)
        (Function.update (fun b : Fin (s + 1) => V b x) a ((cov (V a) x) (X x))))]
    have hcons0 :
        Function.update (fun b : Fin (s + 1) => V b x) 0 ((cov (V 0) x) (X x)) =
          Fin.cons ((cov (V 0) x) (X x)) (fun i : Fin s => V i.succ x) := by
      funext j
      refine Fin.cases ?_ ?_ j
      · simp
      · intro i
        simp
    have hconsSucc : ∀ i : Fin s,
        Function.update (fun b : Fin (s + 1) => V b x) i.succ ((cov (V i.succ) x) (X x)) =
          Fin.cons (V 0 x)
            (Function.update (fun j : Fin s => V j.succ x) i ((cov (V i.succ) x) (X x))) := by
      intro i
      funext j
      refine Fin.cases ?_ ?_ j
      · simp [Function.update_of_ne (Fin.succ_ne_zero i).symm]
      · intro k
        rcases eq_or_ne k i with hk | hk
        · subst hk; simp
        · rw [Function.update_of_ne (by exact fun h => hk (Fin.succ_injective _ h)),
            Fin.cons_succ, Function.update_of_ne hk]
    simp only [hcons0, hconsSucc]
    ring

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem nabla0SFun_eq_tensor0SCovariantDerivative
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (α : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (x : M) :
    nabla0SFun (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) s
        (LeviCivita (I := I) g) X α x =
      Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)
        (fun y : M => α y) x (X x) := by
  classical
  apply ContinuousMultilinearMap.ext
  intro m
  choose V hVx using fun a : Fin s =>
    ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞)) (F := E)
      (V := (TangentSpace I : M → Type _)) x (m a)
  have hmV : (fun a : Fin s => V a x) = m := funext hVx
  rw [← hmV]
  rw [nabla0SFun_eval_smooth_slots (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      (s := s) (LeviCivita (I := I) g) X V α x]
  rw [abstractDerivEval_aux (I := I) (M := M) (LeviCivita (I := I) g) s
      (fun y : M => α y) (fun a => (V a : Π b : M, TangentSpace I b)) X
      α.contMDiff (fun a => (V a).contMDiff) X.contMDiff x]

end Connection
end Geometry
end DifferentialGeometry

end
