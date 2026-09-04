import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.Norm
import DifferentialGeometry.Geometry.Comparison.Variation.Covariant.CurvatureDerivative
import DifferentialGeometry.Geometry.Comparison.Variation.PerpendicularFrame.Basic
import DifferentialGeometry.Geometry.Comparison.Variation.Covariant.ChainRule
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Derivative.SmoothAlongExpansion
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Sections
import DifferentialGeometry.Geometry.Operator.Basic
import DifferentialGeometry.Geometry.Operator.Gradient.CotangentSharpSmoothness
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.FrozenSlot
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Smooth

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.RSTensor
open scoped Manifold ContDiff

namespace DifferentialGeometry
namespace HCGCompactness

universe u uE uH

variable {E : Type uE} [eAdd : NormedAddCommGroup E] [nE : NormedSpace Real E]
  [fdE : FiniteDimensional Real E] [CompleteSpace E]
  [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [boundarylessI : I.Boundaryless]

private theorem update_snoc_last
    {V : Type*} {n : Nat} (v : Fin n -> V) (w z : V) :
    Function.update (Fin.snoc v w : Fin (n + 1) -> V) (Fin.last n) z =
      (Fin.snoc v z : Fin (n + 1) -> V) := by
  funext i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · rw [Function.update_of_ne (Fin.castSucc_lt_last j).ne,
      Fin.snoc_castSucc, Fin.snoc_castSucc]
  · rw [Function.update_self, Fin.snoc_last]

private theorem update_snoc_castSucc
    {V : Type*} {n : Nat} (v : Fin n -> V) (w z : V) (i : Fin n) :
    Function.update (Fin.snoc v w : Fin (n + 1) -> V) i.castSucc z =
      (Fin.snoc (Function.update v i z) w : Fin (n + 1) -> V) := by
  funext j
  rcases Fin.eq_castSucc_or_eq_last j with ⟨a, rfl⟩ | rfl
  · rw [Fin.snoc_castSucc]
    rcases eq_or_ne a i with rfl | hai
    · rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne (fun h => hai (Fin.castSucc_injective _ h)),
        Function.update_of_ne hai, Fin.snoc_castSucc]
  · rw [Function.update_of_ne (Fin.castSucc_lt_last i).ne',
      Fin.snoc_last, Fin.snoc_last]

private theorem sum_erase_last
    {V : Type*} [AddCommGroup V] {n : Nat} (f : Fin (n + 1) -> V) :
    (∑ i ∈ Finset.univ.erase (Fin.last n), f i) =
      ∑ i : Fin n, f i.castSucc := by
  have h :=
    Finset.sum_erase_add Finset.univ f (Finset.mem_univ (Fin.last n))
  rw [Fin.sum_univ_castSucc] at h
  exact add_right_cancel h

section FixedMetric

variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] in
omit fdE in
private theorem snoc_section_apply
    {n : Nat}
    (Y : Fin n ->
      ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M -> Type _))
    (x : M) :
    (fun i : Fin (n + 1) =>
      (Fin.snoc
        (α := fun _ =>
          ContMDiffSection I E (∞ : WithTop ℕ∞)
            (TangentSpace I : M -> Type _)) Y 0) i x) =
      Fin.snoc (fun i : Fin n => Y i x) 0 := by
  funext i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
  · simp

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] in
private theorem oneForm_comp_smooth
    (beta : Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 1)
    (a : M) (j : Fin (Module.finrank Real E)) :
    ContMDiffOn I 𝓘(Real, Real) ∞
      (fun b : M =>
        beta b (fun _ : Fin 1 => DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) a j b))
      (chartAt H a).source := by
  intro x hx
  apply ContMDiffAt.contMDiffWithinAt
  have hEval :=
    TensorMultilinear.contMDiffAt_section_apply
      (I := I) (M := M) (n := 1)
      (T := fun b : M => beta b) (beta.contMDiff x)
      (fun _ : Fin 1 => fun b : M =>
        DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) a j b) (by
          intro i
          fin_cases i
          have hbase :
              (trivializationAt E (TangentSpace I) a).baseSet =
                (chartAt H a).source :=
            TangentBundle.trivializationAt_baseSet (I := I) a
          have hxbase :
              x ∈ (trivializationAt E (TangentSpace I) a).baseSet := by
            rw [hbase]
            exact hx
          exact
            (DifferentialGeometry.Tensor.Coordinates.chartBasisVec_contMDiffOn (I := I) a j x hxbase).contMDiffAt
              ((trivializationAt E (TangentSpace I) a).open_baseSet.mem_nhds
                hxbase))
  exact hEval

private noncomputable def curvLastCov
    (g : SmoothRiemannianMetric I M) (k : Nat) (x : M)
    (v : Fin (k + 3) -> TangentSpace I x) :
    Module.Dual Real (TangentSpace I x) where
  toFun := fun w =>
    curvCovDeriv (I := I) (M := M) g k x (Fin.snoc v w)
  map_add' := by
    intro w z
    let m : Fin (k + 4) -> TangentSpace I x := Fin.snoc v w
    have hmap :=
      (curvCovDeriv (I := I) (M := M) g k x).map_update_add
        m (Fin.last (k + 3)) w z
    simpa only [m, update_snoc_last] using hmap
  map_smul' := by
    intro c w
    let m : Fin (k + 4) -> TangentSpace I x := Fin.snoc v w
    have hmap :=
      (curvCovDeriv (I := I) (M := M) g k x).map_update_smul
        m (Fin.last (k + 3)) c w
    change curvCovDeriv (I := I) (M := M) g k x (Fin.snoc v (c • w)) =
      c • curvCovDeriv (I := I) (M := M) g k x (Fin.snoc v w)
    simpa only [m, update_snoc_last] using hmap

noncomputable def curvOpN
    (g : SmoothRiemannianMetric I M) (k : Nat) (x : M)
    (v : Fin (k + 3) -> TangentSpace I x) :
    TangentSpace I x :=
  DifferentialGeometry.Geometry.Operator.metricSharp (I := I) g x
    (curvLastCov (I := I) g k x v)

private noncomputable def curvOpNMap
    (g : SmoothRiemannianMetric I M) (k : Nat) (x : M) :
    MultilinearMap Real
      (fun _ : Fin (k + 3) => TangentSpace I x) (TangentSpace I x) where
  toFun := curvOpN (I := I) g k x
  map_update_add' := by
    intro dec v i y z
    let : DecidableEq (Fin (k + 3)) := dec
    have hlast :
        curvLastCov (I := I) g k x (Function.update v i (y + z)) =
          curvLastCov (I := I) g k x (Function.update v i y) +
            curvLastCov (I := I) g k x (Function.update v i z) := by
      ext w
      let m : Fin (k + 4) -> TangentSpace I x := Fin.snoc v w
      have hmap :=
        (curvCovDeriv (I := I) (M := M) g k x).map_update_add
          m i.castSucc y z
      have hupd (q : TangentSpace I x) :
          Function.update (Fin.snoc v w) i.castSucc q =
            (Fin.snoc
              (α := fun _ : Fin (k + 4) => TangentSpace I x)
              (Function.update v i q) w : Fin (k + 4) -> TangentSpace I x) := by
        funext j
        rcases Fin.eq_castSucc_or_eq_last j with ⟨a, rfl⟩ | rfl
        · rw [Fin.snoc_castSucc]
          by_cases hai : a = i
          · subst a
            rw [Function.update_self, Function.update_self]
          · rw [Function.update_of_ne
                (fun h => hai (Fin.castSucc_injective _ h)),
              Function.update_of_ne hai, Fin.snoc_castSucc]
        · rw [Function.update_of_ne (Fin.castSucc_lt_last i).ne',
            Fin.snoc_last, Fin.snoc_last]
      change
        curvCovDeriv (I := I) (M := M) g k x
            (Fin.snoc (Function.update v i (y + z)) w) =
          curvCovDeriv (I := I) (M := M) g k x
              (Fin.snoc (Function.update v i y) w) +
            curvCovDeriv (I := I) (M := M) g k x
              (Fin.snoc (Function.update v i z) w)
      simpa only [m, hupd] using hmap
    unfold curvOpN
    rw [hlast]
    exact map_add _ _ _
  map_update_smul' := by
    intro dec v i c y
    let : DecidableEq (Fin (k + 3)) := dec
    have hlast :
        curvLastCov (I := I) g k x (Function.update v i (c • y)) =
          c • curvLastCov (I := I) g k x (Function.update v i y) := by
      ext w
      let m : Fin (k + 4) -> TangentSpace I x := Fin.snoc v w
      have hmap :=
        (curvCovDeriv (I := I) (M := M) g k x).map_update_smul
          m i.castSucc c y
      have hupd (q : TangentSpace I x) :
          Function.update (Fin.snoc v w) i.castSucc q =
            (Fin.snoc
              (α := fun _ : Fin (k + 4) => TangentSpace I x)
              (Function.update v i q) w : Fin (k + 4) -> TangentSpace I x) := by
        funext j
        rcases Fin.eq_castSucc_or_eq_last j with ⟨a, rfl⟩ | rfl
        · rw [Fin.snoc_castSucc]
          by_cases hai : a = i
          · subst a
            rw [Function.update_self, Function.update_self]
          · rw [Function.update_of_ne
                (fun h => hai (Fin.castSucc_injective _ h)),
              Function.update_of_ne hai, Fin.snoc_castSucc]
        · rw [Function.update_of_ne (Fin.castSucc_lt_last i).ne',
            Fin.snoc_last, Fin.snoc_last]
      change
        curvCovDeriv (I := I) (M := M) g k x
            (Fin.snoc (Function.update v i (c • y)) w) =
          c • curvCovDeriv (I := I) (M := M) g k x
            (Fin.snoc (Function.update v i y) w)
      simpa only [m, hupd] using hmap
    unfold curvOpN
    rw [hlast]
    exact map_smul _ _ _

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
omit [CompleteSpace E] in
@[simp] private theorem curvOpNMap_apply
    (g : SmoothRiemannianMetric I M) (k : Nat) (x : M)
    (v : Fin (k + 3) -> TangentSpace I x) :
    curvOpNMap (I := I) g k x v = curvOpN (I := I) g k x v :=
  rfl

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
omit [CompleteSpace E] in
private theorem curvOpN_expand
    (g : SmoothRiemannianMetric I M) (k d : Nat) (x : M)
    (c : Fin (k + 3) -> Fin d -> Real)
    (v : Fin (k + 3) -> Fin d -> TangentSpace I x) :
    curvOpN (I := I) g k x (fun i => ∑ a, c i a • v i a) =
      ∑ r : Fin (k + 3) -> Fin d,
        (∏ i, c i (r i)) •
          curvOpN (I := I) g k x (fun i => v i (r i)) := by
  change
    curvOpNMap (I := I) g k x (fun i => ∑ a, c i a • v i a) = _
  rw [MultilinearMap.map_sum]
  apply Finset.sum_congr rfl
  intro r hr
  rw [MultilinearMap.map_smul_univ, curvOpNMap_apply]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
omit [CompleteSpace E] in
private theorem curvOpN_update_add
    (g : SmoothRiemannianMetric I M) (k : Nat) (x : M)
    (v : Fin (k + 3) -> TangentSpace I x) (i : Fin (k + 3))
    (y z : TangentSpace I x) :
    curvOpN (I := I) g k x (Function.update v i (y + z)) =
      curvOpN (I := I) g k x (Function.update v i y) +
        curvOpN (I := I) g k x (Function.update v i z) := by
  change curvOpNMap (I := I) g k x (Function.update v i (y + z)) = _
  rw [MultilinearMap.map_update_add, curvOpNMap_apply, curvOpNMap_apply]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
omit [CompleteSpace E] in
private theorem curvOpN_update_smul
    (g : SmoothRiemannianMetric I M) (k : Nat) (x : M)
    (v : Fin (k + 3) -> TangentSpace I x) (i : Fin (k + 3))
    (c : Real) (y : TangentSpace I x) :
    curvOpN (I := I) g k x (Function.update v i (c • y)) =
      c • curvOpN (I := I) g k x (Function.update v i y) := by
  change curvOpNMap (I := I) g k x (Function.update v i (c • y)) = _
  rw [MultilinearMap.map_update_smul, curvOpNMap_apply]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
omit [CompleteSpace E] in
theorem curvOpN_zero_at
    (g : SmoothRiemannianMetric I M) (k : Nat) (x : M)
    (v : Fin (k + 3) -> TangentSpace I x) (i : Fin (k + 3))
    (hi : v i = 0) :
    curvOpN (I := I) g k x v = 0 := by
  rw [← Function.update_eq_self i v, hi]
  simpa only [zero_smul] using
    curvOpN_update_smul (I := I) g k x v i (0 : Real)
      (0 : TangentSpace I x)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
omit [CompleteSpace E] in
theorem curvOpN_eq_sharp
    (g : SmoothRiemannianMetric I M) (k : Nat) (x : M)
    (v : Fin (k + 3) -> TangentSpace I x) :
    curvOpN (I := I) g k x v =
      Tensor0SBundle.cotangentSharpGen (I := I) g x
        (DifferentialGeometry.Tensor.RSTensor.oneFormAtSlot0S
          (I := I) (curvCovDeriv (I := I) (M := M) g k x)
          (Fin.snoc v 0) (Fin.last (k + 3))) := by
  rw [DifferentialGeometry.Geometry.Operator.cotangentSharp_gen_eq_metricSharp]
  unfold curvOpN
  congr 1
  ext w
  rw [Tensor0SBundle.cotangentToDual_apply_gen,
    DifferentialGeometry.Tensor.RSTensor.oneFormAtSlot0S_apply]
  exact congrArg (curvCovDeriv (I := I) (M := M) g k x)
    (update_snoc_last v 0 w).symm

noncomputable def curvOpNForm
    (g : SmoothRiemannianMetric I M) (k : Nat)
    (Y : Fin (k + 3) ->
      ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M -> Type _)) :
    Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 1 :=
  DifferentialGeometry.PDE.RicciFlow.freezeAllBut0SField
    (I := I) (M := M) (curvCovDeriv (I := I) (M := M) g k)
    (Fin.last (k + 3))
    (Fin.snoc
      (α := fun _ =>
        ContMDiffSection I E (∞ : WithTop ℕ∞)
          (TangentSpace I : M -> Type _)) Y 0)

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  [I.Boundaryless] [SigmaCompactSpace M] in
@[simp] theorem curvOpNForm_apply
    (g : SmoothRiemannianMetric I M) (k : Nat)
    (Y : Fin (k + 3) ->
      ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M -> Type _))
    (x : M) :
    curvOpNForm (I := I) g k Y x =
      DifferentialGeometry.Tensor.RSTensor.oneFormAtSlot0S
        (I := I) (curvCovDeriv (I := I) (M := M) g k x)
        (Fin.snoc (fun i => Y i x) 0) (Fin.last (k + 3)) := by
  unfold curvOpNForm
  rw [DifferentialGeometry.PDE.RicciFlow.freezeAllBut0SField_apply]
  rw [snoc_section_apply]

noncomputable def curvOpNField
    (g : SmoothRiemannianMetric I M) (k : Nat)
    (Y : Fin (k + 3) ->
      ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M -> Type _)) :
    ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _) := by
  exact ContMDiffSection.mk
    (fun x : M =>
      Tensor0SBundle.cotangentSharpGen (I := I) g x
        (curvOpNForm (I := I) g k Y x))
    (DifferentialGeometry.Geometry.Operator.cotangentSharp_gen_contMDiff_total
      (I := I) g (fun a j => by
        exact oneForm_comp_smooth
          (I := I) (curvOpNForm (I := I) g k Y) a j))

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  [SigmaCompactSpace M] in
omit boundarylessI in
@[simp] theorem curvOpNField_apply
    (g : SmoothRiemannianMetric I M) (k : Nat)
    (Y : Fin (k + 3) ->
      ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M -> Type _))
    (x : M) :
    curvOpNField (I := I) g k Y x =
      curvOpN (I := I) g k x (fun i => Y i x) := by
  rw [curvOpN_eq_sharp]
  change Tensor0SBundle.cotangentSharpGen (I := I) g x
      (curvOpNForm (I := I) g k Y x) = _
  rw [curvOpNForm_apply]

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  [SigmaCompactSpace M] in
omit boundarylessI in
theorem curvOpN_smoothAlong
    (g : SmoothRiemannianMetric I M) (k : Nat)
    (gamma : Real -> M)
    (Y : Fin (k + 3) -> forall s : Real, TangentSpace I (gamma s))
    (hgamma : ContMDiff 𝓘(Real, Real) I ∞ gamma)
    (hY : forall i, ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun s : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (gamma s) (Y i s) : TangentBundle I M))) :
    ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun s : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (gamma s)
          (curvOpN (I := I) g k (gamma s)
            (fun i => Y i s)) : TangentBundle I M)) := by
  classical
  intro t
  obtain ⟨B, hBsm, hBnear⟩ :=
    exists_smooth_chartBasisExtension (I := I) (gamma t)
  choose c hcsm hcval hcexp using fun i : Fin (k + 3) =>
    exists_frame_exp (I := I) gamma (Y i) t hgamma (hY i) B hBnear
  let Bsec : Fin (Module.finrank Real E) ->
      ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M -> Type _) :=
    fun a => ContMDiffSection.mk (B a) (hBsm a)
  have hbase (r : Fin (k + 3) -> Fin (Module.finrank Real E)) :
      ContMDiff 𝓘(Real, Real) I.tangent ∞
        (fun s : Real =>
          (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
            (gamma s)
            (curvOpN (I := I) g k (gamma s)
              (fun i => B (r i) (gamma s))) : TangentBundle I M)) := by
    change ContMDiff 𝓘(Real, Real) (I.prod 𝓘(Real, E)) ∞
      (fun s : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (gamma s)
          (curvOpN (I := I) g k (gamma s)
            (fun i => B (r i) (gamma s))) : TangentBundle I M))
    refine ContMDiff.congr
      ((curvOpNField (I := I) g k (fun i => Bsec (r i))).contMDiff.comp hgamma) ?_
    intro s
    apply TotalSpace.ext
    · rfl
    · exact heq_of_eq
        (curvOpNField_apply (I := I) g k (fun i => Bsec (r i)) (gamma s)).symm
  have hcoeff (r : Fin (k + 3) -> Fin (Module.finrank Real E)) :
      ContMDiff 𝓘(Real, Real) 𝓘(Real, Real) ∞
        (fun s : Real => ∏ i, c i (r i) s) := by
    exact ContMDiff.prod (t := Finset.univ) fun i _ => hcsm i (r i)
  have hterm (r : Fin (k + 3) -> Fin (Module.finrank Real E)) :
      ContMDiff 𝓘(Real, Real) I.tangent ∞
        (fun s : Real =>
          (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
            (gamma s)
            ((∏ i, c i (r i) s) •
              curvOpN (I := I) g k (gamma s)
                (fun i => B (r i) (gamma s))) : TangentBundle I M)) :=
    contMDiff_smul_bundleField_perp (I := I) hgamma (hcoeff r) (hbase r)
  have hsum :
      ContMDiff 𝓘(Real, Real) I.tangent ∞
        (fun s : Real =>
          (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
            (gamma s)
            (∑ r : Fin (k + 3) -> Fin (Module.finrank Real E),
              (∏ i, c i (r i) s) •
                curvOpN (I := I) g k (gamma s)
                  (fun i => B (r i) (gamma s))) : TangentBundle I M)) := by
    simpa using
      (contMDiff_sum_along (I := I)
        (Finset.univ :
          Finset (Fin (k + 3) -> Fin (Module.finrank Real E)))
        gamma
        (fun r s =>
          (∏ i, c i (r i) s) •
            curvOpN (I := I) g k (gamma s)
              (fun i => B (r i) (gamma s)))
        hgamma (fun r _ => hterm r))
  have hYexp :
      ∀ᶠ s in nhds t, forall i,
        Y i s = ∑ a, c i a s • B a (gamma s) :=
    Filter.eventually_all.mpr hcexp
  have heq :
      (fun s : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (gamma s)
          (curvOpN (I := I) g k (gamma s)
            (fun i => Y i s)) : TangentBundle I M)) =ᶠ[nhds t]
      (fun s : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (gamma s)
          (∑ r : Fin (k + 3) -> Fin (Module.finrank Real E),
            (∏ i, c i (r i) s) •
              curvOpN (I := I) g k (gamma s)
                (fun i => B (r i) (gamma s))) : TangentBundle I M)) := by
    filter_upwards [hYexp] with s hs
    congr 1
    rw [show (fun i => Y i s) =
        fun i => ∑ a, c i a s • B a (gamma s) by
      funext i
      exact hs i]
    exact curvOpN_expand (I := I) g k (Module.finrank Real E) (gamma s)
      (fun i a => c i a s) (fun i a => B a (gamma s))
  exact (hsum t).congr_of_eventuallyEq heq

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] in
omit fdE in
private theorem smooth_update_along
    (k : Nat) (gamma : Real -> M)
    (Y : Fin (k + 3) -> forall s : Real, TangentSpace I (gamma s))
    (i : Fin (k + 3))
    (V : forall s : Real, TangentSpace I (gamma s))
    (hY : forall j, ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun s : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (gamma s) (Y j s) : TangentBundle I M)))
    (hV : ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun s : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (gamma s) (V s) : TangentBundle I M))) :
    forall j, ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun s : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (gamma s) ((Function.update Y i V) j s) :
            TangentBundle I M)) := by
  classical
  intro j
  by_cases hji : j = i
  · subst j
    simpa only [Function.update_self] using hV
  · simpa only [Function.update_of_ne hji] using hY j

private noncomputable def curvOpNablaForm
    (g : SmoothRiemannianMetric I M) (k : Nat)
    (Y : Fin (k + 3) ->
      ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M -> Type _)) :
    Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2 :=
  Tensor0SBundle.totalNabla0S (𝕜 := Real) (E := E) (H := H)
    (I := I) (M := M) 1
    (DifferentialGeometry.Geometry.Curvature.metricCov (I := I) (M := M) g)
    (curvOpNForm (I := I) g k Y)
    (Tensor0SBundle.totalNabla0S_reg (E := E) (H := H)
      (I := I) (M := M) 1
      (DifferentialGeometry.Geometry.Curvature.metricCov (I := I) (M := M) g)
      (DifferentialGeometry.Geometry.Curvature.metricCov_smooth
        (I := I) (M := M) g)
      (curvOpNForm (I := I) g k Y))

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
private theorem curvOpNabla_real
    (g : SmoothRiemannianMetric I M) (k : Nat)
    (Y : Fin (k + 3) ->
      ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M -> Type _)) :
    Tensor0SBundle.TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 1
      (DifferentialGeometry.Geometry.Curvature.metricCov (I := I) (M := M) g)
      (curvOpNForm (I := I) g k Y)
      (curvOpNablaForm (I := I) g k Y) := by
  simpa [curvOpNablaForm] using
    (Tensor0SBundle.totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 1
      (DifferentialGeometry.Geometry.Curvature.metricCov (I := I) (M := M) g)
      (curvOpNForm (I := I) g k Y)
      (Tensor0SBundle.totalNabla0S_reg (E := E) (H := H)
        (I := I) (M := M) 1
        (DifferentialGeometry.Geometry.Curvature.metricCov (I := I) (M := M) g)
        (DifferentialGeometry.Geometry.Curvature.metricCov_smooth
          (I := I) (M := M) g)
        (curvOpNForm (I := I) g k Y)))

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] in
private theorem curvOpNabla_eval_raw
    (g : SmoothRiemannianMetric I M) (k : Nat)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (Y : Fin (k + 3) ->
      ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M -> Type _))
    (x : M) (U : TangentSpace I x) :
    curvOpNablaForm (I := I) g k Y x
        (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) (X x) U) =
      curvCovDeriv (I := I) (M := M) g (k + 1) x
          (Fin.cons (X x)
            (Function.update
              (Fin.snoc (fun i : Fin (k + 3) => Y i x) 0)
              (Fin.last (k + 3)) U)) +
        ∑ i ∈ Finset.univ.erase (Fin.last (k + 3)),
          curvCovDeriv (I := I) (M := M) g k x
            (Function.update
              (Function.update
                (Fin.snoc (fun j : Fin (k + 3) => Y j x) 0)
                (Fin.last (k + 3)) U) i
              (((DifferentialGeometry.Geometry.Curvature.metricCov
                (I := I) (M := M) g)
                (fun p : M =>
                  (Fin.snoc
                    (α := fun _ =>
                      ContMDiffSection I E (∞ : WithTop ℕ∞)
                        (TangentSpace I : M -> Type _)) Y 0) i p) x) (X x))) := by
  let cov :=
    DifferentialGeometry.Geometry.Curvature.metricCov (I := I) (M := M) g
  let Yfull : Fin (k + 4) ->
      ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M -> Type _) :=
    Fin.snoc
      (α := fun _ =>
        ContMDiffSection I E (∞ : WithTop ℕ∞)
          (TangentSpace I : M -> Type _)) Y 0
  have hBval :
      curvOpNablaForm (I := I) g k Y x
          (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) (X x) U) =
        Tensor0SBundle.totalNabla0SFun (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) 1 cov
          (curvOpNForm (I := I) g k Y) x
          (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) (X x) U) := rfl
  have hAval :
      curvCovDeriv (I := I) (M := M) g (k + 1) x
          (Fin.cons (X x)
            (Function.update (fun i : Fin (k + 4) => Yfull i x)
              (Fin.last (k + 3)) U)) =
        Tensor0SBundle.totalNabla0SFun (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) (k + 4) cov
          (curvCovDeriv (I := I) (M := M) g k) x
          (Fin.cons (X x)
            (Function.update (fun i : Fin (k + 4) => Yfull i x)
              (Fin.last (k + 3)) U)) := rfl
  have hYfull_apply :
      (fun i : Fin (k + 4) => Yfull i x) =
        Fin.snoc (fun i : Fin (k + 3) => Y i x) 0 := by
    simpa [Yfull] using snoc_section_apply (I := I) Y x
  rw [← hYfull_apply]
  rw [hBval, hAval]
  simpa [cov, curvOpNForm, Yfull, snoc_section_apply] using
    (DifferentialGeometry.PDE.RicciFlow.freezeNabla_leibniz
      (I := I) cov
      (curvCovDeriv (I := I) (M := M) g k) (Fin.last (k + 3))
      X Yfull U)

private noncomputable def curvSlotCov
    (g : SmoothRiemannianMetric I M) (k : Nat)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (Y : Fin (k + 3) ->
      ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M -> Type _))
    (x : M) (i : Fin (k + 3)) :
    TangentSpace I x :=
  ((DifferentialGeometry.Geometry.Curvature.metricCov
    (I := I) (M := M) g) (fun p : M => Y i p) x) (X x)

private noncomputable def curvNextForm
    (g : SmoothRiemannianMetric I M) (k : Nat)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (Y : Fin (k + 3) ->
      ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M -> Type _))
    (x : M) :
    Tensor0SSpace 1 I x :=
  DifferentialGeometry.Tensor.RSTensor.oneFormAtSlot0S
    (I := I) (curvCovDeriv (I := I) (M := M) g (k + 1) x)
    (Fin.snoc (Fin.cons (X x) (fun i : Fin (k + 3) => Y i x)) 0)
    (Fin.last ((k + 1) + 3))

private noncomputable def curvCorrForm
    (g : SmoothRiemannianMetric I M) (k : Nat)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (Y : Fin (k + 3) ->
      ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M -> Type _))
    (x : M) (i : Fin (k + 3)) :
    Tensor0SSpace 1 I x :=
  DifferentialGeometry.Tensor.RSTensor.oneFormAtSlot0S
    (I := I) (curvCovDeriv (I := I) (M := M) g k x)
    (Fin.snoc
      (Function.update (fun j : Fin (k + 3) => Y j x) i
        (curvSlotCov (I := I) g k X Y x i)) 0)
    (Fin.last (k + 3))

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] in
private theorem curvOpNabla_eval_sum
    (g : SmoothRiemannianMetric I M) (k : Nat)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (Y : Fin (k + 3) ->
      ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M -> Type _))
    (x : M) (U : TangentSpace I x) :
    curvOpNablaForm (I := I) g k Y x
        (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) (X x) U) =
      curvCovDeriv (I := I) (M := M) g (k + 1) x
          (Fin.cons (X x) (Fin.snoc (fun i : Fin (k + 3) => Y i x) U)) +
        ∑ i : Fin (k + 3),
          curvCovDeriv (I := I) (M := M) g k x
            (Fin.snoc
              (Function.update (fun j : Fin (k + 3) => Y j x) i
                (curvSlotCov (I := I) g k X Y x i))
              U) := by
  rw [curvOpNabla_eval_raw (I := I) g k X Y x U]
  rw [update_snoc_last]
  congr 1
  rw [sum_erase_last]
  apply Finset.sum_congr rfl
  intro i hi
  rw [update_snoc_castSucc]
  have hsec :
      (fun p : M =>
        (Fin.snoc
          (α := fun _ =>
            ContMDiffSection I E (∞ : WithTop ℕ∞)
              (TangentSpace I : M -> Type _)) Y 0) i.castSucc p) =
        fun p : M => Y i p := by
    funext p
    rw [Fin.snoc_castSucc]
  rw [hsec]
  change
    curvCovDeriv (I := I) (M := M) g k x
        (Fin.snoc
          (Function.update (fun j : Fin (k + 3) => Y j x) i
            (curvSlotCov (I := I) g k X Y x i)) U) =
      _
  rfl

omit [NeZero (Module.finrank ℝ E)] boundarylessI
  [SigmaCompactSpace M] in
private theorem curvOpNabla_curry
    (g : SmoothRiemannianMetric I M) (k : Nat)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (Y : Fin (k + 3) ->
      ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M -> Type _))
    (x : M) :
    Tensor0SBundle.tensor0SCurry (I := I) (𝕜 := Real) (M := M) 1 x
        (curvOpNablaForm (I := I) g k Y x) (X x) =
      curvNextForm (I := I) g k X Y x +
        ∑ i : Fin (k + 3), curvCorrForm (I := I) g k X Y x i := by
  classical
  apply ContinuousMultilinearMap.ext
  intro slots
  have hslots :
      Fin.cons (X x) slots =
        DifferentialGeometry.Geometry.Curvature.vec2
          (I := I) (X x) (slots 0) := by
    funext i
    fin_cases i <;> rfl
  have hslots_one : slots = fun _ : Fin 1 => slots 0 := by
    funext i
    fin_cases i
    rfl
  calc
    (Tensor0SBundle.tensor0SCurry (I := I) (𝕜 := Real) (M := M) 1 x
        (curvOpNablaForm (I := I) g k Y x) (X x)) slots =
        curvOpNablaForm (I := I) g k Y x (Fin.cons (X x) slots) :=
      Tensor0SBundle.tensor0S_curry_apply_cons (I := I) 1
        (curvOpNablaForm (I := I) g k Y x) (X x) slots
    _ = curvOpNablaForm (I := I) g k Y x
        (DifferentialGeometry.Geometry.Curvature.vec2
          (I := I) (X x) (slots 0)) := by
      rw [hslots]
    _ = curvCovDeriv (I := I) (M := M) g (k + 1) x
          (Fin.cons (X x)
            (Fin.snoc (fun i : Fin (k + 3) => Y i x) (slots 0))) +
        ∑ i : Fin (k + 3),
          curvCovDeriv (I := I) (M := M) g k x
            (Fin.snoc
              (Function.update (fun j : Fin (k + 3) => Y j x) i
                (curvSlotCov (I := I) g k X Y x i))
              (slots 0)) :=
      curvOpNabla_eval_sum (I := I) g k X Y x (slots 0)
    _ = curvNextForm (I := I) g k X Y x slots +
        ∑ i : Fin (k + 3), curvCorrForm (I := I) g k X Y x i slots := by
      congr 1
      · rw [curvNextForm, hslots_one]
        rw [DifferentialGeometry.Tensor.RSTensor.oneFormAtSlot0S_apply]
        rw [update_snoc_last, Fin.cons_snoc_eq_snoc_cons]
      · apply Finset.sum_congr rfl
        intro i hi
        rw [curvCorrForm, hslots_one]
        rw [DifferentialGeometry.Tensor.RSTensor.oneFormAtSlot0S_apply]
        rw [update_snoc_last]
    _ = (curvNextForm (I := I) g k X Y x +
        ∑ i : Fin (k + 3), curvCorrForm (I := I) g k X Y x i) slots := by
      simp

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] in
private theorem curvOpNabla_eval
    (g : SmoothRiemannianMetric I M) (k : Nat)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (Y : Fin (k + 3) ->
      ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M -> Type _))
    (x : M)
    (hYzero : ∀ i : Fin (k + 3),
      ((DifferentialGeometry.Geometry.Curvature.metricCov
        (I := I) (M := M) g (fun p : M => Y i p) x) (X x)) = 0)
    (U : TangentSpace I x) :
    curvOpNablaForm (I := I) g k Y x
        (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) (X x) U) =
      curvCovDeriv (I := I) (M := M) g (k + 1) x
        (Fin.cons (X x)
          (Function.update
            (Fin.snoc (fun i : Fin (k + 3) => Y i x) 0)
            (Fin.last (k + 3)) U)) := by
  let cov :=
    DifferentialGeometry.Geometry.Curvature.metricCov (I := I) (M := M) g
  let Yfull : Fin (k + 4) ->
      ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M -> Type _) :=
    Fin.snoc
      (α := fun _ =>
        ContMDiffSection I E (∞ : WithTop ℕ∞)
          (TangentSpace I : M -> Type _)) Y 0
  have hYfull : ∀ i : Fin (k + 4), i ≠ Fin.last (k + 3) ->
      ((cov (fun p : M => Yfull i p) x) (X x)) = 0 := by
    intro i hi
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · simpa [Yfull] using hYzero j
    · exact (hi rfl).elim
  have hBval :
      curvOpNablaForm (I := I) g k Y x
          (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) (X x) U) =
        Tensor0SBundle.totalNabla0SFun (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) 1 cov
          (curvOpNForm (I := I) g k Y) x
          (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) (X x) U) := rfl
  have hAval :
      curvCovDeriv (I := I) (M := M) g (k + 1) x
          (Fin.cons (X x)
            (Function.update (fun i : Fin (k + 4) => Yfull i x)
              (Fin.last (k + 3)) U)) =
        Tensor0SBundle.totalNabla0SFun (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) (k + 4) cov
          (curvCovDeriv (I := I) (M := M) g k) x
          (Fin.cons (X x)
            (Function.update (fun i : Fin (k + 4) => Yfull i x)
              (Fin.last (k + 3)) U)) := rfl
  have hYfull_apply :
      (fun i : Fin (k + 4) => Yfull i x) =
        Fin.snoc (fun i : Fin (k + 3) => Y i x) 0 := by
    simpa [Yfull] using snoc_section_apply (I := I) Y x
  rw [← hYfull_apply]
  rw [hBval, hAval]
  simpa [cov, curvOpNForm, Yfull, snoc_section_apply] using
    (DifferentialGeometry.PDE.RicciFlow.allBut0SFreezeNabla
      (I := I) cov
      (curvCovDeriv (I := I) (M := M) g k) (Fin.last (k + 3))
      X Yfull hYfull U)

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
omit boundarylessI in
theorem curvOpN_cov_sum
    (g : SmoothRiemannianMetric I M) (k : Nat)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (Y : Fin (k + 3) ->
      ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M -> Type _))
    (x : M) :
    (DifferentialGeometry.Geometry.Curvature.metricCov
        (I := I) (M := M) g
        (fun p : M => curvOpNField (I := I) g k Y p) x) (X x) =
      curvOpN (I := I) g (k + 1) x
          (Fin.cons (X x) (fun i : Fin (k + 3) => Y i x)) +
        ∑ i : Fin (k + 3),
          curvOpN (I := I) g k x
            (Function.update (fun j : Fin (k + 3) => Y j x) i
              (((DifferentialGeometry.Geometry.Curvature.metricCov
                (I := I) (M := M) g)
                (fun p : M => Y i p) x) (X x))) := by
  classical
  let cov :=
    DifferentialGeometry.Geometry.Curvature.metricCov (I := I) (M := M) g
  have hmc :
      DifferentialGeometry.Geometry.Connection.IsMetricCompatibleGen
        (I := I) cov g := by
    change DifferentialGeometry.Geometry.Connection.IsMetricCompatibleGen
      (I := I)
      (DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric (I := I) g) g
    exact DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric_isMetricCompatible
      (I := I) g
  have hSharp :
      MDiffAt
        (T% (fun p : M =>
          Tensor0SBundle.cotangentSharpGen (I := I) g p
            (curvOpNForm (I := I) g k Y p))) x := by
    change MDiffAt (T% (fun p : M => curvOpNField (I := I) g k Y p)) x
    exact
      (curvOpNField (I := I) g k Y).contMDiff.contMDiffAt.mdifferentiableAt
        (by simp)
  have hcov :=
    Tensor0SBundle.cotangentSharp_cov_eq_sharp_curry_of_mdiffAt
      (I := I) cov g hmc
      (curvOpNForm (I := I) g k Y)
      (curvOpNablaForm (I := I) g k Y)
      (curvOpNabla_real (I := I) g k Y) X x hSharp
  change
    cov
        (fun p : M =>
          Tensor0SBundle.cotangentSharpGen (I := I) g p
            (curvOpNForm (I := I) g k Y p))
        x (X x) =
      curvOpN (I := I) g (k + 1) x
          (Fin.cons (X x) (fun i : Fin (k + 3) => Y i x)) +
        ∑ i : Fin (k + 3),
          curvOpN (I := I) g k x
            (Function.update (fun j : Fin (k + 3) => Y j x) i
              (curvSlotCov (I := I) g k X Y x i))
  rw [hcov, curvOpNabla_curry (I := I) g k X Y x]
  change
    Tensor0SBundle.cotangentSharpLinearGen (I := I) g x
        (curvNextForm (I := I) g k X Y x +
          ∑ i : Fin (k + 3), curvCorrForm (I := I) g k X Y x i) =
      _
  rw [map_add, map_sum]
  congr 1
  · simpa [curvNextForm] using
      (curvOpN_eq_sharp (I := I) g (k + 1) x
        (Fin.cons (X x) (fun i : Fin (k + 3) => Y i x))).symm
  · apply Finset.sum_congr rfl
    intro i hi
    simpa [curvCorrForm] using
      (curvOpN_eq_sharp (I := I) g k x
        (Function.update (fun j : Fin (k + 3) => Y j x) i
          (curvSlotCov (I := I) g k X Y x i))).symm

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem curvOpN_cov_restrict
    (g : SmoothRiemannianMetric I M) (k : Nat)
    (γ : Real -> M)
    (Y : Fin (k + 3) ->
      ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M -> Type _))
    (t : Real)
    (hγ : ContMDiff 𝓘(Real, Real) I ∞ γ) :
    let v : TangentSpace I (γ t) :=
      (mfderiv 𝓘(Real, Real) I γ t : Real →L[Real] _) (1 : Real)
    covDerivAlong (I := I) g γ
        (fun s : Real => curvOpNField (I := I) g k Y (γ s)) t =
      curvOpN (I := I) g (k + 1) (γ t)
          (Fin.cons v (fun i : Fin (k + 3) => Y i (γ t))) +
        ∑ i : Fin (k + 3),
          curvOpN (I := I) g k (γ t)
            (Function.update (fun j : Fin (k + 3) => Y j (γ t)) i
              (covDerivAlong (I := I) g γ
                (fun s : Real => Y i (γ s)) t)) := by
  classical
  dsimp only
  let v : TangentSpace I (γ t) :=
    (mfderiv 𝓘(Real, Real) I γ t : Real →L[Real] _) (1 : Real)
  let X : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _) :=
    ContMDiffSection.mk
      (smoothExtensionTangent (I := I) (γ t) v)
      (smoothExtensionTangent_contMDiff (I := I) (γ t) v)
  have hX : X (γ t) = v :=
    smoothExtensionTangent_eq (I := I) (γ t) v
  have hleft :
      covDerivAlong (I := I) g γ
          (fun s : Real => curvOpNField (I := I) g k Y (γ s)) t =
        (DifferentialGeometry.Geometry.Curvature.metricCov
          (I := I) (M := M) g
          (fun p : M => curvOpNField (I := I) g k Y p) (γ t)) v := by
    simpa only [DifferentialGeometry.Geometry.Connection.LeviCivita,
      DifferentialGeometry.Geometry.Curvature.metricCov] using
      covDerivAlong_restrict_eq_leviCivita (I := I) g γ
          (fun p : M => curvOpNField (I := I) g k Y p) t hγ
          (((curvOpNField (I := I) g k Y).contMDiff
            (γ t)).mdifferentiableAt (by simp))
  have hslot : ∀ i : Fin (k + 3),
      covDerivAlong (I := I) g γ (fun s : Real => Y i (γ s)) t =
        (DifferentialGeometry.Geometry.Curvature.metricCov
          (I := I) (M := M) g (fun p : M => Y i p) (γ t)) v := by
    intro i
    simpa only [DifferentialGeometry.Geometry.Connection.LeviCivita,
      DifferentialGeometry.Geometry.Curvature.metricCov] using
      covDerivAlong_restrict_eq_leviCivita
          (I := I) g γ (fun p : M => Y i p) t hγ
          (((Y i).contMDiff (γ t)).mdifferentiableAt (by simp))
  rw [hleft]
  have hmain := curvOpN_cov_sum (I := I) g k X Y (γ t)
  rw [hX] at hmain
  rw [hmain]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [hslot i]

noncomputable def curvOpNDerivAlong
    (g : SmoothRiemannianMetric I M) (k : Nat)
    (γ : Real -> M)
    (Y : Fin (k + 3) -> ∀ s : Real, TangentSpace I (γ s))
    (t : Real) : TangentSpace I (γ t) :=
  covDerivAlong (I := I) g γ
      (fun s : Real => curvOpN (I := I) g k (γ s)
        (fun i : Fin (k + 3) => Y i s)) t -
    ∑ i : Fin (k + 3),
      curvOpN (I := I) g k (γ t)
        (Function.update (fun j : Fin (k + 3) => Y j t) i
          (covDerivAlong (I := I) g γ (Y i) t))

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
omit [CompleteSpace E] in
private theorem curvOpNDeriv_congr
    (g : SmoothRiemannianMetric I M) (k : Nat)
    (gamma : Real -> M)
    (Y Z : Fin (k + 3) -> forall s : Real, TangentSpace I (gamma s))
    (t : Real)
    (h : forall i, Y i =ᶠ[nhds t] Z i) :
    curvOpNDerivAlong (I := I) g k gamma Y t =
      curvOpNDerivAlong (I := I) g k gamma Z t := by
  classical
  have hall :
      ∀ᶠ s in nhds t, forall i, Y i s = Z i s :=
    Filter.eventually_all.mpr h
  have heval :
      (fun s : Real =>
        curvOpN (I := I) g k (gamma s) (fun i => Y i s)) =ᶠ[nhds t]
      (fun s : Real =>
        curvOpN (I := I) g k (gamma s) (fun i => Z i s)) := by
    filter_upwards [hall] with s hs
    congr 1
    funext i
    exact hs i
  have hlead :
      covDerivAlong (I := I) g gamma
          (fun s : Real =>
            curvOpN (I := I) g k (gamma s) (fun i => Y i s)) t =
        covDerivAlong (I := I) g gamma
          (fun s : Real =>
            curvOpN (I := I) g k (gamma s) (fun i => Z i s)) t :=
    covDerivAlong_congr_of_eventuallyEq (I := I) g gamma heval
  have hval (i : Fin (k + 3)) : Y i t = Z i t :=
    (h i).self_of_nhds
  have hslot (i : Fin (k + 3)) :
      covDerivAlong (I := I) g gamma (Y i) t =
        covDerivAlong (I := I) g gamma (Z i) t :=
    covDerivAlong_congr_of_eventuallyEq (I := I) g gamma (h i)
  unfold curvOpNDerivAlong
  rw [hlead]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  funext j
  by_cases hji : j = i
  · subst j
    simp only [Function.update_self, hslot]
  · rw [Function.update_of_ne hji, Function.update_of_ne hji, hval j]

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  [SigmaCompactSpace M] in
private theorem curvOpNDeriv_smul
    (g : SmoothRiemannianMetric I M) (k : Nat)
    (gamma : Real -> M)
    (Y : Fin (k + 3) -> forall s : Real, TangentSpace I (gamma s))
    (i : Fin (k + 3)) (f : Real -> Real) (t : Real)
    (hgamma : ContMDiff 𝓘(Real, Real) I ∞ gamma)
    (hY : forall j, ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun s : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (gamma s) (Y j s) : TangentBundle I M)))
    (hf : DifferentiableAt Real f t) :
    curvOpNDerivAlong (I := I) g k gamma
        (Function.update Y i (fun s => f s • Y i s)) t =
      f t • curvOpNDerivAlong (I := I) g k gamma Y t := by
  rcases boundarylessI with ⟨hI⟩
  let : I.Boundaryless := ⟨hI⟩
  classical
  let Yf : Fin (k + 3) -> forall s : Real, TangentSpace I (gamma s) :=
    Function.update Y i (fun s => f s • Y i s)
  let v : Fin (k + 3) -> TangentSpace I (gamma t) := fun j => Y j t
  let dY : Fin (k + 3) -> TangentSpace I (gamma t) :=
    fun j => covDerivAlong (I := I) g gamma (Y j) t
  have hYf_val (s : Real) :
      (fun j => Yf j s) =
        Function.update (fun j => Y j s) i (f s • Y i s) := by
    funext j
    by_cases hji : j = i
    · subst j
      simp only [Yf, Function.update_self]
    · simp only [Yf, Function.update_of_ne hji]
  have heval :
      (fun s : Real =>
        curvOpN (I := I) g k (gamma s) (fun j => Yf j s)) =
        fun s : Real =>
          f s • curvOpN (I := I) g k (gamma s) (fun j => Y j s) := by
    funext s
    rw [hYf_val]
    rw [curvOpN_update_smul]
    rw [Function.update_eq_self]
  have hEvalSmooth :=
    curvOpN_smoothAlong (I := I) g k gamma Y hgamma hY
  have hEvalDiff :
      DifferentiableAt Real
        (chartRepAt (I := I) gamma
          (fun s : Real =>
            curvOpN (I := I) g k (gamma s) (fun j => Y j s)) t) t :=
    chartRep_diff (I := I) gamma
      (fun s : Real =>
        curvOpN (I := I) g k (gamma s) (fun j => Y j s))
      hEvalSmooth t
  have hYdiff (j : Fin (k + 3)) :
      DifferentiableAt Real (chartRepAt (I := I) gamma (Y j) t) t :=
    chartRep_diff (I := I) gamma (Y j) (hY j) t
  have hDYf :
      covDerivAlong (I := I) g gamma (Yf i) t =
        (deriv f t) • Y i t + f t • dY i := by
    have hYfi : Yf i = fun s => f s • Y i s := by
      simp only [Yf, Function.update_self]
    rw [hYfi]
    simpa only [dY] using
      covDerivAlong_smulFun (I := I) g gamma f (Y i) t hf (hYdiff i)
  have hcorr_i :
      curvOpN (I := I) g k (gamma t)
          (Function.update (fun j => Yf j t) i
            (covDerivAlong (I := I) g gamma (Yf i) t)) =
        (deriv f t) • curvOpN (I := I) g k (gamma t) v +
          f t • curvOpN (I := I) g k (gamma t)
            (Function.update v i (dY i)) := by
    rw [hYf_val, hDYf]
    simp only [Function.update_idem]
    rw [curvOpN_update_add, curvOpN_update_smul, curvOpN_update_smul]
    simp only [v, Function.update_eq_self]
  have hcorr_ne (j : Fin (k + 3)) (hji : j ≠ i) :
      curvOpN (I := I) g k (gamma t)
          (Function.update (fun q => Yf q t) j
            (covDerivAlong (I := I) g gamma (Yf j) t)) =
        f t • curvOpN (I := I) g k (gamma t)
          (Function.update v j (dY j)) := by
    have hslot :
        covDerivAlong (I := I) g gamma (Yf j) t = dY j := by
      have hYfj : Yf j = Y j := by
        simp only [Yf, Function.update_of_ne hji]
      rw [hYfj]
    rw [hYf_val, hslot]
    rw [Function.update_comm hji.symm]
    rw [curvOpN_update_smul]
    have hbase :
        Function.update (Function.update v j (dY j)) i (v i) =
          Function.update v j (dY j) := by
      have hvi : Function.update v j (dY j) i = v i :=
        Function.update_of_ne hji.symm _ _
      rw [← hvi, Function.update_eq_self]
    rw [hbase]
  let corrF : Fin (k + 3) -> TangentSpace I (gamma t) := fun j =>
    curvOpN (I := I) g k (gamma t)
      (Function.update (fun q => Yf q t) j
        (covDerivAlong (I := I) g gamma (Yf j) t))
  let corr : Fin (k + 3) -> TangentSpace I (gamma t) := fun j =>
    curvOpN (I := I) g k (gamma t)
      (Function.update v j (dY j))
  have herase :
      (∑ j ∈ Finset.univ.erase i, corrF j) =
        f t • ∑ j ∈ Finset.univ.erase i, corr j := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    exact hcorr_ne j (Finset.mem_erase.mp hj).1
  have hfull :
      (∑ j ∈ Finset.univ.erase i, corr j) + corr i =
        ∑ j : Fin (k + 3), corr j :=
    Finset.sum_erase_add Finset.univ corr (Finset.mem_univ i)
  have hsumcorr :
      (∑ j : Fin (k + 3), corrF j) =
        (deriv f t) • curvOpN (I := I) g k (gamma t) v +
          f t • ∑ j : Fin (k + 3), corr j := by
    calc
      (∑ j : Fin (k + 3), corrF j) =
          (∑ j ∈ Finset.univ.erase i, corrF j) + corrF i :=
        (Finset.sum_erase_add Finset.univ corrF (Finset.mem_univ i)).symm
      _ = f t • (∑ j ∈ Finset.univ.erase i, corr j) +
          ((deriv f t) • curvOpN (I := I) g k (gamma t) v +
            f t • corr i) := by
        rw [herase]
        exact congrArg
          (fun z => f t • (∑ j ∈ Finset.univ.erase i, corr j) + z)
          (by simpa only [corrF, corr] using hcorr_i)
      _ = (deriv f t) • curvOpN (I := I) g k (gamma t) v +
          f t • ∑ j : Fin (k + 3), corr j := by
        rw [← hfull]
        module
  change curvOpNDerivAlong (I := I) g k gamma Yf t =
    f t • curvOpNDerivAlong (I := I) g k gamma Y t
  unfold curvOpNDerivAlong
  rw [heval]
  rw [covDerivAlong_smulFun (I := I) g gamma f
    (fun s : Real =>
      curvOpN (I := I) g k (gamma s) (fun j => Y j s)) t hf hEvalDiff]
  change
    (deriv f t) • curvOpN (I := I) g k (gamma t) v +
        f t • covDerivAlong (I := I) g gamma
          (fun s : Real =>
            curvOpN (I := I) g k (gamma s) (fun j => Y j s)) t -
      ∑ j : Fin (k + 3), corrF j =
    f t •
      (covDerivAlong (I := I) g gamma
          (fun s : Real =>
            curvOpN (I := I) g k (gamma s) (fun j => Y j s)) t -
        ∑ j : Fin (k + 3), corr j)
  rw [hsumcorr]
  module

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  [SigmaCompactSpace M] in
private theorem curvOpNDeriv_add
    (g : SmoothRiemannianMetric I M) (k : Nat)
    (gamma : Real -> M)
    (Y : Fin (k + 3) -> forall s : Real, TangentSpace I (gamma s))
    (i : Fin (k + 3))
    (A B : forall s : Real, TangentSpace I (gamma s)) (t : Real)
    (hgamma : ContMDiff 𝓘(Real, Real) I ∞ gamma)
    (hY : forall j, ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun s : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (gamma s) (Y j s) : TangentBundle I M)))
    (hA : ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun s : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (gamma s) (A s) : TangentBundle I M)))
    (hB : ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun s : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (gamma s) (B s) : TangentBundle I M))) :
    curvOpNDerivAlong (I := I) g k gamma
        (Function.update Y i (fun s => A s + B s)) t =
      curvOpNDerivAlong (I := I) g k gamma
          (Function.update Y i A) t +
        curvOpNDerivAlong (I := I) g k gamma
          (Function.update Y i B) t := by
  rcases boundarylessI with ⟨hI⟩
  let : I.Boundaryless := ⟨hI⟩
  classical
  let YA : Fin (k + 3) -> forall s : Real, TangentSpace I (gamma s) :=
    Function.update Y i A
  let YB : Fin (k + 3) -> forall s : Real, TangentSpace I (gamma s) :=
    Function.update Y i B
  let YAB : Fin (k + 3) -> forall s : Real, TangentSpace I (gamma s) :=
    Function.update Y i (fun s => A s + B s)
  have hAB : ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun s : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (gamma s) (A s + B s) : TangentBundle I M)) := by
    have hsum := contMDiff_sum_along (I := I)
      (Finset.univ : Finset (Fin 2)) gamma
      (fun q s => Fin.cases (A s) (fun _ => B s) q) hgamma (by
        intro q hq
        fin_cases q
        · exact hA
        · exact hB)
    refine ContMDiff.congr hsum ?_
    intro s
    apply TotalSpace.ext
    · rfl
    · rw [Fin.sum_univ_two]
      rfl
  have hYA := smooth_update_along (I := I) k gamma Y i A hY hA
  have hYB := smooth_update_along (I := I) k gamma Y i B hY hB
  have hYAB :=
    smooth_update_along (I := I) k gamma Y i (fun s => A s + B s) hY hAB
  have hupdate
      (V : forall s : Real, TangentSpace I (gamma s)) (s : Real) :
      (fun j => (Function.update Y i V) j s) =
        Function.update (fun j => Y j s) i (V s) := by
    funext j
    by_cases hji : j = i
    · subst j
      simp only [Function.update_self]
    · simp only [Function.update_of_ne hji]
  have heval :
      (fun s : Real =>
        curvOpN (I := I) g k (gamma s) (fun j => YAB j s)) =
        fun s : Real =>
          curvOpN (I := I) g k (gamma s) (fun j => YA j s) +
            curvOpN (I := I) g k (gamma s) (fun j => YB j s) := by
    funext s
    change
      curvOpN (I := I) g k (gamma s)
          (fun j => (Function.update Y i (fun u => A u + B u)) j s) =
        curvOpN (I := I) g k (gamma s)
            (fun j => (Function.update Y i A) j s) +
          curvOpN (I := I) g k (gamma s)
            (fun j => (Function.update Y i B) j s)
    rw [hupdate, hupdate, hupdate]
    exact curvOpN_update_add (I := I) g k (gamma s)
      (fun j => Y j s) i (A s) (B s)
  have hEvalA :=
    curvOpN_smoothAlong (I := I) g k gamma YA hgamma hYA
  have hEvalB :=
    curvOpN_smoothAlong (I := I) g k gamma YB hgamma hYB
  have hEvalAdiff :
      DifferentiableAt Real
        (chartRepAt (I := I) gamma
          (fun s : Real =>
            curvOpN (I := I) g k (gamma s) (fun j => YA j s)) t) t :=
    chartRep_diff (I := I) gamma
      (fun s : Real =>
        curvOpN (I := I) g k (gamma s) (fun j => YA j s))
      hEvalA t
  have hEvalBdiff :
      DifferentiableAt Real
        (chartRepAt (I := I) gamma
          (fun s : Real =>
            curvOpN (I := I) g k (gamma s) (fun j => YB j s)) t) t :=
    chartRep_diff (I := I) gamma
      (fun s : Real =>
        curvOpN (I := I) g k (gamma s) (fun j => YB j s))
      hEvalB t
  have hAdiff :
      DifferentiableAt Real (chartRepAt (I := I) gamma A t) t :=
    chartRep_diff (I := I) gamma A hA t
  have hBdiff :
      DifferentiableAt Real (chartRepAt (I := I) gamma B t) t :=
    chartRep_diff (I := I) gamma B hB t
  let v : Fin (k + 3) -> TangentSpace I (gamma t) := fun j => Y j t
  let dY : Fin (k + 3) -> TangentSpace I (gamma t) :=
    fun j => covDerivAlong (I := I) g gamma (Y j) t
  let corrAB : Fin (k + 3) -> TangentSpace I (gamma t) := fun j =>
    curvOpN (I := I) g k (gamma t)
      (Function.update (fun q => YAB q t) j
        (covDerivAlong (I := I) g gamma (YAB j) t))
  let corrA : Fin (k + 3) -> TangentSpace I (gamma t) := fun j =>
    curvOpN (I := I) g k (gamma t)
      (Function.update (fun q => YA q t) j
        (covDerivAlong (I := I) g gamma (YA j) t))
  let corrB : Fin (k + 3) -> TangentSpace I (gamma t) := fun j =>
    curvOpN (I := I) g k (gamma t)
      (Function.update (fun q => YB q t) j
        (covDerivAlong (I := I) g gamma (YB j) t))
  have hcorr (j : Fin (k + 3)) : corrAB j = corrA j + corrB j := by
    by_cases hji : j = i
    · subst j
      have hDAB :
          covDerivAlong (I := I) g gamma (YAB i) t =
            covDerivAlong (I := I) g gamma A t +
              covDerivAlong (I := I) g gamma B t := by
        have hYABi : YAB i = fun s => A s + B s := by
          simp only [YAB, Function.update_self]
        rw [hYABi]
        exact covDerivAlong_add (I := I) g gamma A B t hAdiff hBdiff
      have hYAi : YA i = A := by
        simp only [YA, Function.update_self]
      have hYBi : YB i = B := by
        simp only [YB, Function.update_self]
      have hbaseAB :
          (fun q => YAB q t) =
            Function.update v i (A t + B t) := by
        change
          (fun q => (Function.update Y i (fun s => A s + B s)) q t) =
            Function.update v i (A t + B t)
        simpa only [v] using hupdate (fun s => A s + B s) t
      have hbaseA :
          (fun q => YA q t) = Function.update v i (A t) := by
        change
          (fun q => (Function.update Y i A) q t) =
            Function.update v i (A t)
        simpa only [v] using hupdate A t
      have hbaseB :
          (fun q => YB q t) = Function.update v i (B t) := by
        change
          (fun q => (Function.update Y i B) q t) =
            Function.update v i (B t)
        simpa only [v] using hupdate B t
      simp only [corrAB, corrA, corrB, hDAB, hYAi, hYBi]
      rw [hbaseAB, hbaseA, hbaseB]
      simp only [Function.update_idem]
      exact curvOpN_update_add (I := I) g k (gamma t) v i
        (covDerivAlong (I := I) g gamma A t)
        (covDerivAlong (I := I) g gamma B t)
    · have hDAB :
          covDerivAlong (I := I) g gamma (YAB j) t = dY j := by
        have hEq : YAB j = Y j := by
          simp only [YAB, Function.update_of_ne hji]
        rw [hEq]
      have hDA :
          covDerivAlong (I := I) g gamma (YA j) t = dY j := by
        have hEq : YA j = Y j := by
          simp only [YA, Function.update_of_ne hji]
        rw [hEq]
      have hDB :
          covDerivAlong (I := I) g gamma (YB j) t = dY j := by
        have hEq : YB j = Y j := by
          simp only [YB, Function.update_of_ne hji]
        rw [hEq]
      simp only [corrAB, corrA, corrB, hDAB, hDA, hDB]
      rw [hupdate, hupdate, hupdate]
      rw [Function.update_comm (Ne.symm hji),
        Function.update_comm (Ne.symm hji),
        Function.update_comm (Ne.symm hji)]
      exact curvOpN_update_add (I := I) g k (gamma t)
        (Function.update v j (dY j)) i (A t) (B t)
  have hsumcorr :
      (∑ j : Fin (k + 3), corrAB j) =
        (∑ j : Fin (k + 3), corrA j) +
          ∑ j : Fin (k + 3), corrB j := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    exact hcorr j
  change curvOpNDerivAlong (I := I) g k gamma YAB t =
    curvOpNDerivAlong (I := I) g k gamma YA t +
      curvOpNDerivAlong (I := I) g k gamma YB t
  unfold curvOpNDerivAlong
  rw [heval]
  rw [covDerivAlong_add (I := I) g gamma
    (fun s : Real =>
      curvOpN (I := I) g k (gamma s) (fun j => YA j s))
    (fun s : Real =>
      curvOpN (I := I) g k (gamma s) (fun j => YB j s))
    t hEvalAdiff hEvalBdiff]
  change
    (covDerivAlong (I := I) g gamma
          (fun s : Real =>
            curvOpN (I := I) g k (gamma s) (fun j => YA j s)) t +
        covDerivAlong (I := I) g gamma
          (fun s : Real =>
            curvOpN (I := I) g k (gamma s) (fun j => YB j s)) t) -
      ∑ j : Fin (k + 3), corrAB j =
    (covDerivAlong (I := I) g gamma
          (fun s : Real =>
            curvOpN (I := I) g k (gamma s) (fun j => YA j s)) t -
        ∑ j : Fin (k + 3), corrA j) +
      (covDerivAlong (I := I) g gamma
          (fun s : Real =>
            curvOpN (I := I) g k (gamma s) (fun j => YB j s)) t -
        ∑ j : Fin (k + 3), corrB j)
  rw [hsumcorr]
  abel

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  [SigmaCompactSpace M] in
private theorem curvOpNDeriv_sum
    (g : SmoothRiemannianMetric I M) (k : Nat)
    (gamma : Real -> M)
    (Y : Fin (k + 3) -> forall s : Real, TangentSpace I (gamma s))
    (i : Fin (k + 3)) {alpha : Type*}
    (S : Finset alpha)
    (V : alpha -> forall s : Real, TangentSpace I (gamma s)) (t : Real)
    (hgamma : ContMDiff 𝓘(Real, Real) I ∞ gamma)
    (hY : forall j, ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun s : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (gamma s) (Y j s) : TangentBundle I M)))
    (hV : forall a, ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun s : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (gamma s) (V a s) : TangentBundle I M))) :
    curvOpNDerivAlong (I := I) g k gamma
        (Function.update Y i (fun s => ∑ a ∈ S, V a s)) t =
      ∑ a ∈ S,
        curvOpNDerivAlong (I := I) g k gamma
          (Function.update Y i (V a)) t := by
  rcases boundarylessI with ⟨hI⟩
  let : I.Boundaryless := ⟨hI⟩
  classical
  induction S using Finset.induction_on with
  | empty =>
      have hzero := curvOpNDeriv_smul (I := I) g k gamma Y i
        (fun _ : Real => 0) t hgamma hY
        (differentiableAt_const (c := (0 : Real)))
      simpa only [Finset.sum_empty, zero_smul] using hzero
  | @insert a S ha ih =>
      have htail := contMDiff_sum_along (I := I) S gamma V hgamma
        (fun b hb => hV b)
      have hadd := curvOpNDeriv_add (I := I) g k gamma Y i
        (V a) (fun s => ∑ b ∈ S, V b s) t hgamma hY (hV a) htail
      have hsumfun :
          (fun s => ∑ b ∈ insert a S, V b s) =
            fun s => V a s + ∑ b ∈ S, V b s := by
        funext s
        rw [Finset.sum_insert ha]
      rw [hsumfun, hadd, ih]
      rw [Finset.sum_insert ha]

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  [SigmaCompactSpace M] in
private theorem curvOpNDeriv_slot
    (g : SmoothRiemannianMetric I M) (k : Nat)
    (gamma : Real -> M)
    (Y : Fin (k + 3) -> forall s : Real, TangentSpace I (gamma s))
    (i : Fin (k + 3))
    (A B : forall s : Real, TangentSpace I (gamma s)) (t : Real)
    (hgamma : ContMDiff 𝓘(Real, Real) I ∞ gamma)
    (hY : forall j, ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun s : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (gamma s) (Y j s) : TangentBundle I M)))
    (hA : ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun s : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (gamma s) (A s) : TangentBundle I M)))
    (hB : ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun s : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (gamma s) (B s) : TangentBundle I M)))
    (hAt : A t = B t) :
    curvOpNDerivAlong (I := I) g k gamma (Function.update Y i A) t =
      curvOpNDerivAlong (I := I) g k gamma (Function.update Y i B) t := by
  classical
  obtain ⟨Frame, hFrameSm, hFrameNear⟩ :=
    exists_smooth_chartBasisExtension (I := I) (gamma t)
  obtain ⟨c, hcSm, hcVal, hcExp⟩ :=
    exists_frame_exp (I := I) gamma A t hgamma hA Frame hFrameNear
  obtain ⟨d, hdSm, hdVal, hdExp⟩ :=
    exists_frame_exp (I := I) gamma B t hgamma hB Frame hFrameNear
  have hFrameCurve :
      forall a, ContMDiff 𝓘(Real, Real) I.tangent ∞
        (fun s : Real =>
          (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
            (gamma s) (Frame a (gamma s)) : TangentBundle I M)) := by
    intro a
    change ContMDiff 𝓘(Real, Real) (I.prod 𝓘(Real, E)) ∞
      (fun s : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (gamma s) (Frame a (gamma s)) : TangentBundle I M))
    refine ContMDiff.congr ((hFrameSm a).comp hgamma) ?_
    intro s
    rfl
  have hCoeff (a : Fin (Module.finrank Real E)) : c a t = d a t := by
    rw [hcVal a, hdVal a, AlongCurve.chartSectionCoord_def,
      AlongCurve.chartSectionCoord_def]
    rw [chartRepAt_apply, chartRepAt_apply, hAt]
  have hScaledC :
      forall a, ContMDiff 𝓘(Real, Real) I.tangent ∞
        (fun s : Real =>
          (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
            (gamma s) (c a s • Frame a (gamma s)) : TangentBundle I M)) := by
    intro a
    exact contMDiff_smul_bundleField_perp (I := I)
      hgamma (hcSm a) (hFrameCurve a)
  have hScaledD :
      forall a, ContMDiff 𝓘(Real, Real) I.tangent ∞
        (fun s : Real =>
          (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
            (gamma s) (d a s • Frame a (gamma s)) : TangentBundle I M)) := by
    intro a
    exact contMDiff_smul_bundleField_perp (I := I)
      hgamma (hdSm a) (hFrameCurve a)
  have hTermC (a : Fin (Module.finrank Real E)) :
      curvOpNDerivAlong (I := I) g k gamma
          (Function.update Y i
            (fun s => c a s • Frame a (gamma s))) t =
        c a t • curvOpNDerivAlong (I := I) g k gamma
          (Function.update Y i (fun s => Frame a (gamma s))) t := by
    have hBase :=
      smooth_update_along (I := I) k gamma Y i
        (fun s => Frame a (gamma s)) hY (hFrameCurve a)
    have hSmul := curvOpNDeriv_smul (I := I) g k gamma
      (Function.update Y i (fun s => Frame a (gamma s))) i (c a) t
      hgamma hBase ((hcSm a).contDiff.contDiffAt.differentiableAt (by simp))
    simpa only [Function.update_self, Function.update_idem] using hSmul
  have hTermD (a : Fin (Module.finrank Real E)) :
      curvOpNDerivAlong (I := I) g k gamma
          (Function.update Y i
            (fun s => d a s • Frame a (gamma s))) t =
        d a t • curvOpNDerivAlong (I := I) g k gamma
          (Function.update Y i (fun s => Frame a (gamma s))) t := by
    have hBase :=
      smooth_update_along (I := I) k gamma Y i
        (fun s => Frame a (gamma s)) hY (hFrameCurve a)
    have hSmul := curvOpNDeriv_smul (I := I) g k gamma
      (Function.update Y i (fun s => Frame a (gamma s))) i (d a) t
      hgamma hBase ((hdSm a).contDiff.contDiffAt.differentiableAt (by simp))
    simpa only [Function.update_self, Function.update_idem] using hSmul
  have hSumC :
      curvOpNDerivAlong (I := I) g k gamma
          (Function.update Y i
            (fun s => ∑ a, c a s • Frame a (gamma s))) t =
        ∑ a, curvOpNDerivAlong (I := I) g k gamma
          (Function.update Y i
            (fun s => c a s • Frame a (gamma s))) t := by
    simpa using curvOpNDeriv_sum (I := I) g k gamma Y i Finset.univ
      (fun a s => c a s • Frame a (gamma s)) t hgamma hY hScaledC
  have hSumD :
      curvOpNDerivAlong (I := I) g k gamma
          (Function.update Y i
            (fun s => ∑ a, d a s • Frame a (gamma s))) t =
        ∑ a, curvOpNDerivAlong (I := I) g k gamma
          (Function.update Y i
            (fun s => d a s • Frame a (gamma s))) t := by
    simpa using curvOpNDeriv_sum (I := I) g k gamma Y i Finset.univ
      (fun a s => d a s • Frame a (gamma s)) t hgamma hY hScaledD
  have hCongrC :
      curvOpNDerivAlong (I := I) g k gamma (Function.update Y i A) t =
        curvOpNDerivAlong (I := I) g k gamma
          (Function.update Y i
            (fun s => ∑ a, c a s • Frame a (gamma s))) t := by
    apply curvOpNDeriv_congr (I := I) g k gamma
    intro j
    by_cases hji : j = i
    · subst j
      filter_upwards [hcExp] with s hs
      calc
        Function.update Y i A i s = A s := by rw [Function.update_self]
        _ = ∑ a, c a s • Frame a (gamma s) := hs
        _ = Function.update Y i
            (fun s => ∑ a, c a s • Frame a (gamma s)) i s := by
          rw [Function.update_self]
    · simpa only [Function.update_of_ne hji] using
        (Filter.EventuallyEq.rfl : Y j =ᶠ[nhds t] Y j)
  have hCongrD :
      curvOpNDerivAlong (I := I) g k gamma (Function.update Y i B) t =
        curvOpNDerivAlong (I := I) g k gamma
          (Function.update Y i
            (fun s => ∑ a, d a s • Frame a (gamma s))) t := by
    apply curvOpNDeriv_congr (I := I) g k gamma
    intro j
    by_cases hji : j = i
    · subst j
      filter_upwards [hdExp] with s hs
      calc
        Function.update Y i B i s = B s := by rw [Function.update_self]
        _ = ∑ a, d a s • Frame a (gamma s) := hs
        _ = Function.update Y i
            (fun s => ∑ a, d a s • Frame a (gamma s)) i s := by
          rw [Function.update_self]
    · simpa only [Function.update_of_ne hji] using
        (Filter.EventuallyEq.rfl : Y j =ᶠ[nhds t] Y j)
  calc
    curvOpNDerivAlong (I := I) g k gamma (Function.update Y i A) t =
        curvOpNDerivAlong (I := I) g k gamma
          (Function.update Y i
            (fun s => ∑ a, c a s • Frame a (gamma s))) t := hCongrC
    _ = ∑ a, curvOpNDerivAlong (I := I) g k gamma
          (Function.update Y i
            (fun s => c a s • Frame a (gamma s))) t := hSumC
    _ = ∑ a, curvOpNDerivAlong (I := I) g k gamma
          (Function.update Y i
            (fun s => d a s • Frame a (gamma s))) t := by
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [hTermC a, hTermD a, hCoeff a]
    _ = curvOpNDerivAlong (I := I) g k gamma
          (Function.update Y i
            (fun s => ∑ a, d a s • Frame a (gamma s))) t := hSumD.symm
    _ = curvOpNDerivAlong (I := I) g k gamma
          (Function.update Y i B) t := hCongrD.symm

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  [SigmaCompactSpace M] in
private theorem curvOpNDeriv_all
    (g : SmoothRiemannianMetric I M) (k : Nat)
    (gamma : Real -> M)
    (Y Z : Fin (k + 3) -> forall s : Real, TangentSpace I (gamma s))
    (t : Real)
    (hgamma : ContMDiff 𝓘(Real, Real) I ∞ gamma)
    (hY : forall j, ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun s : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (gamma s) (Y j s) : TangentBundle I M)))
    (hZ : forall j, ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun s : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (gamma s) (Z j s) : TangentBundle I M)))
    (hAt : forall j, Y j t = Z j t) :
    curvOpNDerivAlong (I := I) g k gamma Y t =
      curvOpNDerivAlong (I := I) g k gamma Z t := by
  classical
  let mix :
      Finset (Fin (k + 3)) -> Fin (k + 3) ->
        forall s : Real, TangentSpace I (gamma s) :=
    fun S j => if j ∈ S then Z j else Y j
  have hMix (S : Finset (Fin (k + 3))) (j : Fin (k + 3)) :
      ContMDiff 𝓘(Real, Real) I.tangent ∞
        (fun s : Real =>
          (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
            (gamma s) (mix S j s) : TangentBundle I M)) := by
    by_cases hj : j ∈ S
    · simpa only [mix, if_pos hj] using hZ j
    · simpa only [mix, if_neg hj] using hY j
  have hPartial (S : Finset (Fin (k + 3))) :
      curvOpNDerivAlong (I := I) g k gamma Y t =
        curvOpNDerivAlong (I := I) g k gamma (mix S) t := by
    induction S using Finset.induction_on with
    | empty =>
        have hEmpty : mix ∅ = Y := by
          funext j
          simp [mix]
        rw [hEmpty]
    | @insert a S ha ih =>
        have hMixA : mix S a = Y a := by
          simp only [mix, if_neg ha]
        have hAtA : mix S a t = Z a t := by
          rw [hMixA]
          exact hAt a
        have hstep := curvOpNDeriv_slot (I := I) g k gamma (mix S) a
          (mix S a) (Z a) t hgamma (hMix S) (hMix S a) (hZ a) hAtA
        have hleft :
            Function.update (mix S) a (mix S a) = mix S := by
          funext j
          by_cases hja : j = a
          · subst j
            simp only [Function.update_self]
          · simp only [Function.update_of_ne hja]
        have hright :
            Function.update (mix S) a (Z a) = mix (insert a S) := by
          funext j
          by_cases hja : j = a
          · subst j
            simp only [Function.update_self, mix, Finset.mem_insert,
              true_or, if_true]
          · rw [Function.update_of_ne hja]
            simp only [mix, Finset.mem_insert, hja, false_or]
        rw [hleft, hright] at hstep
        exact ih.trans hstep
  have hall := hPartial (Finset.univ : Finset (Fin (k + 3)))
  have hUniv : mix Finset.univ = Z := by
    funext j
    simp only [mix, Finset.mem_univ, if_true]
  rw [hUniv] at hall
  exact hall

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem curvOpNDeriv_comp
    (g : SmoothRiemannianMetric I M) (k : Nat)
    (γ : Real -> M)
    (Y : Fin (k + 3) ->
      ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M -> Type _))
    (t : Real)
    (hγ : ContMDiff 𝓘(Real, Real) I ∞ γ) :
    curvOpNDerivAlong (I := I) g k γ
        (fun i s => Y i (γ s)) t =
      curvOpN (I := I) g (k + 1) (γ t)
        (Fin.cons
          ((mfderiv 𝓘(Real, Real) I γ t : Real →L[Real] _) (1 : Real))
          (fun i : Fin (k + 3) => Y i (γ t))) := by
  unfold curvOpNDerivAlong
  have hfield :
      (fun s : Real =>
        curvOpN (I := I) g k (γ s)
          (fun i : Fin (k + 3) => Y i (γ s))) =
        (fun s : Real => curvOpNField (I := I) g k Y (γ s)) := by
    funext s
    exact (curvOpNField_apply (I := I) g k Y (γ s)).symm
  rw [hfield]
  rw [curvOpN_cov_restrict (I := I) g k γ Y t hγ]
  abel

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem curvOpN_covAlong
    (g : SmoothRiemannianMetric I M) (k : Nat)
    (gamma : Real -> M)
    (Y : Fin (k + 3) -> forall s : Real, TangentSpace I (gamma s))
    (t : Real)
    (hgamma : ContMDiff 𝓘(Real, Real) I ∞ gamma)
    (hY : forall i, ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun s : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (gamma s) (Y i s) : TangentBundle I M))) :
    curvOpNDerivAlong (I := I) g k gamma Y t =
      curvOpN (I := I) g (k + 1) (gamma t)
        (Fin.cons
          ((mfderiv 𝓘(Real, Real) I gamma t : Real →L[Real] _) (1 : Real))
          (fun i : Fin (k + 3) => Y i t)) := by
  classical
  choose G hG using fun i : Fin (k + 3) =>
    ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞)) (F := E)
      (V := (TangentSpace I : M -> Type _)) (gamma t) (Y i t)
  have hGcurve :
      forall i, ContMDiff 𝓘(Real, Real) I.tangent ∞
        (fun s : Real =>
          (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
            (gamma s) (G i (gamma s)) : TangentBundle I M)) := by
    intro i
    change ContMDiff 𝓘(Real, Real) (I.prod 𝓘(Real, E)) ∞
      (fun s : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (gamma s) (G i (gamma s)) : TangentBundle I M))
    refine ContMDiff.congr ((G i).contMDiff.comp hgamma) ?_
    intro s
    rfl
  calc
    curvOpNDerivAlong (I := I) g k gamma Y t =
        curvOpNDerivAlong (I := I) g k gamma
          (fun i s => G i (gamma s)) t :=
      curvOpNDeriv_all (I := I) g k gamma Y
        (fun i s => G i (gamma s)) t hgamma hY hGcurve
        (fun i => (hG i).symm)
    _ = curvOpN (I := I) g (k + 1) (gamma t)
          (Fin.cons
            ((mfderiv 𝓘(Real, Real) I gamma t : Real →L[Real] _) (1 : Real))
            (fun i : Fin (k + 3) => G i (gamma t))) :=
      curvOpNDeriv_comp (I := I) g k gamma G t hgamma
    _ = curvOpN (I := I) g (k + 1) (gamma t)
          (Fin.cons
            ((mfderiv 𝓘(Real, Real) I gamma t : Real →L[Real] _) (1 : Real))
            (fun i : Fin (k + 3) => Y i t)) := by
      congr 1
      funext j
      refine Fin.cases ?_ (fun i => ?_) j
      · rfl
      · exact hG i

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
omit boundarylessI in
theorem curvOpN_cov
    (g : SmoothRiemannianMetric I M) (k : Nat)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (Y : Fin (k + 3) ->
      ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M -> Type _))
    (x : M)
    (hYzero : ∀ i : Fin (k + 3),
      ((DifferentialGeometry.Geometry.Curvature.metricCov
        (I := I) (M := M) g (fun p : M => Y i p) x) (X x)) = 0) :
    (DifferentialGeometry.Geometry.Curvature.metricCov
        (I := I) (M := M) g
        (fun p : M => curvOpNField (I := I) g k Y p) x) (X x) =
      curvOpN (I := I) g (k + 1) x
        (Fin.cons (X x) (fun i : Fin (k + 3) => Y i x)) := by
  let cov :=
    DifferentialGeometry.Geometry.Curvature.metricCov (I := I) (M := M) g
  have hmc :
      DifferentialGeometry.Geometry.Connection.IsMetricCompatibleGen
        (I := I) cov g := by
    change DifferentialGeometry.Geometry.Connection.IsMetricCompatibleGen
      (I := I)
      (DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric (I := I) g) g
    exact DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric_isMetricCompatible
      (I := I) g
  have hSharp :
      MDiffAt
        (T% (fun p : M =>
          Tensor0SBundle.cotangentSharpGen (I := I) g p
            (curvOpNForm (I := I) g k Y p))) x := by
    change MDiffAt (T% (fun p : M => curvOpNField (I := I) g k Y p)) x
    exact
      (curvOpNField (I := I) g k Y).contMDiff.contMDiffAt.mdifferentiableAt
        (by simp)
  have hcov :=
    Tensor0SBundle.cotangentSharp_cov_eq_sharp_curry_of_mdiffAt
      (I := I) cov g hmc
      (curvOpNForm (I := I) g k Y)
      (curvOpNablaForm (I := I) g k Y)
      (curvOpNabla_real (I := I) g k Y) X x hSharp
  change
    cov
        (fun p : M =>
          Tensor0SBundle.cotangentSharpGen (I := I) g p
            (curvOpNForm (I := I) g k Y p))
        x (X x) =
      curvOpN (I := I) g (k + 1) x
        (Fin.cons (X x) (fun i : Fin (k + 3) => Y i x))
  rw [hcov, curvOpN_eq_sharp]
  congr 1
  apply ContinuousMultilinearMap.ext
  intro slots
  have hslots :
      Fin.cons (X x) slots =
        DifferentialGeometry.Geometry.Curvature.vec2
          (I := I) (X x) (slots 0) := by
    funext i
    fin_cases i <;> rfl
  have hslots_one : slots = fun _ : Fin 1 => slots 0 := by
    funext i
    fin_cases i
    rfl
  calc
    (Tensor0SBundle.tensor0SCurry (I := I) (𝕜 := Real) (M := M) 1 x
        (curvOpNablaForm (I := I) g k Y x) (X x)) slots =
        curvOpNablaForm (I := I) g k Y x (Fin.cons (X x) slots) :=
      Tensor0SBundle.tensor0S_curry_apply_cons (I := I) 1
        (curvOpNablaForm (I := I) g k Y x) (X x) slots
    _ = curvOpNablaForm (I := I) g k Y x
        (DifferentialGeometry.Geometry.Curvature.vec2
          (I := I) (X x) (slots 0)) := by
      rw [hslots]
    _ = curvCovDeriv (I := I) (M := M) g (k + 1) x
        (Fin.cons (X x)
          (Function.update
            (Fin.snoc (fun i : Fin (k + 3) => Y i x) 0)
            (Fin.last (k + 3)) (slots 0))) :=
      curvOpNabla_eval (I := I) g k X Y x hYzero (slots 0)
    _ = curvCovDeriv (I := I) (M := M) g (k + 1) x
        (Fin.snoc (Fin.cons (X x) (fun i : Fin (k + 3) => Y i x))
          (slots 0)) := by
      rw [update_snoc_last, Fin.cons_snoc_eq_snoc_cons]
    _ = DifferentialGeometry.Tensor.RSTensor.oneFormAtSlot0S
        (I := I) (curvCovDeriv (I := I) (M := M) g (k + 1) x)
        (Fin.snoc (Fin.cons (X x) (fun i : Fin (k + 3) => Y i x)) 0)
        (Fin.last ((k + 1) + 3)) slots := by
      rw [hslots_one]
      rw [DifferentialGeometry.Tensor.RSTensor.oneFormAtSlot0S_apply]
      rw [update_snoc_last]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
omit [CompleteSpace E] in
theorem curvOpN_inner
    (g : SmoothRiemannianMetric I M) (k : Nat) (x : M)
    (v : Fin (k + 3) -> TangentSpace I x) (w : TangentSpace I x) :
    g.inner x w (curvOpN (I := I) g k x v) =
      curvCovDeriv (I := I) (M := M) g k x (Fin.snoc v w) := by
  change g.inner x w
      (DifferentialGeometry.Geometry.Operator.metricSharp (I := I) g x
        (curvLastCov (I := I) g k x v)) =
    curvLastCov (I := I) g k x v w
  exact DifferentialGeometry.Geometry.Operator.inner_metricSharp_right
    (I := I) g x (curvLastCov (I := I) g k x v) w

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] in
omit fdE in
private theorem snoc_vec3
    {x : M} (X Y Z W : TangentSpace I x) :
    Fin.snoc
        (DifferentialGeometry.Geometry.Curvature.vec3 (I := I) X Y Z) W =
      DifferentialGeometry.Geometry.Curvature.vec4 (I := I) X Y Z W := by
  funext i
  fin_cases i
  · change Fin.snoc (α := fun _ : Fin 4 => TangentSpace I x)
      (DifferentialGeometry.Geometry.Curvature.vec3 (I := I) X Y Z) W
        (0 : Fin 4) = X
    rw [show (0 : Fin 4) = (0 : Fin 3).castSucc by rfl,
      Fin.snoc_castSucc]
    simp [DifferentialGeometry.Geometry.Curvature.vec3]
  · change Fin.snoc (α := fun _ : Fin 4 => TangentSpace I x)
      (DifferentialGeometry.Geometry.Curvature.vec3 (I := I) X Y Z) W
        (1 : Fin 4) = Y
    rw [show (1 : Fin 4) = (1 : Fin 3).castSucc by rfl,
      Fin.snoc_castSucc]
    simp [DifferentialGeometry.Geometry.Curvature.vec3]
  · change Fin.snoc (α := fun _ : Fin 4 => TangentSpace I x)
      (DifferentialGeometry.Geometry.Curvature.vec3 (I := I) X Y Z) W
        (2 : Fin 4) = Z
    rw [show (2 : Fin 4) = (2 : Fin 3).castSucc by rfl,
      Fin.snoc_castSucc]
    simp [DifferentialGeometry.Geometry.Curvature.vec3]
  · change Fin.snoc (α := fun _ : Fin 4 => TangentSpace I x)
      (DifferentialGeometry.Geometry.Curvature.vec3 (I := I) X Y Z) W
        (3 : Fin 4) = W
    rw [show (3 : Fin 4) = Fin.last 3 by rfl, Fin.snoc_last]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] in
omit fdE in
private theorem snoc_vec4
    {x : M} (D X Y Z W : TangentSpace I x) :
    Fin.snoc
        (DifferentialGeometry.Geometry.Curvature.vec4 (I := I) D X Y Z) W =
      DifferentialGeometry.Geometry.Curvature.vec5 (I := I) D X Y Z W := by
  funext i
  fin_cases i
  · change Fin.snoc (α := fun _ : Fin 5 => TangentSpace I x)
      (DifferentialGeometry.Geometry.Curvature.vec4 (I := I) D X Y Z) W
        (0 : Fin 5) = D
    rw [show (0 : Fin 5) = (0 : Fin 4).castSucc by rfl,
      Fin.snoc_castSucc]
    simp [DifferentialGeometry.Geometry.Curvature.vec4]
  · change Fin.snoc (α := fun _ : Fin 5 => TangentSpace I x)
      (DifferentialGeometry.Geometry.Curvature.vec4 (I := I) D X Y Z) W
        (1 : Fin 5) = X
    rw [show (1 : Fin 5) = (1 : Fin 4).castSucc by rfl,
      Fin.snoc_castSucc]
    simp [DifferentialGeometry.Geometry.Curvature.vec4]
  · change Fin.snoc (α := fun _ : Fin 5 => TangentSpace I x)
      (DifferentialGeometry.Geometry.Curvature.vec4 (I := I) D X Y Z) W
        (2 : Fin 5) = Y
    rw [show (2 : Fin 5) = (2 : Fin 4).castSucc by rfl,
      Fin.snoc_castSucc]
    simp [DifferentialGeometry.Geometry.Curvature.vec4]
  · change Fin.snoc (α := fun _ : Fin 5 => TangentSpace I x)
      (DifferentialGeometry.Geometry.Curvature.vec4 (I := I) D X Y Z) W
        (3 : Fin 5) = Z
    rw [show (3 : Fin 5) = (3 : Fin 4).castSucc by rfl,
      Fin.snoc_castSucc]
    simp [DifferentialGeometry.Geometry.Curvature.vec4]
  · change Fin.snoc (α := fun _ : Fin 5 => TangentSpace I x)
      (DifferentialGeometry.Geometry.Curvature.vec4 (I := I) D X Y Z) W
        (4 : Fin 5) = W
    rw [show (4 : Fin 5) = Fin.last 4 by rfl, Fin.snoc_last]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem curvOpN_zero
    (g : SmoothRiemannianMetric I M) (x : M)
    (X Y Z : TangentSpace I x) :
    curvOpN (I := I) g 0 x
        (DifferentialGeometry.Geometry.Curvature.vec3 (I := I) X Y Z) =
      DifferentialGeometry.Geometry.Curvature.riemannOp
        (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g)
        x X Y Z := by
  apply DifferentialGeometry.Geometry.Connection.SmoothRiemannianMetric.eq_of_inner_eq g
  intro W
  calc
    g.inner x
        (curvOpN (I := I) g 0 x
          (DifferentialGeometry.Geometry.Curvature.vec3 (I := I) X Y Z)) W =
        g.inner x W
          (curvOpN (I := I) g 0 x
            (DifferentialGeometry.Geometry.Curvature.vec3 (I := I) X Y Z)) :=
      g.symm x _ _
    _ = curvCovDeriv (I := I) (M := M) g 0 x
          (DifferentialGeometry.Geometry.Curvature.vec4
            (I := I) X Y Z W) := by
      rw [curvOpN_inner, snoc_vec3]
    _ = g.inner x W
          (DifferentialGeometry.Geometry.Curvature.riemannOp
            (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g)
            x X Y Z) :=
      curvZero_apply (I := I) g x X Y Z W
    _ = g.inner x
          (DifferentialGeometry.Geometry.Curvature.riemannOp
            (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g)
            x X Y Z) W :=
      (g.symm x _ _).symm

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
omit [CompleteSpace E] in
theorem curvOpN_one
    (g : SmoothRiemannianMetric I M) (x : M)
    (D X Y Z : TangentSpace I x) :
    curvOpN (I := I) g 1 x
        (DifferentialGeometry.Geometry.Curvature.vec4 (I := I) D X Y Z) =
      DifferentialGeometry.Integral.Connection.nablaRiemannOp
        (I := I) g x D X Y Z := by
  apply DifferentialGeometry.Geometry.Connection.SmoothRiemannianMetric.eq_of_inner_eq g
  intro W
  calc
    g.inner x
        (curvOpN (I := I) g 1 x
          (DifferentialGeometry.Geometry.Curvature.vec4
            (I := I) D X Y Z)) W =
        g.inner x W
          (curvOpN (I := I) g 1 x
            (DifferentialGeometry.Geometry.Curvature.vec4
              (I := I) D X Y Z)) :=
      g.symm x _ _
    _ = curvCovDeriv (I := I) (M := M) g 1 x
          (DifferentialGeometry.Geometry.Curvature.vec5
            (I := I) D X Y Z W) := by
      rw [curvOpN_inner, snoc_vec4]
    _ = g.inner x W
          (DifferentialGeometry.Integral.Connection.nablaRiemannOp
            (I := I) g x D X Y Z) :=
      curvOne_apply (I := I) g x D X Y Z W
    _ = g.inner x
          (DifferentialGeometry.Integral.Connection.nablaRiemannOp
            (I := I) g x D X Y Z) W :=
      (g.symm x _ _).symm

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem curvAlong_eq_op0
    (g : SmoothRiemannianMetric I M) (gamma : Real -> M)
    (X Y Z : forall s : Real, TangentSpace I (gamma s)) (t : Real) :
    curvAlong (I := I) g gamma X Y Z t =
      curvOpN (I := I) g 0 (gamma t)
        (DifferentialGeometry.Geometry.Curvature.vec3
          (I := I) (X t) (Y t) (Z t)) := by
  simpa only [curvAlong] using
    (curvOpN_zero (I := I) g (gamma t) (X t) (Y t) (Z t)).symm

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
omit [CompleteSpace E] in
theorem curvDeriv_eq_op1
    (g : SmoothRiemannianMetric I M) (gamma : Real -> M)
    (X Y Z : forall s : Real, TangentSpace I (gamma s)) (t : Real)
    (hgamma : ContMDiff 𝓘(Real, Real) I ∞ gamma)
    (hX : ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun s : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (gamma s) (X s) : TangentBundle I M)))
    (hY : ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun s : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (gamma s) (Y s) : TangentBundle I M)))
    (hZ : ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun s : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (gamma s) (Z s) : TangentBundle I M))) :
    curvDerivAlong (I := I) g gamma X Y Z t =
      curvOpN (I := I) g 1 (gamma t)
        (DifferentialGeometry.Geometry.Curvature.vec4 (I := I)
          ((mfderiv 𝓘(Real, Real) I gamma t : Real →L[Real] _) (1 : Real))
          (X t) (Y t) (Z t)) := by
  calc
    curvDerivAlong (I := I) g gamma X Y Z t =
        DifferentialGeometry.Integral.Connection.nablaRiemannOp
          (I := I) g (gamma t)
          ((mfderiv 𝓘(Real, Real) I gamma t : Real →L[Real] _) (1 : Real))
          (X t) (Y t) (Z t) :=
      curvDeriv_eq_nabla (I := I) g gamma X Y Z t hgamma hX hY hZ
    _ = curvOpN (I := I) g 1 (gamma t)
          (DifferentialGeometry.Geometry.Curvature.vec4 (I := I)
            ((mfderiv 𝓘(Real, Real) I gamma t : Real →L[Real] _) (1 : Real))
            (X t) (Y t) (Z t)) :=
      (curvOpN_one (I := I) g (gamma t)
        ((mfderiv 𝓘(Real, Real) I gamma t : Real →L[Real] _) (1 : Real))
        (X t) (Y t) (Z t)).symm

end FixedMetric

end HCGCompactness
end DifferentialGeometry
