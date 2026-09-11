import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifference.LoweredCoefficient
import DifferentialGeometry.Geometry.Metric.Convergence.Coordinates.ConnectionComparison
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Self
import DifferentialGeometry.Geometry.Metric.Convergence.Coordinates.GoodFrame
import DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.Arity
import DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.Product
import DifferentialGeometry.Geometry.Metric.TensorInner.Cotangent.Riemannian
import DifferentialGeometry.Geometry.Coordinates.Connection.Christoffel

open Bundle Manifold Set Filter DifferentialGeometry
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open scoped Manifold ContDiff BigOperators Topology

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.Geometry.Connection

private def mixedRecurrence (r : ℕ) (a b : ℝ) : ℕ → ℕ → ℝ
  | 0, _ => b
  | k + 1, l => mixedRecurrence r a b k (l + 1) +
      ((r + k : ℕ) : ℝ) * ∑ c ∈ Finset.range (l + 1),
        (l.choose c : ℝ) * a * mixedRecurrence r a b k (l - c)

private theorem mixedRecurrence_nonneg (r : ℕ) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (k l : ℕ) :
    0 ≤ mixedRecurrence r a b k l := by
  induction k generalizing l with
  | zero => exact hb
  | succ k ih =>
    change 0 ≤ mixedRecurrence r a b k (l + 1) +
      ((r + k : ℕ) : ℝ) * ∑ c ∈ Finset.range (l + 1),
        (l.choose c : ℝ) * a * mixedRecurrence r a b k (l - c)
    exact add_nonneg (ih (l + 1)) (mul_nonneg (by positivity)
      (Finset.sum_nonneg fun c _ => mul_nonneg
        (mul_nonneg (Nat.cast_nonneg _) ha) (ih (l - c))))

section Local

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [T2Space M]
  {Idx : Type*} [Fintype Idx] [DecidableEq Idx]

omit [DecidableEq Idx] in
private theorem lowered_component_contraction
    (G g : SmoothRiemannianMetric I M)
    (frame : Idx → (x : M) → TangentSpace I x) {u : Set M}
    (hframe : IsLocalFrameOn I E 1 frame u) (hu : IsOpen u)
    {x : M} (hx : x ∈ u) (idx : Fin 3 → Idx) :
    frameComp0S (metricLoweredConnectionDifferenceField G g) frame x
        (fun i => idx (Equiv.swap (0 : Fin 3) 1 i)) =
      contrTail
        (fun m : Fin 3 → Idx =>
          christoffelSymbolInFrame (leviCivitaConnectionOfMetric g) frame hframe x
              (m 0) (m 1) (m 2) -
            christoffelSymbolInFrame (leviCivitaConnectionOfMetric G) frame hframe x
              (m 0) (m 1) (m 2))
        (frameComp0S (metricTensorField G) frame x) idx := by
  classical
  have hmd := ((hframe.contMDiffOn (idx 1)).contMDiffAt (hu.mem_nhds hx)).mdifferentiableAt
    (show (1 : WithTop ℕ∞) ≠ 0 by simp)
  rw [frameComp0S_apply]
  change G.inner x (PDE.DeTurck.connectionDifference g G x
    (frame (idx (Equiv.swap (0 : Fin 3) 1 0)) x)
    (frame (idx (Equiv.swap (0 : Fin 3) 1 1)) x))
    (frame (idx (Equiv.swap (0 : Fin 3) 1 2)) x) = _
  simp only [Equiv.swap_apply_left, Equiv.swap_apply_right,
    Equiv.swap_apply_of_ne_of_ne (by decide : (2 : Fin 3) ≠ 0) (by decide : (2 : Fin 3) ≠ 1)]
  change G.inner x
    ((CovariantDerivative.difference (leviCivitaConnectionOfMetric g)
      (leviCivitaConnectionOfMetric G) x (frame (idx 1) x)) (frame (idx 0) x))
    (frame (idx 2) x) = _
  rw [DifferentialGeometry.Tensor.Coordinates.christoffelSymbolDifference_expansion _ _ frame hframe hx,
    map_sum, sum_apply, contrTail_apply]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [ContinuousLinearMap.map_smul, smul_apply, smul_eq_mul]
  rw [DifferentialGeometry.Tensor.Coordinates.christoffelSymbolDifferenceInFrame_eq_sub _ _ frame hframe
    (idx 0) (idx 1) d hmd]
  change _ * G.inner x (frame d x) (frame (idx 2) x) =
    _ * G.inner x (frame (idx 2) x) (frame d x)
  rw [G.symm]
  rfl

private theorem component_tower_le_lowered
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e]
    (G g : SmoothRiemannianMetric I M) (basis : Module.Basis Idx ℝ E)
    {x : M} (hx : x ∈ e.baseSet)
    (hON : ∀ i j : Idx,
      G.inner x (e.localFrame basis i x) (e.localFrame basis j x) =
        if i = j then 1 else 0) (m : ℕ) :
    compL2 (iterCovCompU (I := I) (fun d y => e.localFrame basis d y)
      (fun y => christoffelSymbolInFrame (leviCivitaConnectionOfMetric G)
        (fun d z => e.localFrame basis d z)
        (e.isLocalFrameOn_localFrame_baseSet I 1 basis) y)
      (akCompField e g G basis) m x) ≤
    Real.sqrt (normSq0S G x (3 + m)
      (iterCov G 3 (metricLoweredConnectionDifferenceField G g) m x)) *
      Real.sqrt (Fintype.card Idx : ℝ) := by
  classical
  let frame := fun d y => e.localFrame basis d y
  let hf := e.isLocalFrameOn_localFrame_baseSet I 1 basis
  let chr := fun y => christoffelSymbolInFrame (leviCivitaConnectionOfMetric G) frame hf y
  let F := frameComp0S (metricLoweredConnectionDifferenceField G g) frame
  let B := frameComp0S (metricTensorField G) frame
  let A := akCompField e g G basis
  have hinv : MetricInverseInBasis G x (hf.toBasisAt hx)
      (identityInvMetric (Idx := Idx)) := by
    apply metricInverseInBasis_identity_of_orthonormal
    intro i j
    simpa only [IsLocalFrameOn.toBasisAt_coe] using hON i j
  have hcomp : ∀ y ∈ e.baseSet,
      (fun k : Fin 3 → Idx => F y (fun i => k (Equiv.swap (0 : Fin 3) 1 i))) =
        contrTail (A y) (B y) := by
    intro y hy
    funext k
    exact lowered_component_contraction G g frame hf e.open_baseSet hy k
  have hnorm : compL2 (iterCovComp (I := I) frame chr
      (fun y => contrTail (A y) (B y)) m x) =
      Real.sqrt (normSq0S G x (3 + m)
        (iterCov G 3 (metricLoweredConnectionDifferenceField G g) m x)) := by
    rw [← compL2_tower_eq G (metricLoweredConnectionDifferenceField G g)
      frame hf e.open_baseSet hx hinv m]
    change _ = compL2 (iterCovComp (I := I) frame chr F m x)
    rw [← compL2_iterCovComp_compReindex (Equiv.swap (0 : Fin 3) 1) frame chr F m x,
      iterCovComp_congr_on e.open_baseSet frame chr hcomp m x hx]
  have hzero : ∀ s, compL2 (iterCovComp (I := I) frame chr B (s + 1) x) = 0 := by
    intro s
    rw [compL2_tower_eq G (metricTensorField G) frame hf e.open_baseSet hx hinv (s + 1),
      ← metricCovDerivNorm_eq_iterCov G G (s + 1) (hf.toBasisAt hx) hinv,
      covNorm_self_succ]
  have htop := compL2_contrTail_topU_le e.open_baseSet frame chr
    (fun d => frame_e_mdiffOn e basis d)
    (fun d i j => lcChrist_e_mdiffOn e G basis d i j)
    B (fun k => gCompField_mdiffOn e G basis k) m A
    (fun k => akCompField_mdiffOn e g G basis k) hx
  have hres : (∑ c ∈ Finset.range m, (m.choose c : ℝ) *
      compL2 (iterCovCompU (I := I) frame chr A c x) *
      compL2 (iterCovComp (I := I) frame chr B (m - c) x)) = 0 := by
    apply Finset.sum_eq_zero
    intro c hc
    obtain ⟨s, hs⟩ := Nat.exists_eq_succ_of_ne_zero
      (show m - c ≠ 0 by have := Finset.mem_range.mp hc; omega)
    rw [hs, hzero]
    simp
  rw [hres, add_zero, hnorm] at htop
  have hraise := compL2_le_contrTail_inv
    (iterCovCompU (I := I) frame chr A m x) (B x) (ginvCompField e G basis x)
    (ginv_hinv e G basis hx)
  have hginv : compL2 (ginvCompField e G basis x) ≤
      Real.sqrt (Fintype.card Idx : ℝ) := by
    have h := ginv_compL2_le e G basis (1 : ℝ) zero_lt_one (fun v => by
      rw [gramE_eq_one e G basis hON, Matrix.one_mulVec, one_mul])
    simpa only [div_one] using h
  exact hraise.trans (mul_le_mul htop hginv (compL2_nonneg _)
    (Real.sqrt_nonneg _))

private theorem forward_step_bound (G g : SmoothRiemannianMetric I M)
    {r : ℕ} (hr : 0 < r)
    (S : Tensor0SField (I := I) (n := (∞ : WithTop ℕ∞)) r)
    (x : M) (l : ℕ) (a : ℝ)
    (hA : ∀ c, c ≤ l → Real.sqrt (normSq0S G x (3 + c)
      (iterCov G 3 (metricLoweredConnectionDifferenceField G g) c x)) ≤ a) :
    Real.sqrt (normSq0S G x ((r + 1) + l)
      (iterCov G (r + 1) (covStep g r S) l x)) ≤
    Real.sqrt (normSq0S G x (r + (l + 1)) (iterCov G r S (l + 1) x)) +
      (r : ℝ) * ∑ c ∈ Finset.range (l + 1), (l.choose c : ℝ) *
        (Real.sqrt (Module.finrank ℝ E : ℝ) * a) *
          Real.sqrt (normSq0S G x (r + (l - c)) (iterCov G r S (l - c) x)) := by
  classical
  obtain ⟨R, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  obtain ⟨basis, hON⟩ := exists_trivONBasis G x
  let e := trivializationAt E (TangentSpace I : M → Type _) x
  let frame := fun d y => e.localFrame basis d y
  let hf := e.isLocalFrameOn_localFrame_baseSet I 1 basis
  let chrG := fun y => christoffelSymbolInFrame (leviCivitaConnectionOfMetric G) frame hf y
  let chrg := fun y => christoffelSymbolInFrame (leviCivitaConnectionOfMetric g) frame hf y
  let F := frameComp0S S frame
  let A := akCompField e g G basis
  let Act := fun y => akAct (A y) (F y)
  let Fg := fun y => iterCovComp (I := I) frame chrg F 1 y
  let FG := fun y => iterCovComp (I := I) frame chrG F 1 y
  have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x
  have hinv : MetricInverseInBasis G x (hf.toBasisAt hx)
      (identityInvMetric (Idx := Fin (Module.finrank ℝ E))) := by
    apply metricInverseInBasis_identity_of_orthonormal
    intro i j
    simpa only [IsLocalFrameOn.toBasisAt_coe] using hON i j
  have hframe := fun d => frame_e_mdiffOn e basis d
  have hchrG := fun d i j => lcChrist_e_mdiffOn e G basis d i j
  have hchrg := fun d i j => lcChrist_e_mdiffOn e g basis d i j
  have hF := fun m => tensorComp_mdiffOn e S basis m
  have hA_sm := fun m => akCompField_mdiffOn e g G basis m
  have hFg := iterCovComp_contMDiffOn e.open_baseSet frame chrg F hframe hchrg hF 1
  have hAct : ∀ m, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => Act y m) e.baseSet := by
    intro m
    change ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun y => ∑ s : Fin (R + 1), ∑ p : Fin (Module.finrank ℝ E),
        A y ![m 0, Fin.tail m s, p] * F y (Function.update (Fin.tail m) s p)) e.baseSet
    exact contMDiffOn_finsetSum (fun s _ =>
      contMDiffOn_finsetSum (fun p _ =>
        (hA_sm ![m 0, Fin.tail m s, p]).mul (hF _)))
  have hconvert : ∀ y ∈ e.baseSet, FG y = fun m => Fg y m + Act y m := by
    intro y _
    funext m
    exact iterCov_chr_convert frame chrG chrg F y m
  have htower : iterCovComp (I := I) frame chrG FG l x =
      fun m => iterCovComp (I := I) frame chrG Fg l x m +
        iterCovComp (I := I) frame chrG Act l x m := by
    rw [iterCovComp_congr_on e.open_baseSet frame chrG hconvert l x hx]
    funext m
    exact iterCovComp_add e.open_baseSet frame chrG Fg Act hframe hchrG hFg hAct l x hx m
  have hsub : iterCovComp (I := I) frame chrG Fg l x =
      fun m => iterCovComp (I := I) frame chrG FG l x m -
        iterCovComp (I := I) frame chrG Act l x m := by
    funext m
    have hm := congrFun htower m
    linarith
  have hFg_actual : ∀ y ∈ e.baseSet,
      Fg y = frameComp0S (covStep g (R + 1) S) frame y := by
    intro y hy
    funext m
    exact iterCovComp_eq_iterCov g S frame hf e.open_baseSet 1 hy m
  have hnormg : compL2 (iterCovComp (I := I) frame chrG Fg l x) =
      Real.sqrt (normSq0S G x ((R + 1 + 1) + l)
        (iterCov G (R + 1 + 1) (covStep g (R + 1) S) l x)) := by
    rw [iterCovComp_congr_on e.open_baseSet frame chrG hFg_actual l x hx]
    exact compL2_tower_eq G (covStep g (R + 1) S) frame hf e.open_baseSet hx hinv l
  have hnormG : compL2 (iterCovComp (I := I) frame chrG FG l x) =
      Real.sqrt (normSq0S G x ((R + 1) + (l + 1))
        (iterCov G (R + 1) S (l + 1) x)) := by
    rw [← compL2_iterCovComp_shift frame chrG F l x]
    exact compL2_tower_eq G S frame hf e.open_baseSet hx hinv (l + 1)
  have hcompA : ∀ c, c ≤ l →
      compL2 (iterCovCompU (I := I) frame chrG A c x) ≤
        Real.sqrt (Module.finrank ℝ E : ℝ) * a := by
    intro c hc
    have h := component_tower_le_lowered e G g basis hx hON c
    simp only [Fintype.card_fin] at h
    have h' := mul_le_mul_of_nonneg_right (hA c hc)
      (Real.sqrt_nonneg (Module.finrank ℝ E : ℝ))
    simpa only [Fintype.card_fin, mul_comm] using h.trans h'
  have hactbound := compL2_akAct_le e.open_baseSet frame chrG hframe hchrG
    A F hA_sm hF l hx
  have hact : compL2 (iterCovComp (I := I) frame chrG Act l x) ≤
      (R + 1 : ℝ) * ∑ c ∈ Finset.range (l + 1), (l.choose c : ℝ) *
        (Real.sqrt (Module.finrank ℝ E : ℝ) * a) *
          Real.sqrt (normSq0S G x ((R + 1) + (l - c))
            (iterCov G (R + 1) S (l - c) x)) := by
    refine hactbound.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    refine Finset.sum_le_sum fun c hc => ?_
    rw [← compL2_tower_eq G S frame hf e.open_baseSet hx hinv (l - c)]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hcompA c (by have := Finset.mem_range.mp hc; omega))
        (Nat.cast_nonneg _)) (compL2_nonneg _)
  rw [← hnormg, hsub]
  simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_succ] using
    (compL2_sub_le _ _).trans (add_le_add (le_of_eq hnormG) hact)

private theorem mixed_actual_bound (G g : SmoothRiemannianMetric I M)
    {r : ℕ} (hr : 0 < r)
    (T : Tensor0SField (I := I) (n := (∞ : WithTop ℕ∞)) r)
    (x : M) (j : ℕ) (a b : ℝ) (ha : 0 ≤ a)
    (hA : ∀ s, s < j → Real.sqrt (normSq0S G x (3 + s)
      (iterCov G 3 (metricLoweredConnectionDifferenceField G g) s x)) ≤ a)
    (hT : ∀ s, s ≤ j → Real.sqrt (normSq0S G x (r + s)
      (iterCov G r T s x)) ≤ b) :
    ∀ k l, k + l ≤ j →
      Real.sqrt (normSq0S G x ((r + k) + l)
        (iterCov G (r + k) (iterCov g r T k) l x)) ≤
      mixedRecurrence r (Real.sqrt (Module.finrank ℝ E : ℝ) * a) b k l := by
  intro k
  induction k with
  | zero =>
    intro l hl
    exact hT l (by omega)
  | succ k ih =>
    intro l hkl
    rw [iterCov_succ]
    have hstep := forward_step_bound G g (by omega : 0 < r + k)
      (iterCov g r T k) x l a (fun c hc => hA c (by omega))
    refine hstep.trans ?_
    change _ ≤ mixedRecurrence r (Real.sqrt (Module.finrank ℝ E : ℝ) * a) b k (l + 1) +
      ((r + k : ℕ) : ℝ) * ∑ c ∈ Finset.range (l + 1), (l.choose c : ℝ) *
        (Real.sqrt (Module.finrank ℝ E : ℝ) * a) *
          mixedRecurrence r (Real.sqrt (Module.finrank ℝ E : ℝ) * a) b k (l - c)
    refine add_le_add (ih (l + 1) (by omega))
      (mul_le_mul_of_nonneg_left ?_ (by positivity))
    refine Finset.sum_le_sum fun c _ => ?_
    exact mul_le_mul_of_nonneg_left (ih (l - c) (by omega))
      (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) ha))

end Local

section Euclidean

open TopologicalSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

theorem exists_mixed_iterCov_bound_on_opens
    (r j : ℕ) (hr : 0 < r) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∃ C > 0, ∀ (U : Opens E)
      (G g : SmoothRiemannianMetric 𝓘(ℝ, E) U)
      (T : Tensor0SField (I := 𝓘(ℝ, E)) (M := U) (n := (∞ : WithTop ℕ∞)) r) (q : U),
      (∀ s, s < j → Real.sqrt (normSq0S G q (3 + s)
        (iterCov G 3 (metricLoweredConnectionDifferenceField G g) s q)) ≤ a) →
      (∀ s, s ≤ j → Real.sqrt (normSq0S G q (r + s) (iterCov G r T s q)) ≤ b) →
      ∀ k l, k + l ≤ j → Real.sqrt (normSq0S G q ((r + k) + l)
        (iterCov G (r + k) (iterCov g r T k) l q)) ≤ C := by
  let ae := Real.sqrt (Module.finrank ℝ E : ℝ) * a
  have hae : 0 ≤ ae := mul_nonneg (Real.sqrt_nonneg _) ha
  let P := mixedRecurrence r ae b
  have hP : ∀ k l, 0 ≤ P k l := mixedRecurrence_nonneg r ae b hae hb
  let C := 1 + ∑ k ∈ Finset.range (j + 1), ∑ l ∈ Finset.range (j + 1), P k l
  have hC : 0 < C := by
    have hsum : 0 ≤ ∑ k ∈ Finset.range (j + 1),
        ∑ l ∈ Finset.range (j + 1), P k l :=
      Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun l _ => hP k l
    dsimp only [C]
    linarith
  refine ⟨C, hC, ?_⟩
  intro U G g T q hA hT k l hkl
  have h := mixed_actual_bound G g hr T q j a b ha hA hT k l hkl
  have hk : k ∈ Finset.range (j + 1) := Finset.mem_range.mpr (by omega)
  have hl : l ∈ Finset.range (j + 1) := Finset.mem_range.mpr (by omega)
  have hinner : P k l ≤ ∑ t ∈ Finset.range (j + 1), P k t :=
    Finset.single_le_sum (fun t _ => hP k t) hl
  have houter : (∑ t ∈ Finset.range (j + 1), P k t) ≤
      ∑ s ∈ Finset.range (j + 1), ∑ t ∈ Finset.range (j + 1), P s t :=
    Finset.single_le_sum (fun s _ => Finset.sum_nonneg fun t _ => hP s t) hk
  exact h.trans ((hinner.trans houter).trans (by dsimp only [C]; linarith))

end Euclidean

end DifferentialGeometry.Geometry.Connection
