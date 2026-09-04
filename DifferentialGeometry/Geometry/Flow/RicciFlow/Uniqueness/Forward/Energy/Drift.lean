import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.Energy.Remainder

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle DifferentialGeometry.Tensor0SBundle
open _root_.Tensor0SBundle
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.RSTensor
open scoped Manifold ContDiff BigOperators Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]


section Slots

variable {x : M}

omit [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
private theorem drift_onFrame (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ b : Module.Basis (Fin (Module.finrank Real (TangentSpace I x))) Real
        (TangentSpace I x),
      ∀ i j, g.inner x (b i) (b j) = if i = j then (1 : Real) else 0 := by
  classical
  let D := (tangentMetricDataGen (I := I) g x).metric
  let : InnerProductSpace.Core Real (TangentSpace I x) := D.toCore
  let : NormedAddCommGroup (TangentSpace I x) :=
    @InnerProductSpace.Core.toNormedAddCommGroup Real (TangentSpace I x) _ _ _ D.toCore
  let : InnerProductSpace Real (TangentSpace I x) :=
    @InnerProductSpace.ofCore Real (TangentSpace I x) _ _ _ D.toCore.toCore
  let ob := stdOrthonormalBasis Real (TangentSpace I x)
  refine ⟨ob.toBasis, ?_⟩
  intro i j
  have hinner : Inner.inner Real (ob i) (ob j) = D.inner (ob i) (ob j) :=
    MetricFiberData.toCore_inner D (ob i) (ob j)
  change g.inner x (ob.toBasis i) (ob.toBasis j) = if i = j then (1 : Real) else 0
  rw [← TangentMetricDataGen.inner_eq_gen
    (tangentMetricDataGen (I := I) g x) (ob.toBasis i) (ob.toBasis j)]
  change D.inner (ob i) (ob j) = if i = j then (1 : Real) else 0
  rw [← hinner]
  exact ob.inner_eq_ite i j

omit [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
private theorem drift_onFrame_inv {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) {x : M}
    (b : Module.Basis Idx Real (TangentSpace I x))
    (hON : ∀ i j, g.inner x (b i) (b j) = if i = j then (1 : Real) else 0) :
    MetricInverseInBasisGen (I := I) g x b (identityInvMetric (Idx := Idx)) := by
  intro i j
  constructor <;> simp [identityInvMetric, diagonalInvMetric, hON]

private def driftPermutationCycleZeroTwoOneThree : Equiv.Perm (Fin 4) :=
  Equiv.ofBijective ![2, 3, 1, 0] (by decide)

private def driftPermutationSwapZeroTwoOneThree : Equiv.Perm (Fin 4) :=
  Equiv.ofBijective ![2, 3, 0, 1] (by decide)

private def driftPermutationSwapTwoThree : Equiv.Perm (Fin 4) :=
  Equiv.ofBijective ![0, 1, 3, 2] (by decide)

private def reindexDriftTensor (e : Equiv.Perm (Fin 4))
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x :=
  T.domDomCongr e

omit [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
@[simp] private theorem reindexDriftTensor_apply (e : Equiv.Perm (Fin 4))
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x)
    (v : Fin 4 → TangentSpace I x) :
    Tensor0SSpace.eval (reindexDriftTensor (I := I) e T) v =
      Tensor0SSpace.eval T (fun a : Fin 4 => v (e a)) :=
  Tensor0SSpace.domDomCongr_apply (I := I) e T v

def driftSlots
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x :=
  (T - reindexDriftTensor (I := I) driftPermutationCycleZeroTwoOneThree T) +
    (reindexDriftTensor (I := I) driftPermutationSwapZeroTwoOneThree T - reindexDriftTensor (I := I) driftPermutationSwapTwoThree T)

omit [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
theorem driftSlots_apply
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x)
    (X Y Z W : TangentSpace I x) :
    Tensor0SSpace.eval (driftSlots (I := I) T) (vec4 (I := I) X Y Z W) =
      (Tensor0SSpace.eval T (vec4 (I := I) X Y Z W) -
        Tensor0SSpace.eval T (vec4 (I := I) Z W Y X)) +
      (Tensor0SSpace.eval T (vec4 (I := I) Z W X Y) -
        Tensor0SSpace.eval T (vec4 (I := I) X Y W Z)) := by
  rw [driftSlots, Tensor0SSpace.eval_add, Tensor0SSpace.eval_sub,
    Tensor0SSpace.eval_sub]
  simp only [reindexDriftTensor_apply]
  congr 2 <;>
    · congr 1
      funext a
      fin_cases a <;> simp [driftPermutationCycleZeroTwoOneThree, driftPermutationSwapZeroTwoOneThree, driftPermutationSwapTwoThree, vec4]

omit [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
theorem driftSlots_add
    (A B : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x) :
    driftSlots (I := I) (A + B) =
      driftSlots (I := I) A + driftSlots (I := I) B := by
  refine tensor0SSpace_ext (𝕜 := Real) 4 x fun v => ?_
  change Tensor0SSpace.eval (driftSlots (I := I) (A + B)) v =
    Tensor0SSpace.eval (driftSlots (I := I) A + driftSlots (I := I) B) v
  simp only [driftSlots, Tensor0SSpace.eval_add, Tensor0SSpace.eval_sub,
    reindexDriftTensor_apply]
  ring

omit [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
theorem driftSlots_sub
    (A B : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x) :
    driftSlots (I := I) A - driftSlots (I := I) B =
      driftSlots (I := I) (A - B) := by
  refine tensor0SSpace_ext (𝕜 := Real) 4 x fun v => ?_
  change Tensor0SSpace.eval (driftSlots (I := I) A - driftSlots (I := I) B) v =
    Tensor0SSpace.eval (driftSlots (I := I) (A - B)) v
  simp only [driftSlots, Tensor0SSpace.eval_add, Tensor0SSpace.eval_sub,
    reindexDriftTensor_apply]
  ring

variable [NeZero (Module.finrank Real E)]


omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
theorem driftSlotsSq_le (g : SmoothRiemannianMetric I M)
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x) :
    normSq0S (I := I) g x 4 (driftSlots (I := I) T) ≤
      16 * normSq0S (I := I) g x 4 T := by
  classical
  obtain ⟨basis, hON⟩ := drift_onFrame (I := I) g x
  have hinv := drift_onFrame_inv (I := I) g basis hON
  have hp1 : normSq0S (I := I) g x 4 (reindexDriftTensor (I := I) driftPermutationCycleZeroTwoOneThree T) =
      normSq0S (I := I) g x 4 T :=
    normSq0S_domDomCongr (I := I) g x basis hinv driftPermutationCycleZeroTwoOneThree T
  have hp2 : normSq0S (I := I) g x 4 (reindexDriftTensor (I := I) driftPermutationSwapZeroTwoOneThree T) =
      normSq0S (I := I) g x 4 T :=
    normSq0S_domDomCongr (I := I) g x basis hinv driftPermutationSwapZeroTwoOneThree T
  have hp3 : normSq0S (I := I) g x 4 (reindexDriftTensor (I := I) driftPermutationSwapTwoThree T) =
      normSq0S (I := I) g x 4 T :=
    normSq0S_domDomCongr (I := I) g x basis hinv driftPermutationSwapTwoThree T
  have hleft := normSq0S_sub_le (I := I) g x 4 T
    (reindexDriftTensor (I := I) driftPermutationCycleZeroTwoOneThree T)
  have hright := normSq0S_sub_le (I := I) g x 4
    (reindexDriftTensor (I := I) driftPermutationSwapZeroTwoOneThree T) (reindexDriftTensor (I := I) driftPermutationSwapTwoThree T)
  have houter := normSq0S_add_le (I := I) g x 4
    (T - reindexDriftTensor (I := I) driftPermutationCycleZeroTwoOneThree T)
    (reindexDriftTensor (I := I) driftPermutationSwapZeroTwoOneThree T - reindexDriftTensor (I := I) driftPermutationSwapTwoThree T)
  rw [hp1] at hleft
  rw [hp2, hp3] at hright
  rw [driftSlots]
  linarith

end Slots

section Core

variable {x : M}

omit [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
private theorem drift02_add_left
    (q : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (u₁ u₂ Z : TangentSpace I x) :
    q (fun a : Fin 2 => if a = 0 then u₁ + u₂ else Z) =
      q (fun a : Fin 2 => if a = 0 then u₁ else Z) +
        q (fun a : Fin 2 => if a = 0 then u₂ else Z) := by
  classical
  set m : Fin 2 → TangentSpace I x := fun a => if a = 0 then u₁ else Z with hm
  have hupd : ∀ u : TangentSpace I x,
      Function.update m 0 u = (fun a : Fin 2 => if a = 0 then u else Z) := by
    intro u
    funext a
    fin_cases a <;> simp [hm]
  calc
    q (fun a : Fin 2 => if a = 0 then u₁ + u₂ else Z) =
        q (Function.update m 0 (u₁ + u₂)) := by rw [hupd]
    _ = q (Function.update m 0 u₁) + q (Function.update m 0 u₂) :=
      q.map_update_add m 0 u₁ u₂
    _ = q (fun a : Fin 2 => if a = 0 then u₁ else Z) +
        q (fun a : Fin 2 => if a = 0 then u₂ else Z) := by rw [hupd, hupd]

omit [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
private theorem drift02_sub_left
    (q : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (u₁ u₂ Z : TangentSpace I x) :
    q (fun a : Fin 2 => if a = 0 then u₁ - u₂ else Z) =
      q (fun a : Fin 2 => if a = 0 then u₁ else Z) -
        q (fun a : Fin 2 => if a = 0 then u₂ else Z) := by
  have h := drift02_add_left (I := I) q (u₁ - u₂) u₂ Z
  rw [sub_add_cancel] at h
  exact eq_sub_of_add_eq h.symm

omit [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
theorem lowerTri_split
    (q₁ q₂ : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (A₁ A₂ : TangentSpace I x →L[Real] TangentSpace I x →L[Real]
      TangentSpace I x →L[Real] TangentSpace I x) :
    lowerTri (I := I) q₁ A₁ - lowerTri (I := I) q₂ A₂ =
      lowerTri (I := I) (q₁ - q₂) A₁ + lowerTri (I := I) q₂ (A₁ - A₂) := by
  refine tensor0SSpace_ext (𝕜 := Real) 4 x fun v => ?_
  change Tensor0SSpace.eval (lowerTri (I := I) q₁ A₁ - lowerTri (I := I) q₂ A₂) v =
    Tensor0SSpace.eval
      (lowerTri (I := I) (q₁ - q₂) A₁ + lowerTri (I := I) q₂ (A₁ - A₂)) v
  rw [Tensor0SSpace.eval_sub, Tensor0SSpace.eval_add,
    lowerTri_apply, lowerTri_apply, lowerTri_apply, lowerTri_apply,
    Tensor0SSpace.eval_sub]
  have hA :
      (((A₁ - A₂) (v 0)) (v 1)) (v 2) =
        ((A₁ (v 0)) (v 1)) (v 2) - ((A₂ (v 0)) (v 1)) (v 2) := rfl
  rw [hA]
  have hsub := drift02_sub_left (I := I) q₂
    (((A₁ (v 0)) (v 1)) (v 2)) (((A₂ (v 0)) (v 1)) (v 2)) (v 3)
  change Tensor0SSpace.eval q₂
      (fun a : Fin 2 => if a = 0 then
        ((A₁ (v 0)) (v 1)) (v 2) - ((A₂ (v 0)) (v 1)) (v 2) else v 3) =
    Tensor0SSpace.eval q₂
        (fun a : Fin 2 => if a = 0 then ((A₁ (v 0)) (v 1)) (v 2) else v 3) -
      Tensor0SSpace.eval q₂
        (fun a : Fin 2 => if a = 0 then ((A₂ (v 0)) (v 1)) (v 2) else v 3) at hsub
  rw [hsub]
  ring


omit [SigmaCompactSpace M] in
theorem lowerRm_eq_rm04 (g : SmoothRiemannianMetric I M) (x : M) :
    lowerTri (I := I) (metricTensorField (I := I) g x)
        (riemannOp (metricCov (I := I) g) x) =
      metricRm04At (I := I) g x := by
  refine tensor0SSpace_ext (𝕜 := Real) 4 x fun v => ?_
  change Tensor0SSpace.eval
      (lowerTri (I := I) (metricTensorField (I := I) g x)
        (riemannOp (metricCov (I := I) g) x)) v =
    Tensor0SSpace.eval (metricRm04At (I := I) g x) v
  have hv : vec4 (I := I) (v 0) (v 1) (v 2) (v 3) = v := by
    funext a
    fin_cases a <;> simp [vec4]
  have hleft :
      Tensor0SSpace.eval
          (lowerTri (I := I) (metricTensorField (I := I) g x)
            (riemannOp (metricCov (I := I) g) x)) v =
        g.inner x ((((riemannOp (metricCov (I := I) g) x) (v 0)) (v 1)) (v 2)) (v 3) := by
    rw [lowerTri_apply, metricTensorField_eval]
    simp
  calc
    Tensor0SSpace.eval
        (lowerTri (I := I) (metricTensorField (I := I) g x)
          (riemannOp (metricCov (I := I) g) x)) v =
        g.inner x ((((riemannOp (metricCov (I := I) g) x) (v 0)) (v 1)) (v 2)) (v 3) := hleft
    _ = Tensor0SSpace.eval (metricRm04At (I := I) g x)
        (vec4 (I := I) (v 0) (v 1) (v 2) (v 3)) :=
      (metricRm04At_inner (I := I) g x (v 0) (v 1) (v 2) (v 3)).symm
    _ = Tensor0SSpace.eval (metricRm04At (I := I) g x) v :=
      congrArg (Tensor0SSpace.eval (metricRm04At (I := I) g x)) hv

def ricciDrift04 (g : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x :=
  driftSlots (I := I)
    (lowerTri (I := I) (metricRicciAt (I := I) g x)
      (riemannOp (metricCov (I := I) g) x))

omit [SigmaCompactSpace M] in
theorem ricciDrift_sub (g₁ g₂ : SmoothRiemannianMetric I M) (x : M) :
    ricciDrift04 (I := I) g₁ x - ricciDrift04 (I := I) g₂ x =
      driftSlots (I := I)
        (lowerTri (I := I)
          (metricRicciAt (I := I) g₁ x - metricRicciAt (I := I) g₂ x)
          (riemannOp (metricCov (I := I) g₁) x)) +
      driftSlots (I := I)
        (lowerTri (I := I) (metricRicciAt (I := I) g₂ x)
          (rmDiffVec (I := I) g₁ g₂ x)) := by
  rw [ricciDrift04, ricciDrift04, driftSlots_sub, lowerTri_split, driftSlots_add]
  rfl

variable [NeZero (Module.finrank Real E)]


omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem ricciDriftSq_le (g₁ g₂ : SmoothRiemannianMetric I M) (x : M) :
    normSq0S (I := I) g₁ x 4
        (ricciDrift04 (I := I) g₁ x - ricciDrift04 (I := I) g₂ x) ≤
      32 * (Module.finrank Real E : Real) ^ 6 *
        (normSq0S (I := I) g₁ x 2
            (metricRicciAt (I := I) g₁ x - metricRicciAt (I := I) g₂ x) *
          normSq0S (I := I) g₁ x 4 (metricRm04At (I := I) g₁ x) +
        normSq0S (I := I) g₁ x 2 (metricRicciAt (I := I) g₂ x) *
          rmDiffSq (I := I) g₁ g₂ x) := by
  let U : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x :=
    lowerTri (I := I)
      (metricRicciAt (I := I) g₁ x - metricRicciAt (I := I) g₂ x)
      (riemannOp (metricCov (I := I) g₁) x)
  let V : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x :=
    lowerTri (I := I) (metricRicciAt (I := I) g₂ x)
      (rmDiffVec (I := I) g₁ g₂ x)
  have hU0 := lowerTriSq_le (I := I) g₁
    (metricRicciAt (I := I) g₁ x - metricRicciAt (I := I) g₂ x)
    (riemannOp (metricCov (I := I) g₁) x)
  have hV0 := lowerTriSq_le (I := I) g₁
    (metricRicciAt (I := I) g₂ x)
    (rmDiffVec (I := I) g₁ g₂ x)
  have hU : normSq0S (I := I) g₁ x 4 (driftSlots (I := I) U) ≤
      16 * (Module.finrank Real E : Real) ^ 6 *
        (normSq0S (I := I) g₁ x 2
            (metricRicciAt (I := I) g₁ x - metricRicciAt (I := I) g₂ x) *
          normSq0S (I := I) g₁ x 4 (metricRm04At (I := I) g₁ x)) := by
    refine (driftSlotsSq_le (I := I) g₁ U).trans ?_
    rw [lowerRm_eq_rm04] at hU0
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left hU0 (by norm_num : (0 : Real) ≤ 16)
  have hV : normSq0S (I := I) g₁ x 4 (driftSlots (I := I) V) ≤
      16 * (Module.finrank Real E : Real) ^ 6 *
        (normSq0S (I := I) g₁ x 2 (metricRicciAt (I := I) g₂ x) *
          rmDiffSq (I := I) g₁ g₂ x) := by
    refine (driftSlotsSq_le (I := I) g₁ V).trans ?_
    rw [← rmDiffLowAt_eq_lowerTri, ← rmDiffSq_def] at hV0
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left hV0 (by norm_num : (0 : Real) ≤ 16)
  have houter := normSq0S_add_le (I := I) g₁ x 4
    (driftSlots (I := I) U) (driftSlots (I := I) V)
  rw [ricciDrift_sub]
  change normSq0S (I := I) g₁ x 4
      (driftSlots (I := I) U + driftSlots (I := I) V) ≤ _
  calc
    normSq0S (I := I) g₁ x 4
        (driftSlots (I := I) U + driftSlots (I := I) V) ≤
      2 * normSq0S (I := I) g₁ x 4 (driftSlots (I := I) U) +
        2 * normSq0S (I := I) g₁ x 4 (driftSlots (I := I) V) := houter
    _ ≤
      2 * (16 * (Module.finrank Real E : Real) ^ 6 *
        (normSq0S (I := I) g₁ x 2
            (metricRicciAt (I := I) g₁ x - metricRicciAt (I := I) g₂ x) *
          normSq0S (I := I) g₁ x 4 (metricRm04At (I := I) g₁ x))) +
      2 * (16 * (Module.finrank Real E : Real) ^ 6 *
        (normSq0S (I := I) g₁ x 2 (metricRicciAt (I := I) g₂ x) *
          rmDiffSq (I := I) g₁ g₂ x)) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hU (by norm_num))
          (mul_le_mul_of_nonneg_left hV (by norm_num))
    _ = _ := by ring

end Core

section Components

variable [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {x : M}

omit [SigmaCompactSpace M] [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
private theorem ricciAt_symm' (g : SmoothRiemannianMetric I M) (x : M)
    (X Y : TangentSpace I x) :
    metricRicciAt (I := I) g x (vec2 (I := I) X Y) =
      metricRicciAt (I := I) g x (vec2 (I := I) Y X) := by
  rw [metricRicciAt_apply_eq_ricciTensor, metricRicciAt_apply_eq_ricciTensor]
  exact ricciTensor_symm (I := I) g x X Y

omit [SigmaCompactSpace M] [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
private theorem rm04_swap12 (g : SmoothRiemannianMetric I M) (x : M)
    (A B C D : TangentSpace I x) :
    metricRm04At (I := I) g x (vec4 (I := I) A B C D) =
      -metricRm04At (I := I) g x (vec4 (I := I) B A C D) := by
  rw [metricRm04At_inner, metricRm04At_inner,
    riemannOp_swap (metricCov (I := I) g) x A B C]
  simp

omit [SigmaCompactSpace M] [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
private theorem rm04_swap34 (g : SmoothRiemannianMetric I M) (x : M)
    (A B C D : TangentSpace I x) :
    metricRm04At (I := I) g x (vec4 (I := I) A B C D) =
      -metricRm04At (I := I) g x (vec4 (I := I) A B D C) := by
  rw [metricRm04At_inner, metricRm04At_inner]
  change
    g.inner x (riemannOp (LeviCivita (I := I) g) x A B C) D =
      -g.inner x (riemannOp (LeviCivita (I := I) g) x A B D) C
  have h := riemannOp_metric_skew (I := I) g x A B C D
  calc
    g.inner x (riemannOp (LeviCivita (I := I) g) x A B C) D =
        -g.inner x C (riemannOp (LeviCivita (I := I) g) x A B D) := by
      linarith
    _ = -g.inner x (riemannOp (LeviCivita (I := I) g) x A B D) C := by
      rw [g.symm x C]

omit [SigmaCompactSpace M] [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
private theorem rm04_pair (g : SmoothRiemannianMetric I M) (x : M)
    (A B C D : TangentSpace I x) :
    metricRm04At (I := I) g x (vec4 (I := I) A B C D) =
      metricRm04At (I := I) g x (vec4 (I := I) C D A B) := by
  rw [metricRm04At_inner, metricRm04At_inner]
  exact riemannOp_inner_pair_symm (I := I) g x A B C D

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private theorem ricciLow_comp
    (g : SmoothRiemannianMetric I M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx → Idx → Real)
    (hinv : MetricInverseInBasisGen (I := I) g x basis gInv)
    (X Y Z : TangentSpace I x) (l : Idx) :
    Tensor0SSpace.eval
        (lowerTri (I := I) (metricRicciAt (I := I) g x)
          (riemannOp (metricCov (I := I) g) x))
        (vec4 (I := I) X Y Z (basis l)) =
      ∑ p : Idx,
        (∑ a : Idx, gInv p a *
          metricRicciAt (I := I) g x (vec2 (I := I) (basis l) (basis a))) *
        metricRm04At (I := I) g x (vec4 (I := I) X Y Z (basis p)) := by
  classical
  let V : TangentSpace I x := riemannOp (metricCov (I := I) g) x X Y Z
  have hrepr : ∀ p : Idx, basis.repr V p =
      ∑ a : Idx, gInv p a *
        metricRm04At (I := I) g x (vec4 (I := I) X Y Z (basis a)) := by
    intro p
    rw [basis_repr_eq_sum_inv_inner (I := I) g x basis gInv hinv V p]
    exact Finset.sum_congr rfl fun a _ => by
      rw [metricRm04At_inner]
  have hsym := invMetric_symm (I := I) g x basis gInv hinv
  change Tensor0SSpace.eval
    (lowerTri (I := I) (metricRicciAt (I := I) g x)
      (riemannOp (metricCov (I := I) g) x))
      (vec4 (I := I) X Y Z (basis l)) = _
  rw [lowerTri_apply]
  change metricRicciAt (I := I) g x
      (fun a : Fin 2 => if a = 0 then V else basis l) = _
  rw [tensor02_expand (I := I) (metricRicciAt (I := I) g x) basis V (basis l)]
  simp_rw [hrepr]
  calc
    (∑ p : Idx,
        (∑ a : Idx, gInv p a *
          metricRm04At (I := I) g x (vec4 (I := I) X Y Z (basis a))) *
        metricRicciAt (I := I) g x (vec2 (I := I) (basis p) (basis l)))
        =
      ∑ p : Idx, ∑ a : Idx,
        gInv p a *
          metricRm04At (I := I) g x (vec4 (I := I) X Y Z (basis a)) *
          metricRicciAt (I := I) g x (vec2 (I := I) (basis l) (basis p)) := by
            refine Finset.sum_congr rfl fun p _ => ?_
            rw [Finset.sum_mul]
            exact Finset.sum_congr rfl fun a _ => by
              rw [ricciAt_symm' (I := I) g x (basis p) (basis l)]
    _ =
      ∑ a : Idx, ∑ p : Idx,
        gInv p a *
          metricRm04At (I := I) g x (vec4 (I := I) X Y Z (basis a)) *
          metricRicciAt (I := I) g x (vec2 (I := I) (basis l) (basis p)) := by
            rw [Finset.sum_comm]
    _ =
      ∑ p : Idx, ∑ a : Idx,
        gInv p a *
          metricRicciAt (I := I) g x (vec2 (I := I) (basis l) (basis a)) *
          metricRm04At (I := I) g x (vec4 (I := I) X Y Z (basis p)) := by
            refine Finset.sum_congr rfl fun p _ => ?_
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [hsym a p]
            ring
    _ =
      ∑ p : Idx,
        (∑ a : Idx, gInv p a *
          metricRicciAt (I := I) g x (vec2 (I := I) (basis l) (basis a))) *
        metricRm04At (I := I) g x (vec4 (I := I) X Y Z (basis p)) := by
            refine Finset.sum_congr rfl fun p _ => ?_
            rw [Finset.sum_mul]

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem ricciDrift_comp
    (g : SmoothRiemannianMetric I M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx → Idx → Real)
    (hinv : MetricInverseInBasisGen (I := I) g x basis gInv)
    (i j k l : Idx) :
    Tensor0SSpace.eval (ricciDrift04 (I := I) g x)
        (vec4 (I := I) (basis i) (basis j) (basis k) (basis l)) =
      (∑ p : Idx,
        (∑ a : Idx, gInv p a *
          metricRicciAt (I := I) g x (vec2 (I := I) (basis i) (basis a))) *
        metricRm04At (I := I) g x
          (vec4 (I := I) (basis p) (basis j) (basis k) (basis l))) +
      (∑ p : Idx,
        (∑ a : Idx, gInv p a *
          metricRicciAt (I := I) g x (vec2 (I := I) (basis j) (basis a))) *
        metricRm04At (I := I) g x
          (vec4 (I := I) (basis i) (basis p) (basis k) (basis l))) +
      (∑ p : Idx,
        (∑ a : Idx, gInv p a *
          metricRicciAt (I := I) g x (vec2 (I := I) (basis k) (basis a))) *
        metricRm04At (I := I) g x
          (vec4 (I := I) (basis i) (basis j) (basis p) (basis l))) +
      (∑ p : Idx,
        (∑ a : Idx, gInv p a *
          metricRicciAt (I := I) g x (vec2 (I := I) (basis l) (basis a))) *
        metricRm04At (I := I) g x
          (vec4 (I := I) (basis i) (basis j) (basis k) (basis p))) := by
  classical
  rw [ricciDrift04, driftSlots_apply,
    ricciLow_comp (I := I) g basis gInv hinv (basis i) (basis j) (basis k) l,
    ricciLow_comp (I := I) g basis gInv hinv (basis k) (basis l) (basis j) i,
    ricciLow_comp (I := I) g basis gInv hinv (basis k) (basis l) (basis i) j,
    ricciLow_comp (I := I) g basis gInv hinv (basis i) (basis j) (basis l) k]
  have h1 : (∑ p : Idx,
      (∑ a : Idx, gInv p a *
        metricRicciAt (I := I) g x (vec2 (I := I) (basis i) (basis a))) *
      metricRm04At (I := I) g x
        (vec4 (I := I) (basis k) (basis l) (basis j) (basis p))) =
    -(∑ p : Idx,
      (∑ a : Idx, gInv p a *
        metricRicciAt (I := I) g x (vec2 (I := I) (basis i) (basis a))) *
      metricRm04At (I := I) g x
        (vec4 (I := I) (basis p) (basis j) (basis k) (basis l))) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [rm04_pair (I := I) g x (basis k) (basis l) (basis j) (basis p),
      rm04_swap12 (I := I) g x (basis j) (basis p) (basis k) (basis l)]
    ring
  have h2 : (∑ p : Idx,
      (∑ a : Idx, gInv p a *
        metricRicciAt (I := I) g x (vec2 (I := I) (basis j) (basis a))) *
      metricRm04At (I := I) g x
        (vec4 (I := I) (basis k) (basis l) (basis i) (basis p))) =
    ∑ p : Idx,
      (∑ a : Idx, gInv p a *
        metricRicciAt (I := I) g x (vec2 (I := I) (basis j) (basis a))) *
      metricRm04At (I := I) g x
        (vec4 (I := I) (basis i) (basis p) (basis k) (basis l)) := by
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [rm04_pair (I := I) g x (basis k) (basis l) (basis i) (basis p)]
  have h3 : (∑ p : Idx,
      (∑ a : Idx, gInv p a *
        metricRicciAt (I := I) g x (vec2 (I := I) (basis k) (basis a))) *
      metricRm04At (I := I) g x
        (vec4 (I := I) (basis i) (basis j) (basis l) (basis p))) =
    -(∑ p : Idx,
      (∑ a : Idx, gInv p a *
        metricRicciAt (I := I) g x (vec2 (I := I) (basis k) (basis a))) *
      metricRm04At (I := I) g x
        (vec4 (I := I) (basis i) (basis j) (basis p) (basis l))) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [rm04_swap34 (I := I) g x (basis i) (basis j) (basis l) (basis p)]
    ring
  rw [h1, h2, h3]
  ring

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem ricciDrift_low
    (g : SmoothRiemannianMetric I M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx → Idx → Real)
    (hinv : MetricInverseInBasisGen (I := I) g x basis gInv) :
    lowOfComp (I := I) g basis
        (fun i j k l =>
          (∑ p : Idx,
            (∑ a : Idx, gInv p a *
              metricRicciAt (I := I) g x (vec2 (I := I) (basis i) (basis a))) *
            metricRm04At (I := I) g x
              (vec4 (I := I) (basis p) (basis j) (basis k) (basis l))) +
          (∑ p : Idx,
            (∑ a : Idx, gInv p a *
              metricRicciAt (I := I) g x (vec2 (I := I) (basis j) (basis a))) *
            metricRm04At (I := I) g x
              (vec4 (I := I) (basis i) (basis p) (basis k) (basis l))) +
          (∑ p : Idx,
            (∑ a : Idx, gInv p a *
              metricRicciAt (I := I) g x (vec2 (I := I) (basis k) (basis a))) *
            metricRm04At (I := I) g x
              (vec4 (I := I) (basis i) (basis j) (basis p) (basis l))) +
          (∑ p : Idx,
            (∑ a : Idx, gInv p a *
              metricRicciAt (I := I) g x (vec2 (I := I) (basis l) (basis a))) *
            metricRm04At (I := I) g x
              (vec4 (I := I) (basis i) (basis j) (basis k) (basis p)))) =
      ricciDrift04 (I := I) g x := by
  apply lowOfComp_ext (I := I)
  intro i j k l
  exact ricciDrift_comp (I := I) g basis gInv hinv i j k l

end Components

end DifferentialGeometry.PDE.RicciFlow
