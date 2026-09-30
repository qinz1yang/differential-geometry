import DifferentialGeometry.Tensor.RSTensor.SlotSubstitution
import DifferentialGeometry.Geometry.Metric.OrthonormalFrame.Parseval
import DifferentialGeometry.Geometry.Metric.Duality
import DifferentialGeometry.Geometry.Metric.TensorInner.FiberNorm.Inner
import DifferentialGeometry.Geometry.Metric.TensorInner.FiberNorm.OrthonormalFrame.Tensor02
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic.Ring

open DifferentialGeometry.TensorMetric
  (fiberNormSqComponent tensorInnerPointwise tensorInnerPointwise_eq_sum_componentS_mul)
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

noncomputable section

open Bundle Manifold Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry.Analysis.Sobolev.TensorHilbert

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
theorem _root_.DifferentialGeometry.TensorMetric.multilinear_slot_pairing_le
    (g₀ : SmoothRiemannianMetric I M) (x : M) {r : ℕ} (j : Fin r)
    (Λ : TangentSpace I x →L[ℝ] TangentSpace I x)
    (hadj : ∀ a b : TangentSpace I x, g₀.inner x (Λ a) b = g₀.inner x a (Λ b))
    {κ : ℝ}
    (hbound : ∀ v : TangentSpace I x, g₀.inner x (Λ v) v ≤ κ * g₀.inner x v v)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (horth : ∀ i k, g₀.inner x (e i) (e k) = if i = k then (1 : ℝ) else 0)
    (Wm : ContinuousMultilinearMap ℝ (fun _ : Fin r ↦ TangentSpace I x) ℝ)
    (z : Fin r → TangentSpace I x) :
    (∑ a : Fin (Module.finrank ℝ E),
        Wm (Function.update z j (e a)) *
          Wm (Function.update z j (Λ (e a))))
      ≤ κ * ∑ a : Fin (Module.finrank ℝ E),
          Wm (Function.update z j (e a)) ^ 2 := by
  classical
  by_cases hdim : Module.finrank ℝ E = 0
  · let : IsEmpty (Fin (Module.finrank ℝ E)) :=
      ⟨fun i => Fin.elim0 (Fin.cast hdim i)⟩
    simp
  · let : NeZero (Module.finrank ℝ E) := ⟨hdim⟩
    set φ : TangentSpace I x →L[ℝ] ℝ :=
      (Wm.toContinuousLinearMap z j).comp
        (ContinuousLinearMap.id ℝ (TangentSpace I x)) with hφ_def
    have hφ_apply : ∀ u : TangentSpace I x,
        φ u = Wm (Function.update z j u) := by
      intro u
      rw [hφ_def, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
        ContinuousMultilinearMap.toContinuousLinearMap_apply]
    set w : TangentSpace I x :=
      DifferentialGeometry.Geometry.Operator.metricSharp
        (I := I) g₀ x φ.toLinearMap with hw_def
    have hw_inner : ∀ u : TangentSpace I x, g₀.inner x w u = φ u := by
      intro u
      rw [hw_def]
      exact DifferentialGeometry.Geometry.Operator.inner_metricSharp
        (I := I) g₀ x φ.toLinearMap u
    have hcomp : ∀ a : Fin (Module.finrank ℝ E),
        Wm (Function.update z j (e a)) = g₀.inner x w (e a) := by
      intro a
      rw [hw_inner, hφ_apply]
    have hcompΛ : ∀ a : Fin (Module.finrank ℝ E),
        Wm (Function.update z j (Λ (e a))) = g₀.inner x w (Λ (e a)) := by
      intro a
      rw [hw_inner, hφ_apply]
    have hkey : (∑ a : Fin (Module.finrank ℝ E),
          Wm (Function.update z j (e a)) *
            Wm (Function.update z j (Λ (e a)))) = g₀.inner x (Λ w) w := by
      calc
        (∑ a : Fin (Module.finrank ℝ E),
            Wm (Function.update z j (e a)) *
              Wm (Function.update z j (Λ (e a)))) =
            ∑ a : Fin (Module.finrank ℝ E),
              g₀.inner x (e a) (Λ w) * g₀.inner x (e a) w := by
                refine Finset.sum_congr rfl (fun a _ ↦ ?_)
                rw [hcomp a, hcompΛ a, g₀.symm x w (e a)]
                have ha : g₀.inner x w (Λ (e a)) = g₀.inner x (Λ w) (e a) := by
                  rw [g₀.symm x w (Λ (e a)), hadj (e a) w,
                    g₀.symm x (e a) (Λ w)]
                rw [ha, g₀.symm x (Λ w) (e a)]
                ring
        _ = g₀.inner x (Λ w) w :=
          parseval_family_inner_mul_sum (I := I) g₀ x e
            (orthonormal_tangent_expansion (I := I) (M := M) g₀ x e horth) (Λ w) w
    have hself : (∑ a : Fin (Module.finrank ℝ E),
          Wm (Function.update z j (e a)) ^ 2) = g₀.inner x w w := by
      calc
        (∑ a : Fin (Module.finrank ℝ E),
            Wm (Function.update z j (e a)) ^ 2) =
            ∑ a : Fin (Module.finrank ℝ E),
              g₀.inner x (e a) w * g₀.inner x (e a) w := by
                refine Finset.sum_congr rfl (fun a _ ↦ ?_)
                rw [hcomp a, g₀.symm x w (e a), sq]
        _ = g₀.inner x w w :=
          parseval_family_inner_mul_sum (I := I) g₀ x e
            (orthonormal_tangent_expansion (I := I) (M := M) g₀ x e horth) w w
    rw [hkey, hself]
    exact hbound w

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless]
    [T2Space M] [SigmaCompactSpace M] in
private theorem slotFib_eval_at (r : ℕ) (j : Fin r) (x : M)
    (Λ : TangentSpace I x →L[ℝ] TangentSpace I x)
    (A : Tensor0SSpace r I x) (v : Fin r → TangentSpace I x) :
    (slotInsertEndoFib r j x Λ A) v = A (Function.update v j (Λ (v j))) := by
  exact slotInsertEndoFib_apply_natural (I := I) (M := M) r j x Λ A v

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
private theorem inner_slotAt_le
    (g₀ : SmoothRiemannianMetric I M) (r : ℕ) (j : Fin r) (x : M)
    (Λ : TangentSpace I x →L[ℝ] TangentSpace I x)
    (hadj : ∀ a b : TangentSpace I x, g₀.inner x (Λ a) b = g₀.inner x a (Λ b))
    {κ : ℝ}
    (hbound : ∀ v : TangentSpace I x, g₀.inner x (Λ v) v ≤ κ * g₀.inner x v v)
    (W : TensorRSSpace 0 r I x)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (bse : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x))
    (hbse : ∀ i, bse i = e i)
    (horth : ∀ a b, g₀.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0) :
    tensorInnerPointwise g₀ 0 r x
        (TensorRSSpace.toModel W)
        (TensorRSSpace.toModel
          (show TensorRSSpace 0 r I x from
            TensorRSSpace.ofCLM ((slotInsertEndoFib r j x Λ).comp
              (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from W))))
      ≤ κ * tensorInnerPointwise g₀ 0 r x
          (TensorRSSpace.toModel W) (TensorRSSpace.toModel W) := by
  classical
  set slotW : TensorRSSpace 0 r I x :=
    TensorRSSpace.ofCLM ((slotInsertEndoFib r j x Λ).comp
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from W)) with hslotW
  set Wm : ContinuousMultilinearMap ℝ (fun _ : Fin r ↦ TangentSpace I x) ℝ :=
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from W)
      ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
        (fun k ↦ g₀.inner x (e ((Fin.elim0 : Fin 0 → Fin (Module.finrank ℝ E)) k)))))
      with hWm
  have hcompW : ∀ (K : Fin 0 → Fin (Module.finrank ℝ E))
      (J : Fin r → Fin (Module.finrank ℝ E)),
      fiberNormSqComponent (I := I) (M := M) g₀ x 0 r W
          (Module.finrank ℝ E) e K J = Wm (fun k ↦ e (J k)) := by
    intro K J
    rw [hWm]
    rfl
  have hcompSlot : ∀ (K : Fin 0 → Fin (Module.finrank ℝ E))
      (J : Fin r → Fin (Module.finrank ℝ E)),
      fiberNormSqComponent (I := I) (M := M) g₀ x 0 r slotW
          (Module.finrank ℝ E) e K J =
        Wm (Function.update (fun k ↦ e (J k)) j (Λ (e (J j)))) := by
    intro K J
    rw [hWm, hslotW]
    rw [show fiberNormSqComponent (I := I) (M := M) g₀ x 0 r
          (TensorRSSpace.ofCLM ((slotInsertEndoFib r j x Λ).comp
            (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from W)))
          (Module.finrank ℝ E) e K J =
        (slotInsertEndoFib r j x Λ
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from W)
            ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
              (fun k ↦ g₀.inner x (e (K k)))))) (fun k ↦ e (J k)) from rfl,
      slotFib_eval_at]
    rfl
  rw [tensorInnerPointwise_eq_sum_componentS_mul (I := I) (M := M) g₀ 0 r x
    e bse rfl hbse horth W slotW]
  rw [tensorInnerPointwise_eq_sum_componentS_mul (I := I) (M := M) g₀ 0 r x
    e bse rfl hbse horth W W]
  have hKcollapse : ∀ (F : (Fin 0 → Fin (Module.finrank ℝ E)) → ℝ),
      (∑ K : Fin 0 → Fin (Module.finrank ℝ E), F K) = F Fin.elim0 := by
    intro F
    rw [Finset.sum_eq_single Fin.elim0]
    · intro b _ hb
      exact absurd (Subsingleton.elim b Fin.elim0) hb
    · intro hmem
      exact absurd (Finset.mem_univ _) hmem
  rw [hKcollapse, hKcollapse]
  have hLHS : ∀ J : Fin r → Fin (Module.finrank ℝ E),
      fiberNormSqComponent (I := I) (M := M) g₀ x 0 r W
          (Module.finrank ℝ E) e Fin.elim0 J *
        fiberNormSqComponent (I := I) (M := M) g₀ x 0 r slotW
          (Module.finrank ℝ E) e Fin.elim0 J =
        Wm (fun k ↦ e (J k)) *
          Wm (Function.update (fun k ↦ e (J k)) j (Λ (e (J j)))) := by
    intro J
    rw [hcompW, hcompSlot]
  have hRHS : ∀ J : Fin r → Fin (Module.finrank ℝ E),
      fiberNormSqComponent (I := I) (M := M) g₀ x 0 r W
          (Module.finrank ℝ E) e Fin.elim0 J *
        fiberNormSqComponent (I := I) (M := M) g₀ x 0 r W
          (Module.finrank ℝ E) e Fin.elim0 J = Wm (fun k ↦ e (J k)) ^ 2 := by
    intro J
    rw [hcompW]
    ring
  rw [Finset.sum_congr rfl (fun J _ ↦ hLHS J),
    Finset.sum_congr rfl (fun J _ ↦ hRHS J)]
  set ee := Equiv.funSplitAt j (Fin (Module.finrank ℝ E)) with hee
  have hsplit : ∀ q : (Fin r → Fin (Module.finrank ℝ E)) → ℝ,
      (∑ J : Fin r → Fin (Module.finrank ℝ E), q J) =
        ∑ ρ : {i : Fin r // i ≠ j} → Fin (Module.finrank ℝ E),
          ∑ a : Fin (Module.finrank ℝ E), q (ee.symm (a, ρ)) := by
    intro q
    rw [← (Equiv.sum_comp ee.symm q), Fintype.sum_prod_type, Finset.sum_comm]
  rw [hsplit, hsplit, Finset.mul_sum]
  refine Finset.sum_le_sum (fun ρ _ ↦ ?_)
  let z : Fin r → TangentSpace I x := fun k ↦
    if hkj : k = j then 0 else e (ρ ⟨k, hkj⟩)
  have hkval : ∀ a : Fin (Module.finrank ℝ E), (ee.symm (a, ρ)) j = a := by
    intro a
    rw [hee]
    simp [Equiv.funSplitAt, Equiv.piSplitAt]
  have hcoe : ∀ (a : Fin (Module.finrank ℝ E)) (k : Fin r) (hkj : k ≠ j),
      (ee.symm (a, ρ)) k = ρ ⟨k, hkj⟩ := by
    intro a k hkj
    rw [hee]
    simp [Equiv.funSplitAt, Equiv.piSplitAt, hkj]
  have harg : ∀ a : Fin (Module.finrank ℝ E),
      (fun k ↦ e ((ee.symm (a, ρ)) k)) = Function.update z j (e a) := by
    intro a
    funext k
    by_cases hkj : k = j
    · subst k
      rw [Function.update_self, hkval]
    · rw [Function.update_of_ne hkj, hcoe a k hkj]
      simp [z, hkj]
  simpa only [harg, hkval, Function.update_idem] using
    (TensorMetric.multilinear_slot_pairing_le (I := I) (M := M) g₀ x j Λ hadj hbound e horth Wm z)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
theorem _root_.DifferentialGeometry.TensorMetric.tensorInnerPointwise_slot_insert_le
    (g₀ : SmoothRiemannianMetric I M) (r : ℕ) (j : Fin r) (x : M)
    (Λ : TangentSpace I x →L[ℝ] TangentSpace I x)
    (hadj : ∀ a b : TangentSpace I x, g₀.inner x (Λ a) b = g₀.inner x a (Λ b))
    {κ : ℝ}
    (hbound : ∀ v : TangentSpace I x, g₀.inner x (Λ v) v ≤ κ * g₀.inner x v v)
    (W : TensorRSSpace 0 r I x) :
    tensorInnerPointwise g₀ 0 r x
        (TensorRSSpace.toModel W)
        (TensorRSSpace.toModel
          (show TensorRSSpace 0 r I x from
            TensorRSSpace.ofCLM ((slotInsertEndoFib r j x Λ).comp
              (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from W))))
      ≤ κ * tensorInnerPointwise g₀ 0 r x
          (TensorRSSpace.toModel W) (TensorRSSpace.toModel W) := by
  obtain ⟨n, e, bse, hn, hbse, horth, _, _, _⟩ :=
    TensorMetric.exists_tangent_orthonormalBasis_with_norm_sum (I := I) (M := M) g₀ x
  change n = Module.finrank ℝ E at hn
  subst n
  exact inner_slotAt_le (I := I) (M := M) g₀ r j x Λ hadj hbound W e bse hbse horth

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
theorem multilinear_firstSlot_pairing_le
    (g₀ : SmoothRiemannianMetric I M) (x : M) {s : ℕ}
    (Λ : TangentSpace I x →L[ℝ] TangentSpace I x)
    (hadj : ∀ a b : TangentSpace I x, g₀.inner x (Λ a) b = g₀.inner x a (Λ b))
    {κ : ℝ}
    (hbound : ∀ v : TangentSpace I x, g₀.inner x (Λ v) v ≤ κ * g₀.inner x v v)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (horth : ∀ i j, g₀.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (Wm : ContinuousMultilinearMap ℝ (fun _ : Fin (s + 1) => TangentSpace I x) ℝ)
    (J' : Fin s → Fin (Module.finrank ℝ E)) :
    (∑ a : Fin (Module.finrank ℝ E),
        Wm (Fin.cons (e a) (fun k => e (J' k))) *
          Wm (Fin.cons (Λ (e a)) (fun k => e (J' k))))
      ≤ κ * ∑ a : Fin (Module.finrank ℝ E),
          Wm (Fin.cons (e a) (fun k => e (J' k))) ^ 2 := by
  classical
  simpa only [Fin.update_cons_zero] using
    TensorMetric.multilinear_slot_pairing_le (I := I) (M := M) g₀ x 0 Λ hadj hbound e horth Wm
      (Fin.cons (0 : TangentSpace I x) (fun k => e (J' k)))

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless]
    [T2Space M] [SigmaCompactSpace M] in
theorem slotInsertEndoFib_bundle_eval (s : ℕ) (x : M)
    (Λ : TangentSpace I x →L[ℝ] TangentSpace I x)
    (A : Tensor0SSpace (s + 1) I x) (v : Fin (s + 1) → TangentSpace I x) :
    (slotInsertEndoFib (s + 1) 0 x Λ A) v = A (Function.update v 0 (Λ (v 0))) := by
  exact slotInsertEndoFib_apply_natural (I := I) (M := M) (s + 1) 0 x Λ A v

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
theorem exists_orthoFrame_basis_E (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ (e : Fin (Module.finrank ℝ E) → TangentSpace I x)
      (bse : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x)),
      (∀ i : Fin (Module.finrank ℝ E), bse i = e i) ∧
      (∀ a b : Fin (Module.finrank ℝ E),
        g.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0) := by
  obtain ⟨n, e, bse, hn, hbse, horth, _, _, _⟩ :=
    TensorMetric.exists_tangent_orthonormalBasis_with_norm_sum (I := I) (M := M) g x
  change n = Module.finrank ℝ E at hn
  subst n
  exact ⟨e, bse, hbse, horth⟩

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
theorem tensorInnerPointwise_slotΛ_le
    (g₀ : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (Λ : TangentSpace I x →L[ℝ] TangentSpace I x)
    (hadj : ∀ a b : TangentSpace I x, g₀.inner x (Λ a) b = g₀.inner x a (Λ b))
    {κ : ℝ}
    (hbound : ∀ v : TangentSpace I x, g₀.inner x (Λ v) v ≤ κ * g₀.inner x v v)
    (W : TensorRSSpace 0 (s+1) I x)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (bse : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x))
    (hbse : ∀ i, bse i = e i)
    (horth : ∀ a b, g₀.inner x (e a) (e b) = if a = b then (1:ℝ) else 0) :
    tensorInnerPointwise g₀ 0 (s+1) x
        (TensorRSSpace.toModel W)
        (TensorRSSpace.toModel
          (show TensorRSSpace 0 (s+1) I x from
            TensorRSSpace.ofCLM ((slotInsertEndoFib (s+1) 0 x Λ).comp
              (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s+1) I x from W))))
      ≤ κ * tensorInnerPointwise g₀ 0 (s+1) x
          (TensorRSSpace.toModel W) (TensorRSSpace.toModel W) := by
  exact inner_slotAt_le
    (I := I) (M := M) g₀ (s + 1) 0 x Λ hadj hbound W e bse hbse horth

omit [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
theorem multilinear_slot0_pairing_self_adjoint
    (g₀ : SmoothRiemannianMetric I M) (x : M) {s : ℕ}
    (Λ : TangentSpace I x →L[ℝ] TangentSpace I x)
    (hadj : ∀ a b : TangentSpace I x, g₀.inner x (Λ a) b = g₀.inner x a (Λ b))
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (horth : ∀ i j, g₀.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (Am Bm : ContinuousMultilinearMap ℝ (fun _ : Fin (s + 1) => TangentSpace I x) ℝ)
    (J' : Fin s → Fin (Module.finrank ℝ E)) :
    (∑ a : Fin (Module.finrank ℝ E),
        Am (Fin.cons (e a) (fun k => e (J' k))) *
          Bm (Fin.cons (Λ (e a)) (fun k => e (J' k))))
      = ∑ a : Fin (Module.finrank ℝ E),
          Am (Fin.cons (Λ (e a)) (fun k => e (J' k))) *
            Bm (Fin.cons (e a) (fun k => e (J' k))) := by
  classical
  set φA : TangentSpace I x →L[ℝ] ℝ :=
    (Am.toContinuousLinearMap (Fin.cons (0 : TangentSpace I x) (fun k => e (J' k))) 0).comp
      (ContinuousLinearMap.id ℝ (TangentSpace I x)) with hφA_def
  have hφA_apply : ∀ u : TangentSpace I x,
      φA u = Am (Fin.cons u (fun k => e (J' k))) := by
    intro u
    rw [hφA_def, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      ContinuousMultilinearMap.toContinuousLinearMap_apply]
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp
  set φB : TangentSpace I x →L[ℝ] ℝ :=
    (Bm.toContinuousLinearMap (Fin.cons (0 : TangentSpace I x) (fun k => e (J' k))) 0).comp
      (ContinuousLinearMap.id ℝ (TangentSpace I x)) with hφB_def
  have hφB_apply : ∀ u : TangentSpace I x,
      φB u = Bm (Fin.cons u (fun k => e (J' k))) := by
    intro u
    rw [hφB_def, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      ContinuousMultilinearMap.toContinuousLinearMap_apply]
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp
  set wA : TangentSpace I x :=
    DifferentialGeometry.Geometry.Operator.metricSharp
      (I := I) g₀ x φA.toLinearMap with hwA_def
  set wB : TangentSpace I x :=
    DifferentialGeometry.Geometry.Operator.metricSharp
      (I := I) g₀ x φB.toLinearMap with hwB_def
  have hwA_inner : ∀ u : TangentSpace I x, g₀.inner x wA u = φA u := by
    intro u
    rw [hwA_def]
    exact DifferentialGeometry.Geometry.Operator.inner_metricSharp
      (I := I) g₀ x φA.toLinearMap u
  have hwB_inner : ∀ u : TangentSpace I x, g₀.inner x wB u = φB u := by
    intro u
    rw [hwB_def]
    exact DifferentialGeometry.Geometry.Operator.inner_metricSharp
      (I := I) g₀ x φB.toLinearMap u
  have hAe : ∀ a : Fin (Module.finrank ℝ E),
      Am (Fin.cons (e a) (fun k => e (J' k))) = g₀.inner x wA (e a) := by
    intro a; rw [hwA_inner, hφA_apply]
  have hAΛe : ∀ a : Fin (Module.finrank ℝ E),
      Am (Fin.cons (Λ (e a)) (fun k => e (J' k))) = g₀.inner x wA (Λ (e a)) := by
    intro a; rw [hwA_inner, hφA_apply]
  have hBe : ∀ a : Fin (Module.finrank ℝ E),
      Bm (Fin.cons (e a) (fun k => e (J' k))) = g₀.inner x wB (e a) := by
    intro a; rw [hwB_inner, hφB_apply]
  have hBΛe : ∀ a : Fin (Module.finrank ℝ E),
      Bm (Fin.cons (Λ (e a)) (fun k => e (J' k))) = g₀.inner x wB (Λ (e a)) := by
    intro a; rw [hwB_inner, hφB_apply]
  have hLHS : (∑ a : Fin (Module.finrank ℝ E),
        Am (Fin.cons (e a) (fun k => e (J' k))) *
          Bm (Fin.cons (Λ (e a)) (fun k => e (J' k))))
      = g₀.inner x (Λ wB) wA := by
    have hsum_eq : (∑ a : Fin (Module.finrank ℝ E),
          Am (Fin.cons (e a) (fun k => e (J' k))) *
            Bm (Fin.cons (Λ (e a)) (fun k => e (J' k))))
        = ∑ a : Fin (Module.finrank ℝ E),
            g₀.inner x (e a) (Λ wB) * g₀.inner x (e a) wA := by
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [hAe a, hBΛe a]
      rw [g₀.symm x wA (e a)]
      have hadj' : g₀.inner x wB (Λ (e a)) = g₀.inner x (Λ wB) (e a) := by
        rw [g₀.symm x wB (Λ (e a)), hadj (e a) wB, g₀.symm x (e a) (Λ wB)]
      rw [hadj', g₀.symm x (Λ wB) (e a)]
      ring
    rw [hsum_eq, parseval_family_inner_mul_sum (I := I) g₀ x e
          (orthonormal_tangent_expansion (I := I) (M := M) g₀ x e horth) (Λ wB) wA]
  have hRHS : (∑ a : Fin (Module.finrank ℝ E),
        Am (Fin.cons (Λ (e a)) (fun k => e (J' k))) *
          Bm (Fin.cons (e a) (fun k => e (J' k))))
      = g₀.inner x (Λ wA) wB := by
    have hsum_eq : (∑ a : Fin (Module.finrank ℝ E),
          Am (Fin.cons (Λ (e a)) (fun k => e (J' k))) *
            Bm (Fin.cons (e a) (fun k => e (J' k))))
        = ∑ a : Fin (Module.finrank ℝ E),
            g₀.inner x (e a) (Λ wA) * g₀.inner x (e a) wB := by
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [hAΛe a, hBe a]
      rw [g₀.symm x wB (e a)]
      have hadj' : g₀.inner x wA (Λ (e a)) = g₀.inner x (Λ wA) (e a) := by
        rw [g₀.symm x wA (Λ (e a)), hadj (e a) wA, g₀.symm x (e a) (Λ wA)]
      rw [hadj', g₀.symm x (Λ wA) (e a)]
    rw [hsum_eq, parseval_family_inner_mul_sum (I := I) g₀ x e
          (orthonormal_tangent_expansion (I := I) (M := M) g₀ x e horth) (Λ wA) wB]
  rw [hLHS, hRHS]
  rw [hadj wB wA, g₀.symm x wB (Λ wA)]

omit [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
theorem tensorInnerPointwise_slotΛ_self_adjoint
    (g₀ : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (Λ : TangentSpace I x →L[ℝ] TangentSpace I x)
    (hadj : ∀ a b : TangentSpace I x, g₀.inner x (Λ a) b = g₀.inner x a (Λ b))
    (A B : TensorRSSpace 0 (s + 1) I x)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (bse : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x))
    (hbse : ∀ i, bse i = e i)
    (horth : ∀ a b, g₀.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0) :
    tensorInnerPointwise g₀ 0 (s + 1) x
        (TensorRSSpace.toModel
          (show TensorRSSpace 0 (s + 1) I x from
            TensorRSSpace.ofCLM ((slotInsertEndoFib (s + 1) 0 x Λ).comp
              (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from A))))
        (TensorRSSpace.toModel B)
      = tensorInnerPointwise g₀ 0 (s + 1) x
          (TensorRSSpace.toModel A)
          (TensorRSSpace.toModel
            (show TensorRSSpace 0 (s + 1) I x from
              TensorRSSpace.ofCLM ((slotInsertEndoFib (s + 1) 0 x Λ).comp
                (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from B)))) := by
  classical
  set slotA : TensorRSSpace 0 (s + 1) I x :=
    TensorRSSpace.ofCLM ((slotInsertEndoFib (s + 1) 0 x Λ).comp
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from A)) with hslotA
  set slotB : TensorRSSpace 0 (s + 1) I x :=
    TensorRSSpace.ofCLM ((slotInsertEndoFib (s + 1) 0 x Λ).comp
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from B)) with hslotB
  set Am : ContinuousMultilinearMap ℝ (fun _ : Fin (s + 1) => TangentSpace I x) ℝ :=
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from A)
      ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
        (fun k => g₀.inner x (e ((Fin.elim0 : Fin 0 → Fin (Module.finrank ℝ E)) k))))) with hAm
  set Bm : ContinuousMultilinearMap ℝ (fun _ : Fin (s + 1) => TangentSpace I x) ℝ :=
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from B)
      ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
        (fun k => g₀.inner x (e ((Fin.elim0 : Fin 0 → Fin (Module.finrank ℝ E)) k))))) with hBm
  have hcompA : ∀ (K : Fin 0 → Fin (Module.finrank ℝ E))
    (J : Fin (s + 1) → Fin (Module.finrank ℝ E)),
      fiberNormSqComponent (I := I) (M := M) g₀ x 0 (s + 1) A (Module.finrank ℝ E) e K J
        = Am (fun k => e (J k)) := by
    intro K J; rw [hAm]; rfl
  have hcompB : ∀ (K : Fin 0 → Fin (Module.finrank ℝ E))
    (J : Fin (s + 1) → Fin (Module.finrank ℝ E)),
      fiberNormSqComponent (I := I) (M := M) g₀ x 0 (s + 1) B (Module.finrank ℝ E) e K J
        = Bm (fun k => e (J k)) := by
    intro K J; rw [hBm]; rfl
  have hcompSlotA : ∀ (K : Fin 0 → Fin (Module.finrank ℝ E))
    (J : Fin (s + 1) → Fin (Module.finrank ℝ E)),
      fiberNormSqComponent (I := I) (M := M) g₀ x 0 (s + 1) slotA (Module.finrank ℝ E) e K J
        = Am (Function.update (fun k => e (J k)) 0 (Λ (e (J 0)))) := by
    intro K J
    rw [hAm, hslotA]
    rw [show fiberNormSqComponent (I := I) (M := M) g₀ x 0 (s + 1)
          (TensorRSSpace.ofCLM ((slotInsertEndoFib (s + 1) 0 x Λ).comp
            (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from A))) (Module.finrank ℝ E)
              e K J
        = (slotInsertEndoFib (s + 1) 0 x Λ
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from A)
              ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
                (fun k => g₀.inner x (e (K k)))))) (fun k => e (J k)) from rfl,
      slotInsertEndoFib_bundle_eval]
    rfl
  have hcompSlotB : ∀ (K : Fin 0 → Fin (Module.finrank ℝ E))
    (J : Fin (s + 1) → Fin (Module.finrank ℝ E)),
      fiberNormSqComponent (I := I) (M := M) g₀ x 0 (s + 1) slotB (Module.finrank ℝ E) e K J
        = Bm (Function.update (fun k => e (J k)) 0 (Λ (e (J 0)))) := by
    intro K J
    rw [hBm, hslotB]
    rw [show fiberNormSqComponent (I := I) (M := M) g₀ x 0 (s + 1)
          (TensorRSSpace.ofCLM ((slotInsertEndoFib (s + 1) 0 x Λ).comp
            (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from B))) (Module.finrank ℝ E)
              e K J
        = (slotInsertEndoFib (s + 1) 0 x Λ
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from B)
              ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
                (fun k => g₀.inner x (e (K k)))))) (fun k => e (J k)) from rfl,
      slotInsertEndoFib_bundle_eval]
    rfl
  rw [tensorInnerPointwise_eq_sum_componentS_mul (I := I) (M := M) g₀ 0 (s + 1) x e bse rfl hbse
    horth slotA B]
  rw [tensorInnerPointwise_eq_sum_componentS_mul (I := I) (M := M) g₀ 0 (s + 1) x e bse rfl hbse
    horth A slotB]
  have hKcollapse : ∀ (F : (Fin 0 → Fin (Module.finrank ℝ E)) → ℝ),
      (∑ K : Fin 0 → Fin (Module.finrank ℝ E), F K) = F Fin.elim0 := by
    intro F
    rw [Finset.sum_eq_single Fin.elim0]
    · intro b _ hb; exact absurd (Subsingleton.elim b Fin.elim0) hb
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hKcollapse, hKcollapse]
  have hLHS : ∀ J : Fin (s + 1) → Fin (Module.finrank ℝ E),
      fiberNormSqComponent (I := I) (M := M) g₀ x 0 (s + 1) slotA (Module.finrank ℝ E) e Fin.elim0 J
        *
        fiberNormSqComponent (I := I) (M := M) g₀ x 0 (s + 1) B (Module.finrank ℝ E) e Fin.elim0 J
      = Am (Function.update (fun k => e (J k)) 0 (Λ (e (J 0)))) * Bm (fun k => e (J k)) := by
    intro J; rw [hcompSlotA, hcompB]
  have hRHS : ∀ J : Fin (s + 1) → Fin (Module.finrank ℝ E),
      fiberNormSqComponent (I := I) (M := M) g₀ x 0 (s + 1) A (Module.finrank ℝ E) e Fin.elim0 J *
        fiberNormSqComponent (I := I) (M := M) g₀ x 0 (s + 1) slotB (Module.finrank ℝ E) e Fin.elim0
          J
      = Am (fun k => e (J k)) * Bm (Function.update (fun k => e (J k)) 0 (Λ (e (J 0)))) := by
    intro J; rw [hcompSlotB, hcompA]
  rw [Finset.sum_congr rfl (fun J _ => hLHS J), Finset.sum_congr rfl (fun J _ => hRHS J)]
  have hsplit : ∀ G : (Fin (s + 1) → Fin (Module.finrank ℝ E)) → ℝ,
      (∑ J : Fin (s + 1) → Fin (Module.finrank ℝ E), G J)
        = ∑ J' : Fin s → Fin (Module.finrank ℝ E), ∑ a : Fin (Module.finrank ℝ E), G
          (Fin.cons a J') := by
    intro G
    rw [← (Fin.consEquiv (fun _ : Fin (s + 1) => Fin (Module.finrank ℝ E))).sum_comp G,
      Fintype.sum_prod_type, Finset.sum_comm]
    rfl
  rw [hsplit (fun J => Am (Function.update (fun k => e (J k)) 0 (Λ (e (J 0)))) * Bm
    (fun k => e (J k))),
    hsplit (fun J => Am (fun k => e (J k)) * Bm
      (Function.update (fun k => e (J k)) 0 (Λ (e (J 0)))))]
  refine Finset.sum_congr rfl (fun J' _ => ?_)
  have hkey := multilinear_slot0_pairing_self_adjoint (I := I) (M := M) g₀ x Λ hadj e horth Bm Am J'
  have hLHSeq : (∑ a : Fin (Module.finrank ℝ E),
        Am (Function.update (fun k => e
          ((Fin.cons a J' : Fin (s + 1) → Fin (Module.finrank ℝ E)) k)) 0
            (Λ (e ((Fin.cons a J' : Fin (s + 1) → Fin (Module.finrank ℝ E)) 0)))) *
          Bm (fun k => e ((Fin.cons a J' : Fin (s + 1) → Fin (Module.finrank ℝ E)) k)))
      = ∑ a : Fin (Module.finrank ℝ E),
          Am (Fin.cons (Λ (e a)) (fun k => e (J' k))) *
            Bm (Fin.cons (e a) (fun k => e (J' k))) := by
    refine Finset.sum_congr rfl (fun a _ => ?_)
    have h1 : (fun k => e ((Fin.cons a J' : Fin (s + 1) → Fin (Module.finrank ℝ E)) k))
        = Fin.cons (e a) (fun k => e (J' k)) := by
      funext i; rcases Fin.eq_zero_or_eq_succ i with hi|⟨j,rfl⟩
      · subst hi; simp
      · simp
    have h2 : Function.update
      (fun k => e ((Fin.cons a J' : Fin (s + 1) → Fin (Module.finrank ℝ E)) k)) 0
          (Λ (e ((Fin.cons a J' : Fin (s + 1) → Fin (Module.finrank ℝ E)) 0)))
        = Fin.cons (Λ (e a)) (fun k => e (J' k)) := by
      rw [show ((Fin.cons a J' : Fin (s + 1) → Fin (Module.finrank ℝ E)) 0) = a from rfl]
      funext i; rcases Fin.eq_zero_or_eq_succ i with hi|⟨j,rfl⟩
      · subst hi; simp
      · simp
    rw [h2, h1]
  have hRHSeq : (∑ a : Fin (Module.finrank ℝ E),
        Am (fun k => e ((Fin.cons a J' : Fin (s + 1) → Fin (Module.finrank ℝ E)) k)) *
          Bm (Function.update (fun k => e
            ((Fin.cons a J' : Fin (s + 1) → Fin (Module.finrank ℝ E)) k)) 0
            (Λ (e ((Fin.cons a J' : Fin (s + 1) → Fin (Module.finrank ℝ E)) 0)))))
      = ∑ a : Fin (Module.finrank ℝ E),
          Am (Fin.cons (e a) (fun k => e (J' k))) *
            Bm (Fin.cons (Λ (e a)) (fun k => e (J' k))) := by
    refine Finset.sum_congr rfl (fun a _ => ?_)
    have h1 : (fun k => e ((Fin.cons a J' : Fin (s + 1) → Fin (Module.finrank ℝ E)) k))
        = Fin.cons (e a) (fun k => e (J' k)) := by
      funext i; rcases Fin.eq_zero_or_eq_succ i with hi|⟨j,rfl⟩
      · subst hi; simp
      · simp
    have h2 : Function.update
      (fun k => e ((Fin.cons a J' : Fin (s + 1) → Fin (Module.finrank ℝ E)) k)) 0
          (Λ (e ((Fin.cons a J' : Fin (s + 1) → Fin (Module.finrank ℝ E)) 0)))
        = Fin.cons (Λ (e a)) (fun k => e (J' k)) := by
      rw [show ((Fin.cons a J' : Fin (s + 1) → Fin (Module.finrank ℝ E)) 0) = a from rfl]
      funext i; rcases Fin.eq_zero_or_eq_succ i with hi|⟨j,rfl⟩
      · subst hi; simp
      · simp
    rw [h2, h1]
  rw [hLHSeq, hRHSeq]
  have hkey' : (∑ a : Fin (Module.finrank ℝ E),
        Am (Fin.cons (Λ (e a)) (fun k => e (J' k))) *
          Bm (Fin.cons (e a) (fun k => e (J' k))))
      = ∑ a : Fin (Module.finrank ℝ E),
          Am (Fin.cons (e a) (fun k => e (J' k))) *
            Bm (Fin.cons (Λ (e a)) (fun k => e (J' k))) := by
    have hkeyL : (∑ a : Fin (Module.finrank ℝ E),
          Am (Fin.cons (Λ (e a)) (fun k => e (J' k))) *
            Bm (Fin.cons (e a) (fun k => e (J' k))))
        = ∑ a : Fin (Module.finrank ℝ E),
            Bm (Fin.cons (e a) (fun k => e (J' k))) *
              Am (Fin.cons (Λ (e a)) (fun k => e (J' k))) :=
      Finset.sum_congr rfl (fun a _ => mul_comm _ _)
    have hkeyR : (∑ a : Fin (Module.finrank ℝ E),
          Bm (Fin.cons (Λ (e a)) (fun k => e (J' k))) *
            Am (Fin.cons (e a) (fun k => e (J' k))))
        = ∑ a : Fin (Module.finrank ℝ E),
            Am (Fin.cons (e a) (fun k => e (J' k))) *
              Bm (Fin.cons (Λ (e a)) (fun k => e (J' k))) :=
      Finset.sum_congr rfl (fun a _ => mul_comm _ _)
    rw [hkeyL, hkey, hkeyR]
  rw [hkey']

end DifferentialGeometry.Analysis.Sobolev.TensorHilbert

end
