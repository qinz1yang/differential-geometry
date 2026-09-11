import DifferentialGeometry.Geometry.Metric.JoinJets
import DifferentialGeometry.Bundle.Section

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Connection
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Geometry.Metric
section General
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] in
private theorem mvfderiv_opens_inclusion {U V : TopologicalSpace.Opens M} (hVU : V ≤ U)
    (f : U → ℝ) (hf : MDifferentiable I 𝓘(ℝ) f) (x : V) (v : TangentSpace I x) :
    mvfderiv I (fun y : V => f (TopologicalSpace.Opens.inclusion hVU y)) x v =
      mvfderiv I f (TopologicalSpace.Opens.inclusion hVU x) v := by
  have hc := mfderiv_comp_apply x (hf _)
    ((contMDiff_inclusion (I := I) (n := ∞) hVU).mdifferentiable (by simp) x) v
  rw [mfderiv_opens_incl (I := I) hVU x] at hc
  exact congrArg (NormedSpace.fromTangentSpace (f (TopologicalSpace.Opens.inclusion hVU x))) hc

private theorem metricCovDeriv_succ_global_slots
    (U : TopologicalSpace.Opens M) (h : SmoothRiemannianMetric I U)
    (gRef : SmoothRiemannianMetric I M) (m : ℕ)
    (X : ContMDiffSection I E ∞ (TangentSpace I : M → Type _))
    (W : Fin (m + 2) → ContMDiffSection I E ∞ (TangentSpace I : M → Type _)) (x : U) :
    metricCovDeriv h (gRef.restrictOpen U) (m + 1) x
      (Fin.cons (X (x : M)) (fun i => W i (x : M))) =
    mvfderiv I (fun y : U => metricCovDeriv h (gRef.restrictOpen U) m y
      (fun i => W i (y : M))) x (X (x : M)) -
      ∑ i : Fin (m + 2), metricCovDeriv h (gRef.restrictOpen U) m x
        (Function.update (fun j => W j (x : M)) i
          (leviCivitaConnectionOfMetric gRef (fun y => W i y) (x : M) (X (x : M)))) := by
  have hs := metricCovDeriv_succ_eval_smooth_slots h (gRef.restrictOpen U) m
    (restrictOpenTangentSection U X) (fun i => restrictOpenTangentSection U (W i)) x
  simp only [restrictOpenTangentSection_apply] at hs
  refine hs.trans (congrArg (fun z : ℝ =>
    mvfderiv I (fun y : U => metricCovDeriv h (gRef.restrictOpen U) m y
      (fun i => W i (y : M))) x (X (x : M)) - z) ?_)
  apply Finset.sum_congr rfl
  intro i _
  have hc := metricCov_restrictOpen_globalSection gRef U (W i) x (X (x : M))
  have hfield : restrictOpenTangentField U (fun y : M => W i y) =
      (fun y : U => W i (y : M)) := by
    funext y
    exact restrictOpenTangentField_apply U (fun y : M => W i y) y
  rw [hfield] at hc
  simp only [metricCov] at hc
  exact congrArg (fun v : TangentSpace I x =>
    metricCovDeriv h (gRef.restrictOpen U) m x
      (Function.update (fun j => W j (x : M)) i v)) hc

theorem metricCovDeriv_restrictSubset_ref_apply
    {U V : TopologicalSpace.Opens M} (hVU : V ≤ U)
    (h : SmoothRiemannianMetric I U) (gRef : SmoothRiemannianMetric I M) (m : ℕ)
    (x : V) (slots : Fin (m + 2) → TangentSpace I x) :
    metricCovDeriv (h.restrictOpenOfSubset hVU) (gRef.restrictOpen V) m x slots =
      metricCovDeriv h (gRef.restrictOpen U) m (TopologicalSpace.Opens.inclusion hVU x) slots := by
  classical
  induction m generalizing x with
  | zero => rfl
  | succ m ih =>
      obtain ⟨X, hX⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
        (V := TangentSpace I) (n := (⊤ : ℕ∞)) (x : M) (slots 0)
      choose W hW using fun i : Fin (m + 2) => ContMDiffSection.exists_eq_at
        (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) (x : M) (slots i.succ)
      have hslots : Fin.cons (X (x : M)) (fun i => W i (x : M)) = slots := by
        ext i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact hX
        · exact hW j
      rw [← hslots]
      have hleft := metricCovDeriv_succ_global_slots V (h.restrictOpenOfSubset hVU)
        gRef m X W x
      have hright := metricCovDeriv_succ_global_slots U h gRef m X W
        (TopologicalSpace.Opens.inclusion hVU x)
      refine hleft.trans (Eq.trans ?_ hright.symm)
      apply congrArg₂ (· - ·)
      · have heq : (fun y : V => metricCovDeriv (h.restrictOpenOfSubset hVU)
              (gRef.restrictOpen V) m y (fun i => W i (y : M))) =
            (fun y : V => metricCovDeriv h (gRef.restrictOpen U) m
              (TopologicalSpace.Opens.inclusion hVU y) (fun i => W i (y : M))) := by
          funext y
          exact ih y _
        rw [heq]
        apply mvfderiv_opens_inclusion hVU
          (fun y : U => metricCovDeriv h (gRef.restrictOpen U) m y
            (fun i => W i (y : M))) ?_ x (X (x : M))
        intro y
        simpa only [restrictOpenTangentSection_apply] using
          (Tensor0SBundle.tensor0SField_eval_smooth_slots_contMDiffAt
            (metricCovDeriv h (gRef.restrictOpen U) m)
            (fun i => restrictOpenTangentSection U (W i)) y).mdifferentiableAt (by simp)
      · apply Finset.sum_congr rfl
        intro i _
        exact ih x _
end General

section Cylinder
variable {E H N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T2Space N]

theorem metricCovDeriv_local_extensions_eq_on_halfOpen_cylinder
    (A : ℝ) (b : ∀ y : N × ℝ, TangentSpace (I.prod 𝓘(ℝ)) y →L[ℝ]
      TangentSpace (I.prod 𝓘(ℝ)) y →L[ℝ] ℝ)
    (gRef : SmoothRiemannianMetric (I.prod 𝓘(ℝ)) (N × ℝ))
    (U V : TopologicalSpace.Opens (N × ℝ))
    (hU : SmoothRiemannianMetric (I.prod 𝓘(ℝ)) U)
    (hV : SmoothRiemannianMetric (I.prod 𝓘(ℝ)) V)
    (heqU : ∀ y : U, (y : N × ℝ).2 ∈ Ioc (-A) 0 →
      ∀ v w : TangentSpace (I.prod 𝓘(ℝ)) y, hU.inner y v w = b (y : N × ℝ) v w)
    (heqV : ∀ y : V, (y : N × ℝ).2 ∈ Ioc (-A) 0 →
      ∀ v w : TangentSpace (I.prod 𝓘(ℝ)) y, hV.inner y v w = b (y : N × ℝ) v w)
    (q : N × ℝ) (hqU : q ∈ U) (hqV : q ∈ V) (hq : q.2 ∈ Ioc (-A) 0)
    (m : ℕ) (slots : Fin (m + 2) → TangentSpace (I.prod 𝓘(ℝ)) q) :
    metricCovDeriv hU (gRef.restrictOpen U) m ⟨q, hqU⟩ slots =
      metricCovDeriv hV (gRef.restrictOpen V) m ⟨q, hqV⟩ slots := by
  let W : TopologicalSpace.Opens (N × ℝ) := U ⊓ V
  let x : W := ⟨q, hqU, hqV⟩
  let kU := hU.restrictOpenOfSubset (show W ≤ U from inf_le_left)
  let kV := hV.restrictOpenOfSubset (show W ≤ V from inf_le_right)
  let O : TopologicalSpace.Opens W :=
    ⟨{y : W | (y : N × ℝ).2 ∈ Ioo (-A) 0},
      isOpen_Ioo.preimage (continuous_snd.comp continuous_subtype_val)⟩
  have hopen : IsOpenMap (fun y : W => (y : N × ℝ).2) :=
    isOpenMap_snd.comp W.isOpen.isOpenEmbedding_subtypeVal.isOpenMap
  have hqcl : q.2 ∈ closure (Ioo (-A) 0) := by
    rw [closure_Ioo (ne_of_lt (lt_of_lt_of_le hq.1 hq.2))]
    exact ⟨hq.1.le, hq.2⟩
  have hxcl : x ∈ closure (O : Set W) := by
    exact hopen.preimage_closure_subset_closure_preimage (s := Ioo (-A) 0)
      (show (x : N × ℝ).2 ∈ closure (Ioo (-A) 0) from hqcl)
  have heq : ∀ y : W, y ∈ O → ∀ v w : TangentSpace (I.prod 𝓘(ℝ)) y,
      kU.inner y v w = kV.inner y v w := by
    intro y hy v w
    exact (heqU (TopologicalSpace.Opens.inclusion inf_le_left y)
      ⟨hy.1, hy.2.le⟩ v w).trans
      (heqV (TopologicalSpace.Opens.inclusion inf_le_right y) ⟨hy.1, hy.2.le⟩ v w).symm
  have hj := metricCovDeriv_eq_of_eqOn_open_closure kU kV (gRef.restrictOpen W)
    O heq x hxcl m
  have hslots := congrArg (fun C => C slots) hj
  exact (metricCovDeriv_restrictSubset_ref_apply inf_le_left hU gRef m x slots).symm.trans
    (hslots.trans (metricCovDeriv_restrictSubset_ref_apply inf_le_right hV gRef m x slots))
end Cylinder
end DifferentialGeometry.Geometry.Metric
