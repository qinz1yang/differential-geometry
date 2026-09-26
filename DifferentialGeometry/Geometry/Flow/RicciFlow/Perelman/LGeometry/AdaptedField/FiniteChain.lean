import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.AdaptedField.Existence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.AdaptedField.InnerProduct
import DifferentialGeometry.Geometry.Metric.Pullback.Local
import DifferentialGeometry.Analysis.Calculus.SmoothExtension.Curve

noncomputable section

open Bundle Set Filter
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]

section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] {D : RealTimeInterval}

private theorem exists_lAdaptedFrame_on_Icc_of_contMDiff
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (alpha : Real → M)
    (halpha : ContMDiff (modelWithCornersSelf Real Real) I ∞ alpha)
    {a b : Real} (hab : a ≤ b) {J : Set Real} (hJ : IsOpen J) (hseg : Set.Icc a b ⊆ J)
    (hreg : ∀ s ∈ J, T - s ^ 2 ∈ D.regular)
    (V : Fin (Module.finrank Real E) → TangentSpace I (alpha b))
    (hON : ∀ i j,
      (S.base.metric (T - b ^ 2)).inner (alpha b) (V i) (V j) =
        if i = j then 1 else 0) :
    ∃ (P : Fin (Module.finrank Real E) → ∀ s, TangentSpace I (alpha s)) (Ω : Set Real),
      IsOpen Ω ∧ Set.Icc a b ⊆ Ω ∧ Ω ⊆ J ∧
      (∀ i, ContMDiffOn (modelWithCornersSelf Real Real) I.tangent ∞
        (fun s : Real ↦
          (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
            (alpha s) (P i s) : TangentBundle I M)) Ω) ∧
      (∀ i, IsLAdapted S T alpha (P i) Ω) ∧
      (∀ i, P i b = V i) ∧
      ∀ s ∈ Set.Icc a b, ∀ i j,
        (S.base.metric (T - s ^ 2)).inner (alpha s) (P i s) (P j s) =
          if i = j then 1 else 0 := by
  classical
  have hex (i : Fin (Module.finrank Real E)) := by
    letI : NeZero (Module.finrank Real E) := ⟨Nat.ne_zero_of_lt i.isLt⟩
    exact exists_lAdaptedField_on_Icc S hS T alpha halpha hab hJ hseg hreg (V i)
  choose P Ωi hΩi hseg_i hsub_i hPsm_i hPb hPode_i using hex
  let Ω : Set Real := J ∩ ⋂ i, Ωi i
  have hΩ : IsOpen Ω := hJ.inter (isOpen_iInter_of_finite hΩi)
  have hsegΩ : Set.Icc a b ⊆ Ω := by
    intro s hs
    exact ⟨hseg hs, Set.mem_iInter.mpr fun i ↦ hseg_i i hs⟩
  have hsubΩ : Ω ⊆ J := inter_subset_left
  have hPsm : ∀ i, ContMDiffOn (modelWithCornersSelf Real Real) I.tangent ∞
      (fun s : Real ↦
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (alpha s) (P i s) : TangentBundle I M)) Ω := by
    intro i
    exact (hPsm_i i).mono (fun _ hs ↦ Set.mem_iInter.mp hs.2 i)
  have hPode : ∀ i, IsLAdapted S T alpha (P i) Ω := by
    intro i s hs
    exact hPode_i i s (Set.mem_iInter.mp hs.2 i)
  have hPdiff (i : Fin (Module.finrank Real E)) (s : Real) (hs : s ∈ Ω) :
      DifferentiableAt Real (chartRepAt (I := I) alpha (P i) s) s := by
    apply differentiableAt_chartRepAt_of_contMDiffAt_two (I := I)
    exact ((hPsm i s hs).contMDiffAt (hΩ.mem_nhds hs)).of_le
      (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞)))
  refine ⟨P, Ω, hΩ, hsegΩ, hsubΩ, hPsm, hPode, hPb, ?_⟩
  intro s hs i j
  rw [metric_inner_eq_of_isLAdapted S hS T alpha (P i) (P j) hs.2
    (fun r hr ↦ hreg r (hseg ⟨hs.1.trans hr.1, hr.2⟩))
    (fun _ _ ↦ halpha.mdifferentiable (by norm_num) _)
    (fun r hr ↦ hPdiff i r (hsegΩ ⟨hs.1.trans hr.1, hr.2⟩))
    (fun r hr ↦ hPdiff j r (hsegΩ ⟨hs.1.trans hr.1, hr.2⟩))
    (fun r hr ↦ hPode i r (hsegΩ ⟨hs.1.trans hr.1, hr.2⟩))
    (fun r hr ↦ hPode j r (hsegΩ ⟨hs.1.trans hr.1, hr.2⟩))]
  rw [hPb i, hPb j]
  exact hON i j

private theorem exists_lAdaptedFrame_on_Icc
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : ℝ) (alpha : ℝ → M)
    {a b : ℝ} (hab : a ≤ b) {J : Set ℝ}
    (halpha : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ alpha J)
    (hJ : IsOpen J) (hseg : Icc a b ⊆ J)
    (hreg : ∀ s ∈ J, T - s ^ 2 ∈ D.regular)
    (V : Fin (Module.finrank ℝ E) → TangentSpace I (alpha b))
    (hON : ∀ i j,
      (S.base.metric (T - b ^ 2)).inner (alpha b) (V i) (V j) = if i = j then 1 else 0) :
    ∃ (P : Fin (Module.finrank ℝ E) → ∀ s, TangentSpace I (alpha s)) (Ω : Set ℝ),
      IsOpen Ω ∧ Icc a b ⊆ Ω ∧ Ω ⊆ J ∧
      (∀ i, ContMDiffOn 𝓘(ℝ, ℝ) I.tangent ∞
        (fun s => (TotalSpace.mk' E (alpha s) (P i s) : TangentBundle I M)) Ω) ∧
      (∀ i, IsLAdapted S T alpha (P i) Ω) ∧
      (∀ i, P i b = V i) ∧
      ∀ s ∈ Icc a b, ∀ i j,
        (S.base.metric (T - s ^ 2)).inner (alpha s) (P i s) (P j s) = if i = j then 1 else 0 := by
  obtain ⟨beta, hbeta, heq⟩ := halpha.exists_extension_uIcc (a := a) (b := b) hJ
    (by simpa only [uIcc_of_le hab] using hseg)
  let K : Set ℝ := J ∩ {r | beta =ᶠ[𝓝 r] alpha}
  have hK : IsOpen K := hJ.inter isOpen_setOfPred_eventually_nhds
  have hsegK : Icc a b ⊆ K := by
    intro r hr
    exact ⟨hseg hr, heq r (by simpa only [uIcc_of_le hab] using hr)⟩
  have hbase (r : ℝ) (hr : r ∈ K) : beta r = alpha r := hr.2.self_of_nhds
  let Vbeta : Fin (Module.finrank ℝ E) → TangentSpace I (beta b) := fun i => (V i : E)
  have hONbeta : ∀ i j, (S.base.metric (T - b ^ 2)).inner (beta b) (Vbeta i) (Vbeta j) =
      if i = j then 1 else 0 := by
    intro i j
    dsimp only [Vbeta]
    rw [hbase b (hsegK ⟨hab, le_rfl⟩)]
    exact hON i j
  obtain ⟨R, Ω, hΩ, hsegΩ, hsubΩ, hRsm, hRode, hRb, hRON⟩ :=
    exists_lAdaptedFrame_on_Icc_of_contMDiff S hS T beta hbeta hab hK hsegK
      (fun r hr => hreg r hr.1) Vbeta hONbeta
  let P : Fin (Module.finrank ℝ E) → ∀ r, TangentSpace I (alpha r) := fun i r => (R i r : E)
  have hPsm : ∀ i, ContMDiffOn 𝓘(ℝ, ℝ) I.tangent ∞
      (fun r => (TotalSpace.mk' E (alpha r) (P i r) : TangentBundle I M)) Ω := by
    intro i
    apply (hRsm i).congr
    intro r hr
    change TotalSpace.mk' E (alpha r) (P i r) = TotalSpace.mk' E (beta r) (R i r)
    rw [hbase r (hsubΩ hr)]
  have hPode : ∀ i, IsLAdapted S T alpha (P i) Ω := by
    intro i r hr
    have hcov := DifferentialGeometry.Geometry.Riemannian.covDerivAlong_congr_curve
      (I := I) (S.base.metric (T - r ^ 2)) (R i) (P i) (hsubΩ hr).2
      (Filter.Eventually.of_forall fun _ => rfl)
    have hh := hRode i r hr
    change (covDerivAlong (I := I) (S.base.metric (T - r ^ 2)) alpha (P i) r : E) = _
    rw [← hcov, hh]
    change (-2 * r) • (ricciSharp (I := I) (S.base.metric (T - r ^ 2)) (beta r) (R i r) : E) = _
    rw [hbase r (hsubΩ hr)]
  refine ⟨P, Ω, hΩ, hsegΩ, fun _ hr => (hsubΩ hr).1, hPsm, hPode, ?_, ?_⟩
  · intro i
    exact hRb i
  · intro r hr i j
    have hh := hRON r hr i j
    rw [hbase r (hsubΩ (hsegΩ hr))] at hh
    exact hh


end

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_lAdaptedFrame_finite_chain_of_local_isometries
    {n : ℕ} (M : Fin (n + 1) → Type*)
    [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace H (M i)]
    [∀ i, IsManifold I ∞ (M i)] [∀ i, T2Space (M i)]
    (D : Fin (n + 1) → RealTimeInterval)
    (S : (i : Fin (n + 1)) → SolutionOn (I := I) (M := M i) (D i))
    (hS : ∀ i, IsSolutionOn (S i)) (T : ℝ)
    (t : Fin (n + 2) → ℝ) (ht : Monotone t)
    (α : (i : Fin (n + 1)) → ℝ → M i)
    (J : Fin (n + 1) → Set ℝ)
    (hα : ∀ i, ContMDiffOn 𝓘(ℝ, ℝ) I ∞ (α i) (J i))
    (hJ : ∀ i, IsOpen (J i))
    (hseg : ∀ i, Icc (t i.castSucc) (t i.succ) ⊆ J i)
    (hclock : ∀ i, ∀ r ∈ J i, T - r ^ 2 ∈ (D i).regular)
    (X : Fin n → Type*) [∀ i, TopologicalSpace (X i)] [∀ i, ChartedSpace H (X i)]
    [∀ i, IsManifold I ∞ (X i)] [∀ i, T2Space (X i)]
    (g : (i : Fin n) → SmoothRiemannianMetric I (X i))
    (x : (i : Fin n) → X i)
    (leftMap : (i : Fin n) → X i → M i.castSucc)
    (rightMap : (i : Fin n) → X i → M i.succ)
    (hleft : ∀ i, IsLocalDiffeomorph I I ∞ (leftMap i))
    (hright : ∀ i, IsLocalDiffeomorph I I ∞ (rightMap i))
    (hmetricLeft : ∀ i : Fin n, g i = localPullMetric
      ((S i.castSucc).base.metric (T - (t i.castSucc.succ) ^ 2)) (leftMap i) (hleft i))
    (hmetricRight : ∀ i : Fin n, g i = localPullMetric
      ((S i.succ).base.metric (T - (t i.castSucc.succ) ^ 2)) (rightMap i) (hright i))
    (hpointLeft : ∀ i : Fin n, α i.castSucc (t i.castSucc.succ) = leftMap i (x i))
    (hpointRight : ∀ i : Fin n, α i.succ (t i.castSucc.succ) = rightMap i (x i)) :
    ∃ (P : (i : Fin (n + 1)) → Fin (Module.finrank ℝ E) → ∀ r, TangentSpace I (α i r))
      (Ω : Fin (n + 1) → Set ℝ),
      (∀ i, IsOpen (Ω i) ∧ Icc (t i.castSucc) (t i.succ) ⊆ Ω i ∧ Ω i ⊆ J i) ∧
      (∀ i k, ContMDiffOn 𝓘(ℝ, ℝ) I.tangent ∞
        (fun r => (TotalSpace.mk' E (α i r) (P i k r) : TangentBundle I (M i))) (Ω i)) ∧
      (∀ i k, IsLAdapted (S i) T (α i) (P i k) (Ω i)) ∧
      (∀ i, ∀ r ∈ Icc (t i.castSucc) (t i.succ), ∀ k l,
        ((S i).base.metric (T - r ^ 2)).inner (α i r) (P i k r) (P i l r) =
          if k = l then 1 else 0) ∧
      (∀ i : Fin n, ∀ k,
        P i.castSucc k (t i.castSucc.succ) =
          mfderiv I I (leftMap i) (x i)
            (((hright i).mfderivToContinuousLinearEquiv (by simp) (x i)).symm
              (P i.succ k (t i.castSucc.succ)))) := by
  classical
  let Frame (i : Fin (n + 1)) :=
    {F : (Fin (Module.finrank ℝ E) → ∀ r, TangentSpace I (α i r)) × Set ℝ //
      IsOpen F.2 ∧ Icc (t i.castSucc) (t i.succ) ⊆ F.2 ∧ F.2 ⊆ J i ∧
      (∀ k, ContMDiffOn 𝓘(ℝ, ℝ) I.tangent ∞
        (fun r => (TotalSpace.mk' E (α i r) (F.1 k r) : TangentBundle I (M i))) F.2) ∧
      (∀ k, IsLAdapted (S i) T (α i) (F.1 k) F.2) ∧
      ∀ r ∈ Icc (t i.castSucc) (t i.succ), ∀ k l,
        ((S i).base.metric (T - r ^ 2)).inner (α i r) (F.1 k r) (F.1 l r) = if k = l then 1 else 0}
  have build (i : Fin (n + 1)) (V : Fin (Module.finrank ℝ E) → TangentSpace I (α i (t i.succ)))
      (hV : ∀ k l, ((S i).base.metric (T - (t i.succ) ^ 2)).inner (α i (t i.succ))
        (V k) (V l) = if k = l then 1 else 0) :
      ∃ F : Frame i, ∀ k, F.val.1 k (t i.succ) = V k := by
    obtain ⟨P, Ω, hΩ, hseg', hsub, hPsm, hDP, hPV, hON⟩ := exists_lAdaptedFrame_on_Icc
      (S i) (hS i) T (α i) (ht i.castSucc_le_succ) (hα i) (hJ i) (hseg i) (hclock i) V hV
    exact ⟨⟨(P, Ω), hΩ, hseg', hsub, hPsm, hDP, hON⟩, hPV⟩
  let back (i : Fin n) (v : TangentSpace I (α i.succ (t i.castSucc.succ))) :
      TangentSpace I (α i.castSucc (t i.castSucc.succ)) :=
    mfderiv I I (leftMap i) (x i)
      (((hright i).mfderivToContinuousLinearEquiv (by simp) (x i)).symm v)
  have hbackON (i : Fin n) (F : Frame i.succ) :
      ∀ k l, ((S i.castSucc).base.metric (T - (t i.castSucc.succ) ^ 2)).inner
        (α i.castSucc (t i.castSucc.succ))
        (back i (F.val.1 k (t i.castSucc.succ))) (back i (F.val.1 l (t i.castSucc.succ))) =
          if k = l then 1 else 0 := by
    intro k l
    have htime : i.succ.castSucc = i.castSucc.succ := Fin.ext rfl
    have hON := F.property.2.2.2.2.2 (t i.castSucc.succ)
      ⟨by rw [← htime], by simpa only [htime] using ht i.succ.castSucc_le_succ⟩ k l
    let A := (hright i).mfderivToContinuousLinearEquiv (by simp) (x i)
    have hAk : mfderiv I I (rightMap i) (x i) (A.symm (F.val.1 k (t i.castSucc.succ))) =
        F.val.1 k (t i.castSucc.succ) := A.apply_symm_apply _
    have hAl : mfderiv I I (rightMap i) (x i) (A.symm (F.val.1 l (t i.castSucc.succ))) =
        F.val.1 l (t i.castSucc.succ) := A.apply_symm_apply _
    dsimp only [back]
    rw [hpointLeft i, ← localPullMetric_inner _ _ (hleft i), ← hmetricLeft i, hmetricRight i,
      localPullMetric_inner, hAk, hAl, ← hpointRight i]
    exact hON
  let step (i : Fin n) (F : Frame i.succ) : Frame i.castSucc :=
    (build i.castSucc (fun k => back i (F.val.1 k (t i.castSucc.succ))) (hbackON i F)).choose
  have hstep (i : Fin n) (F : Frame i.succ) (k : Fin (Module.finrank ℝ E)) :
      (step i F).val.1 k (t i.castSucc.succ) = back i (F.val.1 k (t i.castSucc.succ)) :=
    (build i.castSucc (fun k => back i (F.val.1 k (t i.castSucc.succ))) (hbackON i F)).choose_spec k
  obtain ⟨basis, hON⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis
    ((S (Fin.last n)).base.metric (T - (t (Fin.last n).succ) ^ 2)) (α (Fin.last n) (t (Fin.last n).succ))
  let terminal : Frame (Fin.last n) := (build (Fin.last n) basis hON).choose
  let frames : (i : Fin (n + 1)) → Frame i := Fin.reverseInduction terminal step
  have hframes (i : Fin n) : frames i.castSucc = step i (frames i.succ) :=
    Fin.reverseInduction_castSucc i
  refine ⟨fun i => (frames i).val.1, fun i => (frames i).val.2, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact ⟨(frames i).property.1, (frames i).property.2.1, (frames i).property.2.2.1⟩
  · intro i
    exact (frames i).property.2.2.2.1
  · intro i
    exact (frames i).property.2.2.2.2.1
  · intro i
    exact (frames i).property.2.2.2.2.2
  · intro i k
    have hh := congrArg (fun F : Frame i.castSucc => F.val.1 k (t i.castSucc.succ)) (hframes i)
    exact hh.trans (hstep i (frames i.succ) k)

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
