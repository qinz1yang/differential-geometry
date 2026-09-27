import DifferentialGeometry.Geometry.Comparison.Variation.EndpointAccelerationGerm
import DifferentialGeometry.Geometry.Curvature.Bounds.ScalarNorm
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.LocalCross
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.FirstVariation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.AdaptedField.Existence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.AdaptedField.InnerProduct
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Geodesic.Congruence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Hamilton.TraceIntegral
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Index.AdaptedCutoffTrace
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Index.Algebra
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Index.Integrability
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Index.MinimizerNonnegativity
import DifferentialGeometry.Geometry.Comparison.Variation.EndpointAccelerationSum
import DifferentialGeometry.Geometry.Comparison.Variation.Field.PrescribedEndpoints
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.LagrangianRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.AdaptedField.ExistenceIcc
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Hamilton.TraceIntegralGeodesic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Index.MinimizerNonnegativitySum
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Set Bundle Filter MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open scoped _root_.Manifold ContDiff _root_.Topology BigOperators

universe uM uE uH

private theorem exists_compatible_lAdapted_frames
    {n : ℕ} {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {H : Type uH} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Fin (n + 1) → Type uM} [∀ i, TopologicalSpace (M i)]
    [∀ i, ChartedSpace H (M i)] [∀ i, IsManifold I ∞ (M i)] [∀ i, T2Space (M i)]
    {D : Fin (n + 1) → RealTimeInterval}
    (S : (i : Fin (n + 1)) → SolutionOn (I := I) (M := M i) (D i))
    (hS : ∀ i, IsSolutionOn (S i)) (T : ℝ)
    (alpha : (i : Fin (n + 1)) → ℝ → M i)
    (halpha : ∀ i, ContMDiff 𝓘(ℝ, ℝ) I ∞ (alpha i))
    (a b lo hi : Fin (n + 1) → ℝ)
    (hlo : ∀ i, lo i < a i) (hab : ∀ i, a i ≤ b i) (hhi : ∀ i, b i < hi i)
    (hreg : ∀ i, ∀ r ∈ Ioo (lo i) (hi i), T - r ^ 2 ∈ (D i).regular)
    (Phi : (i : Fin n) → TangentSpace I (alpha i.castSucc (b i.castSucc)) ≃ₗ[ℝ]
      TangentSpace I (alpha i.succ (a i.succ)))
    (hPhi : ∀ i V W,
      ((S i.succ).base.metric (T - (a i.succ) ^ 2)).inner (alpha i.succ (a i.succ))
        (Phi i V) (Phi i W) =
      ((S i.castSucc).base.metric (T - (b i.castSucc) ^ 2)).inner
        (alpha i.castSucc (b i.castSucc)) V W)
    (V : Fin (Module.finrank ℝ E) → TangentSpace I (alpha (Fin.last n) (b (Fin.last n))))
    (hV : ∀ k l,
      ((S (Fin.last n)).base.metric (T - (b (Fin.last n)) ^ 2)).inner
        (alpha (Fin.last n) (b (Fin.last n))) (V k) (V l) = if k = l then 1 else 0) :
    ∃ (P : (i : Fin (n + 1)) → Fin (Module.finrank ℝ E) → ∀ r, TangentSpace I (alpha i r))
      (Omega : Fin (n + 1) → Set ℝ),
      (∀ i, IsOpen (Omega i) ∧ Icc (a i) (b i) ⊆ Omega i ∧ Omega i ⊆ Ioo (lo i) (hi i)) ∧
      (∀ i k, ContMDiffOn 𝓘(ℝ, ℝ) I.tangent ∞
        (fun r => (TotalSpace.mk' E (E := (TangentSpace I : M i → Type _))
          (alpha i r) (P i k r) : TangentBundle I (M i))) (Omega i)) ∧
      (∀ i k, IsLAdapted (S i) T (alpha i) (P i k) (Omega i)) ∧
      (∀ k, P (Fin.last n) k (b (Fin.last n)) = V k) ∧
      (∀ i k, Phi i (P i.castSucc k (b i.castSucc)) = P i.succ k (a i.succ)) ∧
      ∀ i r, r ∈ Icc (a i) (b i) → ∀ k l,
        ((S i).base.metric (T - r ^ 2)).inner (alpha i r) (P i k r) (P i l r) =
          if k = l then 1 else 0 := by
  classical
  by_cases hdim : Module.finrank ℝ E = 0
  · have hempty (k : Fin (Module.finrank ℝ E)) : False := by
      have hk := k.isLt
      omega
    refine ⟨fun _ _ _ => 0, fun i => Ioo (lo i) (hi i), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      exact ⟨isOpen_Ioo, fun r hr => ⟨(hlo i).trans_le hr.1, hr.2.trans_lt (hhi i)⟩, Subset.rfl⟩
    · intro i k
      exact (hempty k).elim
    · intro i k
      exact (hempty k).elim
    · intro k
      exact (hempty k).elim
    · intro i k
      exact (hempty k).elim
    · intro i r hr k l
      exact (hempty k).elim
  let : NeZero (Module.finrank ℝ E) := ⟨hdim⟩
  have hex (i : Fin (n + 1)) (W : TangentSpace I (alpha i (b i))) :=
    exists_lAdaptedField_on_Icc (S i) (hS i) T (alpha i) (halpha i)
      (hab i) isOpen_Ioo
      (fun r hr => ⟨(hlo i).trans_le hr.1, hr.2.trans_lt (hhi i)⟩) (hreg i) W
  choose field dom hdomOpen hdomIcc hdomSub hfieldSmooth hfieldEnd hfieldAdapt using hex
  let P : (i : Fin (n + 1)) → Fin (Module.finrank ℝ E) →
      ∀ r, TangentSpace I (alpha i r) := fun i k =>
    Fin.reverseInduction (motive := fun i => ∀ r, TangentSpace I (alpha i r))
      (field (Fin.last n) (V k))
      (fun j next => field j.castSucc ((Phi j).symm (next (a j.succ)))) i
  have hPlast (k : Fin (Module.finrank ℝ E)) :
      P (Fin.last n) k = field (Fin.last n) (V k) := by
    simp only [P, Fin.reverseInduction_last]
  have hPold (i : Fin n) (k : Fin (Module.finrank ℝ E)) :
      P i.castSucc k = field i.castSucc ((Phi i).symm (P i.succ k (a i.succ))) := by
    simp only [P, Fin.reverseInduction_castSucc]
  let target (i : Fin (n + 1)) (k : Fin (Module.finrank ℝ E)) :
      TangentSpace I (alpha i (b i)) :=
    Fin.lastCases (motive := fun i => TangentSpace I (alpha i (b i)))
      (V k) (fun j => (Phi j).symm (P j.succ k (a j.succ))) i
  have hPeq (i : Fin (n + 1)) (k : Fin (Module.finrank ℝ E)) :
      P i k = field i (target i k) := by
    cases i using Fin.lastCases with
    | last => simpa only [target, Fin.lastCases_last] using hPlast k
    | cast i => simpa only [target, Fin.lastCases_castSucc] using hPold i k
  let Omega (i : Fin (n + 1)) : Set ℝ := ⋂ k, dom i (target i k)
  have hOmOpen (i : Fin (n + 1)) : IsOpen (Omega i) :=
    isOpen_iInter_of_finite fun k => hdomOpen i (target i k)
  have hOmIcc (i : Fin (n + 1)) : Icc (a i) (b i) ⊆ Omega i := by
    intro r hr
    exact mem_iInter.mpr fun k => hdomIcc i (target i k) hr
  have hOmDom (i : Fin (n + 1)) (k : Fin (Module.finrank ℝ E)) :
      Omega i ⊆ dom i (target i k) := fun _ hr => mem_iInter.mp hr k
  have hOmSub (i : Fin (n + 1)) : Omega i ⊆ Ioo (lo i) (hi i) :=
    (hOmDom i ⟨0, Nat.pos_of_ne_zero hdim⟩).trans (hdomSub i _)
  have hPsmooth (i : Fin (n + 1)) (k : Fin (Module.finrank ℝ E)) :
      ContMDiffOn 𝓘(ℝ, ℝ) I.tangent ∞
        (fun r => (TotalSpace.mk' E (E := (TangentSpace I : M i → Type _))
          (alpha i r) (P i k r) : TangentBundle I (M i))) (Omega i) := by
    rw [hPeq]
    exact (hfieldSmooth i (target i k)).mono (hOmDom i k)
  have hPadapt (i : Fin (n + 1)) (k : Fin (Module.finrank ℝ E)) :
      IsLAdapted (S i) T (alpha i) (P i k) (Omega i) := by
    rw [hPeq]
    exact fun r hr => hfieldAdapt i (target i k) r (hOmDom i k hr)
  have hPend (k : Fin (Module.finrank ℝ E)) : P (Fin.last n) k (b (Fin.last n)) = V k := by
    rw [hPlast]
    exact hfieldEnd _ _
  have hmatch (i : Fin n) (k : Fin (Module.finrank ℝ E)) :
      Phi i (P i.castSucc k (b i.castSucc)) = P i.succ k (a i.succ) := by
    rw [hPold, hfieldEnd]
    exact (Phi i).apply_symm_apply _
  have hdiff (i : Fin (n + 1)) (k : Fin (Module.finrank ℝ E))
      (r : ℝ) (hr : r ∈ Icc (a i) (b i)) :
      DifferentiableAt ℝ (chartRepAt (I := I) (alpha i) (P i k) r) r :=
    differentiableAt_chartRepAt_of_contMDiffAt_two
      (((hPsmooth i k).contMDiffAt ((hOmOpen i).mem_nhds (hOmIcc i hr))).of_le
        (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)))
  have hinner (i : Fin (n + 1)) (r : ℝ) (hr : r ∈ Icc (a i) (b i))
      (k l : Fin (Module.finrank ℝ E)) :
      ((S i).base.metric (T - r ^ 2)).inner (alpha i r) (P i k r) (P i l r) =
        ((S i).base.metric (T - (b i) ^ 2)).inner (alpha i (b i))
          (P i k (b i)) (P i l (b i)) := by
    have hsub : Icc r (b i) ⊆ Icc (a i) (b i) := Icc_subset_Icc_left hr.1
    exact metric_inner_eq_of_isLAdapted (S i) (hS i) T (alpha i) (P i k) (P i l) hr.2
      (fun t ht => hreg i t (hOmSub i (hOmIcc i (hsub ht))))
      (fun t _ => (halpha i).mdifferentiableAt (by simp))
      (fun t ht => hdiff i k t (hsub ht)) (fun t ht => hdiff i l t (hsub ht))
      (fun t ht => hPadapt i k t (hOmIcc i (hsub ht)))
      (fun t ht => hPadapt i l t (hOmIcc i (hsub ht)))
  refine ⟨P, Omega, fun i => ⟨hOmOpen i, hOmIcc i, hOmSub i⟩,
    hPsmooth, hPadapt, hPend, hmatch, ?_⟩
  intro i
  induction i using Fin.reverseInduction with
  | last =>
    intro r hr k l
    rw [hinner _ r hr k l, hPend k, hPend l]
    exact hV k l
  | cast i ih =>
    intro r hr k l
    rw [hinner _ r hr k l, ← hPhi i, hmatch i k, hmatch i l]
    exact ih _ ⟨le_rfl, hab i.succ⟩ k l

private theorem exists_compatible_variations_of_lAdapted_frames
    {n : ℕ} {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {H : Type uH} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Fin (n + 1) → Type uM} [∀ i, TopologicalSpace (M i)]
    [∀ i, ChartedSpace H (M i)] [∀ i, IsManifold I ∞ (M i)] [∀ i, T2Space (M i)]
    {D : Fin (n + 1) → RealTimeInterval}
    (S : (i : Fin (n + 1)) → SolutionOn (I := I) (M := M i) (D i))
    (hS : ∀ i, IsSolutionOn (S i)) (T : ℝ)
    (alpha : (i : Fin (n + 1)) → ℝ → M i)
    (halpha : ∀ i, ContMDiff 𝓘(ℝ, ℝ) I ∞ (alpha i))
    (a b lo hi : Fin (n + 1) → ℝ)
    (hlo : ∀ i, lo i < a i) (hab : ∀ i, a i < b i) (hhi : ∀ i, b i < hi i)
    (hadj : ∀ i : Fin n, b i.castSucc = a i.succ)
    (hreg : ∀ i, ∀ r ∈ Ioo (lo i) (hi i), T - r ^ 2 ∈ (D i).regular)
    (F : (i : Fin n) → PartialDiffeomorph I I (M i.castSucc) (M i.succ) ∞)
    (hsource : ∀ i, alpha i.castSucc (b i.castSucc) ∈ (F i).source)
    (hpoint : ∀ i, F i (alpha i.castSucc (b i.castSucc)) = alpha i.succ (a i.succ))
    (hmetric : ∀ i X Y,
      ((S i.succ).base.metric (T - (a i.succ) ^ 2)).inner
        (F i (alpha i.castSucc (b i.castSucc)))
        (mfderiv I I (F i : M i.castSucc → M i.succ) (alpha i.castSucc (b i.castSucc)) X)
        (mfderiv I I (F i : M i.castSucc → M i.succ) (alpha i.castSucc (b i.castSucc)) Y) =
      ((S i.castSucc).base.metric (T - (b i.castSucc) ^ 2)).inner
        (alpha i.castSucc (b i.castSucc)) X Y)
    (V : Fin (Module.finrank ℝ E) → TangentSpace I (alpha (Fin.last n) (b (Fin.last n))))
    (hV : ∀ k l,
      ((S (Fin.last n)).base.metric (T - (b (Fin.last n)) ^ 2)).inner
        (alpha (Fin.last n) (b (Fin.last n))) (V k) (V l) = if k = l then 1 else 0) :
    a 0 < b (Fin.last n) ∧
    ∃ (P : (i : Fin (n + 1)) → Fin (Module.finrank ℝ E) → ∀ r, TangentSpace I (alpha i r))
      (Omega : Fin (n + 1) → Set ℝ),
      (∀ i, IsOpen (Omega i) ∧ Icc (a i) (b i) ⊆ Omega i ∧ Omega i ⊆ Ioo (lo i) (hi i)) ∧
      (∀ i k, ContMDiffOn 𝓘(ℝ, ℝ) I.tangent ∞
        (fun r => (TotalSpace.mk' E (E := (TangentSpace I : M i → Type _))
          (alpha i r) (P i k r) : TangentBundle I (M i))) (Omega i)) ∧
      (∀ i k, IsLAdapted (S i) T (alpha i) (P i k) (Omega i)) ∧
      (∀ k, P (Fin.last n) k (b (Fin.last n)) = V k) ∧
      (∀ i k,
        mfderiv I I (F i : M i.castSucc → M i.succ) (alpha i.castSucc (b i.castSucc))
          (P i.castSucc k (b i.castSucc)) = P i.succ k (a i.succ)) ∧
      (∀ i r, r ∈ Icc (a i) (b i) → ∀ k l,
        ((S i).base.metric (T - r ^ 2)).inner (alpha i r) (P i k r) (P i l r) =
          if k = l then 1 else 0) ∧
      ∀ k : Fin (Module.finrank ℝ E), ∃ f : (i : Fin (n + 1)) → ℝ → ℝ → M i,
        (∀ i, IsSmoothVariation (I := I) (f i)) ∧
        (∀ i t, t ∈ Icc (a i) (b i) → f i 0 =ᶠ[𝓝 t] alpha i) ∧
        (∀ i t, t ∈ Icc (a i) (b i) →
          (fun r => (mfderiv 𝓘(ℝ, ℝ) I (fun e => f i e r) 0 1 : E)) =ᶠ[𝓝 t]
            (fun r => ((r - a 0) / (b (Fin.last n) - a 0)) • P i k r)) ∧
        (∀ᶠ e in 𝓝 (0 : ℝ), f 0 e (a 0) = alpha 0 (a 0)) ∧
        ∀ᶠ e in 𝓝 (0 : ℝ), ∀ i : Fin n,
          f i.castSucc e (b i.castSucc) ∈ (F i).source ∧
          F i (f i.castSucc e (b i.castSucc)) = f i.succ e (a i.succ) := by
  classical
  have hspan (i : Fin (n + 1)) : a i < b (Fin.last n) := by
    induction i using Fin.reverseInduction with
    | last => exact hab _
    | cast i ih => exact (hab i.castSucc).trans ((hadj i).trans_lt ih)
  let Phi (i : Fin n) : TangentSpace I (alpha i.castSucc (b i.castSucc)) ≃ₗ[ℝ]
      TangentSpace I (alpha i.succ (a i.succ)) :=
    ((F i).isLocalDiffeomorphAt I I ∞ (hsource i)).mfderivToContinuousLinearEquiv
      (by simp) |>.toLinearEquiv
  have hPhi (i : Fin n) (X Y : TangentSpace I (alpha i.castSucc (b i.castSucc))) :
      ((S i.succ).base.metric (T - (a i.succ) ^ 2)).inner (alpha i.succ (a i.succ))
        (Phi i X) (Phi i Y) =
      ((S i.castSucc).base.metric (T - (b i.castSucc) ^ 2)).inner
        (alpha i.castSucc (b i.castSucc)) X Y := by
    change ((S i.succ).base.metric (T - (a i.succ) ^ 2)).inner (alpha i.succ (a i.succ))
      (mfderiv I I (F i : M i.castSucc → M i.succ) (alpha i.castSucc (b i.castSucc)) X)
      (mfderiv I I (F i : M i.castSucc → M i.succ) (alpha i.castSucc (b i.castSucc)) Y) = _
    have heq := congrArg (fun p : M i.succ =>
      ((S i.succ).base.metric (T - (a i.succ) ^ 2)).inner p
        (mfderiv I I (F i : M i.castSucc → M i.succ) (alpha i.castSucc (b i.castSucc)) X)
        (mfderiv I I (F i : M i.castSucc → M i.succ) (alpha i.castSucc (b i.castSucc)) Y))
      (hpoint i)
    exact heq.symm.trans (hmetric i X Y)
  obtain ⟨P, Omega, hOmega, hP, hAdapt, hEnd, hMatch, hON⟩ :=
    exists_compatible_lAdapted_frames S hS T alpha halpha a b lo hi hlo
      (fun i => (hab i).le) hhi hreg Phi hPhi V hV
  refine ⟨hspan 0, P, Omega, hOmega, hP, hAdapt, hEnd, hMatch, hON, ?_⟩
  intro k
  let chi : ℝ → ℝ := fun r => (r - a 0) / (b (Fin.last n) - a 0)
  let Y : Fin (n + 1) → ℝ → E := fun i r => chi r • P i k r
  have hchi : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ chi :=
    (contMDiff_id.sub contMDiff_const).div_const _
  have hY (i : Fin (n + 1)) : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent ∞
      (fun r => (⟨alpha i r, Y i r⟩ : TangentBundle I (M i))) (Omega i) :=
    hchi.contMDiffOn.smul_bundle (hP i k)
  have hfield (i : Fin n) :
      (mfderiv I I (F i : M i.castSucc → M i.succ) (alpha i.castSucc (b i.castSucc))
        (Y i.castSucc (b i.castSucc)) : E) = Y i.succ (a i.succ) := by
    change Phi i (chi (b i.castSucc) • P i.castSucc k (b i.castSucc)) =
      chi (a i.succ) • P i.succ k (a i.succ)
    rw [map_smul, hMatch, hadj]
  have hfirst : Y 0 (a 0) = 0 := by
    simp only [Y, chi, sub_self, zero_div, zero_smul]
    rfl
  exact exists_compatible_variations_of_endpoint_fields
    (fun i => (S i).base.metric (T - (a i) ^ 2)) alpha Y a b hab
    Omega (fun i => (hOmega i).1) (fun i => (hOmega i).2.1) hY
    (fun i => (F i : M i.castSucc → M i.succ)) (fun i => (F i).source)
    (fun i => (F i).open_source)
    (fun i => (F i).contMDiffOn.of_le (WithTop.coe_le_coe.mpr le_top))
    hsource hpoint hfield hfirst

private theorem finite_piece_weighted_trace_bound
    {n : ℕ} {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Fin (n + 1) → Type uM} [∀ i, TopologicalSpace (M i)]
    [∀ i, ChartedSpace H (M i)] [∀ i, IsManifold I ∞ (M i)] [∀ i, T2Space (M i)]
    {D : Fin (n + 1) → RealTimeInterval}
    (S : (i : Fin (n + 1)) → SolutionOn (I := I) (M := M i) (D i))
    (hS : ∀ i, IsSolutionOn (S i)) (T : ℝ)
    (alpha : (i : Fin (n + 1)) → ℝ → M i)
    (s : Fin (n + 2) → ℝ) (hs : Monotone s) (ha : 0 < s 0)
    (hav : s 0 < s (Fin.last (n + 1)))
    (P : (i : Fin (n + 1)) → Fin (Module.finrank ℝ E) →
      ∀ t, TangentSpace I (alpha i t))
    (hgeo : ∀ i, IsLRegularizedGeodesicOn (S i) T (alpha i)
      (Ioo (s i.castSucc) (s i.succ)))
    (hLag : ∀ i, ContinuousOn (lRegularizedLagrangian (S i) T (alpha i))
      (Icc (s i.castSucc) (s i.succ)))
    (hHam : ∀ i, IntervalIntegrable (lHamSq (S i) T (alpha i)) volume
      (s i.castSucc) (s i.succ))
    (hreg : ∀ i, ∀ t ∈ Icc (s i.castSucc) (s i.succ), T - t ^ 2 ∈ (D i).regular)
    (halpha : ∀ i, ∀ t ∈ Icc (s i.castSucc) (s i.succ),
      MDifferentiableAt 𝓘(ℝ, ℝ) I (alpha i) t)
    (hP : ∀ i k t, t ∈ Icc (s i.castSucc) (s i.succ) →
      DifferentiableAt ℝ (chartRepAt (I := I) (alpha i) (P i k) t) t)
    (hDP : ∀ i k, IsLAdapted (S i) T (alpha i) (P i k)
      (Icc (s i.castSucc) (s i.succ)))
    (hON : ∀ i k l,
      ((S i).base.metric (T - (s i.succ) ^ 2)).inner (alpha i (s i.succ))
        (P i k (s i.succ)) (P i l (s i.succ)) = if k = l then 1 else 0)
    (hindexInt : ∀ i k, IntervalIntegrable
      (lRegularizedIndexIntegrand (S i) T (alpha i)
        (fun t => ((t - s 0) / (s (Fin.last (n + 1)) - s 0)) • P i k t)
        (fun t => ((t - s 0) / (s (Fin.last (n + 1)) - s 0)) • P i k t))
      volume (s i.castSucc) (s i.succ))
    (hscalar : ∀ i : Fin n,
      (S i.castSucc).scalar (T - (s i.castSucc.succ) ^ 2)
          (alpha i.castSucc (s i.castSucc.succ)) =
        (S i.succ).scalar (T - (s i.succ.castSucc) ^ 2)
          (alpha i.succ (s i.succ.castSucc)))
    (hlag : ∀ i : Fin n,
      lRegularizedLagrangian (S i.castSucc) T (alpha i.castSucc) (s i.castSucc.succ) =
        lRegularizedLagrangian (S i.succ) T (alpha i.succ) (s i.succ.castSucc))
    (hfinal : lVelocity (I := I) (alpha (Fin.last n)) (s (Fin.last (n + 1))) = 0)
    (hindex : ∀ k : Fin (Module.finrank ℝ E), 0 ≤ ∑ i : Fin (n + 1),
      lRegularizedIndex (S i) T (alpha i)
        (fun t => ((t - s 0) / (s (Fin.last (n + 1)) - s 0)) • P i k t)
        (fun t => ((t - s 0) / (s (Fin.last (n + 1)) - s 0)) • P i k t)
        (s i.castSucc) (s i.succ)) :
    (∑ i : Fin (n + 1), ∫ t in (s i.castSucc)..(s i.succ),
      (1 - (s 0) ^ 2 / t ^ 2) * lRegularizedLagrangian (S i) T (alpha i) t) +
      2 * s (Fin.last (n + 1)) *
        (S (Fin.last n)).scalar (T - (s (Fin.last (n + 1))) ^ 2)
          (alpha (Fin.last n) (s (Fin.last (n + 1)))) *
        (s (Fin.last (n + 1)) - s 0) ^ 2 ≤
      2 * (Module.finrank ℝ E : ℝ) * (s (Fin.last (n + 1)) - s 0) := by
  classical
  let a := s 0
  let v := s (Fin.last (n + 1))
  let delta := v - a
  let chi : ℝ → ℝ := fun t => (t - a) / delta
  let L (i : Fin (n + 1)) := lRegularizedLagrangian (S i) T (alpha i)
  let R (i : Fin (n + 1)) (t : ℝ) := (S i).scalar (T - t ^ 2) (alpha i t)
  let J (i : Fin (n + 1)) := ∑ k : Fin (Module.finrank ℝ E),
    lRegularizedIndex (S i) T (alpha i) (fun t => chi t • P i k t)
      (fun t => chi t • P i k t) (s i.castSucc) (s i.succ)
  let A (i : Fin (n + 1)) := ∫ t in (s i.castSucc)..(s i.succ),
    (1 - a ^ 2 / t ^ 2) * L i t
  let Q (i : Fin (n + 1)) (t : ℝ) := t * (t - a) ^ 2 * R i t
  let F (i : Fin (n + 1)) (t : ℝ) := ((t - a) ^ 2 / t) * L i t
  have hd : 0 < delta := sub_pos.mpr hav
  have hv : 0 < v := ha.trans hav
  have hleft (i : Fin (n + 1)) : a ≤ s i.castSucc := hs (Fin.zero_le _)
  have hordered (i : Fin (n + 1)) : s i.castSucc ≤ s i.succ :=
    hs i.castSucc_le_succ
  have hpos (i : Fin (n + 1)) : 0 < s i.castSucc := ha.trans_le (hleft i)
  have hpiece (i : Fin (n + 1)) :
      4 * delta ^ 2 * J i =
        2 * (Module.finrank ℝ E : ℝ) * (s i.succ - s i.castSucc) -
          4 * (Q i (s i.succ) - Q i (s i.castSucc)) - A i +
          (F i (s i.succ) - F i (s i.castSucc)) := by
    have hnonzero (t : ℝ) (ht : t ∈ Icc (s i.castSucc) (s i.succ)) : t ≠ 0 :=
      ((hpos i).trans_le ht.1).ne'
    have hweight : ContinuousOn (fun t => (chi t / t) ^ 2)
        (uIcc (s i.castSucc) (s i.succ)) := by
      rw [uIcc_of_le (hordered i)]
      exact (((continuousOn_id.sub continuousOn_const).div_const delta).div
        continuousOn_id hnonzero).pow 2
    have hHamChi := (hHam i).continuousOn_mul hweight
    have hchi (t : ℝ) (_ht : t ∈ Icc (s i.castSucc) (s i.succ)) :
        HasDerivAt chi (1 / delta) t :=
      ((hasDerivAt_id t).sub_const a).div_const delta
    have htrace := lRegularizedIndex_trace_smul_function (S i) (hS i) T (alpha i)
      (P i) chi (fun _ => 1 / delta) (s i.castSucc) (s i.succ) (hpos i) (hordered i)
      hchi (hreg i) (halpha i) (hP i) (hDP i) (hON i) (hindexInt i)
      intervalIntegrable_const hHamChi
    have hHamEq :
        (∫ t in (s i.castSucc)..(s i.succ), (chi t / t) ^ 2 * lHamSq (S i) T (alpha i) t) =
          (∫ t in (s i.castSucc)..(s i.succ),
            ((t - a) / t) ^ 2 * lHamSq (S i) T (alpha i) t) / delta ^ 2 := by
      rw [← intervalIntegral.integral_div]
      apply intervalIntegral.integral_congr
      intro t ht
      have ht0 := hnonzero t (by simpa only [uIcc_of_le (hordered i)] using ht)
      dsimp only [chi]
      field_simp [hd.ne', ht0]
    have ht : 4 * delta ^ 2 * J i =
        2 * (Module.finrank ℝ E : ℝ) * (s i.succ - s i.castSucc) -
          4 * (Q i (s i.succ) - Q i (s i.castSucc)) -
          4 * (∫ t in (s i.castSucc)..(s i.succ),
            ((t - a) / t) ^ 2 * lHamSq (S i) T (alpha i) t) := by
      change J i = _ at htrace
      rw [htrace, hHamEq, intervalIntegral.integral_const]
      dsimp only [Q, R, chi]
      simp only [smul_eq_mul]
      field_simp [hd.ne']
      ring
    have he := integral_lHamSq_mul_eq_of_geodesic (S i) (hS i) T (alpha i) (a := a)
      (ha.trans_le (hleft i)) (hordered i) (hgeo i) (hLag i) (hHam i)
    change 4 * (∫ t in (s i.castSucc)..(s i.succ),
      ((t - a) / t) ^ 2 * lHamSq (S i) T (alpha i) t) =
        A i - (F i (s i.succ) - F i (s i.castSucc)) at he
    linarith
  have telescope (f g : Fin (n + 1) → ℝ)
      (hmatch : ∀ i : Fin n, f i.castSucc = g i.succ) :
      (∑ i : Fin (n + 1), (f i - g i)) = f (Fin.last n) - g 0 := by
    rw [Finset.sum_sub_distrib, Fin.sum_univ_castSucc f, Fin.sum_univ_succ g]
    have hmid : (∑ i : Fin n, f i.castSucc) = ∑ i : Fin n, g i.succ :=
      Finset.sum_congr rfl (fun i _ => hmatch i)
    rw [hmid]
    ring
  have ht : (∑ i : Fin (n + 1), (s i.succ - s i.castSucc)) = delta := by
    exact telescope (fun i => s i.succ) (fun i => s i.castSucc) (fun _ => rfl)
  have hQ : (∑ i : Fin (n + 1), (Q i (s i.succ) - Q i (s i.castSucc))) =
      v * delta ^ 2 * R (Fin.last n) v := by
    have hh := telescope (fun i => Q i (s i.succ)) (fun i => Q i (s i.castSucc))
      (fun i => by dsimp only [Q, R]; rw [hscalar i]; simp only [Fin.castSucc_succ])
    simpa only [Q, a, v, delta, Fin.succ_last, Fin.castSucc_zero, sub_self,
      zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, zero_mul, sub_zero] using hh
  have hF : (∑ i : Fin (n + 1), (F i (s i.succ) - F i (s i.castSucc))) =
      (delta ^ 2 / v) * L (Fin.last n) v := by
    have hh := telescope (fun i => F i (s i.succ)) (fun i => F i (s i.castSucc))
      (fun i => by dsimp only [F, L]; rw [hlag i]; simp only [Fin.castSucc_succ])
    simpa only [F, a, v, delta, Fin.succ_last, Fin.castSucc_zero, sub_self,
      zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_div, zero_mul, sub_zero] using hh
  have hsum := congrArg (fun f : Fin (n + 1) → ℝ => ∑ i, f i) (funext hpiece)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
  simp only [Finset.sum_sub_distrib] at ht hQ hF
  rw [ht, hQ, hF] at hsum
  have hLv : L (Fin.last n) v = 2 * v ^ 2 * R (Fin.last n) v := by
    dsimp only [L, lRegularizedLagrangian, lRegularizedSpeedSq]
    rw [hfinal]
    simp only [map_zero, zero_add, mul_zero]
    rfl
  have hflux : (delta ^ 2 / v) * L (Fin.last n) v =
      2 * v * R (Fin.last n) v * delta ^ 2 := by
    rw [hLv]
    field_simp [hv.ne']
  rw [hflux] at hsum
  have hnonneg : 0 ≤ ∑ i : Fin (n + 1), J i := by
    dsimp only [J]
    rw [Finset.sum_comm]
    exact Finset.sum_nonneg (fun k _ => hindex k)
  have hp := mul_nonneg (show 0 ≤ 4 * delta ^ 2 by positivity) hnonneg
  change (∑ i : Fin (n + 1), A i) +
    2 * v * R (Fin.last n) v * delta ^ 2 ≤ 2 * (Module.finrank ℝ E : ℝ) * delta
  linarith

private theorem lagrangian_continuousOn_and_hamilton_intervalIntegrable_on_piece
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type uH} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [T2Space M]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) (T : ℝ) (alpha : ℝ → M)
    (halpha : ContMDiff 𝓘(ℝ, ℝ) I (8 : ℕ) alpha)
    {a b lo hi : ℝ} (hlo : lo < a) (hab : a ≤ b) (hhi : b < hi)
    (hreg : ∀ r ∈ Ioo lo hi, T - r ^ 2 ∈ D.regular)
    (hgeo : IsLRegularizedGeodesicOn S T alpha (Icc a b)) :
    ContinuousOn (lRegularizedLagrangian S T alpha) (Icc a b) ∧
      IntervalIntegrable (lHamSq S T alpha) volume a b := by
  let L := lRegularizedLagrangian S T alpha
  let F : ℝ → ℝ := fun r => r * L r
  have hf : IsSmoothVariation (I := I) (fun _ : ℝ => alpha) :=
    halpha.comp contMDiff_snd
  have hfamily := lRegularizedLagrangian_contDiffOn_two S hS T (fun _ : ℝ => alpha) hf
  have hpair : ContDiff ℝ 2 (fun r : ℝ => ((0 : ℝ), r)) :=
    contDiff_const.prodMk contDiff_id
  have hL : ContDiffOn ℝ 2 L (Ioo lo hi) := by
    change ContDiffOn ℝ 2
      ((fun p : ℝ × ℝ => lRegularizedLagrangian S T alpha p.2) ∘
        fun r : ℝ => ((0 : ℝ), r)) (Ioo lo hi)
    exact hfamily.comp hpair.contDiffOn (fun r hr => hreg r hr)
  have hseg : Icc a b ⊆ Ioo lo hi :=
    fun r hr => ⟨hlo.trans_le hr.1, hr.2.trans_lt hhi⟩
  have hcont : ContinuousOn L (Icc a b) := hL.continuousOn.mono hseg
  have hF : ContDiffOn ℝ 2 F (Ioo lo hi) := contDiffOn_id.mul hL
  have hdcont : ContinuousOn (deriv F) (Icc a b) :=
    (hF.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)).mono hseg
  have hIntL : IntervalIntegrable L volume a b := hcont.intervalIntegrable_of_Icc hab
  have hIntD : IntervalIntegrable (deriv F) volume a b :=
    hdcont.intervalIntegrable_of_Icc hab
  have hInt : IntervalIntegrable (fun r => (L r - deriv F r) / 4) volume a b :=
    (hIntL.sub hIntD).div_const 4
  have hcurve : IsLRegularizedCurveOn S T alpha (Icc a b) (alpha 0)
      ((1 / 2 : ℝ) • lVelocity (I := I) alpha 0) := by
    refine ⟨rfl, ?_, hgeo⟩
    rw [two_smul, ← add_smul]
    norm_num
  refine ⟨hcont, hInt.congr ?_⟩
  intro r hr
  have hr' : r ∈ Icc a b := Ioc_subset_Icc_self (by simpa only [uIoc_of_le hab] using hr)
  have hderiv : deriv F r = L r - 4 * lHamSq S T alpha r :=
    (lLagMul_deriv S hS T hcurve hr').deriv
  change (L r - deriv F r) / 4 = lHamSq S T alpha r
  rw [hderiv]
  ring

theorem sum_integral_lRegularizedLagrangian_mul_add_scalar_le_of_variational_minimum
    {n : ℕ} {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Fin (n + 1) → Type uM} [∀ i, TopologicalSpace (M i)]
    [∀ i, ChartedSpace H (M i)] [∀ i, IsManifold I ∞ (M i)] [∀ i, T2Space (M i)]
    {D : Fin (n + 1) → RealTimeInterval}
    (S : (i : Fin (n + 1)) → SolutionOn (I := I) (M := M i) (D i))
    (hS : ∀ i, IsSolutionOn (S i)) (T : ℝ)
    (alpha : (i : Fin (n + 1)) → ℝ → M i)
    (halpha : ∀ i, ContMDiff 𝓘(ℝ, ℝ) I ∞ (alpha i))
    (s : Fin (n + 2) → ℝ) (hs : StrictMono s) (ha : 0 < s 0)
    (lo hi : Fin (n + 1) → ℝ)
    (hlo : ∀ i, lo i < s i.castSucc) (hhi : ∀ i, s i.succ < hi i)
    (hreg : ∀ i, ∀ r ∈ Ioo (lo i) (hi i), T - r ^ 2 ∈ (D i).regular)
    (hgeo : ∀ i, IsLRegularizedGeodesicOn (S i) T (alpha i)
      (Icc (s i.castSucc) (s i.succ)))
    (F : (i : Fin n) → PartialDiffeomorph I I (M i.castSucc) (M i.succ) ∞)
    (hsource : ∀ i, alpha i.castSucc (s i.castSucc.succ) ∈ (F i).source)
    (hpoint : ∀ i,
      F i (alpha i.castSucc (s i.castSucc.succ)) = alpha i.succ (s i.succ.castSucc))
    (hmetric : ∀ (i : Fin n) (x : M i.castSucc), x ∈ (F i).source →
      ∀ X Y : TangentSpace I x,
      ((S i.castSucc).base.metric (T - (s i.castSucc.succ) ^ 2)).inner x X Y =
        ((S i.succ).base.metric (T - (s i.castSucc.succ) ^ 2)).inner (F i x)
          (mfderiv I I (F i : M i.castSucc → M i.succ) x X)
          (mfderiv I I (F i : M i.castSucc → M i.succ) x Y))
    (hvelocity : ∀ i : Fin n,
      (mfderiv I I (F i : M i.castSucc → M i.succ)
        (alpha i.castSucc (s i.castSucc.succ))
        (lVelocity (I := I) (alpha i.castSucc) (s i.castSucc.succ)) : E) =
          lVelocity (I := I) (alpha i.succ) (s i.succ.castSucc))
    (hfinal : lVelocity (I := I) (alpha (Fin.last n)) (s (Fin.last (n + 1))) = 0)
    (hmin : ∀ f : (i : Fin (n + 1)) → ℝ → ℝ → M i,
      (∀ i, IsSmoothVariation (I := I) (f i)) →
      (∀ i r, r ∈ Icc (s i.castSucc) (s i.succ) → f i 0 =ᶠ[𝓝 r] alpha i) →
      (∀ᶠ e in 𝓝 (0 : ℝ), f 0 e (s 0) = alpha 0 (s 0)) →
      (∀ᶠ e in 𝓝 (0 : ℝ), ∀ i : Fin n,
        f i.castSucc e (s i.castSucc.succ) ∈ (F i).source ∧
        F i (f i.castSucc e (s i.castSucc.succ)) = f i.succ e (s i.succ.castSucc)) →
      IsLocalMin (fun e => ∑ i : Fin (n + 1),
        lRegularizedAction (S i) T (f i e) (s i.castSucc) (s i.succ)) 0) :
    (∑ i : Fin (n + 1), ∫ r in (s i.castSucc)..(s i.succ),
      (1 - (s 0) ^ 2 / r ^ 2) * lRegularizedLagrangian (S i) T (alpha i) r) +
      2 * s (Fin.last (n + 1)) *
        (S (Fin.last n)).scalar (T - (s (Fin.last (n + 1))) ^ 2)
          (alpha (Fin.last n) (s (Fin.last (n + 1)))) *
        (s (Fin.last (n + 1)) - s 0) ^ 2 ≤
      2 * (Module.finrank ℝ E : ℝ) * (s (Fin.last (n + 1)) - s 0) := by
  classical
  by_cases hE : Module.finrank ℝ E = 0
  · have : Subsingleton E := (Module.finrank_eq_zero_iff_of_free ℝ E).mp hE
    have hscalarZero (i : Fin (n + 1)) (t : ℝ) (x : M i) : (S i).scalar t x = 0 :=
      metricScalarAt_eq_zero_of_finrank_eq_zero ((S i).base.metric t) hE x
    have hlagZero (i : Fin (n + 1)) (r : ℝ) :
        lRegularizedLagrangian (S i) T (alpha i) r = 0 := by
      have hv : lVelocity (I := I) (alpha i) r = 0 := by
        change (_ : E) = _
        exact Subsingleton.elim _ _
      dsimp only [lRegularizedLagrangian]
      rw [hv, hscalarZero]
      simp
    simp only [hlagZero, hscalarZero, mul_zero, intervalIntegral.integral_zero,
      Finset.sum_const_zero, zero_add, hE, Nat.cast_zero, zero_mul, le_refl]
  · have : NeZero (Module.finrank ℝ E) := ⟨hE⟩
    have hscalar (i : Fin n) :
        (S i.castSucc).scalar (T - (s i.castSucc.succ) ^ 2)
            (alpha i.castSucc (s i.castSucc.succ)) =
          (S i.succ).scalar (T - (s i.succ.castSucc) ^ 2)
            (alpha i.succ (s i.succ.castSucc)) := by
      have h := metricScalarAt_eq_of_partialDiffeomorph_inner
        ((S i.castSucc).base.metric (T - (s i.castSucc.succ) ^ 2))
        ((S i.succ).base.metric (T - (s i.castSucc.succ) ^ 2))
        (F i) ⟨(F i).source, (F i).open_source⟩ (fun _ hx => hx)
        (hmetric i) (hsource i)
      calc
        (S i.castSucc).scalar (T - (s i.castSucc.succ) ^ 2)
            (alpha i.castSucc (s i.castSucc.succ)) =
            metricScalarAt ((S i.castSucc).base.metric (T - (s i.castSucc.succ) ^ 2))
              (alpha i.castSucc (s i.castSucc.succ)) := rfl
        _ = metricScalarAt ((S i.succ).base.metric (T - (s i.castSucc.succ) ^ 2))
              (F i (alpha i.castSucc (s i.castSucc.succ))) := h
        _ = (S i.succ).scalar (T - (s i.succ.castSucc) ^ 2)
              (alpha i.succ (s i.succ.castSucc)) := by
          rw [hpoint i]
          rfl
    have hlag (i : Fin n) :
        lRegularizedLagrangian (S i.castSucc) T (alpha i.castSucc) (s i.castSucc.succ) =
          lRegularizedLagrangian (S i.succ) T (alpha i.succ) (s i.succ.castSucc) := by
      dsimp only [lRegularizedLagrangian]
      rw [hmetric i _ (hsource i), hvelocity i, hpoint i, hscalar i]
      rfl
    obtain ⟨V, hV⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis (I := I)
      ((S (Fin.last n)).base.metric (T - (s (Fin.last (n + 1))) ^ 2))
      (alpha (Fin.last n) (s (Fin.last (n + 1))))
    let a : Fin (n + 1) → ℝ := fun i => s i.castSucc
    let b : Fin (n + 1) → ℝ := fun i => s i.succ
    have hab (i : Fin (n + 1)) : a i < b i := hs i.castSucc_lt_succ
    have hadj (i : Fin n) : b i.castSucc = a i.succ := rfl
    have hcoeff (i : Fin (n + 1)) :
        ContinuousOn (lRegularizedLagrangian (S i) T (alpha i)) (Icc (a i) (b i)) ∧
          IntervalIntegrable (lHamSq (S i) T (alpha i)) volume (a i) (b i) :=
      lagrangian_continuousOn_and_hamilton_intervalIntegrable_on_piece
        (S i) (hS i) T (alpha i)
        ((halpha i).of_le (by decide : (8 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞)))
        (hlo i) (hab i).le (hhi i) (hreg i) (hgeo i)
    have hpointMetric (i : Fin n) (X Y : TangentSpace I (alpha i.castSucc (b i.castSucc))) :
        ((S i.succ).base.metric (T - (a i.succ) ^ 2)).inner
          (F i (alpha i.castSucc (b i.castSucc)))
          (mfderiv I I (F i : M i.castSucc → M i.succ)
            (alpha i.castSucc (b i.castSucc)) X)
          (mfderiv I I (F i : M i.castSucc → M i.succ)
            (alpha i.castSucc (b i.castSucc)) Y) =
        ((S i.castSucc).base.metric (T - (b i.castSucc) ^ 2)).inner
          (alpha i.castSucc (b i.castSucc)) X Y :=
      (hmetric i _ (hsource i) X Y).symm
    obtain ⟨hspan, P, Omega, hOmega, hP, hAdapt, hEnd, hMatch, hON, hvar⟩ :=
      exists_compatible_variations_of_lAdapted_frames S hS T alpha halpha
        a b lo hi hlo hab hhi hadj hreg F hsource hpoint hpointMetric V hV
    let chi : ℝ → ℝ := fun r => (r - s 0) / (s (Fin.last (n + 1)) - s 0)
    let Y (i : Fin (n + 1)) (k : Fin (Module.finrank ℝ E)) (r : ℝ) := chi r • P i k r
    have hregClosed (i : Fin (n + 1)) (r : ℝ) (hr : r ∈ Icc (a i) (b i)) :
        T - r ^ 2 ∈ (D i).regular :=
      hreg i r ⟨(hlo i).trans_le hr.1, hr.2.trans_lt (hhi i)⟩
    have hchi : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) 2 chi :=
      (contMDiff_id.sub contMDiff_const).div_const _
    have hY (i : Fin (n + 1)) (k : Fin (Module.finrank ℝ E)) :
        ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 2
          (fun r => (TotalSpace.mk' E (E := (TangentSpace I : M i → Type _))
            (alpha i r) (Y i k r) : TangentBundle I (M i))) (Omega i) :=
      hchi.contMDiffOn.smul_bundle ((hP i k).of_le (by decide : (2 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞)))
    have hindexInt (i : Fin (n + 1)) (k : Fin (Module.finrank ℝ E)) :
        IntervalIntegrable (lRegularizedIndexIntegrand (S i) T (alpha i)
          (Y i k) (Y i k)) volume (a i) (b i) := by
      apply intervalIntegrable_lRegularizedIndexIntegrand_of_contMDiffOn
        (S i) (hS i) T (a i) (b i) (alpha i) (Y i k) (Y i k) (hOmega i).1
      · simpa only [uIcc_of_le (hab i).le] using (hOmega i).2.1
      · exact hY i k
      · exact hY i k
      · simpa only [uIcc_of_le (hab i).le] using hregClosed i
    have hindex (k : Fin (Module.finrank ℝ E)) :
        0 ≤ ∑ i : Fin (n + 1), lRegularizedIndex (S i) T (alpha i)
          (Y i k) (Y i k) (a i) (b i) := by
      obtain ⟨f, hf, hcenter, hfield, hfirst, hjoin⟩ := hvar k
      have hvel (i : Fin (n + 1)) (r : ℝ) (hr : r ∈ Icc (a i) (b i)) :
          lVelocity (I := I) (f i 0) r = lVelocity (I := I) (alpha i) r := by
        unfold lVelocity
        rw [(hcenter i r hr).mfderiv_eq]
        rfl
      have hfgeo (i : Fin (n + 1)) :
          IsLRegularizedGeodesicOn (S i) T (f i 0) (uIcc (a i) (b i)) := by
        rw [uIcc_of_le (hab i).le]
        exact (hgeo i).congr_of_eventuallyEq (hcenter i)
      have hfvelocity (i : Fin n) :
          (mfderiv I I (F i : M i.castSucc → M i.succ)
            (f i.castSucc 0 (b i.castSucc))
            (lVelocity (I := I) (f i.castSucc 0) (b i.castSucc)) : E) =
              lVelocity (I := I) (f i.succ 0) (a i.succ) := by
        rw [hvel _ _ (right_mem_Icc.mpr (hab _).le),
          hvel _ _ (left_mem_Icc.mpr (hab _).le),
          (hcenter _ _ (right_mem_Icc.mpr (hab _).le)).self_of_nhds]
        exact hvelocity i
      have hflast : lVelocity (I := I) (f (Fin.last n) 0) (b (Fin.last n)) = 0 := by
        rw [hvel _ _ (right_mem_Icc.mpr (hab _).le)]
        exact hfinal
      have hboundary := sum_variation_acceleration_boundary_eq_zero
        (fun i r => (S i).base.metric (T - r ^ 2)) a b f
        (fun i => ((hf i.castSucc : ContMDiff _ _ _ _).comp
          (contMDiff_id.prodMk contMDiff_const)).contMDiffAt.of_le (by norm_num)) F
        (fun i x hx X Y => by
        have hclock : s i.castSucc.succ = s i.succ.castSucc := rfl
        simpa only [a, b, hclock] using hmetric i x hx X Y)
        hjoin hfvelocity (alpha 0 (s 0)) hfirst hflast
      have hnonneg := sum_lRegularizedIndex_nonneg_of_isLocalMin_sum_action
        S hS T a b f hf hfgeo (hmin f hf hcenter hfirst hjoin) hboundary
      have heq : (∑ i : Fin (n + 1), lRegularizedIndex (S i) T (f i 0)
          (fun r => lVelocity (I := I) (fun e => f i e r) 0)
          (fun r => lVelocity (I := I) (fun e => f i e r) 0) (a i) (b i)) =
          ∑ i : Fin (n + 1), lRegularizedIndex (S i) T (alpha i)
            (Y i k) (Y i k) (a i) (b i) := by
        apply Finset.sum_congr rfl
        intro i _
        apply lRegularizedIndex_congr_of_eventuallyEq
        · intro r hr
          rw [uIoo_of_le (hab i).le] at hr
          exact hcenter i r (Ioo_subset_Icc_self hr)
        · intro r hr
          rw [uIoo_of_le (hab i).le] at hr
          exact hfield i r (Ioo_subset_Icc_self hr)
        · intro r hr
          rw [uIoo_of_le (hab i).le] at hr
          exact hfield i r (Ioo_subset_Icc_self hr)
      exact heq ▸ hnonneg
    have hPdiff (i : Fin (n + 1)) (k : Fin (Module.finrank ℝ E))
        (r : ℝ) (hr : r ∈ Icc (a i) (b i)) :
        DifferentiableAt ℝ (chartRepAt (I := I) (alpha i) (P i k) r) r := by
      apply differentiableAt_chartRepAt_of_contMDiffAt_two
      exact ((hP i k).of_le (by decide : (2 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞)) r ((hOmega i).2.1 hr)).contMDiffAt
        ((hOmega i).1.mem_nhds ((hOmega i).2.1 hr))
    exact finite_piece_weighted_trace_bound S hS T alpha s hs.monotone ha hspan P
      (fun i r hr => hgeo i r (Ioo_subset_Icc_self hr))
      (fun i => (hcoeff i).1) (fun i => (hcoeff i).2) hregClosed
      (fun i r _ => (halpha i).mdifferentiableAt (by simp)) hPdiff
      (fun i k r hr => hAdapt i k r ((hOmega i).2.1 hr))
      (fun i k l => hON i (b i) (right_mem_Icc.mpr (hab i).le) k l)
      hindexInt hscalar hlag hfinal hindex

end DifferentialGeometry.PDE.RicciFlow.Perelman
