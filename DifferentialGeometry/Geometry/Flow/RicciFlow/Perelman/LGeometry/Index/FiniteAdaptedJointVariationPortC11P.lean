import Mathlib.Topology.Algebra.Module.FiniteDimension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Index.FiniteJointTrace
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.AdaptedField.ExistenceIcc
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.AdaptedField.InnerProduct
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.LagrangianRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Hamilton.TraceIntegralGeodesic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Index.Integrability
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.LocalCross
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.MetricComparison

/-!
# S-CH11-FIX4 `PortC11P` port

Module `Perelman.LGeometry.Index.FiniteAdaptedJointVariation`.

Source: donor file of the same relative path in the chapter-11 branch (ch11 HEAD a73e4bdbfd).
Verbatim it does not elaborate against this tree (2 errors, both `simp made no progress` in
`hBsingle`).  `simp` cannot use the dependent index type `Fin (finrank ℝ E)` against
`Fin (finrank ℝ (TangentSpace I _))`.  One elaboration-level repair, `hBsingle`:
`rw [hBsum]; simp` becomes `change V.equivFun.symm (Pi.single k 1) = (V k : E)`,
`rw [LinearEquiv.symm_apply_eq]`, `funext j`, `rw [V.equivFun_self k j]` and a case split `k = j`
closed by `Pi.single_eq_same` / `Pi.single_eq_of_ne` with `ite_eq_left` / `ite_eq_right`.
No statement, definition or proof idea is altered.  The module
`Perelman.LGeometry.Index.FiniteAdaptedJointVariation` is a shim re-exporting this file.
-/

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Set Bundle Filter MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Exponential
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


/-- Construct adapted frames and one compatible joint family on the actual smooth
geodesic pieces. The chosen terminal orthonormal basis supplies the endpoint
linear equivalence for this same family. All coefficient and index regularity
are derived from the physical flows; the endpoint velocity is unrestricted. -/
theorem exists_compatible_joint_variation_of_smooth_geodesic_pieces
    {n : ℕ} {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
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
    :
    let v := s (Fin.last (n + 1));
    ∃ (terminalBasis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ
        (TangentSpace I (alpha (Fin.last n) v)))
      (Pframe : (i : Fin (n + 1)) → Fin (Module.finrank ℝ E) →
        ∀ r, TangentSpace I (alpha i r))
      (Omega : Fin (n + 1) → Set ℝ)
      (Bframe : (Fin (Module.finrank ℝ E) → ℝ) ≃L[ℝ] E)
      (f : (i : Fin (n + 1)) → (Fin (Module.finrank ℝ E) → ℝ) × ℝ → M i),
      (∀ k l, ((S (Fin.last n)).base.metric (T - v ^ 2)).inner
        (alpha (Fin.last n) v) (terminalBasis k) (terminalBasis l) = if k = l then 1 else 0) ∧
      (∀ z, Bframe z = (∑ k, z k • terminalBasis k : E)) ∧
      (∀ i, IsOpen (Omega i) ∧ Icc (s i.castSucc) (s i.succ) ⊆ Omega i ∧
        Omega i ⊆ Ioo (lo i) (hi i)) ∧
      (∀ i k, ContMDiffOn 𝓘(ℝ, ℝ) I.tangent ∞
        (fun r => (⟨alpha i r, Pframe i k r⟩ : TangentBundle I (M i))) (Omega i)) ∧
      (∀ i k, IsLAdapted (S i) T (alpha i) (Pframe i k) (Omega i)) ∧
      (∀ k, Pframe (Fin.last n) k v = terminalBasis k) ∧
      (∀ i k,
        (mfderiv I I (F i : M i.castSucc → M i.succ)
          (alpha i.castSucc (s i.castSucc.succ))
          (Pframe i.castSucc k (s i.castSucc.succ)) : E) =
            Pframe i.succ k (s i.succ.castSucc)) ∧
      (∀ i r, r ∈ Icc (s i.castSucc) (s i.succ) → ∀ k l,
        ((S i).base.metric (T - r ^ 2)).inner (alpha i r)
          (Pframe i k r) (Pframe i l r) = if k = l then 1 else 0) ∧
      (∀ i, ContinuousOn (lRegularizedLagrangian (S i) T (alpha i))
        (Icc (s i.castSucc) (s i.succ))) ∧
      (∀ i, IntervalIntegrable (lHamSq (S i) T (alpha i)) volume
        (s i.castSucc) (s i.succ)) ∧
      (∀ i r, r ∈ Icc (s i.castSucc) (s i.succ) → T - r ^ 2 ∈ (D i).regular) ∧
      (∀ i k r, r ∈ Icc (s i.castSucc) (s i.succ) →
        DifferentiableAt ℝ (chartRepAt (I := I) (alpha i) (Pframe i k) r) r) ∧
      (∀ i k, IntervalIntegrable
        (lRegularizedIndexIntegrand (S i) T (alpha i)
          (fun r => ((r - s 0) / (v - s 0)) • Pframe i k r)
          (fun r => ((r - s 0) / (v - s 0)) • Pframe i k r))
        volume (s i.castSucc) (s i.succ)) ∧
      (∀ i : Fin n,
        (S i.castSucc).scalar (T - (s i.castSucc.succ) ^ 2)
          (alpha i.castSucc (s i.castSucc.succ)) =
        (S i.succ).scalar (T - (s i.succ.castSucc) ^ 2)
          (alpha i.succ (s i.succ.castSucc))) ∧
      (∀ i : Fin n,
        lRegularizedLagrangian (S i.castSucc) T (alpha i.castSucc) (s i.castSucc.succ) =
        lRegularizedLagrangian (S i.succ) T (alpha i.succ) (s i.succ.castSucc)) ∧
      (∀ i, ContMDiff (𝓘(ℝ, Fin (Module.finrank ℝ E) → ℝ).prod 𝓘(ℝ, ℝ))
        I (8 : ℕ) (f i)) ∧
      (∀ i r, r ∈ Icc (s i.castSucc) (s i.succ) →
        (fun t => f i (0, t)) =ᶠ[𝓝 r] alpha i) ∧
      (∀ i k r, r ∈ Icc (s i.castSucc) (s i.succ) →
        Filter.EventuallyEq (β := E) (𝓝 r)
          (fun t => (mfderiv 𝓘(ℝ, Fin (Module.finrank ℝ E) → ℝ) I
            (fun z => f i (z, t)) 0 (Pi.single k 1) : E))
          (fun t => (((t - s 0) / (v - s 0)) • Pframe i k t : E))) ∧
      (∀ z, f 0 (z, s 0) = alpha 0 (s 0)) ∧
      (∀ z i, f i.castSucc (z, s i.castSucc.succ) ∈ (F i).source ∧
        F i (f i.castSucc (z, s i.castSucc.succ)) = f i.succ (z, s i.succ.castSucc)) ∧
      ((fun z => f (Fin.last n) (z, v)) =ᶠ[𝓝 (0 : Fin (Module.finrank ℝ E) → ℝ)]
        (fun z => expMap (I := I) ((S (Fin.last n)).base.metric (T - v ^ 2))
          (alpha (Fin.last n) v)
          (show TangentSpace I (alpha (Fin.last n) v) from Bframe z))) ∧
      (∀ k l, ((S (Fin.last n)).base.metric (T - v ^ 2)).inner
        (alpha (Fin.last n) v)
        (show TangentSpace I (alpha (Fin.last n) v) from Bframe (Pi.single k 1))
        (show TangentSpace I (alpha (Fin.last n) v) from Bframe (Pi.single l 1)) =
          if k = l then 1 else 0) := by
  classical
  intro v
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
    exact heq.symm.trans (hpointMetric i X Y)
  obtain ⟨P, Omega, hOmega, hP, hAdapt, hEnd, hMatch, hON⟩ :=
    exists_compatible_lAdapted_frames S hS T alpha halpha a b lo hi hlo
      (fun i => (hab i).le) hhi hreg Phi hPhi V hV
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
  have hPdiff (i : Fin (n + 1)) (k : Fin (Module.finrank ℝ E))
      (r : ℝ) (hr : r ∈ Icc (a i) (b i)) :
      DifferentiableAt ℝ (chartRepAt (I := I) (alpha i) (P i k) r) r :=
    differentiableAt_chartRepAt_of_contMDiffAt_two
      (((hP i k).contMDiffAt ((hOmega i).1.mem_nhds ((hOmega i).2.1 hr))).of_le
        (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)))
  have hframe (i : Fin n) (k : Fin (Module.finrank ℝ E)) :
      (mfderiv I I (F i : M i.castSucc → M i.succ)
        (alpha i.castSucc (s i.castSucc.succ))
        (P i.castSucc k (s i.castSucc.succ)) : E) =
          P i.succ k (s i.succ.castSucc) := by
    change Phi i (P i.castSucc k (b i.castSucc)) = P i.succ k (a i.succ)
    exact hMatch i k
  let Blinear : (Fin (Module.finrank ℝ E) → ℝ) ≃ₗ[ℝ] E :=
    show (Fin (Module.finrank ℝ E) → ℝ) ≃ₗ[ℝ] E from V.equivFun.symm
  let Bframe : (Fin (Module.finrank ℝ E) → ℝ) ≃L[ℝ] E :=
    Blinear.toContinuousLinearEquiv
  have hBsum (z : Fin (Module.finrank ℝ E) → ℝ) :
      Bframe z = (∑ k, z k • V k : E) := by
    change V.equivFun.symm z = _
    exact V.equivFun_symm_apply z
  have hBsingle (k : Fin (Module.finrank ℝ E)) :
      Bframe (Pi.single k 1) = (V k : E) := by
    change V.equivFun.symm (Pi.single k 1) = (V k : E)
    rw [LinearEquiv.symm_apply_eq]
    funext j
    rw [V.equivFun_self k j]
    by_cases h : k = j
    · subst h
      exact (Pi.single_eq_same k 1).trans (ite_eq_left rfl).symm
    · exact (Pi.single_eq_of_ne (Ne.symm h) 1).trans (ite_eq_right h).symm
  obtain ⟨f, hf, hcenter, hfield, hfix, hjoin, hend, _⟩ :=
    exists_compatible_joint_variation_with_index_trace_energy S hS T alpha s hs ha P
      Omega (fun i => (hOmega i).1) (fun i => (hOmega i).2.1)
      (fun i => (halpha i).contMDiffOn.of_le
        (WithTop.coe_le_coe.mpr (le_top : (8 : ℕ∞) ≤ ⊤)))
      (fun i k => (hP i k).of_le
        (WithTop.coe_le_coe.mpr (le_top : (8 : ℕ∞) ≤ ⊤)))
      (fun i => (F i : M i.castSucc → M i.succ)) (fun i => (F i).source)
      (fun i => (F i).open_source)
      (fun i => (F i).contMDiffOn.of_le
        (WithTop.coe_le_coe.mpr (le_top : (8 : ℕ∞) ≤ ⊤)))
      hsource hpoint hframe
      (fun i r hr => hgeo i r (Ioo_subset_Icc_self hr))
      (fun i => (hcoeff i).1) (fun i => (hcoeff i).2) hregClosed
      (fun i k r hr => hAdapt i k r ((hOmega i).2.1 hr))
      (fun i k l => hON i (b i) (right_mem_Icc.mpr (hab i).le) k l)
      hindexInt hscalar hlag
  have hendB :
      (fun z => f (Fin.last n) (z, v)) =ᶠ[𝓝 (0 : Fin (Module.finrank ℝ E) → ℝ)]
        (fun z => expMap (I := I) ((S (Fin.last n)).base.metric (T - v ^ 2))
          (alpha (Fin.last n) v)
          (show TangentSpace I (alpha (Fin.last n) v) from Bframe z)) := by
    filter_upwards [hend] with z hz
    have hvector :
        (∑ k, z k • P (Fin.last n) k v : TangentSpace I (alpha (Fin.last n) v)) =
          (show TangentSpace I (alpha (Fin.last n) v) from Bframe z) := by
      change (∑ k, z k • P (Fin.last n) k v : E) = Bframe z
      rw [hBsum]
      apply Finset.sum_congr rfl
      intro k _
      exact congrArg (fun w : TangentSpace I (alpha (Fin.last n) v) => z k • w) (hEnd k)
    exact hz.trans (congrArg
      (expMap (I := I) ((S (Fin.last n)).base.metric (T - v ^ 2)) (alpha (Fin.last n) v))
      hvector)
  refine ⟨V, P, Omega, Bframe, f, hV, hBsum, hOmega, hP, hAdapt, hEnd,
    hframe, hON, (fun i => (hcoeff i).1), (fun i => (hcoeff i).2),
    hregClosed, hPdiff, hindexInt, hscalar, hlag, hf, hcenter, hfield,
    hfix, hjoin, hendB, ?_⟩
  intro k l
  rw [hBsingle k, hBsingle l]
  exact hV k l

end DifferentialGeometry.PDE.RicciFlow.Perelman
