import DifferentialGeometry.Geometry.Comparison.DistanceIndex
import DifferentialGeometry.Analysis.Calculus.CutoffIntegral
import DifferentialGeometry.Geometry.Comparison.Distance.Calabi
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Distance.LengthVariation

set_option autoImplicit false

noncomputable section

open Bundle Filter Set
open Manifold (riemannianEDist)
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
private theorem ricci_velocity_continuousOn
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) {t : Real} (ht : t ∈ D.regular)
    (γ : Real → M) (hγ : ContMDiff 𝓘(Real, Real) I 1 γ)
    (a b : Real) :
    ContinuousOn (fun u => ricciTensor (I := I) (S.base.metric t) (γ u)
      (mfderiv 𝓘(Real, Real) I γ u (1 : Real))
      (mfderiv 𝓘(Real, Real) I γ u (1 : Real))) (Icc a b) := by
  let v : (u : Real) → TangentSpace I (γ u) :=
    fun u => mfderiv 𝓘(Real, Real) I γ u (1 : Real)
  have hvLift : Continuous (fun u : Real =>
      TotalSpace.mk' E (E := fun y : M => TangentSpace I y) (γ u) (v u)) := by
    have h := DifferentialGeometry.Geometry.Riemannian.MFDerivAlongCurve.continuous_tangentMap_unitLift
      (I := I) (M := M) (γ := γ) (by norm_num) hγ
    simpa only [v, tangentMap] using h
  have hRicAtCont : ContinuousOn
      (fun u => S.ricciAt t (γ u) (vec2 (I := I) (v u) (v u))) (Icc a b) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hbase : Continuous (fun u : ↥(Icc a b) => γ (u : Real)) :=
      hγ.continuous.comp continuous_subtype_val
    have hvec : ∀ _i : Fin 2, Continuous (fun u : ↥(Icc a b) =>
        TotalSpace.mk' E (E := fun y : M => TangentSpace I y) (γ (u : Real)) (v (u : Real))) :=
      fun _i => hvLift.comp continuous_subtype_val
    have heval := hS.ricciCont.eval_continuous (P := ↥(Icc a b))
      (τ := fun _u => t) (b := fun u => γ (u : Real)) continuous_const
      (fun _u => D.regular_subset ht) hbase (v := fun _i u => v (u : Real)) hvec
    refine heval.congr (fun u => ?_)
    simp only [SolutionOn.ricci, SolutionFamily.ricci_apply, SolutionFamily.ricciAt]
    change Geometry.Curvature.metricRicciAt (I := I) (S.base.metric t) (γ (u : Real))
        (fun _i : Fin 2 => v (u : Real)) =
      Geometry.Curvature.metricRicciAt (I := I) (S.base.metric t) (γ (u : Real))
        (vec2 (I := I) (v (u : Real)) (v (u : Real)))
    congr 1
    funext i
    fin_cases i <;> rfl
  refine hRicAtCont.congr (fun u _ => ?_)
  simpa only [v, SolutionOn.ricciAt, SolutionFamily.ricciAt] using
    (metricRicciAt_apply_eq_ricciTensor (I := I) (S.base.metric t) (γ u) (v u) (v u)).symm

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem arcLength_deriv_sub_laplacian_branchRadius_ge_of_ricci_le_near_start
    [RiemannianBundle (fun y : M => TangentSpace I y)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) {t : Real} (ht : t ∈ D.regular)
    (hEnorm : IsMetricNorm (I := I) (M := M) (S.base.metric t))
    (p : M) (u : TangentSpace I p) {L r K : Real}
    (hr : 0 < r) (hrL : r ≤ L) (hK : 0 ≤ K)
    (hu : (S.base.metric t).inner p u u = 1)
    (B : ExponentialInverseBranch (I := I) (S.base.metric t) hEnorm p)
    (hsrc : tangentSpaceModelContinuousLinearEquiv (I := I) p (L • u) ∈ B.hom.source)
    (hmin : ∀ η : Real → M,
      ContMDiffOn 𝓘(Real, Real) I 1 η (Icc 0 L) →
      η 0 = p → η L = intrinsicGeodesic (I := I) (S.base.metric t) hEnorm p u L →
      arcLength (I := I) (S.base.metric t)
        (intrinsicGeodesic (I := I) (S.base.metric t) hEnorm p u) 0 L ≤
          arcLength (I := I) (S.base.metric t) η 0 L)
    (hRic : ∀ s ∈ Icc (0 : Real) r,
      let γ := intrinsicGeodesic (I := I) (S.base.metric t) hEnorm p u
      ricciTensor (I := I) (S.base.metric t) (γ s)
        (curveVelocity (I := I) γ s) (curveVelocity (I := I) γ s) ≤ K) :
    let γ := intrinsicGeodesic (I := I) (S.base.metric t) hEnorm p u;
    -((Module.finrank Real E - 1 : Real) * Analysis.CutoffProfile.derivBound ^ 2 / r + K * r) ≤
      deriv (fun s => arcLength (I := I) (S.base.metric s) γ 0 L) t -
        laplacian (I := I) (LeviCivita (I := I) (S.base.metric t)) (S.base.metric t)
          (branchRadius (I := I) (S.base.metric t) B) (γ L) := by
  let γ := intrinsicGeodesic (I := I) (S.base.metric t) hEnorm p u
  let Ric := fun s => ricciTensor (I := I) (S.base.metric t) (γ s)
    (curveVelocity (I := I) γ s) (curveVelocity (I := I) γ s)
  let φ : Real → Real := fun s => 1 - Analysis.CutoffProfile.value (1 + s / r)
  have hL : 0 < L := hr.trans_le hrL
  have hγ : ContMDiff 𝓘(Real, Real) I ∞ γ := intrinsicGeodesic_contMDiff (I := I) (S.base.metric t) hEnorm p u
  have hunit (s : Real) : (S.base.metric t).inner (γ s)
      (curveVelocity (I := I) γ s) (curveVelocity (I := I) γ s) = 1 :=
    (intrinsicGeodesic_speedSq_eq (I := I) (S.base.metric t) hEnorm p u s).trans hu
  have hvel (s : Real) : curveVelocity (I := I) γ s ≠ 0 := by
    intro hv
    have hs := hunit s
    rw [hv, map_zero] at hs
    exact zero_ne_one hs
  have hderiv := pathLength_timeDeriv_of_ricciFlow (I := I) S hS hL.le ht γ (hγ.of_le (by simp))
    (fun s _ => hvel s)
  have htime : deriv (fun s => arcLength (I := I) (S.base.metric s) γ 0 L) t =
      -(∫ s in (0 : Real)..L, Ric s) := by
    rw [hderiv.deriv, ← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro s _
    change -Ric s / Real.sqrt ((S.base.metric t).inner (γ s)
      (curveVelocity (I := I) γ s) (curveVelocity (I := I) γ s)) = -Ric s
    rw [hunit, Real.sqrt_one, div_one]
  have hφ : ContDiff Real ∞ φ :=
    contDiff_const.sub (Analysis.CutoffProfile.contDiff.comp (contDiff_const.add (contDiff_id.div_const r)))
  have hφ0 : φ 0 = 0 := by simp only [φ, zero_div, add_zero, Analysis.CutoffProfile.one_of_le_one le_rfl, sub_self]
  have hφL : φ L = 1 := by
    have harg : 2 ≤ 1 + L / r := by
      have h : 1 ≤ L / r := (le_div_iff₀ hr).mpr (by simpa using hrL)
      linarith
    simp only [φ, Analysis.CutoffProfile.zero_of_two_le harg, sub_zero]
  have hlap := branchLap_le_ricci_integral_of_minimizing (I := I) (S.base.metric t) hEnorm p u L hL hu B hsrc hmin φ hφ hφ0 hφL
  have hR : IntervalIntegrable Ric MeasureTheory.volume 0 L :=
    (ricci_velocity_continuousOn (I := I) S hS ht γ (hγ.of_le (by simp)) 0 L).intervalIntegrable_of_Icc hL.le
  have hn : 0 ≤ (Module.finrank Real E - 1 : Real) := by
    have hdim : 1 ≤ Module.finrank Real E := Nat.pos_of_ne_zero (NeZero.ne _)
    have hdimR : (1 : Real) ≤ Module.finrank Real E := by exact_mod_cast hdim
    linarith
  have hcancel := Analysis.CutoffProfile.integral_deriv_sq_add_weighted_le_of_bound_near_zero hr hrL hn hK hR hRic
  have hint1 : IntervalIntegrable (fun s => (Module.finrank Real E - 1 : Real) * deriv φ s ^ 2) MeasureTheory.volume 0 L :=
    ((contDiff_infty_iff_deriv.mp hφ).2.continuous.pow 2).intervalIntegrable 0 L |>.const_mul _
  have hint2 : IntervalIntegrable (fun s => φ s ^ 2 * Ric s) MeasureTheory.volume 0 L :=
    hR.continuousOn_mul (hφ.continuous.pow 2).continuousOn
  have hid : (∫ s in (0 : Real)..L, ((Module.finrank Real E - 1 : Real) * deriv φ s ^ 2 + (1 - φ s ^ 2) * Ric s)) =
      (∫ s in (0 : Real)..L, ((Module.finrank Real E - 1 : Real) * deriv φ s ^ 2 - φ s ^ 2 * Ric s)) +
        ∫ s in (0 : Real)..L, Ric s := by
    rw [← intervalIntegral.integral_add (hint1.sub hint2) hR]
    apply intervalIntegral.integral_congr
    intro s _
    ring
  change (∫ s in (0 : Real)..L, ((Module.finrank Real E - 1 : Real) * deriv φ s ^ 2 + (1 - φ s ^ 2) * Ric s)) ≤ _ at hcancel
  rw [hid] at hcancel
  dsimp only at hlap
  change laplacian (I := I) (LeviCivita (I := I) (S.base.metric t)) (S.base.metric t)
      (branchRadius (I := I) (S.base.metric t) B) (γ L) ≤
    (∫ s in (0 : Real)..L, ((Module.finrank Real E - 1 : Real) * deriv φ s ^ 2 - φ s ^ 2 * Ric s)) at hlap
  change _ ≤ deriv (fun s => arcLength (I := I) (S.base.metric s) γ 0 L) t - _
  rw [htime]
  linarith

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem calabi_support_regularity
    [RiemannianBundle (fun y : M => TangentSpace I y)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {O x : M} {r : ℝ} (tail : CalabiTail (I := I) g hEnorm O x r) :
    let ρ := fun y => tail.initialLength + branchRadius (I := I) g tail.branch y;
    ContMDiffAt I 𝓘(ℝ, ℝ) ∞ ρ x ∧ ρ x = r ∧
      (∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) ρ y) ∧
      MDiffAt (T% fun y : M => gradientFun (I := I) g ρ y) x ∧
      g.inner x (gradientFun (I := I) g ρ x) (gradientFun (I := I) g ρ x) = 1 := by
  have hu : 0 < g.inner tail.splitPoint tail.endpointVector tail.endpointVector := by
    apply Real.sqrt_pos.mp
    rw [tail.endpointVector_norm]
    exact tail.terminalLength_pos
  obtain ⟨w, hw, hperp⟩ := exists_perp_pos (I := I) g tail.splitPoint tail.endpointVector hu
  have hwLI : LinearIndependent ℝ w := by
    let b : TangentSpace I tail.splitPoint →ₗ[ℝ] TangentSpace I tail.splitPoint →ₗ[ℝ] ℝ :=
      { toFun := fun v => (g.inner tail.splitPoint v).toLinearMap
        map_add' := by intros; ext; simp
        map_smul' := by intros; ext; simp }
    apply LinearMap.linearIndependent_of_isOrthoᵢ (B := b)
    · intro i j hij
      change g.inner tail.splitPoint (w i) (w j) = 0
      rw [hw i j, if_neg hij]
    · intro i
      change g.inner tail.splitPoint (w i) (w i) ≠ 0
      simp [hw]
  have hperp' (i) : g.inner tail.splitPoint tail.endpointVector (w i) = 0 := by
    rw [g.symm]
    exact hperp i
  obtain ⟨hρ, hρx, _, hspace, hgrad, hnorm, _⟩ :=
    calabi_support_of_tail_of_frame (I := I) g hEnorm tail w hwLI hperp'
  exact ⟨hρ, hρx, hspace, hgrad, hnorm⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem distance_upper_support_of_tail
    [RiemannianBundle (fun y : M => TangentSpace I y)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) {t : ℝ} (ht : t ∈ D.regular)
    (hEnorm : IsMetricNorm (I := I) (M := M) (S.base.metric t))
    {O x : M} {r R a K : ℝ}
    (tail : CalabiTail (I := I) (S.base.metric t) hEnorm O x r)
    (hr : r = (riemannianEDist I O x).toReal)
    (ha : 0 < a) (haell : a ≤ tail.terminalLength) (hreach : tail.initialLength + a < R)
    (hK : 0 ≤ K)
    (hRic : ∀ y : M, riemannianEDist I O y < ENNReal.ofReal R →
      ∀ v : TangentSpace I y, ricciTensor (I := I) (S.base.metric t) y v v ≤
        K * (S.base.metric t).inner y v v) :
    ∃ ρ : ℝ → M → ℝ,
      ρ t x = r ∧
      (∀ᶠ y in 𝓝 x, ∀ s : ℝ,
        riemannianEDistOf (I := I) (S.base.metric s) O y ≤ ENNReal.ofReal (ρ s y)) ∧
      DifferentiableAt ℝ (fun s => ρ s x) t ∧
      (∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (ρ t) y) ∧
      MDiffAt (T% fun y : M => gradientFun (I := I) (S.base.metric t) (ρ t) y) x ∧
      (S.base.metric t).inner x (gradientFun (I := I) (S.base.metric t) (ρ t) x)
        (gradientFun (I := I) (S.base.metric t) (ρ t) x) = 1 ∧
      -((Module.finrank ℝ E - 1 : ℝ) * Analysis.CutoffProfile.derivBound ^ 2 / a +
        K * (tail.initialLength + a)) ≤
        deriv (fun s => ρ s x) t - laplacian (I := I)
          (LeviCivita (I := I) (S.base.metric t)) (S.base.metric t) (ρ t) x := by
  classical
  have hleft_fin : riemannianEDist I O tail.splitPoint ≠ (⊤ : ENNReal) := by
    rw [tail.initial_edist]
    exact ENNReal.ofReal_ne_top
  obtain ⟨vLeft, hvLeft_exp, hvLeft_norm⟩ :=
    minExp_of_ne_top (I := I) (S.base.metric t) hEnorm O tail.splitPoint hleft_fin
  have hvLeft_norm' : Real.sqrt ((S.base.metric t).inner O vLeft vLeft) = tail.initialLength := by
    rw [hvLeft_norm, tail.initial_edist, ENNReal.toReal_ofReal tail.initialLength_nonneg]
  let eLeft : TangentSpace I O := tail.initialLength⁻¹ • vLeft
  let γ := intrinsicGeodesic (I := I) (S.base.metric t) hEnorm O eLeft
  let e : TangentSpace I tail.splitPoint := tail.terminalLength⁻¹ • tail.endpointVector
  let δ : M → ℝ → M := fun y => intrinsicGeodesic (I := I) (S.base.metric t) hEnorm tail.splitPoint
    (tail.terminalLength⁻¹ • (tangentSpaceModelContinuousLinearEquiv (I := I) tail.splitPoint).symm (tail.branch.inv y))
  let L₁ := fun s => arcLength (I := I) (S.base.metric s) γ 0 tail.initialLength
  let L₂ := fun s y => arcLength (I := I) (S.base.metric s) (δ y) 0 tail.terminalLength
  let ρ := fun s y => L₁ s + L₂ s y
  let ρ₀ := fun y => tail.initialLength + branchRadius (I := I) (S.base.metric t) tail.branch y
  have hleft_sq : (S.base.metric t).inner O vLeft vLeft = tail.initialLength ^ 2 := by
    rw [← Real.sq_sqrt (gInner_self_nonneg (I := I) (S.base.metric t) O vLeft), hvLeft_norm']
  have heLeft : (S.base.metric t).inner O eLeft eLeft = 1 := by
    dsimp only [eLeft]
    rw [gInner_smul_self, hleft_sq]
    field_simp [tail.initialLength_pos.ne']
  have hleft_scale : tail.initialLength • eLeft = vLeft := by
    dsimp only [eLeft]
    rw [smul_smul, mul_inv_cancel₀ tail.initialLength_pos.ne', one_smul]
  have hγzero : γ 0 = O := intrinsicGeodesic_zero (I := I) (S.base.metric t) hEnorm O eLeft
  have hγend : γ tail.initialLength = tail.splitPoint := by
    dsimp only [γ]
    rw [← intrinsicGeodesic_smul (I := I) (S.base.metric t) hEnorm O eLeft tail.initialLength,
      hleft_scale, ← expMapIntrinsic_def]
    exact hvLeft_exp
  have hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ := intrinsicGeodesic_contMDiff (I := I) (S.base.metric t) hEnorm O eLeft
  have hδ (y : M) : ContMDiff 𝓘(ℝ, ℝ) I ∞ (δ y) := intrinsicGeodesic_contMDiff (I := I) (S.base.metric t) hEnorm tail.splitPoint _
  have hδzero (y : M) : δ y 0 = tail.splitPoint := intrinsicGeodesic_zero (I := I) (S.base.metric t) hEnorm tail.splitPoint _
  have hδend (y : M) (hy : y ∈ tail.branch.dom) : δ y tail.terminalLength = y := by
    dsimp only [δ]
    rw [← intrinsicGeodesic_smul, smul_smul, mul_inv_cancel₀ tail.terminalLength_pos.ne', one_smul,
      ← expMapIntrinsic_def]
    exact tail.branch.right_inv hy
  have hL₁ : L₁ t = tail.initialLength := by
    dsimp only [L₁, γ]
    rw [arcLength_radial, heLeft, Real.sqrt_one, sub_zero, mul_one]
  have hL₂ (y : M) : L₂ t y = branchRadius (I := I) (S.base.metric t) tail.branch y := by
    dsimp only [L₂, δ]
    rw [arcLength_radial, sub_zero, gInner_smul_self,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs, abs_of_pos (inv_pos.mpr tail.terminalLength_pos),
      ← mul_assoc, mul_inv_cancel₀ tail.terminalLength_pos.ne', one_mul]
    rfl
  have hρslice : ρ t = ρ₀ := by
    funext y
    exact congrArg₂ (· + ·) hL₁ (hL₂ y)
  have hupper : ∀ᶠ y in 𝓝 x, ∀ s : ℝ,
      riemannianEDistOf (I := I) (S.base.metric s) O y ≤ ENNReal.ofReal (ρ s y) := by
    filter_upwards [tail.branch.hom.open_target.mem_nhds tail.target_mem] with y hy s
    have hed := edistOf_le_two_arcs (I := I) (S.base.metric s) tail.initialLength_nonneg tail.terminalLength_pos.le
      (hγ.of_le (by simp)).contMDiffOn ((hδ y).of_le (by simp)).contMDiffOn
      (hγend.trans (hδzero y).symm)
    rw [hγzero, hδend y hy] at hed
    have hL₁n : 0 ≤ L₁ s := intervalIntegral.integral_nonneg tail.initialLength_nonneg (fun _ _ => Real.sqrt_nonneg _)
    have hL₂n : 0 ≤ L₂ s y := intervalIntegral.integral_nonneg tail.terminalLength_pos.le (fun _ _ => Real.sqrt_nonneg _)
    simpa only [ρ, L₁, L₂, ENNReal.ofReal_add hL₁n hL₂n] using hed
  have hγunit (q : ℝ) : (S.base.metric t).inner (γ q)
      (curveVelocity (I := I) γ q) (curveVelocity (I := I) γ q) = 1 :=
    (intrinsicGeodesic_speedSq_eq (I := I) (S.base.metric t) hEnorm O eLeft q).trans heLeft
  have hγvel (q : ℝ) : curveVelocity (I := I) γ q ≠ 0 := by
    intro hzero
    have h := hγunit q
    rw [hzero, map_zero] at h
    exact zero_ne_one h
  have hδxeq : δ x = intrinsicGeodesic (I := I) (S.base.metric t) hEnorm tail.splitPoint e := by
    have hinv : tail.branch.inv x = (tail.endpointVector : E) := by
      have h := tail.branch.left_inv tail.source_mem
      have hexp : expMapIntrinsic (I := I) (S.base.metric t) hEnorm tail.splitPoint
          ((tangentSpaceModelContinuousLinearEquiv (I := I) tail.splitPoint).symm (tail.endpointVector : E)) = x := by
        convert! tail.exp_eq using 1
      rw [hexp] at h
      exact h
    have hround : (tangentSpaceModelContinuousLinearEquiv (I := I) tail.splitPoint).symm
        (tail.endpointVector : E) = tail.endpointVector := by
      with_unfolding_all
        exact (tangentSpaceModelContinuousLinearEquiv (I := I) tail.splitPoint).symm_apply_apply tail.endpointVector
    dsimp only [δ, e]
    rw [hinv, hround]
  have he : (S.base.metric t).inner tail.splitPoint e e = 1 :=
    tail.inner_normalized_tangent
  have hδunit (q : ℝ) : (S.base.metric t).inner (δ x q)
      (curveVelocity (I := I) (δ x) q) (curveVelocity (I := I) (δ x) q) = 1 := by
    rw [hδxeq]
    exact (intrinsicGeodesic_speedSq_eq (I := I) (S.base.metric t) hEnorm tail.splitPoint e q).trans he
  have hδvel (q : ℝ) : curveVelocity (I := I) (δ x) q ≠ 0 := by
    intro hzero
    have h := hδunit q
    rw [hzero, map_zero] at h
    exact zero_ne_one h
  have hR : 0 < R := (add_pos tail.initialLength_pos ha).trans hreach
  have hγball (q : ℝ) (hq : q ∈ Icc (0 : ℝ) tail.initialLength) :
      riemannianEDist I O (γ q) < ENNReal.ofReal R := by
    have hd := intrinsicGeodesic_riemannianEDist_le (I := I) (S.base.metric t) hEnorm O eLeft hq.1
    rw [intrinsicGeodesic_zero, heLeft, Real.sqrt_one, sub_zero, one_mul] at hd
    have hqR : q < R := by linarith [hq.2]
    exact hd.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hR).mpr hqR)
  have hδball (q : ℝ) (hq : q ∈ Icc (0 : ℝ) a) :
      riemannianEDist I O (δ x q) < ENNReal.ofReal R := by
    have hd := intrinsicGeodesic_riemannianEDist_le (I := I) (S.base.metric t) hEnorm tail.splitPoint e hq.1
    rw [intrinsicGeodesic_zero, he, Real.sqrt_one, sub_zero, one_mul] at hd
    rw [← hδxeq] at hd
    calc
      riemannianEDist I O (δ x q) ≤ riemannianEDist I O tail.splitPoint + riemannianEDist I tail.splitPoint (δ x q) := Manifold.riemannianEDist_triangle
      _ ≤ ENNReal.ofReal tail.initialLength + ENNReal.ofReal q := add_le_add tail.initial_edist.le hd
      _ = ENNReal.ofReal (tail.initialLength + q) := (ENNReal.ofReal_add tail.initialLength_nonneg hq.1).symm
      _ < ENNReal.ofReal R := (ENNReal.ofReal_lt_ofReal_iff hR).mpr (by linarith [hq.2])
  have hleftTime := pathLength_timeDeriv_of_ricciFlow (I := I) S hS tail.initialLength_nonneg ht γ
    (hγ.of_le (by simp)) (fun q _ => hγvel q)
  have hrightTime := pathLength_timeDeriv_of_ricciFlow (I := I) S hS tail.terminalLength_pos.le ht (δ x)
    ((hδ x).of_le (by simp)) (fun q _ => hδvel q)
  have hL₁diff : DifferentiableAt ℝ L₁ t := hleftTime.differentiableAt
  have hL₂diff : DifferentiableAt ℝ (fun s => L₂ s x) t := hrightTime.differentiableAt
  have hL₁lower : -K * tail.initialLength ≤ deriv L₁ t := by
    rw [← hL₁]
    exact pathLength_deriv_ge_of_ricci_le (I := I) S hS tail.initialLength_nonneg ht γ
      (hγ.of_le (by simp)) (fun q _ => hγvel q)
      (fun q hq => hRic (γ q) (hγball q hq) _)
  have hend : intrinsicGeodesic (I := I) (S.base.metric t) hEnorm tail.splitPoint e tail.terminalLength = x :=
    tail.intrinsicGeodesic_normalized_tangent_ell
  have hscale : tail.terminalLength • e = tail.endpointVector := by
    dsimp only [e]
    rw [smul_smul, mul_inv_cancel₀ tail.terminalLength_pos.ne', one_smul]
  have hsrc : tangentSpaceModelContinuousLinearEquiv (I := I) tail.splitPoint (tail.terminalLength • e) ∈ tail.branch.hom.source := by
    rw [hscale]
    with_unfolding_all exact tail.source_mem
  have hmin : ∀ η : ℝ → M,
      ContMDiffOn 𝓘(ℝ, ℝ) I 1 η (Icc 0 tail.terminalLength) →
      η 0 = tail.splitPoint → η tail.terminalLength = intrinsicGeodesic (I := I) (S.base.metric t) hEnorm tail.splitPoint e tail.terminalLength →
      arcLength (I := I) (S.base.metric t)
        (intrinsicGeodesic (I := I) (S.base.metric t) hEnorm tail.splitPoint e) 0 tail.terminalLength ≤
        arcLength (I := I) (S.base.metric t) η 0 tail.terminalLength := by
    intro η hη hη0 hηell
    exact tail.arcLength_normalized_tangent_le hr hη hη0 (hηell.trans hend)
  have hRicNear : ∀ q ∈ Icc (0 : ℝ) a,
      let σ := intrinsicGeodesic (I := I) (S.base.metric t) hEnorm tail.splitPoint e;
      ricciTensor (I := I) (S.base.metric t) (σ q)
        (curveVelocity (I := I) σ q) (curveVelocity (I := I) σ q) ≤ K := by
    intro q hq
    have h := hRic (δ x q) (hδball q hq) (curveVelocity (I := I) (δ x) q)
    rw [hδunit, mul_one] at h
    rw [hδxeq] at h
    exact h
  have hrightLower := arcLength_deriv_sub_laplacian_branchRadius_ge_of_ricci_le_near_start
    (I := I) S hS ht hEnorm tail.splitPoint e ha haell hK he tail.branch hsrc hmin hRicNear
  dsimp only at hrightLower
  rw [hend, ← hδxeq] at hrightLower
  have hu : 0 < (S.base.metric t).inner tail.splitPoint tail.endpointVector tail.endpointVector := by
    apply Real.sqrt_pos.mp
    rw [tail.endpointVector_norm]
    exact tail.terminalLength_pos
  obtain ⟨U, hUopen, hxU, hbrU⟩ := branchRadius_open (I := I) tail.branch tail.source_mem hu
  rw [tail.exp_eq] at hxU
  have hbrSpace : ∀ᶠ y in 𝓝 x,
      MDifferentiableAt I 𝓘(ℝ, ℝ) (branchRadius (I := I) (S.base.metric t) tail.branch) y := by
    filter_upwards [hUopen.mem_nhds hxU] with y hy
    exact ((hbrU y hy).contMDiffAt (hUopen.mem_nhds hy)).mdifferentiableAt (by simp)
  have hbrGrad : MDiffAt (T% fun y : M => gradientFun (I := I) (S.base.metric t)
      (branchRadius (I := I) (S.base.metric t) tail.branch) y) x :=
    gradientFun_mdiffOn (I := I) (S.base.metric t) hUopen hbrU hxU
  have hlap : laplacian (I := I) (LeviCivita (I := I) (S.base.metric t))
      (S.base.metric t) ρ₀ x = laplacian (I := I) (LeviCivita (I := I) (S.base.metric t))
      (S.base.metric t) (branchRadius (I := I) (S.base.metric t) tail.branch) x :=
    laplacian_add_const (I := I) (LeviCivita (I := I) (S.base.metric t))
      (S.base.metric t) tail.initialLength hbrSpace hbrGrad
  obtain ⟨_, hρ₀x, hρ₀space, hρ₀grad, hρ₀sq⟩ :=
    calabi_support_regularity (I := I) (S.base.metric t) hEnorm tail
  refine ⟨ρ, ?_, hupper, hL₁diff.add hL₂diff, ?_, ?_, ?_, ?_⟩
  · rw [hρslice]
    exact hρ₀x
  · rw [hρslice]
    exact hρ₀space
  · rw [hρslice]
    exact hρ₀grad
  · rw [hρslice]
    exact hρ₀sq
  · have hd : deriv (fun s => ρ s x) t = deriv L₁ t + deriv (fun s => L₂ s x) t :=
      hL₁diff.hasDerivAt.add hL₂diff.hasDerivAt |>.deriv
    rw [hd, hρslice, hlap]
    change -(_ + K * (tail.initialLength + a)) ≤ deriv L₁ t + deriv (fun s => L₂ s x) t - _
    change -(_ + K * a) ≤ deriv (fun s => L₂ s x) t - _ at hrightLower
    linarith

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_distance_upper_support_of_ricci_le_on_ball
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) {t R K : ℝ} (ht : t ∈ D.regular)
    (hcomplete : RiemannianMetricComplete (I := I) (S.base.metric t))
    (O : M) (hR : 0 < R) (hK : 0 ≤ K)
    (hRic : ∀ y : M, riemannianEDistOf (I := I) (S.base.metric t) O y < ENNReal.ofReal R →
      ∀ v : TangentSpace I y, ricciTensor (I := I) (S.base.metric t) y v v ≤
        K * (S.base.metric t).inner y v v)
    (x : M) (hx : R ≤ (riemannianEDistOf (I := I) (S.base.metric t) O x).toReal) :
    ∃ ρ : ℝ → M → ℝ,
      ρ t x = (riemannianEDistOf (I := I) (S.base.metric t) O x).toReal ∧
      (∀ᶠ y in 𝓝 x, ∀ s : ℝ,
        riemannianEDistOf (I := I) (S.base.metric s) O y ≤ ENNReal.ofReal (ρ s y)) ∧
      DifferentiableAt ℝ (fun s => ρ s x) t ∧
      (∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (ρ t) y) ∧
      MDiffAt (T% fun y : M => gradientFun (I := I) (S.base.metric t) (ρ t) y) x ∧
      (S.base.metric t).inner x (gradientFun (I := I) (S.base.metric t) (ρ t) x)
        (gradientFun (I := I) (S.base.metric t) (ρ t) x) = 1 ∧
      -(2 * (Module.finrank ℝ E - 1 : ℝ) * Analysis.CutoffProfile.derivBound ^ 2 / R + K * R) ≤
        deriv (fun s => ρ s x) t - laplacian (I := I)
          (LeviCivita (I := I) (S.base.metric t)) (S.base.metric t) (ρ t) x := by
  classical
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let : T3Space M := inferInstance
  let : RiemannianBundle (fun y : M => TangentSpace I y) := ⟨(S.base.metric t).toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y) :=
    ⟨⟨(S.base.metric t).inner, (S.base.metric t).contMDiff.continuous,
      by intro y v w; rfl⟩⟩
  let : PseudoEMetricSpace M := PseudoEMetricSpace.ofRiemannianMetric I M
  let : CompleteSpace M := hcomplete.complete
  have hEnorm : IsMetricNorm (I := I) (M := M) (S.base.metric t) := by
    intro y w
    rw [← ofReal_norm, norm_eq_sqrt_real_inner]
    congr 2
  let r := (riemannianEDist I O x).toReal
  have hx' : R ≤ r := hx
  have hr : 0 < r := hR.trans_le hx'
  have hfin : riemannianEDist I O x ≠ (⊤ : ENNReal) := by
    intro htop
    have hz : r = 0 := by simp only [r, htop, ENNReal.toReal_top]
    linarith
  obtain ⟨v, hv_exp, hv_norm⟩ := minExp_of_ne_top (I := I) (S.base.metric t) hEnorm O x hfin
  let s₀ := R / (4 * r)
  have hs₀ : s₀ ∈ Ioo (0 : ℝ) 1 := by
    refine ⟨div_pos hR (mul_pos (by norm_num) hr), ?_⟩
    apply (div_lt_one (mul_pos (by norm_num) hr)).mpr
    linarith
  have hs₀half : s₀ ≤ 1 / 2 := by
    apply (div_le_iff₀ (mul_pos (by norm_num) hr)).mpr
    linarith
  obtain ⟨tail, hleft, hell⟩ := exists_calabiTail_of_split (I := I) (S.base.metric t) hEnorm (r := r) v hv_exp hv_norm hr rfl s₀ hs₀ hs₀half
  have hleft' : tail.initialLength = R / 4 := by
    rw [hleft]
    dsimp only [s₀]
    field_simp [hr.ne']
  have hell' : R / 2 ≤ tail.terminalLength := by
    linarith [tail.length_sum]
  have hreach : tail.initialLength + R / 2 < R := by rw [hleft']; linarith
  obtain ⟨ρ, hρx, hupper, htime, hspace, hgrad, hnorm, hbound⟩ :=
    distance_upper_support_of_tail (I := I) S hS ht hEnorm tail rfl (half_pos hR) hell' hreach hK hRic
  refine ⟨ρ, hρx, hupper, htime, hspace, hgrad, hnorm, ?_⟩
  have hcoef : (Module.finrank ℝ E - 1 : ℝ) * Analysis.CutoffProfile.derivBound ^ 2 / (R / 2) =
      2 * (Module.finrank ℝ E - 1 : ℝ) * Analysis.CutoffProfile.derivBound ^ 2 / R := by ring
  rw [hcoef, hleft'] at hbound
  have hKpart : K * (R / 4 + R / 2) ≤ K * R := mul_le_mul_of_nonneg_left (by linarith) hK
  linarith

end DifferentialGeometry.PDE.RicciFlow
