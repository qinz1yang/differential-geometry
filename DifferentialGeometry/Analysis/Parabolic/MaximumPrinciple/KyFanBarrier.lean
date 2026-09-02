import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.EndomorphismScalarization
import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.FirstContact
import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.Reaction
import DifferentialGeometry.Geometry.Connection.NormalSection

set_option autoImplicit false

noncomputable section

open Bundle CovariantDerivative Filter Set
open DifferentialGeometry
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff Topology InnerProductSpace BigOperators NNReal

namespace PositiveSystem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
  [FiniteDimensional Real F]
variable {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace Real (V x)]
  [FiberBundle F V] [VectorBundle Real F V]
  [ContMDiffVectorBundle ∞ F V I]
  [IsContMDiffRiemannianBundle I ∞ F V]

theorem lowerKyFanSum_first_contact_impossible
    [NeZero (Module.finrank Real E)] [I.Boundaryless]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    [fiberFinite : ∀ y, FiniteDimensional Real (V y)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (cov : CovariantDerivative I F V)
    [ContMDiffCovariantDerivative cov ∞] (hcov : cov.IsMetricCompatible)
    {T : Real} (hT : 0 < T) {s t : Real}
    (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ T)
    (A : Real → Cₛ^∞⟮I; F →L[Real] F, (fun x : M ↦ V x →L[Real] V x)⟯)
    (hAsymm : ∀ q y,
      ((A q y : V y →L[Real] V y) : V y →ₗ[Real] V y).IsSymmetric)
    (x : M)
    (X : Real → (y : M) → TangentSpace I y)
    (reaction : (V x →L[Real] V x) → V x →L[Real] V x)
    (hreactionNull : satisfiesNullEigenvectorCondition reaction)
    (hApos : (A t x).IsPositive)
    {R : Real} (hR : ‖A t x‖ ≤ R) {K : NNReal}
    (hreactionLip : LipschitzOnWith K reaction
      {B : V x →L[Real] V x | B.IsPositive ∧ ‖B‖ ≤ 2 * R})
    {k : Nat} (hkpos : 0 < k) (hk : k ≤ Module.finrank Real F)
    (a : Real → M → Real)
    (ha_time : DifferentiableAt Real (fun q ↦ a q x) t)
    (ha_space : ContMDiff I 𝓘(Real, Real) ∞ (a t))
    {c f : Real} (hc : (K : Real) < c) (hf : 0 < f)
    (ha_lt : -a t x < f)
    (hscalar : c * f ≤
      parabolicOperatorWithDrift (I := I) G T X a t x)
    (hGconn : G.connection t = LeviCivita (I := I) (G.metric t))
    (hAt : DifferentiableAt Real (fun q ↦ A q x) t)
    (hevolution :
      deriv (fun q ↦ A q x) t =
        rawBundleEndomorphismConnLap (I := I) (G.metric t) cov
            (fun y ↦ A t y) x +
          HomConnectionGen.homBundleCovariantDerivativeGen
            I M F V F V cov cov (fun y ↦ A t y) x (X t x) +
          reaction (A t x))
    (htheta_nonneg :
      ∀ᶠ p in 𝓝[Icc s t ×ˢ (Set.univ : Set M)] (t, x),
        0 ≤ (hAsymm p.1 p.2).lowerKyFanSum k + (k : Real) * a p.1 p.2)
    (hcontact :
      (hAsymm t x).lowerKyFanSum k + (k : Real) * a t x = 0) :
    False := by
  let _ := fiberFinite
  have htmem : t ∈ Icc (0 : Real) T := ⟨hs.trans hst.le, ht⟩
  let fiberEquiv := (trivializationAt F V x).linearEquivAt Real x
    (mem_baseSet_trivializationAt F V x)
  have hkx : k ≤ Module.finrank Real (V x) := by
    rw [fiberEquiv.finrank_eq]
    exact hk
  obtain ⟨v₀, eigenvalue, hv₀, heigen, hsum⟩ :=
    hApos.toLinearMap.isSymmetric.exists_eigenframe_lowerKyFanSum_eq hkx
  obtain ⟨U, hU, hxU, v, hvOrth, hvx, hvNormal⟩ :=
    exists_orthonormal_normal_sections cov hcov x v₀ hv₀
  let trace : Real → M → Real := fun q y ↦
    ∑ i, inner Real (A q y (v i y)) (v i y)
  let psi : Real → M → Real := fun q y ↦ trace q y + (k : Real) * a q y
  let theta : Real → M → Real := fun q y ↦
    (hAsymm q y).lowerKyFanSum k + (k : Real) * a q y
  have hunit (i : Fin k) :
      ∀ᶠ y in 𝓝 x, inner Real (v i y) (v i y) = 1 := by
    filter_upwards [hU.mem_nhds hxU] with y hy
    simpa [orthonormal_iff_ite] using
      (orthonormal_iff_ite.mp (hvOrth y hy) i i)
  have hsupport₀ : ∀ᶠ p in 𝓝 (t, x), theta p.1 p.2 ≤ psi p.1 p.2 := by
    filter_upwards [continuousAt_snd.eventually (hU.mem_nhds hxU)] with p hp
    dsimp only [theta, psi, trace]
    simpa [add_comm] using
      add_le_add_right
        ((hAsymm p.1 p.2).lowerKyFanSum_le_frame
          (by
            let e := (trivializationAt F V p.2).linearEquivAt Real p.2
              (mem_baseSet_trivializationAt F V p.2)
            rw [e.finrank_eq]
            exact hk)
          (hvOrth p.2 hp))
        ((k : Real) * a p.1 p.2)
  have hsupport :
      ∀ᶠ p in 𝓝[Icc s t ×ˢ (Set.univ : Set M)] (t, x),
        theta p.1 p.2 ≤ psi p.1 p.2 :=
    hsupport₀.filter_mono inf_le_left
  have htrace_contact : trace t x = (hAsymm t x).lowerKyFanSum k := by
    dsimp only [trace]
    calc
      ∑ i, inner Real (A t x (v i x)) (v i x) =
          ∑ i, eigenvalue i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hvx i]
        change inner Real ((A t x).toLinearMap (v₀ i)) (v₀ i) = _
        rw [heigen i, inner_smul_left]
        simp [hv₀.norm_eq_one]
      _ = (hAsymm t x).lowerKyFanSum k := hsum
  have hpsi_eq : psi t x = theta t x := by
    dsimp only [psi, theta]
    rw [htrace_contact]
  have htheta_zero : theta t x = 0 := hcontact
  have htrace_smooth : ContMDiff I 𝓘(Real, Real) ∞ (trace t) := by
    dsimp only [trace]
    exact ContMDiff.sum (fun i _ ↦
      (ContMDiff.clm_bundle_apply (b := id) (A t).contMDiff
        (v i).contMDiff).inner_bundle (v i).contMDiff)
  have hpsi_smooth : ContMDiff I 𝓘(Real, Real) ∞ (psi t) := by
    dsimp only [psi]
    have hscaled : ContMDiff I 𝓘(Real, Real) ∞
        (fun y ↦ (k : Real) * a t y) :=
      contMDiff_const.mul ha_space
    exact htrace_smooth.add hscaled
  have hcontact_local :=
    derivWithin_sub_heatOperatorWithDrift_nonpos_of_lower_support
      (I := I) G X hst htheta_nonneg hsupport hpsi_eq htheta_zero
      BoundarylessManifold.isInteriorPoint
      (hpsi_smooth.mdifferentiableAt (by simp))
      (Filter.Eventually.of_forall fun y ↦
        hpsi_smooth.mdifferentiableAt (by simp))
      ((gradientFun_smooth (I := I) (G.metric t) hpsi_smooth).mdifferentiableAt
        (by simp))
  have htrace_time : DifferentiableAt Real (fun q ↦ trace q x) t := by
    dsimp only [trace]
    exact DifferentiableAt.fun_sum fun i _ ↦
      (hAt.clm_apply (differentiableAt_const (c := v i x))).inner Real
        (differentiableAt_const (c := v i x))
  have hpsi_time : DifferentiableAt Real (fun q ↦ psi q x) t := by
    dsimp only [psi]
    exact htrace_time.add (ha_time.const_mul (k : Real))
  have hlocal_deriv :
      derivWithin (fun q ↦ psi q x) (Icc s t) t =
        deriv (fun q ↦ psi q x) t :=
    hpsi_time.derivWithin
      ((uniqueDiffOn_Icc hst).uniqueDiffWithinAt ⟨hst.le, le_rfl⟩)
  have hglobal_deriv :
      derivWithin (fun q ↦ psi q x) (Icc 0 T) t =
        deriv (fun q ↦ psi q x) t :=
    hpsi_time.derivWithin
      ((uniqueDiffOn_Icc hT).uniqueDiffWithinAt htmem)
  have hcontact_global :
      parabolicOperatorWithDrift (I := I) G T X psi t x ≤ 0 := by
    unfold parabolicOperatorWithDrift
    rw [hglobal_deriv, ← hlocal_deriv]
    exact hcontact_local
  have ha_space_at (y : M) :
      MDifferentiableAt I 𝓘(Real, Real) (a t) y :=
    ha_space.mdifferentiableAt (by simp)
  have ha_grad (y : M) : MDiffAt
      (T% fun z : M ↦ gradientFun (I := I) (G.metric t) (a t) z) y :=
    (gradientFun_smooth (I := I) (G.metric t) ha_space).mdifferentiableAt
      (by simp)
  have htrace_space_at (y : M) :
      MDifferentiableAt I 𝓘(Real, Real) (trace t) y :=
    htrace_smooth.mdifferentiableAt (by simp)
  have htrace_grad : MDiffAt
      (T% fun z : M ↦ gradientFun (I := I) (G.metric t) (trace t) z) x :=
    (gradientFun_smooth (I := I) (G.metric t) htrace_smooth).mdifferentiableAt
      (by simp)
  have hscale := parabolic_smul (I := I) G T X (k : Real) a t x
    ha_time.differentiableWithinAt ha_space_at (ha_grad x)
  have hadd := parabolic_add (I := I) G T X trace
    (fun q y ↦ (k : Real) * a q y) t x
    htrace_time.differentiableWithinAt
    (ha_time.const_mul (k : Real)).differentiableWithinAt
    htrace_space_at
    (fun y ↦ (ha_space_at y).const_smul (k : Real))
    htrace_grad
    (by
      have heq :
          (T% fun y ↦ gradientFun (I := I) (G.metric t)
            (fun z ↦ (k : Real) * a t z) y) =
            (T% fun y ↦ (k : Real) •
              gradientFun (I := I) (G.metric t) (a t) y) := by
        funext y
        apply congrArg (fun z ↦ (⟨y, z⟩ : TotalSpace E (TangentSpace I)))
        exact gradientFun_const_smul (I := I) (G.metric t) (k : Real)
          (ha_space.mdifferentiableAt (by simp))
      rw [heq]
      exact mdifferentiableAt_const.smul_section (ha_grad x))
  have hpsi_operator :
      parabolicOperatorWithDrift (I := I) G T X psi t x =
        parabolicOperatorWithDrift (I := I) G T X trace t x +
          (k : Real) * parabolicOperatorWithDrift (I := I) G T X a t x := by
    rw [← hscale]
    exact hadd
  have htrace_operator :=
    parabolicOperatorWithDrift_sum_inner_endomorphism_apply_of_normal_eigenframe
      (I := I) G cov hcov hT htmem A v x X eigenvalue hGconn hAt
        (hAsymm t x) (fun i ↦ by
          rw [hvx i]
          change (A t x).toLinearMap (v₀ i) = _
          exact heigen i)
        hvNormal hunit
  have hresidual :
      deriv (fun q ↦ A q x) t -
            rawBundleEndomorphismConnLap (I := I) (G.metric t) cov
              (fun y ↦ A t y) x -
            HomConnectionGen.homBundleCovariantDerivativeGen
              I M F V F V cov cov (fun y ↦ A t y) x (X t x) =
        reaction (A t x) := by
    rw [hevolution]
    abel
  have htrace_reaction :
      parabolicOperatorWithDrift (I := I) G T X trace t x =
        ∑ i, inner Real (reaction (A t x) (v i x)) (v i x) := by
    rw [htrace_operator, hresidual]
  have henergy :
      ∑ i, eigenvalue i = hApos.toLinearMap.isSymmetric.lowerKyFanSum k := hsum
  have hphi_eq :
      hApos.toLinearMap.isSymmetric.lowerKyFanSum k =
        (k : Real) * (-a t x) := by
    have hsame : hApos.toLinearMap.isSymmetric = hAsymm t x := rfl
    rw [hsame]
    linarith [hcontact]
  have hkreal : 0 < (k : Real) := by exact_mod_cast hkpos
  have hphi :
      hApos.toLinearMap.isSymmetric.lowerKyFanSum k < (k : Real) * f := by
    rw [hphi_eq]
    exact mul_lt_mul_of_pos_left ha_lt hkreal
  have hreaction_pos :=
    sum_inner_reaction_add_mul_pos_of_lowerKyFanSum_lt_mul
      hreactionNull hApos hR hreactionLip hv₀ heigen henergy
        hkpos hc hf hphi
  have hreaction_pos' :
      0 < ∑ i, inner Real (reaction (A t x) (v i x)) (v i x) +
        (k : Real) * c * f := by
    simpa only [hvx] using hreaction_pos
  have hscalar_scaled :
      (k : Real) * c * f ≤
        (k : Real) * parabolicOperatorWithDrift (I := I) G T X a t x := by
    nlinarith
  have hpositive :
      0 < parabolicOperatorWithDrift (I := I) G T X psi t x := by
    rw [hpsi_operator, htrace_reaction]
    exact hreaction_pos'.trans_le (by
      simpa [add_comm] using
        add_le_add_left hscalar_scaled
          (∑ i, inner Real (reaction (A t x) (v i x)) (v i x)))
  exact (not_lt_of_ge hcontact_global) hpositive

end PositiveSystem
