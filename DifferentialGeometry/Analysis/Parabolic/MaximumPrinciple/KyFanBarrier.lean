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

private theorem positive_on_compact_slab_of_first_contact_impossible
    {theta : Real → M → Real} {s t : Real}
    {K : Set M} (hK : IsCompact K)
    (htheta : ContinuousOn (fun p : Real × M ↦ theta p.1 p.2)
      (Icc s t ×ˢ K))
    (hinitial : ∀ x ∈ K, 0 < theta s x)
    (hboundary : ∀ q ∈ Icc s t, ∀ x ∈ frontier K, 0 < theta q x)
    (hfirst : ∀ {q : Real} {x : M}, q ∈ Ioc s t → x ∈ interior K →
      (∀ᶠ p in 𝓝[Icc s q ×ˢ (Set.univ : Set M)] (q, x),
        0 ≤ theta p.1 p.2) → theta q x = 0 → False) :
    ∀ q ∈ Icc s t, ∀ x ∈ K, 0 < theta q x := by
  have exists_zero {q : Real} (hq : q ∈ Icc s t) {x : M} (hx : x ∈ K)
      (hqnonpos : theta q x ≤ 0) :
      ∃ r ∈ Icc s q, theta r x = 0 := by
    have hsq : s ≤ q := hq.1
    have htime : ContinuousOn (fun r : Real ↦ -theta r x) (Icc s q) := by
      exact htheta.neg.comp
        (continuous_id.prodMk continuous_const).continuousOn
        (fun r hr ↦ ⟨⟨hr.1, hr.2.trans hq.2⟩, hx⟩)
    have hzero : (0 : Real) ∈ Icc (-theta s x) (-theta q x) := by
      constructor
      · linarith [hinitial x hx]
      · linarith
    obtain ⟨r, hr, hrzero⟩ := intermediate_value_Icc hsq htime hzero
    exact ⟨r, hr, neg_eq_zero.mp hrzero⟩
  by_contra hnot
  push Not at hnot
  obtain ⟨q, hq, x, hx, hqx⟩ := hnot
  obtain ⟨r, hr, hrzero⟩ := exists_zero hq hx hqx
  let slab : Set (Real × M) := Icc s t ×ˢ K
  let zeroSet : Set (Real × M) :=
    slab ∩ (fun p : Real × M ↦ theta p.1 p.2) ⁻¹' {0}
  have hslabCompact : IsCompact slab := isCompact_Icc.prod hK
  have hzeroClosed : IsClosed zeroSet := by
    exact htheta.preimage_isClosed_of_isClosed hslabCompact.isClosed
      isClosed_singleton
  have hzeroCompact : IsCompact zeroSet :=
    hslabCompact.of_isClosed_subset hzeroClosed (by
      intro p hp
      exact hp.1)
  have hzeroNonempty : zeroSet.Nonempty := by
    refine ⟨(r, x), ?_⟩
    exact ⟨⟨⟨hr.1, hr.2.trans hq.2⟩, hx⟩, by simpa using hrzero⟩
  obtain ⟨p, hp, hpmin⟩ :=
    hzeroCompact.exists_isMinOn hzeroNonempty continuous_fst.continuousOn
  rcases p with ⟨tau, z⟩
  have hpSlab : (tau, z) ∈ slab := hp.1
  have htau : tau ∈ Icc s t := hpSlab.1
  have hzK : z ∈ K := hpSlab.2
  have hcontact : theta tau z = 0 := by
    simpa using hp.2
  have hstau : s < tau := by
    apply lt_of_le_of_ne htau.1
    intro heq
    subst tau
    exact (ne_of_gt (hinitial z hzK)) hcontact
  have hzNotFrontier : z ∉ frontier K := by
    intro hz
    exact (ne_of_gt (hboundary tau htau z hz)) hcontact
  have hzInterior : z ∈ interior K :=
    (mem_interior_iff_notMem_frontier hzK).2 hzNotFrontier
  have hnonneg : ∀ q ∈ Icc s tau, ∀ y ∈ K, 0 ≤ theta q y := by
    intro q hq y hy
    by_contra hneg
    have hqneg : theta q y < 0 := lt_of_not_ge hneg
    have hqt : q ∈ Icc s t := ⟨hq.1, hq.2.trans htau.2⟩
    obtain ⟨r, hr, hrzero⟩ := exists_zero hqt hy hqneg.le
    have hrlt : r < q := by
      apply lt_of_le_of_ne hr.2
      intro heq
      subst r
      linarith
    have hrzeroSet : (r, y) ∈ zeroSet := by
      exact ⟨⟨⟨hr.1, hr.2.trans hqt.2⟩, hy⟩, by simpa using hrzero⟩
    have htaur : tau ≤ r := hpmin hrzeroSet
    exact (not_lt_of_ge hq.2) (htaur.trans_lt hrlt)
  have hKnhds : K ∈ 𝓝 z :=
    mem_of_superset (isOpen_interior.mem_nhds hzInterior) interior_subset
  have hspace : ∀ᶠ p in 𝓝 (tau, z), p.2 ∈ K :=
    continuousAt_snd.eventually hKnhds
  have hspaceWithin :
      ∀ᶠ p in 𝓝[Icc s tau ×ˢ (Set.univ : Set M)] (tau, z), p.2 ∈ K :=
    hspace.filter_mono inf_le_left
  have hthetaNonneg :
      ∀ᶠ p in 𝓝[Icc s tau ×ˢ (Set.univ : Set M)] (tau, z),
        0 ≤ theta p.1 p.2 := by
    filter_upwards [self_mem_nhdsWithin, hspaceWithin] with p hpDomain hpK
    exact hnonneg p.1 hpDomain.1 p.2 hpK
  exact hfirst ⟨hstau, htau.2⟩ hzInterior hthetaNonneg hcontact

theorem lowerKyFanSum_first_contact_impossible
    [NeZero (Module.finrank Real E)]
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
    (hx : I.IsInteriorPoint x)
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
      hx
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
      (I := I) G cov hcov hT htmem A v x hx X eigenvalue hGconn hAt
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

theorem lowerKyFanSum_dirichlet_barrier_pos_on_compact_set
    [NeZero (Module.finrank Real E)]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    [fiberFinite : ∀ y, FiniteDimensional Real (V y)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (cov : Real → CovariantDerivative I F V)
    [∀ q, ContMDiffCovariantDerivative (cov q) ∞]
    (hcov : ∀ q, (cov q).IsMetricCompatible)
    {T : Real} (hT : 0 < T) {s t : Real}
    (hs : 0 ≤ s) (ht : t ≤ T)
    {k : Nat} (hkpos : 0 < k) (hk : k ≤ Module.finrank Real F)
    {Kset : Set M} (hKset : IsCompact Kset)
    (hKsetInterior : interior Kset ⊆ I.interior M)
    (A : Real → Cₛ^∞⟮I; F →L[Real] F, (fun x : M ↦ V x →L[Real] V x)⟯)
    (hAsymm : ∀ q y,
      ((A q y : V y →L[Real] V y) : V y →ₗ[Real] V y).IsSymmetric)
    (hApos : ∀ q ∈ Icc s t, ∀ y ∈ Kset, (A q y).IsPositive)
    (hphiCont : ContinuousOn (fun p : Real × M ↦
      (hAsymm p.1 p.2).lowerKyFanSum k) (Icc s t ×ˢ Kset))
    {R : Real} (hR : ∀ q ∈ Icc s t, ∀ y ∈ Kset, ‖A q y‖ ≤ R)
    (X : Real → (y : M) → TangentSpace I y)
    (reaction : Real → (y : M) →
      (V y →L[Real] V y) → V y →L[Real] V y)
    (hreactionNull : ∀ q y,
      satisfiesNullEigenvectorCondition (reaction q y))
    {Klip : NNReal}
    (hreactionLip : ∀ q ∈ Ioc s t, ∀ y ∈ interior Kset,
      LipschitzOnWith Klip (reaction q y)
        {B : V y →L[Real] V y | B.IsPositive ∧ ‖B‖ ≤ 2 * R})
    (f : Real → M → Real)
    (hfCont : ContinuousOn (fun p : Real × M ↦ f p.1 p.2)
      (Icc s t ×ˢ Kset))
    (hfInitial : ∀ y ∈ Kset,
      (k : Real) * f s y ≤ (hAsymm s y).lowerKyFanSum k)
    (hfBoundary : ∀ q ∈ Icc s t, ∀ y ∈ frontier Kset, f q y = 0)
    (hfPos : ∀ q ∈ Ioc s t, ∀ y ∈ interior Kset, 0 < f q y)
    (hfTime : ∀ q ∈ Ioc s t, ∀ y ∈ interior Kset,
      DifferentiableAt Real (fun r ↦ f r y) q)
    (hfSpace : ∀ q ∈ Ioc s t,
      ContMDiff I 𝓘(Real, Real) ∞ (f q))
    {c epsilon : Real} (hc : (Klip : Real) < c) (hepsilon : 0 < epsilon)
    (hfEquation : ∀ q ∈ Ioc s t, ∀ y ∈ interior Kset,
      parabolicOperatorWithDrift (I := I) G T X f q y = -c * f q y)
    (hGconn : ∀ q ∈ Ioc s t,
      G.connection q = LeviCivita (I := I) (G.metric q))
    (hAt : ∀ q ∈ Ioc s t, ∀ y ∈ interior Kset,
      DifferentiableAt Real (fun r ↦ A r y) q)
    (hevolution : ∀ q ∈ Ioc s t, ∀ y ∈ interior Kset,
      deriv (fun r ↦ A r y) q =
        rawBundleEndomorphismConnLap (I := I) (G.metric q) (cov q)
            (fun z ↦ A q z) y +
          HomConnectionGen.homBundleCovariantDerivativeGen
            I M F V F V (cov q) (cov q) (fun z ↦ A q z) y (X q y) +
          reaction q y (A q y)) :
    ∀ q ∈ Icc s t, ∀ y ∈ Kset,
      0 < (hAsymm q y).lowerKyFanSum k +
        (k : Real) * (epsilon * Real.exp (c * (q - s)) - f q y) := by
  let a : Real → M → Real := fun q y ↦
    epsilon * Real.exp (c * (q - s)) - f q y
  let theta : Real → M → Real := fun q y ↦
    (hAsymm q y).lowerKyFanSum k + (k : Real) * a q y
  have hthetaCont : ContinuousOn (fun p : Real × M ↦ theta p.1 p.2)
      (Icc s t ×ˢ Kset) := by
    have heCont : Continuous (fun p : Real × M ↦
        epsilon * Real.exp (c * (p.1 - s))) := by fun_prop
    have haCont : ContinuousOn (fun p : Real × M ↦ a p.1 p.2)
        (Icc s t ×ˢ Kset) := by
      dsimp only [a]
      exact heCont.continuousOn.sub hfCont
    dsimp only [theta]
    exact hphiCont.add (continuousOn_const.mul haCont)
  have hkReal : 0 < (k : Real) := by exact_mod_cast hkpos
  have hinitial : ∀ y ∈ Kset, 0 < theta s y := by
    intro y hy
    have hdom := hfInitial y hy
    dsimp only [theta, a]
    rw [sub_self, mul_zero, Real.exp_zero, mul_one]
    nlinarith [mul_pos hkReal hepsilon]
  have hboundary : ∀ q ∈ Icc s t, ∀ y ∈ frontier Kset,
      0 < theta q y := by
    intro q hq y hy
    have hyK : y ∈ Kset := by
      have hyClosure : y ∈ closure Kset := frontier_subset_closure hy
      simpa [hKset.isClosed.closure_eq] using hyClosure
    have hphiNonneg := LinearMap.IsSymmetric.lowerKyFanSum_nonneg
      ((ContinuousLinearMap.isPositive_toLinearMap_iff (A q y)).mpr
        (hApos q hq y hyK)) k
    have hexp : 0 < epsilon * Real.exp (c * (q - s)) :=
      mul_pos hepsilon (Real.exp_pos _)
    dsimp only [theta, a]
    rw [hfBoundary q hq y hy, sub_zero]
    nlinarith
  apply positive_on_compact_slab_of_first_contact_impossible
    hKset hthetaCont hinitial hboundary
  intro q y hq hy hthetaNonneg hcontact
  have hqIcc : q ∈ Icc s t := ⟨hq.1.le, hq.2⟩
  have hyK : y ∈ Kset := interior_subset hy
  have hqT : q ≤ T := hq.2.trans ht
  have hfq := hfSpace q hq
  have haTime : DifferentiableAt Real (fun r ↦ a r y) q := by
    dsimp only [a]
    fun_prop
  have haSpace : ContMDiff I 𝓘(Real, Real) ∞ (a q) := by
    dsimp only [a]
    exact contMDiff_const.sub hfq
  have haLt : -a q y < f q y := by
    dsimp only [a]
    nlinarith [mul_pos hepsilon (Real.exp_pos (c * (q - s)))]
  let e : Real → M → Real := fun r _ ↦
    epsilon * Real.exp (c * (r - s))
  have huniq : UniqueDiffWithinAt Real (Icc 0 T) q :=
    (uniqueDiffOn_Icc hT).uniqueDiffWithinAt ⟨hs.trans hq.1.le, hqT⟩
  have heTime : DifferentiableWithinAt Real (fun r ↦ e r y) (Icc 0 T) q := by
    fun_prop
  have heSpace : ∀ z : M,
      MDifferentiableAt I 𝓘(Real, Real) (e q) z := by
    intro z
    exact mdifferentiableAt_const
  have heGrad : MDiffAt (T% fun z : M ↦
      gradientFun (I := I) (G.metric q) (e q) z) y := by
    have heq : (T% fun z : M ↦
        gradientFun (I := I) (G.metric q) (e q) z) =
        (T% fun z : M ↦ (0 : TangentSpace I z)) := by
      funext z
      apply congrArg (fun v ↦
        (⟨z, v⟩ : TotalSpace E (TangentSpace I : M → Type _)))
      exact gradientFun_const (I := I) (G.metric q)
        (epsilon * Real.exp (c * (q - s))) z
    rw [heq]
    exact mdifferentiableAt_zeroSection
      (𝕜 := Real) (F := E) (E := (TangentSpace I : M → Type _))
      (IB := I) (x := y)
  have hfSpaceAt : ∀ z : M,
      MDifferentiableAt I 𝓘(Real, Real) (f q) z := fun z ↦
    hfq.mdifferentiable (by simp) z
  have hfGrad : MDiffAt (T% fun z : M ↦
      gradientFun (I := I) (G.metric q) (f q) z) y :=
    (gradientFun_smooth (I := I) (G.metric q) hfq).mdifferentiableAt (by simp)
  have heDerivAt : HasDerivAt (fun r ↦ e r y) (c * e q y) q := by
    have hlinear : HasDerivAt (fun r : Real ↦ c * (r - s)) c q := by
      simpa using ((hasDerivAt_id q).sub_const s).const_mul c
    have hexp : HasDerivAt (fun r : Real ↦ Real.exp (c * (r - s)))
        (Real.exp (c * (q - s)) * c) q := hlinear.exp
    dsimp only [e]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hexp.const_mul epsilon
  have heOperator :
      parabolicOperatorWithDrift (I := I) G T X e q y = c * e q y := by
    unfold parabolicOperatorWithDrift heatOperatorWithDrift laplacianAt driftTerm gradientAt
    rw [heDerivAt.hasDerivWithinAt.derivWithin huniq,
      laplacian_const (I := I) (G.connection q) (G.metric q)
        (epsilon * Real.exp (c * (q - s))) y,
      gradientFun_const]
    simp
  have haOperator :
      parabolicOperatorWithDrift (I := I) G T X a q y =
        c * (epsilon * Real.exp (c * (q - s)) + f q y) := by
    have hsub := parabolic_sub (I := I) G T X e f q y
      heTime (hfTime q hq y hy).differentiableWithinAt
      heSpace hfSpaceAt heGrad hfGrad
    change parabolicOperatorWithDrift (I := I) G T X a q y = _ at hsub
    rw [hsub, heOperator, hfEquation q hq y hy]
    dsimp only [e]
    ring
  apply lowerKyFanSum_first_contact_impossible
    (I := I) G (cov q) (hcov q) hT hs hq.1 hqT A hAsymm y
      (hKsetInterior hy) X (reaction q y) (hreactionNull q y)
      (hApos q hqIcc y hyK) (hR q hqIcc y hyK)
      (hreactionLip q hq y hy) hkpos hk a haTime haSpace hc
      (hfPos q hq y hy) haLt
      (by rw [haOperator]; nlinarith [mul_pos hepsilon (Real.exp_pos (c * (q - s)))])
      (hGconn q hq) (hAt q hq y hy) (hevolution q hq y hy)
  · simpa only [theta] using hthetaNonneg
  · simpa only [theta] using hcontact

theorem lowerKyFanSum_pos_on_compact_set_of_dirichlet_solution
    [NeZero (Module.finrank Real E)]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    [fiberFinite : ∀ y, FiniteDimensional Real (V y)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (cov : Real → CovariantDerivative I F V)
    [∀ q, ContMDiffCovariantDerivative (cov q) ∞]
    (hcov : ∀ q, (cov q).IsMetricCompatible)
    {T : Real} (hT : 0 < T) {s t : Real}
    (hs : 0 ≤ s) (ht : t ≤ T)
    {k : Nat} (hkpos : 0 < k) (hk : k ≤ Module.finrank Real F)
    {Kset : Set M} (hKset : IsCompact Kset)
    (hKsetInterior : interior Kset ⊆ I.interior M)
    (A : Real → Cₛ^∞⟮I; F →L[Real] F, (fun x : M ↦ V x →L[Real] V x)⟯)
    (hAsymm : ∀ q y,
      ((A q y : V y →L[Real] V y) : V y →ₗ[Real] V y).IsSymmetric)
    (hApos : ∀ q ∈ Icc s t, ∀ y ∈ Kset, (A q y).IsPositive)
    (hphiCont : ContinuousOn (fun p : Real × M ↦
      (hAsymm p.1 p.2).lowerKyFanSum k) (Icc s t ×ˢ Kset))
    {R : Real} (hR : ∀ q ∈ Icc s t, ∀ y ∈ Kset, ‖A q y‖ ≤ R)
    (X : Real → (y : M) → TangentSpace I y)
    (reaction : Real → (y : M) →
      (V y →L[Real] V y) → V y →L[Real] V y)
    (hreactionNull : ∀ q y,
      satisfiesNullEigenvectorCondition (reaction q y))
    {Klip : NNReal}
    (hreactionLip : ∀ q ∈ Ioc s t, ∀ y ∈ interior Kset,
      LipschitzOnWith Klip (reaction q y)
        {B : V y →L[Real] V y | B.IsPositive ∧ ‖B‖ ≤ 2 * R})
    (f : Real → M → Real)
    (hfCont : ContinuousOn (fun p : Real × M ↦ f p.1 p.2)
      (Icc s t ×ˢ Kset))
    (hfInitial : ∀ y ∈ Kset,
      (k : Real) * f s y ≤ (hAsymm s y).lowerKyFanSum k)
    (hfBoundary : ∀ q ∈ Icc s t, ∀ y ∈ frontier Kset, f q y = 0)
    (hfPos : ∀ q ∈ Ioc s t, ∀ y ∈ interior Kset, 0 < f q y)
    (hfTime : ∀ q ∈ Ioc s t, ∀ y ∈ interior Kset,
      DifferentiableAt Real (fun r ↦ f r y) q)
    (hfSpace : ∀ q ∈ Ioc s t,
      ContMDiff I 𝓘(Real, Real) ∞ (f q))
    {c : Real} (hc : (Klip : Real) < c)
    (hfEquation : ∀ q ∈ Ioc s t, ∀ y ∈ interior Kset,
      parabolicOperatorWithDrift (I := I) G T X f q y = -c * f q y)
    (hGconn : ∀ q ∈ Ioc s t,
      G.connection q = LeviCivita (I := I) (G.metric q))
    (hAt : ∀ q ∈ Ioc s t, ∀ y ∈ interior Kset,
      DifferentiableAt Real (fun r ↦ A r y) q)
    (hevolution : ∀ q ∈ Ioc s t, ∀ y ∈ interior Kset,
      deriv (fun r ↦ A r y) q =
        rawBundleEndomorphismConnLap (I := I) (G.metric q) (cov q)
            (fun z ↦ A q z) y +
          HomConnectionGen.homBundleCovariantDerivativeGen
            I M F V F V (cov q) (cov q) (fun z ↦ A q z) y (X q y) +
          reaction q y (A q y)) :
    ∀ q ∈ Ioc s t, ∀ y ∈ interior Kset,
      0 < (hAsymm q y).lowerKyFanSum k := by
  intro q hq y hy
  have hkReal : 0 < (k : Real) := by exact_mod_cast hkpos
  have hexp : 0 < Real.exp (c * (q - s)) := Real.exp_pos _
  have hlimit : (k : Real) * f q y ≤
      (hAsymm q y).lowerKyFanSum k := by
    apply le_of_forall_pos_le_add
    intro delta hdelta
    let epsilon : Real := delta / ((k : Real) * Real.exp (c * (q - s)))
    have hepsilon : 0 < epsilon :=
      div_pos hdelta (mul_pos hkReal hexp)
    have hbarrier := lowerKyFanSum_dirichlet_barrier_pos_on_compact_set
      (I := I) G cov hcov hT hs ht hkpos hk hKset hKsetInterior
        A hAsymm hApos hphiCont hR X reaction hreactionNull hreactionLip
        f hfCont hfInitial hfBoundary hfPos hfTime hfSpace hc hepsilon
        hfEquation hGconn hAt hevolution q ⟨hq.1.le, hq.2⟩ y (interior_subset hy)
    have hepsilonEq :
        (k : Real) * (epsilon * Real.exp (c * (q - s))) = delta := by
      dsimp only [epsilon]
      field_simp
    nlinarith
  exact (mul_pos hkReal (hfPos q hq y hy)).trans_le hlimit

end PositiveSystem
