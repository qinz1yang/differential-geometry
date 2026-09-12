import DifferentialGeometry.Topology.Manifold.BoundaryVectorField
import DifferentialGeometry.Topology.Diffeomorph.BoundaryFlow
import DifferentialGeometry.Topology.Morse.BoundaryRegularVectorField
import DifferentialGeometry.Topology.Morse.Flow
import DifferentialGeometry.Topology.Morse.BoundaryPerturbation
import DifferentialGeometry.Topology.Diffeomorph.TimeDependentFlow
import DifferentialGeometry.Analysis.ODE.InvariantHyperplane
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.LevelTransport

open scoped ContDiff Manifold Topology

namespace Diffeomorph

private theorem compactSupportFlow_eq_collar_of_inverse_velocity
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {G H : Type*} [TopologicalSpace G] [TopologicalSpace H]
    {J : ModelWithCorners ℝ E G} {I : ModelWithCorners ℝ F H} [I.Boundaryless]
    {N M : Type*} [TopologicalSpace N] [ChartedSpace G N]
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    (c : PartialDiffeomorph (J.prod 𝓘(ℝ)) I (N × ℝ) M ∞)
    (X : (y : M) → TangentSpace I y)
    (hX : ContMDiff I I.tangent ∞ (fun y => (X y : TangentBundle I M)))
    (hXc : HasCompactSupport X)
    {A : Set N} {ε : ℝ} (hε : 0 < ε)
    (hsource : A ×ˢ Set.Ioo (-ε) ε ⊆ c.source)
    (hcoord : ∀ p ∈ A, ∀ t ∈ Set.Ioo (-ε) ε,
      mfderiv I (J.prod 𝓘(ℝ)) c.symm (c (p, t)) (X (c (p, t))) = (0, 1)) :
    ∀ p ∈ A, ∀ t ∈ Set.Ioo (-ε) ε,
      compactSupportFlow X hX hXc t (c (p, 0)) = c (p, t) := by
  have hvelocity (p : N) (hp : p ∈ A) (t : ℝ) (ht : t ∈ Set.Ioo (-ε) ε) :
      mfderiv (J.prod 𝓘(ℝ)) I c (p, t) (0, 1) = X (c (p, t)) := by
    have hpt := hsource (show (p, t) ∈ A ×ˢ Set.Ioo (-ε) ε from ⟨hp, ht⟩)
    have hct := c.toPartialEquiv.map_source hpt
    have hc := c.mdifferentiableAt (by simp) hpt
    have hi := c.symm.mdifferentiableAt (by simp) hct
    have hleft : (c.symm ∘ c) =ᶠ[𝓝 (p, t)] id := by
      filter_upwards [c.open_source.mem_nhds hpt] with q hq
      exact c.toPartialEquiv.left_inv hq
    have hcomp := mfderiv_comp (p, t) hi hc
    have hcancel :
        (mfderiv I (J.prod 𝓘(ℝ)) c.symm (c (p, t))).comp
          (mfderiv (J.prod 𝓘(ℝ)) I c (p, t)) = ContinuousLinearMap.id ℝ _ := by
      exact hcomp.symm.trans (hleft.mfderiv_eq.trans mfderiv_id)
    apply ((c.symm.isLocalDiffeomorphAt I (J.prod 𝓘(ℝ)) ∞ hct).mfderivToContinuousLinearEquiv
      (by simp)).injective
    change mfderiv I (J.prod 𝓘(ℝ)) c.symm (c (p, t))
        (mfderiv (J.prod 𝓘(ℝ)) I c (p, t) (0, 1)) =
      mfderiv I (J.prod 𝓘(ℝ)) c.symm (c (p, t)) (X (c (p, t)))
    rw [hcoord p hp t ht]
    exact DFunLike.congr_fun hcancel (0, 1)
  intro p hp t ht
  have hcurve : IsMIntegralCurveOn (I := I) (fun s => c (p, s)) X
      (Set.Ioo (-ε) ε) := by
    intro s hs
    have hps := hsource (show (p, s) ∈ A ×ˢ Set.Ioo (-ε) ε from ⟨hp, hs⟩)
    have hc := (c.mdifferentiableAt (by simp) hps).hasMFDerivAt
    have hpderiv : HasMFDerivAt 𝓘(ℝ) (J.prod 𝓘(ℝ)) (fun r : ℝ => (p, r)) s
        ((0 : ℝ →L[ℝ] TangentSpace J p).prod (ContinuousLinearMap.id ℝ ℝ)) :=
      (hasMFDerivAt_const p s).prodMk (hasMFDerivAt_id s)
    let L : (E × ℝ) →L[ℝ] F := mfderiv (J.prod 𝓘(ℝ)) I c (p, s)
    let v : F := X (c (p, s))
    have hLv : L (0, 1) = v := hvelocity p hp s hs
    have hderiv : L.comp ((0 : ℝ →L[ℝ] E).prod (ContinuousLinearMap.id ℝ ℝ)) =
        (1 : ℝ →L[ℝ] ℝ).smulRight v := by
      apply ContinuousLinearMap.ext
      intro r
      change L (0, r) = r • v
      calc
        L (0, r) = L (r • (0, 1)) := by simp
        _ = r • L (0, 1) := map_smul _ _ _
        _ = r • v := by rw [hLv]
    exact ((hc.comp s hpderiv).congr_mfderiv hderiv).hasMFDerivWithinAt
  have hzero : (0 : ℝ) ∈ Set.Ioo (-ε) ε := ⟨by linarith, hε⟩
  have heq := isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless (t₀ := 0)
    hzero (hX.of_le (by simp))
    ((isMIntegralCurve_compactSupportFlow X hX hXc (c (p, 0))).isMIntegralCurveOn _)
    hcurve (DFunLike.congr_fun (compactSupportFlow_zero X hX hXc) (c (p, 0)))
  exact heq ht

end Diffeomorph

namespace DifferentialGeometry.Topology.Morse

private theorem boundary_normal_invariant {n : ℕ}
    {v : ℝ → (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ)}
    {γ : ℝ → (Fin (n + 1) → ℝ)} (hγ : IsIntegralCurve γ v)
    (hv : ContDiff ℝ 1 (fun p : ℝ × (Fin (n + 1) → ℝ) => v p.1 p.2))
    (htangent : ∀ t z, z 0 = 0 → v t z 0 = 0) (s t : ℝ) :
    (γ s 0 = 0 ↔ γ t 0 = 0) ∧ (0 ≤ γ s 0 ↔ 0 ≤ γ t 0) := by
  let A : (Fin (n + 1) → ℝ) →L[ℝ] ℝ × (Fin n → ℝ) :=
    (ContinuousLinearMap.proj 0).prod
      (ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj i.succ))
  let w := fun u (p : ℝ × (Fin n → ℝ)) => A (v u (Fin.cons p.1 p.2))
  let η := fun u => A (γ u)
  have hη : IsIntegralCurve η w := by
    intro u
    have h := A.hasFDerivAt.comp_hasDerivAt u (hγ u)
    change HasDerivAt (A ∘ γ)
      (A (v u (Fin.cons (γ u 0) (Fin.tail (γ u))))) u
    rw [Fin.cons_self_tail]
    exact h
  have hcons : ContDiff ℝ 1
      (fun p : ℝ × (ℝ × (Fin n → ℝ)) => (Fin.cons p.2.1 p.2.2 : Fin (n + 1) → ℝ)) := by
    apply contDiff_pi.mpr
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact contDiff_snd.fst
    · exact (contDiff_apply ℝ ℝ j).comp contDiff_snd.snd
  have hw : ContDiff ℝ 1 (fun p : ℝ × (ℝ × (Fin n → ℝ)) => w p.1 p.2) :=
    A.contDiff.comp (hv.comp (contDiff_fst.prodMk hcons))
  have ht : ∀ u (x : Fin n → ℝ), (w u (0, x)).1 = 0 := by
    intro u x
    exact htangent u (Fin.cons 0 x) rfl
  exact ⟨hη.fst_eq_zero_iff_of_tangent hw ht s t,
    hη.fst_nonneg_iff_of_tangent hw ht s t⟩

private theorem image_halfspace_eq_of_iff {n : ℕ}
    (e : (Fin (n + 1) → ℝ) ≃ₘ[ℝ] (Fin (n + 1) → ℝ))
    (hhalf : ∀ x, 0 ≤ x 0 ↔ 0 ≤ e x 0)
    {P Q : (Fin (n + 1) → ℝ) → Prop}
    (h : ∀ x, 0 ≤ x 0 → (P x ↔ Q (e x))) :
    e '' {x | 0 ≤ x 0 ∧ P x} = {y | 0 ≤ y 0 ∧ Q y} := by
  ext y
  constructor
  · rintro ⟨x, ⟨hx, hp⟩, rfl⟩
    exact ⟨(hhalf x).mp hx, (h x hx).mp hp⟩
  · intro hy
    have hx : 0 ≤ e.symm y 0 := (hhalf (e.symm y)).mpr (by simpa using hy.1)
    exact ⟨e.symm y, ⟨hx, (h (e.symm y) hx).mpr (by simpa using hy.2)⟩,
      e.apply_symm_apply y⟩

theorem exists_isotopy_halfspace_sublevel_with_support {n : ℕ}
    {F : ℝ × (Fin (n + 1) → ℝ) → ℝ} {L : Set ℝ}
    {O : Set (Fin (n + 1) → ℝ)}
    (hF : ContDiff ℝ ∞ F)
    (hsupport : HasCompactSupport (fun p : ℝ × ((Fin n → ℝ) × Set.Ici (0 : ℝ)) =>
      deriv (fun t => F (t, Fin.cons (p.2.2 : ℝ) p.2.1)) p.1))
    (hL : IsClosed L) (hO : IsOpen O)
    (hKO : ((fun p : ℝ × ((Fin n → ℝ) × Set.Ici (0 : ℝ)) =>
        (p.1, (Fin.cons (p.2.2 : ℝ) p.2.1 : Fin (n + 1) → ℝ))) ''
      tsupport (fun p : ℝ × ((Fin n → ℝ) × Set.Ici (0 : ℝ)) =>
        deriv (fun t => F (t, Fin.cons (p.2.2 : ℝ) p.2.1)) p.1)) ∩ F ⁻¹' L ⊆ Set.univ ×ˢ O)
    (hregular : ∀ p : ℝ × (Fin (n + 1) → ℝ), 0 < p.2 0 → F p ∈ L →
      fderiv ℝ (fun z => F (p.1, z)) p.2 ≠ 0)
    (hboundary : ∀ p : ℝ × (Fin (n + 1) → ℝ), p.2 0 = 0 → F p ∈ L →
      fderiv ℝ (fun x => F (p.1, Fin.cons 0 x)) (Fin.tail p.2) ≠ 0) :
    ∃ H : ℝ → ((Fin (n + 1) → ℝ) ≃ₘ[ℝ] (Fin (n + 1) → ℝ)),
      ContDiff ℝ ∞ (fun p : ℝ × (Fin (n + 1) → ℝ) => H p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × (Fin (n + 1) → ℝ) => (H p.1).symm p.2) ∧
      H 0 = Diffeomorph.refl 𝓘(ℝ, Fin (n + 1) → ℝ) _ ∞ ∧
      (∀ t x, (x 0 = 0 ↔ H t x 0 = 0) ∧ (0 ≤ x 0 ↔ 0 ≤ H t x 0)) ∧
      (∀ t r, r ∈ interior L →
        H t '' {x | 0 ≤ x 0 ∧ F (0, x) = r} = {x | 0 ≤ x 0 ∧ F (t, x) = r} ∧
        H t '' {x | 0 ≤ x 0 ∧ F (0, x) < r} = {x | 0 ≤ x 0 ∧ F (t, x) < r} ∧
        H t '' {x | 0 ≤ x 0 ∧ F (0, x) ≤ r} = {x | 0 ≤ x 0 ∧ F (t, x) ≤ r}) ∧
      (∀ x, (∀ t, deriv (fun s => F (s, x)) t = 0) →
        ∀ t, H t x = x ∧ (H t).symm x = x) ∧
      ∃ K : Set (Fin (n + 1) → ℝ), IsCompact K ∧ K ⊆ O ∧
        ∀ t, Set.EqOn (H t) id Kᶜ ∧ Set.EqOn (H t).symm id Kᶜ := by
  obtain ⟨V, hV, hVc, hVs, hVb, hVz, hVe⟩ :=
    exists_contDiff_boundary_tangent_vector_field_on_halfspace_levels_with_tsupport_subset
      hF hsupport hL (isOpen_univ.prod hO) hKO hregular hboundary
  let H := fun t => Diffeomorph.timeDependentFlow V hV hVc 0 t
  have hH : ContDiff ℝ ∞ (fun p : ℝ × (Fin (n + 1) → ℝ) => H p.1 p.2) :=
    (Diffeomorph.contDiff_timeDependentFlow V hV hVc).comp
      (contDiff_const.prodMk (contDiff_fst.prodMk contDiff_snd))
  have hHi : ContDiff ℝ ∞ (fun p : ℝ × (Fin (n + 1) → ℝ) => (H p.1).symm p.2) :=
    (Diffeomorph.contDiff_timeDependentFlow_symm V hV hVc).comp
      (contDiff_const.prodMk (contDiff_fst.prodMk contDiff_snd))
  have hzero : H 0 = Diffeomorph.refl 𝓘(ℝ, Fin (n + 1) → ℝ) _ ∞ :=
    Diffeomorph.timeDependentFlow_refl V hV hVc 0
  have hγ (x : Fin (n + 1) → ℝ) :
      IsIntegralCurve (fun t => H t x) (fun t z => V (t, z)) :=
    Diffeomorph.isIntegralCurve_timeDependentFlow V hV hVc 0 x
  have hhalf (t : ℝ) (x : Fin (n + 1) → ℝ) :
      (x 0 = 0 ↔ H t x 0 = 0) ∧ (0 ≤ x 0 ↔ 0 ≤ H t x 0) := by
    have h := boundary_normal_invariant (hγ x) (hV.of_le (by simp))
      (fun s z hz => hVb (s, z) hz) 0 t
    simpa only [hzero, Diffeomorph.coe_refl, id_eq] using h
  have hstay (x : Fin (n + 1) → ℝ) (hx : 0 ≤ x 0) (t : ℝ) :
      (t, H t x) ∈ {p : ℝ × (Fin (n + 1) → ℝ) | 0 ≤ p.2 0} :=
    (hhalf t x).2.mp hx
  have hrate (t : ℝ) (x : Fin (n + 1) → ℝ) (hx : 0 ≤ x 0) (hr : F (t, x) ∈ interior L) :
      fderiv ℝ (fun z => F (t, z)) x (V (t, x)) = -deriv (fun s => F (s, x)) t :=
    hVe (t, x) hx (interior_subset hr)
  refine ⟨H, hH, hHi, hzero, hhalf, ?_, ?_, ?_⟩
  · intro t r hr
    refine ⟨image_halfspace_eq_of_iff (H t) (fun x => (hhalf t x).2) ?_,
      image_halfspace_eq_of_iff (H t) (fun x => (hhalf t x).2) ?_,
      image_halfspace_eq_of_iff (H t) (fun x => (hhalf t x).2) ?_⟩
    · intro x hx
      simpa only [hzero, Diffeomorph.coe_refl, id_eq] using
        (hγ x).level_eq_iff_of_transport_on (hF.differentiable (by simp))
          (hstay x hx) isOpen_interior hrate hr 0 t
    · intro x hx
      simpa only [hzero, Diffeomorph.coe_refl, id_eq] using
        (hγ x).sublevel_lt_iff_of_transport_on (hF.differentiable (by simp))
          (hstay x hx) isOpen_interior hrate hr 0 t
    · intro x hx
      simpa only [hzero, Diffeomorph.coe_refl, id_eq] using
        (hγ x).sublevel_le_iff_of_transport_on (hF.differentiable (by simp))
          (hstay x hx) isOpen_interior hrate hr 0 t
  · intro x hx t
    have hz : ∀ s, V (s, x) = 0 := fun s => hVz (s, x) (hx s)
    exact ⟨Diffeomorph.timeDependentFlow_apply_eq_self_of_forall_eq_zero V hV hVc hz 0 t,
      by
        change (Diffeomorph.timeDependentFlow V hV hVc 0 t).symm x = x
        rw [Diffeomorph.timeDependentFlow_symm]
        exact Diffeomorph.timeDependentFlow_apply_eq_self_of_forall_eq_zero V hV hVc hz t 0⟩
  · refine ⟨Prod.snd '' tsupport V, hVc.image continuous_snd, ?_,
      fun t => Diffeomorph.timeDependentFlow_eqOn_compl_image_tsupport V hV hVc 0 t⟩
    rintro x ⟨p, hp, rfl⟩
    exact (hVs hp).2

theorem exists_isotopy_halfspace_sublevel_of_regularFamily {n : ℕ}
    {F : ℝ × (Fin (n + 1) → ℝ) → ℝ} {L : Set ℝ}
    (hF : ContDiff ℝ ∞ F)
    (hsupport : HasCompactSupport (fun p : ℝ × ((Fin n → ℝ) × Set.Ici (0 : ℝ)) =>
      deriv (fun t => F (t, Fin.cons (p.2.2 : ℝ) p.2.1)) p.1))
    (hL : IsClosed L)
    (hregular : ∀ p : ℝ × (Fin (n + 1) → ℝ), 0 < p.2 0 → F p ∈ L →
      fderiv ℝ (fun z => F (p.1, z)) p.2 ≠ 0)
    (hboundary : ∀ p : ℝ × (Fin (n + 1) → ℝ), p.2 0 = 0 → F p ∈ L →
      fderiv ℝ (fun x => F (p.1, Fin.cons 0 x)) (Fin.tail p.2) ≠ 0) :
    ∃ H : ℝ → ((Fin (n + 1) → ℝ) ≃ₘ[ℝ] (Fin (n + 1) → ℝ)),
      ContDiff ℝ ∞ (fun p : ℝ × (Fin (n + 1) → ℝ) => H p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × (Fin (n + 1) → ℝ) => (H p.1).symm p.2) ∧
      H 0 = Diffeomorph.refl 𝓘(ℝ, Fin (n + 1) → ℝ) _ ∞ ∧
      (∀ t x, (x 0 = 0 ↔ H t x 0 = 0) ∧ (0 ≤ x 0 ↔ 0 ≤ H t x 0)) ∧
      (∀ t r, r ∈ interior L →
        H t '' {x | 0 ≤ x 0 ∧ F (0, x) = r} = {x | 0 ≤ x 0 ∧ F (t, x) = r} ∧
        H t '' {x | 0 ≤ x 0 ∧ F (0, x) < r} = {x | 0 ≤ x 0 ∧ F (t, x) < r} ∧
        H t '' {x | 0 ≤ x 0 ∧ F (0, x) ≤ r} = {x | 0 ≤ x 0 ∧ F (t, x) ≤ r}) ∧
      (∀ x, (∀ t, deriv (fun s => F (s, x)) t = 0) →
        ∀ t, H t x = x ∧ (H t).symm x = x) ∧
      ∃ K : Set (Fin (n + 1) → ℝ), IsCompact K ∧
        ∀ t, Set.EqOn (H t) id Kᶜ ∧ Set.EqOn (H t).symm id Kᶜ := by
  obtain ⟨H, hH, hHi, hzero, hhalf, hlevels, hstationary, K, hK, hKO, hfix⟩ :=
    exists_isotopy_halfspace_sublevel_with_support (O := Set.univ) hF hsupport hL
      isOpen_univ (by intro p hp; exact ⟨Set.mem_univ _, Set.mem_univ _⟩) hregular hboundary
  exact ⟨H, hH, hHi, hzero, hhalf, hlevels, hstationary, K, hK, hfix⟩

private theorem tsupport_deriv_boundaryMorseInterpolation_subset_box {n : ℕ} (c : Fin n → ℝ)
    (b : ContDiffBump (0 : Fin n → ℝ)) {a : ℝ} (ha : 0 < a) :
    tsupport (fun p : ℝ × ((Fin n → ℝ) × Set.Ici (0 : ℝ)) =>
      deriv (fun t => boundaryMorseInterpolation c b a (Real.smoothTransition t)
        (Fin.cons p.2.2.val p.2.1)) p.1) ⊆
      {p | p.2.2.val ≤ a ∧ ‖p.2.1‖ ≤ b.rOut} := by
  have hclosed : IsClosed
      {p : ℝ × ((Fin n → ℝ) × Set.Ici (0 : ℝ)) |
        p.2.2.val ≤ a ∧ ‖p.2.1‖ ≤ b.rOut} := by
    have hu : IsClosed
        {p : ℝ × ((Fin n → ℝ) × Set.Ici (0 : ℝ)) | p.2.2.val ≤ a} :=
      isClosed_le (by fun_prop) continuous_const
    have hx : IsClosed
        {p : ℝ × ((Fin n → ℝ) × Set.Ici (0 : ℝ)) | ‖p.2.1‖ ≤ b.rOut} :=
      isClosed_le (by fun_prop) continuous_const
    exact hu.inter hx
  apply closure_minimal ?_ hclosed
  intro p hp
  change deriv (fun t => boundaryMorseInterpolation c b a (Real.smoothTransition t)
    (Fin.cons p.2.2.val p.2.1)) p.1 ≠ 0 at hp
  have hu : p.2.2.val < a := by
    by_contra h
    apply hp
    have heq : (fun t => boundaryMorseInterpolation c b a (Real.smoothTransition t)
        (Fin.cons p.2.2.val p.2.1)) =
        fun _ => (∑ i : Fin n, c i * p.2.1 i ^ 2) + p.2.2.val := by
      funext t
      simpa only [Fin.cons_succ, Fin.cons_zero] using
        boundaryMorseInterpolation_eq_of_le c b ha (Real.smoothTransition t)
          (Fin.cons p.2.2.val p.2.1) (le_of_not_gt h)
    rw [heq, deriv_const]
  have hx : ‖p.2.1‖ < b.rOut := by
    by_contra h
    apply hp
    have heq : (fun t => boundaryMorseInterpolation c b a (Real.smoothTransition t)
        (Fin.cons p.2.2.val p.2.1)) =
        fun _ => (∑ i : Fin n, c i * p.2.1 i ^ 2) + p.2.2.val := by
      funext t
      simpa only [Fin.cons_succ, Fin.cons_zero] using
        boundaryMorseInterpolation_eq_of_le_norm c b a (Real.smoothTransition t)
          (Fin.cons p.2.2.val p.2.1)
          (by simpa only [Fin.tail_cons] using le_of_not_gt h)
    rw [heq, deriv_const]
  exact ⟨hu.le, hx.le⟩

private theorem image_tsupport_deriv_boundaryMorseInterpolation_subset_box {n : ℕ} (c : Fin n → ℝ)
    (b : ContDiffBump (0 : Fin n → ℝ)) {a : ℝ} (ha : 0 < a) :
    (fun p : ℝ × ((Fin n → ℝ) × Set.Ici (0 : ℝ)) =>
      (p.1, (Fin.cons p.2.2.val p.2.1 : Fin (n + 1) → ℝ))) ''
      tsupport (fun p : ℝ × ((Fin n → ℝ) × Set.Ici (0 : ℝ)) =>
        deriv (fun t => boundaryMorseInterpolation c b a (Real.smoothTransition t)
          (Fin.cons p.2.2.val p.2.1)) p.1) ⊆
      {p | 0 ≤ p.2 0 ∧ p.2 0 ≤ a ∧ ‖Fin.tail p.2‖ ≤ b.rOut} := by
  rintro p ⟨q, hq, rfl⟩
  have h := tsupport_deriv_boundaryMorseInterpolation_subset_box c b ha hq
  simpa only [Set.mem_ofPred_eq, Fin.cons_zero, Fin.tail_cons] using
    (show 0 ≤ q.2.2.val ∧ q.2.2.val ≤ a ∧ ‖q.2.1‖ ≤ b.rOut from
      ⟨q.2.2.property, h.1, h.2⟩)

theorem exists_isotopy_boundaryMorseInterpolation_with_support {n : ℕ} (c : Fin n → ℝ)
    (hc : ∀ i, c i ≠ 0) (b : ContDiffBump (0 : Fin n → ℝ)) :
    ∃ δ > 0, ∀ a ∈ Set.Ioc 0 δ,
      ∀ O : Set (Fin (n + 1) → ℝ), IsOpen O →
      {z | 0 ≤ z 0 ∧ z 0 ≤ a ∧ ‖Fin.tail z‖ ≤ b.rOut} ⊆ O →
      ∀ L : Set ℝ, IsClosed L → Disjoint L (Set.Icc 0 a) →
      let F := fun p : ℝ × (Fin (n + 1) → ℝ) =>
        boundaryMorseInterpolation c b a (Real.smoothTransition p.1) p.2
      ∃ H : ℝ → ((Fin (n + 1) → ℝ) ≃ₘ[ℝ] (Fin (n + 1) → ℝ)),
        ContDiff ℝ ∞ (fun p : ℝ × (Fin (n + 1) → ℝ) => H p.1 p.2) ∧
        ContDiff ℝ ∞ (fun p : ℝ × (Fin (n + 1) → ℝ) => (H p.1).symm p.2) ∧
        H 0 = Diffeomorph.refl 𝓘(ℝ, Fin (n + 1) → ℝ) _ ∞ ∧
        (∀ t x, (x 0 = 0 ↔ H t x 0 = 0) ∧ (0 ≤ x 0 ↔ 0 ≤ H t x 0)) ∧
        (∀ t r, r ∈ interior L →
          H t '' {x | 0 ≤ x 0 ∧ F (0, x) = r} = {x | 0 ≤ x 0 ∧ F (t, x) = r} ∧
          H t '' {x | 0 ≤ x 0 ∧ F (0, x) < r} = {x | 0 ≤ x 0 ∧ F (t, x) < r} ∧
          H t '' {x | 0 ≤ x 0 ∧ F (0, x) ≤ r} = {x | 0 ≤ x 0 ∧ F (t, x) ≤ r}) ∧
        (∀ x, (∀ t, deriv (fun s => F (s, x)) t = 0) →
          ∀ t, H t x = x ∧ (H t).symm x = x) ∧
        ∃ K : Set (Fin (n + 1) → ℝ), IsCompact K ∧ K ⊆ O ∧
          ∀ t, Set.EqOn (H t) id Kᶜ ∧ Set.EqOn (H t).symm id Kᶜ := by
  obtain ⟨δ, hδ, hreg⟩ := exists_pos_boundaryMorseInterpolation_regular_levels c hc b
  refine ⟨δ, hδ, ?_⟩
  intro a ha O hO hbox L hL hdisj
  let F := fun p : ℝ × (Fin (n + 1) → ℝ) =>
    boundaryMorseInterpolation c b a (Real.smoothTransition p.1) p.2
  have hF : ContDiff ℝ ∞ F :=
    (contDiff_boundaryMorseInterpolation c b a).comp
      ((Real.smoothTransition.contDiff.comp contDiff_fst).prodMk contDiff_snd)
  have hσ (t : ℝ) : Real.smoothTransition t ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨Real.smoothTransition.nonneg t, Real.smoothTransition.le_one t⟩
  have hnot (p) (hp : F p ∈ L) : F p ∉ Set.Icc 0 a :=
    fun h => Set.disjoint_left.mp hdisj hp h
  apply exists_isotopy_halfspace_sublevel_with_support hF
    (hasCompactSupport_deriv_boundaryMorseInterpolation c b ha.1) hL hO
  · intro p hp
    exact ⟨Set.mem_univ _, hbox
      (image_tsupport_deriv_boundaryMorseInterpolation_subset_box c b ha.1 hp.1)⟩
  · intro p hp hpL
    have h := (hreg a ha (Real.smoothTransition p.1) (hσ p.1) (F p)
      (hnot p hpL)).1 p.2 hp.le rfl
    rw [IsCriticalPointAt, mfderiv_eq_fderiv] at h
    exact h
  · intro p hp hpL
    have hpoint : Fin.cons 0 (Fin.tail p.2) = p.2 := by
      rw [← hp, Fin.cons_self_tail]
    have h := (hreg a ha (Real.smoothTransition p.1) (hσ p.1) (F p)
      (hnot p hpL)).2 (Fin.tail p.2) (by rw [hpoint])
    rw [IsCriticalPointAt, mfderiv_eq_fderiv] at h
    exact h

theorem exists_isotopy_boundaryMorseInterpolation {n : ℕ} (c : Fin n → ℝ)
    (hc : ∀ i, c i ≠ 0) (b : ContDiffBump (0 : Fin n → ℝ)) :
    ∃ δ > 0, ∀ a ∈ Set.Ioc 0 δ, ∀ L : Set ℝ, IsClosed L → Disjoint L (Set.Icc 0 a) →
      let F := fun p : ℝ × (Fin (n + 1) → ℝ) =>
        boundaryMorseInterpolation c b a (Real.smoothTransition p.1) p.2
      ∃ H : ℝ → ((Fin (n + 1) → ℝ) ≃ₘ[ℝ] (Fin (n + 1) → ℝ)),
        ContDiff ℝ ∞ (fun p : ℝ × (Fin (n + 1) → ℝ) => H p.1 p.2) ∧
        ContDiff ℝ ∞ (fun p : ℝ × (Fin (n + 1) → ℝ) => (H p.1).symm p.2) ∧
        H 0 = Diffeomorph.refl 𝓘(ℝ, Fin (n + 1) → ℝ) _ ∞ ∧
        (∀ t x, (x 0 = 0 ↔ H t x 0 = 0) ∧ (0 ≤ x 0 ↔ 0 ≤ H t x 0)) ∧
        (∀ t r, r ∈ interior L →
          H t '' {x | 0 ≤ x 0 ∧ F (0, x) = r} = {x | 0 ≤ x 0 ∧ F (t, x) = r} ∧
          H t '' {x | 0 ≤ x 0 ∧ F (0, x) < r} = {x | 0 ≤ x 0 ∧ F (t, x) < r} ∧
          H t '' {x | 0 ≤ x 0 ∧ F (0, x) ≤ r} = {x | 0 ≤ x 0 ∧ F (t, x) ≤ r}) ∧
        (∀ x, (∀ t, deriv (fun s => F (s, x)) t = 0) →
          ∀ t, H t x = x ∧ (H t).symm x = x) ∧
        ∃ K : Set (Fin (n + 1) → ℝ), IsCompact K ∧
          ∀ t, Set.EqOn (H t) id Kᶜ ∧ Set.EqOn (H t).symm id Kᶜ := by
  obtain ⟨δ, hδ, h⟩ := exists_isotopy_boundaryMorseInterpolation_with_support c hc b
  refine ⟨δ, hδ, ?_⟩
  intro a ha L hL hdisj
  obtain ⟨H, hH, hHi, hzero, hhalf, hlevels, hstationary, K, hK, hKO, hfix⟩ :=
    h a ha Set.univ isOpen_univ (Set.subset_univ _) L hL hdisj
  exact ⟨H, hH, hHi, hzero, hhalf, hlevels, hstationary, K, hK, hfix⟩

theorem exists_diffeomorph_image_boundaryMorsePerturbation_sublevels_with_support {n : ℕ}
    (c : Fin n → ℝ) (hc : ∀ i, c i ≠ 0) (b : ContDiffBump (0 : Fin n → ℝ))
    {lower upper : ℝ} (hlower : lower < 0) (hupper : 0 < upper) :
    ∃ δ > 0, ∀ a ∈ Set.Ioc 0 δ,
      ∀ O : Set (Fin (n + 1) → ℝ), IsOpen O →
      {z | 0 ≤ z 0 ∧ z 0 ≤ a ∧ ‖Fin.tail z‖ ≤ b.rOut} ⊆ O →
      ∃ Φ : (Fin (n + 1) → ℝ) ≃ₘ[ℝ] (Fin (n + 1) → ℝ),
        (∀ r ∈ ({lower, upper} : Set ℝ),
          Φ '' {x | 0 ≤ x 0 ∧ ((∑ i : Fin n, c i * x i.succ ^ 2) + x 0) ≤ r} =
            {x | 0 ≤ x 0 ∧ boundaryMorsePerturbation c b a x ≤ r}) ∧
        (∀ x, (x 0 = 0 ↔ Φ x 0 = 0) ∧ (0 ≤ x 0 ↔ 0 ≤ Φ x 0)) ∧
        (∀ x, a ≤ x 0 ∨ b.rOut ≤ ‖Fin.tail x‖ → Φ x = x ∧ Φ.symm x = x) ∧
        ∃ K : Set (Fin (n + 1) → ℝ), IsCompact K ∧ K ⊆ O ∧
          Set.EqOn Φ id Kᶜ ∧ Set.EqOn Φ.symm id Kᶜ := by
  obtain ⟨δ, hδ, h⟩ := exists_isotopy_boundaryMorseInterpolation_with_support c hc b
  refine ⟨min δ (upper / 4), lt_min hδ (by positivity), ?_⟩
  intro a ha O hO hbox
  have haδ : a ∈ Set.Ioc 0 δ := ⟨ha.1, ha.2.trans (min_le_left _ _)⟩
  have ha4 : a ≤ upper / 4 := ha.2.trans (min_le_right _ _)
  let L := Set.Iic (lower / 2) ∪ Set.Ici (upper / 2)
  have hLc : IsClosed L := isClosed_Iic.union isClosed_Ici
  have hLd : Disjoint L (Set.Icc 0 a) := by
    apply Set.disjoint_left.mpr
    intro r hr hrI
    rcases hr with hr | hr
    · change r ≤ lower / 2 at hr
      linarith [hrI.1]
    · change upper / 2 ≤ r at hr
      linarith [hrI.2]
  have hm : lower ∈ interior L := by
    apply interior_mono (Set.subset_union_left (s := Set.Iic (lower / 2)) (t := Set.Ici (upper / 2)))
    rw [interior_Iic]
    change lower < lower / 2
    linarith
  have hp : upper ∈ interior L := by
    apply interior_mono (Set.subset_union_right (s := Set.Iic (lower / 2)) (t := Set.Ici (upper / 2)))
    rw [interior_Ici]
    change upper / 2 < upper
    linarith
  obtain ⟨H, hH, hHi, h0, hnormal, himages, hfix, K, hK, hKO, hKfix⟩ := h a haδ O hO hbox L hLc hLd
  refine ⟨H 1, ?_, hnormal 1, ?_, K, hK, hKO, (hKfix 1).1, (hKfix 1).2⟩
  · intro r hr
    have hrL : r ∈ interior L := by
      rcases Set.mem_insert_iff.mp hr with hr | hr
      · rw [hr]
        exact hm
      · rw [Set.mem_singleton_iff.mp hr]
        exact hp
    simpa only [Real.smoothTransition.zero, Real.smoothTransition.one,
      boundaryMorseInterpolation_zero, boundaryMorseInterpolation_one] using (himages 1 r hrL).2.2
  · intro x hx
    apply hfix x ?_ 1
    intro s
    have heq : (fun t => boundaryMorseInterpolation c b a (Real.smoothTransition t) x) =
        fun _ => (∑ i : Fin n, c i * x i.succ ^ 2) + x 0 := by
      funext t
      rcases hx with hx | hx
      · exact boundaryMorseInterpolation_eq_of_le c b ha.1 _ x hx
      · exact boundaryMorseInterpolation_eq_of_le_norm c b a _ x hx
    rw [heq]
    exact deriv_const s _

theorem exists_diffeomorph_image_boundaryMorsePerturbation_sublevels {n : ℕ}
    (c : Fin n → ℝ) (hc : ∀ i, c i ≠ 0) (b : ContDiffBump (0 : Fin n → ℝ))
    {lower upper : ℝ} (hlower : lower < 0) (hupper : 0 < upper) :
    ∃ δ > 0, ∀ a ∈ Set.Ioc 0 δ,
      ∃ Φ : (Fin (n + 1) → ℝ) ≃ₘ[ℝ] (Fin (n + 1) → ℝ),
        (∀ r ∈ ({lower, upper} : Set ℝ),
          Φ '' {x | 0 ≤ x 0 ∧ ((∑ i : Fin n, c i * x i.succ ^ 2) + x 0) ≤ r} =
            {x | 0 ≤ x 0 ∧ boundaryMorsePerturbation c b a x ≤ r}) ∧
        (∀ x, (x 0 = 0 ↔ Φ x 0 = 0) ∧ (0 ≤ x 0 ↔ 0 ≤ Φ x 0)) ∧
        (∀ x, a ≤ x 0 ∨ b.rOut ≤ ‖Fin.tail x‖ → Φ x = x ∧ Φ.symm x = x) ∧
        ∃ K : Set (Fin (n + 1) → ℝ), IsCompact K ∧
          Set.EqOn Φ id Kᶜ ∧ Set.EqOn Φ.symm id Kᶜ := by
  obtain ⟨δ, hδ, h⟩ :=
    exists_diffeomorph_image_boundaryMorsePerturbation_sublevels_with_support c hc b hlower hupper
  refine ⟨δ, hδ, ?_⟩
  intro a ha
  obtain ⟨Φ, himages, hnormal, hfix, K, hK, hKO, hKfix⟩ :=
    h a ha Set.univ isOpen_univ (Set.subset_univ _)
  exact ⟨Φ, himages, hnormal, hfix, K, hK, hKfix⟩

open Set in
private theorem image_sublevel_compactSupportFlow_on_set
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ F H} [I.Boundaryless]
    {M : Type} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    {g : M → ℝ} (hg : ContMDiff I 𝓘(ℝ) ∞ g)
    (X : (x : M) → TangentSpace I x)
    (hX : ContMDiff I I.tangent ∞ (fun x => (X x : TangentBundle I M)))
    (hXc : IsCompact (tsupport X)) (D : Set M) {a b : ℝ} (hab : a ≤ b)
    (hunit : ∀ x ∈ D ∩ g ⁻¹' Icc a b,
      NormedSpace.fromTangentSpace (g x) (mfderiv I 𝓘(ℝ) g x (X x)) = 1)
    (hrate : ∀ x ∈ D,
      0 ≤ NormedSpace.fromTangentSpace (g x) (mfderiv I 𝓘(ℝ) g x (X x)) ∧
      NormedSpace.fromTangentSpace (g x) (mfderiv I 𝓘(ℝ) g x (X x)) ≤ 1)
    (hpreserve : ∀ t : ℝ, MapsTo (Diffeomorph.compactSupportFlow X hX hXc t) D D) :
    (Diffeomorph.compactSupportFlow X hX hXc (b - a)) ''
      (D ∩ sublevel g a) =
      D ∩ sublevel g b := by
  let Φ := Diffeomorph.compactSupportFlow X hX hXc
  let w : (x : M) → TangentSpace I x := fun x => -X x
  have hz (x : M) : Φ 0 x = x := by simp [Φ]
  have hrev (x : M) : IsMIntegralCurve (fun t => Φ (-t) x) w := by
    simpa only [Function.comp_def, mul_neg_one, neg_one_smul] using!
      (Diffeomorph.isMIntegralCurve_compactSupportFlow X hX hXc x).comp_mul (-1)
  let hc : ∀ x, ∃ γ, γ 0 = x ∧ IsMIntegralCurve γ w :=
    fun x => ⟨fun t => Φ (-t) x, by simpa only [neg_zero] using hz x, hrev x⟩
  have hw : ContMDiff I I.tangent 1 (fun x => (w x : TangentBundle I M)) :=
    hX.neg_section.of_le (by simp)
  have heq (x : M) (t : ℝ) : DifferentialGeometry.Analysis.ODE.curveAt w hc x t = Φ (-t) x := by
    apply congrFun (DifferentialGeometry.Analysis.ODE.integralCurve_eq_of_agree_zero w hw
      (DifferentialGeometry.Analysis.ODE.curveAt_integralCurve w hc x) (hrev x) ?_) t
    exact (DifferentialGeometry.Analysis.ODE.curveAt_zero w hc x).trans
      (by simpa only [neg_zero] using (hz x).symm)
  have hu : ∀ x ∈ D ∩ g ⁻¹' Icc a b,
      NormedSpace.fromTangentSpace (g x) (mfderiv I 𝓘(ℝ) g x (w x)) = -1 := by
    intro x hx
    let L : TangentSpace I x →L[ℝ] ℝ := mfderiv I 𝓘(ℝ) g x
    change L (-X x) = -1
    rw [map_neg]
    exact congrArg Neg.neg (hunit x hx)
  have hr : ∀ x ∈ D,
      -1 ≤ NormedSpace.fromTangentSpace (g x) (mfderiv I 𝓘(ℝ) g x (w x)) ∧
      NormedSpace.fromTangentSpace (g x) (mfderiv I 𝓘(ℝ) g x (w x)) ≤ 0 := by
    intro x hx
    let L : TangentSpace I x →L[ℝ] ℝ := mfderiv I 𝓘(ℝ) g x
    change -1 ≤ L (-X x) ∧ L (-X x) ≤ 0
    rw [map_neg]
    have h := hrate x hx
    change 0 ≤ L (X x) ∧ L (X x) ≤ 1 at h
    constructor <;> linarith
  have h := sublevel_transport_on_set_of_stripUnitSpeedVectorField
    g (hg.mdifferentiable (by simp)) hab w hw D hu hr hc
    (by intro t x hx; change DifferentialGeometry.Analysis.ODE.curveAt w hc x t ∈ D
        rw [heq]; exact hpreserve (-t) hx)
  simpa only [heq, neg_sub] using h

private theorem exists_product_boundary_chart
    {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (X : (x : M) → TangentSpace I x) {D : Set M}
    (d : PartialDiffeomorph I 𝓘(ℝ, Fin (n + 1) → ℝ) M (Fin (n + 1) → ℝ) ∞)
    {p : M} (hpd : p ∈ d.source)
    (hdD : d.toOpenPartialHomeomorph.IsImage D {z | 0 ≤ z 0})
    (htangent : ∀ x ∈ frontier D, x ∈ d.source →
      (mfderiv I 𝓘(ℝ, Fin (n + 1) → ℝ) d x (X x)) 0 = 0) :
    ∃ e : PartialDiffeomorph I 𝓘(ℝ, ℝ × (Fin n → ℝ)) M (ℝ × (Fin n → ℝ)) ∞,
      p ∈ e.source ∧ e.toOpenPartialHomeomorph.IsImage D {z | 0 ≤ z.1} ∧
      ∀ x ∈ frontier D ∩ e.source,
        (mfderiv I 𝓘(ℝ, ℝ × (Fin n → ℝ)) e x (X x)).1 = 0 := by
  let L : (Fin (n + 1) → ℝ) ≃L[ℝ] ℝ × (Fin n → ℝ) :=
    (Fin.consEquivL ℝ (fun _ : Fin (n + 1) => ℝ)).symm
  let e := d.trans L.toDiffeomorph.toPartialDiffeomorph
  have hed : e.source ⊆ d.source := fun _ hx => hx.1
  have heD : e.toOpenPartialHomeomorph.IsImage D {z | 0 ≤ z.1} := by
    intro x hx
    change 0 ≤ (L (d x)).1 ↔ x ∈ D
    change 0 ≤ d x 0 ↔ x ∈ D
    exact hdD (hed hx)
  refine ⟨e, ⟨hpd, Set.mem_univ _⟩, heD, ?_⟩
  intro x hx
  have hd : MDifferentiableAt I 𝓘(ℝ, Fin (n + 1) → ℝ) d x :=
    d.mdifferentiableAt (by simp) (hed hx.2)
  have hL : HasMFDerivAt 𝓘(ℝ, Fin (n + 1) → ℝ) 𝓘(ℝ, ℝ × (Fin n → ℝ))
      L (d x) L.toContinuousLinearMap := L.hasFDerivAt.hasMFDerivAt
  have he : mfderiv I 𝓘(ℝ, ℝ × (Fin n → ℝ)) e x =
      L.toContinuousLinearMap.comp (mfderiv I 𝓘(ℝ, Fin (n + 1) → ℝ) d x) :=
    (hL.comp x hd.hasMFDerivAt).mfderiv
  rw [he]
  change (mfderiv I 𝓘(ℝ, Fin (n + 1) → ℝ) d x (X x)) 0 = 0
  exact htangent x hx.1 (hed hx.2)

private theorem exists_boundary_field_with_collar_flow
    {n : ℕ} {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {G H : Type*} [TopologicalSpace G] [TopologicalSpace H]
    {J : ModelWithCorners ℝ E G} {I : ModelWithCorners ℝ F H} [I.Boundaryless]
    {N M : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J 1 N]
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    (c : PartialDiffeomorph (J.prod 𝓘(ℝ)) I (N × ℝ) M ∞)
    {g : M → ℝ} (hg : ContMDiff I 𝓘(ℝ) ∞ g) {a : ℝ}
    (hheight : ∀ p ∈ c.source, g (c p) = a + p.2)
    {A : Set N} (hA : IsCompact A) {ε : ℝ} (hε : 0 < ε)
    (hsource : A ×ˢ Set.Icc (-ε) ε ⊆ c.source)
    {D B O : Set M} (hB : IsCompact B) (hO : IsOpen O) (hBO : B ⊆ O)
    (htraceO : c '' (A ×ˢ Set.Icc (-ε) ε) ⊆ O)
    (htraceD : Disjoint (c '' (A ×ˢ Set.Icc (-ε) ε)) (frontier D))
    (hregular : ∀ p ∈ B, p ∉ frontier D → mfderiv I 𝓘(ℝ) g p ≠ 0)
    (hcharts : ∀ p ∈ frontier D,
      ∃ d : PartialDiffeomorph I 𝓘(ℝ, Fin (n + 1) → ℝ) M (Fin (n + 1) → ℝ) ∞,
        p ∈ d.source ∧ d.toOpenPartialHomeomorph.IsImage D {z | 0 ≤ z 0} ∧
        (p ∈ B → fderiv ℝ (fun u : Fin n → ℝ => g (d.symm (Fin.cons 0 u)))
          (Fin.tail (d p)) ≠ 0)) :
    ∃ (X : (y : M) → TangentSpace I y)
      (hX : ContMDiff I I.tangent ∞ (fun y => (X y : TangentBundle I M)))
      (hXc : HasCompactSupport X),
      tsupport X ⊆ O ∧
      (∀ y, 0 ≤ NormedSpace.fromTangentSpace (g y) (mfderiv I 𝓘(ℝ) g y (X y)) ∧
        NormedSpace.fromTangentSpace (g y) (mfderiv I 𝓘(ℝ) g y (X y)) ≤ 1) ∧
      (∃ U, IsOpen U ∧ B ⊆ U ∧ U ⊆ O ∧
        ∀ y ∈ U, NormedSpace.fromTangentSpace (g y) (mfderiv I 𝓘(ℝ) g y (X y)) = 1) ∧
      (∀ (m : ℕ)
        (d : PartialDiffeomorph I 𝓘(ℝ, Fin (m + 1) → ℝ) M (Fin (m + 1) → ℝ) ∞),
        d.toOpenPartialHomeomorph.IsImage D {z | 0 ≤ z 0} →
        ∀ y ∈ frontier D, y ∈ d.source →
          (mfderiv I 𝓘(ℝ, Fin (m + 1) → ℝ) d y (X y)) 0 = 0) ∧
      (∀ t x,
        (Diffeomorph.compactSupportFlow X hX hXc t x ∈ frontier D ↔ x ∈ frontier D) ∧
        (Diffeomorph.compactSupportFlow X hX hXc t x ∈ D ↔ x ∈ D) ∧
        ((Diffeomorph.compactSupportFlow X hX hXc t).symm x ∈ frontier D ↔ x ∈ frontier D) ∧
        ((Diffeomorph.compactSupportFlow X hX hXc t).symm x ∈ D ↔ x ∈ D)) ∧
      (∀ t x, x ∉ tsupport X →
        Diffeomorph.compactSupportFlow X hX hXc t x = x ∧
        (Diffeomorph.compactSupportFlow X hX hXc t).symm x = x) ∧
      ∀ p ∈ A, ∀ t ∈ Set.Ioo (-ε) ε,
        Diffeomorph.compactSupportFlow X hX hXc t (c (p, 0)) = c (p, t) ∧
        (Diffeomorph.compactSupportFlow X hX hXc t).symm (c (p, t)) = c (p, 0) := by
  let T := c '' (A ×ˢ Set.Icc (-ε) ε)
  have hT : IsCompact T :=
    (hA.prod isCompact_Icc).image_of_continuousOn (c.contMDiffOn.continuousOn.mono hsource)
  have hTc : T ⊆ c.target := by
    rintro _ ⟨p, hp, rfl⟩
    exact c.toPartialEquiv.map_source (hsource hp)
  obtain ⟨X, hX, hXc, hXO, hrates, ⟨U, hU, hBTU, hUO, hunit⟩, hboundary,
      P, hP, hTP, hPc, hcoord⟩ :=
    Manifold.exists_contMDiff_boundary_tangent_vector_field_eq_collar_velocity c hg hheight hB hT hO hBO
      htraceO hTc htraceD hregular (by
        intro p hp
        obtain ⟨d, hpd, hdD, hreg⟩ := hcharts p hp.2
        exact ⟨d, hpd, hdD, hreg hp.1⟩)
  have hproductCharts : ∀ p ∈ frontier D, X p ≠ 0 →
      ∃ d : PartialDiffeomorph I 𝓘(ℝ, ℝ × (Fin n → ℝ)) M (ℝ × (Fin n → ℝ)) ∞,
        p ∈ d.source ∧ d.toOpenPartialHomeomorph.IsImage D {z | 0 ≤ z.1} ∧
        ∀ x ∈ frontier D ∩ d.source,
          (mfderiv I 𝓘(ℝ, ℝ × (Fin n → ℝ)) d x (X x)).1 = 0 := by
    intro p hp _
    obtain ⟨d, hpd, hdD, _⟩ := hcharts p hp
    exact exists_product_boundary_chart X d hpd hdD (hboundary n d hdD)
  have hpreserve := Diffeomorph.compactSupportFlow_mem_iff_of_boundary_tangent
    X hX hXc D hproductCharts
  refine ⟨X, hX, hXc, hXO, hrates,
    ⟨U, hU, (fun p hp => hBTU (Or.inl hp)), hUO, hunit⟩, hboundary,
    hpreserve, ?_, ?_⟩
  · intro t x hx
    exact ⟨(Diffeomorph.compactSupportFlow_eqOn_compl_tsupport X hX hXc t).1 hx,
      (Diffeomorph.compactSupportFlow_eqOn_compl_tsupport X hX hXc t).2 hx⟩
  · have hmotion := Diffeomorph.compactSupportFlow_eq_collar_of_inverse_velocity c X hX hXc hε
      (fun p hp => hsource ⟨hp.1, hp.2.1.le, hp.2.2.le⟩)
      (fun p hp t ht => hcoord _ (hTP ⟨(p, t), ⟨hp, ht.1.le, ht.2.le⟩, rfl⟩))
    intro p hp t ht
    have hforward := hmotion p hp t ht
    refine ⟨hforward, ?_⟩
    rw [← hforward]
    exact (Diffeomorph.compactSupportFlow X hX hXc t).symm_apply_apply _

open Set in
theorem exists_isotopy_eq_collar_preserving_domain
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {G : Type*} [TopologicalSpace G] {H : Type} [TopologicalSpace H]
    {J : ModelWithCorners ℝ E G} {I : ModelWithCorners ℝ F H} [I.Boundaryless]
    {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J 1 N]
    {M : Type} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    (c : PartialDiffeomorph (J.prod 𝓘(ℝ)) I (N × ℝ) M ∞)
    {g : M → ℝ} (hg : ContMDiff I 𝓘(ℝ) ∞ g) {a₀ : ℝ}
    (hheight : ∀ p ∈ c.source, g (c p) = a₀ + p.2)
    {A : Set N} (hA : IsCompact A) {ε : ℝ} (hε : 0 < ε)
    (hsource : A ×ˢ Icc (-ε) ε ⊆ c.source)
    {D B O : Set M} (hB : IsCompact B) (hO : IsOpen O) (hBO : B ⊆ O)
    (htraceO : c '' (A ×ˢ Icc (-ε) ε) ⊆ O)
    (htraceD : Disjoint (c '' (A ×ˢ Icc (-ε) ε)) (frontier D))
    (hregular : ∀ p ∈ B, p ∉ frontier D → mfderiv I 𝓘(ℝ) g p ≠ 0)
    (hcharts : ∀ p ∈ frontier D,
      ∃ d : PartialDiffeomorph I 𝓘(ℝ, Fin (n + 1) → ℝ) M (Fin (n + 1) → ℝ) ∞,
        p ∈ d.source ∧ d.toOpenPartialHomeomorph.IsImage D {z | 0 ≤ z 0} ∧
        (p ∈ B → fderiv ℝ (fun u : Fin n → ℝ => g (d.symm (Fin.cons 0 u)))
          (Fin.tail (d p)) ≠ 0)) :
    ∃ Φ : ℝ → Diffeomorph I I M M ∞,
      Φ 0 = Diffeomorph.refl I M ∞ ∧
      ContMDiff (𝓘(ℝ).prod I) I ∞ (fun p : ℝ × M => Φ p.1 p.2) ∧
      ContMDiff (𝓘(ℝ).prod I) I ∞ (fun p : ℝ × M => (Φ p.1).symm p.2) ∧
      (∀ t x,
        (Φ t x ∈ frontier D ↔ x ∈ frontier D) ∧
        (Φ t x ∈ D ↔ x ∈ D) ∧
        ((Φ t).symm x ∈ frontier D ↔ x ∈ frontier D) ∧
        ((Φ t).symm x ∈ D ↔ x ∈ D)) ∧
      (∃ K : Set M, IsCompact K ∧ K ⊆ O ∧
        ∀ t x, x ∉ K → Φ t x = x ∧ (Φ t).symm x = x) ∧
      (∀ p ∈ A, ∀ t ∈ Ioo (-ε) ε,
        Φ t (c (p, 0)) = c (p, t) ∧ (Φ t).symm (c (p, t)) = c (p, 0)) ∧
      (∀ a b, a ≤ b → D ∩ g ⁻¹' Icc a b ⊆ B →
        Φ (b - a) '' (D ∩ sublevel g a) = D ∩ sublevel g b) ∧
      ∃ δ > 0, ∀ x ∈ B, ∀ t ∈ Ioo (-δ) δ,
        g (Φ t x) = g x + t ∧ g ((Φ t).symm x) = g x - t := by
  obtain ⟨X, hX, hXc, hXO, hrates, ⟨U, hU, hBU, _, hunit⟩, _,
      hpreserve, hfixed, hmotion⟩ :=
    exists_boundary_field_with_collar_flow c hg hheight hA hε hsource
      hB hO hBO htraceO htraceD hregular hcharts
  let Φ := Diffeomorph.compactSupportFlow X hX hXc
  obtain ⟨δ, hδ, hlocal⟩ :=
    Diffeomorph.exists_pos_compactSupportFlow_height X hX hXc g hB hU hBU hunit
  refine ⟨Φ, Diffeomorph.compactSupportFlow_zero X hX hXc,
    Diffeomorph.contMDiff_compactSupportFlow X hX hXc,
    Diffeomorph.contMDiff_compactSupportFlow_symm X hX hXc,
    hpreserve, ⟨tsupport X, hXc, hXO, hfixed⟩, hmotion, ?_, δ, hδ, ?_⟩
  · intro a b hab hband
    exact image_sublevel_compactSupportFlow_on_set hg X hX hXc D hab
      (fun x hx => hunit x (hBU (hband hx))) (fun x _ => hrates x)
      (fun t x hx => (hpreserve t x).2.1.mpr hx)
  · intro x hx t ht
    refine ⟨(hlocal x hx t ht).2, ?_⟩
    have hinverse : (Φ t).symm = Φ (-t) :=
      Diffeomorph.compactSupportFlow_symm X hX hXc t
    rw [hinverse]
    have hneg : -t ∈ Ioo (-δ) δ := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    simpa only [sub_eq_add_neg] using (hlocal x hx (-t) hneg).2


theorem exists_isotopy_eq_collar_preserving_halfspace
    {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
    {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J 1 N]
    (Φ : OpenPartialHomeomorph (N × ℝ) (Fin (n + 1) → ℝ))
    (hΦ : ContMDiffOn (J.prod 𝓘(ℝ)) 𝓘(ℝ, Fin (n + 1) → ℝ) ∞ Φ Φ.source)
    (hi : ContMDiffOn 𝓘(ℝ, Fin (n + 1) → ℝ) (J.prod 𝓘(ℝ)) ∞ Φ.symm Φ.target)
    {g : (Fin (n + 1) → ℝ) → ℝ} (hg : ContDiff ℝ ∞ g) {c : ℝ}
    (hheight : ∀ q ∈ Φ.source, g (Φ q) = c + q.2)
    {A : Set N} (hA : IsCompact A) {ε : ℝ} (hε : 0 < ε)
    (hw : A ×ˢ Set.Icc (-ε) ε ⊆ Φ.source)
    (hplane : ∀ x ∈ Φ '' (A ×ˢ Set.Icc (-ε) ε), x 0 ≠ 0)
    {B W : Set (Fin (n + 1) → ℝ)}
    (hB : IsCompact B) (hW : IsOpen W) (hBW : B ⊆ W)
    (hTW : Φ '' (A ×ˢ Set.Icc (-ε) ε) ⊆ W)
    (hregular : ∀ x ∈ B, x 0 ≠ 0 → fderiv ℝ g x ≠ 0)
    (hboundary : ∀ x ∈ B, x 0 = 0 →
      fderiv ℝ (fun z : Fin n → ℝ => g (Fin.cons 0 z)) (Fin.tail x) ≠ 0) :
    ∃ H : ℝ → ((Fin (n + 1) → ℝ) ≃ₘ[ℝ] (Fin (n + 1) → ℝ)),
      H 0 = Diffeomorph.refl 𝓘(ℝ, Fin (n + 1) → ℝ) _ ∞ ∧
      ContMDiff (𝓘(ℝ).prod 𝓘(ℝ, Fin (n + 1) → ℝ)) 𝓘(ℝ, Fin (n + 1) → ℝ) ∞
        (fun q : ℝ × (Fin (n + 1) → ℝ) => H q.1 q.2) ∧
      ContMDiff (𝓘(ℝ).prod 𝓘(ℝ, Fin (n + 1) → ℝ)) 𝓘(ℝ, Fin (n + 1) → ℝ) ∞
        (fun q : ℝ × (Fin (n + 1) → ℝ) => (H q.1).symm q.2) ∧
      (∀ t x, (x 0 = 0 ↔ H t x 0 = 0) ∧ (0 ≤ x 0 ↔ 0 ≤ H t x 0)) ∧
      ∃ K : Set (Fin (n + 1) → ℝ), IsCompact K ∧ K ⊆ W ∧
        (∀ t, Set.EqOn (H t) id Kᶜ ∧ Set.EqOn (H t).symm id Kᶜ) ∧
        (∀ p ∈ A, ∀ t ∈ Set.Ioo (-ε) ε, H t (Φ (p, 0)) = Φ (p, t)) ∧
        (∀ a b, a ≤ b → ({x | 0 ≤ x 0} ∩ g ⁻¹' Set.Icc a b) ⊆ B →
          H (b - a) '' ({x | 0 ≤ x 0} ∩ sublevel g a) =
            {x | 0 ≤ x 0} ∩ sublevel g b) ∧
        ∃ δ > 0, ∀ x ∈ B, ∀ t ∈ Set.Ioo (-δ) δ,
          g (H t x) = g x + t ∧ g ((H t).symm x) = g x - t := by
  let cΦ : PartialDiffeomorph (J.prod 𝓘(ℝ)) 𝓘(ℝ, Fin (n + 1) → ℝ)
      (N × ℝ) (Fin (n + 1) → ℝ) ∞ :=
    { toPartialEquiv := Φ.toPartialEquiv
      open_source := Φ.open_source
      open_target := Φ.open_target
      contMDiffOn_toFun := hΦ
      contMDiffOn_invFun := hi }
  have hfrontier : frontier {x : Fin (n + 1) → ℝ | 0 ≤ x 0} = {x | x 0 = 0} := by
    change frontier ((fun x : Fin (n + 1) → ℝ => x 0) ⁻¹' Set.Ici 0) =
      (fun x : Fin (n + 1) → ℝ => x 0) ⁻¹' {0}
    rw [← (isOpenMap_eval (0 : Fin (n + 1))).preimage_frontier_eq_frontier_preimage
      (continuous_apply 0) (Set.Ici 0), frontier_Ici]
  obtain ⟨H, hzero, hH, hHi, hpreserve, ⟨K, hK, hKW, hfixed⟩,
      hmotion, himages, hlocal⟩ :=
    exists_isotopy_eq_collar_preserving_domain (n := n) cΦ
      (contMDiff_iff_contDiff.mpr hg) hheight hA hε hw hB hW hBW hTW
      (D := {x | 0 ≤ x 0})
      (by
        apply Set.disjoint_left.mpr
        intro x hx hxf
        exact hplane x hx (by simpa only [hfrontier, Set.mem_ofPred_eq] using hxf))
      (by
        intro x hx hn
        simpa only [mfderiv_eq_fderiv] using! hregular x hx
          (by simpa only [hfrontier, Set.mem_ofPred_eq] using hn))
      (by
        intro x hx
        refine ⟨(Diffeomorph.refl 𝓘(ℝ, Fin (n + 1) → ℝ) _ ∞).toPartialDiffeomorph,
          Set.mem_univ x, ?_, ?_⟩
        · intro y _
          rfl
        · intro hxB
          exact hboundary x hxB (by simpa only [hfrontier, Set.mem_ofPred_eq] using hx))
  refine ⟨H, hzero, hH, hHi, ?_, K, hK, hKW, ?_, ?_, himages, hlocal⟩
  · intro t x
    have hf := (hpreserve t x).1
    rw [hfrontier] at hf
    exact ⟨hf.symm, (hpreserve t x).2.1.symm⟩
  · intro t
    exact ⟨fun x hx => (hfixed t x hx).1, fun x hx => (hfixed t x hx).2⟩
  · intro p hp t ht
    exact (hmotion p hp t ht).1

open Set in
theorem exists_isotopy_image_sublevel_of_compact_regular_band
    {n : ℕ} {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F]
    {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ F H} [I.Boundaryless]
    {M : Type} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    {g : M → ℝ} (hg : ContMDiff I 𝓘(ℝ) ∞ g)
    {a b : ℝ} (hab : a ≤ b) {D O : Set M}
    (hB : IsCompact (D ∩ g ⁻¹' Icc a b)) (hO : IsOpen O)
    (hBO : D ∩ g ⁻¹' Icc a b ⊆ O)
    (hregular : ∀ p ∈ D ∩ g ⁻¹' Icc a b,
      p ∉ frontier D → mfderiv I 𝓘(ℝ) g p ≠ 0)
    (hcharts : ∀ p ∈ frontier D,
      ∃ c : PartialDiffeomorph I 𝓘(ℝ, Fin (n + 1) → ℝ) M (Fin (n + 1) → ℝ) ∞,
        p ∈ c.source ∧ c.toOpenPartialHomeomorph.IsImage D {z | 0 ≤ z 0} ∧
        (p ∈ D ∩ g ⁻¹' Icc a b →
          fderiv ℝ (fun u : Fin n → ℝ => g (c.symm (Fin.cons 0 u)))
            (Fin.tail (c p)) ≠ 0)) :
    ∃ Φ : ℝ → Diffeomorph I I M M ∞,
      Φ 0 = Diffeomorph.refl I M ∞ ∧
      ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × M => Φ p.1 p.2) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × M => (Φ p.1).symm p.2) ∧
      (∀ (t : ℝ) (x : M),
        (Φ t x ∈ frontier D ↔ x ∈ frontier D) ∧
        (Φ t x ∈ D ↔ x ∈ D) ∧
        ((Φ t).symm x ∈ frontier D ↔ x ∈ frontier D) ∧
        ((Φ t).symm x ∈ D ↔ x ∈ D)) ∧
      (∃ K : Set M, IsCompact K ∧ K ⊆ O ∧
        ∀ (t : ℝ) (x : M), x ∉ K → Φ t x = x ∧ (Φ t).symm x = x) ∧
      Φ (b - a) '' (D ∩ sublevel g a) =
        D ∩ sublevel g b := by
  obtain ⟨X, hX, hXc, hXO, hrate, ⟨U, _, hBU, _, hunit⟩, htangent⟩ :=
    Manifold.exists_contMDiff_boundary_tangent_vector_field (n := n) hB hO hBO hg hregular
      (by
        intro p hp
        obtain ⟨c, hpc, hcD, hc⟩ := hcharts p hp.2
        exact ⟨c, hpc, hcD, hc hp.1⟩)
  let Φ := Diffeomorph.compactSupportFlow X hX hXc
  have hproductCharts : ∀ p ∈ frontier D, X p ≠ 0 →
      ∃ c : PartialDiffeomorph I 𝓘(ℝ, ℝ × (Fin n → ℝ)) M (ℝ × (Fin n → ℝ)) ∞,
        p ∈ c.source ∧ c.toOpenPartialHomeomorph.IsImage D {z | 0 ≤ z.1} ∧
        ∀ x ∈ frontier D ∩ c.source,
          (mfderiv I 𝓘(ℝ, ℝ × (Fin n → ℝ)) c x (X x)).1 = 0 := by
    intro p hp _
    obtain ⟨c, hpc, hcD, _⟩ := hcharts p hp
    exact exists_product_boundary_chart X c hpc hcD (htangent n c hcD)
  have hpreserve := Diffeomorph.compactSupportFlow_mem_iff_of_boundary_tangent
    X hX hXc D hproductCharts
  have himage := image_sublevel_compactSupportFlow_on_set hg X hX hXc D hab
    (fun x hx => hunit x (hBU hx)) (fun x _ => hrate x)
    (fun t x hx => (hpreserve t x).2.1.mpr hx)
  refine ⟨Φ, Diffeomorph.compactSupportFlow_zero X hX hXc,
    Diffeomorph.contMDiff_compactSupportFlow X hX hXc,
    Diffeomorph.contMDiff_compactSupportFlow_symm X hX hXc,
    hpreserve, ⟨tsupport X, hXc, hXO, ?_⟩, himage⟩
  intro t x hx
  exact ⟨(Diffeomorph.compactSupportFlow_eqOn_compl_tsupport X hX hXc t).1 hx,
    (Diffeomorph.compactSupportFlow_eqOn_compl_tsupport X hX hXc t).2 hx⟩

end DifferentialGeometry.Topology.Morse
