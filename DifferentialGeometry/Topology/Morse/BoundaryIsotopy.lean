import DifferentialGeometry.Topology.Morse.BoundaryRegularVectorField
import DifferentialGeometry.Topology.Morse.BoundaryPerturbation
import DifferentialGeometry.Topology.Diffeomorph.TimeDependentFlow
import DifferentialGeometry.Analysis.ODE.InvariantHyperplane
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.LevelTransport

open scoped ContDiff Manifold Topology

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

end DifferentialGeometry.Topology.Morse
