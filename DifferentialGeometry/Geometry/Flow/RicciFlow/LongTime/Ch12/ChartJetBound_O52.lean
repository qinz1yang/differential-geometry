import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ChartODE_O52
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.JetBootstrap_O52
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# CH12-O52 G2b: bounded `C^{n+2}` of the chart map from small jets of `G̃ - P`

`chart_jet_bound_O52` (`[FROZEN] CH12-O52 G2`): `P` a smooth positive symmetric coefficient
field on an open `T`, `Kz ⊆ T` compact. There are `η > 0` and `C` such that every smooth
`Ψ : V → Kz` (`V ⊆ Kz` open) with `‖D^i (pullbackForm (P ∘ Ψ, DΨ) - P)‖ ≤ η` (`i ≤ n + 1`) has
`‖D^i Ψ‖ ≤ C` (`i ≤ n + 2`). Proof: `bootstrap_jet_bound_O52` for `w = (Ψ, DΨ)`,
`γ = (G̃, DG̃)`, `Φ = chartODE_O52 P`, on a compact value set built from coercivity of `P`.
-/

set_option autoImplicit false

open Set Metric
open scoped ContDiff
open DifferentialGeometry.CheegerGromovCompactness

namespace GC.LongTime.Ch12

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A positive bilinear form on a finite-dimensional space is invertible as `E →L E^*`. -/
theorem isInvertible_of_pos_O52 [FiniteDimensional ℝ E] {A : E →L[ℝ] E →L[ℝ] ℝ}
    (hpos : ∀ v, v ≠ 0 → 0 < A v v) : A.IsInvertible := by
  have hinj : Function.Injective A := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    by_contra h
    have := hpos v h
    rw [hv] at this
    simp at this
  have hdim : Module.finrank ℝ E = Module.finrank ℝ (E →L[ℝ] ℝ) :=
    (Subspace.dual_finrank_eq (K := ℝ) (V := E)).symm.trans
      (LinearMap.toContinuousLinearMap : (E →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (E →L[ℝ] ℝ)).finrank_eq
  have hsurj : Function.Surjective A :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim
      (f := (A : E →ₗ[ℝ] (E →L[ℝ] ℝ)))).1 hinj
  refine ⟨(LinearEquiv.ofBijective (A : E →ₗ[ℝ] (E →L[ℝ] ℝ)) ⟨hinj, hsurj⟩).toContinuousLinearEquiv,
    ?_⟩
  ext v
  rfl

/-- Uniform coercivity of a continuous positive family on a compact set. -/
theorem exists_coercive_O52 [FiniteDimensional ℝ E] {P : E → E →L[ℝ] E →L[ℝ] ℝ} {Kz : Set E}
    (hKz : IsCompact Kz) (hPc : ContinuousOn P Kz) (hpos : ∀ z ∈ Kz, ∀ v, v ≠ 0 → 0 < P z v v) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ z ∈ Kz, ∀ v, lam * ‖v‖ ^ 2 ≤ P z v v := by
  have hmem : ∀ z ∈ Kz, ∀ v : E, v ≠ 0 → (z, ‖v‖⁻¹ • v) ∈ Kz ×ˢ sphere (0 : E) 1 := by
    intro z hz v hv
    refine ⟨hz, ?_⟩
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.2 hv)]
  by_cases hne : (Kz ×ˢ sphere (0 : E) 1).Nonempty
  · have hcomp : IsCompact (Kz ×ˢ sphere (0 : E) 1) := hKz.prod (isCompact_sphere 0 1)
    have hcont : ContinuousOn (fun p : E × E => P p.1 p.2 p.2) (Kz ×ˢ sphere (0 : E) 1) :=
      ((hPc.comp continuousOn_fst (fun p hp => hp.1)).clm_apply continuousOn_snd).clm_apply
        continuousOn_snd
    obtain ⟨p0, hp0, hmin⟩ := hcomp.exists_isMinOn hne hcont
    have hp0ne : p0.2 ≠ 0 := by
      intro h
      have := hp0.2
      rw [mem_sphere_zero_iff_norm, h, norm_zero] at this
      exact zero_ne_one this
    refine ⟨P p0.1 p0.2 p0.2, hpos _ hp0.1 _ hp0ne, fun z hz v => ?_⟩
    rcases eq_or_ne v 0 with rfl | hv
    · simp
    · have h1 : P p0.1 p0.2 p0.2 ≤ P z (‖v‖⁻¹ • v) (‖v‖⁻¹ • v) :=
        isMinOn_iff.1 hmin _ (hmem z hz v hv)
      have hn : 0 < ‖v‖ := norm_pos_iff.2 hv
      simp only [map_smul, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul] at h1
      have h2 : P z v v = ‖v‖ ^ 2 * (‖v‖⁻¹ * (‖v‖⁻¹ * P z v v)) := by
        field_simp
      rw [h2]
      nlinarith [sq_nonneg ‖v‖, pow_pos hn 2]
  · refine ⟨1, one_pos, fun z hz v => ?_⟩
    rcases eq_or_ne v 0 with rfl | hv
    · simp
    · exact absurd ⟨_, hmem z hz v hv⟩ hne

/-- Norm bound of `N` from `pullbackForm (Q, N)` and coercivity of `Q`. -/
theorem norm_le_of_coercive_O52 {Q : E →L[ℝ] E →L[ℝ] ℝ} {lam c : ℝ} (hlam : 0 < lam)
    (hcoer : ∀ v, lam * ‖v‖ ^ 2 ≤ Q v v) (N : E →L[ℝ] E) (hG : ‖pullbackForm (Q, N)‖ ≤ c) :
    ‖N‖ ≤ max 1 (c / lam) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (le_trans zero_le_one (le_max_left _ _))
    fun v => ?_
  set R := max 1 (c / lam)
  have hR1 : 1 ≤ R := le_max_left _ _
  have h1 : lam * ‖N v‖ ^ 2 ≤ c * ‖v‖ ^ 2 := by
    calc lam * ‖N v‖ ^ 2 ≤ Q (N v) (N v) := hcoer (N v)
      _ = pullbackForm (Q, N) v v := rfl
      _ ≤ ‖pullbackForm (Q, N) v v‖ := Real.le_norm_self _
      _ ≤ ‖pullbackForm (Q, N)‖ * ‖v‖ * ‖v‖ := ContinuousLinearMap.le_opNorm₂ _ _ _
      _ ≤ c * ‖v‖ * ‖v‖ := by gcongr
      _ = c * ‖v‖ ^ 2 := by ring
  have h2 : ‖N v‖ ^ 2 ≤ (R * ‖v‖) ^ 2 := by
    have hc : c / lam ≤ R := le_max_right _ _
    have h3 : ‖N v‖ ^ 2 ≤ c / lam * ‖v‖ ^ 2 := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hlam]
      linarith
    calc ‖N v‖ ^ 2 ≤ c / lam * ‖v‖ ^ 2 := h3
      _ ≤ R * ‖v‖ ^ 2 := by gcongr
      _ ≤ R ^ 2 * ‖v‖ ^ 2 := by
        gcongr
        nlinarith
      _ = (R * ‖v‖) ^ 2 := by ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h2

/-- Jets of `D^i (G̃, DG̃)` from jets of `G̃` (helper of `chart_jet_bound_O52`). -/
theorem norm_iteratedFDeriv_pair_fderiv_le_O52 {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {g : E → F} {V : Set E} (hV : IsOpen V) (hg : ContDiffOn ℝ ∞ g V)
    {x : E} (hx : x ∈ V) (i : ℕ) :
    ‖iteratedFDeriv ℝ i (fun z => (g z, fderiv ℝ g z)) x‖ =
      max ‖iteratedFDeriv ℝ i g x‖ ‖iteratedFDeriv ℝ (i + 1) g x‖ := by
  have hga : ContDiffAt ℝ ∞ g x := hg.contDiffAt (hV.mem_nhds hx)
  have hda : ContDiffAt ℝ ∞ (fderiv ℝ g) x :=
    (hg.fderiv_of_isOpen hV (by exact_mod_cast le_top)).contDiffAt (hV.mem_nhds hx)
  rw [iteratedFDeriv_prodMk hga hda (by exact_mod_cast le_top),
    ContinuousMultilinearMap.opNorm_prod, norm_iteratedFDeriv_fderiv]

/-- Smoothness and jets of `G̃ = pullbackForm (P ∘ Ψ, DΨ)` (helper of `chart_jet_bound_O52`). -/
theorem pullback_jet_le_O52 {P : E → E →L[ℝ] E →L[ℝ] ℝ} {T : Set E} (hT : IsOpen T)
    (hP : ContDiffOn ℝ ∞ P T) {Kz : Set E} (hKzT : Kz ⊆ T) {CP : ℕ → ℝ}
    (hCP : ∀ i, ∀ z ∈ Kz, ‖iteratedFDeriv ℝ i P z‖ ≤ CP i) {η : ℝ} {n : ℕ} {Ψ : E → E}
    {V : Set E} (hV : IsOpen V) (hVK : V ⊆ Kz) (hΨ : ContDiffOn ℝ ∞ Ψ V) (hΨK : MapsTo Ψ V Kz)
    (hjet : ∀ i : ℕ, i ≤ n + 1 → ∀ y ∈ V,
      ‖iteratedFDeriv ℝ i (fun x => pullbackForm (P (Ψ x), fderiv ℝ Ψ x) - P x) y‖ ≤ η) :
    ContDiffOn ℝ ∞ (fun x => pullbackForm (P (Ψ x), fderiv ℝ Ψ x)) V ∧
      ∀ i : ℕ, i ≤ n + 1 → ∀ x ∈ V,
        ‖iteratedFDeriv ℝ i (fun x => pullbackForm (P (Ψ x), fderiv ℝ Ψ x)) x‖ ≤ CP i + η := by
  have hPa : ∀ z ∈ Kz, ContDiffAt ℝ ∞ P z := fun z hz => hP.contDiffAt (hT.mem_nhds (hKzT hz))
  have hdΨ : ContDiffOn ℝ ∞ (fderiv ℝ Ψ) V := hΨ.fderiv_of_isOpen hV (by exact_mod_cast le_top)
  have hPΨ : ContDiffOn ℝ ∞ (fun x => P (Ψ x)) V := fun x hx =>
    ((hPa _ (hΨK hx)).comp x (hΨ.contDiffAt (hV.mem_nhds hx))).contDiffWithinAt
  have hGt : ContDiffOn ℝ ∞ (fun x => pullbackForm (P (Ψ x), fderiv ℝ Ψ x)) V :=
    pullbackForm.contDiff.comp_contDiffOn (hPΨ.prodMk hdΨ)
  have hDiff : ContDiffOn ℝ ∞ (fun x => pullbackForm (P (Ψ x), fderiv ℝ Ψ x) - P x) V :=
    hGt.sub (hP.mono (hVK.trans hKzT))
  refine ⟨hGt, fun i hi x hx => ?_⟩
  have hsplit : (fun x => pullbackForm (P (Ψ x), fderiv ℝ Ψ x)) =
      P + fun x => pullbackForm (P (Ψ x), fderiv ℝ Ψ x) - P x := by
    funext x
    simp
  rw [hsplit, iteratedFDeriv_add_apply ((hPa x (hVK hx)).of_le (by exact_mod_cast le_top))
    ((hDiff.contDiffAt (hV.mem_nhds hx)).of_le (by exact_mod_cast le_top))]
  exact (norm_add_le _ _).trans (add_le_add (hCP i x (hVK hx)) (hjet i hi x hx))

/-- The compact value set of `((G̃, DG̃), (Ψ, DΨ))` (helper of `chart_jet_bound_O52`). -/
theorem chart_value_set_O52 [FiniteDimensional ℝ E] {P : E → E →L[ℝ] E →L[ℝ] ℝ} {T : Set E}
    (hT : IsOpen T) (hP : ContDiffOn ℝ ∞ P T) (hpos : ∀ z ∈ T, ∀ v, v ≠ 0 → 0 < P z v v)
    {Kz : Set E} (hKz : IsCompact Kz) (hKzT : Kz ⊆ T) (n : ℕ) :
    ∃ η > 0, ∃ K : Set (((E →L[ℝ] E →L[ℝ] ℝ) × (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)) ×
        (E × (E →L[ℝ] E))),
      IsCompact K ∧ K ⊆ ({A : E →L[ℝ] E →L[ℝ] ℝ | A.IsInvertible} ×ˢ univ) ×ˢ (T ×ˢ univ) ∧
      ∃ B : ℝ, ∀ (Ψ : E → E) (V : Set E), IsOpen V → V ⊆ Kz → ContDiffOn ℝ ∞ Ψ V →
        MapsTo Ψ V Kz →
        (∀ i : ℕ, i ≤ n + 1 → ∀ y ∈ V,
          ‖iteratedFDeriv ℝ i (fun x => pullbackForm (P (Ψ x), fderiv ℝ Ψ x) - P x) y‖ ≤ η) →
        ContDiffOn ℝ ∞ (fun x => pullbackForm (P (Ψ x), fderiv ℝ Ψ x)) V ∧
        (∀ x ∈ V, ((pullbackForm (P (Ψ x), fderiv ℝ Ψ x),
          fderiv ℝ (fun x => pullbackForm (P (Ψ x), fderiv ℝ Ψ x)) x), (Ψ x, fderiv ℝ Ψ x)) ∈ K) ∧
        (∀ i : ℕ, i ≤ n → ∀ x ∈ V, ‖iteratedFDeriv ℝ i (fun x =>
          (pullbackForm (P (Ψ x), fderiv ℝ Ψ x),
            fderiv ℝ (fun x => pullbackForm (P (Ψ x), fderiv ℝ Ψ x)) x)) x‖ ≤ B) := by
  have hPc : ContinuousOn P T := hP.continuousOn
  obtain ⟨lam, hlam, hcoer⟩ :=
    exists_coercive_O52 hKz (hPc.mono hKzT) (fun z hz => hpos z (hKzT hz))
  have hjetP : ∀ i : ℕ, ∃ Ci : ℝ, ∀ z ∈ Kz, ‖iteratedFDeriv ℝ i P z‖ ≤ Ci := by
    intro i
    have hc : ContinuousOn (iteratedFDeriv ℝ i P) T :=
      (hP.continuousOn_iteratedFDerivWithin (m := i) (by exact_mod_cast le_top)
        hT.uniqueDiffOn).congr (fun z hz => (iteratedFDerivWithin_of_isOpen i hT hz).symm)
    exact hKz.exists_bound_of_continuousOn (hc.mono hKzT)
  choose CP hCP using hjetP
  have hinvK : P '' Kz ⊆ {A : E →L[ℝ] E →L[ℝ] ℝ | A.IsInvertible} := by
    rintro _ ⟨z, hz, rfl⟩
    exact isInvertible_of_pos_O52 (hpos z (hKzT hz))
  obtain ⟨δ, hδ, hδsub⟩ := (hKz.image_of_continuousOn (hPc.mono hKzT)).exists_thickening_subset_open
    ContinuousLinearMap.isOpen_setOfPred_isInvertible hinvK
  obtain ⟨η, hη_def⟩ : ∃ η : ℝ, η = min (δ / 2) 1 := ⟨_, rfl⟩
  have hη : 0 < η := hη_def ▸ lt_min (by linarith) one_pos
  have hηδ : η < δ := hη_def ▸ (min_le_left _ _).trans_lt (by linarith)
  obtain ⟨KA, hKA_def⟩ : ∃ KA : Set (E →L[ℝ] E →L[ℝ] ℝ),
      KA = (fun p : E × (E →L[ℝ] E →L[ℝ] ℝ) => P p.1 + p.2) '' (Kz ×ˢ closedBall 0 η) :=
    ⟨_, rfl⟩
  have hKA : IsCompact KA := hKA_def ▸
    (hKz.prod (isCompact_closedBall 0 η)).image_of_continuousOn
      (((hPc.mono hKzT).comp continuousOn_fst (fun p hp => hp.1)).add continuousOn_snd)
  have hKAinv : KA ⊆ {A : E →L[ℝ] E →L[ℝ] ℝ | A.IsInvertible} := by
    rw [hKA_def]
    rintro _ ⟨⟨z, X⟩, ⟨hz, hX⟩, rfl⟩
    apply hδsub
    rw [mem_thickening_iff]
    refine ⟨P z, ⟨z, hz, rfl⟩, ?_⟩
    rw [dist_eq_norm, add_sub_cancel_left]
    exact (mem_closedBall_zero_iff.1 hX).trans_lt hηδ
  have hKAmem : ∀ z ∈ Kz, ∀ A : E →L[ℝ] E →L[ℝ] ℝ, ‖A - P z‖ ≤ η → A ∈ KA := by
    intro z hz A hA
    rw [hKA_def]
    exact ⟨(z, A - P z), ⟨hz, mem_closedBall_zero_iff.2 hA⟩, add_sub_cancel _ _⟩
  obtain ⟨K, hK_def⟩ : ∃ K : Set (((E →L[ℝ] E →L[ℝ] ℝ) × (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)) ×
      (E × (E →L[ℝ] E))), K = (KA ×ˢ closedBall 0 (CP 1 + η)) ×ˢ
        (Kz ×ˢ closedBall 0 (max 1 ((CP 0 + η) / lam))) := ⟨_, rfl⟩
  refine ⟨η, hη, K, ?_, ?_, ∑ j ∈ Finset.range (n + 2), |CP j| + η, ?_⟩
  · rw [hK_def]
    exact (hKA.prod (isCompact_closedBall _ _)).prod (hKz.prod (isCompact_closedBall _ _))
  · rw [hK_def]
    rintro ⟨⟨A, A'⟩, z, N⟩ ⟨⟨hA, -⟩, hz, -⟩
    exact ⟨⟨hKAinv hA, mem_univ _⟩, hKzT hz, mem_univ _⟩
  intro Ψ V hV hVK hΨ hΨK hjet
  obtain ⟨hGt, hGjet⟩ := pullback_jet_le_O52 hT hP hKzT hCP hV hVK hΨ hΨK hjet
  refine ⟨hGt, fun x hx => ?_, fun i hi x hx => ?_⟩
  · rw [hK_def]
    have h0 := hGjet 0 (Nat.zero_le _) x hx
    rw [norm_iteratedFDeriv_zero] at h0
    have hj0 := hjet 0 (Nat.zero_le _) x hx
    rw [norm_iteratedFDeriv_zero] at hj0
    refine ⟨⟨hKAmem x (hVK hx) _ hj0, ?_⟩, hΨK hx, ?_⟩
    · rw [mem_closedBall_zero_iff, ← norm_iteratedFDeriv_one]
      exact hGjet 1 (by omega) x hx
    · rw [mem_closedBall_zero_iff]
      exact norm_le_of_coercive_O52 hlam (hcoer _ (hΨK hx)) _ h0
  · have hB : ∀ j, j ≤ n + 1 → CP j + η ≤ ∑ j ∈ Finset.range (n + 2), |CP j| + η := by
      intro j hj
      have := Finset.single_le_sum (f := fun j => |CP j|) (fun j _ => abs_nonneg _)
        (Finset.mem_range.2 (Nat.lt_succ_of_le hj))
      have := le_abs_self (CP j)
      linarith
    rw [norm_iteratedFDeriv_pair_fderiv_le_O52 hV hGt hx]
    exact max_le ((hGjet i (by omega) x hx).trans (hB i (by omega)))
      ((hGjet (i + 1) (by omega) x hx).trans (hB (i + 1) (by omega)))

/-- **Bounded `C^{n+2}` of the chart map** (`[FROZEN] CH12-O52 G2`). -/
theorem chart_jet_bound_O52 [FiniteDimensional ℝ E] {P : E → E →L[ℝ] E →L[ℝ] ℝ} {T : Set E}
    (hT : IsOpen T) (hP : ContDiffOn ℝ ∞ P T)
    (hsym : ∀ z ∈ T, ∀ v w, P z v w = P z w v) (hpos : ∀ z ∈ T, ∀ v, v ≠ 0 → 0 < P z v v)
    {Kz : Set E} (hKz : IsCompact Kz) (hKzT : Kz ⊆ T) (n : ℕ) :
    ∃ η > 0, ∃ C : ℝ, ∀ (Ψ : E → E) (V : Set E), IsOpen V → V ⊆ Kz → ContDiffOn ℝ ∞ Ψ V →
      MapsTo Ψ V Kz →
      (∀ i : ℕ, i ≤ n + 1 → ∀ y ∈ V,
        ‖iteratedFDeriv ℝ i (fun x => pullbackForm (P (Ψ x), fderiv ℝ Ψ x) - P x) y‖ ≤ η) →
      ∀ i : ℕ, i ≤ n + 2 → ∀ y ∈ V, ‖iteratedFDeriv ℝ i Ψ y‖ ≤ C := by
  obtain ⟨η, hη, K, hK, hKt, B, hval⟩ := chart_value_set_O52 hT hP hpos hKz hKzT n
  have ht : IsOpen (({A : E →L[ℝ] E →L[ℝ] ℝ | A.IsInvertible} ×ˢ
      (univ : Set (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ))) ×ˢ (T ×ˢ (univ : Set (E →L[ℝ] E)))) :=
    (ContinuousLinearMap.isOpen_setOfPred_isInvertible.prod isOpen_univ).prod
      (hT.prod isOpen_univ)
  have hΦ : ContDiffOn ℝ ∞ (chartODE_O52 P) (({A : E →L[ℝ] E →L[ℝ] ℝ | A.IsInvertible} ×ˢ
      (univ : Set (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ))) ×ˢ (T ×ˢ (univ : Set (E →L[ℝ] E)))) :=
    contDiffOn_chartODE_O52 hT hP
  obtain ⟨C, hC⟩ := bootstrap_jet_bound_O52 (E := E) (Φ := chartODE_O52 P) ht hΦ hK hKt B n
  refine ⟨η, hη, C, ?_⟩
  intro Ψ V hV hVK hΨ hΨK hjet
  obtain ⟨hGt, hmem, hγB⟩ := hval Ψ V hV hVK hΨ hΨK hjet
  have hdΨ : ContDiffOn ℝ ∞ (fderiv ℝ Ψ) V := hΨ.fderiv_of_isOpen hV (by exact_mod_cast le_top)
  have hODE : ∀ x ∈ V, fderiv ℝ (fun x => (Ψ x, fderiv ℝ Ψ x)) x =
      chartODE_O52 P ((pullbackForm (P (Ψ x), fderiv ℝ Ψ x),
        fderiv ℝ (fun x => pullbackForm (P (Ψ x), fderiv ℝ Ψ x)) x), (Ψ x, fderiv ℝ Ψ x)) := by
    intro x hx
    have hz : Ψ x ∈ T := hKzT (hΨK hx)
    have hinv : (pullbackForm (P (Ψ x), fderiv ℝ Ψ x)).IsInvertible := by
      have h := hKt (hmem x hx)
      simp only [Set.mem_prod, Set.mem_ofPred_eq] at h
      exact h.1.1
    have hPd : DifferentiableAt ℝ P (Ψ x) :=
      (hP.contDiffAt (hT.mem_nhds hz)).differentiableAt (by simp)
    exact fderiv_chartPair_eq_O52 hPd (hΨ.contDiffAt (hV.mem_nhds hx)) (hsym _ hz) hinv
  have hw := hC (fun x => (pullbackForm (P (Ψ x), fderiv ℝ Ψ x),
      fderiv ℝ (fun x => pullbackForm (P (Ψ x), fderiv ℝ Ψ x)) x))
    (fun x => (Ψ x, fderiv ℝ Ψ x)) V hV (hGt.prodMk (hGt.fderiv_of_isOpen hV (by exact_mod_cast le_top)))
    (hΨ.prodMk hdΨ) hmem hODE hγB
  intro i hi y hy
  rcases Nat.lt_or_ge i (n + 2) with h | h
  · have := hw i (by omega) y hy
    rw [norm_iteratedFDeriv_pair_fderiv_le_O52 hV hΨ hy] at this
    exact (le_max_left _ _).trans this
  · obtain rfl : i = n + 2 := by omega
    have := hw (n + 1) le_rfl y hy
    rw [norm_iteratedFDeriv_pair_fderiv_le_O52 hV hΨ hy] at this
    exact (le_max_right _ _).trans this

end GC.LongTime.Ch12
