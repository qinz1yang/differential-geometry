import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.RightFamily_O75
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThinBarrierTransferA_O27
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CompNaturality_S71
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CkErrBridge_S57
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CompAbstract_S60
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThreeMetric_S76
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.PersistTime_S50
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CompImmersion_S60

set_option autoImplicit false

/-!
# CH12-O75 G2a: C^p transfer of `ckErr_S45` to the right of a time (both directions)

* `ckErr_metric_change_O75`: on a fixed target `N`, if `cA • gA` and `cB • gB` are `δ`-close in
  `metricDerivNorm` (orders `≤ p`, reference `cA • gA`) and `f` is `δ`-good for `(gA, cA)` on `U`
  (injective on `U`), then `f` is `ε`-good for `(gB, cB)`: naturality of `metricDerivNorm` under the
  partial diffeomorphism `f|_U` (`metricDerivNorm_localPullback_S71`) + the two-step reference change
  `ckComp_abstract_S60`.
* `exists_small_derivNorm_O75`: the S50 right time continuity at all orders `≤ p`.
* `ckTransfer_O75` (`[FROZEN] CH12-O75 G2`): flow version on the right smooth family of
  `exists_right_family_O75`; the reverse direction via `three_metric_closeness_S76`.
-/

noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.LongTime Set Filter TopologicalSpace
open Manifold DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff ENNReal Topology

namespace GC.LongTime.Ch12

universe u

section Core

variable (H₁ : FiniteVolumeHyperbolicModel.{u}) {N : Type u} [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N] [IsManifold (𝓡 3) ∞ N] [T2Space N]
  [SigmaCompactSpace N]

omit [T2Space N] [SigmaCompactSpace N] in
/-- An injective immersion on an open `U` is a partial diffeomorphism with source `U`. -/
theorem exists_partialDiffeo_of_injOn_O75 (f : H₁.Carrier → N) (U : Opens H₁.Carrier)
    (hF : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U)
    (hinj : ∀ y ∈ U, Function.Injective (mfderiv (𝓡 3) (𝓡 3) f y))
    (hinjU : Set.InjOn f U) (z : H₁.Carrier) (hz : z ∈ U) :
    ∃ Φ : PartialDiffeomorph (𝓡 3) (𝓡 3) H₁.Carrier N (∞ : WithTop ℕ∞),
      Φ.source = (U : Set H₁.Carrier) ∧ ∀ x ∈ (U : Set H₁.Carrier), Φ x = f x := by
  have hf : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (fun x : U => f x) :=
    isLocalDiffeomorph_of_injective_mfderiv _ (contMDiff_restrict_C4 f U hF)
      (immersion_restrict_inj_S57 H₁ f U hF hinj) rfl
  have hinj' : Function.Injective (fun x : U => f x) := fun a b hab =>
    Subtype.ext (hinjU a.2 b.2 hab)
  let p : U := ⟨z, hz⟩
  let V := hf.image
  let e : Diffeomorph (𝓡 3) (𝓡 3) U V ∞ :=
    DifferentialGeometry.Topology.diffeomorphRangeOfInjective hf hinj'
  let iU := DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph (𝓡 3) U ⟨p⟩
  let iV := DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph (𝓡 3) V ⟨e p⟩
  let Φ := (iU.symm.trans e.toPartialDiffeomorph).trans iV
  have hsrc : Φ.source = (U : Set H₁.Carrier) := by
    ext x
    change ((x ∈ iU.target ∧ iU.symm x ∈ (univ : Set U)) ∧
      e (iU.symm x) ∈ (univ : Set V)) ↔ x ∈ U
    simp only [mem_univ, and_true, iU,
      DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_target]
    rfl
  refine ⟨Φ, hsrc, fun x hx => ?_⟩
  change (e (iU.symm x) : N) = _
  rw [show iU.symm x = (⟨x, hx⟩ : U) from
    DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_symm_apply (𝓡 3) U ⟨p⟩ hx]
  rfl

omit [SigmaCompactSpace N] in
/-- The restricted pull-back metric is the local pull-back under a partial diffeomorphism that
agrees with `f` on `U`. -/
theorem pullbackRestrict_eq_local_O75 (g : SmoothRiemannianMetric (𝓡 3) N)
    (f : H₁.Carrier → N) (U : Opens H₁.Carrier) (hF : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U)
    (hinj : ∀ y ∈ U, Function.Injective (mfderiv (𝓡 3) (𝓡 3) f y))
    (Φ : PartialDiffeomorph (𝓡 3) (𝓡 3) H₁.Carrier N (∞ : WithTop ℕ∞))
    (hU : (U : Set H₁.Carrier) ⊆ Φ.source) (hΦ : ∀ x ∈ (U : Set H₁.Carrier), Φ x = f x) :
    pullbackRestrict_S57 H₁ g f U hF hinj =
      localPullbackMetric_S71 Φ U hU (partialImage_S71 Φ U hU) subset_rfl
        (g.restrictOpen (partialImage_S71 Φ U hU)) := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [localPullbackMetric_inner_S71]
  have hev : (Φ : H₁.Carrier → N) =ᶠ[𝓝 (x : H₁.Carrier)] f := by
    filter_upwards [U.isOpen.mem_nhds x.2] with y hy using hΦ y hy
  have hx : Φ x = f x := hΦ x x.2
  simp only [pullbackRestrict_S57, SmoothRiemannianMetric.pullbackOfImmersion_inner,
    mfderiv_comp_val_C4 f U hF x, hev.mfderiv_eq]
  have key : ∀ (y₁ y₂ : N), y₁ = y₂ → ∀ a b : EuclideanSpace ℝ (Fin 3),
      g.inner y₁ a b = g.inner y₂ a b := by
    intro y₁ y₂ h a b; subst h; rfl
  exact key _ _ hx.symm _ _

/-- **Core**: change of the target metric for a fixed injective map. -/
theorem ckErr_metric_change_O75 (gA gB : SmoothRiemannianMetric (𝓡 3) N) {cA cB : ℝ}
    (hcA : 0 < cA) (hcB : 0 < cB) (f : H₁.Carrier → N) (U : Opens H₁.Carrier)
    (hF : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U) (hinjU : Set.InjOn f U) {δ ε : ℝ} {p : ℕ}
    (hδ1 : δ < 1)
    (habs : ∀ A gHat gBase : SmoothRiemannianMetric (𝓡 3) U,
      (∀ x : U, ∀ q : ℕ, q ≤ p → metricDerivNorm (I := 𝓡 3) q gHat gBase gBase x ≤ δ) →
      (∀ x : U, ∀ q : ℕ, q ≤ p → metricDerivNorm (I := 𝓡 3) q A gHat gHat x ≤ δ) →
      ∀ x : U, ∀ q : ℕ, q ≤ p → metricDerivNorm (I := 𝓡 3) q A gBase gBase x ≤ ε)
    (hN : ∀ y : N, ∀ j : ℕ, j ≤ p → metricDerivNorm (I := 𝓡 3) j (scaleMetric cB hcB gB)
      (scaleMetric cA hcA gA) (scaleMetric cA hcA gA) y ≤ δ)
    (hA : ∀ j : ℕ, j ≤ p → ∀ x ∈ U, ckErr_S45 H₁ gA cA f j x ≤ δ) :
    ∀ j : ℕ, j ≤ p → ∀ x ∈ U, ckErr_S45 H₁ gB cB f j x ≤ ε := by
  intro j hj x hx
  have hinj : ∀ y ∈ U, Function.Injective (mfderiv (𝓡 3) (𝓡 3) f y) := fun y hy =>
    (ckErr0_immersion_S60 H₁ gA cA f y ((hA 0 (Nat.zero_le _) y hy).trans_lt hδ1)).2
  obtain ⟨Φ, hsrc, hΦ⟩ := exists_partialDiffeo_of_injOn_O75 H₁ f U hF hinj hinjU x hx
  have hU : (U : Set H₁.Carrier) ⊆ Φ.source := hsrc.symm.subset
  let W := partialImage_S71 Φ U hU
  let _ : SigmaCompactSpace W := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen (𝓡 3) W.isOpen)
  have eA := pullbackRestrict_eq_local_O75 H₁ (scaleMetric cA hcA gA) f U hF hinj Φ hU hΦ
  have eB := pullbackRestrict_eq_local_O75 H₁ (scaleMetric cB hcB gB) f U hF hinj Φ hU hΦ
  have h1 : ∀ y : U, ∀ r : ℕ, r ≤ p →
      metricDerivNorm (I := 𝓡 3) r (pullbackRestrict_S57 H₁ (scaleMetric cA hcA gA) f U hF hinj)
        (H₁.metric.restrictOpen U) (H₁.metric.restrictOpen U) y ≤ δ := by
    intro y r hr
    rw [← ckErr_S45_eq_metricDerivNorm_S57 H₁ gA cA hcA f U hF hinj r y]
    exact hA r hr y y.2
  have h2 : ∀ y : U, ∀ r : ℕ, r ≤ p →
      metricDerivNorm (I := 𝓡 3) r (pullbackRestrict_S57 H₁ (scaleMetric cB hcB gB) f U hF hinj)
        (pullbackRestrict_S57 H₁ (scaleMetric cA hcA gA) f U hF hinj)
        (pullbackRestrict_S57 H₁ (scaleMetric cA hcA gA) f U hF hinj) y ≤ δ := by
    intro y r hr
    rw [eA, eB, metricDerivNorm_localPullback_S71 Φ U hU W subset_rfl _ _ _ r y,
      metricDerivNorm_restrictOpen]
    exact hN _ r hr
  have key := habs _ _ _ h1 h2 ⟨x, hx⟩ j hj
  rw [ckErr_S45_eq_metricDerivNorm_S57 H₁ gB cB hcB f U hF hinj j ⟨x, hx⟩]
  exact key

end Core

section Flow

/-- S50 right time continuity (`exists_small_derivNorm_S50`) at all orders `≤ p`, closed at `a`. -/
theorem exists_small_derivNorm_O75 (Q : OrientedThreeStage.{u}) (G : ℝ → Q.Metric) {a ε0 : ℝ}
    (ha : 0 < a) (hε0 : 0 < ε0) (hG : Q.MetricSmoothUpTo G (Icc a (a + ε0))) (p : ℕ) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ ε1 : ℝ, 0 < ε1 ∧ ε1 ≤ ε0 ∧ ∀ t : ℝ, a ≤ t → t ≤ a + ε1 → ∀ (x : Q.Carrier) (j : ℕ),
      j ≤ p → metricDerivNorm j (normFamily_S50 Q G t) (normFamily_S50 Q G a)
        (normFamily_S50 Q G a) x ≤ ε := by
  have hĜ := metricSmoothUpTo_normFamily_S50 Q G ha hG
  have hcomp : IsCompact (univ : Set Q.Carrier) := isCompact_univ
  have hj (j : ℕ) : ∀ᶠ t in 𝓝[Icc a (a + ε0)] a, ∀ x ∈ (univ : Set Q.Carrier),
      metricDerivNorm j (normFamily_S50 Q G t) (normFamily_S50 Q G a) (normFamily_S50 Q G a) x
        < ε := by
    have he (x : Q.Carrier) :
        {q : ℝ × Q.Carrier | metricDerivNorm j (normFamily_S50 Q G q.1) (normFamily_S50 Q G a)
          (normFamily_S50 Q G a) q.2 < ε} ∈ 𝓝[Icc a (a + ε0)] a ×ˢ 𝓝 x := by
      have h := (hĜ.metricDerivNorm_continuousOn Q (normFamily_S50 Q G a) (normFamily_S50 Q G a) j
        (a, x) ⟨⟨le_rfl, by linarith⟩, mem_univ x⟩).eventually_lt_const
        (by simpa only [metricDerivNorm_self] using hε)
      simp only [nhdsWithin_prod_eq, nhdsWithin_univ] at h
      exact h
    have hprod : ∀ᶠ q in 𝓝[Icc a (a + ε0)] a ×ˢ 𝓝ˢ (univ : Set Q.Carrier),
        metricDerivNorm j (normFamily_S50 Q G q.1) (normFamily_S50 Q G a)
          (normFamily_S50 Q G a) q.2 < ε :=
      hcomp.mem_prod_nhdsSet_of_forall (fun x _ => he x)
    exact hprod.curry.mono (fun _ ht => ht.self_of_nhdsSet)
  have hall : ∀ᶠ t in 𝓝[Icc a (a + ε0)] a, ∀ j ∈ Finset.range (p + 1),
      ∀ x ∈ (univ : Set Q.Carrier),
      metricDerivNorm j (normFamily_S50 Q G t) (normFamily_S50 Q G a) (normFamily_S50 Q G a) x
        < ε :=
    (Filter.eventually_all_finset _).mpr (fun j _ => hj j)
  rw [nhdsWithin_Icc_eq_nhdsGE (by linarith)] at hall
  obtain ⟨u, hu, hsub⟩ := (mem_nhdsGE_iff_exists_Ico_subset).mp hall
  refine ⟨min ((u - a) / 2) ε0, lt_min (by linarith [mem_Ioi.mp hu]) hε0, min_le_right _ _, ?_⟩
  intro t hat hta x j hj
  have h1 : t ∈ Ico a u := ⟨hat, by
    have := min_le_left ((u - a) / 2) ε0
    linarith [mem_Ioi.mp hu]⟩
  exact (hsub h1 j (Finset.mem_range.mpr (by omega)) x (mem_univ x)).le

theorem heq_cast_comp_O75 {X : Type u} {A B : OrientedThreeStage.{u}} (h : A = B)
    (q : X → A.Carrier) :
    HEq q (fun x => cast (congrArg OrientedThreeStage.Carrier h) (q x)) := by
  subst h; rfl

theorem ckErr_heq_O75 (H₁ : FiniteVolumeHyperbolicModel.{u}) {A B : OrientedThreeStage.{u}}
    (h : A = B) {gA : A.Metric} {gB : B.Metric} (hg : HEq gA gB)
    {qA : H₁.Carrier → A.Carrier} {qB : H₁.Carrier → B.Carrier} (hq : HEq qA qB) (c : ℝ)
    (j : ℕ) (x : H₁.Carrier) :
    ckErr_S45 H₁ gA c qA j x = ckErr_S45 H₁ gB c qB j x := by
  subst h; cases hg; cases hq; rfl

theorem contMDiffOn_heq_O75 {H₁ : FiniteVolumeHyperbolicModel.{u}} {A B : OrientedThreeStage.{u}}
    (h : A = B) {qA : H₁.Carrier → A.Carrier} {qB : H₁.Carrier → B.Carrier} (hq : HEq qA qB)
    (U : Set H₁.Carrier) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ qA U → ContMDiffOn (𝓡 3) (𝓡 3) ∞ qB U := by
  subst h; cases hq; exact id

theorem injOn_heq_O75 {H₁ : FiniteVolumeHyperbolicModel.{u}} {A B : OrientedThreeStage.{u}}
    (h : A = B) {qA : H₁.Carrier → A.Carrier} {qB : H₁.Carrier → B.Carrier} (hq : HEq qA qB)
    (U : Set H₁.Carrier) : Set.InjOn qA U → Set.InjOn qB U := by
  subst h; cases hq; exact id

variable {P : OrientedThreeStage.{u}} {g : P.Metric}

/-- `[FROZEN] CH12-O75 G2`: C^p transfer of `ckErr_S45` between `t` and `s ∈ [t, t + τ)`. -/
theorem ckTransfer_O75 (O : ObservationTower P g) :
    ∀ (p : ℕ) (ε : ℝ), 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → ∃ τ : ℝ, 0 < τ ∧
      ∀ s : ℝ, t ≤ s → s < t + τ →
      ∀ (H₁ : FiniteVolumeHyperbolicModel.{u}) (U : TopologicalSpace.Opens H₁.Carrier)
        (q : H₁.Carrier → (postStage O t).Carrier) (q' : H₁.Carrier → (postStage O s).Carrier),
        HEq q q' → ContMDiffOn (𝓡 3) (𝓡 3) ∞ q U → Set.InjOn q U →
        ((∀ j : ℕ, j ≤ p → ∀ x ∈ U, ckErr_S45 H₁ (postMetric O t) t⁻¹ q j x ≤ δ) →
          ∀ j : ℕ, j ≤ p → ∀ x ∈ U, ckErr_S45 H₁ (postMetric O s) s⁻¹ q' j x ≤ ε) ∧
        ((∀ j : ℕ, j ≤ p → ∀ x ∈ U, ckErr_S45 H₁ (postMetric O s) s⁻¹ q' j x ≤ δ) →
          ∀ j : ℕ, j ≤ p → ∀ x ∈ U, ckErr_S45 H₁ (postMetric O t) t⁻¹ q j x ≤ ε) := by
  intro p ε hε
  obtain ⟨δc, hδc, habs⟩ := ckComp_abstract_S60 (E := EuclideanSpace ℝ (Fin 3)) (I := 𝓡 3) p hε
  set δ := min δc (1 / 2) with hδdef
  have hδ : 0 < δ := lt_min hδc (by norm_num)
  have hδ1 : δ < 1 := (min_le_right _ _).trans_lt (by norm_num)
  refine ⟨δ, hδ, fun t ht => ?_⟩
  obtain ⟨Q, G, ε0, hε0, hG, hfam⟩ := exists_right_family_O75 O t ht
  obtain ⟨δ3, hδ3, h3⟩ := three_metric_closeness_S76 (M := Q.Carrier) p δ hδ
  obtain ⟨ε1, hε1, hε1le, hsmall⟩ := exists_small_derivNorm_O75 Q G ht hε0 hG p
    (ε := min δ (δ3 / 2)) (lt_min hδ (by linarith))
  refine ⟨ε1, hε1, fun s hts hst H₁ U q q' hqq' hqs hqi => ?_⟩
  have hs0 : 0 < s := ht.trans_le hts
  obtain ⟨eT, hGT⟩ := hfam t le_rfl (by linarith)
  obtain ⟨eS, hGS⟩ := hfam s hts (by linarith)
  set gT := scaleMetric t⁻¹ (inv_pos.mpr ht) (G t) with hgT
  set gS := scaleMetric s⁻¹ (inv_pos.mpr hs0) (G s) with hgS
  have hfwd : ∀ y : Q.Carrier, ∀ j : ℕ, j ≤ p →
      metricDerivNorm (I := 𝓡 3) j gS gT gT y ≤ min δ (δ3 / 2) := by
    intro y j hj
    have := hsmall s hts (by linarith) y j hj
    rwa [normFamily_S50_of_pos Q G hs0, normFamily_S50_of_pos Q G ht] at this
  have hbwd : ∀ y : Q.Carrier, ∀ j : ℕ, j ≤ p → metricDerivNorm (I := 𝓡 3) j gT gS gS y ≤ δ := by
    intro y j hj
    exact (h3 gS gS gT (fun z i _ => by rw [metricDerivNorm_self_S60]; exact hδ3)
      (fun z i hi => (hfwd z i hi).trans_lt ((min_le_right _ _).trans_lt (by linarith)))
      y j hj).le
  let qQ : H₁.Carrier → Q.Carrier := fun x => cast (congrArg OrientedThreeStage.Carrier eT) (q x)
  have hq1 : HEq q qQ := heq_cast_comp_O75 eT q
  have hq2 : HEq q' qQ := hqq'.symm.trans hq1
  have hcT : ∀ j x, ckErr_S45 H₁ (postMetric O t) t⁻¹ q j x = ckErr_S45 H₁ (G t) t⁻¹ qQ j x :=
    fun j x => ckErr_heq_O75 H₁ eT hGT hq1 _ j x
  have hcS : ∀ j x, ckErr_S45 H₁ (postMetric O s) s⁻¹ q' j x = ckErr_S45 H₁ (G s) s⁻¹ qQ j x :=
    fun j x => ckErr_heq_O75 H₁ eS hGS hq2 _ j x
  have hQs : ContMDiffOn (𝓡 3) (𝓡 3) ∞ qQ U := contMDiffOn_heq_O75 eT hq1 _ hqs
  have hQi : Set.InjOn qQ U := injOn_heq_O75 eT hq1 _ hqi
  have habsU : ∀ A gHat gBase : SmoothRiemannianMetric (𝓡 3) U,
      (∀ x : U, ∀ q : ℕ, q ≤ p → metricDerivNorm (I := 𝓡 3) q gHat gBase gBase x ≤ δ) →
      (∀ x : U, ∀ q : ℕ, q ≤ p → metricDerivNorm (I := 𝓡 3) q A gHat gHat x ≤ δ) →
      ∀ x : U, ∀ q : ℕ, q ≤ p → metricDerivNorm (I := 𝓡 3) q A gBase gBase x ≤ ε :=
    fun A gHat gBase h1 h2 x q hq => habs isOpen_univ A gHat gBase
      (fun z _ r hr => (h1 z r hr).trans (min_le_left _ _))
      (fun z _ r hr => (h2 z r hr).trans (min_le_left _ _)) x (mem_univ x) q hq
  constructor
  · intro hA j hj x hx
    rw [hcS]
    exact ckErr_metric_change_O75 H₁ (G t) (G s) (inv_pos.mpr ht) (inv_pos.mpr hs0) qQ U hQs hQi
      hδ1 habsU (fun y i hi => (hfwd y i hi).trans (min_le_left _ _))
      (fun i hi z hz => by rw [← hcT]; exact hA i hi z hz) j hj x hx
  · intro hB j hj x hx
    rw [hcT]
    exact ckErr_metric_change_O75 H₁ (G s) (G t) (inv_pos.mpr hs0) (inv_pos.mpr ht) qQ U hQs hQi
      hδ1 habsU hbwd (fun i hi z hz => by rw [← hcS]; exact hB i hi z hz) j hj x hx

end Flow

end GC.LongTime.Ch12
