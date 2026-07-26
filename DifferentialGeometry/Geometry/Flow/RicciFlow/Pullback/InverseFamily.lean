import DifferentialGeometry.Geometry.Flow.RicciFlow.Pullback.ChainRule
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTimeFlow.ConjugatingFlowProperties
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.Regularity.PushforwardSmooth

/-!
# Algebraic pullback identities for inverse diffeomorphisms

This file records the composition and inverse-family identities for the
Ricci-flow pullback metric.  They are the algebraic part of running the
Hamilton--DeTurck pullback construction in the reverse direction.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Pullback

open Bundle Filter
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

/-- Pullback first by `Φ` and then by `Φ.symm` recovers the original metric. -/
theorem Diffeomorph.pbMetric_symm
    (g : SmoothRiemannianMetric I M) (Φ : M ≃ₘ⟮I, I⟯ M) :
    Diffeomorph.pullbackMetric
        (Diffeomorph.pullbackMetric g Φ) Φ.symm = g := by
  rw [Diffeomorph.pullbackMetric_trans, Φ.symm_trans_self,
    Diffeomorph.pullbackMetric_refl]

/-- Pullback first by `Φ.symm` and then by `Φ` recovers the original metric. -/
theorem Diffeomorph.pbMetric_self
    (g : SmoothRiemannianMetric I M) (Φ : M ≃ₘ⟮I, I⟯ M) :
    Diffeomorph.pullbackMetric
        (Diffeomorph.pullbackMetric g Φ.symm) Φ = g := by
  rw [Diffeomorph.pullbackMetric_trans, Φ.self_trans_symm,
    Diffeomorph.pullbackMetric_refl]

/-- If the time-preserving total map of a diffeomorphism family is itself a
local diffeomorphism, then evaluation of the inverse family is jointly smooth.

The total map is automatically bijective because every time slice is a
diffeomorphism.  Packaging it by `diffeomorphOfBijective` makes its smooth
inverse available, and that inverse is exactly
`(t, x) ↦ (t, (Ψ_fam t).symm x)`. -/
theorem joint_symm_smooth
    (Ψ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M))
    (hlocal : IsLocalDiffeomorph (𝓘(ℝ, ℝ).prod I)
      (𝓘(ℝ, ℝ).prod I) ∞
      (fun q : ℝ × M => (q.1, (Ψ_fam q.1 : M → M) q.2))) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞
      (fun q : ℝ × M => ((Ψ_fam q.1).symm : M → M) q.2) := by
  let F : ℝ × M → ℝ × M := fun q =>
    (q.1, (Ψ_fam q.1 : M → M) q.2)
  have hF_inj : Function.Injective F := by
    rintro ⟨s, x⟩ ⟨t, y⟩ hxy
    have hst : s = t := congrArg Prod.fst hxy
    subst t
    have hxy' : (Ψ_fam s : M → M) x = (Ψ_fam s : M → M) y :=
      congrArg Prod.snd hxy
    have : x = y := (Ψ_fam s).injective hxy'
    subst y
    rfl
  have hF_surj : Function.Surjective F := by
    rintro ⟨t, y⟩
    refine ⟨(t, ((Ψ_fam t).symm : M → M) y), ?_⟩
    simp only [F, Diffeomorph.apply_symm_apply]
  let e : (ℝ × M) ≃ₘ⟮𝓘(ℝ, ℝ).prod I, 𝓘(ℝ, ℝ).prod I⟯ (ℝ × M) :=
    hlocal.diffeomorphOfBijective ⟨hF_inj, hF_surj⟩
  have he_coe : (e : ℝ × M → ℝ × M) = F := rfl
  have he_symm : (e.symm : ℝ × M → ℝ × M) =
      (fun q : ℝ × M => (q.1, ((Ψ_fam q.1).symm : M → M) q.2)) := by
    funext q
    apply hF_inj
    have hleft : F (e.symm q) = q := by
      rw [← he_coe]
      exact e.apply_symm_apply q
    have hright : F
        (q.1, ((Ψ_fam q.1).symm : M → M) q.2) = q := by
      simp only [F, Diffeomorph.apply_symm_apply]
    exact hleft.trans hright.symm
  have hpair : ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) ∞
      (fun q : ℝ × M =>
        (q.1, ((Ψ_fam q.1).symm : M → M) q.2)) := by
    rw [← he_symm]
    exact e.symm.contMDiff
  exact contMDiff_snd.comp hpair

/-- Joint smoothness of the inverse evaluation map on an open time slab only
requires the time-preserving total map to be a local diffeomorphism on that
slab.

Unlike `joint_symm_smooth`, this windowed form does not ask for any regularity
of the family outside the interval where the gauge PDE is solved.  Slice-wise
injectivity identifies the set-theoretic inverse family with each chosen local
inverse of the total map. -/
theorem joint_symm_smoothOn
    (Ψ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M)) (T : ℝ)
    (hlocal : IsLocalDiffeomorphOn (𝓘(ℝ, ℝ).prod I)
      (𝓘(ℝ, ℝ).prod I) ∞
      (fun q : ℝ × M => (q.1, (Ψ_fam q.1 : M → M) q.2))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞
      (fun q : ℝ × M => ((Ψ_fam q.1).symm : M → M) q.2)
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ) := by
  let F : ℝ × M → ℝ × M := fun q =>
    (q.1, (Ψ_fam q.1 : M → M) q.2)
  let G : ℝ × M → ℝ × M := fun q =>
    (q.1, ((Ψ_fam q.1).symm : M → M) q.2)
  have hF_inj : Function.Injective F := by
    rintro ⟨s, x⟩ ⟨t, y⟩ hxy
    have hst : s = t := congrArg Prod.fst hxy
    subst t
    have hxy' : (Ψ_fam s : M → M) x = (Ψ_fam s : M → M) y :=
      congrArg Prod.snd hxy
    have : x = y := (Ψ_fam s).injective hxy'
    subst y
    rfl
  have hFG : ∀ q : ℝ × M, F (G q) = q := by
    rintro ⟨t, x⟩
    simp only [F, G, Diffeomorph.apply_symm_apply]
  intro q hq
  have hG_mem : G q ∈ Set.Ioo (0 : ℝ) T ×ˢ (Set.univ : Set M) := by
    exact ⟨hq.1, Set.mem_univ _⟩
  let hloc : IsLocalDiffeomorphAt (𝓘(ℝ, ℝ).prod I)
      (𝓘(ℝ, ℝ).prod I) ∞ F (G q) := hlocal ⟨G q, hG_mem⟩
  have hq_source : q ∈ hloc.localInverse.source := by
    simpa only [hFG q] using hloc.localInverse_mem_source
  have hG_event : G =ᶠ[𝓝 q] hloc.localInverse := by
    filter_upwards [hloc.localInverse_open_source.mem_nhds hq_source] with r hr
    apply hF_inj
    rw [hFG r, hloc.localInverse_right_inv hr]
  have hlocal_smooth : ContMDiffAt (𝓘(ℝ, ℝ).prod I)
      (𝓘(ℝ, ℝ).prod I) ∞ hloc.localInverse q := by
    simpa only [hFG q] using hloc.localInverse_contMDiffAt
  have hG_at : ContMDiffAt (𝓘(ℝ, ℝ).prod I)
      (𝓘(ℝ, ℝ).prod I) ∞ G q :=
    hlocal_smooth.congr_of_eventuallyEq hG_event
  have hsnd : ContMDiffAt (𝓘(ℝ, ℝ).prod I) I ∞ (Prod.snd ∘ G) q :=
    contMDiffAt_snd.comp q hG_at
  simpa only [Function.comp_apply, G] using hsnd.contMDiffWithinAt

/-- The inverse of a diffeomorphism family satisfying the negative gauge
equation satisfies the positive pushed-forward gauge equation.

This is the differential bridge from the harmonic-map heat-flow convention
`∂ₜ Ψ = -W ∘ Ψ` to the inverse family used by the reverse DeTurck pullback.
Joint smoothness of both evaluation families supplies the chain rule; it is
not an existence hypothesis for the harmonic-map heat flow itself. -/
theorem symm_gauge_vel
    (Ψ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M))
    (W : ℝ → Cₘ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (T : ℝ)
    (hΨode : ∀ y : M, ∀ t ∈ Set.Ioo (0 : ℝ) T,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I
        (fun s : ℝ => (Ψ_fam s : M → M) y) (Set.Ici (0 : ℝ)) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          (-(W t ((Ψ_fam t : M → M) y)))))
    (hjoint : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞
      (fun q : ℝ × M => (Ψ_fam q.1 : M → M) q.2)
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ))
    (hsymm_joint : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞
      (fun q : ℝ × M => ((Ψ_fam q.1).symm : M → M) q.2)
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ))
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) (x : M) :
    HasMFDerivWithinAt 𝓘(ℝ, ℝ) I
      (fun s : ℝ => ((Ψ_fam s).symm : M → M) x)
      (Set.Ici (0 : ℝ)) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (Diffeomorph.pushforward (Ψ_fam t).symm (W t)
          (((Ψ_fam t).symm : M → M) x))) := by
  let y : M := ((Ψ_fam t).symm : M → M) x
  have hΨy : (Ψ_fam t : M → M) y = x := by
    simp only [y, Diffeomorph.apply_symm_apply]
  have hopen : IsOpen (Set.Ioo (0 : ℝ) T ×ˢ (Set.univ : Set M)) :=
    isOpen_Ioo.prod isOpen_univ
  have hsymm_at : ContMDiffAt 𝓘(ℝ, ℝ) I ∞
      (fun s : ℝ => ((Ψ_fam s).symm : M → M) x) t := by
    have htotal := hsymm_joint.contMDiffAt
      (hopen.mem_nhds ⟨ht, Set.mem_univ x⟩)
    exact htotal.comp t (contMDiffAt_id.prodMk contMDiffAt_const)
  have hsymm_diff : MDifferentiableAt 𝓘(ℝ, ℝ) I
      (fun s : ℝ => ((Ψ_fam s).symm : M → M) x) t :=
    hsymm_at.mdifferentiableAt (by simp)
  let vΦ : TangentSpace I y :=
    mfderiv 𝓘(ℝ, ℝ) I
      (fun s : ℝ => ((Ψ_fam s).symm : M → M) x) t (1 : ℝ)
  let P : ℝ × M → M := fun q => (Ψ_fam q.1 : M → M) q.2
  let C : ℝ → ℝ × M := fun s =>
    (s, ((Ψ_fam s).symm : M → M) x)
  have hP_at : ContMDiffAt (𝓘(ℝ, ℝ).prod I) I ∞ P (t, y) := by
    exact hjoint.contMDiffAt
      (hopen.mem_nhds ⟨ht, Set.mem_univ y⟩)
  have hP_diff : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) I P (t, y) :=
    hP_at.mdifferentiableAt (by simp)
  have hC_diff : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod I) C t := by
    simpa only [C] using mdifferentiableAt_id.prodMk hsymm_diff
  have hC_val : mfderiv 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod I) C t (1 : ℝ) =
      ((1 : ℝ), vΦ) := by
    rw [show C = (fun s : ℝ =>
      (s, ((Ψ_fam s).symm : M → M) x)) from rfl]
    rw [mfderiv_prodMk mdifferentiableAt_id hsymm_diff]
    simp only [ContinuousLinearMap.prod_apply, mfderiv_id,
      ContinuousLinearMap.id_apply, vΦ]
  have hPC : P ∘ C = (fun _ : ℝ => x) := by
    funext s
    exact (Ψ_fam s).apply_symm_apply x
  have htotal_zero :
      mfderiv (𝓘(ℝ, ℝ).prod I) I P (t, y) ((1 : ℝ), vΦ) = 0 := by
    have hchain := mfderiv_comp t hP_diff hC_diff
    have happ := congrArg (fun A => A (1 : ℝ)) hchain
    rw [hPC, mfderiv_const, ContinuousLinearMap.zero_apply,
      ContinuousLinearMap.comp_apply, hC_val] at happ
    exact happ.symm
  have htime_has :=
    (hΨode y t ht).hasMFDerivAt (Ici_mem_nhds ht.1)
  have htime :
      mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ => P (s, y)) t (1 : ℝ) =
        -(W t x) := by
    rw [htime_has.mfderiv]
    simp only [ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.one_apply, one_smul, P, hΨy]
  have hsum :
      -(W t x) + mfderiv I I (Ψ_fam t : M → M) y vΦ = 0 := by
    have hsplit := mfderiv_prod_eq_add_apply hP_diff
      (v := ((1 : ℝ), vΦ))
    rw [hsplit, htime] at htotal_zero
    exact htotal_zero
  have hspace :
      mfderiv I I (Ψ_fam t : M → M) y vΦ = W t x := by
    apply sub_eq_zero.mp
    simpa only [sub_eq_add_neg, add_comm] using hsum
  have hinv := Diffeomorph.mfderiv_symm_self (Ψ_fam t) y vΦ
  rw [hΨy] at hinv
  have hvΦ : vΦ = mfderiv I I ((Ψ_fam t).symm : M → M) x (W t x) := by
    calc
      vΦ = mfderiv I I ((Ψ_fam t).symm : M → M) x
          (mfderiv I I (Ψ_fam t : M → M) y vΦ) := hinv.symm
      _ = mfderiv I I ((Ψ_fam t).symm : M → M) x (W t x) := by
        rw [hspace]
  have hvPush : vΦ = Diffeomorph.pushforward (Ψ_fam t).symm (W t)
      (((Ψ_fam t).symm : M → M) x) :=
    hvΦ.trans (Diffeomorph.pushforward_image (Ψ_fam t).symm (W t) x).symm
  have hderiv := hsymm_diff.hasMFDerivAt
  apply (hderiv.congr_mfderiv ?_).hasMFDerivWithinAt
  ext a
  calc
    mfderiv 𝓘(ℝ, ℝ) I
          (fun s : ℝ => ((Ψ_fam s).symm : M → M) x) t a =
        mfderiv 𝓘(ℝ, ℝ) I
          (fun s : ℝ => ((Ψ_fam s).symm : M → M) x) t (a • (1 : ℝ)) := by
            rw [smul_eq_mul, mul_one]
    _ = a • vΦ := by
      rw [map_smul]
      rfl
    _ = a • Diffeomorph.pushforward (Ψ_fam t).symm (W t)
        (((Ψ_fam t).symm : M → M) x) := by rw [hvPush]
    _ = ((1 : ℝ →L[ℝ] ℝ).smulRight
        (Diffeomorph.pushforward (Ψ_fam t).symm (W t)
          (((Ψ_fam t).symm : M → M) x))) a := by
      simp only [ContinuousLinearMap.smulRight_apply,
        ContinuousLinearMap.one_apply]

section Gauge

variable [CompactSpace M] [I.Boundaryless]

open DifferentialGeometry
open DifferentialGeometry.PDE.DeTurck

/-- At the identity gauge, the positive gauge velocity is exactly the DeTurck
vector field of the unpulled metric.  This is the initial compatibility
identity for a harmonic-map heat-flow gauge starting from `id`. -/
@[simp] theorem gauge_vel_refl
    (g g_bg : SmoothRiemannianMetric I M) (x : M) :
    Diffeomorph.pushforward (Diffeomorph.refl I M ∞)
        (deTurckVF (I := I)
          (Diffeomorph.pullbackMetric g (Diffeomorph.refl I M ∞)) g_bg) x =
      deTurckVF (I := I) g g_bg x := by
  rw [Diffeomorph.pullbackMetric_refl, Diffeomorph.pushforward_refl]

/-- Pulling a Ricci flow back by a jointly smooth diffeomorphism family whose
velocity is the pushforward of the DeTurck field produces the Ricci--DeTurck
PDE.  This is the reverse gauge identity; it does not assert existence of the
required diffeomorphism family. -/
theorem ricci_pullback_DT
    (g_RF : ℝ → SmoothRiemannianMetric I M)
    (g_bg : SmoothRiemannianMetric I M)
    (T : ℝ) (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M))
    (hRF_deriv : ∀ s ∈ Set.Ico (0 : ℝ) T, ∀ y : M,
      ∀ a b : TangentSpace I y,
      HasDerivWithinAt (fun u : ℝ => (g_RF u).inner y a b)
        ((-2 : ℝ) * ricciTensor (I := I) (g_RF s) y a b) (Set.Ici 0) s)
    (hΦode : ∀ x : M, ∀ t ∈ Set.Ioo (0 : ℝ) T,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => (Φ_fam s : M → M) x)
        (Set.Ici (0 : ℝ)) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          (Diffeomorph.pushforward (Φ_fam t)
            (deTurckVF (I := I)
              (Diffeomorph.pullbackMetric (g_RF t) (Φ_fam t)) g_bg)
            ((Φ_fam t : M → M) x))))
    (hjoint : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞
      (fun q : ℝ × M => (Φ_fam q.1 : M → M) q.2)
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ))
    (hgram_RF : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × M =>
          Integral.Measure.chartGramMatrix (I := I) (g_RF p.1) x₀ p.2 i j)
        (Set.Ioo (0 : ℝ) T ×ˢ
          (trivializationAt E (TangentSpace I) x₀).baseSet)) :
    ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivWithinAt
        (fun s : ℝ =>
          (Diffeomorph.pullbackMetric (g_RF s) (Φ_fam s)).inner x v w)
        (deTurckRicciRHS (I := I) g_bg
          (Diffeomorph.pullbackMetric (g_RF t) (Φ_fam t)) x v w)
        (Set.Ici 0) t := by
  let W : ℝ → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ := fun s =>
    deTurckVF (I := I) (Diffeomorph.pullbackMetric (g_RF s) (Φ_fam s)) g_bg
  let hPush : ∀ s : ℝ,
      ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun z : M => TotalSpace.mk' E (E := TangentSpace I) z
          (Diffeomorph.pushforward (Φ_fam s) (W s) z)) := fun s =>
    ODE.flowFamily_pushforward_contMDiff (I := I) Φ_fam s (W s).contMDiff
  let Y : ℝ → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ := fun s =>
    ⟨Diffeomorph.pushforward (Φ_fam s) (W s), hPush s⟩
  have hYode : ∀ z : M, ∀ s ∈ Set.Ioo (0 : ℝ) T,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u : ℝ => (Φ_fam u : M → M) z)
        (Set.Ici (0 : ℝ)) s
        ((1 : ℝ →L[ℝ] ℝ).smulRight (Y s ((Φ_fam s : M → M) z))) := by
    intro z s hs
    simpa [Y, W] using hΦode z s hs
  intro t ht x v w
  have ht_Ico : t ∈ Set.Ico (0 : ℝ) T := ⟨le_of_lt ht.1, ht.2⟩
  have h_metric := hRF_deriv t ht_Ico ((Φ_fam t : M → M) x)
    (mfderiv I I (Φ_fam t : M → M) x v)
    (mfderiv I I (Φ_fam t : M → M) x w)
  have h_push := flow_slot_pos (I := I) (g_RF t) Y T Φ_fam hYode hjoint
    t ht x v w
  obtain ⟨Q', hQ'⟩ := evalForm_joint (I := I) g_RF T Φ_fam hjoint hgram_RF
    t ht x v w
  have h_total := deTurck_evalForm_chain_hasDerivWithinAt (I := I) g_RF Φ_fam
    t (le_of_lt ht.1) x v w _ _ h_metric h_push hQ'
  have h_ric := ricci_tensor_pullback_natural_under_diffeomorphism
    (I := I) (g_RF t) (Φ_fam t) x v w
  have h_lie :
      lieDerivMetric (I := I)
          (Diffeomorph.pullbackMetric (g_RF t) (Φ_fam t)) (W t) x v w =
        lieDerivMetric (I := I) (g_RF t) (Y t) ((Φ_fam t : M → M) x)
          (mfderiv I I (Φ_fam t : M → M) x v)
          (mfderiv I I (Φ_fam t : M → M) x w) := by
    simpa [Y] using
      (lie_derivative_metric_pullback_natural_under_diffeomorphism_pointwise
        (I := I) (g_RF t) (Φ_fam t) (W t) (W t).contMDiff (hPush t) x v w)
  have h_value :
      ((-2 : ℝ) * ricciTensor (I := I) (g_RF t) ((Φ_fam t : M → M) x)
          (mfderiv I I (Φ_fam t : M → M) x v)
          (mfderiv I I (Φ_fam t : M → M) x w)
        + lieDerivMetric (I := I) (g_RF t) (Y t) ((Φ_fam t : M → M) x)
          (mfderiv I I (Φ_fam t : M → M) x v)
          (mfderiv I I (Φ_fam t : M → M) x w)) =
      deTurckRicciRHS (I := I) g_bg
        (Diffeomorph.pullbackMetric (g_RF t) (Φ_fam t)) x v w := by
    rw [deTurckRicciRHS_apply, ← h_ric, ← h_lie]
    rfl
  have h_total' : HasDerivWithinAt
      (fun s : ℝ => (g_RF s).inner ((Φ_fam s : M → M) x)
        (mfderiv I I (Φ_fam s : M → M) x v)
        (mfderiv I I (Φ_fam s : M → M) x w))
      (deTurckRicciRHS (I := I) g_bg
        (Diffeomorph.pullbackMetric (g_RF t) (Φ_fam t)) x v w)
      (Set.Ici 0) t := by
    rw [← h_value]
    exact h_total
  have hcurve :
      (fun s : ℝ =>
        (Diffeomorph.pullbackMetric (g_RF s) (Φ_fam s)).inner x v w) =
      (fun s : ℝ => (g_RF s).inner ((Φ_fam s : M → M) x)
        (mfderiv I I (Φ_fam s : M → M) x v)
        (mfderiv I I (Φ_fam s : M → M) x w)) := by
    funext s
    exact pullback_metric_evaluation_formula (I := I) (g_RF s) (Φ_fam s) x v w
  rwa [hcurve]

end Gauge

end DifferentialGeometry.PDE.RicciFlow.Pullback
