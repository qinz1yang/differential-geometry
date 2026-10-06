/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Regularity.BranchedDeckSlit
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Regularity.ProfileBranchDeckExclusion
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Regularity.BranchedDeckMorreyNodal
import DifferentialGeometry.Analysis.Elliptic.Planar.RootNodalArc
import Mathlib.RingTheory.RootsOfUnity.Complex

set_option autoImplicit false
noncomputable section

open Set Metric Filter Manifold Bundle TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Geometry.Metric.BarrierProfile DifferentialGeometry.Tensor.Coordinates
open scoped ContDiff Manifold Topology ENNReal NNReal

namespace DifferentialGeometry.Geometry

private theorem morrey_deck_nodal_family_impossible
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {γ : freeLoop M}
    {q : C(closedDisk, M)} (hq : IsMorreyDisk g γ q)
    (hd3 : Module.finrank ℝ E = 3)
    {Lq : ℝ≥0} (hqLip : ∀ z v, riemannianEDistOf g (q z) (q v) ≤
      (Lq : ℝ≥0∞) * edist z v)
    (p : M) (P : E →L[ℝ] ℂ) (height : E →L[ℝ] ℝ)
    (N : E) (lift : ℂ → E)
    (hsplit : ∀ v : E, v = lift (P v) + height v • N)
    (e : OpenPartialHomeomorph ℂ ℂ) {a : ℂ}
    (hae : a ∈ e.source) (hea : e a = 0)
    (he : ContDiffOn ℝ 1 (e : ℂ → ℂ) e.source)
    (hei : ContDiffOn ℝ 1 (e.symm : ℂ → ℂ) e.target)
    (heSource : e.source ⊆ Metric.ball (0 : ℂ) 1)
    (hechart : ∀ z ∈ e.source, diskExtension q z ∈ (chartAt E p).source)
    (heForward : ContDiffOn ℝ ∞ (e : ℂ → ℂ) (e.source \ {a}))
    (heInverse : ContDiffOn ℝ ∞ (e.symm : ℂ → ℂ) (e.target \ {0}))
    (n : ℕ) (ζ : ℂ) (hζ : ‖ζ‖ = 1) (hζne : ζ ≠ 1) (hζpower : ζ ^ n = 1) :
    let U := diskExtension q
    let X : ℂ → E := fun z => extChartAt 𝓘(ℝ, E) p (U z)
    let F : ℂ → ℂ := fun z => P (X z)
    (∀ z ∈ e.source, z ≠ a → (fderiv ℝ F z).IsInvertible) →
    (∀ w ∈ e.target, F (e.symm w) = F a + w ^ n / (n : ℂ)) →
    let H : ℂ → ℝ := fun w => height (X (e.symm w) - X a)
    let d : ℂ → ℝ := fun w => H w - H (ζ * w)
    ∀ (eIso : OpenPartialHomeomorph ℂ ℂ),
      (0 : ℂ) ∈ eIso.source → eIso 0 = 0 →
      ContDiffOn ℝ 1 (eIso : ℂ → ℂ) eIso.source →
      ContDiffOn ℝ 1 (eIso.symm : ℂ → ℂ) eIso.target →
      ContinuousOn H eIso.source → ContDiffOn ℝ ∞ d (eIso.source \ {0}) →
      let v : ℂ → ℝ := d ∘ eIso.symm
      ∀ ρ : ℝ, 0 < ρ → ball (0 : ℂ) ρ ⊆ eIso.target →
        (∀ z ∈ ball (0 : ℂ) ρ, z ≠ 0 → fderiv ℝ v z ≠ 0) →
        ∀ (S : Set ℝ) (Γ : S → ℝ → ℂ),
          (∀ s, Γ s 0 = 0 ∧ ContDiffOn ℝ 1 (Γ s) (Ioo (-ρ) ρ) ∧
            HasDerivAt (Γ s) (Complex.exp (((s : ℝ) : ℂ) * Complex.I)) 0 ∧
            Set.InjOn (Γ s) (Ico 0 ρ) ∧
            ∀ r ∈ Ico 0 ρ, ‖Γ s r - 0‖ = r ∧ v (Γ s r) = 0) →
          (∀ z ∈ ball (0 : ℂ) ρ,
            v z = 0 ↔ z = 0 ∨ ∃ s : S, ∃ r ∈ Ioo 0 ρ, z = Γ s r) → False := by
  intro U X F hreg hpower H d eIso hIso0 hIsozero hIsoC1 hIsoInvC1 hH hdsmooth v
    ρ hρ hρtarget hvregular S Γ hΓ hcover
  have h0target : (0 : ℂ) ∈ e.target := hea ▸ e.map_source hae
  obtain ⟨s, T, _hT, _hTρ, hR, hRtarget, _hαzero, hαvalue, hαLip, hαsmooth, hαregular⟩ :=
    Analysis.exists_original_radius_arc_of_deck_nodal_family H hζ
      eIso hIso0 hIsozero hIsoC1 hIsoInvC1 hH hdsmooth
      ρ hρ hρtarget hvregular S Γ hΓ hcover e.target e.open_target h0target
  let β : ℝ → ℂ := eIso.symm ∘ Γ s
  let R := ‖β T‖
  let τ := Function.invFunOn (fun t => ‖β t‖) (Icc 0 T)
  let α := β ∘ τ
  change 0 < R at hR
  change closedBall (0 : ℂ) R ⊆ e.target at hRtarget
  change ∀ r ∈ Icc 0 R, ‖α r‖ = r ∧ d (α r) = 0 at hαvalue
  change ∃ L : ℝ≥0, LipschitzOnWith L α (Icc 0 R) at hαLip
  change ContDiffOn ℝ ∞ α (Ioo 0 R) at hαsmooth
  change ∀ r ∈ Ioc 0 R, fderiv ℝ d (α r) ≠ 0 at hαregular
  have hdRaw : d = fun w =>
      height (X (e.symm w)) - height (X (e.symm (ζ * w))) := by
    funext w
    dsimp only [d, H]
    simp only [map_sub]
    ring
  apply hq.not_regular_branched_height_zero_arc hd3 hqLip p P height N lift hsplit
    e hea he hei heSource hechart heForward heInverse n ζ hζ hζne hζpower
    hreg hpower α R hR hRtarget (fun r hr => (hαvalue r hr).1) hαLip hαsmooth
  · intro r hr
    have hzero := (hαvalue r hr).2
    rw [hdRaw] at hzero
    exact sub_eq_zero.mp hzero
  · have hr : R / 16 ∈ Ioc (0 : ℝ) R := by constructor <;> linarith
    simpa only [hdRaw] using hαregular (R / 16) hr

private theorem morrey_interior_rank_of_finite_restriction
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {γ : freeLoop M}
    {q : C(closedDisk, M)} (hq : IsMorreyDisk g γ q)
    (hγ : IsSmoothEmbeddedLoop (E := E) γ) (hd3 : Module.finrank ℝ E = 3)
    (S : Set M) (hfinite : (q ⁻¹' S).Finite)
    (hno : coincidentGermPairs ((Sᶜ).restrictPreimage (q : closedDisk → M)) = ∅)
    {Lq : ℝ≥0} (hqLip : ∀ z v, riemannianEDistOf g (q z) (q v) ≤
      (Lq : ℝ≥0∞) * edist z v)
    {a : ℂ} (ha : a ∈ ball (0 : ℂ) 1) :
    Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension q) a) := by
  classical
  by_contra hbranch
  obtain ⟨m, B, eRoot, N, L, hm, _hB, _hBne, _hfactor, hroot⟩ :=
    hq.exists_branched_deck_nodal_chart_of_not_injective hγ hd3 ha hbranch
  obtain ⟨hae, hea, heSource, _heD, he, hei, heForward, heInverse, hechart,
    hreg, hpower, _hNN, _hN, hsplit, _hL, hH, _hHsmooth,
    ε, _hε, _hε1, hεtarget, hdeck⟩ := hroot
  let ζ := Complex.exp (2 * Real.pi * Complex.I / ((m + 1 : ℕ) : ℂ))
  have hζprimitive : IsPrimitiveRoot ζ (m + 1) :=
    Complex.isPrimitiveRoot_exp (m + 1) (by omega)
  have hζpower : ζ ^ (m + 1) = 1 := hζprimitive.pow_eq_one
  have hζne : ζ ≠ 1 := hζprimitive.ne_one (by omega)
  have hζnorm : ‖ζ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hζpower (by omega)
  have hnotzero := hq.not_branched_height_zero_germ_of_finite_restriction
    S hfinite hno m (B a) eRoot hae hea heSource hechart
    hreg hpower N (fun w => L w) hsplit ζ hζpower hζne
  obtain ⟨_hW2, hWsmooth, eIso, hIso0, hIsoSource, hIsozero, hIso, hIsoInv,
    _hIsoDet, _hv0, _hDv0, _hvC1, _hsame, hcases⟩ := hdeck ζ hζpower
  rcases hcases with hzero | hnodal
  · exact hnotzero hzero
  · obtain ⟨ρ, hρ, hρtarget, hvregular, A, _hAfinite, Γ, hΓ, hcover⟩ := hnodal
    apply morrey_deck_nodal_family_impossible hq hd3 hqLip (diskExtension q a)
      (chartLeadingPlaneProjection g (diskExtension q a) (diskExtension q a) (B a))
      (chartGramBilin g (diskExtension q a) (diskExtension q a) N)
      N (fun w => L w) hsplit eRoot hae hea he hei heSource hechart heForward heInverse
      (m + 1) ζ hζnorm hζne hζpower hreg hpower
      eIso hIso0 hIsozero hIso hIsoInv
      (hH.continuousOn.mono (hIsoSource.trans hεtarget))
      (hWsmooth.mono (fun z hz => ⟨hIsoSource hz.1, hz.2⟩))
      ρ hρ hρtarget hvregular A Γ
    · simpa only [sub_zero, Function.comp_apply] using hΓ
    · exact hcover

/-- The same confined Morrey disk in the completed profile metric has no
interior branch points. Its closed-disk smooth extension, finite exceptional
fibers and boundary singleton structure determine the original disk's regular
value restriction. A nontrivial deck root is excluded in both analytic cases:
coincident regular germs for the zero germ, and the actual paired slit for a
nonzero nodal germ. No new minimizer or rank hypothesis is introduced. -/
theorem interior_immersion_of_completed_profile
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    (hd3 : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (a : ℝ) (ha : 0 < a)
    (ρ : M → ℝ) (hρ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ ρ)
    (hbase : ∀ x : M, 0 < ρ x → ρ x < a →
      ∀ v : TangentSpace 𝓘(ℝ, E) x, 0 ≤ hessFun g ρ x v v)
    (hcontact : ∀ x : M, ρ x = 0 → ∀ v : TangentSpace 𝓘(ℝ, E) x,
      v ≠ 0 → 0 < hessFun g ρ x v v) :
    let U : Opens M := ⟨{x | ρ x < a}, isOpen_lt hρ.continuous continuous_const⟩
    let δ : M → ℝ := fun x => cutoff a (ρ x)
    let hδ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ δ :=
      (cutoff_smooth a).contMDiff.comp hρ
    let hU : ∀ x : M, x ∈ U ↔ 0 < δ x :=
      fun x => (cutoff_pos_iff ha (ρ x)).symm
    let G := canonicalPositiveDomainMetric g hδ U hU
    ∀ (γU : freeLoop U) (q : C(closedDisk, U)),
      IsSmoothEmbeddedLoop (E := E) γU → IsMorreyDisk G γU q →
      (∀ θ : loopCircle, ρ (γU θ : M) = 0) →
      ∀ (Q : ℂ → U), SmoothDiskExtension (E := E) q Q →
        ∀ z ∈ ball (0 : ℂ) 1,
          Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Q z) := by
  intro U δ hδ hU G γU q hγ hq hγzero Q hQ z hz
  let : LocallyCompactSpace U := ChartedSpace.locallyCompactSpace E U
  have : T3Space U := inferInstance
  let B : Set closedDisk := {w | ¬ Function.Injective
    (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Q w)}
  have hprofile := DiskRegularity.ConsumerAudit.profile_regular_value_restriction_no_coincident_germs
    hd3 g a ha ρ hρ hbase hcontact γU q hγ hq hγzero Q hQ
  obtain ⟨Lq, hqLip⟩ := hQ.lipschitz G
  have hinner := morrey_interior_rank_of_finite_restriction hq hγ hd3
    (q '' B) hprofile.1 hprofile.2.2 hqLip hz
  have heq : (show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Q z) =
      (show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension q) z) := by
    ext v
    exact congrArg (fun L => L v)
      ((hQ.eventuallyEq_diskExtension hz).mfderiv_eq
        (I := 𝓘(ℝ, ℂ)) (I' := 𝓘(ℝ, E)))
  change Function.Injective
    (show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Q z)
  exact (congrArg (fun L : ℂ →L[ℝ] E => Function.Injective (L : ℂ → E)) heq).mpr
    hinner

end DifferentialGeometry.Geometry
