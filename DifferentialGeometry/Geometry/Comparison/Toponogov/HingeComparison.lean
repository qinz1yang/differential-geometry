/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import DifferentialGeometry.Geometry.Comparison.Toponogov.HingeAlgebra
import DifferentialGeometry.Geometry.Comparison.Toponogov.RiemannianDistance
import DifferentialGeometry.Geometry.Comparison.Toponogov.SquaredDistanceDefectConvexity

set_option autoImplicit false

noncomputable section

open Bundle Filter Function Manifold Set Topology
open scoped ENNReal Manifold ContDiff Topology

namespace DifferentialGeometry.Toponogov

open DifferentialGeometry
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.HopfRinow
open DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [T2Space (TangentBundle I M)]
  [SigmaCompactSpace M] [BoundarylessManifold I M]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
    [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
    [BoundarylessManifold I M] in
private theorem isGeodesicAt_mdifferentiableAt
    (g : SmoothRiemannianMetric I M) {gamma : ℝ → M} {t : ℝ}
    (h : IsGeodesicAt (I := I) g gamma t) :
    MDifferentiableAt 𝓘(ℝ, ℝ) I gamma t := by
  obtain ⟨alpha, f, hproj, _halpha, hf⟩ := h
  have hfd : MDifferentiableAt 𝓘(ℝ, ℝ) I.tangent f t :=
    hf.hasMFDerivAt.mdifferentiableAt
  have hpd : MDifferentiableAt I.tangent I
      (Bundle.TotalSpace.proj : TangentBundle I M → M) (f t) :=
    (Bundle.contMDiffAt_proj (E := (TangentSpace I : M → Type _))
      (n := 1)).mdifferentiableAt (by norm_num)
  have hcomp := hpd.comp t hfd
  have heq : (fun s : ℝ ↦ (f s).proj) = gamma := funext hproj
  rw [← heq]
  simpa only [Function.comp_def] using hcomp

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
    [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
    [BoundarylessManifold I M] in
private theorem UnitSpeedGeodesicOn.mdifferentiableAt
    (g : SmoothRiemannianMetric I M) {gamma : ℝ → M} {J : Set ℝ}
    (hgamma : UnitSpeedGeodesicOn (I := I) g gamma J)
    {t : ℝ} (ht : t ∈ J) : MDifferentiableAt 𝓘(ℝ, ℝ) I gamma t := by
  let shifted : ℝ → M := fun s ↦ gamma (t + s)
  have hshifted : MDifferentiableAt 𝓘(ℝ, ℝ) I shifted 0 :=
    isGeodesicAt_mdifferentiableAt (I := I) g (hgamma.geodesicAt_shift t ht)
  let phi : ℝ → ℝ := (fun _ : ℝ ↦ -t) + id
  have haffDeriv : HasDerivAt phi 1 t := by
    simpa only [phi, zero_add] using
      (hasDerivAt_const (x := t) (-t)).add (hasDerivAt_id t)
  have haff : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
      phi t :=
    haffDeriv.hasFDerivAt.hasMFDerivAt.mdifferentiableAt
  have hshifted' : MDifferentiableAt 𝓘(ℝ, ℝ) I shifted (phi t) := by
    simpa only [phi, Pi.add_apply, id_eq, neg_add_cancel] using hshifted
  have hcomp := hshifted'.comp t haff
  have heq : shifted ∘ phi = gamma := by
    funext s
    simp only [shifted, phi, Function.comp_apply, Pi.add_apply, id_eq]
    congr 1
    ring
  rw [heq] at hcomp
  exact hcomp

omit [NeZero (Module.finrank ℝ E)] [T2Space M]
    [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
    [BoundarylessManifold I M] in
private theorem UnitSpeedGeodesicOn.isGeodesicOn
    (g : SmoothRiemannianMetric I M) {gamma : ℝ → M} {J : Set ℝ}
    (hgamma : UnitSpeedGeodesicOn (I := I) g gamma J) :
    IsGeodesicOn (I := I) g gamma J := by
  intro t ht
  have hshift :=
    (hgamma.geodesicAt_shift t ht).hasGeodesicEquationAt g
  have hshift' : HasGeodesicEquationAt (I := I) g
      (fun s : ℝ ↦ gamma (t + s)) (1 * t + -t) := by
    simpa only [one_mul, add_neg_cancel] using hshift
  have hback := hasGeodesicEquationAt_comp_affine (I := I)
    (c := (1 : ℝ)) (d := -t) (t := t) hshift'
  have heq : (fun s : ℝ ↦ gamma (t + (1 * s + -t))) =ᶠ[nhds t] gamma :=
    Filter.Eventually.of_forall (fun s ↦ by
      ring_nf)
  exact HasGeodesicEquationAt.congr_of_eventuallyEq_at
    heq.symm.self_of_nhds heq.symm hback

private structure SmoothArmRepresentative
    (g : SmoothRiemannianMetric I M) (sigma : ℝ → M) (a : ℝ) where
  curve : ℝ → M
  smooth : ContMDiff 𝓘(ℝ, ℝ) I ∞ curve
  agrees : Set.EqOn curve sigma (Icc 0 a)
  geodesicOn : IsGeodesicOn (I := I) g curve (Icc 0 a)

omit [T2Space (TangentBundle I M)] [BoundarylessManifold I M] in
private theorem exists_smoothArmRepresentative
    (g : SmoothRiemannianMetric I M) {sigma : ℝ → M} {a : ℝ}
    (ha : 0 < a)
    (hsigma : UnitSpeedGeodesicOn (I := I) g sigma (Icc 0 a)) :
    Nonempty (SmoothArmRepresentative (I := I) g sigma a) := by
  have hsmooth : ContMDiffOn 𝓘(ℝ, ℝ) I 1 sigma (Ioo 0 a) := by
    have h := hsigma.smoothOn_interior.of_le
      (by norm_num : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
    simpa [interior_Icc, ha.ne'] using h
  have hgeo : IsGeodesicOn (I := I) g sigma (Ioo 0 a) :=
    (hsigma.isGeodesicOn g).mono Ioo_subset_Icc_self
  let sigmaRev : ℝ → M := fun t ↦ sigma (-t)
  have hrevSmooth : ContMDiffOn 𝓘(ℝ, ℝ) I 1 sigmaRev (Ioo (-a) 0) := by
    exact hsmooth.comp contDiff_neg.contMDiff.contMDiffOn (by
      intro t ht
      exact ⟨by linarith [ht.2], by linarith [ht.1]⟩)
  have hrevUnit : ∀ t ∈ Ioo (-a) 0,
      g.inner (sigmaRev t) (mfderiv 𝓘(ℝ, ℝ) I sigmaRev t 1)
        (mfderiv 𝓘(ℝ, ℝ) I sigmaRev t 1) = 1 := by
    intro t ht
    apply unitSpeed_comp_neg g hsmooth
      (fun s hs ↦ hsigma.unitSpeed s ⟨hs.1.le, hs.2.le⟩)
    exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hrevGeo : IsGeodesicOn (I := I) g sigmaRev (Ioo (-a) 0) := by
    have h := isGeodesicOn_comp_neg (I := I) hgeo
    exact h.mono (by
      intro t ht
      exact ⟨by linarith [ht.2], by linarith [ht.1]⟩)
  have hrevContClosed : ContinuousOn sigmaRev (Icc (-a) 0) := by
    exact hsigma.continuousOn.comp continuous_neg.continuousOn (by
      intro t ht
      constructor <;> linarith [ht.1, ht.2])
  have hrevLim : Tendsto sigmaRev (nhdsWithin 0 (Iio 0)) (nhds (sigmaRev 0)) := by
    have hc := hrevContClosed 0 ⟨by linarith, le_rfl⟩
    apply hc.mono_left
    intro s hs
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter] at hs ⊢
    obtain ⟨u, hu, hus⟩ := hs
    refine ⟨u ∩ Ioi (-a), inter_mem hu (Ioi_mem_nhds (by linarith)), ?_⟩
    intro t ht
    exact hus ⟨ht.1.1, ⟨ht.1.2.le, ht.2.le⟩⟩
  have hleftEndpoint : HasEndpointContinuation (I := I) g sigmaRev 0 :=
    hasEndpointContinuation_of_unitSpeed g (sigmaRev 0) (by linarith)
      hrevSmooth hrevUnit hrevGeo hrevLim
  obtain ⟨sigmaRevExt, bLeft, hbLeft, hrevExtGeo, hrevExtCont,
      hrevExtAgree⟩ :=
    isGeodesicOn_Ioo_extend (I := I) g (by linarith : -a < (0 : ℝ))
      hrevGeo hrevSmooth.continuousOn hleftEndpoint
  let sigmaLeft : ℝ → M := fun t ↦ sigmaRevExt (-t)
  have hleftGeo : IsGeodesicOn (I := I) g sigmaLeft (Ioo (-bLeft) a) := by
    have h := isGeodesicOn_comp_neg (I := I) hrevExtGeo
    exact h.mono (by
      intro t ht
      exact ⟨by linarith [ht.2], by linarith [ht.1]⟩)
  have hleftCont : ContinuousOn sigmaLeft (Ioo (-bLeft) a) := by
    exact hrevExtCont.comp continuous_neg.continuousOn (by
      intro t ht
      exact ⟨by linarith [ht.2], by linarith [ht.1]⟩)
  have hleftAgree : Set.EqOn sigmaLeft sigma (Ioo 0 a) := by
    intro t ht
    have hagree := hrevExtAgree (-t) (by linarith [ht.1])
    simpa only [sigmaLeft, sigmaRev, neg_neg] using hagree
  have hrightLim : Tendsto sigma (nhdsWithin a (Iio a)) (nhds (sigma a)) := by
    have hc := hsigma.continuousOn a ⟨ha.le, le_rfl⟩
    apply hc.mono_left
    intro s hs
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter] at hs ⊢
    obtain ⟨u, hu, hus⟩ := hs
    refine ⟨u ∩ Ioi 0, inter_mem hu (Ioi_mem_nhds ha), ?_⟩
    intro t ht
    exact hus ⟨ht.1.1, ⟨ht.1.2.le, ht.2.le⟩⟩
  have hrightEndpoint : HasEndpointContinuation (I := I) g sigma a :=
    hasEndpointContinuation_of_unitSpeed g (sigma a) ha hsmooth
      (fun t ht ↦ hsigma.unitSpeed t ⟨ht.1.le, ht.2.le⟩)
      hgeo hrightLim
  have hleftEventually :
      sigmaLeft =ᶠ[nhdsWithin a (Iio a)] sigma := by
    filter_upwards [Ioo_mem_nhdsLT ha] with t ht
    exact hleftAgree ht
  have hrightForLeft : HasEndpointContinuation (I := I) g sigmaLeft a :=
    hasEndpointContinuation_congr_left g hrightEndpoint hleftEventually
  obtain ⟨sigmaFinal, bRight, hbRight, hfinalGeo, hfinalCont,
      hfinalAgreeLeft⟩ :=
    isGeodesicOn_Ioo_extend (I := I) g (by linarith : -bLeft < a)
      hleftGeo hleftCont hrightForLeft
  have hfinalAgreeOpen : Set.EqOn sigmaFinal sigma (Ioo 0 a) := by
    intro t ht
    exact (hfinalAgreeLeft t ht.2).trans (hleftAgree ht)
  have hIccSubset : Icc (0 : ℝ) a ⊆ Ioo (-bLeft) bRight := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2, hbLeft, hbRight]
  have hfinalAgreeClosed : Set.EqOn sigmaFinal sigma (Icc 0 a) := by
    apply hfinalAgreeOpen.of_subset_closure
      (hfinalCont.mono hIccSubset) hsigma.continuousOn
      (fun _ ht ↦ ⟨ht.1.le, ht.2.le⟩)
    calc
      Icc (0 : ℝ) a = closure (Ioo 0 a) := (closure_Ioo ha.ne).symm
      _ ⊆ closure (Ioo 0 a) := subset_rfl
  have hfinalSmooth : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ sigmaFinal
      (Ioo (-bLeft) bRight) :=
    isGeodesicOn_contMDiffOn_infty (I := I) g isOpen_Ioo hfinalGeo hfinalCont
  let margin : ℝ := min bLeft (bRight - a)
  have hmargin : 0 < margin := lt_min hbLeft (sub_pos.mpr hbRight)
  let A : ℝ := -margin / 2
  let D : ℝ := a + margin / 2
  let epsilon : ℝ := margin / 4
  have hAD : A < D := by
    dsimp only [A, D]
    linarith [ha, hmargin]
  have hepsilon : 0 < epsilon := by
    dsimp only [epsilon]
    linarith [hmargin]
  obtain ⟨rho, hrhoSmooth, hrhoId, _hrhoDeriv, hrhoRange⟩ :=
    DifferentialGeometry.exists_smooth_time_clamp A D epsilon hAD hepsilon
  have hrhoRange' : ∀ t : ℝ, rho t ∈ Ioo (-bLeft) bRight := by
    intro t
    have ht := hrhoRange t
    dsimp only [A, D, epsilon, margin] at ht
    constructor
    · linarith [ht.1, hmargin, min_le_left bLeft (bRight - a)]
    · linarith [ht.2, hmargin, min_le_right bLeft (bRight - a)]
  let gamma : ℝ → M := sigmaFinal ∘ rho
  have hgammaSmooth : ContMDiff 𝓘(ℝ, ℝ) I ∞ gamma :=
    hfinalSmooth.comp_contMDiff hrhoSmooth.contMDiff hrhoRange'
  have hgammaAgree : Set.EqOn gamma sigma (Icc 0 a) := by
    intro t ht
    have htAD : t ∈ Icc A D := by
      dsimp only [A, D]
      constructor <;> linarith [ht.1, ht.2, hmargin]
    change sigmaFinal (rho t) = sigma t
    rw [hrhoId t htAD]
    exact hfinalAgreeClosed ht
  have hgammaGeo : IsGeodesicOn (I := I) g gamma (Icc 0 a) := by
    intro t ht
    have htAD : t ∈ Ioo A D := by
      dsimp only [A, D]
      constructor <;> linarith [ht.1, ht.2, hmargin]
    have heq : gamma =ᶠ[nhds t] sigmaFinal := by
      filter_upwards [isOpen_Ioo.mem_nhds htAD] with s hs
      change sigmaFinal (rho s) = sigmaFinal s
      rw [hrhoId s ⟨hs.1.le, hs.2.le⟩]
    exact HasGeodesicEquationAt.congr_of_eventuallyEq_at
      heq.self_of_nhds heq (hfinalGeo t (hIccSubset ht))
  exact ⟨⟨gamma, hgammaSmooth, hgammaAgree, hgammaGeo⟩⟩

omit [FiniteDimensional ℝ E] [CompleteSpace E]
    [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
    [IsManifold I ∞ M] [T2Space M] [T2Space (TangentBundle I M)]
    [SigmaCompactSpace M] [BoundarylessManifold I M] in
private theorem mfderiv_eq_of_eqOn_Icc
    {f gamma : ℝ → M} {a t : ℝ} (ha : 0 < a)
    (heq : Set.EqOn f gamma (Icc 0 a))
    (hf : MDifferentiableAt 𝓘(ℝ, ℝ) I f t)
    (hgamma : MDifferentiableAt 𝓘(ℝ, ℝ) I gamma t)
    (ht : t ∈ Icc (0 : ℝ) a) :
    mfderiv 𝓘(ℝ, ℝ) I f t = mfderiv 𝓘(ℝ, ℝ) I gamma t := by
  have hu := (uniqueDiffOn_Icc ha t ht).uniqueMDiffWithinAt
  rw [← mfderivWithin_eq_mfderiv hu hf,
    ← mfderivWithin_eq_mfderiv hu hgamma]
  exact mfderivWithin_congr_of_mem heq ht

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
    [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
    [BoundarylessManifold I M] in
private theorem SmoothArmRepresentative.unitSpeed
    (g : SmoothRiemannianMetric I M) {sigma : ℝ → M} {a t : ℝ}
    (r : SmoothArmRepresentative (I := I) g sigma a) (ha : 0 < a)
    (hsigma : UnitSpeedGeodesicOn (I := I) g sigma (Icc 0 a))
    (ht : t ∈ Icc (0 : ℝ) a) :
    g.inner (r.curve t) (mfderiv 𝓘(ℝ, ℝ) I r.curve t 1)
      (mfderiv 𝓘(ℝ, ℝ) I r.curve t 1) = 1 := by
  have hderiv := mfderiv_eq_of_eqOn_Icc (I := I) ha r.agrees
    (r.smooth.mdifferentiableAt (by norm_num))
    (hsigma.mdifferentiableAt g ht) ht
  rw [r.agrees ht, hderiv]
  exact hsigma.unitSpeed t ht

omit [FiniteDimensional ℝ E] [CompleteSpace E]
    [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
    [IsManifold I ∞ M] [T2Space M] [T2Space (TangentBundle I M)]
    [SigmaCompactSpace M] [BoundarylessManifold I M] in
private theorem mfderiv_comp_reverse_apply_one
    {gamma : ℝ → M} {L t : ℝ}
    (hgamma : MDifferentiableAt 𝓘(ℝ, ℝ) I gamma (L - t)) :
    mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ ↦ gamma (L - s)) t (1 : ℝ) =
      -(mfderiv 𝓘(ℝ, ℝ) I gamma (L - t) (1 : ℝ)) := by
  have haff : HasDerivAt (fun s : ℝ ↦ L - s) (-1) t := by
    exact (hasDerivAt_id t).const_sub L
  have hcomp := hgamma.hasMFDerivAt.comp t haff.hasFDerivAt.hasMFDerivAt
  have happly := congrArg (fun D ↦ D (1 : ℝ)) hcomp.mfderiv
  change mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ ↦ gamma (L - s)) t (1 : ℝ) =
    mfderiv 𝓘(ℝ, ℝ) I gamma (L - t)
      ((ContinuousLinearMap.toSpanSingleton ℝ (-1 : ℝ)) 1) at happly
  rw [happly]
  simp only [ContinuousLinearMap.toSpanSingleton_apply, one_smul]
  exact map_neg (mfderiv 𝓘(ℝ, ℝ) I gamma (L - t)) (1 : ℝ)

omit [FiniteDimensional ℝ E] [CompleteSpace E]
    [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
    [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
    [BoundarylessManifold I M] in
private theorem riemannianEDistOf_ne_top_of_distance_pos
    (g : SmoothRiemannianMetric I M) {x y : M}
    (h : 0 < riemannianDistance (I := I) g x y) :
    riemannianEDistOf (I := I) g x y ≠ ⊤ := by
  intro htop
  unfold riemannianDistance at h
  rw [htop] at h
  norm_num at h

omit [T2Space (TangentBundle I M)] in
theorem hingeComparison_of_realizedConnectors
    (g : SmoothRiemannianMetric I M)
    (hsec : HasNonnegativeSectionalCurvature (I := I) g)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {o : M} (sigma tau : ℝ → M)
    (hsigma : UnitSpeedGeodesicOn (I := I) g sigma (Icc 0 a))
    (htau : UnitSpeedGeodesicOn (I := I) g tau (Icc 0 b))
    (hsigma0 : sigma 0 = o) (htau0 : tau 0 = o)
    (hfirst : riemannianDistance (I := I) g o (sigma a) = a)
    (hconnectors : RealizedConnectors (I := I) g (sigma a) tau (Icc 0 b)) :
    riemannianDistance (I := I) g (sigma a) (tau b) ^ 2 ≤
      a ^ 2 + b ^ 2 -
        2 * a * b * Real.cos
          (tangentAngle g
            (mfderiv 𝓘(ℝ, ℝ) I sigma 0 (1 : ℝ))
            (mfderiv 𝓘(ℝ, ℝ) I tau 0 (1 : ℝ))) := by
  let F := squaredRiemannianDistanceDefect (I := I) g (sigma a) tau
  have hconvex : ConvexOn ℝ (Icc 0 b) F :=
    squaredDistanceDefect_convexOn_of_realizedConnectors
      (I := I) g hsec (sigma a) tau (Icc 0 b)
        (convex_Icc (0 : ℝ) b) htau hconnectors
  let rep := Classical.choice
    (exists_smoothArmRepresentative (I := I) g ha hsigma)
  let gamma : ℝ → M := fun s ↦ rep.curve (a - s)
  have hgammaSmooth : ContMDiff 𝓘(ℝ, ℝ) I ∞ gamma := by
    exact rep.smooth.comp
      (contDiff_const.sub contDiff_id).contMDiff
  have hgammaGeo : IsGeodesicOn (I := I) g gamma (Icc 0 a) := by
    have h := isGeodesicOn_comp_affine (I := I)
      (c := (-1 : ℝ)) (d := a) rep.geodesicOn
    have h' := h.mono (by
      intro (t : ℝ) (ht : t ∈ Icc (0 : ℝ) a)
      change -1 * t + a ∈ Icc (0 : ℝ) a
      constructor <;> linarith [ht.1, ht.2])
    intro t ht
    have heqt : gamma =ᶠ[nhds t]
        (fun s : ℝ ↦ rep.curve (-1 * s + a)) :=
      Filter.Eventually.of_forall (fun s ↦ by
        change rep.curve (a - s) = rep.curve (-1 * s + a)
        congr 1
        ring)
    exact HasGeodesicEquationAt.congr_of_eventuallyEq_at
      heqt.self_of_nhds heqt (h' t ht)
  have hgammaUnit : ∀ t ∈ Icc (0 : ℝ) a,
      g.inner (gamma t) (mfderiv 𝓘(ℝ, ℝ) I gamma t 1)
        (mfderiv 𝓘(ℝ, ℝ) I gamma t 1) = 1 := by
    intro t ht
    have htime : a - t ∈ Icc (0 : ℝ) a := by
      constructor <;> linarith [ht.1, ht.2]
    have hderiv := mfderiv_comp_reverse_apply_one (I := I)
      (gamma := rep.curve) (L := a) (t := t)
      (rep.smooth.mdifferentiableAt (by norm_num))
    change g.inner (rep.curve (a - t))
      (mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ ↦ rep.curve (a - s)) t 1)
      (mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ ↦ rep.curve (a - s)) t 1) = 1
    calc
      g.inner (rep.curve (a - t))
          (mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ ↦ rep.curve (a - s)) t 1)
          (mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ ↦ rep.curve (a - s)) t 1) =
        g.inner (rep.curve (a - t))
          (-(mfderiv 𝓘(ℝ, ℝ) I rep.curve (a - t) 1))
          (-(mfderiv 𝓘(ℝ, ℝ) I rep.curve (a - t) 1)) := by
            exact congrArg₂
              (fun u v ↦ g.inner (rep.curve (a - t)) u v) hderiv hderiv
      _ = 1 := by
        simpa only [map_neg, neg_apply, neg_neg] using
          rep.unitSpeed g ha hsigma htime
  have hgamma0 : gamma 0 = sigma a := by
    change rep.curve (a - 0) = sigma a
    simpa only [sub_zero] using rep.agrees ⟨ha.le, le_rfl⟩
  have hgammaa : gamma a = tau 0 := by
    change rep.curve (a - a) = tau 0
    rw [sub_self, rep.agrees ⟨le_rfl, ha.le⟩, hsigma0, htau0]
  have hdist : riemannianDistance (I := I) g (sigma a) (tau 0) = a := by
    rw [htau0, riemannianDistance_comm (I := I), hfirst]
  let w : TangentSpace I (gamma a) :=
    (mfderiv 𝓘(ℝ, ℝ) I tau 0 (1 : ℝ) : E)
  have hw : g.inner (gamma a) w w = 1 := by
    rw [hgammaa]
    exact htau.unitSpeed 0 ⟨le_rfl, hb.le⟩
  have htauVel :
      (mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ ↦ tau (0 + s)) 0 (1 : ℝ) : E) = w := by
    have heq : (fun s : ℝ ↦ tau (0 + s)) = tau := by
      funext s
      rw [zero_add]
    rw [heq]
    rfl
  obtain ⟨S, hSderiv, _hC2⟩ :=
    exists_squaredDistanceLowerSupport_of_positive
      (I := I) g hsec (sigma a) tau gamma Set.univ 0 a
      (by simp) ha hgammaSmooth hgammaGeo hgammaUnit hgamma0 hgammaa
      hdist w hw (htau.geodesicAt_shift 0 ⟨le_rfl, hb.le⟩) htauVel
  have hrepDeriv0 :
      mfderiv 𝓘(ℝ, ℝ) I rep.curve 0 =
        mfderiv 𝓘(ℝ, ℝ) I sigma 0 :=
    mfderiv_eq_of_eqOn_Icc (I := I) ha rep.agrees
      (rep.smooth.mdifferentiableAt (by norm_num))
      (hsigma.mdifferentiableAt g ⟨le_rfl, ha.le⟩) ⟨le_rfl, ha.le⟩
  have hgammaDerivA :
      mfderiv 𝓘(ℝ, ℝ) I gamma a (1 : ℝ) =
        -(mfderiv 𝓘(ℝ, ℝ) I sigma 0 (1 : ℝ)) := by
    rw [mfderiv_comp_reverse_apply_one (I := I)
      (rep.smooth.mdifferentiableAt (by norm_num)), sub_self, hrepDeriv0]
    rfl
  have hvSigma : IsUnitTangent g
      (mfderiv 𝓘(ℝ, ℝ) I sigma 0 (1 : ℝ)) := by
    unfold IsUnitTangent
    exact hsigma.unitSpeed 0 ⟨le_rfl, ha.le⟩
  have hvTau : IsUnitTangent g
      (mfderiv 𝓘(ℝ, ℝ) I tau 0 (1 : ℝ)) := by
    unfold IsUnitTangent
    exact htau.unitSpeed 0 ⟨le_rfl, hb.le⟩
  have hvTauAtSigma : IsUnitTangent (x := sigma 0) g
      (mfderiv 𝓘(ℝ, ℝ) I tau 0 (1 : ℝ)) := by
    unfold IsUnitTangent at hvTau ⊢
    rw [hsigma0, ← htau0]
    exact hvTau
  have hSderiv' :
      S.supportDeriv 0 =
        2 * a * g.inner (sigma 0)
          (mfderiv 𝓘(ℝ, ℝ) I sigma 0 (1 : ℝ))
          (mfderiv 𝓘(ℝ, ℝ) I tau 0 (1 : ℝ)) := by
    calc
      S.supportDeriv 0 =
          2 * 0 - 2 * a * g.inner (gamma a)
            (mfderiv 𝓘(ℝ, ℝ) I gamma a (1 : ℝ)) w := hSderiv
      _ = 2 * a * g.inner (sigma 0)
          (mfderiv 𝓘(ℝ, ℝ) I sigma 0 (1 : ℝ))
          (mfderiv 𝓘(ℝ, ℝ) I tau 0 (1 : ℝ)) := by
        have hbase : gamma a = sigma 0 := by
          rw [hgammaa, htau0, hsigma0]
        rw [hgammaDerivA, hbase]
        dsimp only [w]
        change
          2 * 0 - 2 * a * g.inner (sigma 0)
            (-(mfderiv 𝓘(ℝ, ℝ) I sigma 0 (1 : ℝ)))
            (mfderiv 𝓘(ℝ, ℝ) I tau 0 (1 : ℝ)) =
          2 * a * g.inner (sigma 0)
            (mfderiv 𝓘(ℝ, ℝ) I sigma 0 (1 : ℝ))
            (mfderiv 𝓘(ℝ, ℝ) I tau 0 (1 : ℝ))
        have hinnerNeg :
            g.inner (sigma 0)
              (-(mfderiv 𝓘(ℝ, ℝ) I sigma 0 (1 : ℝ)))
              (mfderiv 𝓘(ℝ, ℝ) I tau 0 (1 : ℝ)) =
            -g.inner (sigma 0)
              (mfderiv 𝓘(ℝ, ℝ) I sigma 0 (1 : ℝ))
              (mfderiv 𝓘(ℝ, ℝ) I tau 0 (1 : ℝ)) := by
          calc
            g.inner (sigma 0)
                (-(mfderiv 𝓘(ℝ, ℝ) I sigma 0 (1 : ℝ)))
                (mfderiv 𝓘(ℝ, ℝ) I tau 0 (1 : ℝ)) =
              g.inner (sigma 0)
                (mfderiv 𝓘(ℝ, ℝ) I tau 0 (1 : ℝ))
                (-(mfderiv 𝓘(ℝ, ℝ) I sigma 0 (1 : ℝ))) :=
                  g.symm _ _ _
            _ = -g.inner (sigma 0)
                (mfderiv 𝓘(ℝ, ℝ) I tau 0 (1 : ℝ))
                (mfderiv 𝓘(ℝ, ℝ) I sigma 0 (1 : ℝ)) := by
                  rw [map_neg]
            _ = -g.inner (sigma 0)
                (mfderiv 𝓘(ℝ, ℝ) I sigma 0 (1 : ℝ))
                (mfderiv 𝓘(ℝ, ℝ) I tau 0 (1 : ℝ)) := by
                  exact congrArg Neg.neg
                    (g.symm (sigma 0)
                      (mfderiv 𝓘(ℝ, ℝ) I tau 0 (1 : ℝ))
                      (mfderiv 𝓘(ℝ, ℝ) I sigma 0 (1 : ℝ)))
        rw [hinnerNeg]
        ring
  obtain ⟨delta, hdelta, hdeltaSub⟩ :=
    Metric.mem_nhds_iff.mp S.domain_mem_nhds
  let epsilon : ℝ := min delta b / 2
  have hepsilon : 0 < epsilon := by
    dsimp only [epsilon]
    positivity
  have hepsilonB : epsilon ≤ b := by
    dsimp only [epsilon]
    linarith [min_le_right delta b, hb]
  have hsupport : ∀ r ∈ Ico (0 : ℝ) epsilon, S.support r ≤ F r := by
    intro r hr
    apply S.support_le r
    apply hdeltaSub
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hr.1]
    have hepsDelta : epsilon < delta := by
      dsimp only [epsilon]
      have hmin := min_le_left delta b
      linarith
    exact hr.2.trans hepsDelta
  have hzeroDomain : 0 ∈ S.domain := mem_of_mem_nhds S.domain_mem_nhds
  have hendpoint := convex_endpoint_ge_of_lower_support hb hepsilon hepsilonB
    hconvex hsupport S.support_eq
      (S.hasDerivAt_support 0 hzeroDomain).hasDerivWithinAt
  rw [hSderiv'] at hendpoint
  have hcos := cos_tangentAngle_of_unit g hvSigma hvTauAtSigma
  change
    riemannianDistance (I := I) g (sigma a) (tau b) ^ 2 ≤
      a ^ 2 + b ^ 2 -
        2 * a * b * Real.cos
          (tangentAngle g
            (mfderiv 𝓘(ℝ, ℝ) I sigma 0 (1 : ℝ))
            (mfderiv 𝓘(ℝ, ℝ) I tau 0 (1 : ℝ)))
  unfold F squaredRiemannianDistanceDefect at hendpoint
  rw [htau0, riemannianDistance_comm (I := I), hfirst] at hendpoint
  rw [hcos]
  calc
    riemannianDistance (I := I) g (sigma a) (tau b) ^ 2 ≤
        b ^ 2 -
          (-a ^ 2 + b *
            (2 * a * g.inner (sigma 0)
              (mfderiv 𝓘(ℝ, ℝ) I sigma 0 (1 : ℝ))
              (mfderiv 𝓘(ℝ, ℝ) I tau 0 (1 : ℝ)))) := by
      apply (le_sub_iff_add_le).2
      have h := (le_sub_iff_add_le).mp hendpoint
      norm_num at h
      rw [add_comm] at h
      exact h
    _ = a ^ 2 + b ^ 2 -
        2 * a * b * g.inner (sigma 0)
          (mfderiv 𝓘(ℝ, ℝ) I sigma 0 (1 : ℝ))
          (mfderiv 𝓘(ℝ, ℝ) I tau 0 (1 : ℝ)) := by ring

theorem hingeComparison_of_complete
    [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M)
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsec : HasNonnegativeSectionalCurvature (I := I) g)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {o : M} (sigma tau : ℝ → M)
    (hsigma : UnitSpeedGeodesicOn (I := I) g sigma (Icc 0 a))
    (htau : UnitSpeedGeodesicOn (I := I) g tau (Icc 0 b))
    (hsigma0 : sigma 0 = o) (htau0 : tau 0 = o)
    (hfirst : riemannianDistance (I := I) g o (sigma a) = a) :
    riemannianDistance (I := I) g (sigma a) (tau b) ^ 2 ≤
      a ^ 2 + b ^ 2 -
        2 * a * b * Real.cos
          (tangentAngle g
            (mfderiv 𝓘(ℝ, ℝ) I sigma 0 (1 : ℝ))
            (mfderiv 𝓘(ℝ, ℝ) I tau 0 (1 : ℝ))) := by
  exact hingeComparison_of_realizedConnectors
    (I := I) g hsec ha hb sigma tau hsigma htau hsigma0 htau0 hfirst
      (realizedConnectors_of_complete
        (I := I) g hcomplete (sigma a) tau (Icc 0 b))

theorem equalArmEndpointEstimate_of_complete
    [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M)
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsec : HasNonnegativeSectionalCurvature (I := I) g)
    {a : ℝ} (ha : 0 < a)
    {o : M} (sigma tau : ℝ → M)
    (hsigma : UnitSpeedGeodesicOn (I := I) g sigma (Icc 0 a))
    (htau : UnitSpeedGeodesicOn (I := I) g tau (Icc 0 a))
    (hsigma0 : sigma 0 = o) (htau0 : tau 0 = o)
    (hfirst : riemannianDistance (I := I) g o (sigma a) = a) :
    riemannianDistance (I := I) g (sigma a) (tau a) ≤
      2 * a * Real.sin
        (tangentAngle g
          (mfderiv 𝓘(ℝ, ℝ) I sigma 0 (1 : ℝ))
          (mfderiv 𝓘(ℝ, ℝ) I tau 0 (1 : ℝ)) / 2) := by
  let theta : ℝ :=
    tangentAngle g
      (mfderiv 𝓘(ℝ, ℝ) I sigma 0 (1 : ℝ))
      (mfderiv 𝓘(ℝ, ℝ) I tau 0 (1 : ℝ))
  have hhinge := hingeComparison_of_complete
    (I := I) g hcomplete hsec ha ha sigma tau hsigma htau
      hsigma0 htau0 hfirst
  apply equalArm_le_two_mul_sin_half_of_sq_le ha.le
    (ENNReal.toReal_nonneg) (tangentAngle_mem_Icc g _ _)
  change riemannianDistance (I := I) g (sigma a) (tau a) ^ 2 ≤
    2 * a ^ 2 * (1 - Real.cos theta)
  change riemannianDistance (I := I) g (sigma a) (tau a) ^ 2 ≤
    a ^ 2 + a ^ 2 - 2 * a * a * Real.cos theta at hhinge
  calc
    riemannianDistance (I := I) g (sigma a) (tau a) ^ 2 ≤
        a ^ 2 + a ^ 2 - 2 * a * a * Real.cos theta := hhinge
    _ = 2 * a ^ 2 * (1 - Real.cos theta) := by ring

omit [T2Space (TangentBundle I M)] in
theorem riemannianComparisonAngle_le_tangentAngle_of_realizedConnectors
    (g : SmoothRiemannianMetric I M)
    (hsec : HasNonnegativeSectionalCurvature (I := I) g)
    {x o y : M} (hxo : x ≠ o) (hyo : y ≠ o)
    (sigma tau : ℝ → M)
    (hsigma : UnitSpeedGeodesicOn (I := I) g sigma
      (Icc 0 (riemannianDistance (I := I) g o x)))
    (htau : UnitSpeedGeodesicOn (I := I) g tau
      (Icc 0 (riemannianDistance (I := I) g o y)))
    (hsigma0 : sigma 0 = o)
    (hsigmaEnd :
      sigma (riemannianDistance (I := I) g o x) = x)
    (htau0 : tau 0 = o)
    (htauEnd :
      tau (riemannianDistance (I := I) g o y) = y)
    (hconnectors : RealizedConnectors (I := I) g x tau
      (Icc 0 (riemannianDistance (I := I) g o y))) :
    riemannianComparisonAngle (I := I) g x o y ≤
      tangentAngle g
        (mfderiv 𝓘(ℝ, ℝ) I sigma 0 (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) I tau 0 (1 : ℝ)) := by
  let a := riemannianDistance (I := I) g o x
  let b := riemannianDistance (I := I) g o y
  change UnitSpeedGeodesicOn (I := I) g sigma (Icc 0 a) at hsigma
  change UnitSpeedGeodesicOn (I := I) g tau (Icc 0 b) at htau
  change sigma a = x at hsigmaEnd
  change tau b = y at htauEnd
  change RealizedConnectors (I := I) g x tau (Icc 0 b) at hconnectors
  have haNonneg : 0 ≤ a := ENNReal.toReal_nonneg
  have hbNonneg : 0 ≤ b := ENNReal.toReal_nonneg
  have ha : 0 < a := by
    rcases haNonneg.eq_or_lt with hzero | hpos
    · exfalso
      apply hxo
      rw [← hsigmaEnd]
      rw [← hzero, hsigma0]
    · exact hpos
  have hb : 0 < b := by
    rcases hbNonneg.eq_or_lt with hzero | hpos
    · exfalso
      apply hyo
      rw [← htauEnd]
      rw [← hzero, htau0]
    · exact hpos
  have hhinge := hingeComparison_of_realizedConnectors
    (I := I) g hsec ha hb sigma tau hsigma htau hsigma0 htau0
      (by
        rw [hsigmaEnd])
      (by
        rw [hsigmaEnd]
        exact hconnectors)
  have hhinge' :
      riemannianDistance (I := I) g x y ^ 2 ≤
        a ^ 2 + b ^ 2 -
          2 * a * b * Real.cos
            (tangentAngle g
              (mfderiv 𝓘(ℝ, ℝ) I sigma 0 (1 : ℝ))
              (mfderiv 𝓘(ℝ, ℝ) I tau 0 (1 : ℝ))) := by
    rw [hsigmaEnd, htauEnd] at hhinge
    exact hhinge
  have hoxFinite : riemannianEDistOf (I := I) g o x ≠ ⊤ :=
    riemannianEDistOf_ne_top_of_distance_pos (I := I) g ha
  have hoyFinite : riemannianEDistOf (I := I) g o y ≠ ⊤ :=
    riemannianEDistOf_ne_top_of_distance_pos (I := I) g hb
  have hxyFinite : riemannianEDistOf (I := I) g x y ≠ ⊤ := by
    obtain ⟨c⟩ := hconnectors b ⟨hb.le, le_rfl⟩
    rw [htauEnd] at c
    rw [c.realizes]
    exact ENNReal.ofReal_ne_top
  have hsides :=
    riemannianComparisonAngle_sideInequalities
      (I := I) g x o y hoxFinite hoyFinite hxyFinite
  unfold riemannianComparisonAngle
  exact comparisonAngle_le_of_hinge_sq ha hb hsides.1 hsides.2
    (tangentAngle_mem_Icc g _ _) hhinge'

theorem riemannianComparisonAngle_le_tangentAngle_of_complete
    [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M)
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsec : HasNonnegativeSectionalCurvature (I := I) g)
    {x o y : M} (hxo : x ≠ o) (hyo : y ≠ o)
    (sigma tau : ℝ → M)
    (hsigma : UnitSpeedGeodesicOn (I := I) g sigma
      (Icc 0 (riemannianDistance (I := I) g o x)))
    (htau : UnitSpeedGeodesicOn (I := I) g tau
      (Icc 0 (riemannianDistance (I := I) g o y)))
    (hsigma0 : sigma 0 = o)
    (hsigmaEnd :
      sigma (riemannianDistance (I := I) g o x) = x)
    (htau0 : tau 0 = o)
    (htauEnd :
      tau (riemannianDistance (I := I) g o y) = y) :
    riemannianComparisonAngle (I := I) g x o y ≤
      tangentAngle g
        (mfderiv 𝓘(ℝ, ℝ) I sigma 0 (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) I tau 0 (1 : ℝ)) := by
  exact riemannianComparisonAngle_le_tangentAngle_of_realizedConnectors
    (I := I) g hsec hxo hyo sigma tau hsigma htau
      hsigma0 hsigmaEnd htau0 htauEnd
      (realizedConnectors_of_complete
        (I := I) g hcomplete x tau
          (Icc 0 (riemannianDistance (I := I) g o y)))

end DifferentialGeometry.Toponogov
