import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CylinderDeckProductForm
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientCylinderNoTranslation
import DifferentialGeometry.Geometry.Metric.UniversalCover.DeckIsometry
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Group.Subgroup.Ker

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Riemannian.Topology
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood
open scoped Manifold ContDiff

local notation "SphereAmbient" => EuclideanSpace ℝ (Fin 3)
local notation "SphereTwo" => Metric.sphere (0 : SphereAmbient) 1
private abbrev CylinderI := (𝓡 2).prod (𝓘(ℝ, ℝ))
local notation "OrthogonalThree" => SphereAmbient ≃ₗᵢ[ℝ] SphereAmbient
local notation "LineIsometry" => ℝ ≃ᵃⁱ[ℝ] ℝ
local notation "CylinderIsometry" => OrthogonalThree × LineIsometry
local notation "sphereMetric" => roundMetric (E := SphereAmbient) (n := 2)

private local instance cylinderRepresentationSphereDimension :
    Fact (Module.finrank ℝ SphereAmbient = 2 + 1) := ⟨by simp⟩

private def cylinderRepresentationSpherePoint : SphereTwo :=
  ⟨EuclideanSpace.single (0 : Fin 3) (1 : ℝ), by
    simp only [Metric.mem_sphere, dist_zero_right, PiLp.norm_single, norm_one]⟩

private theorem cylinderRepresentation_deck_eval_injective
    {X : Type*} [TopologicalSpace X] [Inhabited X] (p : UniversalCover X) :
    Function.Injective (fun gamma : FundamentalGroup X (default : X) => gamma • p) := by
  intro gamma delta h
  rcases p with ⟨x, q⟩
  change (⟨x, (FundamentalGroup.toPath gamma⁻¹).trans q⟩ : UniversalCover X) =
    ⟨x, (FundamentalGroup.toPath delta⁻¹).trans q⟩ at h
  have hpaths : (FundamentalGroup.toPath gamma⁻¹).trans q =
      (FundamentalGroup.toPath delta⁻¹).trans q := sigma_mk_injective h
  have hcancel := congrArg
    (fun a : Path.Homotopic.Quotient (default : X) x => a.trans q.symm) hpaths
  simp only [Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.trans_symm,
    Path.Homotopic.Quotient.trans_refl] at hcancel
  have hinv : gamma⁻¹ = delta⁻¹ := hcancel
  exact inv_injective hinv

section FixedCylinder

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [LocallyPathConnectedSpace M] [SemilocallySimplyConnectedSpace M] [Inhabited M]

private def cylinderRepresentation_conjugate
    (Psi : (SphereTwo × ℝ) ≃ₘ⟮CylinderI, I⟯ UniversalCover M)
    (gamma : FundamentalGroup M (default : M)) :
    (SphereTwo × ℝ) ≃ₘ⟮CylinderI, CylinderI⟯ (SphereTwo × ℝ) :=
  (Psi.trans (UniversalCover.deckDiffeo (I := I) gamma)).trans Psi.symm

omit [IsManifold I ∞ M] in
private theorem cylinderRepresentation_conjugate_eq
    (Psi : (SphereTwo × ℝ) ≃ₘ⟮CylinderI, I⟯ UniversalCover M)
    (gamma : FundamentalGroup M (default : M)) (p : SphereTwo × ℝ) :
    Psi (cylinderRepresentation_conjugate Psi gamma p) = gamma • Psi p :=
  Psi.apply_symm_apply (gamma • Psi p)

omit [IsManifold I ∞ M] in
private theorem cylinderRepresentation_conjugate_deriv
    (Psi : (SphereTwo × ℝ) ≃ₘ⟮CylinderI, I⟯ UniversalCover M)
    (gamma : FundamentalGroup M (default : M)) (p : SphereTwo × ℝ)
    (v : TangentSpace CylinderI p) :
    mfderiv CylinderI I Psi (cylinderRepresentation_conjugate Psi gamma p)
        (mfderiv CylinderI CylinderI (cylinderRepresentation_conjugate Psi gamma) p v) =
      mfderiv I I (fun q : UniversalCover M => gamma • q) (Psi p)
        (mfderiv CylinderI I Psi p v) := by
  have hfun : (Psi : SphereTwo × ℝ → UniversalCover M) ∘
      cylinderRepresentation_conjugate Psi gamma =
      (fun q : UniversalCover M => gamma • q) ∘ Psi :=
    funext (cylinderRepresentation_conjugate_eq Psi gamma)
  have h := congrArg
    (fun f : SphereTwo × ℝ → UniversalCover M => mfderiv CylinderI I f p v) hfun
  rw [mfderiv_comp_apply p
    (Psi.mdifferentiable (by decide) (cylinderRepresentation_conjugate Psi gamma p))
    ((cylinderRepresentation_conjugate Psi gamma).mdifferentiable (by decide) p) v,
    mfderiv_comp_apply p
      ((UniversalCover.deckAct_contMDiff (I := I) gamma).mdifferentiable
        (by decide) (Psi p)) (Psi.mdifferentiable (by decide) p) v] at h
  exact h

private theorem cylinderRepresentation_metric_preserved
    (g : ℝ → SmoothRiemannianMetric I M) (T : ℝ)
    (Psi : (SphereTwo × ℝ) ≃ₘ⟮CylinderI, I⟯ UniversalCover M)
    (hproduct : ∀ t : ℝ, t ≤ 0 → ∀ (x : SphereTwo) (s : ℝ)
      (v w : TangentSpace (𝓡 2) x) (a b : ℝ),
      (UniversalCover.liftedMetric (I := I) (g t)).inner (Psi (x, s))
          (mfderiv CylinderI I Psi (x, s) (v, a))
          (mfderiv CylinderI I Psi (x, s) (w, b)) =
        (2 * (T - t)) * (sphereMetric).inner x v w + a * b)
    (gamma : FundamentalGroup M (default : M)) (t : ℝ) (ht : t ≤ 0)
    (p : SphereTwo × ℝ) (v w : TangentSpace (𝓡 2) p.1) (a b : ℝ) :
    (2 * (T - t)) * (sphereMetric).inner
        (cylinderRepresentation_conjugate Psi gamma p).1
        (mfderiv CylinderI CylinderI (cylinderRepresentation_conjugate Psi gamma) p (v, a)).1
        (mfderiv CylinderI CylinderI (cylinderRepresentation_conjugate Psi gamma) p (w, b)).1 +
      (mfderiv CylinderI CylinderI (cylinderRepresentation_conjugate Psi gamma) p (v, a)).2 *
        (mfderiv CylinderI CylinderI (cylinderRepresentation_conjugate Psi gamma) p (w, b)).2 =
      (2 * (T - t)) * (sphereMetric).inner p.1 v w + a * b := by
  let Phi := cylinderRepresentation_conjugate Psi gamma
  calc
    _ = (UniversalCover.liftedMetric (I := I) (g t)).inner (Psi (Phi p))
        (mfderiv CylinderI I Psi (Phi p) (mfderiv CylinderI CylinderI Phi p (v, a)))
        (mfderiv CylinderI I Psi (Phi p) (mfderiv CylinderI CylinderI Phi p (w, b))) :=
      (hproduct t ht (Phi p).1 (Phi p).2
        (mfderiv CylinderI CylinderI Phi p (v, a)).1
        (mfderiv CylinderI CylinderI Phi p (w, b)).1
        (mfderiv CylinderI CylinderI Phi p (v, a)).2
        (mfderiv CylinderI CylinderI Phi p (w, b)).2).symm
    _ = (UniversalCover.liftedMetric (I := I) (g t)).inner (gamma • Psi p)
        (mfderiv I I (fun q : UniversalCover M => gamma • q) (Psi p)
          (mfderiv CylinderI I Psi p (v, a)))
        (mfderiv I I (fun q : UniversalCover M => gamma • q) (Psi p)
          (mfderiv CylinderI I Psi p (w, b))) := by
      have hbase : Psi (Phi p) = gamma • Psi p := by
        exact cylinderRepresentation_conjugate_eq Psi gamma p
      have hv :
          mfderiv CylinderI I Psi (Phi p)
              (mfderiv CylinderI CylinderI Phi p (v, a)) =
            mfderiv I I (fun q : UniversalCover M => gamma • q) (Psi p)
              (mfderiv CylinderI I Psi p (v, a)) := by
        exact cylinderRepresentation_conjugate_deriv Psi gamma p (v, a)
      have hw :
          mfderiv CylinderI I Psi (Phi p)
              (mfderiv CylinderI CylinderI Phi p (w, b)) =
            mfderiv I I (fun q : UniversalCover M => gamma • q) (Psi p)
              (mfderiv CylinderI I Psi p (w, b)) := by
        exact cylinderRepresentation_conjugate_deriv Psi gamma p (w, b)
      rw [← hbase, hv, hw]
      rfl
    _ = (UniversalCover.liftedMetric (I := I) (g t)).inner (Psi p)
        (mfderiv CylinderI I Psi p (v, a)) (mfderiv CylinderI I Psi p (w, b)) :=
      UniversalCover.deck_inner (I := I) (g t) gamma (Psi p) _ _
    _ = _ := hproduct t ht p.1 p.2 v w a b

theorem exists_cylinderDeckRepresentation
    (g : ℝ → SmoothRiemannianMetric I M) (T : ℝ)
    (Psi : (SphereTwo × ℝ) ≃ₘ⟮CylinderI, I⟯ UniversalCover M)
    (hproduct : ∀ t : ℝ, t ≤ 0 → ∀ (x : SphereTwo) (s : ℝ)
      (v w : TangentSpace (𝓡 2) x) (a b : ℝ),
      (UniversalCover.liftedMetric (I := I) (g t)).inner (Psi (x, s))
          (mfderiv CylinderI I Psi (x, s) (v, a))
          (mfderiv CylinderI I Psi (x, s) (w, b)) =
        (2 * (T - t)) * (sphereMetric).inner x v w + a * b) :
    ∃ rho : FundamentalGroup M (default : M) →* CylinderIsometry,
      Function.Injective rho ∧
      (∀ (gamma : FundamentalGroup M (default : M)) (x : SphereTwo) (s : ℝ),
        gamma • Psi (x, s) = Psi (sphereDiffeo (n := 2) (rho gamma).1 x, (rho gamma).2 s)) ∧
      ∀ delta : CylinderIsometry, delta ∈ rho.range → delta ≠ 1 →
        ∀ p : SphereTwo × ℝ,
          (delta.1 (p.1 : SphereAmbient), delta.2 p.2) ≠ ((p.1 : SphereAmbient), p.2) := by
  classical
  let Phi := cylinderRepresentation_conjugate Psi
  have hPhiOne (p : SphereTwo × ℝ) : Phi 1 p = p := by
    change Psi.symm ((1 : FundamentalGroup M (default : M)) • Psi p) = p
    rw [one_smul, Psi.symm_apply_apply]
  have hPhiMul (gamma delta : FundamentalGroup M (default : M)) (p : SphereTwo × ℝ) :
      Phi (gamma * delta) p = Phi gamma (Phi delta p) := by
    change Psi.symm ((gamma * delta) • Psi p) =
      Psi.symm (gamma • Psi (Psi.symm (delta • Psi p)))
    rw [Psi.apply_symm_apply, mul_smul]
  have hsplit (gamma : FundamentalGroup M (default : M)) :
      ∃ (A : SphereTwo ≃ₘ⟮𝓡 2, 𝓡 2⟯ SphereTwo) (b : LineIsometry),
        (∀ (x : SphereTwo) (v w : TangentSpace (𝓡 2) x),
          (sphereMetric).inner (A x)
              (mfderiv (𝓡 2) (𝓡 2) A x v) (mfderiv (𝓡 2) (𝓡 2) A x w) =
            (sphereMetric).inner x v w) ∧
        ∀ (x : SphereTwo) (s : ℝ), Phi gamma (x, s) = (A x, b s) := by
    have ht : ∀ t : ℝ, t = -1 ∨ t = 0 → t ≤ 0 := by
      intro t ht
      rcases ht with rfl | rfl <;> norm_num
    obtain ⟨A, b, hA, hfactor, -⟩ := cylinderDeck_exists_product_affine
      (Phi gamma) (T := T) (t₀ := -1) (t₁ := 0) (by norm_num)
      (fun t ht' p v w a b =>
        cylinderRepresentation_metric_preserved g T Psi hproduct gamma t (ht t ht') p v w a b)
    exact ⟨A, b, hA, hfactor⟩
  choose A b hA hfactor using hsplit
  let p₀ : SphereTwo := cylinderRepresentationSpherePoint
  have hAOne (x : SphereTwo) : A 1 x = x :=
    (congrArg Prod.fst (hfactor 1 x 0)).symm.trans (congrArg Prod.fst (hPhiOne (x, 0)))
  have hAMul (gamma delta : FundamentalGroup M (default : M)) (x : SphereTwo) :
      A (gamma * delta) x = A gamma (A delta x) := by
    have h := hPhiMul gamma delta (x, 0)
    rw [hfactor (gamma * delta) x 0, hfactor delta x 0,
      hfactor gamma (A delta x) (b delta 0)] at h
    exact congrArg Prod.fst h
  have hbOne (s : ℝ) : b 1 s = s :=
    (congrArg Prod.snd (hfactor 1 p₀ s)).symm.trans (congrArg Prod.snd (hPhiOne (p₀, s)))
  have hbMul (gamma delta : FundamentalGroup M (default : M)) (s : ℝ) :
      b (gamma * delta) s = b gamma (b delta s) := by
    have h := hPhiMul gamma delta (p₀, s)
    rw [hfactor (gamma * delta) p₀ s, hfactor delta p₀ s,
      hfactor gamma (A delta p₀) (b delta s)] at h
    exact congrArg Prod.snd h
  obtain ⟨rhoSphere, hrhoSphere⟩ := orth_rep_of_iso (n := 2) p₀ A (by decide)
    hAOne hAMul (fun gamma x v w => (hA gamma x v w).symm)
  let rhoLine : FundamentalGroup M (default : M) →* LineIsometry := {
    toFun := b
    map_one' := AffineIsometryEquiv.ext hbOne
    map_mul' gamma delta := AffineIsometryEquiv.ext (hbMul gamma delta) }
  let rho := rhoSphere.prod rhoLine
  have hdeck (gamma : FundamentalGroup M (default : M)) (x : SphereTwo) (s : ℝ) :
      gamma • Psi (x, s) = Psi (sphereDiffeo (n := 2) (rho gamma).1 x, (rho gamma).2 s) := by
    change gamma • Psi (x, s) = Psi (sphereDiffeo (n := 2) (rhoSphere gamma) x, b gamma s)
    rw [hrhoSphere gamma]
    have h := congrArg Psi (hfactor gamma x s)
    change Psi (Psi.symm (gamma • Psi (x, s))) = Psi (A gamma x, b gamma s) at h
    rw [Psi.apply_symm_apply] at h
    exact h
  have hinjective : Function.Injective rho := by
    intro gamma delta h
    apply cylinderRepresentation_deck_eval_injective (Psi (p₀, 0))
    change gamma • Psi (p₀, 0) = delta • Psi (p₀, 0)
    rw [hdeck, hdeck, h]
  refine ⟨rho, hinjective, hdeck, ?_⟩
  intro delta hdelta hne p hfixed
  obtain ⟨gamma, hgamma⟩ := MonoidHom.mem_range.mp hdelta
  have hsphere : sphereDiffeo (n := 2) delta.1 p.1 = p.1 :=
    Subtype.ext (congrArg Prod.fst hfixed)
  have hline : delta.2 p.2 = p.2 := congrArg Prod.snd hfixed
  have hact : gamma • Psi p = Psi p := by
    rw [hdeck gamma p.1 p.2, hgamma, hsphere, hline]
  have hgammaOne : gamma = 1 := cylinderRepresentation_deck_eval_injective (Psi p)
    (hact.trans (one_smul (FundamentalGroup M (default : M)) (Psi p)).symm)
  apply hne
  rw [← hgamma, hgammaOne, map_one]

end FixedCylinder

section AncientFlow

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance cylinderRepresentationBaseTopology : TopologicalSpace F.M := F.topology
local instance cylinderRepresentationBaseCharted : ChartedSpace H F.M := F.charted
local instance cylinderRepresentationBaseSmooth : IsManifold I ∞ F.M := F.smooth
local instance cylinderRepresentationBaseInhabited : Inhabited F.M := ⟨F.basepoint⟩
local instance cylinderRepresentationBaseT2 : T2Space F.M := F.t2
local instance cylinderRepresentationBaseSigma : SigmaCompactSpace F.M := F.sigmaCompact
local instance cylinderRepresentationBaseLocallyPathConnected : LocallyPathConnectedSpace F.M := by
  let _ : LocallyPathConnectedSpace H := I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  exact ChartedSpace.locallyPathConnectedSpace H F.M
local instance cylinderRepresentationBaseSemilocallySimplyConnected :
    SemilocallySimplyConnectedSpace F.M :=
  manifold_semilocallySimplyConnectedSpace (I := I) (M := F.M)

theorem ancientKappa_exists_cylinderDeckRepresentation {kappa : ℝ}
    (hF : IsAncientKappaSolution (I := I) kappa F) (hdim : Module.finrank ℝ E = 3)
    (T : ℝ) (hT : 0 < T)
    (Psi : (SphereTwo × ℝ) ≃ₘ⟮CylinderI, I⟯ UniversalCover F.M)
    (hproduct : ∀ t : ℝ, t ≤ 0 → ∀ (x : SphereTwo) (s : ℝ)
      (v w : TangentSpace (𝓡 2) x) (a b : ℝ),
      (UniversalCover.liftedMetric (I := I) (F.S.family.metric t)).inner (Psi (x, s))
          (mfderiv CylinderI I Psi (x, s) (v, a))
          (mfderiv CylinderI I Psi (x, s) (w, b)) =
        (2 * (T - t)) * (sphereMetric).inner x v w + a * b) :
    ∃ rho : FundamentalGroup F.M (default : F.M) →* CylinderIsometry,
      Function.Injective rho ∧
      (∀ (gamma : FundamentalGroup F.M (default : F.M)) (x : SphereTwo) (s : ℝ),
        gamma • Psi (x, s) = Psi (sphereDiffeo (n := 2) (rho gamma).1 x, (rho gamma).2 s)) ∧
      (∀ delta : CylinderIsometry, delta ∈ rho.range → delta ≠ 1 →
        ∀ p : SphereTwo × ℝ,
          (delta.1 (p.1 : SphereAmbient), delta.2 p.2) ≠ ((p.1 : SphereAmbient), p.2)) ∧
      ∀ delta : CylinderIsometry, delta ∈ rho.range → ∀ c : ℝ,
        delta.2 = AffineIsometryEquiv.vaddConst ℝ c → c = 0 := by
  obtain ⟨rho, hinjective, hdeck, hfree⟩ :=
    exists_cylinderDeckRepresentation (F.S.family.metric) T Psi hproduct
  refine ⟨rho, hinjective, hdeck, hfree, ?_⟩
  intro delta hdelta c hc
  obtain ⟨gamma, hgamma⟩ := MonoidHom.mem_range.mp hdelta
  apply ancientKappa_fixed_cylinder_deck_translation_eq_zero F hF hdim T hT Psi hproduct
    gamma (sphereDiffeo (n := 2) (rho gamma).1).toEquiv c
  intro x s
  rw [hdeck]
  apply congrArg Psi
  apply Prod.ext
  · rfl
  · change (rho gamma).2 s = s + c
    rw [hgamma, hc]
    rfl

end AncientFlow

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
