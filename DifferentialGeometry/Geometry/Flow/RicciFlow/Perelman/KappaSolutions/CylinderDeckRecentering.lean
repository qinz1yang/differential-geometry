import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientCylinderDeckClassification
import Mathlib.Analysis.Calculus.FDeriv.Add

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Riemannian.Topology
open scoped _root_.Manifold ContDiff

local notation "SphereAmbient" => EuclideanSpace ℝ (Fin 3)
local notation "SphereTwo" => Metric.sphere (0 : SphereAmbient) 1
private abbrev CylinderI := (𝓡 2).prod (𝓘(ℝ, ℝ))
local notation "OrthogonalThree" => SphereAmbient ≃ₗᵢ[ℝ] SphereAmbient
local notation "sphereMetric" => roundMetric (E := SphereAmbient) (n := 2)
local notation "antipodal" => sphereDiffeo (n := 2)
  (LinearIsometryEquiv.neg ℝ : OrthogonalThree)

private local instance cylinderRecenteringSphereDimension :
    Fact (Module.finrank ℝ SphereAmbient = 2 + 1) := ⟨by simp⟩

private def cylinderRecentering_lineTranslation (c : ℝ) : ℝ ≃ₘ[ℝ] ℝ where
  toFun s := s + c
  invFun s := s - c
  left_inv s := add_sub_cancel_right s c
  right_inv s := sub_add_cancel s c
  contMDiff_toFun := (contDiff_id.add contDiff_const).contMDiff
  contMDiff_invFun := (contDiff_id.sub contDiff_const).contMDiff


def cylinderLineTranslation (c : ℝ) :
    (SphereTwo × ℝ) ≃ₘ⟮CylinderI, CylinderI⟯ (SphereTwo × ℝ) :=
  (Diffeomorph.refl (𝓡 2) SphereTwo ∞).prodCongr (cylinderRecentering_lineTranslation c)


theorem cylinderLineTranslation_apply (c : ℝ) (p : SphereTwo × ℝ) :
    cylinderLineTranslation c p = (p.1, p.2 + c) := rfl


theorem mfderiv_cylinderLineTranslation (c : ℝ) (x : SphereTwo) (s : ℝ)
    (v : TangentSpace (𝓡 2) x) (a : ℝ) :
    mfderiv CylinderI CylinderI (cylinderLineTranslation c) (x, s) (v, a) =
      (v, a) := by
  have hline : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (cylinderRecentering_lineTranslation c) s =
      ContinuousLinearMap.id ℝ ℝ := by
    change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun r : ℝ => r + c) s = _
    rw [mfderiv_eq_fderiv, fderiv_add_const]
    exact fderiv_id
  change mfderiv CylinderI CylinderI
    (Prod.map (id : SphereTwo → SphereTwo) (cylinderRecentering_lineTranslation c))
      (x, s) (v, a) = _
  rw [mfderiv_prodMap mdifferentiableAt_id
    ((cylinderRecentering_lineTranslation c).mdifferentiable (by decide) s),
    mfderiv_id, hline]
  rfl

section FixedCover

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [LocallyPathConnectedSpace M] [SemilocallySimplyConnectedSpace M] [Inhabited M]

theorem cylinderLineTranslation_trans_pullback
    (g : ℝ → SmoothRiemannianMetric I M) (T : ℝ)
    (Psi : (SphereTwo × ℝ) ≃ₘ⟮CylinderI, I⟯ UniversalCover M)
    (hproduct : ∀ t : ℝ, t ≤ 0 → ∀ (x : SphereTwo) (s : ℝ)
      (v w : TangentSpace (𝓡 2) x) (a b : ℝ),
      (UniversalCover.liftedMetric (I := I) (g t)).inner (Psi (x, s))
          (mfderiv CylinderI I Psi (x, s) (v, a))
          (mfderiv CylinderI I Psi (x, s) (w, b)) =
        (2 * (T - t)) * (sphereMetric).inner x v w + a * b)
    (c : ℝ) :
    ∀ t : ℝ, t ≤ 0 → ∀ (x : SphereTwo) (s : ℝ)
      (v w : TangentSpace (𝓡 2) x) (a b : ℝ),
      (UniversalCover.liftedMetric (I := I) (g t)).inner
          (((cylinderLineTranslation c).trans Psi) (x, s))
          (mfderiv CylinderI I ((cylinderLineTranslation c).trans Psi) (x, s) (v, a))
          (mfderiv CylinderI I ((cylinderLineTranslation c).trans Psi) (x, s) (w, b)) =
        (2 * (T - t)) * (sphereMetric).inner x v w + a * b := by
  have hderiv (x : SphereTwo) (s : ℝ) (v : TangentSpace (𝓡 2) x) (a : ℝ) :
      mfderiv CylinderI I ((cylinderLineTranslation c).trans Psi) (x, s) (v, a) =
        mfderiv CylinderI I Psi (x, s + c) (v, a) := by
    change mfderiv CylinderI I
      ((Psi : SphereTwo × ℝ → UniversalCover M) ∘ (cylinderLineTranslation c))
        (x, s) (v, a) = _
    rw [mfderiv_comp_apply (x, s)
      (Psi.mdifferentiable (by decide) (cylinderLineTranslation c (x, s)))
      ((cylinderLineTranslation c).mdifferentiable (by decide) (x, s)) (v, a),
      mfderiv_cylinderLineTranslation, cylinderLineTranslation_apply]
    rfl
  intro t ht x s v w a b
  change (UniversalCover.liftedMetric (I := I) (g t)).inner (Psi (x, s + c))
    (mfderiv CylinderI I ((cylinderLineTranslation c).trans Psi) (x, s) (v, a))
    (mfderiv CylinderI I ((cylinderLineTranslation c).trans Psi) (x, s) (w, b)) = _
  rw [hderiv, hderiv]
  exact hproduct t ht x (s + c) v w a b

omit [IsManifold I ∞ M] in
theorem cylinderDeck_recenter_fibres
    (Psi : (SphereTwo × ℝ) ≃ₘ⟮CylinderI, I⟯ UniversalCover M) (c : ℝ)
    (hfibres : ∀ p q : SphereTwo × ℝ,
      UniversalCover.proj (Psi p) = UniversalCover.proj (Psi q) ↔
        q = p ∨ q = (antipodal p.1, 2 * c - p.2)) :
    ∀ p q : SphereTwo × ℝ,
      UniversalCover.proj (((cylinderLineTranslation c).trans Psi) p) =
        UniversalCover.proj (((cylinderLineTranslation c).trans Psi) q) ↔
          q = p ∨ q = (antipodal p.1, -p.2) := by
  intro p q
  change UniversalCover.proj (Psi (p.1, p.2 + c)) =
    UniversalCover.proj (Psi (q.1, q.2 + c)) ↔ _
  rw [hfibres]
  constructor
  · rintro (h | h)
    · left
      apply Prod.ext
      · simpa only using congrArg (fun z : SphereTwo × ℝ => z.1) h
      · have hs := congrArg (fun z : SphereTwo × ℝ => z.2) h
        change q.2 + c = p.2 + c at hs
        linarith
    · right
      apply Prod.ext
      · simpa only using congrArg (fun z : SphereTwo × ℝ => z.1) h
      · have hs := congrArg (fun z : SphereTwo × ℝ => z.2) h
        change q.2 + c = 2 * c - (p.2 + c) at hs
        change q.2 = -p.2
        linarith
  · rintro (h | h)
    · subst q
      exact Or.inl rfl
    · right
      rw [h]
      apply Prod.ext
      · rfl
      · change -p.2 + c = 2 * c - (p.2 + c)
        ring

omit [IsManifold I ∞ M] in
theorem cylinderDeck_recenter_surjective
    (Psi : (SphereTwo × ℝ) ≃ₘ⟮CylinderI, I⟯ UniversalCover M)
    (hsurjective : Function.Surjective
      (fun p : SphereTwo × ℝ => UniversalCover.proj (Psi p))) (c : ℝ) :
    Function.Surjective (fun p : SphereTwo × ℝ =>
      UniversalCover.proj (((cylinderLineTranslation c).trans Psi) p)) :=
  hsurjective.comp (cylinderLineTranslation c).surjective

end FixedCover

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
