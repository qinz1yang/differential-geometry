import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FibrePlugSideDiffeomorph
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveSplitCappedCollarAdapterDisc

/-!
Actual positive collar compression removes the plug recognition width without changing its meridian.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Seifert
open DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold

private local instance meridianDiscCharts : ChartedSpace (EuclideanHalfSpace 2)
    (discPlanarBase.{u} 1).surface.Carrier :=
  inferInstanceAs (ChartedSpace (EuclideanHalfSpace 2) discSet.{u})

set_option backward.isDefEq.respectTransparency false in
theorem exists_solidCollarCompression {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ∃ R : solidSet.{u} ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ solidSet.{u},
      R.preservesOrientation (solidAtlas.orientation planeCircleOrientation)
        (solidAtlas.orientation planeCircleOrientation) ∧
      (∀ p : Torus, R (solidCollar 1 (p, halfZero)) = solidCollar 1 (p, halfZero)) ∧
      ∀ (p : Torus) (s : ℝ) (hs : 0 ≤ s), s < 1 →
        R (solidCollar 1 (p, halfPoint s hs)) =
          solidCollar 1 (p, halfPoint (ρ * s) (mul_nonneg hρ.le hs)) := by
  obtain ⟨D, hfix, hcollar⟩ := exists_discCollarCompression.{u} hρ hρ1
  let R : solidSet.{u} ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ solidSet.{u} :=
    (solidDiffeomorph.symm.trans
      (D.prodCongr (Diffeomorph.refl (𝓡 1) Circle ∞))).trans solidDiffeomorph
  let z : (discPlanarBase.{u} 1).surface.Carrier :=
    ⟨ULift.up 0, by rw [mem_discSet_iff]; norm_num⟩
  let x0 := solidDiffeomorph (z, (1 : Circle))
  let ν : solidSet.{u} → ℝ := fun x =>
    ‖(discPlanarBase.{u} 1).embedding (solidDiffeomorph.symm x).1‖
  have hν : Continuous ν := continuous_norm.comp
    ((discPlanarBase.{u} 1).isSmoothEmbedding.contMDiff.continuous.comp
      (continuous_fst.comp solidDiffeomorph.symm.continuous))
  have hx0 : ν x0 < 1 := by
    dsimp only [ν, x0]
    rw [solidDiffeomorph.symm_apply_apply]
    change ‖(0 : ℂ)‖ < 1
    norm_num
  have hg : (R : solidSet.{u} → solidSet.{u}) =ᶠ[𝓝 x0] id := by
    filter_upwards [(isOpen_lt hν continuous_const).mem_nhds hx0] with x hx
    change solidDiffeomorph (D (solidDiffeomorph.symm x).1,
      (solidDiffeomorph.symm x).2) = x
    rw [hfix _ hx.le]
    exact solidDiffeomorph.apply_symm_apply x
  have hpositive : R.preservesOrientation (solidAtlas.orientation planeCircleOrientation)
      (solidAtlas.orientation planeCircleOrientation) := by
    apply Diffeomorph.preservesOrientation_of_eq_at R _ _ x0
    have he0 : R x0 = x0 := hg.self_of_nhds
    have he : (R.mfderivToContinuousLinearEquiv (by simp) x0).toLinearEquiv =
        LinearEquiv.refl ℝ (TangentSpace (𝓡∂ 3) x0) := by
      apply LinearEquiv.ext
      intro v
      change mfderiv (𝓡∂ 3) (𝓡∂ 3) R x0 v = v
      rw [hg.mfderiv_eq, mfderiv_id]
      rfl
    rw [he, he0]
    exact congrArg (fun q => q ((solidAtlas.orientation planeCircleOrientation).orientation x0))
      (Orientation.map_refl (ι := Fin 3) (R := ℝ) (M := TangentSpace (𝓡∂ 3) x0))
  have hc : ∀ (p : Torus) (s : ℝ) (hs : 0 ≤ s), s < 1 →
      R (solidCollar 1 (p, halfPoint s hs)) =
        solidCollar 1 (p, halfPoint (ρ * s) (mul_nonneg hρ.le hs)) := by
    intro p s hs hs1
    change solidDiffeomorph (D ((discPlanarBase.{u} 1).collar 0
      (p.1, halfPoint s hs)), p.2) = _
    rw [hcollar p.1 s hs hs1]
    rfl
  refine ⟨R, hpositive, ?_, hc⟩
  intro p
  have hh := hc p 0 le_rfl (by norm_num)
  simpa only [mul_zero, halfZero, GC.Endpoint.halfPoint] using hh

end GC.GraphManifold

namespace GC.Seifert.ElementaryPresentation

open SplitTube

variable {W : CompactCarrier.{u}} (E : ElementaryPresentation W)
  {j : Fin E.toTorus.pairing.count} {b : Bool} (h : E.IsSplitSeam j b)
  (hlin : E.IsLinearSeam j)
  (d : PartialDiffeomorph sphereSignedCollarModel W.model
    (ClosureSphere.{u} × ℝ) W.Carrier ∞) (hs : d.source = sphereSignedCollarSource)
  (hI : d.target ⊆ W.interior)
  (heq : ∀ z s, d (z, s) = E.boundedSplitTubeMap h hlin (z.down, s))
  (hc : E.toTorus.components.count = 2) (hn : E.toTorus.pairing.count = 1)
  {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
  (havρ : ∀ r, Disjoint ((E.toTorus.external.shrink hρ hρ1).collar r).target d.target)

set_option backward.isDefEq.respectTransparency false in
theorem exists_boundedPlugMeridionalDiffeomorph (t : Bool) :
    ∃ (ε : Bool) (f : solidSet.{u} ≃ₘ⟮𝓡∂ 3,
      (E.fibrePlugCutBoundary d hs hρ hρ1 hI havρ).sphereCapCarrier.model⟯
        E.boundedPlugSideComponent h hlin d hs hI heq hc hn hρ hρ1 havρ t),
      f.preservesOrientation (solidAtlas.orientation planeCircleOrientation)
        ((E.fibrePlugCutBoundary d hs hρ hρ1 hI havρ).sphereCapCarrier.orientation.restrictOpen
          (E.boundedPlugSideComponent h hlin d hs hI heq hc hn hρ hρ1 havρ t)) ∧
      ∃ (σ : ℝ) (hσ : 0 < σ), σ ≤ 1 ∧
      (∀ (p : Torus) (s : ℝ) (hs0 : 0 ≤ s), s < σ →
        (f (solidCollar 1 (p, halfPoint s hs0))).val =
          (E.fibrePlugCutBoundary d hs hρ hρ1 hI havρ).sphereCapRetained.collar
            (E.fibrePlugSideExternalEquiv h hc hn t)
              (germHol ((E.boundedSplitCharts h hlin).e₀ * (E.boundedSplitCharts h hlin).d)
                (E.boundedSplitCharts h hlin).e₁ (E.boundedSplitCharts h hlin).he₁
                  (p.1, if ε then p.2⁻¹ else p.2), halfPoint s hs0)) ∧
      (∀ p ∈ halfCollarSource,
        (f (solidCollar 1 (p.1, halfSpaceScale hσ p.2))).val =
          (E.fibrePlugCutBoundary d hs hρ hρ1 hI havρ).sphereCapRetained.collar
            (E.fibrePlugSideExternalEquiv h hc hn t)
              (germHol ((E.boundedSplitCharts h hlin).e₀ * (E.boundedSplitCharts h hlin).d)
                (E.boundedSplitCharts h hlin).e₁ (E.boundedSplitCharts h hlin).he₁
                  (p.1.1, if ε then p.1.2⁻¹ else p.1.2), halfSpaceScale hσ p.2)) ∧
      ∀ θ : Circle,
        (f (solidCollar 1 ((θ, 1), halfZero))).val =
          (E.fibrePlugCutBoundary d hs hρ hρ1 hI havρ).sphereCapRetained.collar
            (E.fibrePlugSideExternalEquiv h hc hn t)
              ((1, θ ^ (E.boundedSplitCharts h hlin).e₁), halfZero) := by
  obtain ⟨ε, g, hgo, hgp, hgc⟩ :=
    E.exists_boundedPlugSidePositiveDiffeomorph h hlin d hs hI heq hc hn hρ hρ1 havρ t
  obtain ⟨R, hRo, hR0, hRc⟩ := GC.GraphManifold.exists_solidCollarCompression.{u} hρ hρ1
  let f := R.trans g
  let σ : ℝ := min (1 / 6) ((E.splitData h).δ / 2)
  have hσ : 0 < σ := lt_min (by norm_num) (half_pos (E.splitData h).hδ)
  have hσ1 : σ ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have hσ3 : σ < 1 / 3 := (min_le_left _ _).trans_lt (by norm_num)
  have hσδ : σ < (E.splitData h).δ := (min_le_right _ _).trans_lt
    (half_lt_self (E.splitData h).hδ)
  have hfc : ∀ (p : Torus) (s : ℝ) (hs0 : 0 ≤ s), s < σ →
      (f (solidCollar 1 (p, halfPoint s hs0))).val =
        (E.fibrePlugCutBoundary d hs hρ hρ1 hI havρ).sphereCapRetained.collar
          (E.fibrePlugSideExternalEquiv h hc hn t)
            (germHol ((E.boundedSplitCharts h hlin).e₀ * (E.boundedSplitCharts h hlin).d)
              (E.boundedSplitCharts h hlin).e₁ (E.boundedSplitCharts h hlin).he₁
                (p.1, if ε then p.2⁻¹ else p.2), halfPoint s hs0) := by
    intro p s hs0 hsσ
    have hs1 := hsσ.trans_le hσ1
    have hrs : ρ * s ≤ s := mul_le_of_le_one_left hs0 hρ1
    change (g (R (solidCollar 1 (p, halfPoint s hs0)))).val = _
    rw [hRc p s hs0 hs1]
    exact hgc p s hs0 hs1 (hrs.trans_lt (hsσ.trans hσ3))
      (hrs.trans_lt (hsσ.trans hσδ))
  refine ⟨ε, f, Diffeomorph.preservesOrientation_trans hRo hgo, σ, hσ, hσ1, hfc, ?_, ?_⟩
  · intro p hp
    have hsp := (halfSpaceScale hσ p.2).property
    have hsq : (halfSpaceScale hσ p.2).val 0 < σ := halfSpaceScale_lt hσ hp
    have hh := hfc p.1 ((halfSpaceScale hσ p.2).val 0) hsp hsq
    simpa only [halfPoint_coord] using hh
  intro θ
  have hh := hfc (θ, 1) 0 le_rfl hσ
  simpa only [ite_self, inv_one, germHol_apply, one_zpow, one_mul,
    halfZero, GC.Endpoint.halfPoint] using hh

end GC.Seifert.ElementaryPresentation
