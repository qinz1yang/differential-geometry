import DifferentialGeometry.Geometry.Metric.Sphere.Isometry.OrthogonalAction
import DifferentialGeometry.Geometry.Metric.Construction.SmoothMetricFromCoefficients
import DifferentialGeometry.Geometry.Metric.Construction.BumpExtension
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Opens
import DifferentialGeometry.Topology.SigmaCompactOpen
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.Local
import DifferentialGeometry.Geometry.Curvature.Sphere.ConstCurvature

open DifferentialGeometry.Geometry.Curvature


noncomputable section

open Bundle Manifold Set Metric Module
open scoped Manifold Topology ContDiff RealInnerProductSpace

namespace DifferentialGeometry
namespace Geometry

universe uE uQ

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {n : ℕ} [Fact (finrank ℝ E = n + 1)] [NeZero n]

structure LocalSmoothSection (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (n : ℕ) [Fact (finrank ℝ E = n + 1)] [NeZero n]
    (Q : Type*) [TopologicalSpace Q] [ChartedSpace (EuclideanSpace ℝ (Fin n)) Q]
    [IsManifold (𝓡 n) ∞ Q]
    (proj : sphere (0 : E) 1 → Q) (x : Q) where
  baseNeighborhood : TopologicalSpace.Opens Q
  sphereNeighborhood : TopologicalSpace.Opens (sphere (0 : E) 1)
  [baseSigmaCompact : SigmaCompactSpace baseNeighborhood]
  [baseT2 : T2Space baseNeighborhood]
  [baseBoundaryless : BoundarylessManifold (𝓡 n) baseNeighborhood]
  [baseManifoldOne : IsManifold (𝓡 n) 1 baseNeighborhood]
  [baseManifoldTop : IsManifold (𝓡 n) ((∞ : WithTop ℕ∞) + 1) baseNeighborhood]
  [sphereSigmaCompact : SigmaCompactSpace sphereNeighborhood]
  [sphereT2 : T2Space sphereNeighborhood]
  [sphereBoundaryless : BoundarylessManifold (𝓡 n) sphereNeighborhood]
  [sphereManifoldOne : IsManifold (𝓡 n) 1 sphereNeighborhood]
  [sphereManifoldTop : IsManifold (𝓡 n) ((∞ : WithTop ℕ∞) + 1) sphereNeighborhood]
  localSection : baseNeighborhood ≃ₘ⟮𝓡 n, 𝓡 n⟯ sphereNeighborhood
  mem_baseNeighborhood : x ∈ baseNeighborhood
  proj_localSection : ∀ r : baseNeighborhood,
    proj ((localSection r : sphereNeighborhood) : sphere (0 : E) 1) = (r : Q)

structure RoundSphereQuotient (E : Type uE) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (n : ℕ) [Fact (finrank ℝ E = n + 1)] [NeZero n] where
  Q : Type uQ
  [topos : TopologicalSpace Q]
  [charted : ChartedSpace (EuclideanSpace ℝ (Fin n)) Q]
  [mfld : IsManifold (𝓡 n) ∞ Q]
  [mfld1 : IsManifold (𝓡 n) 1 Q]
  [mfldTop : IsManifold (𝓡 n) ((∞ : WithTop ℕ∞) + 1) Q]
  [t2 : T2Space Q]
  [sigmaCompact : SigmaCompactSpace Q]
  [boundaryless : BoundarylessManifold (𝓡 n) Q]
  Γ : Type uQ
  [grp : Group Γ]
  [fin : Fintype Γ]
  ρ : Γ →* (E ≃ₗᵢ[ℝ] E)
  proj : sphere (0 : E) 1 → Q
  proj_smooth : ContMDiff (𝓡 n) (𝓡 n) ∞ proj
  proj_smul : ∀ (γ : Γ) (q : sphere (0 : E) 1),
    proj (sphereDiffeo (n := n) (ρ γ) q) = proj q
  proj_eq_imp : ∀ q₁ q₂ : sphere (0 : E) 1,
    proj q₁ = proj q₂ → ∃ γ : Γ, sphereDiffeo (n := n) (ρ γ) q₁ = q₂
  sectionAt : ∀ x : Q, LocalSmoothSection E n Q proj x

attribute [instance] RoundSphereQuotient.topos RoundSphereQuotient.charted RoundSphereQuotient.mfld
  RoundSphereQuotient.mfld1 RoundSphereQuotient.mfldTop RoundSphereQuotient.t2
  RoundSphereQuotient.sigmaCompact RoundSphereQuotient.boundaryless RoundSphereQuotient.grp
  RoundSphereQuotient.fin
  LocalSmoothSection.baseSigmaCompact LocalSmoothSection.baseT2
  LocalSmoothSection.baseBoundaryless LocalSmoothSection.baseManifoldOne
  LocalSmoothSection.baseManifoldTop LocalSmoothSection.sphereSigmaCompact
  LocalSmoothSection.sphereT2 LocalSmoothSection.sphereBoundaryless
  LocalSmoothSection.sphereManifoldOne LocalSmoothSection.sphereManifoldTop

private noncomputable def tangentOpenEquiv
    {Q : Type*} [TopologicalSpace Q] [ChartedSpace (EuclideanSpace ℝ (Fin n)) Q]
    (U : TopologicalSpace.Opens Q) (x : U) :
    TangentSpace (𝓡 n) (x : Q) ≃L[ℝ] TangentSpace (𝓡 n) x :=
  (tangentSpaceModelContinuousLinearEquiv (I := 𝓡 n) (x : Q)).trans
    (tangentSpaceModelContinuousLinearEquiv (I := 𝓡 n) x).symm

omit [NeZero n] in
private theorem mfderiv_subtype_val_tangentOpenEquiv
    {Q : Type*} [TopologicalSpace Q] [ChartedSpace (EuclideanSpace ℝ (Fin n)) Q]
    (U : TopologicalSpace.Opens Q) (x : U) (v : TangentSpace (𝓡 n) (x : Q)) :
    mfderiv (𝓡 n) (𝓡 n) (Subtype.val : U → Q) x (tangentOpenEquiv U x v) = v := by
  rw [mfderiv_subtype_val_apply]
  apply (tangentSpaceModelContinuousLinearEquiv (I := 𝓡 n) (x : Q)).injective
  change tangentSpaceModelContinuousLinearEquiv (I := 𝓡 n) (x : Q)
      ((tangentSpaceModelContinuousLinearEquiv (I := 𝓡 n) x).symm
        (tangentSpaceModelContinuousLinearEquiv (I := 𝓡 n) (x : Q) v)) =
    tangentSpaceModelContinuousLinearEquiv (I := 𝓡 n) (x : Q) v
  rw [tangentSpaceModelContinuousLinearEquiv_symm_apply]
  exact tangentSpaceModelContinuousLinearEquiv_apply (I := 𝓡 n) (x : Q) v

omit [NeZero n] in
private theorem tangentOpenEquiv_mfderiv_subtype_val
    {Q : Type*} [TopologicalSpace Q] [ChartedSpace (EuclideanSpace ℝ (Fin n)) Q]
    (U : TopologicalSpace.Opens Q) (x : U) (v : TangentSpace (𝓡 n) x) :
    tangentOpenEquiv U x (mfderiv (𝓡 n) (𝓡 n) (Subtype.val : U → Q) x v) = v := by
  rw [mfderiv_subtype_val_apply]
  apply (tangentSpaceModelContinuousLinearEquiv (I := 𝓡 n) x).injective
  change tangentSpaceModelContinuousLinearEquiv (I := 𝓡 n) x
      ((tangentSpaceModelContinuousLinearEquiv (I := 𝓡 n) x).symm
        (tangentSpaceModelContinuousLinearEquiv (I := 𝓡 n) (x : Q) v)) =
    tangentSpaceModelContinuousLinearEquiv (I := 𝓡 n) x v
  rw [tangentSpaceModelContinuousLinearEquiv_symm_apply]
  exact (tangentSpaceModelContinuousLinearEquiv_apply (I := 𝓡 n) (x : Q) v).trans
    (tangentSpaceModelContinuousLinearEquiv_apply (I := 𝓡 n) x v).symm

namespace LocalSmoothSection

variable {Q : Type*} [TopologicalSpace Q] [ChartedSpace (EuclideanSpace ℝ (Fin n)) Q]
  [IsManifold (𝓡 n) ∞ Q] {proj : sphere (0 : E) 1 → Q} {x₀ : Q}
  (S : LocalSmoothSection E n Q proj x₀)

noncomputable def ofLocal
    [SigmaCompactSpace Q] [T2Space Q] [BoundarylessManifold (𝓡 n) Q]
    (hsurj : Function.Surjective proj)
    (hloc : IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ proj)
    (x : Q) : LocalSmoothSection E n Q proj x := by
  let q := Classical.choose (hsurj x)
  have hqx : proj q = x := Classical.choose_spec (hsurj x)
  let Φ := Classical.choose (hloc q)
  have hq : q ∈ Φ.source := (Classical.choose_spec (hloc q)).1
  have hΦ : Set.EqOn proj Φ Φ.source := (Classical.choose_spec (hloc q)).2
  let V : TopologicalSpace.Opens (sphere (0 : E) 1) :=
    ⟨Φ.source, Φ.open_source⟩
  let W : TopologicalSpace.Opens Q :=
    ⟨(Φ : sphere (0 : E) 1 → Q) '' (V : Set (sphere (0 : E) 1)),
      image_opens_isOpen Φ (by exact Subset.rfl)⟩
  letI : SigmaCompactSpace V :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen (𝓡 n) V.2)
  letI : SigmaCompactSpace W :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen (𝓡 n) W.2)
  let e : V ≃ₘ⟮𝓡 n, 𝓡 n⟯ W :=
    PartialDiffeomorph.toOpensDiffeo Φ (by exact Subset.rfl)
  refine
    { baseNeighborhood := W
      sphereNeighborhood := V
      localSection := e.symm
      mem_baseNeighborhood := ?_
      proj_localSection := ?_ }
  · exact ⟨q, hq, (hΦ hq).symm.trans hqx⟩
  · intro r
    have hvr : ((e.symm r : V) : sphere (0 : E) 1) ∈ Φ.source :=
      (e.symm r).2
    calc
      proj ((e.symm r : V) : sphere (0 : E) 1) =
          Φ ((e.symm r : V) : sphere (0 : E) 1) := hΦ hvr
      _ = (r : Q) := by
        exact congrArg Subtype.val (e.apply_symm_apply r)

def toSphere : S.baseNeighborhood → sphere (0 : E) 1 := fun r => ((S.localSection r : S.sphereNeighborhood) : sphere (0 : E) 1)

theorem toSphere_proj (r : S.baseNeighborhood) : proj (S.toSphere r) = (r : Q) := S.proj_localSection r

theorem toSphere_contMDiff : ContMDiff (𝓡 n) (𝓡 n) ∞ S.toSphere := by
  have h : ContMDiff (𝓡 n) (𝓡 n) ∞
      ((Subtype.val : S.sphereNeighborhood → sphere (0 : E) 1) ∘ (S.localSection : S.baseNeighborhood → S.sphereNeighborhood)) :=
    (contMDiff_subtype_val (I := 𝓡 n)).comp S.localSection.contMDiff
  exact h

theorem mfderiv_toSphere_apply (r : S.baseNeighborhood) (v : TangentSpace (𝓡 n) r) :
    mfderiv (𝓡 n) (𝓡 n) S.toSphere r v = mfderiv (𝓡 n) (𝓡 n) S.localSection r v := by
  have hval : MDifferentiableAt (𝓡 n) (𝓡 n)
      (Subtype.val : S.sphereNeighborhood → sphere (0 : E) 1) (S.localSection r) :=
    (contMDiff_subtype_val (I := 𝓡 n)).mdifferentiableAt (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have hs : MDifferentiableAt (𝓡 n) (𝓡 n) (S.localSection : S.baseNeighborhood → S.sphereNeighborhood) r :=
    S.localSection.contMDiff.mdifferentiableAt (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have hcomp : S.toSphere = (Subtype.val : S.sphereNeighborhood → sphere (0 : E) 1) ∘ (S.localSection : S.baseNeighborhood → S.sphereNeighborhood) := rfl
  rw [hcomp, mfderiv_comp_apply r hval hs v, mfderiv_subtype_val_apply]

theorem pullback_inner_eval {x : Q} (hx : x ∈ S.baseNeighborhood)
    (v w : TangentSpace (𝓡 n) (⟨x, hx⟩ : S.baseNeighborhood)) :
    (Diffeomorph.pullbackMetric
        ((roundMetric (E := E) (n := n)).restrictOpen S.sphereNeighborhood) S.localSection).inner ⟨x, hx⟩ v w
      = roundInner (n := n) (S.toSphere ⟨x, hx⟩)
          (mfderiv (𝓡 n) (𝓡 n) S.toSphere ⟨x, hx⟩ v)
          (mfderiv (𝓡 n) (𝓡 n) S.toSphere ⟨x, hx⟩ w) := by
  rw [Diffeomorph.pullbackMetric_inner, SmoothRiemannianMetric.restrictOpen_inner,
    mfderiv_toSphere_apply, mfderiv_toSphere_apply]
  rfl

theorem dproj_sec (hproj : ContMDiff (𝓡 n) (𝓡 n) ∞ proj) (r : S.baseNeighborhood) :
    (mfderiv (𝓡 n) (𝓡 n) proj (S.toSphere r)).comp (mfderiv (𝓡 n) (𝓡 n) S.toSphere r)
      = mfderiv (𝓡 n) (𝓡 n) (Subtype.val : S.baseNeighborhood → Q) r := by
  have hp : MDifferentiableAt (𝓡 n) (𝓡 n) proj (S.toSphere r) :=
    hproj.mdifferentiableAt (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have hts : MDifferentiableAt (𝓡 n) (𝓡 n) S.toSphere r :=
    S.toSphere_contMDiff.mdifferentiableAt (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have hpts : proj ∘ S.toSphere = (Subtype.val : S.baseNeighborhood → Q) := by
    funext r'; exact S.toSphere_proj r'
  have e1 : mfderiv (𝓡 n) (𝓡 n) (proj ∘ S.toSphere) r
      = (mfderiv (𝓡 n) (𝓡 n) proj (S.toSphere r)).comp
          (mfderiv (𝓡 n) (𝓡 n) S.toSphere r) := mfderiv_comp r hp hts
  rw [hpts] at e1
  exact e1.symm

theorem dproj_inj (hproj : ContMDiff (𝓡 n) (𝓡 n) ∞ proj) (r : S.baseNeighborhood) :
    Function.Injective (mfderiv (𝓡 n) (𝓡 n) proj (S.toSphere r)) := by
  have hcomp := S.dproj_sec hproj r
  have hsurj : Function.Surjective (mfderiv (𝓡 n) (𝓡 n) proj (S.toSphere r)) := by
    intro u
    let uW : TangentSpace (𝓡 n) r := tangentOpenEquiv S.baseNeighborhood r u
    refine ⟨mfderiv (𝓡 n) (𝓡 n) S.toSphere r uW, ?_⟩
    change ((mfderiv (𝓡 n) (𝓡 n) proj (S.toSphere r)).comp
      (mfderiv (𝓡 n) (𝓡 n) S.toSphere r)) uW = u
    rw [hcomp]
    exact mfderiv_subtype_val_tangentOpenEquiv S.baseNeighborhood r u
  have hlin : Function.Injective
      ((mfderiv (𝓡 n) (𝓡 n) proj (S.toSphere r)).toLinearMap :
        TangentSpace (𝓡 n) (S.toSphere r) →ₗ[ℝ] TangentSpace (𝓡 n) (r : Q)) :=
    LinearMap.injective_iff_surjective.mpr hsurj
  exact hlin

end LocalSmoothSection

namespace RoundSphereQuotient

variable (D : RoundSphereQuotient E n)

def gm (x : D.Q) : TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x →L[ℝ] ℝ :=
  let xW : (D.sectionAt x).baseNeighborhood := ⟨x, (D.sectionAt x).mem_baseNeighborhood⟩
  let e := (tangentOpenEquiv (D.sectionAt x).baseNeighborhood xW).toContinuousLinearMap
  let g := (Diffeomorph.pullbackMetric
    ((roundMetric (E := E) (n := n)).restrictOpen (D.sectionAt x).sphereNeighborhood)
    (D.sectionAt x).localSection).inner xW
  ((ContinuousLinearMap.compL ℝ (TangentSpace (𝓡 n) x)
    (TangentSpace (𝓡 n) xW) ℝ).flip e).comp (g.comp e)

theorem gm_apply (x : D.Q) (v w : TangentSpace (𝓡 n) x) :
    D.gm x v w =
      (Diffeomorph.pullbackMetric
        ((roundMetric (E := E) (n := n)).restrictOpen (D.sectionAt x).sphereNeighborhood)
        (D.sectionAt x).localSection).inner ⟨x, (D.sectionAt x).mem_baseNeighborhood⟩
          (tangentOpenEquiv (D.sectionAt x).baseNeighborhood ⟨x, (D.sectionAt x).mem_baseNeighborhood⟩ v)
          (tangentOpenEquiv (D.sectionAt x).baseNeighborhood ⟨x, (D.sectionAt x).mem_baseNeighborhood⟩ w) := by
  rfl

theorem gm_symm (x : D.Q) (v w : TangentSpace (𝓡 n) x) : D.gm x v w = D.gm x w v :=
  by
    rw [D.gm_apply, D.gm_apply]
    exact (Diffeomorph.pullbackMetric
      ((roundMetric (E := E) (n := n)).restrictOpen (D.sectionAt x).sphereNeighborhood)
      (D.sectionAt x).localSection).symm _ _ _

theorem gm_pos (x : D.Q) (v : TangentSpace (𝓡 n) x) (hv : v ≠ 0) : 0 < D.gm x v v := by
  rw [D.gm_apply]
  apply (Diffeomorph.pullbackMetric
    ((roundMetric (E := E) (n := n)).restrictOpen (D.sectionAt x).sphereNeighborhood)
    (D.sectionAt x).localSection).pos
  intro h
  apply hv
  exact (tangentOpenEquiv (D.sectionAt x).baseNeighborhood
    ⟨x, (D.sectionAt x).mem_baseNeighborhood⟩).injective (by simpa using h)

theorem sections_agree {x₁ x : D.Q} (hx : x ∈ (D.sectionAt x₁).baseNeighborhood) :
    ∃ γ : D.Γ,
      (D.sectionAt x₁).toSphere ⟨x, hx⟩
          = sphereDiffeo (n := n) (D.ρ γ)
              ((D.sectionAt x).toSphere ⟨x, (D.sectionAt x).mem_baseNeighborhood⟩)
      ∧ ∀ v : TangentSpace (𝓡 n) x,
          mfderiv (𝓡 n) (𝓡 n) (D.sectionAt x₁).toSphere ⟨x, hx⟩
              (tangentOpenEquiv (D.sectionAt x₁).baseNeighborhood ⟨x, hx⟩ v)
            = mfderiv (𝓡 n) (𝓡 n) (sphereDiffeo (n := n) (D.ρ γ))
                ((D.sectionAt x).toSphere ⟨x, (D.sectionAt x).mem_baseNeighborhood⟩)
                (mfderiv (𝓡 n) (𝓡 n) (D.sectionAt x).toSphere
                  ⟨x, (D.sectionAt x).mem_baseNeighborhood⟩
                  (tangentOpenEquiv (D.sectionAt x).baseNeighborhood
                    ⟨x, (D.sectionAt x).mem_baseNeighborhood⟩ v)) := by
  have h0 : (∞ : WithTop ℕ∞) ≠ 0 := by decide
  have hpq : D.proj ((D.sectionAt x).toSphere ⟨x, (D.sectionAt x).mem_baseNeighborhood⟩) = x :=
    (D.sectionAt x).toSphere_proj ⟨x, (D.sectionAt x).mem_baseNeighborhood⟩
  have hpq₁ : D.proj ((D.sectionAt x₁).toSphere ⟨x, hx⟩) = x :=
    (D.sectionAt x₁).toSphere_proj ⟨x, hx⟩
  obtain ⟨γ, hγ⟩ := D.proj_eq_imp _ _ (hpq.trans hpq₁.symm)
  refine ⟨γ, hγ.symm, fun v => ?_⟩
  apply (D.sectionAt x₁).dproj_inj D.proj_smooth ⟨x, hx⟩
  have hA1 := ContinuousLinearMap.ext_iff.mp
    ((D.sectionAt x₁).dproj_sec D.proj_smooth ⟨x, hx⟩)
      (tangentOpenEquiv (D.sectionAt x₁).baseNeighborhood ⟨x, hx⟩ v)
  simp only [ContinuousLinearMap.comp_apply] at hA1
  rw [hpq₁] at hA1
  rw [mfderiv_subtype_val_tangentOpenEquiv] at hA1
  have hφ : MDifferentiableAt (𝓡 n) (𝓡 n) (sphereDiffeo (n := n) (D.ρ γ))
      ((D.sectionAt x).toSphere ⟨x, (D.sectionAt x).mem_baseNeighborhood⟩) :=
    (sphereDiffeo (n := n) (D.ρ γ)).contMDiff.mdifferentiableAt h0
  have hp' : MDifferentiableAt (𝓡 n) (𝓡 n) D.proj
      (sphereDiffeo (n := n) (D.ρ γ)
        ((D.sectionAt x).toSphere ⟨x, (D.sectionAt x).mem_baseNeighborhood⟩)) :=
    D.proj_smooth.mdifferentiableAt h0
  have hA2 : mfderiv (𝓡 n) (𝓡 n) D.proj ((D.sectionAt x₁).toSphere ⟨x, hx⟩)
      (mfderiv (𝓡 n) (𝓡 n) (sphereDiffeo (n := n) (D.ρ γ))
        ((D.sectionAt x).toSphere ⟨x, (D.sectionAt x).mem_baseNeighborhood⟩)
        (mfderiv (𝓡 n) (𝓡 n) (D.sectionAt x).toSphere
          ⟨x, (D.sectionAt x).mem_baseNeighborhood⟩
          (tangentOpenEquiv (D.sectionAt x).baseNeighborhood
            ⟨x, (D.sectionAt x).mem_baseNeighborhood⟩ v))) = v := by
    rw [← hγ, ← mfderiv_comp_apply _ hp' hφ,
      show D.proj ∘ ⇑(sphereDiffeo (n := n) (D.ρ γ)) = D.proj from by
        funext y; exact D.proj_smul γ y]
    have hsx := ContinuousLinearMap.ext_iff.mp
      ((D.sectionAt x).dproj_sec D.proj_smooth ⟨x, (D.sectionAt x).mem_baseNeighborhood⟩)
        (tangentOpenEquiv (D.sectionAt x).baseNeighborhood
          ⟨x, (D.sectionAt x).mem_baseNeighborhood⟩ v)
    simp only [ContinuousLinearMap.comp_apply] at hsx
    rw [hpq] at hsx
    rw [mfderiv_subtype_val_tangentOpenEquiv] at hsx
    exact hsx
  exact hA1.trans hA2.symm

theorem gm_locallyEq {x₁ x : D.Q} (hx : x ∈ (D.sectionAt x₁).baseNeighborhood)
    (v w : TangentSpace (𝓡 n) x) :
    D.gm x v w = (Diffeomorph.pullbackMetric
        ((roundMetric (E := E) (n := n)).restrictOpen (D.sectionAt x₁).sphereNeighborhood)
        (D.sectionAt x₁).localSection).inner ⟨x, hx⟩
          (tangentOpenEquiv (D.sectionAt x₁).baseNeighborhood ⟨x, hx⟩ v)
          (tangentOpenEquiv (D.sectionAt x₁).baseNeighborhood ⟨x, hx⟩ w) := by
  rw [D.gm_apply,
    (D.sectionAt x).pullback_inner_eval (D.sectionAt x).mem_baseNeighborhood
      (tangentOpenEquiv (D.sectionAt x).baseNeighborhood ⟨x, (D.sectionAt x).mem_baseNeighborhood⟩ v)
      (tangentOpenEquiv (D.sectionAt x).baseNeighborhood ⟨x, (D.sectionAt x).mem_baseNeighborhood⟩ w),
    (D.sectionAt x₁).pullback_inner_eval hx
      (tangentOpenEquiv (D.sectionAt x₁).baseNeighborhood ⟨x, hx⟩ v)
      (tangentOpenEquiv (D.sectionAt x₁).baseNeighborhood ⟨x, hx⟩ w)]
  obtain ⟨γ, hq₁, hd⟩ := D.sections_agree hx
  rw [hd v, hd w, hq₁, roundInner_sphereDiffeo]

theorem gm_coeff (x₀ : D.Q) (i j : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))) :
    ContMDiffOn (𝓡 n) 𝓘(ℝ) ∞
      (fun x => D.gm x (frameVec (I := 𝓡 n) x₀ i x) (frameVec (I := 𝓡 n) x₀ j x))
      (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x₀).baseSet := by
  intro x₁ hx₁
  apply ContMDiffAt.contMDiffWithinAt
  refine (contMDiffAt_subtype_iff (U := (D.sectionAt x₁).baseNeighborhood)
    (x := ⟨x₁, (D.sectionAt x₁).mem_baseNeighborhood⟩)).mp ?_
  have hfun : (fun r : (D.sectionAt x₁).baseNeighborhood =>
        D.gm (↑r) (frameVec (I := 𝓡 n) x₀ i ↑r) (frameVec (I := 𝓡 n) x₀ j ↑r))
      = fun r : (D.sectionAt x₁).baseNeighborhood =>
        (Diffeomorph.pullbackMetric
          ((roundMetric (E := E) (n := n)).restrictOpen (D.sectionAt x₁).sphereNeighborhood)
          (D.sectionAt x₁).localSection).inner r
          (tangentOpenEquiv (D.sectionAt x₁).baseNeighborhood r (frameVec (I := 𝓡 n) x₀ i ↑r))
          (tangentOpenEquiv (D.sectionAt x₁).baseNeighborhood r (frameVec (I := 𝓡 n) x₀ j ↑r)) := by
    funext r
    exact D.gm_locallyEq r.2 _ _
  rw [hfun]
  exact CovariantDerivative.metric_inner_contMDiffAt
    (Diffeomorph.pullbackMetric
      ((roundMetric (E := E) (n := n)).restrictOpen (D.sectionAt x₁).sphereNeighborhood)
      (D.sectionAt x₁).localSection)
    (frameVec_sub_cmdiffAt (I := 𝓡 n) (D.sectionAt x₁).baseNeighborhood x₀ i hx₁ (D.sectionAt x₁).mem_baseNeighborhood)
    (frameVec_sub_cmdiffAt (I := 𝓡 n) (D.sectionAt x₁).baseNeighborhood x₀ j hx₁ (D.sectionAt x₁).mem_baseNeighborhood)
    (le_refl _)

def gQuot : SmoothRiemannianMetric (𝓡 n) D.Q :=
  (smoothMetric_of_localCoeff (I := 𝓡 n) D.gm D.gm_symm D.gm_pos D.gm_coeff).choose

theorem gQuot_inner (x : D.Q) (v w : TangentSpace (𝓡 n) x) :
    D.gQuot.inner x v w = D.gm x v w :=
  (smoothMetric_of_localCoeff (I := 𝓡 n) D.gm D.gm_symm D.gm_pos D.gm_coeff).choose_spec x v w

theorem gQuot_constPosSec :
    ∃ c : ℝ, 0 < c ∧ ∀ (x : D.Q) (X Y : TangentSpace (𝓡 n) x),
      metricRm04StandardAt (I := 𝓡 n) D.gQuot x X Y Y X =
        c * (D.gQuot.inner x X X * D.gQuot.inner x Y Y
          - D.gQuot.inner x X Y * D.gQuot.inner x X Y) := by
  refine ⟨1, one_pos, fun x X Y => ?_⟩
  have : NeZero (finrank ℝ (EuclideanSpace ℝ (Fin n))) := by
    rw [finrank_euclideanSpace_fin]; infer_instance
  set S := D.sectionAt x with hS
  let xW : S.baseNeighborhood := ⟨x, S.mem_baseNeighborhood⟩
  let XW : TangentSpace (𝓡 n) xW := tangentOpenEquiv S.baseNeighborhood xW X
  let YW : TangentSpace (𝓡 n) xW := tangentOpenEquiv S.baseNeighborhood xW Y
  have hXW : mfderiv (𝓡 n) (𝓡 n) (Subtype.val : S.baseNeighborhood → D.Q) xW XW = X :=
    mfderiv_subtype_val_tangentOpenEquiv S.baseNeighborhood xW X
  have hYW : mfderiv (𝓡 n) (𝓡 n) (Subtype.val : S.baseNeighborhood → D.Q) xW YW = Y :=
    mfderiv_subtype_val_tangentOpenEquiv S.baseNeighborhood xW Y
  have hB : metricRm04StandardAt (I := 𝓡 n) D.gQuot x X Y Y X
      = metricRm04StandardAt (I := 𝓡 n) (D.gQuot.restrictOpen S.baseNeighborhood) xW XW YW YW XW := by
    rw [metricRm04StandardAt_restrictOpen, hXW, hYW]
  have hmetric : D.gQuot.restrictOpen S.baseNeighborhood
      = Diffeomorph.pullbackMetric
          ((roundMetric (E := E) (n := n)).restrictOpen S.sphereNeighborhood) S.localSection := by
    apply SmoothRiemannianMetric.ext_inner
    intro r v w
    let vQ : TangentSpace (𝓡 n) (r : D.Q) :=
      mfderiv (𝓡 n) (𝓡 n) (Subtype.val : S.baseNeighborhood → D.Q) r v
    let wQ : TangentSpace (𝓡 n) (r : D.Q) :=
      mfderiv (𝓡 n) (𝓡 n) (Subtype.val : S.baseNeighborhood → D.Q) r w
    calc
      (D.gQuot.restrictOpen S.baseNeighborhood).inner r v w = D.gQuot.inner (r : D.Q) vQ wQ := by
        simpa only [vQ, wQ, mfderiv_subtype_val_apply] using!
          SmoothRiemannianMetric.restrictOpen_inner D.gQuot S.baseNeighborhood r v w
      _ = D.gm (r : D.Q) vQ wQ := D.gQuot_inner (r : D.Q) vQ wQ
      _ = (Diffeomorph.pullbackMetric
          ((roundMetric (E := E) (n := n)).restrictOpen S.sphereNeighborhood) S.localSection).inner r
            (tangentOpenEquiv S.baseNeighborhood r vQ) (tangentOpenEquiv S.baseNeighborhood r wQ) := by
        exact D.gm_locallyEq (x₁ := x) r.2 vQ wQ
      _ = (Diffeomorph.pullbackMetric
          ((roundMetric (E := E) (n := n)).restrictOpen S.sphereNeighborhood) S.localSection).inner r v w := by
        rw [show tangentOpenEquiv S.baseNeighborhood r vQ = v from by
              exact tangentOpenEquiv_mfderiv_subtype_val S.baseNeighborhood r v,
          show tangentOpenEquiv S.baseNeighborhood r wQ = w from by
              exact tangentOpenEquiv_mfderiv_subtype_val S.baseNeighborhood r w]
  have hC : metricRm04StandardAt (I := 𝓡 n)
        (Diffeomorph.pullbackMetric
          ((roundMetric (E := E) (n := n)).restrictOpen S.sphereNeighborhood) S.localSection) xW XW YW YW XW
      = metricRm04StandardAt (I := 𝓡 n) (roundMetric (E := E) (n := n)) (S.toSphere xW)
          (mfderiv (𝓡 n) (𝓡 n) S.toSphere xW XW)
          (mfderiv (𝓡 n) (𝓡 n) S.toSphere xW YW)
          (mfderiv (𝓡 n) (𝓡 n) S.toSphere xW YW)
          (mfderiv (𝓡 n) (𝓡 n) S.toSphere xW XW) := by
    rw [metricRm04StandardAt_pullback_localDiffeo (I := 𝓡 n) (roundMetric (E := E) (n := n))
        S.sphereNeighborhood S.baseNeighborhood S.localSection xW XW YW YW XW,
      S.mfderiv_toSphere_apply xW XW, S.mfderiv_toSphere_apply xW YW]
    rfl
  have hbridge : ∀ v w : TangentSpace (𝓡 n) x,
      (roundMetric (E := E) (n := n)).inner (S.toSphere xW)
          (mfderiv (𝓡 n) (𝓡 n) S.toSphere xW (tangentOpenEquiv S.baseNeighborhood xW v))
          (mfderiv (𝓡 n) (𝓡 n) S.toSphere xW (tangentOpenEquiv S.baseNeighborhood xW w))
        = D.gQuot.inner x v w := by
    intro v w
    rw [D.gQuot_inner, D.gm_apply]
    exact (S.pullback_inner_eval S.mem_baseNeighborhood
      (tangentOpenEquiv S.baseNeighborhood xW v) (tangentOpenEquiv S.baseNeighborhood xW w)).symm
  rw [hB, hmetric, hC,
    roundMetric_sec_value (S.toSphere xW)
      (mfderiv (𝓡 n) (𝓡 n) S.toSphere xW XW)
      (mfderiv (𝓡 n) (𝓡 n) S.toSphere xW YW),
    hbridge X X, hbridge Y Y, hbridge X Y, one_mul]

end RoundSphereQuotient

end Geometry
end DifferentialGeometry
