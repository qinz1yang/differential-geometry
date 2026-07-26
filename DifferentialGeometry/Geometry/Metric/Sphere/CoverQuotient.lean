import DifferentialGeometry.Geometry.Coordinates.LocalDiffeoOpen
import DifferentialGeometry.Geometry.Metric.Sphere.IsometryRepresentation
import DifferentialGeometry.Geometry.Metric.Sphere.QuotientDescent
import DifferentialGeometry.Geometry.Topology.UniversalCover.DeckIsometry
import DifferentialGeometry.Geometry.Topology.UniversalCover.FibreEquiv
import DifferentialGeometry.Geometry.Topology.UniversalCover.LocalDiffeomorph

/-!
# Round quotient data from a universal-cover isometry

This file packages a global isometry from the round sphere to the universal
cover of a standard-model manifold into the finite orthogonal quotient data
used by spherical metric descent.
-/

noncomputable section

open Bundle Function Manifold Metric Module
open scoped ContDiff Manifold RealInnerProductSpace Topology

namespace DifferentialGeometry
namespace Geometry

open Riemannian.Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {n : ℕ} [Fact (finrank ℝ E = n + 1)] [NeZero n]

/-- A global round isometry onto the universal cover realizes the base as a
finite quotient of the round sphere by ambient orthogonal transformations. -/
noncomputable def roundQuotientUC
    {Q : Type*} [TopologicalSpace Q]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) Q]
    [IsManifold (𝓡 n) ∞ Q] [T2Space Q] [SigmaCompactSpace Q]
    [BoundarylessManifold (𝓡 n) Q]
    [ConnectedSpace Q] [LocPathConnectedSpace Q]
    [Riemannian.Topology.SemilocallySimplyConnectedSpace Q] [Inhabited Q]
    (g : SmoothRiemannianMetric (𝓡 n) Q)
    (d : sphere (0 : E) 1 ≃ₘ⟮𝓡 n, 𝓡 n⟯ UniversalCover Q)
    (hd : ∀ x (v w : TangentSpace (𝓡 n) x),
      (UniversalCover.liftedMetric (I := 𝓡 n) g).inner (d x)
          (mfderiv (𝓡 n) (𝓡 n) d x v)
          (mfderiv (𝓡 n) (𝓡 n) d x w) =
        (roundMetric (E := E) (n := n)).inner x v w) :
    RoundQuotientData E n := by
  classical
  let φ (a : FundamentalGroup Q (default : Q)) :
      sphere (0 : E) 1 ≃ₘ⟮𝓡 n, 𝓡 n⟯ sphere (0 : E) 1 :=
    (d.trans (UniversalCover.deckDiffeo (I := 𝓡 n) a)).trans d.symm
  have hfr : 0 < finrank ℝ E := by
    rw [show finrank ℝ E = n + 1 from Fact.out]
    omega
  letI : Nontrivial E := Module.nontrivial_of_finrank_pos hfr
  let p : sphere (0 : E) 1 :=
    Classical.choice
      (NormedSpace.sphere_nonempty_rclike ℝ
        (E := E) (r := (1 : ℝ)) zero_le_one)
  have hone : ∀ x, φ 1 x = x := by
    intro x
    dsimp only [φ]
    change d.symm ((1 : FundamentalGroup Q (default : Q)) • d x) = x
    simp
  have hmul : ∀ a b x, φ (a * b) x = φ a (φ b x) := by
    intro a b x
    change d.symm ((a * b) • d x) =
      d.symm (a • d (d.symm (b • d x)))
    simp only [d.apply_symm_apply, mul_smul]
  have hiso : ∀ a x (v w : TangentSpace (𝓡 n) x),
      (roundMetric (E := E) (n := n)).inner x v w =
        (roundMetric (E := E) (n := n)).inner (φ a x)
          (mfderiv (𝓡 n) (𝓡 n) (φ a) x v)
          (mfderiv (𝓡 n) (𝓡 n) (φ a) x w) := by
    intro a x v w
    have hconj (z : sphere (0 : E) 1)
        (u : TangentSpace (𝓡 n) z) :
        mfderiv (𝓡 n) (𝓡 n) d (φ a z)
            (mfderiv (𝓡 n) (𝓡 n) (φ a) z u) =
          mfderiv (𝓡 n) (𝓡 n)
              (fun q : UniversalCover Q => a • q) (d z)
            (mfderiv (𝓡 n) (𝓡 n) d z u) := by
      have hfun :
          (d ∘ (φ a : sphere (0 : E) 1 → sphere (0 : E) 1)) =
            ((fun q : UniversalCover Q => a • q) ∘ d) := by
        funext y
        simp only [φ, Diffeomorph.coe_trans, Function.comp_apply,
          d.apply_symm_apply]
        rfl
      have hleft := mfderiv_comp_apply
        (g := (d : sphere (0 : E) 1 → UniversalCover Q))
        (f := (φ a : sphere (0 : E) 1 → sphere (0 : E) 1))
        (x := z)
        (d.contMDiff.mdifferentiableAt (by simp))
        ((φ a).contMDiff.mdifferentiableAt (by simp)) u
      rw [hfun] at hleft
      have hright := mfderiv_comp_apply
        (g := fun q : UniversalCover Q => a • q)
        (f := (d : sphere (0 : E) 1 → UniversalCover Q))
        (x := z)
        ((UniversalCover.deckDiffeo (I := 𝓡 n) a).contMDiff.mdifferentiableAt
          (by simp))
        (d.contMDiff.mdifferentiableAt (by simp)) u
      exact hleft.symm.trans hright
    have hbase : d (φ a x) = a • d x := by
      simp only [φ, Diffeomorph.coe_trans, Function.comp_apply,
        d.apply_symm_apply]
      rfl
    calc
      (roundMetric (E := E) (n := n)).inner x v w =
          (UniversalCover.liftedMetric (I := 𝓡 n) g).inner (d x)
            (mfderiv (𝓡 n) (𝓡 n) d x v)
            (mfderiv (𝓡 n) (𝓡 n) d x w) :=
        (hd x v w).symm
      _ = (UniversalCover.liftedMetric (I := 𝓡 n) g).inner (a • d x)
            (mfderiv (𝓡 n) (𝓡 n)
                (fun q : UniversalCover Q => a • q) (d x)
              (mfderiv (𝓡 n) (𝓡 n) d x v))
            (mfderiv (𝓡 n) (𝓡 n)
                (fun q : UniversalCover Q => a • q) (d x)
              (mfderiv (𝓡 n) (𝓡 n) d x w)) :=
        (UniversalCover.deck_inner (I := 𝓡 n) g a (d x)
          (mfderiv (𝓡 n) (𝓡 n) d x v)
          (mfderiv (𝓡 n) (𝓡 n) d x w)).symm
      _ = (UniversalCover.liftedMetric (I := 𝓡 n) g).inner (d (φ a x))
            (mfderiv (𝓡 n) (𝓡 n) d (φ a x)
              (mfderiv (𝓡 n) (𝓡 n) (φ a) x v))
            (mfderiv (𝓡 n) (𝓡 n) d (φ a x)
              (mfderiv (𝓡 n) (𝓡 n) (φ a) x w)) := by
        rw [hbase, ← hconj x v, ← hconj x w]
        rfl
      _ = (roundMetric (E := E) (n := n)).inner (φ a x)
            (mfderiv (𝓡 n) (𝓡 n) (φ a) x v)
            (mfderiv (𝓡 n) (𝓡 n) (φ a) x w) :=
        hd (φ a x)
          (mfderiv (𝓡 n) (𝓡 n) (φ a) x v)
          (mfderiv (𝓡 n) (𝓡 n) (φ a) x w)
  let ρ : FundamentalGroup Q (default : Q) →* (E ≃ₗᵢ[ℝ] E) :=
    Classical.choose
      (orth_rep_of_iso (E := E) (n := n) p φ
        (Nat.pos_of_ne_zero (NeZero.ne n)) hone hmul hiso)
  have hρ : ∀ a, sphereDiffeo (n := n) (ρ a) = φ a :=
    Classical.choose_spec
      (orth_rep_of_iso (E := E) (n := n) p φ
        (Nat.pos_of_ne_zero (NeZero.ne n)) hone hmul hiso)
  let proj : sphere (0 : E) 1 → Q := UniversalCover.proj ∘ d
  have hprojSurj :
      Function.Surjective (UniversalCover.proj : UniversalCover Q → Q) := by
    letI : PathConnectedSpace Q :=
      PathConnectedSpace.of_locPathConnectedSpace
    intro x
    let γ : Path (default : Q) x :=
      PathConnectedSpace.somePath default x
    exact ⟨⟨x, Path.Homotopic.Quotient.mk γ⟩, rfl⟩
  have hsurj : Function.Surjective proj :=
    hprojSurj.comp d.surjective
  have hloc :
      IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ proj := by
    exact hloc_comp (UniversalCover.proj_localDiffeo (I := 𝓡 n) (M := Q))
      d.isLocalDiffeomorph
  letI : CompactSpace (UniversalCover Q) := d.toHomeomorph.compactSpace
  letI : Finite (FundamentalGroup Q (default : Q)) :=
    UniversalCover.finite_pi1_of_uc
  letI : Fintype (FundamentalGroup Q (default : Q)) :=
    Fintype.ofFinite _
  letI : IsManifold (𝓡 n) 1 Q :=
    IsManifold.of_le (I := 𝓡 n) (M := Q) (n := (∞ : WithTop ℕ∞))
      (by simp)
  letI : IsManifold (𝓡 n) ((∞ : WithTop ℕ∞) + 1) Q := by
    simpa only [top_add] using (inferInstance : IsManifold (𝓡 n) ∞ Q)
  refine
    { Q := Q
      Γ := FundamentalGroup Q (default : Q)
      ρ := ρ
      proj := proj
      proj_smooth :=
        (UniversalCover.proj_contMDiff (I := 𝓡 n) (M := Q)).comp d.contMDiff
      proj_smul := ?_
      proj_eq_imp := ?_
      section_at := fun x => SectionWitness.ofLocal hsurj hloc x }
  · intro a x
    rw [hρ a]
    simp only [proj, Function.comp_apply]
    have hφbase : d (φ a x) = a • d x := by
      simp only [φ, Diffeomorph.coe_trans, Function.comp_apply,
        d.apply_symm_apply]
      rfl
    rw [hφbase]
    exact UniversalCover.proj_deckAct a (d x)
  · intro x y hxy
    have hdeck :
        ∃ a : FundamentalGroup Q (default : Q), a • d x = d y :=
      (UniversalCover.proj_eq_iff_smul (d x) (d y)).mp hxy
    obtain ⟨a, ha⟩ := hdeck
    refine ⟨a, ?_⟩
    rw [hρ a]
    apply d.injective
    simp only [φ, Diffeomorph.coe_trans, Function.comp_apply]
    change d (d.symm ((UniversalCover.deckDiffeo (I := 𝓡 n) a) (d x))) = d y
    rw [Diffeomorph.apply_symm_apply]
    change a • d x = d y
    exact ha

end Geometry
end DifferentialGeometry
