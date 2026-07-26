import DifferentialGeometry.Geometry.Coordinates.LocalDiffeoIFT
import DifferentialGeometry.Geometry.Exponential.ConjugatePoint

set_option autoImplicit false

/-!
# Fixed-first inverse branches of the intrinsic exponential

This file packages one smooth local inverse branch of the intrinsic
exponential with a fixed base point.  It is the canonical branch object for
fixed-metric radial calculations at a possibly nonzero launch vector.

No injectivity radius or quantitative source radius is stored in the object.
Those bounds belong to the producer that selects a branch for a geometric
application.
-/

noncomputable section

open Bundle Function Manifold Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Exponential

section ChartDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

/-- Passing a map from the model space through the centered target chart does
not change its derivative. -/
theorem hasFDerivAt_chart
    {f : E → M} {u : E}
    (hf : MDifferentiableAt 𝓘(Real, E) I f u) :
    HasFDerivAt
      ((extChartAt I (f u)) ∘ f)
      (mfderiv 𝓘(Real, E) I f u)
      u := by
  have hf' : HasMFDerivAt 𝓘(Real, E) I f u
      (mfderiv 𝓘(Real, E) I f u) :=
    hf.hasMFDerivAt
  have hchart : HasMFDerivAt I 𝓘(Real, E) (extChartAt I (f u)) (f u)
      (ContinuousLinearMap.id Real E) := by
    have h :=
      (mdifferentiableAt_extChartAt (I := I)
        (mem_chart_source H (f u))).hasMFDerivAt
    rw [mfderiv_extChartAt_self (I := I) (x := f u)] at h
    exact h
  have hcomp : HasMFDerivAt 𝓘(Real, E) 𝓘(Real, E)
      ((extChartAt I (f u)) ∘ f) u
      ((ContinuousLinearMap.id Real E).comp
        (mfderiv 𝓘(Real, E) I f u)) :=
    hchart.comp u hf'
  rw [ContinuousLinearMap.id_comp] at hcomp
  exact hasMFDerivAt_iff_hasFDerivAt.mp hcomp

private theorem written_fderiv_inv
    {f : E → M} {u : E}
    (hf : MDifferentiableAt 𝓘(Real, E) I f u)
    (hinv : (mfderiv 𝓘(Real, E) I f u).IsInvertible) :
    (fderiv Real
      (writtenInExtChartAt 𝓘(Real, E) I u f)
      (extChartAt 𝓘(Real, E) u u)).IsInvertible := by
  have hchart := hasFDerivAt_chart (I := I) hf
  have hwritten : HasFDerivAt
      (writtenInExtChartAt 𝓘(Real, E) I u f)
      (mfderiv 𝓘(Real, E) I f u)
      (extChartAt 𝓘(Real, E) u u) := by
    simpa only [writtenInExtChartAt, extChartAt_self_eq,
      modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
      Function.comp_apply, id_eq] using hchart
  rw [hwritten.fderiv]
  exact hinv

end ChartDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
variable [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

/-- A selected smooth local inverse branch of the intrinsic exponential with
fixed base point `p`.

The forward map is stored as a `C∞` partial diffeomorphism and is required to
agree with the intrinsic exponential on its open source. -/
structure ExpInvBranch
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) where
  hom : PartialDiffeomorph 𝓘(Real, E) I E M ∞
  hom_eq :
    EqOn
      (fun u : E =>
        expMapIntrinsic (I := I) g hEnorm p
          (show TangentSpace I p from u))
      hom
      hom.source

namespace ExpInvBranch

/-- The totalized inverse selected by a fixed-first exponential branch. -/
def inv
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {p : M} (B : ExpInvBranch (I := I) g hEnorm p) : M → E :=
  B.hom.symm

/-- The target domain on which the selected inverse laws hold. -/
def dom
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {p : M} (B : ExpInvBranch (I := I) g hEnorm p) : Set M :=
  B.hom.target

/-- The selected branch is a right inverse of the intrinsic exponential on
its target. -/
theorem right_inv
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {p : M} (B : ExpInvBranch (I := I) g hEnorm p)
    {y : M} (hy : y ∈ B.dom) :
    expMapIntrinsic (I := I) g hEnorm p
        (show TangentSpace I p from B.inv y) = y := by
  have hu : B.inv y ∈ B.hom.source := B.hom.map_target hy
  calc
    expMapIntrinsic (I := I) g hEnorm p
        (show TangentSpace I p from B.inv y) =
      B.hom (B.inv y) := B.hom_eq hu
    _ = y := by simpa only [inv] using B.hom.right_inv hy

/-- The selected branch is a left inverse of the intrinsic exponential on
its source. -/
theorem left_inv
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {p : M} (B : ExpInvBranch (I := I) g hEnorm p)
    {u : E} (hu : u ∈ B.hom.source) :
    B.inv
        (expMapIntrinsic (I := I) g hEnorm p
          (show TangentSpace I p from u)) = u := by
  calc
    B.inv
        (expMapIntrinsic (I := I) g hEnorm p
          (show TangentSpace I p from u)) =
      B.inv (B.hom u) := congrArg B.inv (B.hom_eq hu)
    _ = u := by simpa only [inv] using B.hom.left_inv hu

/-- The selected fixed-first inverse is smooth on its target. -/
theorem inv_inf
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {p : M} (B : ExpInvBranch (I := I) g hEnorm p) :
    ContMDiffOn I 𝓘(Real, E) ∞ B.inv B.dom := by
  simpa only [inv, dom] using B.hom.symm.contMDiffOn_toFun

end ExpInvBranch

private theorem branch_of_inj
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {p : M} {u : E}
    (hu : Function.Injective
      (mfderiv 𝓘(Real, E) I
        (fun z : E =>
          expMapIntrinsic (I := I) g hEnorm p
            (show TangentSpace I p from z))
        u)) :
    ∃ B : ExpInvBranch (I := I) g hEnorm p, u ∈ B.hom.source := by
  classical
  let f : E → M := fun z : E =>
    expMapIntrinsic (I := I) g hEnorm p
      (show TangentSpace I p from z)
  have hf : ContMDiff 𝓘(Real, E) I ∞ f :=
    intrinsicFiber_smooth (I := I) g hEnorm p
  have hDsurj : Function.Surjective (mfderiv 𝓘(Real, E) I f u) :=
    LinearMap.surjective_of_injective hu
  let D : E ≃L[Real] E :=
    ContinuousLinearEquiv.ofBijective (mfderiv 𝓘(Real, E) I f u)
      (LinearMap.ker_eq_bot.mpr hu)
      (LinearMap.range_eq_top.mpr hDsurj)
  have hDinv : (mfderiv 𝓘(Real, E) I f u).IsInvertible := by
    refine ⟨D, ?_⟩
    rfl
  have hfu : MDifferentiableAt 𝓘(Real, E) I f u :=
    hf.contMDiffAt.mdifferentiableAt (by simp)
  have hfd_u : (fderiv Real
      (writtenInExtChartAt 𝓘(Real, E) I u f)
      (extChartAt 𝓘(Real, E) u u)).IsInvertible :=
    written_fderiv_inv (I := I) hfu hDinv
  have hf1 : ContMDiffAt 𝓘(Real, E) I 1 f u :=
    hf.contMDiffAt.of_le (by exact_mod_cast le_top)
  obtain ⟨Ψ, huΨ, hEqΨ⟩ :=
    Coordinates.contMDiffAt_isLocalDiffeomorphAt
      (I := 𝓘(Real, E)) (J := I)
      (n := 1) le_rfl
      (by exact_mod_cast (WithTop.one_ne_top : (1 : ℕ∞) ≠ ⊤))
      hf1 hfd_u
  have hinv_source : ∀ z ∈ Ψ.source,
      (fderiv Real
        (writtenInExtChartAt 𝓘(Real, E) I z f)
        (extChartAt 𝓘(Real, E) z z)).IsInvertible := by
    intro z hz
    have hloc : IsLocalDiffeomorphAt 𝓘(Real, E) I 1 f z :=
      ⟨Ψ, hz, hEqΨ⟩
    have hDzinv : (mfderiv 𝓘(Real, E) I f z).IsInvertible :=
      ⟨hloc.mfderivToContinuousLinearEquiv one_ne_zero,
        hloc.mfderivToContinuousLinearEquiv_coe one_ne_zero⟩
    exact written_fderiv_inv (I := I)
      (hf.contMDiffAt.mdifferentiableAt (by simp)) hDzinv
  obtain ⟨Φ, huΦ, -, hEqΦ⟩ :=
    Coordinates.hlocAt_infty' (I := 𝓘(Real, E)) (J := I)
      Ψ.open_source huΨ hf.contMDiffOn hinv_source
  exact ⟨⟨Φ, hEqΦ⟩, huΦ⟩

/-- A nonconjugate launch vector admits a selected smooth fixed-first inverse
branch of the intrinsic exponential. -/
theorem branch_of_not_conj
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {p : M} {u : TangentSpace I p}
    (hu : ¬ IsConjVec (I := I) g hEnorm p (u : E)) :
    ∃ B : ExpInvBranch (I := I) g hEnorm p,
      (u : E) ∈ B.hom.source := by
  classical
  apply branch_of_inj (I := I) g hEnorm
  simpa only [IsConjVec, not_not] using hu

namespace ExpInvBranch

/-- Every vector in the source of a selected fixed-first branch is
nonconjugate. -/
theorem not_conj
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {p : M} (B : ExpInvBranch (I := I) g hEnorm p)
    {u : TangentSpace I p}
    (hu : (u : E) ∈ B.hom.source) :
    ¬ IsConjVec (I := I) g hEnorm p (u : E) := by
  classical
  let f : E → M := fun z : E =>
    expMapIntrinsic (I := I) g hEnorm p
      (show TangentSpace I p from z)
  have hloc : IsLocalDiffeomorphAt 𝓘(Real, E) I ∞ f (u : E) :=
    ⟨B.hom, hu, B.hom_eq⟩
  have hinj : Function.Injective (mfderiv 𝓘(Real, E) I f (u : E)) :=
    (hloc.mfderivToContinuousLinearEquiv (by simp)).injective
  simpa only [IsConjVec, f, not_not] using hinj

end ExpInvBranch

end Exponential
end Riemannian
end Geometry
end DifferentialGeometry
