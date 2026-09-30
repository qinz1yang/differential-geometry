import DifferentialGeometry.Topology.Manifold.SmoothOrientationPullback
import DifferentialGeometry.Topology.Manifold.OpenSubtype

set_option autoImplicit false
noncomputable section
open Set Function Manifold
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Topology.Manifold
variable {E F G H K L M N P : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [NormedAddCommGroup G] [NormedSpace ℝ G]
variable [TopologicalSpace H] [TopologicalSpace K] [TopologicalSpace L]
variable (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ F K) (C : ModelWithCorners ℝ G L)
variable [TopologicalSpace M] [ChartedSpace H M]
variable [TopologicalSpace N] [ChartedSpace K N]
variable [TopologicalSpace P] [ChartedSpace L P]

theorem bijective_mfderiv_comp (f : M → N) (g : N → P)
    (hf : ContMDiff I J ∞ f) (hg : ContMDiff J C ∞ g)
    (hbf : ∀ x : M, Bijective (mfderiv I J f x))
    (hbg : ∀ y : N, Bijective (mfderiv J C g y)) (x : M) :
    Bijective (mfderiv I C (g ∘ f) x) := by
  rw [mfderiv_comp x (hg.mdifferentiableAt (by simp)) (hf.mdifferentiableAt (by simp))]
  exact (hbg (f x)).comp (hbf x)

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

theorem differentialEquivOfBijective_comp (f : M → N) (g : N → P)
    (hf : ContMDiff I J ∞ f) (hg : ContMDiff J C ∞ g)
    (hbf : ∀ x : M, Bijective (mfderiv I J f x))
    (hbg : ∀ y : N, Bijective (mfderiv J C g y))
    (hcomp : ∀ x : M, Bijective (mfderiv I C (g ∘ f) x)) (x : M) :
    differentialEquivOfBijective I C (g ∘ f) hcomp x =
      (differentialEquivOfBijective I J f hbf x).trans
        (differentialEquivOfBijective J C g hbg (f x)) := by
  apply ContinuousLinearEquiv.ext
  funext v
  have h := mfderiv_comp x (hg.mdifferentiableAt (by simp)) (hf.mdifferentiableAt (by simp))
  exact congrArg (fun A : E →L[ℝ] G => A v) h

variable [FiniteDimensional ℝ G]
variable [IsManifold I ∞ M] [IsManifold J ∞ N] [IsManifold C ∞ P]

theorem pullbackSmoothOrientation_comp_apply (f : M → N) (g : N → P)
    (hf : ContMDiff I J ∞ f) (hg : ContMDiff J C ∞ g)
    (hbf : ∀ x : M, Bijective (mfderiv I J f x))
    (hbg : ∀ y : N, Bijective (mfderiv J C g y))
    (hcomp : ∀ x : M, Bijective (mfderiv I C (g ∘ f) x))
    (o : SmoothOrientation C P) (x : M) :
    (pullbackSmoothOrientation I C (g ∘ f) (hg.comp hf) hcomp o).val x =
      (pullbackSmoothOrientation I J f hf hbf
        (pullbackSmoothOrientation J C g hg hbg o)).val x := by
  change tangentOrientationEquiv
      (differentialEquivOfBijective I C (g ∘ f) hcomp x).symm.toLinearEquiv (o.val (g (f x))) =
    tangentOrientationEquiv (differentialEquivOfBijective I J f hbf x).symm.toLinearEquiv
      (tangentOrientationEquiv (differentialEquivOfBijective J C g hbg (f x)).symm.toLinearEquiv
        (o.val (g (f x))))
  rw [differentialEquivOfBijective_comp I J C f g hf hg hbf hbg hcomp x]
  exact tangentOrientationEquiv_trans
    (differentialEquivOfBijective J C g hbg (f x)).symm.toLinearEquiv
    (differentialEquivOfBijective I J f hbf x).symm.toLinearEquiv (o.val (g (f x)))

theorem pullbackSmoothOrientation_pushforward (f : M → N) (hf : ContMDiff I J ∞ f)
    (hbf : ∀ x : M, Bijective (mfderiv I J f x)) (o : SmoothOrientation J N) (x : M) :
    tangentOrientationEquiv (differentialEquivOfBijective I J f hbf x).toLinearEquiv
      ((pullbackSmoothOrientation I J f hf hbf o).val x) = o.val (f x) := by
  exact tangentOrientationEquiv_symm (differentialEquivOfBijective I J f hbf x).symm.toLinearEquiv
    (o.val (f x))

theorem pullbackSmoothOrientation_eq_iff (f : M → N) (hf : ContMDiff I J ∞ f)
    (hbf : ∀ x : M, Bijective (mfderiv I J f x))
    (oN : SmoothOrientation J N) (oM : SmoothOrientation I M) (x : M) :
    (pullbackSmoothOrientation I J f hf hbf oN).val x = oM.val x ↔
      tangentOrientationEquiv (differentialEquivOfBijective I J f hbf x).toLinearEquiv
        (oM.val x) = oN.val (f x) := by
  constructor
  · intro h
    rw [← h]
    exact pullbackSmoothOrientation_pushforward I J f hf hbf oN x
  · intro h
    apply (tangentOrientationEquiv (differentialEquivOfBijective I J f hbf x).toLinearEquiv).injective
    exact (pullbackSmoothOrientation_pushforward I J f hf hbf oN x).trans h.symm
omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem bijective_mfderiv_open_val (U : TopologicalSpace.Opens M) (x : U) :
    Bijective (mfderiv I I (Subtype.val : U → M) x) := by
  rw [DifferentialGeometry.mfderiv_subtype_val]
  exact Function.bijective_id

omit [IsManifold I ∞ M] in
theorem differentialEquivOfBijective_open_val (U : TopologicalSpace.Opens M)
    (hbij : ∀ x : U, Bijective (mfderiv I I (Subtype.val : U → M) x)) (x : U) :
    differentialEquivOfBijective I I (Subtype.val : U → M) hbij x =
      ContinuousLinearEquiv.refl ℝ E := by
  apply ContinuousLinearEquiv.ext
  funext v
  change mfderiv I I (Subtype.val : U → M) x v = v
  rw [DifferentialGeometry.mfderiv_subtype_val]
  rfl

theorem pullbackSmoothOrientation_open_val_apply (U : TopologicalSpace.Opens M)
    (hbij : ∀ x : U, Bijective (mfderiv I I (Subtype.val : U → M) x))
    (o : SmoothOrientation I M) (x : U) :
    (pullbackSmoothOrientation I I (Subtype.val : U → M)
      (contMDiff_subtype_val (I := I) (U := U)) hbij o).val x = o.val x.val := by
  change tangentOrientationEquiv
    (differentialEquivOfBijective I I (Subtype.val : U → M) hbij x).symm.toLinearEquiv (o.val x.val) = _
  rw [differentialEquivOfBijective_open_val]
  exact tangentOrientationEquiv_refl (o.val x.val)
end DifferentialGeometry.Topology.Manifold
