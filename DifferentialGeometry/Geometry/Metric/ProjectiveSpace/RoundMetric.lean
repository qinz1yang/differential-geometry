import DifferentialGeometry.Topology.ProjectiveSpace.Manifold
import DifferentialGeometry.Geometry.Metric.Sphere.Isometry.OrthogonalAction
import DifferentialGeometry.Geometry.Metric.Sphere.Isometry.Representation
import DifferentialGeometry.Geometry.Metric.Quotient

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]
variable {n : Nat} [Fact (Module.finrank Real E = n + 1)]

theorem realProjectiveSpaceAntipodalGroup_pullbackMetric_roundMetric
    (gamma : realProjectiveSpaceAntipodalGroup E) :
    Diffeomorph.pullbackMetric (roundMetric (E := E) (n := n))
      (MulAction.smulDiffeomorph (n := ∞) (𝓡 n) gamma) = roundMetric := by
  rcases realProjectiveSpaceAntipodalGroup_eq_one_or_generator gamma with h | h
  · have heq : MulAction.smulDiffeomorph (n := ∞) (𝓡 n) gamma =
        _root_.Diffeomorph.refl (𝓡 n) (Metric.sphere (0 : E) 1) ∞ := by
      apply _root_.Diffeomorph.ext
      intro x
      change gamma.1 x = x
      rw [h]
      rfl
    rw [heq, Diffeomorph.pullbackMetric_refl]
  · have heq : MulAction.smulDiffeomorph (n := ∞) (𝓡 n) gamma =
        sphereDiffeo (E := E) (n := n) (LinearIsometryEquiv.neg Real) := by
      apply _root_.Diffeomorph.ext
      intro x
      apply Subtype.ext
      change (gamma.1 x : E) = -(x : E)
      rw [h]
      rfl
    rw [heq]
    exact pullbackMetric_round_eq (E := E) (n := n) (LinearIsometryEquiv.neg Real)

def roundProjectiveMetric : SmoothRiemannianMetric (𝓡 n) (RealProjectiveSpace E) :=
  descendedMetric (roundMetric (E := E) (n := n))
    realProjectiveSpaceQuotientMap realProjectiveSpaceQuotientMap_isLocalDiffeomorph
    realProjectiveSpaceQuotientMap_surjective
    (metricFiberCompatible_quotientMk_of_invariant roundMetric
      realProjectiveSpaceAntipodalGroup_pullbackMetric_roundMetric)

theorem localPullMetric_roundProjectiveMetric :
    localPullMetric (roundProjectiveMetric (E := E) (n := n))
      realProjectiveSpaceQuotientMap realProjectiveSpaceQuotientMap_isLocalDiffeomorph =
        roundMetric :=
  localPullMetric_descendedMetric (roundMetric (E := E) (n := n))
    realProjectiveSpaceQuotientMap realProjectiveSpaceQuotientMap_isLocalDiffeomorph
    realProjectiveSpaceQuotientMap_surjective
    (metricFiberCompatible_quotientMk_of_invariant roundMetric
      realProjectiveSpaceAntipodalGroup_pullbackMetric_roundMetric)

theorem not_exists_diffeomorph_pullbackMetric_roundProjectiveMetric (hn : 0 < n) :
    ¬ ∃ Phi : RealProjectiveSpace E ≃ₘ⟮𝓡 n, 𝓡 n⟯ Metric.sphere (0 : E) 1,
      Diffeomorph.pullbackMetricCross (roundMetric (E := E) (n := n)) Phi =
        roundProjectiveMetric := by
  rintro ⟨Phi, hmetric⟩
  let q := realProjectiveSpaceQuotientMap (E := E)
  have hq : IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ q :=
    realProjectiveSpaceQuotientMap_isLocalDiffeomorph
  have hf : IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞
      ((Phi : RealProjectiveSpace E → Metric.sphere (0 : E) 1) ∘ q) :=
    fun x => IsLocalDiffeomorphAt.comp (K := 𝓡 n)
      (M := Metric.sphere (0 : E) 1) (N := RealProjectiveSpace E)
      (P := Metric.sphere (0 : E) 1) (hq x) (Phi.isLocalDiffeomorph (q x))
  have hpull : localPullMetric (roundMetric (E := E) (n := n))
      ((Phi : RealProjectiveSpace E → Metric.sphere (0 : E) 1) ∘ q) hf =
        roundMetric := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    rw [localPullMetric_inner]
    have hchain : mfderiv (𝓡 n) (𝓡 n)
        ((Phi : RealProjectiveSpace E → Metric.sphere (0 : E) 1) ∘ q) x =
      (mfderiv (𝓡 n) (𝓡 n) Phi (q x)).comp (mfderiv (𝓡 n) (𝓡 n) q x) :=
      mfderiv_comp x (Phi.contMDiff.mdifferentiableAt (by simp))
        (hq.contMDiff.mdifferentiableAt (by simp))
    rw [hchain]
    simp only [ContinuousLinearMap.comp_apply, Function.comp_apply]
    have hPhi := congrArg
      (fun k : SmoothRiemannianMetric (𝓡 n) (RealProjectiveSpace E) =>
        k.inner (q x) (mfderiv (𝓡 n) (𝓡 n) q x v) (mfderiv (𝓡 n) (𝓡 n) q x w)) hmetric
    rw [Diffeomorph.pullbackMetricCross_inner] at hPhi
    have hround := congrArg
      (fun k : SmoothRiemannianMetric (𝓡 n) (Metric.sphere (0 : E) 1) => k.inner x v w)
      (localPullMetric_roundProjectiveMetric (E := E) (n := n))
    rw [localPullMetric_inner] at hround
    exact hPhi.trans hround
  obtain ⟨A, hA⟩ := exists_linearIsometryEquiv_of_localPullMetric_roundMetric_eq hn hf hpull
  have hinj : Function.Injective
      ((Phi : RealProjectiveSpace E → Metric.sphere (0 : E) 1) ∘ q) := by
    rw [← hA]
    exact (sphereDiffeo (E := E) (n := n) A).injective
  have hdim : 0 < Module.finrank Real E := by
    rw [show Module.finrank Real E = n + 1 from Fact.out]
    exact Nat.succ_pos n
  let _ : Nontrivial E := Module.nontrivial_of_finrank_pos hdim
  obtain ⟨x, hx⟩ := NormedSpace.sphere_nonempty (E := E).2 zero_le_one
  let y : Metric.sphere (0 : E) 1 := ⟨x, hx⟩
  have heq : q (realProjectiveSpaceAntipodalHomeomorph E y) = q y := by
    apply realProjectiveSpaceQuotientMap_eq_iff.mpr
    exact Or.inr (realProjectiveSpaceAntipodalHomeomorph_coe y)
  exact realProjectiveSpaceAntipodalHomeomorph_fixed_point_free y (hinj (congrArg Phi heq))

end DifferentialGeometry.Geometry
