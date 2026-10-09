import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.OrientationSign
import DifferentialGeometry.Topology.Manifold.SmoothOrientation
import DifferentialGeometry.Topology.Manifold.SmoothOrientationCompatible
import DifferentialGeometry.Topology.Manifold.OrientationTransport
import DifferentialGeometry.Bundle.Orientation.Map
import DifferentialGeometry.Geometry.Exponential.Intrinsic.Framed.Coordinates
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false
noncomputable section
open Bundle Set Filter Topology Manifold Metric
open scoped Manifold ContDiff ENNReal
open DifferentialGeometry.Topology.Manifold (tangentOrientationEquiv tangentOrientationEquiv_self
  euclideanSmoothOrientation smoothOrientationOfManifoldOrientation)
namespace DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

def IsOrientedChart {n : ℕ} (o : ManifoldOrientation 𝓘(ℝ, E) M n)
    (oE : Orientation ℝ E (Fin n)) (Φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E M ∞) : Prop :=
  ∀ x (hx : x ∈ Φ.source), Orientation.map (Fin n)
    ((Φ.isLocalDiffeomorphAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ hx).mfderivToContinuousLinearEquiv
      (by simp)).toLinearEquiv oE = o.orientation (Φ x)

theorem orientation_map_mfderiv_of_isPreconnected {n : ℕ}
    (o : ManifoldOrientation 𝓘(ℝ, E) M n) (oE : Orientation ℝ E (Fin n))
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E M ∞) {s : Set E} (hs : IsPreconnected s)
    (hsrc : s ⊆ Φ.source) {x₀ : E} (hx₀ : x₀ ∈ s)
    (h₀ : Orientation.map (Fin n)
      ((Φ.isLocalDiffeomorphAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (hsrc hx₀)).mfderivToContinuousLinearEquiv
        (by simp)).toLinearEquiv oE = o.orientation (Φ x₀)) :
    ∀ x (hx : x ∈ s), Orientation.map (Fin n)
      ((Φ.isLocalDiffeomorphAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (hsrc hx)).mfderivToContinuousLinearEquiv
        (by simp)).toLinearEquiv oE = o.orientation (Φ x) := by
  have hd := o.dimension_eq
  subst hd
  have key (y : E) (hy : y ∈ s) :
      tangentOrientationEquiv
          ((Φ.isLocalDiffeomorphAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (hsrc hy)).mfderivToContinuousLinearEquiv
            (by simp)).toLinearEquiv ((euclideanSmoothOrientation E oE).val y) =
        Orientation.map (Fin (Module.finrank ℝ E))
          ((Φ.isLocalDiffeomorphAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (hsrc hy)).mfderivToContinuousLinearEquiv
            (by simp)).toLinearEquiv oE := by
    let L : E ≃ₗ[ℝ] E :=
      ((Φ.isLocalDiffeomorphAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (hsrc hy)).mfderivToContinuousLinearEquiv
        (by simp)).toLinearEquiv
    change tangentOrientationEquiv L oE = Orientation.map (Fin (Module.finrank ℝ E)) L oE
    exact tangentOrientationEquiv_self L oE
  have h₁ : tangentOrientationEquiv
      ((Φ.isLocalDiffeomorphAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (hsrc hx₀)).mfderivToContinuousLinearEquiv
        (by simp)).toLinearEquiv ((euclideanSmoothOrientation E oE).val x₀) =
      (smoothOrientationOfManifoldOrientation 𝓘(ℝ, E) o).val (Φ x₀) :=
    (key x₀ hx₀).trans h₀
  intro x hx
  exact (key x hx).symm.trans
    ((DifferentialGeometry.PartialDiffeomorph.tangentOrientationEquiv_eq_iff_of_isPreconnected Φ
      (euclideanSmoothOrientation E oE) (smoothOrientationOfManifoldOrientation 𝓘(ℝ, E) o)
      hs hsrc hx₀ hx).mp h₁)

end

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

def normalFrameEquiv (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (x : M) : E ≃ₗ[ℝ] E :=
  (normalFrame g x).toLinearEquiv

open Classical in
def orientedNormalRotation {n : ℕ} (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (o : ManifoldOrientation 𝓘(ℝ, E) M n) (oE : Orientation ℝ E (Fin n)) (ρ : E ≃ₗᵢ[ℝ] E)
    (x : M) : E ≃ₗᵢ[ℝ] E :=
  if Orientation.map (Fin n) (normalFrameEquiv g x) oE = o.orientation x then
    LinearIsometryEquiv.refl ℝ E
  else ρ

theorem orientation_map_orientedNormalRotation {n : ℕ} (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (o : ManifoldOrientation 𝓘(ℝ, E) M n) (oE : Orientation ℝ E (Fin n)) (ρ : E ≃ₗᵢ[ℝ] E)
    (hρ : LinearMap.det (ρ.toLinearEquiv : E →ₗ[ℝ] E) < 0) (x : M) :
    Orientation.map (Fin n)
      ((orientedNormalRotation g o oE ρ x).toLinearEquiv.trans (normalFrameEquiv g x)) oE =
        o.orientation x := by
  have hcard : Fintype.card (Fin n) = Module.finrank ℝ E :=
    (Fintype.card_fin n).trans o.dimension_eq.symm
  rw [← DifferentialGeometry.VectorBundle.map_orientation_trans_between
    (orientedNormalRotation g o oE ρ x).toLinearEquiv (normalFrameEquiv g x) oE]
  by_cases h : Orientation.map (Fin n) (normalFrameEquiv g x) oE = o.orientation x
  · have hQ : orientedNormalRotation g o oE ρ x = LinearIsometryEquiv.refl ℝ E := by
      unfold orientedNormalRotation
      exact ite_eq_left h
    rw [hQ, LinearIsometryEquiv.toLinearEquiv_refl, Orientation.map_refl]
    exact h
  · have hQ : orientedNormalRotation g o oE ρ x = ρ := by
      unfold orientedNormalRotation
      exact ite_eq_right h
    have hneg : Orientation.map (Fin n) ρ.toLinearEquiv oE = -oE :=
      (Orientation.map_eq_neg_iff_det_neg oE ρ.toLinearEquiv hcard).mpr hρ
    have hother : Orientation.map (Fin n) (normalFrameEquiv g x) oE = -o.orientation x :=
      (Orientation.eq_or_eq_neg _ _ hcard).resolve_left h
    rw [hQ, hneg, Orientation.map_neg, hother]
    exact neg_neg _

private theorem det_reflection_orthogonal_span_singleton {v : E} (hv : v ≠ 0) :
    LinearMap.det ((Submodule.reflection (ℝ ∙ v)ᗮ).toLinearEquiv : E →ₗ[ℝ] E) = -1 := by
  have h := Submodule.det_reflection (ℝ ∙ v)ᗮ
  rw [Submodule.orthogonal_orthogonal, finrank_span_singleton hv, pow_one] at h
  exact h

end

def stdEuclideanOrientation (n : ℕ) : Orientation ℝ (EuclideanSpace ℝ (Fin n)) (Fin n) :=
  (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.orientation

def firstCoordinateReflection {n : ℕ} (hn : 0 < n) :
    EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
  Submodule.reflection (ℝ ∙ (EuclideanSpace.basisFun (Fin n) ℝ) ⟨0, hn⟩)ᗮ

theorem det_firstCoordinateReflection_neg {n : ℕ} (hn : 0 < n) :
    LinearMap.det ((firstCoordinateReflection hn).toLinearEquiv :
      EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) < 0 := by
  rw [firstCoordinateReflection, det_reflection_orthogonal_span_singleton
    ((EuclideanSpace.basisFun (Fin n) ℝ).orthonormal.ne_zero ⟨0, hn⟩)]
  norm_num

def orientedEuclideanNormalRotation {n : ℕ} (hn : 0 < n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
    (g : SmoothRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M)
    (o : ManifoldOrientation 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M n) :
    M → (EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :=
  orientedNormalRotation g o (stdEuclideanOrientation n) (firstCoordinateReflection hn)

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
  [T2Space (TangentBundle 𝓘(ℝ, E) M)] [SigmaCompactSpace M] [PseudoEMetricSpace M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E) x)] [IsRiemannianManifold 𝓘(ℝ, E) M]
  [CompleteSpace M] [IsContinuousRiemannianBundle E (fun x : M => TangentSpace 𝓘(ℝ, E) x)]

private theorem mfderiv_zero_eq_of_eqOn_intrinsicFramedExp (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (hEnorm : ∀ x : M, ∀ v : TangentSpace 𝓘(ℝ, E) x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (z : M) (Q : E ≃ₗᵢ[ℝ] E) (Φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E M ∞) {r : ℝ}
    (hr : 0 < r) (hΦ : EqOn Φ (intrinsicFramedExp g hEnorm z ∘ Q) (ball 0 r)) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) Φ 0 = (intrinsicFrameCLM g z).comp (Q : E →L[ℝ] E) := by
  let L : E →L[ℝ] E := (Q : E →L[ℝ] E)
  have hev : (Φ : E → M) =ᶠ[𝓝 0] (intrinsicFramedExp g hEnorm z ∘ L) :=
    Filter.eventuallyEq_of_mem (Metric.ball_mem_nhds 0 hr) hΦ
  have hF : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (intrinsicFramedExp g hEnorm z) (L 0) :=
    (intrinsicFrame_smooth g hEnorm z).contMDiffAt.mdifferentiableAt (by simp)
  have hchain := mfderiv_comp (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, E)) (I'' := 𝓘(ℝ, E)) (0 : E) hF
    L.mdifferentiableAt
  rw [L.mfderiv_eq, map_zero, intrinsicFrame_deriv_zero g hEnorm z] at hchain
  rw [hev.mfderiv_eq]
  exact hchain

private theorem orientation_map_mfderiv_zero_of_eqOn {n : ℕ} (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (hEnorm : ∀ x : M, ∀ v : TangentSpace 𝓘(ℝ, E) x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (o : ManifoldOrientation 𝓘(ℝ, E) M n) (oE : Orientation ℝ E (Fin n)) (ρ : E ≃ₗᵢ[ℝ] E)
    (hρ : LinearMap.det (ρ.toLinearEquiv : E →ₗ[ℝ] E) < 0) (z : M)
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E M ∞) {r : ℝ} (hr : 0 < r)
    (h0 : (0 : E) ∈ Φ.source)
    (hΦ : EqOn Φ (intrinsicFramedExp g hEnorm z ∘ orientedNormalRotation g o oE ρ z)
      (ball 0 r)) :
    Orientation.map (Fin n)
      ((Φ.isLocalDiffeomorphAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ h0).mfderivToContinuousLinearEquiv
        (by simp)).toLinearEquiv oE = o.orientation (Φ 0) := by
  let A : E ≃ₗ[ℝ] E :=
    ((Φ.isLocalDiffeomorphAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ h0).mfderivToContinuousLinearEquiv
      (by simp)).toLinearEquiv
  have hz : Φ 0 = z := by
    have h := hΦ (Metric.mem_ball_self hr)
    rw [h, Function.comp_apply, map_zero]
    exact intrinsicFrame_zero g hEnorm z
  have hA : A = (orientedNormalRotation g o oE ρ z).toLinearEquiv.trans (normalFrameEquiv g z) := by
    apply LinearEquiv.ext
    intro v
    exact congrArg (fun T : E →L[ℝ] E => T v)
      (mfderiv_zero_eq_of_eqOn_intrinsicFramedExp g hEnorm z _ Φ hr hΦ)
  have hfin : Orientation.map (Fin n) A oE = o.orientation (Φ 0) := by
    rw [hz, hA]
    exact orientation_map_orientedNormalRotation g o oE ρ hρ z
  exact hfin

theorem isOrientedChart_of_eqOn_intrinsicFramedExp {n : ℕ}
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (hEnorm : ∀ x : M, ∀ v : TangentSpace 𝓘(ℝ, E) x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (o : ManifoldOrientation 𝓘(ℝ, E) M n) (oE : Orientation ℝ E (Fin n)) (ρ : E ≃ₗᵢ[ℝ] E)
    (hρ : LinearMap.det (ρ.toLinearEquiv : E →ₗ[ℝ] E) < 0) (z : M)
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E M ∞) {r : ℝ} (hr : 0 < r)
    (hsrc : Φ.source = ball 0 r)
    (hΦ : EqOn Φ (intrinsicFramedExp g hEnorm z ∘ orientedNormalRotation g o oE ρ z)
      (ball 0 r)) :
    IsOrientedChart o oE Φ := by
  have hsub : ball (0 : E) r ⊆ Φ.source := hsrc.symm.subset
  have h0 : (0 : E) ∈ ball (0 : E) r := Metric.mem_ball_self hr
  have hball := orientation_map_mfderiv_of_isPreconnected o oE Φ
    (convex_ball (0 : E) r).isPreconnected hsub h0
    (orientation_map_mfderiv_zero_of_eqOn g hEnorm o oE ρ hρ z Φ hr (hsub h0) hΦ)
  intro x hx
  exact hball x (hsrc.subset hx)

end

end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
