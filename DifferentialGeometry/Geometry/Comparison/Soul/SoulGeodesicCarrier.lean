import DifferentialGeometry.Geometry.Comparison.Soul.SoulSubmanifold
import DifferentialGeometry.Geometry.Comparison.Soul.GeodesicGerms

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.Geodesic

namespace DifferentialGeometry.Geometry.Topology

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [ConnectedSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)]

theorem exists_unit_geodesic_in_soul_of_pos_dim
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    {S : Set M} (hconv : IsTotallyConvex (I := I) g S) (hclosed : IsClosed S)
    (hB : relBoundary I S = ∅) (hdim : 0 < maxSliceDim I S)
    {x : M} (hx : x ∈ S) :
    ∃ γ : ℝ → M, γ 0 = x ∧ ContMDiff 𝓘(ℝ, ℝ) I ∞ γ ∧
      IsGeodesic (I := I) g γ ∧ (∀ t : ℝ, IsGeodesicAt (I := I) g γ t) ∧
      (∀ t : ℝ, g.inner (γ t)
        (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)) = 1) ∧
      ∀ t : ℝ, γ t ∈ S := by
  let hS := isEmbeddedSlice_of_relBoundary_eq_empty hEnorm hconv hB
  let _ : FiniteDimensional ℝ (TangentSpace I x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  have hdimT : 0 < Module.finrank ℝ (sliceTangent I S x) := by
    rw [finrank_sliceTangent hS hx]
    exact hdim
  obtain ⟨v, hv⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hdimT
  have hv0 : (v : TangentSpace I x) ≠ 0 := by
    intro hvzero
    exact hv (Subtype.ext hvzero)
  let L := Real.sqrt (g.inner x v.1 v.1)
  have hL : 0 < L := Real.sqrt_pos.mpr (g.pos x v.1 hv0)
  let u : sliceTangent I S x := L⁻¹ • v
  have hu : g.inner x u.1 u.1 = 1 := by
    change g.inner x (L⁻¹ • v.1) (L⁻¹ • v.1) = 1
    rw [gInner_smul_self]
    have hsq : g.inner x v.1 v.1 = L ^ 2 :=
      (Real.sq_sqrt (gInner_self_nonneg g x v.1)).symm
    rw [hsq, ← mul_pow, inv_mul_cancel₀ hL.ne', one_pow]
  let γ := intrinsicGeodesic g hEnorm x u.1
  have hγsmooth : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ :=
    intrinsicGeodesic_contMDiff g hEnorm x u.1
  have hγgeo : IsGeodesic (I := I) g γ :=
    intrinsicGeodesic_isGeodesic g hEnorm x u.1
  refine ⟨γ, intrinsicGeodesic_zero g hEnorm x u.1, hγsmooth, hγgeo, ?_, ?_, ?_⟩
  · intro t
    exact isGeodesicAt_of_eventually_hasGeodesicEquationAt g
      (Filter.Eventually.of_forall hγgeo)
      (Filter.Eventually.of_forall (fun _ => hγsmooth.continuous.continuousAt))
  · intro t
    exact (intrinsicGeodesic_speedSq_eq g hEnorm x u.1 t).trans hu
  · intro t
    exact intrinsicGeodesic_mem_of_relBoundary_eq_empty g hEnorm hconv hclosed hB hx u.2 t

end DifferentialGeometry.Geometry.Topology

end
