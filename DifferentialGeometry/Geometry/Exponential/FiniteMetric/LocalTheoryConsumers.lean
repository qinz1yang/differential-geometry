import DifferentialGeometry.Geometry.Exponential.FiniteMetric.GaussLemma
import DifferentialGeometry.Geometry.Metric.Basic

/-!
# Consumers of the finite-metric local theory (CM1.a–c and the Gauss lemma)

A smooth metric `g : SmoothRiemannianMetric I M` is a `ContMDiffRiemannianMetric I ((⊤ : ℕ∞) + 1)`
definitionally (`((⊤ : ℕ∞) : ℕ∞ω) + 1 = ∞`), so every finite-order statement applies to it with
`r = ⊤`; and a `C³` metric is the case `r = 2`, the lowest order at which the Gauss lemma is proved.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set
open scoped Manifold ContDiff

namespace Bundle.ContMDiffRiemannianMetric

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

/-- Homogeneity of the geodesic flow of a smooth metric. -/
theorem geodesicFlow_smul_eq_of_smooth (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    (p : TangentBundle I M) (s t : ℝ) (h : (p, s * t) ∈ g.geodesicFlowDomain) :
    g.geodesicFlow ⟨p.proj, s • p.snd⟩ t =
      ⟨(g.geodesicFlow p (s * t)).proj, s • (g.geodesicFlow p (s * t)).snd⟩ :=
  geodesicFlow_smul_eq (r := ⊤) g le_top p s t h

/-- Conservation of speed along the geodesic flow of a smooth metric. -/
theorem inner_geodesicFlow_eq_of_smooth (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    (p : TangentBundle I M) (t : ℝ) (ht : (p, t) ∈ g.geodesicFlowDomain) :
    g.inner (g.geodesicFlow p t).proj (g.geodesicFlow p t).snd (g.geodesicFlow p t).snd =
      g.inner p.proj p.snd p.snd :=
  inner_geodesicFlow_eq (r := ⊤) g le_top p t ht

/-- The differential at the origin of the exponential map of a smooth metric. -/
theorem hasMFDerivAt_expMap_zero_of_smooth (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    (x : M) :
    HasMFDerivAt 𝓘(ℝ, E) I (fun v : E => g.expMap (⟨x, v⟩ : TangentBundle I M)) 0
      (ContinuousLinearMap.id ℝ E) :=
  hasMFDerivAt_expMap_zero (r := ⊤) g le_top x

/-- The Gauss lemma for the (Della) exponential map of a smooth metric. -/
theorem inner_mfderiv_expMap_radial_of_smooth
    (g : DifferentialGeometry.SmoothRiemannianMetric I M) (x : M) {v : E}
    (hv : (⟨x, v⟩ : TangentBundle I M) ∈ g.expDomain) (w : E) :
    g.inner (g.expMap (⟨x, v⟩ : TangentBundle I M))
        (mfderiv 𝓘(ℝ, E) I (fun u : E => g.expMap (⟨x, u⟩ : TangentBundle I M)) v v)
        (mfderiv 𝓘(ℝ, E) I (fun u : E => g.expMap (⟨x, u⟩ : TangentBundle I M)) v w) =
      g.inner x v w :=
  inner_mfderiv_expMap_radial (r := ⊤) g (by exact_mod_cast le_top) x hv w

/-- The Gauss lemma for a `C³` metric, the lowest order covered. -/
theorem inner_mfderiv_expMap_radial_of_C3
    (g : ContMDiffRiemannianMetric I 3 E (TangentSpace I : M → Type _)) (x : M) {v : E}
    (hv : (⟨x, v⟩ : TangentBundle I M) ∈ g.expDomain) (w : E) :
    g.inner (g.expMap (⟨x, v⟩ : TangentBundle I M))
        (mfderiv 𝓘(ℝ, E) I (fun u : E => g.expMap (⟨x, u⟩ : TangentBundle I M)) v v)
        (mfderiv 𝓘(ℝ, E) I (fun u : E => g.expMap (⟨x, u⟩ : TangentBundle I M)) v w) =
      g.inner x v w :=
  inner_mfderiv_expMap_radial (r := 2) g le_rfl x hv w

end Bundle.ContMDiffRiemannianMetric
