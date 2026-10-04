import DifferentialGeometry.Geometry.Comparison.FiniteSoul.NormalParam
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.SoulCarrierBaseApplications

/-!
# Consumers of the §10 normal parametrization (lane CMS3-CARRIER, group G2)

* the frozen interface `exists_normalParametrization` VERBATIM (with `[NeZero (finrank ℝ E)]`,
  `hnorm`, `hSc`, `hbinj`, which the construction does not use), as an `example`; the three unused
  binders are renamed `_hnorm`, `_hSc`, `_hbinj` (statement text otherwise unchanged);
* `exists_normalParametrization_circle`: for a one-dimensional soul (compact connected totally
  geodesic `C^r` slice of dimension one) the normal parametrization over the circle carrier
  `AddCircle 1` of BASE-1a/1b, with fibres of rank `dim − 1`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter Function Metric
open scoped Manifold ContDiff Topology InnerProductSpace

namespace DifferentialGeometry.Geometry.FiniteSoul

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {r : ℕ∞}

/-- The frozen interface §10, verbatim (`FiniteSoulThreeInterfaces.lean` :507–532). -/
example [NeZero (Module.finrank ℝ E)]
    {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [FiniteDimensional ℝ EB]
    {B : Type*} [TopologicalSpace B] [ChartedSpace EB B] [IsManifold 𝓘(ℝ, EB) ∞ B] [CompactSpace B]
    [T2Space B]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (_hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {S : Set M} {d : ℕ} (hS : IsEmbeddedSliceOfOrder I (r : ℕ∞ω) d S) (_hSc : IsCompact S)
    (b : B → M) (hb : ContMDiff 𝓘(ℝ, EB) I ((r - 1 : ℕ∞) : ℕ∞ω) b) (_hbinj : Injective b)
    (hbS : range b = S)
    (hbinv : ∃ R : M → B, (∀ s, R (b s) = s) ∧
      ∀ x ∈ S, ContMDiffAt I 𝓘(ℝ, EB) ((r - 1 : ℕ∞) : ℕ∞ω) R x) :
    ∃ (K : ℕ) (Phat : B → EuclideanSpace ℝ (Fin K) →L[ℝ] EuclideanSpace ℝ (Fin K))
      (ι : B × EuclideanSpace ℝ (Fin K) → TangentBundle I M),
      ContMDiff 𝓘(ℝ, EB) 𝓘(ℝ, EuclideanSpace ℝ (Fin K) →L[ℝ] EuclideanSpace ℝ (Fin K)) ∞ Phat ∧
      (∀ s, Phat s ∘L Phat s = Phat s) ∧ (∀ s, (Phat s).adjoint = Phat s) ∧
      (∀ s, Module.finrank ℝ (LinearMap.range (Phat s : EuclideanSpace ℝ (Fin K) →ₗ[ℝ]
        EuclideanSpace ℝ (Fin K))) = Module.finrank ℝ E - d) ∧
      ContMDiff (𝓘(ℝ, EB).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin K))) I.tangent ((r - 1 : ℕ∞) : ℕ∞ω) ι ∧
      (∀ s w, (ι (s, w)).proj = b s) ∧
      (∀ s, ∃ A : EuclideanSpace ℝ (Fin K) →L[ℝ] E, ∀ w, @Eq E (ι (s, w)).snd (A w)) ∧
      (∀ s w, ι (s, Phat s w) = ι (s, w)) ∧
      (∀ s w, Phat s w = w → ι (s, w) ∈ normalSetFinite g S ∧
        g.inner (ι (s, w)).proj (ι (s, w)).snd (ι (s, w)).snd = ‖w‖ ^ 2) ∧
      (∀ v ∈ normalSetFinite g S, ∃ s w, Phat s w = w ∧ ι (s, w) = v) :=
  exists_normalParametrization g hr hS b hb hbS hbinv

/-- **The normal parametrization of a one-dimensional soul** over the circle carrier. -/
theorem exists_normalParametrization_circle
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {S : Set M} (hSc : IsCompact S) (hconn : IsConnected S)
    (hS : IsEmbeddedSliceOfOrder I (r : ℕ∞ω) 1 S) (htg : IsTotallyGeodesicFinite g S) :
    ∃ b : AddCircle (1 : ℝ) → M, ContMDiff 𝓘(ℝ, ℝ) I ((r - 1 : ℕ∞) : ℕ∞ω) b ∧ Injective b ∧
      range b = S ∧ ∃ (K : ℕ)
        (Phat : AddCircle (1 : ℝ) → EuclideanSpace ℝ (Fin K) →L[ℝ] EuclideanSpace ℝ (Fin K))
        (ι : AddCircle (1 : ℝ) × EuclideanSpace ℝ (Fin K) → TangentBundle I M),
        ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin K) →L[ℝ] EuclideanSpace ℝ (Fin K)) ∞ Phat ∧
        (∀ s, Phat s ∘L Phat s = Phat s) ∧ (∀ s, (Phat s).adjoint = Phat s) ∧
        (∀ s, Module.finrank ℝ (LinearMap.range (Phat s : EuclideanSpace ℝ (Fin K) →ₗ[ℝ]
          EuclideanSpace ℝ (Fin K))) = Module.finrank ℝ E - 1) ∧
        ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin K))) I.tangent
          ((r - 1 : ℕ∞) : ℕ∞ω) ι ∧
        (∀ s w, (ι (s, w)).proj = b s) ∧
        (∀ s w, Phat s w = w → ι (s, w) ∈ normalSetFinite g S ∧
          g.inner (ι (s, w)).proj (ι (s, w)).snd (ι (s, w)).snd = ‖w‖ ^ 2) ∧
        (∀ v ∈ normalSetFinite g S, ∃ s w, Phat s w = w ∧ ι (s, w) = v) := by
  obtain ⟨b, hb, hbinj, hbS, R, hRb, hR⟩ := soulBase_of_slice_dim_one g hr hnorm hSc hconn hS htg
  obtain ⟨K, Phat, ι, h1, h2, h3, h4, h5, h6, -, -, h9, h10⟩ :=
    exists_normalParametrization (EB := ℝ) g hr hS b hb hbS ⟨R, hRb, hR⟩
  exact ⟨b, hb, hbinj, hbS, K, Phat, ι, h1, h2, h3, h4, h5, h6, h9, h10⟩

end DifferentialGeometry.Geometry.FiniteSoul
