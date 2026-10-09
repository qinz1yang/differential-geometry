import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThinBoundaryNaturalityFull
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThinBoundaryAssemble

/-!
# CH12 C4: a `CuspEmbedding` collar from `H`-side data

`CuspEmbedding.ofTruncation_C4`: for a (level-`S`) truncation `T`, a map `f` which is smooth and
an immersion on an open set `Uo ⊇ cuspMap '' cuspDomain` with `H`-side `C^K` error `≤ δ`, and
whose composite `f ∘ cuspMap` is an embedding of `cuspDomain` with height-zero slice `X ⊆ ∂W`,
the collar `f ∘ T.cuspMap i` is a `CuspEmbedding W g K δ X` with cusp `T.cusp i`
(`metric_error` by `cuspMetricErrorBound_of_H_C4`, `boundary_preimage` by `boundary_preimage_C4`).
-/

set_option autoImplicit false

noncomputable section

open Set TopologicalSpace DifferentialGeometry DifferentialGeometry.Tensor0SBundle
  DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Hyperbolic
  DifferentialGeometry.Geometry.Collapse GC.Endpoint
open scoped Manifold ContDiff

namespace GC.LongTime.Ch12

universe u

def CuspEmbedding.ofTruncation_C4 {W : CompactCarrier.{u}} {H : FiniteVolumeHyperbolicModel.{u}}
    (T : HyperbolicTruncation H) (i : Fin T.count)
    (g : SmoothRiemannianMetric W.model W.Carrier) (K : ℕ) (δ : ℝ)
    (f : H.Carrier → W.Carrier) (Uo : Opens H.Carrier)
    (hrange : ∀ p ∈ cuspDomain, T.cuspMap i p ∈ Uo)
    (hf : ContMDiffOn (𝓡 3) W.model ∞ f Uo)
    (himm : ∀ y ∈ Uo, Function.Injective (mfderiv (𝓡 3) W.model f y))
    (herr : ∀ k : ℕ, k ≤ K → ∀ p ∈ cuspDomain,
      tensor0SFiberNorm H.metric (T.cuspMap i p) (2 + k)
        (iteratedMetricCovariantDerivative H.metric 2
          (rawPullbackError_C4 g H.metric f) k (T.cuspMap i p)) ≤ δ)
    (X : Set W.Carrier)
    (hemb : _root_.Topology.IsEmbedding (fun p : cuspDomain => (f ∘ T.cuspMap i) p))
    (hslice : Set.range (fun t : Torus => (f ∘ T.cuspMap i) (t, halfZero)) = X)
    (hX : X ⊆ W.model.boundary W.Carrier) :
    CuspEmbedding W g K δ X :=
  CuspEmbedding.ofSlice_C4 (T.cusp i) (f ∘ T.cuspMap i)
    ((hf.comp (T.cuspEmbedding i).contMDiff.contMDiffOn hrange).of_le
      (by exact_mod_cast le_top))
    hemb
    (fun p hp => by
      intro v w h
      have hyU : T.cuspMap i p ∈ Uo := hrange p hp
      have hfd : MDifferentiableAt (𝓡 3) W.model f (T.cuspMap i p) :=
        (hf.contMDiffAt (Uo.isOpen.mem_nhds hyU)).mdifferentiableAt infty_ne_zero_C4
      have hφd : MDifferentiableAt halfCollarModel (𝓡 3) (T.cuspMap i) p :=
        (T.cuspEmbedding i).contMDiff.mdifferentiableAt infty_ne_zero_C4
      rw [mfderiv_comp p hfd hφd] at h
      exact cuspMap_immersion_C4 T i p (himm _ hyU h))
    hslice hX (cuspMetricErrorBound_of_H_C4 T i g K δ f Uo hrange hf himm herr)

end GC.LongTime.Ch12
