import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.Isometry
import DifferentialGeometry.Topology.Morse.NormalForm.Local

/-!
# The isometry-invariant round metric from a rescaled Ricci flow limit

Chapter 7, packet P8, surface lemma U1 (`exists_isometryInvariant_roundMetric`), route (a),
assembly step. `exists_isometryInvariant_roundMetric_of_rescaled_limit` derives the conclusion of
U1 from a Ricci flow `g` on `[0, T)` starting at `h` (joint smoothness and the Ricci flow equation,
the form of the short-time existence theorem), a sequence of times `τ k ≥ 0` with `τ k → T` from
below, and scalars `lam k` such that `lam k • g (τ k)` converges pointwise, on every pair of
tangent vectors, to a smooth metric of sectional curvature one.

Every isometry of `h` is an isometry of each `g t` (`ricci_flow_pullback_eq_of_initial_isometry`),
hence of each rescaled metric; pointwise limits of real numbers are unique, so it is an isometry of
the limit. One fixed subsequence serves all isometries at once; no diagonal argument is used.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open Filter Topology
open scoped Manifold ContDiff

namespace GC.Geometry

local notation "MM2" => DifferentialGeometry.Topology.Morse.MorseModel 2

variable {N : Type*} [TopologicalSpace N] [ChartedSpace MM2 N] [IsManifold 𝓘(ℝ, MM2) ∞ N]
  [T2Space N] [CompactSpace N]

omit [CompactSpace N] in
theorem pullbackMetric_eq_of_tendsto_smul {h₁ : SmoothRiemannianMetric 𝓘(ℝ, MM2) N}
    (g : ℕ → SmoothRiemannianMetric 𝓘(ℝ, MM2) N) (lam : ℕ → ℝ)
    (hconv : ∀ (x : N) (v w : TangentSpace 𝓘(ℝ, MM2) x),
      Tendsto (fun k => lam k * (g k).inner x v w) atTop (𝓝 (h₁.inner x v w)))
    (φ : N ≃ₘ⟮𝓘(ℝ, MM2), 𝓘(ℝ, MM2)⟯ N)
    (hφ : ∀ᶠ k in atTop, Diffeomorph.pullbackMetric (g k) φ = g k) :
    Diffeomorph.pullbackMetric h₁ φ = h₁ := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [Diffeomorph.pullbackMetric_inner]
  have hleft := hconv (φ x) (mfderiv 𝓘(ℝ, MM2) 𝓘(ℝ, MM2) φ x v)
    (mfderiv 𝓘(ℝ, MM2) 𝓘(ℝ, MM2) φ x w)
  have hseq : (fun k => lam k * (g k).inner (φ x) (mfderiv 𝓘(ℝ, MM2) 𝓘(ℝ, MM2) φ x v)
      (mfderiv 𝓘(ℝ, MM2) 𝓘(ℝ, MM2) φ x w)) =ᶠ[atTop] fun k => lam k * (g k).inner x v w := by
    filter_upwards [hφ] with k hk
    rw [← Diffeomorph.pullbackMetric_inner, hk]
  exact tendsto_nhds_unique (hleft.congr' hseq) (hconv x v w)

theorem exists_isometryInvariant_roundMetric_of_rescaled_limit
    (h : SmoothRiemannianMetric 𝓘(ℝ, MM2) N) {T : ℝ} (hT : 0 < T)
    (g : ℝ → SmoothRiemannianMetric 𝓘(ℝ, MM2) N) (hg : g 0 = h)
    (hjoint : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, MM2))
      (𝓘(ℝ, MM2).prod 𝓘(ℝ, MM2 →L[ℝ] MM2 →L[ℝ] ℝ)) ∞
        (fun p : ℝ × N => (⟨p.2, (g p.1).inner p.2⟩ :
          Bundle.TotalSpace (MM2 →L[ℝ] MM2 →L[ℝ] ℝ)
            (fun x => TangentSpace 𝓘(ℝ, MM2) x →L[ℝ] TangentSpace 𝓘(ℝ, MM2) x →L[ℝ] ℝ)))
        (Set.Ico 0 T ×ˢ (Set.univ : Set N)))
    (hpde : ∀ t ∈ Set.Ico 0 T, ∀ (x : N) (v w : TangentSpace 𝓘(ℝ, MM2) x),
      HasDerivWithinAt (fun s => (g s).inner x v w) (-2 * ricciTensor (g t) x v w)
        (Set.Ici 0) t)
    (τ : ℕ → ℝ) (hτ : ∀ k, 0 ≤ τ k) (hτT : Tendsto τ atTop (𝓝[<] T))
    (lam : ℕ → ℝ) (hlim : SmoothRiemannianMetric 𝓘(ℝ, MM2) N)
    (hconv : ∀ (x : N) (v w : TangentSpace 𝓘(ℝ, MM2) x),
      Tendsto (fun k => lam k * (g (τ k)).inner x v w) atTop (𝓝 (hlim.inner x v w)))
    (hround : ∀ (y : N) (X Y : TangentSpace 𝓘(ℝ, MM2) y),
      metricRm04StandardAt hlim y X Y Y X =
        1 * (hlim.inner y X X * hlim.inner y Y Y - hlim.inner y X Y * hlim.inner y X Y)) :
    ∃ h₁ : SmoothRiemannianMetric 𝓘(ℝ, MM2) N,
      (∀ (y : N) (X Y : TangentSpace 𝓘(ℝ, MM2) y),
        metricRm04StandardAt h₁ y X Y Y X =
          1 * (h₁.inner y X X * h₁.inner y Y Y - h₁.inner y X Y * h₁.inner y X Y)) ∧
      ∀ φ : N ≃ₘ⟮𝓘(ℝ, MM2), 𝓘(ℝ, MM2)⟯ N,
        Diffeomorph.pullbackMetric h φ = h → Diffeomorph.pullbackMetric h₁ φ = h₁ := by
  refine ⟨hlim, hround, fun φ hφ => ?_⟩
  have hflow := DifferentialGeometry.PDE.RicciFlow.ricci_flow_pullback_eq_of_initial_isometry
    g hT hjoint hpde φ (hg ▸ hφ)
  refine pullbackMetric_eq_of_tendsto_smul (fun k => g (τ k)) lam hconv φ ?_
  filter_upwards [hτT self_mem_nhdsWithin] with k hk
  exact hflow (τ k) ⟨hτ k, hk⟩

end GC.Geometry
