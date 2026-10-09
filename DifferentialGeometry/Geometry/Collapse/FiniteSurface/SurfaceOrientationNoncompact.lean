import DifferentialGeometry.Geometry.Collapse.FiniteCategory.ExactSplitting.SplittingOrientation
import DifferentialGeometry.Geometry.Collapse.FiniteSurface.SurfaceOrientation

/-!
# The oriented smooth carrier of a (possibly noncompact) surface factor

Consumer of the general-rank LFR11 orientation clause (`exists_oriented_smoothCarrier_splittingFactor`)
in the rank-one 3-dimensional case, WITHOUT compactness of the residual factor: for an exact line
splitting `e : N ≃ᵢ ℓ²(ℝ × W)` of an oriented 3-manifold with a `C^{k+1}` metric, the zero factor
`Z` has a smooth carrier `S` modelled on `𝓡 2`, `C^{k+2}`-diffeomorphic to `Z`, with a
`ManifoldOrientation (𝓡 2) S 2`; the orientation is the one for which `(∂_t, dι dφ b)` is positive
in `N` exactly when `b` is (`surfaceFactor_oriented_smoothCarrier`). This is the orientation input
(`o : ManifoldOrientation (𝓡 2) Z 2`) of LFR24 needed by LFR28 I6(c).
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter WithLp Manifold Function Module
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Geometry.ExactSplitting DifferentialGeometry.Topology.Manifold

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "P" => Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) - Module.finrank ℝ ℝ) → ℝ

local instance nezero_finrank_euclidean_three_orientNC_F7LFR11c :
    NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) :=
  ⟨by rw [finrank_euclideanSpace_fin]; decide⟩

universe u

/-- The index identification `Fin 1 ⊕ Fin 2 ≃ Fin 3` (normal direction first). -/
def lineSurfaceIndex :
    Fin 1 ⊕ Fin (finrank ℝ (EuclideanSpace ℝ (Fin 2))) ≃
      Fin (finrank ℝ (EuclideanSpace ℝ (Fin 3))) :=
  finSumFinEquiv.trans (finCongr (by simp))

/-- **The oriented smooth carrier of the surface factor (no compactness).** -/
theorem surfaceFactor_oriented_smoothCarrier {N W : Type u} [MetricSpace N] [ChartedSpace E3 N]
    [IsManifold 𝓘(ℝ, E3) ∞ N] [RiemannianBundle (fun x : N => TangentSpace 𝓘(ℝ, E3) x)]
    [IsRiemannianManifold 𝓘(ℝ, E3) N] [CompleteSpace N] [SecondCountableTopology N]
    [MetricSpace W] {k : ℕ}
    (G : ContMDiffRiemannianMetric 𝓘(ℝ, E3) (((k : ℕ∞) : ℕ∞ω) + 1) E3
      (TangentSpace 𝓘(ℝ, E3) : N → Type _))
    (hk : 2 ≤ (k : ℕ∞))
    (hnorm : ∀ (x : N) (v : TangentSpace 𝓘(ℝ, E3) x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (G.inner x v v)))
    (oN : ManifoldOrientation (𝓡 3) N 3) (e : N ≃ᵢ WithLp 2 (ℝ × W)) :
    letI := splittingFactorChartedSpace G hk hnorm e
    letI := splittingFactor_isManifold_one G hk hnorm e
    ∃ (S : Type u) (_ : MetricSpace S) (_ : ChartedSpace E2 S) (_ : IsManifold (𝓡 2) ∞ S)
      (φ : S ≃ₜ {x : N // (e x).fst = 0}),
      ContMDiff (𝓡 2) 𝓘(ℝ, P) ((k + 2 : ℕ) : ℕ∞ω) φ ∧
      ContMDiff 𝓘(ℝ, P) (𝓡 2) ((k + 2 : ℕ) : ℕ∞ω) φ.symm ∧
      ∃ (hbij : ∀ s, Bijective (ambientSplitFrame 𝓘(ℝ, E3) (𝓡 2) (Subtype.val ∘ φ)
          (fun s => splittingFrame G e (φ s).val) s))
        (oS : SmoothOrientation (𝓡 2) S),
        (∀ (s : S) (b : Basis (Fin (finrank ℝ E2)) ℝ E2), b.orientation = oS.val s ↔
          (splitFrameBasis (Basis.singleton (Fin 1) ℝ) b lineSurfaceIndex
            (ambientSplitFrameEquiv 𝓘(ℝ, E3) (𝓡 2) (Subtype.val ∘ φ)
              (fun s => splittingFrame G e (φ s).val) hbij s).toLinearEquiv).orientation =
            (smoothOrientationOfManifoldOrientation (𝓡 3)
              (manifoldOrientationCast (by simp) oN)).val (φ s).val) ∧
        ∃ O : ManifoldOrientation (𝓡 2) S 2,
          O = manifoldOrientationCast (by simp)
            (Classical.choose (exists_manifoldOrientation_eq_of_smoothOrientation (𝓡 2) oS)) := by
  let _ := splittingFactorChartedSpace G hk hnorm e
  let _ := splittingFactor_isManifold_one G hk hnorm e
  obtain ⟨S, mS, cS, iS, φ, hφ, hφs, hbij, oS, hiff⟩ :=
    exists_oriented_smoothCarrier_splittingFactor G hk hnorm e splittingSurfaceModelEquiv
      (Basis.singleton (Fin 1) ℝ) lineSurfaceIndex
      (smoothOrientationOfManifoldOrientation (𝓡 3) (manifoldOrientationCast (by simp) oN))
  exact ⟨S, mS, cS, iS, φ, hφ, hφs, hbij, oS, hiff, _, rfl⟩

/-- The surface factor's carrier is orientable (the `Nonempty` form used by LFR17/LFR24). -/
theorem surfaceFactor_smoothCarrier_orientable {N W : Type u} [MetricSpace N] [ChartedSpace E3 N]
    [IsManifold 𝓘(ℝ, E3) ∞ N] [RiemannianBundle (fun x : N => TangentSpace 𝓘(ℝ, E3) x)]
    [IsRiemannianManifold 𝓘(ℝ, E3) N] [CompleteSpace N] [SecondCountableTopology N]
    [MetricSpace W] {k : ℕ}
    (G : ContMDiffRiemannianMetric 𝓘(ℝ, E3) (((k : ℕ∞) : ℕ∞ω) + 1) E3
      (TangentSpace 𝓘(ℝ, E3) : N → Type _))
    (hk : 2 ≤ (k : ℕ∞))
    (hnorm : ∀ (x : N) (v : TangentSpace 𝓘(ℝ, E3) x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (G.inner x v v)))
    (oN : ManifoldOrientation (𝓡 3) N 3) (e : N ≃ᵢ WithLp 2 (ℝ × W)) :
    letI := splittingFactorChartedSpace G hk hnorm e
    ∃ (S : Type u) (_ : MetricSpace S) (_ : ChartedSpace E2 S) (_ : IsManifold (𝓡 2) ∞ S)
      (φ : S ≃ₜ {x : N // (e x).fst = 0}),
      ContMDiff (𝓡 2) 𝓘(ℝ, P) ((k + 2 : ℕ) : ℕ∞ω) φ ∧
      ContMDiff 𝓘(ℝ, P) (𝓡 2) ((k + 2 : ℕ) : ℕ∞ω) φ.symm ∧
      Nonempty (ManifoldOrientation (𝓡 2) S 2) := by
  let _ := splittingFactorChartedSpace G hk hnorm e
  obtain ⟨S, mS, cS, iS, φ, hφ, hφs, -, -, -, O, -⟩ :=
    surfaceFactor_oriented_smoothCarrier G hk hnorm oN e
  exact ⟨S, mS, cS, iS, φ, hφ, hφs, ⟨O⟩⟩

end DifferentialGeometry.Geometry.Collapse
