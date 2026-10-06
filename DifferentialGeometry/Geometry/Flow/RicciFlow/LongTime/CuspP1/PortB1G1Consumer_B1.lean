import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Restriction.Collar

set_option autoImplicit false
noncomputable section

open Set Filter Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Topology DifferentialGeometry.Geometry
open scoped Topology ContDiff Manifold NNReal ENNReal

-- S-MY-PORT-B1 G1 consumer：`Plateau/Restriction/Collar`（C3，verbatim IMS03）的型检查。
-- 用 `morrey_exists_concentric_restrictions_surrounding_collisions` 取 r₀，
-- 再在 (r₀, 1) 里选 r = (r₀ + 1) / 2：restricted trace 仍是 smooth embedded loop，
-- 且 `affineSubdisk q 0 r` 仍是 Morrey disk（原 metric g 保留）。
example {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {γ : freeLoop M} {q : C(closedDisk, M)} (hq : IsMorreyDisk g γ q)
    {Q : ℂ → M} (hQ : SmoothDiskExtension (E := E) q Q)
    (hγ : IsSmoothEmbeddedLoop (E := E) γ)
    (hrank : ∀ z ∈ Metric.sphere (0 : ℂ) 1,
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Q z))
    (hseparate : ∀ z : closedDisk, ‖(z : ℂ)‖ < 1 →
      ∀ θ : loopCircle, q z ≠ γ θ) :
    ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧
      IsSmoothEmbeddedLoop (E := E) (diskTrace (affineSubdisk q 0 r)) ∧
      IsMorreyDisk g (diskTrace (affineSubdisk q 0 r)) (affineSubdisk q 0 r) := by
  obtain ⟨r₀, hr₀, hr₀1, -, -, hr⟩ :=
    IMS03Embeddedness.morrey_exists_concentric_restrictions_surrounding_collisions
      g hq hQ hγ hrank hseparate
  have h1 : r₀ < (r₀ + 1) / 2 := by linarith
  have h2 : (r₀ + 1) / 2 < 1 := by linarith
  obtain ⟨hloop, hmorrey, -, -⟩ := hr ((r₀ + 1) / 2) h1 h2
  exact ⟨(r₀ + 1) / 2, by linarith, h2, hloop, hmorrey⟩

end
