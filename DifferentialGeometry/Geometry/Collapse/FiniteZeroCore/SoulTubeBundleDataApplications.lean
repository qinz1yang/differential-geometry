import DifferentialGeometry.Geometry.Collapse.FiniteZeroCore.SoulTubeBundleData
import DifferentialGeometry.Geometry.Collapse.FiniteZeroCore.IsometryTransport
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.NormalFlowMap

/-!
# Consumers of LFR49 (c) and (d)

* `exists_finite_soul_diffeomorph_dim_three` ((c) + the restated LFR46): every complete connected
  noncompact three-manifold with a `C^{r+1}` metric (`3 ≤ r`) of `sec ≥ 0` is `C^{r-2}`-diffeomorphic
  to the total space of a smooth Riemannian vector bundle over a compact smooth manifold, with
  `dim B + rank = 3` — the finite-order soul theorem in dimension three, every soul dimension.
* `pointedGHConverges_isometryEquiv_iff`, `hcone_isometryEquiv_iff` ((d) both ways).
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter Function Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Geometry.FiniteSoul
open GC.MetricGeometry

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

section Soul

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M] [CompleteSpace M]

/-- **The finite-order soul theorem in dimension three.** -/
theorem exists_finite_soul_diffeomorph_dim_three [NoncompactSpace M] [ConnectedSpace M]
    (hdim : Module.finrank ℝ E = 3) {r : ℕ∞} (hr : 3 ≤ r)
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂) :
    ∃ (EB : Type) (_ : NormedAddCommGroup EB) (_ : NormedSpace ℝ EB) (_ : FiniteDimensional ℝ EB)
      (B : Type) (_ : TopologicalSpace B) (_ : ChartedSpace EB B) (_ : IsManifold 𝓘(ℝ, EB) ∞ B)
      (_ : CompactSpace B)
      (F : Type) (_ : NormedAddCommGroup F) (_ : InnerProductSpace ℝ F) (_ : FiniteDimensional ℝ F)
      (V : B → Type) (_ : ∀ s, NormedAddCommGroup (V s)) (_ : ∀ s, InnerProductSpace ℝ (V s))
      (_ : TopologicalSpace (TotalSpace F V)) (_ : FiberBundle F V) (_ : VectorBundle ℝ F V)
      (_ : ContMDiffVectorBundle ∞ F V 𝓘(ℝ, EB)) (_ : IsContMDiffRiemannianBundle 𝓘(ℝ, EB) ∞ F V),
      Module.finrank ℝ EB + Module.finrank ℝ F = 3 ∧
      Nonempty (TotalSpace F V ≃ₘ^((r - 2 : ℕ∞) : ℕ∞ω)⟮𝓘(ℝ, EB).prod 𝓘(ℝ, F), I⟯ M) := by
  have instNZ_LFR49 : NeZero (Module.finrank ℝ E) := ⟨by rw [hdim]; norm_num⟩
  obtain ⟨S, ε, ψ, EB, i1, i2, i3, B, i4, i5, i6, i7, F, i8, i9, i10, V, i11, i12, i13, i14, i15,
      i16, i17, b, ι, hdimP, hSc, hSne, hout, hε, hψs, hψ, hψexp, hdS, hbinj, hbS, hbinv, hι, hιb,
      hιlin, hιnorm, hιν, hιonto⟩ := exists_finite_soul_tube_bundle_data_dim_three hdim hr g hnorm hsec
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, e, -⟩ :=
    exists_finite_normalFlowMap_tube g hr hnorm hsec hSc hSne hout hε ψ hψs hψ hψexp hdS b hbinj hbS
      hbinv ι hι hιb hιlin hιnorm hιν hιonto hSne.some
  exact ⟨EB, i1, i2, i3, B, i4, i5, i6, i7, F, i8, i9, i10, V, i11, i12, i13, i14, i15, i16, i17,
    hdimP, ⟨e⟩⟩

end Soul

section Metric

/-- **(d2) both ways.** -/
theorem pointedGHConverges_isometryEquiv_iff {Y : ℕ → Type*} [∀ i, MetricSpace (Y i)]
    {N N' : Type*} [MetricSpace N] [MetricSpace N'] (κ : N' ≃ᵢ N) {P : ∀ i, Y i} {q : N} :
    PointedGHConverges P (κ.symm q) ↔ PointedGHConverges P q := by
  refine ⟨fun h => ?_, pointedGHConverges_of_isometryEquiv κ⟩
  have h' := pointedGHConverges_of_isometryEquiv κ.symm h
  rwa [IsometryEquiv.symm_symm, IsometryEquiv.apply_symm_apply] at h'

/-- **(d1) both ways.** -/
theorem hcone_isometryEquiv_iff {N N' C : Type*} [mN : MetricSpace N] [mN' : MetricSpace N']
    [mC : MetricSpace C] (κ : N' ≃ᵢ N) {q : N} {o : C} :
    (∀ τ : ℝ, 0 < τ → τ < 1 → ∃ R₀ : ℝ, ∀ R : ℝ, ∀ hR : 0 < R, R₀ ≤ R →
      Nonempty (@KleinerLottApprox N' C (mN'.rescale R⁻¹ (inv_pos.mpr hR)) mC (κ.symm q) o τ)) ↔
    (∀ τ : ℝ, 0 < τ → τ < 1 → ∃ R₀ : ℝ, ∀ R : ℝ, ∀ hR : 0 < R, R₀ ≤ R →
      Nonempty (@KleinerLottApprox N C (mN.rescale R⁻¹ (inv_pos.mpr hR)) mC q o τ)) := by
  refine ⟨fun h => ?_, hcone_of_isometryEquiv κ⟩
  have h' := hcone_of_isometryEquiv (q := κ.symm q) κ.symm h
  simpa only [IsometryEquiv.symm_symm, IsometryEquiv.apply_symm_apply] using h'

end Metric

end DifferentialGeometry.Geometry.Collapse
