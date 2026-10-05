import DifferentialGeometry.Topology.VectorBundle.LineSection
import DifferentialGeometry.Geometry.Collapse.FiniteSurface.ClosedSurfaceType

/-!
# The orientable compact surface rows for an actual rank-one bundle

The original finite-order metric classifies the base, and the produced smooth unit section
trivializes the original Riemannian bundle. Composing these actual maps gives the sphere and torus
product rows with their fibre norms; the torus branch retains flatness of the original metric.
-/

set_option autoImplicit false

noncomputable section

open Bundle Module
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.VectorBundle

private def trivialProductDiffeomorph {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H) (B : Type*) [TopologicalSpace B] [ChartedSpace H B] :
    (B × F) ≃ₘ⟮I.prod 𝓘(ℝ, F), I.prod 𝓘(ℝ, F)⟯ TotalSpace F (Trivial B F) where
  toFun z := ⟨z.1, z.2⟩
  invFun z := (z.proj, z.2)
  left_inv z := rfl
  right_inv z := rfl
  contMDiff_toFun := by
    intro z
    apply Bundle.contMDiffAt_totalSpace.mpr
    refine ⟨contMDiffAt_fst, ?_⟩
    simp only [Trivial.fiberBundle_trivializationAt', Trivial.trivialization_apply]
    change ContMDiffAt (I.prod 𝓘(ℝ, F)) 𝓘(ℝ, F) ∞ Prod.snd z
    exact contMDiffAt_snd
  contMDiff_invFun := by
    intro z
    let productTrivAtlas : MemTrivializationAtlas (Trivial.trivialization B F) :=
      ⟨Set.mem_singleton _⟩
    have h := (Trivial.trivialization B F).contMDiffOn (IB := I) (n := ∞)
    exact h.contMDiffAt (by simpa only [Trivial.trivialization_source] using Filter.univ_mem)

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {B : Type*} [TopologicalSpace B] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) B]
  [IsManifold (𝓡 2) ∞ B] [CompactSpace B] [T2Space B] [ConnectedSpace B]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ b, NormedAddCommGroup (V b)] [∀ b, InnerProductSpace ℝ (V b)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V (𝓡 2)]
  [IsContMDiffRiemannianBundle (𝓡 2) ∞ F V]

theorem exists_orientable_surface_line_rows (o : ManifoldOrientation (𝓡 2) B 2)
    {n : ℕ∞ω} (hn : (2 : ℕ∞ω) ≤ n)
    (k : ContMDiffRiemannianMetric (𝓡 2) n (EuclideanSpace ℝ (Fin 2))
      (TangentSpace (𝓡 2) : B → Type _))
    (hK : ∀ (b : B) (v w : TangentSpace (𝓡 2) b), 0 ≤ k.sectionalCurvature b v w)
    (hF : finrank ℝ F = 1)
    (hS : ¬ IsPreconnected {z : TotalSpace F V | ‖z.2‖ = 1}) :
    (∃ Ψ : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ×
        EuclideanSpace ℝ (Fin 1)) ≃ₘ⟮(𝓡 2).prod (𝓡 1),
          (𝓡 2).prod 𝓘(ℝ, F)⟯ TotalSpace F V,
      ∀ z, ‖(Ψ z).2‖ = ‖z.2‖) ∨
    ((∃ Ψ : ((AddCircle (1 : ℝ) × AddCircle (1 : ℝ)) ×
        EuclideanSpace ℝ (Fin 1)) ≃ₘ⟮
          (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod (𝓡 1),
          (𝓡 2).prod 𝓘(ℝ, F)⟯ TotalSpace F V,
      ∀ z, ‖(Ψ z).2‖ = ‖z.2‖) ∧
      ∀ (b : B) (v w : TangentSpace (𝓡 2) b), k.sectionalCurvature b v w = 0) := by
  obtain ⟨s, Φ, hΦ, hnorm, hu⟩ :=
    exists_line_trivialization_of_sphere_not_preconnected (IB := 𝓡 2) hF hS
  let Ψ := (trivialProductDiffeomorph (𝓡 2) B).trans Φ
  have hΨ (z : B × EuclideanSpace ℝ (Fin 1)) : ‖(Ψ z).2‖ = ‖z.2‖ :=
    hnorm ⟨z.1, z.2⟩
  rcases Geometry.Collapse.finiteSurface_sphere_or_flat_torus o hn k hK with h | ⟨h, hflat⟩
  · obtain ⟨e⟩ := h
    left
    exact ⟨(e.symm.prodCongr (Diffeomorph.refl (𝓡 1) (EuclideanSpace ℝ (Fin 1)) ∞)).trans Ψ,
      fun z => hΨ (e.symm z.1, z.2)⟩
  · obtain ⟨e⟩ := h
    right
    exact ⟨⟨(e.symm.prodCongr (Diffeomorph.refl (𝓡 1)
      (EuclideanSpace ℝ (Fin 1)) ∞)).trans Ψ, fun z => hΨ (e.symm z.1, z.2)⟩, hflat⟩

end DifferentialGeometry.Topology.VectorBundle
