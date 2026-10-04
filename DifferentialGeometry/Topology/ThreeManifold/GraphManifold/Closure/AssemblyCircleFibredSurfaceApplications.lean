import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCircleFibredSurface
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySeamCollar

/-!
# Consumer of B2-param: torus seams of circle-fibred regular faces

`exists_torusSeam_of_circle_fibred_level`: a compact oriented surface fibred over the circle with
connected fibres, smoothly embedded in a regular interior level, gets a B2 torus seam whose zero
section is the embedding composed with the B2-param torus parametrization (the "three producers of
parametrizations" route of the design, §3 B2-interior).
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

/-- **B2 torus seam of a circle-fibred regular face.** A compact oriented surface fibred over the
circle with connected fibres, smoothly embedded in a regular level of `f` inside the interior, gets
a torus seam: B2-param gives the torus parametrization `e` (projection = first factor), and the
signed collar of the embedded surface (`exists_signedCollar_of_isolated_level`, isolation from
`exists_isolating_open_of_regular_level`) is reparametrized by `e`. -/
theorem exists_torusSeam_of_circle_fibred_level (W : CompactCarrier.{u})
    (U : TopologicalSpace.Opens W.Carrier) (hU : (U : Set W.Carrier) ⊆ W.interior)
    (f : W.Carrier → ℝ) (c : ℝ) (hf : ContMDiffOn W.model 𝓘(ℝ, ℝ) ∞ f U)
    {S : Type u} [TopologicalSpace S] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    [IsManifold (𝓡 2) ∞ S] [CompactSpace S] [T2Space S]
    (o : ManifoldOrientation (𝓡 2) S 2) (p : S → Circle) (hp : ContMDiff (𝓡 2) (𝓡 1) ∞ p)
    (hsub : ∀ x, Surjective (mfderiv (𝓡 2) (𝓡 1) p x)) (hfib : ∀ z, IsConnected (p ⁻¹' {z}))
    (ι : S → W.Carrier) (hι : IsSmoothEmbedding (𝓡 2) W.model ∞ ι) (hιU : range ι ⊆ U)
    (hlev : ∀ x, f (ι x) = c) (hreg : ∀ x, mfderiv W.model 𝓘(ℝ, ℝ) f (ι x) ≠ 0)
    (V : Set W.Carrier) (hV : IsOpen V) (hιV : range ι ⊆ V) :
    ∃ (e : Torus ≃ₘ⟮torusModel, 𝓡 2⟯ S) (δ : ℝ) (_ : 0 < δ) (T : TorusSeam W),
      (∀ t, p (e t) = t.1) ∧ T.collar.target ⊆ V ∩ U ∧ (∀ t, T.collar (t, 0) = ι (e t)) ∧
      ∀ q ∈ signedCollarSource, f (T.collar q) = c + δ * q.2 := by
  obtain ⟨e, he⟩ := exists_torus_param_of_circle_fibred_surface o p hp hsub hfib
  have : Nonempty S := ⟨e (1, 1)⟩
  have hιU' : range ι ⊆ W.pieceInterior U := fun x hx => ⟨hιU hx, hU (hιU hx)⟩
  obtain ⟨V₀, hV₀, hιV₀, hiso⟩ := exists_isolating_open_of_regular_level (by simp) W U f c
    (hf.mono fun x hx => hx.1) ι hι hιU' hlev hreg
  let O : TopologicalSpace.Opens W.Carrier := ⟨V ∩ V₀ ∩ U, (hV.inter hV₀).inter U.isOpen⟩
  have hOsub : (W.pieceInterior O : Set W.Carrier) ⊆ V ∩ V₀ ∩ U := fun x hx => hx.1
  have hιO : range ι ⊆ W.pieceInterior O :=
    fun x hx => ⟨⟨⟨hιV hx, hιV₀ hx⟩, hιU hx⟩, hU (hιU hx)⟩
  obtain ⟨δ, hδ, Φ, hsrc, htgt, hzero, hval⟩ := exists_signedCollar_of_isolated_level W O f c
    (hf.mono fun x hx => (hOsub hx).2) ι hι hιO hlev
    (fun x hx hfx => hiso x ⟨(hOsub hx).1.2, ⟨(hOsub hx).2, hU (hOsub hx).2⟩⟩ hfx) hreg
  let R : (Torus × ℝ) ≃ₘ⟮signedCollarModel, (𝓡 2).prod 𝓘(ℝ, ℝ)⟯ (S × ℝ) :=
    e.prodCongr (Diffeomorph.refl 𝓘(ℝ, ℝ) ℝ ∞)
  let C : PartialDiffeomorph signedCollarModel W.model (Torus × ℝ) W.Carrier ∞ :=
    R.toPartialDiffeomorph.trans Φ
  have hCsrc : C.source = signedCollarSource := by
    ext q
    change (q ∈ univ ∧ R q ∈ Φ.source) ↔ -1 < q.2 ∧ q.2 < 1
    rw [hsrc]
    constructor
    · rintro ⟨-, -, h⟩
      exact h
    · intro h
      exact ⟨mem_univ _, mem_univ _, h⟩
  have hCtgt : C.target ⊆ W.pieceInterior O := fun y hy => htgt hy.1
  refine ⟨e, δ, hδ, ⟨C, hCsrc, fun y hy => (hCtgt hy).2⟩, he,
    fun y hy => ⟨(hOsub (hCtgt hy)).1.1, (hOsub (hCtgt hy)).2⟩, fun t => hzero (e t), ?_⟩
  intro q hq
  have hq' : R q ∈ Φ.source := by
    rw [hsrc]
    exact ⟨mem_univ _, hq.1, hq.2⟩
  exact hval (R q) hq'

end GC.GraphManifold.Assembly
