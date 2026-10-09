import DifferentialGeometry.Analysis.InnerProductSpace.BufferedNormalGraphQuantitativeProjection
import DifferentialGeometry.Topology.Embedding.Lift
import DifferentialGeometry.Topology.Manifold.OpenSubtype
import DifferentialGeometry.Topology.Manifold.Submersion
import Mathlib.Geometry.Manifold.ContMDiffMap

set_option autoImplicit false
noncomputable section
open Set Metric DifferentialGeometry.Analysis
open scoped ContDiff Manifold

namespace DifferentialGeometry.Topology.Manifold

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_smooth_unique_nearest_submersion_buffered_normal_graph_with_bounds
    (W : Set H) [ChartedSpace E W] [IsManifold 𝓘(ℝ, E) ∞ W]
    (hW : _root_.Manifold.IsSmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, H) ∞
      (Subtype.val : W → H))
    (L : Submodule ℝ H) (hdim : Module.finrank ℝ L = Module.finrank ℝ E)
    (o : H) (g : L → Lᗮ) (R a : ℝ)
    (hR : 0 < R) (ha : a ≤ 1 / 100)
    (hg : ContDiffOn ℝ ∞ g (ball 0 (4 * R)))
    (hvalue : ∀ t ∈ ball (0 : L) (4 * R), ‖g t‖ ≤ a * R)
    (hfirst : ∀ t ∈ ball (0 : L) (4 * R), ‖fderiv ℝ g t‖ ≤ a)
    (hsecond : ∀ t ∈ ball (0 : L) (4 * R), ‖fderiv ℝ (fderiv ℝ g) t‖ ≤ a / R)
    (hgraph : ∀ t ∈ ball (0 : L) (4 * R),
      o + orthogonalCoordinateSum L (t, g t) ∈ W)
    (hsheet : ∀ y ∈ W ∩ ball o (3 * R), ∃ t ∈ ball (0 : L) (4 * R),
      y = o + orthogonalCoordinateSum L (t, g t)) :
    let U : TopologicalSpace.Opens H := ⟨ball o R, isOpen_ball⟩
    ∃ P : C^∞⟮𝓘(ℝ, H), U; 𝓘(ℝ, E), W⟯,
      _root_.Manifold.IsSubmersion 𝓘(ℝ, H) 𝓘(ℝ, E) ∞ P ∧
      ∀ z : U, IsMinOn (fun y => dist (z : H) y) W (P z : H) ∧
        (∀ y ∈ W, IsMinOn (fun w => dist (z : H) w) W y → y = (P z : H)) ∧
        ‖(P z : H) - (o + L.starProjection ((z : H) - o))‖ ≤ 3 * a * R ∧
        let D : H →L[ℝ] H := mfderiv 𝓘(ℝ, H) 𝓘(ℝ, H) (fun y : U => (P y : H)) z
        ‖D - L.starProjection‖ ≤ 7 * a := by
  classical
  let U : TopologicalSpace.Opens H := ⟨ball o R, isOpen_ball⟩
  obtain ⟨Q, hQ, hnearest⟩ := exists_smooth_unique_nearest_buffered_normal_graph_with_bounds
    L o g W R a hR ha hg hvalue hfirst hsecond hgraph hsheet
  let f : U → H := fun z => Q z
  have hf : ContMDiff 𝓘(ℝ, H) 𝓘(ℝ, H) ∞ f := by
    intro z
    exact contMDiffAt_subtype_iff.mpr
      ((hQ.contDiffAt (isOpen_ball.mem_nhds z.property)).contMDiffAt)
  have hrange : Set.range f ⊆ Set.range (Subtype.val : W → H) := by
    rintro y ⟨z, rfl⟩
    exact ⟨⟨Q z, (hnearest z z.property).1⟩, rfl⟩
  let P : C^∞⟮𝓘(ℝ, H), U; 𝓘(ℝ, E), W⟯ :=
    ⟨hW.lift f hrange, hW.contMDiff_lift hf hrange⟩
  have hval (z : U) : (P z : H) = Q z := hW.comp_lift hrange z
  let D : U → H →L[ℝ] H := fun z =>
    mfderiv 𝓘(ℝ, H) 𝓘(ℝ, H) (fun y : U => (P y : H)) z
  have hder (z : U) : D z = fderiv ℝ Q (z : H) := by
    have heq : (fun y : U => (P y : H)) = (fun y : U => Q y) := funext hval
    dsimp only [D]
    rw [heq, DifferentialGeometry.mfderiv_restrict_open Q U z, mfderiv_eq_fderiv]
    rfl
  have hsub : _root_.Manifold.IsSubmersion 𝓘(ℝ, H) 𝓘(ℝ, E) ∞ P := by
    apply isSubmersion_of_surjective_mfderiv P P.contMDiff
    intro z
    let A : E →L[ℝ] H := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, H) (Subtype.val : W → H) (P z)
    let B : H →L[ℝ] E := mfderiv 𝓘(ℝ, H) 𝓘(ℝ, E) P z
    have hinj : Function.Injective A :=
      (hW.isImmersion.isImmersionAt (P z)).mfderiv_injective (by simp)
    have hchain : D z = A.comp B := by
      exact mfderiv_comp z
        (hW.contMDiff.mdifferentiableAt (by simp))
        (P.contMDiff.mdifferentiableAt (by simp))
    have hcomp : A.comp B = fderiv ℝ Q (z : H) := hchain.symm.trans (hder z)
    have hrank : Module.finrank ℝ (LinearMap.range (A.comp B).toLinearMap) =
        Module.finrank ℝ E := by
      rw [hcomp]
      exact (hnearest z z.property).2.2.2.2.2.trans hdim
    have hle : LinearMap.range (A.comp B).toLinearMap ≤ LinearMap.range A.toLinearMap := by
      rintro y ⟨v, rfl⟩
      exact ⟨B v, rfl⟩
    have heq : LinearMap.range (A.comp B).toLinearMap = LinearMap.range A.toLinearMap :=
      Submodule.eq_of_le_of_finrank_eq hle
        (hrank.trans (LinearMap.finrank_range_of_inj hinj).symm)
    intro v
    have hv : A v ∈ LinearMap.range (A.comp B).toLinearMap := by
      rw [heq]
      exact ⟨v, rfl⟩
    obtain ⟨u, hu⟩ := hv
    exact ⟨u, hinj hu⟩
  refine ⟨P, hsub, ?_⟩
  intro z
  rcases hnearest z z.property with ⟨_, hmin, huniq, hvalbound, hderbound, _⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [hval z] using hmin
  · intro y hy hminy
    simpa only [hval z] using huniq y hy hminy
  · simpa only [hval z] using hvalbound
  · change ‖D z - L.starProjection‖ ≤ 7 * a
    rw [hder z]
    exact hderbound

end DifferentialGeometry.Topology.Manifold
