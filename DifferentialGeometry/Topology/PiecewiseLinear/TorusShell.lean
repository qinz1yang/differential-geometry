/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.TorusCompression
import DifferentialGeometry.Topology.PiecewiseLinear.SphericalShell

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Classical in
theorem exists_embedded_torus_compression_in_spherical_shell :
    ∃ (f : (Fin 3 → ℝ) × ℝ → EuclideanSpace ℝ (Fin 3))
      (K R P : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
      (hKfin : K.faces.Finite) (hRfin : R.faces.Finite) (hPfin : P.faces.Finite),
      letI := hKfin.to_subtype
      letI := hRfin.to_subtype
      letI := hPfin.to_subtype
      let J := stdSimplexBoundary 2
      let C := f '' (J ×ˢ {(1 / 4 : ℝ)})
      let W := f '' (J ×ˢ Icc (0 : ℝ) (1 / 2))
      let D₀ := f '' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ {(0 : ℝ)})
      let D₁ := f '' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ {(1 / 2 : ℝ)})
      let D := f '' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ {(1 / 4 : ℝ)})
      IsCombinatorialManifold 2 K ∧ IsConnected K.space ∧
      Nonempty (K.space ≃ₜ (loopCircle × loopCircle)) ∧
      K.space = f '' (J ×ˢ Icc (0 : ℝ) 1) ∧
      IsCombinatorialManifoldWithBoundary 2 R ∧ IsConnected R.space ∧
      R.space = closure (K.space \ W) ∧ W ∪ R.space = K.space ∧
      W ∩ R.space = f '' (J ×ˢ {(0 : ℝ), 1 / 2}) ∧
      (boundaryComplex 2 R).space = f '' (J ×ˢ {(0 : ℝ), 1 / 2}) ∧
      IsPLHomeomorphOn f (J ×ˢ Icc (0 : ℝ) (1 / 2)) W ∧
      IsPLSphere 1 C ∧ (∀ x ∈ C, W ∈ 𝓝[K.space] x) ∧
      (∃ hCK : C ⊆ K.space,
        ¬ (⟨Set.inclusion hCK, continuous_inclusion hCK⟩ : C(C, K.space)).Nullhomotopic) ∧
      IsConnected (K.space \ C) ∧
      IsPLHomeomorphOn (fun x => f (x, 1 / 4)) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D ∧
      K.space ∩ D = C ∧
      IsPLHomeomorphOn (fun x => f (x, 0)) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₀ ∧
      IsPLHomeomorphOn (fun x => f (x, 1 / 2)) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₁ ∧
      Disjoint D₀ D₁ ∧
      K.space ∩ D₀ = (fun x => f (x, 0)) '' stdSimplexBoundary 2 ∧
      K.space ∩ D₁ = (fun x => f (x, 1 / 2)) '' stdSimplexBoundary 2 ∧
      R.space ∩ D₀ = (fun x => f (x, 0)) '' stdSimplexBoundary 2 ∧
      R.space ∩ D₁ = (fun x => f (x, 1 / 2)) '' stdSimplexBoundary 2 ∧
      (fun x => f (x, 0)) '' stdSimplexBoundary 2 = f '' (J ×ˢ {(0 : ℝ)}) ∧
      (fun x => f (x, 1 / 2)) '' stdSimplexBoundary 2 = f '' (J ×ˢ {(1 / 2 : ℝ)}) ∧
      IsPLSphere 2 P.space ∧ P.space = R.space ∪ D₀ ∪ D₁ ∧
      Homology.bettiOne K.space = 2 ∧ Homology.bettiOne P.space = 0 ∧
      Homology.bettiOne P.space < Homology.bettiOne K.space ∧
      ∃ (q : EuclideanSpace ℝ (Fin 3)) (a b : ℝ), 0 < a ∧ a < b ∧
        let X := {x : EuclideanSpace ℝ (Fin 3) | dist x q ∈ Icc a b}
        IsSphericalShell X (Metric.sphere q a) (Metric.sphere q b) ∧
        IsPLBall 3 (f '' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (0 : ℝ) (1 / 2))) ∧
        f '' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (0 : ℝ) (1 / 2)) ⊆ interior X ∧
        K.space ⊆ interior X ∧ P.space ⊆ interior X ∧ D ⊆ interior X ∧
        Separates K.space (Metric.sphere q a) (Metric.sphere q b) ∧
        Separates P.space (Metric.sphere q a) (Metric.sphere q b) := by
  obtain ⟨f, K, R, P, hKfin, hRfin, hPfin, hK, hKc, htorus, hKsp, hR, hRc, hRcl,
    hcover, htrace, hRbd, hW, hC, hWnhds, hn, hCc, hDmid, hDmeet, hr₀, hr₁, hdis,
    hKmeet₀, hKmeet₁, hmeet₀, hmeet₁, hbd₀, hbd₁, hP, hPsp, hβK, hβP, hlt, hregion⟩ :=
      exists_embedded_torus_compression_separating_points
  obtain ⟨N, q', z, hNfin, hN, hsolid, hf, hends, hKfront, hball, hPfront,
    hq, -, -, -, -⟩ := hregion
  let _ : Finite N.faces := hNfin.to_subtype
  have hBsub : f '' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (1 / 2 : ℝ) 1) ⊆ N.space := by
    rw [← hf.image_eq]
    exact image_mono (fun _ hx => ⟨hx.1, le_trans (by norm_num) hx.2.1, hx.2.2⟩)
  obtain ⟨q, a, b, ha, hab, hshell, -, -, hremaining, hNint, hBint, hsepN, hsepB⟩ :=
    exists_isSphericalShell_separating_frontiers (isPolyhedron_space N).isCompact
      hBsub ⟨q', hq⟩
  let X := {x : EuclideanSpace ℝ (Fin 3) | dist x q ∈ Icc a b}
  have hLsub : f '' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (0 : ℝ) (1 / 2)) ⊆ N.space := by
    rw [← hf.image_eq]
    exact image_mono (fun _ hx => ⟨hx.1, hx.2.1, le_trans hx.2.2 (by norm_num)⟩)
  have hLavoid : f '' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (0 : ℝ) (1 / 2)) ⊆
      (interior (f '' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (1 / 2 : ℝ) 1)))ᶜ := by
    intro x hx hxB
    have hcaps := (hf.image_strip_inter (a := 1 / 2) (by norm_num)).subset
      ⟨hx, interior_subset hxB⟩
    have hxP : x ∈ P.space := by
      rw [hPsp]
      rcases hcaps with h₀ | h₁
      · exact Or.inl (Or.inr h₀)
      · exact Or.inr h₁
    exact (hPfront.subset hxP).2 hxB
  have hLInt : f '' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (0 : ℝ) (1 / 2)) ⊆ interior X :=
    fun x hx => hremaining ⟨hLsub hx, hLavoid hx⟩
  have hLball : IsPLBall 3 (f '' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (0 : ℝ) (1 / 2))) :=
    (isPLBall_three_prod (isPLBall_stdSimplex 2)
      (isPLBall_Icc (by norm_num : (0 : ℝ) < 1 / 2))).of_isPLHomeomorphOn
      (hf.isPLHomeomorphOn_strip (isPLBall_stdSimplex 2).isPolyhedron
        le_rfl (by norm_num) (Or.inr (by norm_num)))
  have hDsub : Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ {(1 / 4 : ℝ)} ⊆
      Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (0 : ℝ) (1 / 2) :=
    fun _ hx => ⟨hx.1, hx.2.symm ▸ by norm_num⟩
  exact ⟨f, K, R, P, hKfin, hRfin, hPfin, hK, hKc, htorus, hKsp, hR, hRc, hRcl,
    hcover, htrace, hRbd, hW, hC, hWnhds, hn, hCc, hDmid, hDmeet, hr₀, hr₁, hdis,
    hKmeet₀, hKmeet₁, hmeet₀, hmeet₁, hbd₀, hbd₁, hP, hPsp, hβK, hβP, hlt,
    q, a, b, ha, hab, hshell, hLball, hLInt,
    hKfront.subset.trans hNint, hPfront.subset.trans hBint,
    (image_mono hDsub).trans hLInt, hKfront.symm ▸ hsepN, hPfront.symm ▸ hsepB⟩

end DifferentialGeometry.Topology.PiecewiseLinear
