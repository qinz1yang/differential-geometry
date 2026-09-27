/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.Manifold.RoundedCylinder
import DifferentialGeometry.Topology.Simplex.NormedBall
import DifferentialGeometry.Topology.PiecewiseLinear.PLBallSphere

open Set Metric Topology
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.PiecewiseLinear

open DifferentialGeometry.Manifold

noncomputable def prismBallHomeomorph :
    (stdSimplex ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1 : Set ((Fin 3 → ℝ) × ℝ)) ≃ₜ
      (closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 × Icc (0 : ℝ) 1) :=
  (_root_.Homeomorph.Set.prod _ _).trans
    (_root_.Homeomorph.prodCongr
      (DifferentialGeometry.Simplex.stdSimplexNormedBallHomeomorph
        (EuclideanSpace.equiv (Fin 2) ℝ).symm) (_root_.Homeomorph.refl _))

theorem prismBallHomeomorph_mem_sphere_iff
    (p : (stdSimplex ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1 : Set ((Fin 3 → ℝ) × ℝ))) :
    (prismBallHomeomorph p).1.val ∈ sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ↔
      p.val.1 ∈ stdSimplexBoundary 2 := by
  have h := DifferentialGeometry.Simplex.stdSimplexNormedBallHomeomorph_mem_sphere_iff
    (EuclideanSpace.equiv (Fin 2) ℝ).symm ⟨p.val.1, p.property.1⟩
  exact h.trans ⟨fun hp => ⟨p.property.1, hp⟩, fun hp => hp.2⟩

noncomputable def prismAnnulusSource : TopologicalSpace.Opens
    (stdSimplex ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1 : Set ((Fin 3 → ℝ) × ℝ)) where
  carrier := prismBallHomeomorph ⁻¹' ballPrismCollar (EuclideanSpace ℝ (Fin 2))
  is_open' := (ballPrismCollar _).isOpen.preimage prismBallHomeomorph.continuous

noncomputable def prismAnnulusHomeomorph :
    prismAnnulusSource ≃ₜ ballPrismCollar (EuclideanSpace ℝ (Fin 2)) :=
  prismBallHomeomorph.subtype (fun _ => Iff.rfl)

theorem mem_prismAnnulusSource_of_boundary
    (p : (stdSimplex ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1 : Set ((Fin 3 → ℝ) × ℝ)))
    (hp : p.val.1 ∈ stdSimplexBoundary 2) : p ∈ prismAnnulusSource := by
  have hn := mem_sphere_zero_iff_norm.mp ((prismBallHomeomorph_mem_sphere_iff p).mpr hp)
  change (prismBallHomeomorph p).1.val ≠ 0
  intro heq
  rw [heq, norm_zero] at hn
  norm_num at hn

@[instance_reducible]
noncomputable def prismAnnulusChartedSpace :
    ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanHalfSpace 2))
      prismAnnulusSource := by
  let _ := ballPrismCollarChartedSpace 1
  exact DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace prismAnnulusHomeomorph

theorem prismAnnulus_isManifold :
    let _ := prismAnnulusChartedSpace
    IsManifold ((𝓡 1).prod (𝓡∂ 2)) ∞ prismAnnulusSource := by
  let _ := ballPrismCollarChartedSpace 1
  let _ : IsManifold ((𝓡 1).prod (𝓡∂ 2)) ∞
      (ballPrismCollar (EuclideanSpace ℝ (Fin 2))) := ballPrismCollar_isManifold 1
  exact DifferentialGeometry.Manifold.Homeomorph.instIsManifoldPullback prismAnnulusHomeomorph

noncomputable def prismAnnulusDiffeomorph :
    let _ := ballPrismCollarChartedSpace 1
    let _ := prismAnnulusChartedSpace
    Diffeomorph ((𝓡 1).prod (𝓡∂ 2)) ((𝓡 1).prod (𝓡∂ 2))
      prismAnnulusSource (ballPrismCollar (EuclideanSpace ℝ (Fin 2))) ∞ := by
  let _ := ballPrismCollarChartedSpace 1
  let _ : IsManifold ((𝓡 1).prod (𝓡∂ 2)) ∞
      (ballPrismCollar (EuclideanSpace ℝ (Fin 2))) := ballPrismCollar_isManifold 1
  exact DifferentialGeometry.Manifold.Homeomorph.pullbackDiffeomorph prismAnnulusHomeomorph

theorem prismAnnulus_boundary_iff (p : prismAnnulusSource) :
    let _ := prismAnnulusChartedSpace
    p ∈ ((𝓡 1).prod (𝓡∂ 2)).boundary prismAnnulusSource ↔
      p.val.val.1 ∈ stdSimplexBoundary 2 ∨ p.val.val.2 = 0 ∨ p.val.val.2 = 1 := by
  let _ := ballPrismCollarChartedSpace 1
  let _ := prismAnnulusChartedSpace
  dsimp only
  rw [← prismAnnulusDiffeomorph.preimage_boundary (by simp)]
  change prismAnnulusHomeomorph p ∈ ((𝓡 1).prod (𝓡∂ 2)).boundary
    (ballPrismCollar (EuclideanSpace ℝ (Fin 2))) ↔ _
  have hb := ballPrismCollar_boundary_iff 1 (prismAnnulusHomeomorph p)
  dsimp only at hb
  rw [hb]
  exact or_congr (prismBallHomeomorph_mem_sphere_iff p.val) Iff.rfl

noncomputable def prismAnnulusChart
    (v : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) (upper : Bool) :
    OpenPartialHomeomorph prismAnnulusSource
      (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanHalfSpace 2)) :=
  prismAnnulusHomeomorph.toOpenPartialHomeomorph.trans (ballPrismCollarChart 1 v upper)

theorem prismAnnulusChart_mem_atlas
    (v : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) (upper : Bool) :
    let _ := prismAnnulusChartedSpace
    prismAnnulusChart v upper ∈
      atlas (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanHalfSpace 2)) prismAnnulusSource :=
  ⟨_, ballPrismCollarChart_mem_atlas 1 v upper, rfl⟩

theorem prismAnnulusChart_mem_source_iff
    (v : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) (i : Bool) (p : prismAnnulusSource) :
    p ∈ (prismAnnulusChart v i).source ↔
      ((ballPrismCollarHomeomorph _).symm (prismAnnulusHomeomorph p)).1 ≠ -v ∧
        if i then 0 < p.val.val.2 else p.val.val.2 < 1 := by
  let _ : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 1 + 1) := ⟨by simp⟩
  let q := (ballPrismCollarHomeomorph _).symm (prismAnnulusHomeomorph p)
  change (True ∧ True ∧ q.1 ∈ (stereographic' 1 (-v)).source ∧
    q.2 ∈ (halfOpenStripChart i).source) ↔ _
  rw [true_and, true_and, stereographic'_source, mem_compl_iff, mem_singleton_iff,
    mem_halfOpenStripChart_source]
  rfl

theorem prismAnnulusChart_cover (p : prismAnnulusSource) :
    ∃ v : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1, ∃ upper : Bool,
      p ∈ (prismAnnulusChart v upper).source := by
  obtain ⟨v, upper, hp⟩ := ballPrismCollarChart_cover 1 (prismAnnulusHomeomorph p)
  exact ⟨v, upper, trivial, hp⟩

theorem prismAnnulusChart_transition_mem
    (v w : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) (i j : Bool) :
    (prismAnnulusChart v i).symm.trans (prismAnnulusChart w j) ∈
      contDiffGroupoid ∞ ((𝓡 1).prod (𝓡∂ 2)) := by
  let _ := prismAnnulusChartedSpace
  let _ : IsManifold ((𝓡 1).prod (𝓡∂ 2)) ∞ prismAnnulusSource := prismAnnulus_isManifold
  exact (contDiffGroupoid ∞ ((𝓡 1).prod (𝓡∂ 2))).compatible
    (prismAnnulusChart_mem_atlas v i) (prismAnnulusChart_mem_atlas w j)

theorem prismAnnulusChart_attaching_iff
    (v : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) (i : Bool) (p : prismAnnulusSource) :
    p.val.val.1 ∈ stdSimplexBoundary 2 ↔
      (prismAnnulusChart v i p).2.val 0 = 0 ∧ (prismAnnulusChart v i p).2.val 1 ≤ 0 := by
  rw [← prismBallHomeomorph_mem_sphere_iff p.val]
  exact ballPrismCollarChart_attaching_iff 1 v i (prismAnnulusHomeomorph p)

end DifferentialGeometry.Topology.PiecewiseLinear
