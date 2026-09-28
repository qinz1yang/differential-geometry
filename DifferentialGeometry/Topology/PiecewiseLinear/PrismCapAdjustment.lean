/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ConvexPrismBoundaryExtension
import DifferentialGeometry.Topology.PiecewiseLinear.ConvexPolytope
import DifferentialGeometry.Topology.PiecewiseLinear.PLHomeomorphTopology
import DifferentialGeometry.Topology.PiecewiseLinear.PrismBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.ConeMarkedPrism

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem IsPLHomeomorphOn.exists_prism_cap_images_preserving_axis
    (hdim : Module.finrank ℝ E = 2) {P : Set E} (hP : IsHPolytope P)
    {r : (Fin 3 → ℝ) → E} (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) P)
    (hp : r (stdCenter 1) ∈ interior P)
    {C D₀ D₁ : Set (EuclideanSpace ℝ (Fin 3))}
    {ρ : E × ℝ → EuclideanSpace ℝ (Fin 3)}
    (hρ : IsPLHomeomorphOn ρ (P ×ˢ Icc (0 : ℝ) 1) C)
    (hD₀ : D₀ ⊆ frontier C) (hD₁ : D₁ ⊆ frontier C) (hdis : Disjoint D₀ D₁)
    {r₀ r₁ : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)}
    (hr₀ : IsPLHomeomorphOn r₀ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₀)
    (hr₁ : IsPLHomeomorphOn r₁ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₁)
    (hρ0 : ρ (r (stdCenter 1), 0) = r₀ (stdCenter 1))
    (hρ1 : ρ (r (stdCenter 1), 1) = r₁ (stdCenter 1)) :
    ∃ σ : E × ℝ → EuclideanSpace ℝ (Fin 3),
      IsPLHomeomorphOn σ (P ×ˢ Icc (0 : ℝ) 1) C ∧
      σ '' (P ×ˢ {(0 : ℝ)}) = D₀ ∧ σ '' (P ×ˢ {(1 : ℝ)}) = D₁ ∧
      ∀ t ∈ Icc (0 : ℝ) 1, σ (r (stdCenter 1), t) = ρ (r (stdCenter 1), t) := by
  classical
  let Q := P ×ˢ Icc (0 : ℝ) 1
  let v := Function.invFunOn ρ Q
  have hQ : IsHPolytope Q := hP.prod isHPolytope_Icc
  have hPball : IsPLBall 2 P := ⟨r, hr⟩
  have hQball : IsPLBall 3 Q := isPLBall_three_prod hPball (isPLBall_Icc zero_lt_one)
  have hC : IsPLBall 3 C := hQball.of_isPLHomeomorphOn hρ
  have hv : IsPLHomeomorphOn v C Q := hρ.symm
  have hdimQ : Module.finrank ℝ (E × ℝ) = 3 := by
    rw [Module.finrank_prod, hdim]
    simp
  have hQint : (interior Q).Nonempty := by
    refine ⟨(r (stdCenter 1), (1 / 2 : ℝ)), ?_⟩
    rw [interior_prod_eq, interior_Icc]
    exact ⟨hp, by norm_num⟩
  have hS : IsPLSphere 2 (frontier Q) := hQ.isPLSphere_frontier hdimQ hQint
  have hdimF : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) =
      Module.finrank ℝ (E × ℝ) := by rw [hdimQ]; simp
  have hvfront : v '' frontier C = frontier Q :=
    hv.image_frontier hdimF hC.isPolyhedron.isClosed hQ.isClosed
  have hvD (D : Set (EuclideanSpace ℝ (Fin 3))) (hD : D ⊆ frontier C) :
      v '' D ⊆ frontier Q := (image_mono hD).trans hvfront.subset
  have hv₀ : IsPLHomeomorphOn v D₀ (v '' D₀) :=
    hv.restrict (IsPLBall.isPolyhedron ⟨r₀, hr₀⟩)
      (hD₀.trans hC.isPolyhedron.isClosed.frontier_subset)
  have hv₁ : IsPLHomeomorphOn v D₁ (v '' D₁) :=
    hv.restrict (IsPLBall.isPolyhedron ⟨r₁, hr₁⟩)
      (hD₁.trans hC.isPolyhedron.isClosed.frontier_subset)
  have hvdis : Disjoint (v '' D₀) (v '' D₁) := by
    apply disjoint_left.mpr
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hyx⟩
    have heq := hv.bijOn.injOn (hC.isPolyhedron.isClosed.frontier_subset (hD₁ hy))
      (hC.isPolyhedron.isClosed.frontier_subset (hD₀ hx)) hyx
    exact disjoint_left.mp hdis hx (heq ▸ hy)
  have hcap (a : ℝ) : IsPLHomeomorphOn (fun x => (r x, a))
      (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (P ×ˢ {a}) := hr.trans (hP.isPolyhedron.isPLHomeomorphOn_prod_const a)
  have hcapfront : ∀ a ∈ ({0, 1} : Set ℝ), P ×ˢ {a} ⊆ frontier Q := by
    intro a ha z hz
    rw [frontier_prod_eq, hP.isClosed.closure_eq, frontier_Icc zero_le_one]
    exact Or.inl ⟨hz.1, hz.2 ▸ ha⟩
  have hcapdis : Disjoint (P ×ˢ {(0 : ℝ)}) (P ×ˢ {(1 : ℝ)}) := by
    apply disjoint_left.mpr
    rintro z ⟨-, hz0⟩ ⟨-, hz1⟩
    have h01 : (0 : ℝ) = 1 := hz0.symm.trans hz1
    norm_num at h01
  let g₀ := (v ∘ r₀) ∘ Function.invFunOn (fun x => (r x, (0 : ℝ)))
    (Convexity.StdSimplex.coordinateSet ℝ (Fin 3))
  have hg₀ : IsPLHomeomorphOn g₀ (P ×ˢ {(0 : ℝ)}) (v '' D₀) :=
    (hcap 0).symm.trans (hr₀.trans hv₀)
  obtain ⟨f, hf, hfg, hfD₁, hfc⟩ :=
    exists_isPLHomeomorphOn_map_disk_pair_eqOn_disk_marked hS hS
      (hPball.of_isPLHomeomorphOn (hP.isPolyhedron.isPLHomeomorphOn_prod_const 0))
      (hcapfront 0 (Or.inl rfl)) (hcap 1) (hr₁.trans hv₁)
      (hcapfront 1 (Or.inr rfl)) (hvD D₁ hD₁) hcapdis hvdis hg₀ (hvD D₀ hD₀)
  have hpΔ : stdCenter 1 ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3) :=
    openSimplex_stdVertices_subset_stdSimplex (stdCenter_mem_openSimplex 1)
  have hpP := interior_subset hp
  have hv0 : v (r₀ (stdCenter 1)) = (r (stdCenter 1), 0) := by
    rw [← hρ0]
    exact hρ.bijOn.invOn_invFunOn.1 ⟨hpP, by norm_num⟩
  have hv1 : v (r₁ (stdCenter 1)) = (r (stdCenter 1), 1) := by
    rw [← hρ1]
    exact hρ.bijOn.invOn_invFunOn.1 ⟨hpP, by norm_num⟩
  have hf0 : f (r (stdCenter 1), 0) = (r (stdCenter 1), 0) := by
    rw [hfg (show (r (stdCenter 1), (0 : ℝ)) ∈ P ×ˢ {0} from ⟨hpP, rfl⟩)]
    change v (r₀ (Function.invFunOn (fun x => (r x, (0 : ℝ)))
      (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (r (stdCenter 1), 0))) = _
    rw [(hcap 0).bijOn.invOn_invFunOn.1 hpΔ]
    exact hv0
  have hf1 : f (r (stdCenter 1), 1) = (r (stdCenter 1), 1) := hfc.trans hv1
  obtain ⟨g, hg, hgf, hgp⟩ := exists_isPLHomeomorphOn_prism_fixed_axis hP hp hf hf0 hf1
  have hg₀im : g '' (P ×ˢ {(0 : ℝ)}) = v '' D₀ :=
    (hgf.mono (hcapfront 0 (Or.inl rfl))).image_eq.trans (hfg.image_eq.trans hg₀.image_eq)
  have hg₁im : g '' (P ×ˢ {(1 : ℝ)}) = v '' D₁ :=
    (hgf.mono (hcapfront 1 (Or.inr rfl))).image_eq.trans hfD₁
  have hρv (D : Set (EuclideanSpace ℝ (Fin 3))) (hD : D ⊆ frontier C) :
      ρ '' (v '' D) = D := by
    rw [image_image]
    exact (image_congr fun x hx =>
      hρ.bijOn.invOn_invFunOn.2 (hC.isPolyhedron.isClosed.frontier_subset (hD hx))).trans
        (image_id _)
  refine ⟨ρ ∘ g, hg.trans hρ, ?_, ?_, fun t ht => ?_⟩
  · rw [image_comp, hg₀im, hρv D₀ hD₀]
  · rw [image_comp, hg₁im, hρv D₁ hD₁]
  · change ρ (g (r (stdCenter 1), t)) = ρ (r (stdCenter 1), t)
    rw [hgp t ht]

end DifferentialGeometry.Topology.PiecewiseLinear
