import DifferentialGeometry.Geometry.Neck.SpatialLevelGraph
import DifferentialGeometry.Topology.Manifold.GraphBandComplement
import DifferentialGeometry.Topology.Order.DisjointGraphs

set_option autoImplicit false
noncomputable section
open Set Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem exists_spatial_neck_return_annulus_tolerance :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ eps : ℝ, eps ≤ eta →
        ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
          [IsManifold I3 ∞ M] [T2Space M] [PreconnectedSpace M]
          (g : SmoothRiemannianMetric I3 M) (p p' : M)
          (nk : SpatialNeck g eps p) (nk' : SpatialNeck g eps p')
          (f : Sphere 2 → ℝ), ContMDiff I2 𝓘(ℝ) ∞ f →
          (∀ q, |f q| < 1 / 10) → f nk.center = 0 →
          ∀ (W : Set M) (a : ℝ), |a| ≤ 4 → closure (interior W) = W →
          frontier W = range (fun q => nk.map (q, f q)) ∪
            range (fun q => nk'.map (q, a)) →
          Disjoint (range (fun q => nk.map (q, f q)))
            (range (fun q => nk'.map (q, a))) →
          (∃ δ : ℝ, 0 < δ ∧ ∀ t, 0 < t → t < δ → nk.map (nk.center, t) ∉ W) →
          ∀ (v u : Sphere 2) (b : ℝ), f v < b → b ≤ 3 →
          nk.map (v, b) = nk'.map (u, a) →
          ∃ (η : Sphere 2 ≃ₘ⟮I2, I2⟯ Sphere 2) (h : Sphere 2 → ℝ)
            (A : PartialDiffeomorph IC I3 Cylinder M ∞),
            ContMDiff I2 𝓘(ℝ) ∞ h ∧ (∀ q, f q < h q) ∧
            (∀ q, |h q - b| < 1 / 10) ∧ h v = b ∧
            (univ ×ˢ Icc (0 : ℝ) 1 ⊆ A.source) ∧
            (∀ q t, A (q, t) = nk.map (q, f q + (h q - f q) * t)) ∧
            (∀ q, A (q, 0) = nk.map (q, f q)) ∧
            (∀ q, A (q, 1) = nk'.map (η q, a)) ∧
            IsCompact (A '' (univ ×ˢ Icc (0 : ℝ) 1)) ∧
            frontier (A '' (univ ×ˢ Icc (0 : ℝ) 1)) = frontier W ∧
            (A '' (univ ×ˢ Icc (0 : ℝ) 1)) ∩ W = frontier W ∧
            W ∪ A '' (univ ×ˢ Icc (0 : ℝ) 1) = univ := by
  obtain ⟨eta, heta, hgraph⟩ := exists_spatial_neck_level_graph_tolerance.{u}
  refine ⟨eta, heta, ?_⟩
  intro eps heps M _ _ _ _ _ g p p' nk nk' f hf hfsmall hfzero
    W a ha hregular hfront hdis hout v u b hfb hb hmeet
  have hbabs : |b| ≤ 4 := by
    rw [abs_le]
    exact ⟨by linarith [(abs_lt.mp (hfsmall v)).1], by linarith⟩
  obtain ⟨η, h, hh, hhsmall, hhv, hmem, heq⟩ :=
    hgraph eps heps M g p' p nk' nk u v a b ha hbabs hmeet.symm
  have hgraph_range : range (fun q => nk.map (q, h q)) =
      range (fun q => nk'.map (q, a)) := by
    ext x
    constructor
    · rintro ⟨q, hq⟩
      exact ⟨η q, (heq q).symm.trans hq⟩
    · rintro ⟨q, hq⟩
      obtain ⟨r, hr⟩ := η.surjective q
      refine ⟨r, (heq r).trans ?_⟩
      exact (congrArg (fun z => nk'.map (z, a)) (show η r = q from hr)).trans hq
  have hdis' : Disjoint (range fun q => nk.map (q, f q))
      (range fun q => nk.map (q, h q)) := hgraph_range.symm ▸ hdis
  let _ : ConnectedSpace (Sphere 2) := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp [ThreeSpace]))
      (0 : ThreeSpace) (by norm_num : (0 : ℝ) ≤ 1))
  have havoid : ∀ q, f q ≠ h q := by
    intro q hq
    exact Set.disjoint_left.mp hdis' ⟨q, rfl⟩
      ⟨q, congrArg nk.map (Prod.ext rfl hq.symm)⟩
  obtain ⟨_, _, horder, _⟩ := DifferentialGeometry.Topology.exists_least_graph_above
    (Set.finite_singleton ()) f (fun _ : Unit => h) hf.continuous
    (fun _ _ => hh.continuous)
    (by intro i hi j hj hij; exact (hij (Subsingleton.elim _ _)).elim)
    (fun _ _ => havoid) ⟨(), rfl, v, hhv.symm ▸ hfb⟩
  have hlen : (1 : ℝ) < eps⁻¹ :=
    (one_lt_inv₀ nk.eps_pos).mpr (nk.eps_small.trans (by norm_num))
  have hfmem (q : Sphere 2) : (q, f q) ∈ univ ×ˢ Ioo (-eps⁻¹) eps⁻¹ :=
    ⟨mem_univ _, by constructor <;> linarith [(abs_lt.mp (hfsmall q)).1,
      (abs_lt.mp (hfsmall q)).2]⟩
  have hsource : {z : Cylinder | f z.1 ≤ z.2 ∧ z.2 ≤ h z.1} ⊆ nk.map.source := by
    intro z hz
    exact nk.domain ⟨mem_univ _, (hfmem z.1).2.1.trans_le hz.1,
      hz.2.trans_lt (hmem z.1).2.2⟩
  have hfront' : frontier W = range (fun q => nk.map (q, f q)) ∪
      range (fun q => nk.map (q, h q)) := by rw [hgraph_range]; exact hfront
  have houtside : (nk.map '' {z : Cylinder | f z.1 < z.2 ∧ z.2 < h z.1} \ W).Nonempty := by
    obtain ⟨δ, hδ, houtside⟩ := hout
    have hhpos : 0 < h nk.center := hfzero ▸ horder nk.center
    let t := min δ (h nk.center) / 2
    have htpos : 0 < t := by dsimp only [t]; positivity
    have htδ : t < δ := by dsimp only [t]; linarith [min_le_left δ (h nk.center)]
    have hth : t < h nk.center := by dsimp only [t]; linarith [min_le_right δ (h nk.center)]
    exact ⟨nk.map (nk.center, t), ⟨(nk.center, t), ⟨hfzero ▸ htpos, hth⟩, rfl⟩,
      houtside t htpos htδ⟩
  obtain ⟨A, hA, hformula, hzero, hone, hcompact, hfrontA, hinter, hcover⟩ :=
    DifferentialGeometry.Topology.exists_graphBand_partialDiffeomorph_cover_of_frontier_eq
      nk.map f h hf hh horder hsource hregular hfront' houtside
  exact ⟨η, h, A, hh, horder, hhsmall, hhv, hA,
    fun q t => hformula (q, t), hzero, fun q => (hone q).trans (heq q),
    hcompact, hfrontA, hinter, hcover⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
