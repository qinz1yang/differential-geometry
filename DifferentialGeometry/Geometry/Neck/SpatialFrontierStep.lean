import DifferentialGeometry.Geometry.Neck.SpatialReturnAnnulus
import DifferentialGeometry.Topology.OpenPartialHomeomorph.CollarAdvance

set_option autoImplicit false
noncomputable section
open Set Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem exists_spatial_neck_advance_or_return_tolerance :
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
          (∃ A : PartialDiffeomorph IC I3 Cylinder M ∞,
            (univ ×ˢ Icc (0 : ℝ) 1 ⊆ A.source) ∧
            (∀ q t, A (q, t) = nk.map (q, f q + (3 - f q) * t)) ∧
            (∀ q, A (q, 0) = nk.map (q, f q)) ∧
            (∀ q, A (q, 1) = nk.map (q, 3)) ∧
            IsCompact (A '' (univ ×ˢ Icc (0 : ℝ) 1)) ∧
            (A '' (univ ×ˢ Icc (0 : ℝ) 1)) ∩ W = range (fun q => nk.map (q, f q)) ∧
            closure (interior (W ∪ A '' (univ ×ˢ Icc (0 : ℝ) 1))) =
              W ∪ A '' (univ ×ˢ Icc (0 : ℝ) 1) ∧
            frontier (W ∪ A '' (univ ×ˢ Icc (0 : ℝ) 1)) =
              range (fun q => nk'.map (q, a)) ∪ range (fun q => nk.map (q, 3)) ∧
            nk.map '' (univ ×ˢ Icc (1 : ℝ) 2) ⊆
              (A '' (univ ×ˢ Icc (0 : ℝ) 1)) \ W) ∨
          (∃ (η : Sphere 2 ≃ₘ⟮I2, I2⟯ Sphere 2)
            (A : PartialDiffeomorph IC I3 Cylinder M ∞),
            (univ ×ˢ Icc (0 : ℝ) 1 ⊆ A.source) ∧
            (∀ q, A (q, 0) = nk.map (q, f q)) ∧
            (∀ q, A (q, 1) = nk'.map (η q, a)) ∧
            IsCompact (A '' (univ ×ˢ Icc (0 : ℝ) 1)) ∧
            (A '' (univ ×ˢ Icc (0 : ℝ) 1)) ∩ W = frontier W ∧
            W ∪ A '' (univ ×ˢ Icc (0 : ℝ) 1) = univ) := by
  obtain ⟨eta, heta, hreturn⟩ := exists_spatial_neck_return_annulus_tolerance.{u}
  refine ⟨eta, heta, ?_⟩
  intro eps heps M _ _ _ _ _ g p p' nk nk' f hf hfsmall hfzero
    W a ha hregular hfront hdis hout
  let _ : ConnectedSpace (Sphere 2) := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp [ThreeSpace]))
      (0 : ThreeSpace) (by norm_num : (0 : ℝ) ≤ 1))
  let S := range (fun q : Sphere 2 => nk'.map (q, a))
  let B := nk.map '' {z : Cylinder | f z.1 ≤ z.2 ∧ z.2 ≤ 3}
  by_cases hmeet : (B ∩ S).Nonempty
  · right
    obtain ⟨y, ⟨⟨v, b⟩, hb, rfl⟩, u, hu⟩ := hmeet
    have hfb : f v < b := by
      rcases eq_or_lt_of_le hb.1 with he | he
      · have hpoint : nk.map (v, f v) = nk.map (v, b) :=
          congrArg nk.map (show (v, f v) = (v, b) from Prod.ext rfl he)
        exact (Set.disjoint_left.mp hdis ⟨v, rfl⟩ ⟨u, hu.trans hpoint.symm⟩).elim
      · exact he
    obtain ⟨η, h, A, _, _, _, _, hA, _, hzero, hone, hc, _, hinter, hcover⟩ :=
      hreturn eps heps M g p p' nk nk' f hf hfsmall hfzero W a ha
        hregular hfront hdis hout v u b hfb hb.2 hu.symm
    exact ⟨η, A, hA, hzero, hone, hc, hinter, hcover⟩
  · left
    have hlen : (3 : ℝ) < eps⁻¹ :=
      (lt_inv_comm₀ (by norm_num) nk.eps_pos).mpr (by linarith [nk.eps_small])
    have hsource : {z : Cylinder | z.2 ∈ uIcc (f z.1) 3} ⊆ nk.map.source := by
      intro z hz
      change z.2 ∈ uIcc (f z.1) 3 at hz
      rw [uIcc_of_le (by linarith [(abs_lt.mp (hfsmall z.1)).2])] at hz
      exact nk.domain ⟨mem_univ _, by linarith [hz.1, (abs_lt.mp (hfsmall z.1)).1],
        hz.2.trans_lt hlen⟩
    obtain ⟨A, hA, hformula, hrange, hcompact, _⟩ :=
      DifferentialGeometry.Topology.exists_graphBand_partialDiffeomorph nk.map f
        (fun _ => 3) hf contMDiff_const (fun q => by linarith [(abs_lt.mp (hfsmall q)).2])
        hsource
    have hzero (q) : A (q, 0) = nk.map (q, f q) := by rw [hformula]; simp
    have hone (q) : A (q, 1) = nk.map (q, 3) := by rw [hformula]; simp
    have hB : A '' (univ ×ˢ Icc (0 : ℝ) 1) = B := by
      rw [hrange]
      congr 1
      ext z
      change (z.2 ∈ uIcc (f z.1) 3) ↔ f z.1 ≤ z.2 ∧ z.2 ≤ 3
      rw [uIcc_of_le (by linarith [(abs_lt.mp (hfsmall z.1)).2]), mem_Icc]
    have hlen4 : (4 : ℝ) < eps⁻¹ :=
      (lt_inv_comm₀ (by norm_num) nk'.eps_pos).mpr (by linarith [nk'.eps_small])
    have hSclosed : IsClosed S := by
      apply IsCompact.isClosed
      apply isCompact_range
      exact nk'.map.contMDiffOn_toFun.continuousOn.comp_continuous
        (continuous_id.prodMk continuous_const)
        (fun q => nk'.domain ⟨mem_univ _, by constructor <;>
          linarith [(abs_le.mp ha).1, (abs_le.mp ha).2]⟩)
    have hface (t : ℝ) : A '' (univ ×ˢ ({t} : Set ℝ)) = range (fun q => A (q, t)) := by
      ext y
      constructor
      · rintro ⟨⟨q, s⟩, ⟨_, hs⟩, rfl⟩
        have : s = t := hs
        subst s
        exact ⟨q, rfl⟩
      · rintro ⟨q, rfl⟩
        exact ⟨(q, t), ⟨mem_univ _, rfl⟩, rfl⟩
    have hfrontA : frontier W = A '' (univ ×ˢ ({0} : Set ℝ)) ∪ S := by
      rw [hface, show (fun q => A (q, 0)) = (fun q => nk.map (q, f q)) from funext hzero]
      exact hfront
    have havoid : Disjoint S (A '' (univ ×ˢ Icc (0 : ℝ) 1)) := by
      rw [hB, disjoint_left]
      intro x hxS hxB
      exact hmeet ⟨x, hxB, hxS⟩
    have hseed : (A '' (univ ×ˢ Ioo (0 : ℝ) 1) ∩ Wᶜ).Nonempty := by
      obtain ⟨δ, hδ, houtside⟩ := hout
      let t := min δ 1 / 2
      have ht : 0 < t := by dsimp only [t]; positivity
      have htδ : t < δ := by dsimp only [t]; linarith [min_le_left δ 1]
      have ht3 : t < 3 := by dsimp only [t]; linarith [min_le_right δ 1]
      refine ⟨nk.map (nk.center, t), ⟨(nk.center, t / 3),
        ⟨mem_univ _, by constructor <;> linarith⟩, ?_⟩, houtside t ht htδ⟩
      rw [hformula, hfzero]
      congr 1
      exact Prod.ext rfl (show 0 + (3 - 0) * (t / 3) = t by ring)
    obtain ⟨hinter, hreg, hnewfront⟩ := A.toOpenPartialHomeomorph.closed_cylinder_advance
      (by norm_num : (0 : ℝ) < 1) hA hregular hSclosed hfrontA havoid hseed
    change A '' (univ ×ˢ Icc (0 : ℝ) 1) ∩ W =
      A '' (univ ×ˢ ({0} : Set ℝ)) at hinter
    change closure (interior (A '' (univ ×ˢ Icc (0 : ℝ) 1) ∪ W)) =
      A '' (univ ×ˢ Icc (0 : ℝ) 1) ∪ W at hreg
    change frontier (A '' (univ ×ˢ Icc (0 : ℝ) 1) ∪ W) =
      S ∪ A '' (univ ×ˢ ({1} : Set ℝ)) at hnewfront
    refine ⟨A, hA, fun q t => hformula (q, t), hzero, hone, hcompact, ?_, ?_, ?_, ?_⟩
    · rw [hinter, hface]
      congr 1
      exact funext hzero
    · simpa only [union_comm] using hreg
    · rw [hface] at hnewfront
      have he : (fun q => A (q, 1)) = (fun q => nk.map (q, 3)) := funext hone
      rw [he, union_comm (A '' (univ ×ˢ Icc (0 : ℝ) 1)) W] at hnewfront
      exact hnewfront
    · rintro x ⟨⟨q, t⟩, ht, rfl⟩
      have htB : nk.map (q, t) ∈ B :=
        ⟨(q, t), ⟨by linarith [(abs_lt.mp (hfsmall q)).2, ht.2.1], by linarith [ht.2.2]⟩, rfl⟩
      refine ⟨hB.symm ▸ htB, ?_⟩
      intro hxW
      have hl := hinter ▸ (show nk.map (q, t) ∈ A '' (univ ×ˢ Icc (0 : ℝ) 1) ∩ W from
        ⟨hB.symm ▸ htB, hxW⟩)
      rw [hface] at hl
      obtain ⟨z, hz⟩ := hl
      have hz' : nk.map (z, f z) = nk.map (q, t) := (hzero z).symm.trans hz
      have he := nk.map.injOn
        (nk.domain ⟨mem_univ _, by constructor <;> linarith [(abs_lt.mp (hfsmall z)).1,
          (abs_lt.mp (hfsmall z)).2]⟩)
        (nk.domain ⟨mem_univ _, by constructor <;> linarith [ht.2.1, ht.2.2]⟩) hz'
      have hh := congrArg Prod.snd he
      linarith [(abs_lt.mp (hfsmall z)).2, ht.2.1]

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
