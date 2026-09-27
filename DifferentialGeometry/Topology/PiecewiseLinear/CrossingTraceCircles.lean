/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedralTubeTraces

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem HasPLCrossingAt.exists_lineChart {A X : Set E3} {x : E3}
    (hcross : HasPLCrossingAt A (frontier X) x) (hxA : x ∈ A)
    (hA : ∃ W : Set E3, IsOpen W ∧ x ∈ W ∧ ∃ U : Set (EuclideanSpace ℝ (Fin 2)),
      IsOpen U ∧ Nonempty (↥(W ∩ A) ≃ₜ U))
    (hXc : IsClosed X) (hX : x ∈ closure (interior X)) :
    ∃ (U : Set E3) (φ : E3 → ℝ × ℝ × ℝ) (ρ : ℝ), IsOpen U ∧ x ∈ U ∧ 0 < ρ ∧
      IsPLHomeomorphOn φ U (Metric.ball 0 ρ) ∧ φ x = 0 ∧
        ∀ y ∈ U, (y ∈ A ↔ (φ y).2.2 = 0) ∧ (y ∈ frontier X ↔ (φ y).2.1 = 0) := by
  have hdisk : ∀ N ∈ 𝓝 x, ∃ (c : EuclideanSpace ℝ (Fin 2)) (r : ℝ)
      (g : EuclideanSpace ℝ (Fin 2) → E3), 0 < r ∧ ContinuousOn g (Metric.ball c r) ∧
        InjOn g (Metric.ball c r) ∧ MapsTo g (Metric.ball c r) (A ∩ N) ∧ g c = x := by
    obtain ⟨W, -, hxW, U, hU, ⟨ψ⟩⟩ := hA
    intro N hN
    obtain ⟨c, r, g, hr, hgc, hgi, hgm, hgx⟩ :=
      exists_ball_chart_of_homeomorph_isOpen hU ψ ⟨hxW, hxA⟩ (mem_nhdsWithin_of_mem_nhds hN)
    exact ⟨c, r, g, hr, hgc, hgi, fun o ho => ⟨(hgm ho).1.2, (hgm ho).2⟩, hgx⟩
  obtain ⟨U, φ, ρ, α, β, hU, hxU, hρ, hφ, hφx, hα, hβ, hloc⟩ := hcross.exists_coordinateChart
  have hα0 : α = 0 := hα.resolve_right fun hne =>
    false_of_ballChart_of_halfPlane hU hxU hφ hφx hne (fun y hy hyA => (hloc y hy).1.mp hyA)
      hdisk
  have hβ0 : β = 0 := hβ.resolve_right fun hne =>
    false_of_frontier_halfPlane hU hxU hφ hφx hne (fun y hy => (hloc y hy).2) hXc hX
  refine ⟨U, φ, ρ, hU, hxU, hρ, hφ, hφx, fun y hy => ⟨?_, ?_⟩⟩
  · simpa [hα0] using (hloc y hy).1
  · simpa [hβ0] using (hloc y hy).2

open Classical in
theorem exists_iUnion_isPLSphere_one_of_forall_lineChart {A B : Set E3}
    (hZ : IsPolyhedron (A ∩ B)) (hcross : ∀ x ∈ A ∩ B, HasPLCrossingAt A B x)
    (hline : ∀ x ∈ A ∩ B, ∃ (U : Set E3) (φ : E3 → ℝ × ℝ × ℝ) (ρ : ℝ), IsOpen U ∧ x ∈ U ∧
      0 < ρ ∧ IsPLHomeomorphOn φ U (Metric.ball 0 ρ) ∧ φ x = 0 ∧
        ∀ y ∈ U, (y ∈ A ↔ (φ y).2.2 = 0) ∧ (y ∈ B ↔ (φ y).2.1 = 0)) :
    ∃ (ι : Type) (_ : Finite ι) (C : ι → Set E3), (∀ i, IsPLSphere 1 (C i)) ∧
      (Pairwise fun i j => Disjoint (C i) (C j)) ∧ A ∩ B = ⋃ i, C i := by
  let _ : DecidableEq E3 := fun a b => Classical.propDecidable (a = b)
  obtain ⟨G, hGfin, hGT⟩ := hZ.exists_simplicialComplex
  have : Finite G.faces := hGfin.to_subtype
  have hvT : ∀ v, ({v} : Finset E3) ∈ G.faces → v ∈ A ∩ B := fun v hv =>
    hGT ▸ G.vertices_subset_space hv
  have hlink : ∀ v, ({v} : Finset E3) ∈ G.faces →
      (SimplicialComplex.geometricLink G {v}).space.encard ≤ 2 := by
    intro v hv
    refine (hcross v (hvT v hv)).encard_geometricLink_le_two G
      (Filter.Eventually.of_forall fun y hy => ?_)
    rwa [hGT] at hy
  have hcardle : ∀ s ∈ G.faces, s.card ≤ 2 := by
    intro s hs
    by_contra hlt
    push Not at hlt
    obtain ⟨v, hv⟩ := G.nonempty_of_mem_faces hs
    have hvG := G.down_closed hs (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
    have herase : 1 < (s.erase v).card := by
      rw [Finset.card_erase_of_mem hv]
      omega
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp herase
    have hmem : s.erase v ∈ (SimplicialComplex.geometricLink G {v}).faces :=
      (SimplicialComplex.mem_geometricLink_singleton G v _).mpr
        ⟨⟨a, ha⟩, Finset.notMem_erase v s, by rwa [Finset.insert_erase hv]⟩
    have hsubset : convexHull ℝ ({a, b} : Set E3) ⊆
        (SimplicialComplex.geometricLink G {v}).space := by
      refine (convexHull_mono ?_).trans
        ((SimplicialComplex.geometricLink G {v}).convexHull_subset_space hmem)
      intro y hy
      rcases hy with rfl | rfl
      · exact ha
      · exact hb
    exact infinite_convexHull_pair hab ((Set.finite_of_encard_le_coe (hlink v hvG)).subset hsubset)
  have hnbr : ∀ v, ({v} : Finset E3) ∈ G.faces →
      ∃ a b, a ≠ b ∧ {w | w ≠ v ∧ ({v, w} : Finset E3) ∈ G.faces} = {a, b} := by
    intro v hv
    have hsp := geometricLink_space_eq_neighbors_of_card_le G hcardle v
    have hle := hlink v hv
    rw [hsp] at hle
    by_cases hle1 : {w | w ≠ v ∧ ({v, w} : Finset E3) ∈ G.faces}.encard ≤ 1
    · exfalso
      obtain ⟨w₀, hNb⟩ : ∃ w₀ : E3,
          {w | w ≠ v ∧ ({v, w} : Finset E3) ∈ G.faces} ⊆ {w₀} := by
        rcases Set.encard_le_one_iff_eq.mp hle1 with h0 | ⟨w₀, h1⟩
        · exact ⟨v, by rw [h0]; exact empty_subset _⟩
        · exact ⟨w₀, h1.subset⟩
      have hstar : closedStar G v ⊆ convexHull ℝ ({v, w₀} : Set E3) := by
        intro y hy
        obtain ⟨s, ⟨hs, hvs⟩, hys⟩ := mem_iUnion₂.mp hy
        have hvs' : v ∈ s := mem_of_mem_convexHull_of_singleton_mem G hv hs hvs
        apply convexHull_mono _ hys
        intro z hz
        by_cases hzv : z = v
        · exact Or.inl hzv
        · have hzs : ({v, z} : Finset E3) ∈ G.faces := by
            refine G.down_closed hs (fun u hu => ?_) (by simp)
            simp only [Finset.mem_insert, Finset.mem_singleton] at hu
            rcases hu with rfl | rfl
            · exact hvs'
            · exact hz
          exact Or.inr (hNb ⟨hzv, hzs⟩)
      obtain ⟨U, φ, ρ, hU, hvU, hρ, hφ, hφv, hloc⟩ := hline v (hvT v hv)
      let ψ := Function.invFunOn φ U
      let γ : ℝ → E3 := fun t => ψ (t, 0, 0)
      have hγball : ∀ t : ℝ, |t| < ρ → ((t, 0, 0) : ℝ × ℝ × ℝ) ∈ Metric.ball 0 ρ := by
        intro t ht
        rw [mem_ball_zero_iff]
        simpa [Prod.norm_def] using ht
      have hγU : ∀ t : ℝ, |t| < ρ → γ t ∈ U ∧ φ (γ t) = (t, 0, 0) := fun t ht =>
        ⟨hφ.bijOn.surjOn.mapsTo_invFunOn (hγball t ht),
          hφ.bijOn.invOn_invFunOn.2 (hγball t ht)⟩
      have hγ0 : γ 0 = v := by
        have : ((0 : ℝ), (0 : ℝ), (0 : ℝ)) = φ v := by rw [hφv]; rfl
        change ψ ((0 : ℝ), (0 : ℝ), (0 : ℝ)) = v
        rw [this]
        exact hφ.bijOn.invOn_invFunOn.1 hvU
      have hγT : ∀ t : ℝ, |t| < ρ → γ t ∈ G.space := by
        intro t ht
        obtain ⟨hγt, hφγ⟩ := hγU t ht
        rw [hGT]
        exact ⟨(hloc _ hγt).1.mpr (by rw [hφγ]), (hloc _ hγt).2.mpr (by rw [hφγ])⟩
      have hγinj : ∀ t t' : ℝ, |t| < ρ → |t'| < ρ → γ t = γ t' → t = t' := by
        intro t t' ht ht' heq
        have := congrArg φ heq
        rw [(hγU t ht).2, (hγU t' ht').2] at this
        exact congrArg Prod.fst this
      have hγcont : ContinuousOn γ (Set.Ioo (-ρ) ρ) := by
        refine hφ.isPiecewiseAffineOn_invFunOn.continuousOn.comp
          (Continuous.continuousOn (by fun_prop)) fun t ht => hγball t ?_
        exact abs_lt.mpr ht
      obtain ⟨O, hO, hvO, hOstar⟩ : ∃ O : Set E3, IsOpen O ∧ v ∈ O ∧
          O ∩ G.space ⊆ closedStar G v := by
        obtain ⟨O, hOn, hOsub⟩ :=
          mem_nhdsWithin_iff_exists_mem_nhds_inter.mp (closedStar_mem_nhdsWithin G v)
        obtain ⟨O', hO'sub, hO', hvO'⟩ := mem_nhds_iff.mp hOn
        exact ⟨O', hO', hvO', fun y hy => hOsub ⟨hO'sub hy.1, hy.2⟩⟩
      have hγO : ∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ O := by
        have hc : ContinuousAt γ 0 :=
          hγcont.continuousAt (Ioo_mem_nhds (by linarith) hρ)
        exact hc.preimage_mem_nhds (by rw [hγ0]; exact hO.mem_nhds hvO)
      obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp
        (Filter.inter_mem hγO (Ioo_mem_nhds (show -ρ < 0 by linarith) hρ))
      have hseg : ∀ t : ℝ, |t| < δ → γ t ∈ convexHull ℝ ({v, w₀} : Set E3) := by
        intro t ht
        have htb : t ∈ Metric.ball (0 : ℝ) δ := by
          rw [Metric.mem_ball, Real.dist_eq, sub_zero]
          exact ht
        have hmem := hδsub htb
        have htρ : |t| < ρ := abs_lt.mpr hmem.2
        exact hstar (hOstar ⟨hmem.1, hγT t htρ⟩)
      have hsmall : ∀ t : ℝ, |t| ≤ δ / 2 → |t| < δ ∧ |t| < ρ := by
        have hδρ : δ / 2 < ρ := by
          have h1 : (δ / 2 : ℝ) ∈ Metric.ball (0 : ℝ) δ := by
            rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
            linarith
          exact (hδsub h1).2.2
        exact fun t ht => ⟨by linarith, by linarith⟩
      by_cases hw₀ : w₀ = v
      · subst hw₀
        have hγv := hseg (δ / 2) (by rw [abs_of_pos (by positivity)]; linarith)
        rw [Set.pair_eq_singleton, convexHull_singleton, mem_singleton_iff] at hγv
        have := hγinj (δ / 2) 0 (hsmall _ (by rw [abs_of_pos (by positivity)])).2
          (by simpa using hρ) (hγv.trans hγ0.symm)
        linarith
      · obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : E3 →L[ℝ] ℝ, ℓ (w₀ - v) = 1 := by
          obtain ⟨ℓ, -, hℓ⟩ := exists_dual_vector ℝ (w₀ - v)
            (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hw₀))
          refine ⟨‖w₀ - v‖⁻¹ • ℓ, ?_⟩
          have hn : ‖w₀ - v‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hw₀)
          simp [hℓ, hn]
        have hsegform : ∀ y ∈ convexHull ℝ ({v, w₀} : Set E3),
            0 ≤ ℓ (y - v) ∧ (ℓ (y - v) = 0 → y = v) := by
          intro y hy
          rw [convexHull_pair, segment_eq_image'] at hy
          obtain ⟨θ, hθ, rfl⟩ := hy
          simp only [add_sub_cancel_left, map_smul, hℓ, smul_eq_mul, mul_one]
          exact ⟨hθ.1, fun h0 => by rw [h0, zero_smul, add_zero]⟩
        let f : ℝ → ℝ := fun t => ℓ (γ t - v)
        have hfc : ContinuousOn f (Set.Icc (-(δ / 2)) (δ / 2)) := by
          apply (ℓ.continuous.comp_continuousOn ((hγcont.mono ?_).sub continuousOn_const))
          intro t ht
          obtain ⟨-, htρ⟩ := hsmall t (abs_le.mpr ⟨ht.1, ht.2⟩)
          exact abs_lt.mp htρ
        have hf0 : f 0 = 0 := by simp [f, hγ0]
        have hfpos : ∀ t : ℝ, |t| ≤ δ / 2 → t ≠ 0 → 0 < f t := by
          intro t ht ht0
          obtain ⟨htδ, htρ⟩ := hsmall t ht
          obtain ⟨hnn, heq⟩ := hsegform _ (hseg t htδ)
          rcases eq_or_lt_of_le hnn with hz | hp
          · exact (ht0 (hγinj t 0 htρ (by simpa using hρ) ((heq hz.symm).trans hγ0.symm))).elim
          · exact hp
        have ha := hfpos (-(δ / 2)) (by rw [abs_neg, abs_of_pos (by positivity)])
          (by linarith)
        have hb := hfpos (δ / 2) (by rw [abs_of_pos (by positivity)]) (by linarith)
        have hinjf : ∀ t t' : ℝ, |t| ≤ δ / 2 → |t'| ≤ δ / 2 → f t = f t' → t = t' := by
          intro t t' ht ht' hff
          apply hγinj t t' (hsmall t ht).2 (hsmall t' ht').2
          have hy := hseg t (hsmall t ht).1
          have hy' := hseg t' (hsmall t' ht').1
          rw [convexHull_pair, segment_eq_image'] at hy hy'
          obtain ⟨θ, -, hθ⟩ := hy
          obtain ⟨θ', -, hθ'⟩ := hy'
          have hfθ : f t = θ := by
            simp only [f, ← hθ, add_sub_cancel_left, map_smul, hℓ, smul_eq_mul, mul_one]
          have hfθ' : f t' = θ' := by
            simp only [f, ← hθ', add_sub_cancel_left, map_smul, hℓ, smul_eq_mul, mul_one]
          rw [← hθ, ← hθ', ← hfθ, ← hfθ', hff]
        rcases le_total (f (-(δ / 2))) (f (δ / 2)) with hle | hle
        · have hsub' : Set.Icc (f 0) (f (δ / 2)) ⊆ f '' Set.Icc 0 (δ / 2) :=
            intermediate_value_Icc (by positivity) (hfc.mono fun t ht =>
              ⟨by linarith [ht.1], ht.2⟩)
          obtain ⟨t', ht', hft'⟩ := hsub' ⟨by rw [hf0]; exact ha.le, hle⟩
          have := hinjf t' (-(δ / 2)) (by rw [abs_of_nonneg ht'.1]; exact ht'.2)
            (by rw [abs_neg, abs_of_pos (by positivity)]) hft'
          linarith [ht'.1]
        · have hsub' : Set.Icc (f 0) (f (-(δ / 2))) ⊆ f '' Set.Icc (-(δ / 2)) 0 := by
            have hfc' : ContinuousOn (fun t => f (-t)) (Set.Icc 0 (δ / 2)) :=
              hfc.comp (continuous_neg.continuousOn) fun t ht =>
                ⟨by linarith [ht.2], by linarith [ht.1]⟩
            intro y hy
            obtain ⟨t', ht', hft'⟩ := intermediate_value_Icc (by positivity) hfc'
              (by simpa using hy)
            exact ⟨-t', ⟨by linarith [ht'.2], by linarith [ht'.1]⟩, hft'⟩
          obtain ⟨t', ht', hft'⟩ := hsub' ⟨by rw [hf0]; exact hb.le, hle⟩
          have := hinjf t' (δ / 2) (by rw [abs_of_nonpos ht'.2]; linarith [ht'.1])
            (by rw [abs_of_pos (by positivity)]) hft'
          linarith [ht'.2]
    · have hlt : 1 < {w | w ≠ v ∧ ({v, w} : Finset E3) ∈ G.faces}.encard := not_le.mp hle1
      have htwo : {w | w ≠ v ∧ ({v, w} : Finset E3) ∈ G.faces}.encard = 2 := by
        apply le_antisymm hle
        exact Order.add_one_le_of_lt hlt
      exact Set.encard_eq_two.mp htwo
  have hG1 : IsCombinatorialManifold 1 G := (isCombinatorialManifold_one_iff G).mpr ⟨hcardle, hnbr⟩
  have : Finite (ConnectedComponents G.space) := finite_connectedComponents_space G
  refine ⟨ConnectedComponents G.space, inferInstance,
    fun c => (connectedComponentComplex G c).space, fun c => ?_,
    pairwise_disjoint_connectedComponentComplex_space G, ?_⟩
  · have : Finite (connectedComponentComplex G c).faces :=
      (connectedComponentComplex_faces_finite G c).to_subtype
    exact isPLSphere_one_of_edgeGraph_connected _ (hG1.connectedComponentComplex c)
      (edgeGraph_connected_of_isConnected_space _
        (isConnected_connectedComponentComplex_space G c))
  · rw [← hGT, iUnion_connectedComponentComplex_space G]

end DifferentialGeometry.Topology.PiecewiseLinear
