/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedralTubeTraces

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem exists_iUnion_isPLSphere_one_of_local_real_embeddings {Z : Set E}
    (hZ : IsPolyhedron Z)
    (hcoord : ∀ x ∈ Z, ∃ (U : Set E) (f : E → ℝ), IsOpen U ∧ x ∈ U ∧
      ContinuousOn f (U ∩ Z) ∧ InjOn f (U ∩ Z))
    (harc : ∀ x ∈ Z, ∃ r : ℝ, 0 < r ∧ ∃ γ : ℝ → E,
      ContinuousOn γ (Ioo (-r) r) ∧ InjOn γ (Ioo (-r) r) ∧
        MapsTo γ (Ioo (-r) r) Z ∧ γ 0 = x) :
    ∃ (ι : Type u) (_ : Finite ι) (C : ι → Set E), (∀ i, IsPLSphere 1 (C i)) ∧
      (Pairwise fun i j => Disjoint (C i) (C j)) ∧ Z = ⋃ i, C i := by
  let _ : DecidableEq E := fun a b => Classical.propDecidable (a = b)
  obtain ⟨G, hGfin, hGT⟩ := hZ.exists_simplicialComplex
  have : Finite G.faces := hGfin.to_subtype
  have hvT : ∀ v, ({v} : Finset E) ∈ G.faces → v ∈ Z := fun v hv =>
    hGT ▸ G.vertices_subset_space hv
  have hlink : ∀ v, ({v} : Finset E) ∈ G.faces →
      (SimplicialComplex.geometricLink G {v}).space.encard ≤ 2 := by
    intro v hv
    obtain ⟨U, f, hU, hvU, hf, hinj⟩ := hcoord v (hvT v hv)
    apply (isRadiallyInjective_geometricLink G).encard_le_two_of_real_embedding
      (notMem_geometricLink_space G) hf hinj
    intro q hq
    have hcont : Continuous (fun t : ℝ => v + t • (q - v)) := by fun_prop
    have htend : Filter.Tendsto (fun t : ℝ => v + t • (q - v)) (𝓝 0) (𝓝 v) := by
      simpa only [zero_smul, add_zero] using hcont.tendsto 0
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp
      (htend.eventually_mem (hU.mem_nhds hvU))
    refine ⟨min (δ / 2) 1, lt_min (by positivity) zero_lt_one, fun t ht => ?_⟩
    have htδ : t < δ := lt_of_le_of_lt (ht.2.trans (min_le_left _ _)) (by linarith)
    have ht1 : t ≤ 1 := ht.2.trans (min_le_right _ _)
    refine ⟨hball ?_, ?_⟩
    · rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
      exact htδ
    · rw [← hGT]
      exact mem_convexHull_insert_of_mem_geometricLink_space G hq ht.1 ht1
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
    have hsubset : convexHull ℝ ({a, b} : Set E) ⊆
        (SimplicialComplex.geometricLink G {v}).space := by
      refine (convexHull_mono ?_).trans
        ((SimplicialComplex.geometricLink G {v}).convexHull_subset_space hmem)
      intro y hy
      rcases hy with rfl | rfl
      · exact ha
      · exact hb
    exact infinite_convexHull_pair hab ((Set.finite_of_encard_le_coe (hlink v hvG)).subset hsubset)
  have hnbr : ∀ v, ({v} : Finset E) ∈ G.faces →
      ∃ a b, a ≠ b ∧ {w | w ≠ v ∧ ({v, w} : Finset E) ∈ G.faces} = {a, b} := by
    intro v hv
    have hsp := geometricLink_space_eq_neighbors_of_card_le G hcardle v
    have hle := hlink v hv
    rw [hsp] at hle
    by_cases hle1 : {w | w ≠ v ∧ ({v, w} : Finset E) ∈ G.faces}.encard ≤ 1
    · exfalso
      obtain ⟨w₀, hNb⟩ : ∃ w₀ : E,
          {w | w ≠ v ∧ ({v, w} : Finset E) ∈ G.faces} ⊆ {w₀} := by
        rcases Set.encard_le_one_iff_eq.mp hle1 with h0 | ⟨w₀, h1⟩
        · exact ⟨v, by rw [h0]; exact empty_subset _⟩
        · exact ⟨w₀, h1.subset⟩
      have hstar : closedStar G v ⊆ convexHull ℝ ({v, w₀} : Set E) := by
        intro y hy
        obtain ⟨s, ⟨hs, hvs⟩, hys⟩ := mem_iUnion₂.mp hy
        have hvs' : v ∈ s := mem_of_mem_convexHull_of_singleton_mem G hv hs hvs
        apply convexHull_mono _ hys
        intro z hz
        by_cases hzv : z = v
        · exact Or.inl hzv
        · have hzs : ({v, z} : Finset E) ∈ G.faces := by
            refine G.down_closed hs (fun u hu => ?_) (by simp)
            simp only [Finset.mem_insert, Finset.mem_singleton] at hu
            rcases hu with rfl | rfl
            · exact hvs'
            · exact hz
          exact Or.inr (hNb ⟨hzv, hzs⟩)
      obtain ⟨ρ, hρ, γ, hγcont, hγi, hγmaps, hγ0⟩ := harc v (hvT v hv)
      have hγT : ∀ t : ℝ, |t| < ρ → γ t ∈ G.space := by
        intro t ht
        rw [hGT]
        exact hγmaps (abs_lt.mp ht)
      have hγinj : ∀ t t' : ℝ, |t| < ρ → |t'| < ρ → γ t = γ t' → t = t' :=
        fun t t' ht ht' heq => hγi (abs_lt.mp ht) (abs_lt.mp ht') heq
      obtain ⟨O, hO, hvO, hOstar⟩ : ∃ O : Set E, IsOpen O ∧ v ∈ O ∧
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
      have hseg : ∀ t : ℝ, |t| < δ → γ t ∈ convexHull ℝ ({v, w₀} : Set E) := by
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
      · obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : E →L[ℝ] ℝ, ℓ (w₀ - v) = 1 := by
          obtain ⟨ℓ, -, hℓ⟩ := exists_dual_vector ℝ (w₀ - v)
            (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hw₀))
          refine ⟨‖w₀ - v‖⁻¹ • ℓ, ?_⟩
          have hn : ‖w₀ - v‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hw₀)
          simp [hℓ, hn]
        have hsegform : ∀ y ∈ convexHull ℝ ({v, w₀} : Set E),
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
    · have hlt : 1 < {w | w ≠ v ∧ ({v, w} : Finset E) ∈ G.faces}.encard := not_le.mp hle1
      have htwo : {w | w ≠ v ∧ ({v, w} : Finset E) ∈ G.faces}.encard = 2 := by
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
