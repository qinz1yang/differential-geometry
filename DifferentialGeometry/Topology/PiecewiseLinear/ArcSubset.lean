import DifferentialGeometry.Topology.PiecewiseLinear.PolygonalSchoenflies
import DifferentialGeometry.Topology.PiecewiseLinear.BallFrontier

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem exists_isPLBall_one_superset_of_isClosed_ssubset_planar
    {S C : Set (EuclideanSpace ℝ (Fin 2))} (hS : IsPLSphere 1 S)
    (hC : IsClosed C) (hCS : C ⊂ S) :
    ∃ A, IsPLBall 1 A ∧ C ⊆ A ∧ A ⊆ S := by
  obtain ⟨γ, hγ, hPL, hγS⟩ := exists_piecewiseAffine_loop_of_isPLSphere_one hS
  have hpre : IsClosed (Icc (0 : ℝ) 1 ∩ γ ⁻¹' C) :=
    hPL.continuousOn.preimage_isClosed_of_isClosed isClosed_Icc hC
  have hmiss : ∃ t ∈ Ioo (0 : ℝ) 1, γ t ∉ C := by
    by_contra! h
    apply hCS.2
    intro x hx
    obtain ⟨t, ht, rfl⟩ := hγS.symm.subset hx
    have hsub : Ioo (0 : ℝ) 1 ⊆ Icc (0 : ℝ) 1 ∩ γ ⁻¹' C :=
      fun s hs => ⟨Ioo_subset_Icc_self hs, h s hs⟩
    have hcl := closure_minimal hsub hpre
    rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)] at hcl
    exact (hcl ht).2
  obtain ⟨t, ht, htC⟩ := hmiss
  have hcont : ContinuousAt γ t := hPL.continuousOn.continuousAt (Icc_mem_nhds ht.1 ht.2)
  have hnhds : γ ⁻¹' Cᶜ ∩ Ioo (0 : ℝ) 1 ∈ 𝓝 t :=
    Filter.inter_mem (hcont.preimage_mem_nhds (hC.isOpen_compl.mem_nhds htC))
      (Ioo_mem_nhds ht.1 ht.2)
  obtain ⟨l, u, htu, hlu⟩ := mem_nhds_iff_exists_Ioo_subset.mp hnhds
  let a := (l + t) / 2
  let b := (t + u) / 2
  have ha : a ∈ Ioo l u := ⟨by dsimp [a]; linarith [htu.1], by dsimp [a]; linarith [htu.1, htu.2]⟩
  have hb : b ∈ Ioo l u := ⟨by dsimp [b]; linarith [htu.1, htu.2], by dsimp [b]; linarith [htu.2]⟩
  have haI := (hlu ha).2
  have hbI := (hlu hb).2
  have hab : a < b := by dsimp [a, b]; linarith [htu.1, htu.2]
  refine ⟨γ '' Icc 0 a ∪ γ '' Icc b 1,
    isPLBall_outside_subarcs hγ hPL (Ioo_subset_Icc_self haI) (Ioo_subset_Icc_self hbI) hbI.2 hab,
    ?_, ?_⟩
  · intro x hx
    obtain ⟨s, hs, rfl⟩ := hγS.symm.subset (hCS.1 hx)
    by_cases hsa : s ≤ a
    · exact Or.inl ⟨s, ⟨hs.1, hsa⟩, rfl⟩
    · by_cases hbs : b ≤ s
      · exact Or.inr ⟨s, ⟨hbs, hs.2⟩, rfl⟩
      · have hslu : s ∈ Ioo l u := ⟨by linarith [ha.1], by linarith [hb.2]⟩
        exact ((hlu hslu).1 hx).elim
  · apply union_subset
    · exact (image_mono (Icc_subset_Icc le_rfl haI.2.le)).trans hγS.subset
    · exact (image_mono (Icc_subset_Icc hbI.1.le le_rfl)).trans hγS.subset

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsPLSphere.exists_isPLBall_one_superset_of_ssubset {S C : Set E}
    (hS : IsPLSphere 1 S) (hC : IsClosed C) (hCS : C ⊂ S) :
    ∃ A, IsPLBall 1 A ∧ C ⊆ A ∧ A ⊆ S := by
  obtain ⟨T, hT, hcard, -, -, -⟩ := exists_affineIndependent_openSimplex_subset
    (n := 1) (by simp) (0 : EuclideanSpace ℝ (Fin 2)) Filter.univ_mem
  have hB : IsPLBall 2 (convexHull ℝ (T : Set (EuclideanSpace ℝ (Fin 2)))) :=
    isPLBall_convexHull_of_affineIndependent T hT hcard
  let J := frontier (convexHull ℝ (T : Set (EuclideanSpace ℝ (Fin 2))))
  have hJ : IsPLSphere 1 J := hB.isPLSphere_frontier
  obtain ⟨s, hs⟩ := hS
  obtain ⟨j, hj⟩ := hJ
  let f := j ∘ Function.invFunOn s (stdSimplexBoundary 2)
  have hf : IsPLHomeomorphOn f S J := hs.symm.trans hj
  have hS' : IsPLSphere 1 S := ⟨s, hs⟩
  have hJ' : IsPLSphere 1 J := ⟨j, hj⟩
  have hCcompact := hS'.isPolyhedron.isCompact.of_isClosed_subset hC hCS.1
  have himageClosed : IsClosed (f '' C) :=
    (hCcompact.image_of_continuousOn (hf.isPiecewiseAffineOn.continuousOn.mono hCS.1)).isClosed
  have hproper : f '' C ⊂ J := by
    refine ⟨(image_mono hCS.1).trans hf.image_eq.subset, ?_⟩
    intro h
    apply hCS.2
    intro x hx
    obtain ⟨y, hy, hyx⟩ := h (hf.bijOn.mapsTo hx)
    exact hf.bijOn.injOn (hCS.1 hy) hx hyx ▸ hy
  obtain ⟨A, hA, hCA, hAJ⟩ :=
    exists_isPLBall_one_superset_of_isClosed_ssubset_planar hJ' himageClosed hproper
  let g := Function.invFunOn f S
  refine ⟨g '' A, hA.of_isPLHomeomorphOn (hf.symm.restrict hA.isPolyhedron hAJ), ?_, ?_⟩
  · intro x hx
    exact ⟨f x, hCA ⟨x, hx, rfl⟩, hf.bijOn.invOn_invFunOn.1 (hCS.1 hx)⟩
  · exact (image_mono hAJ).trans hf.symm.image_eq.subset

theorem IsPLBall.isPLBall_one_of_isCompact_of_isConnected {P C : Set E}
    (hP : IsPLBall 1 P) (hC : IsCompact C) (hconn : IsConnected C)
    (hne : C.Nontrivial) (hCP : C ⊆ P) : IsPLBall 1 C := by
  obtain ⟨f, hf⟩ := exists_isPLHomeomorphOn_Icc_of_isPLBall_one hP
  let g := Function.invFunOn f (Icc (0 : ℝ) 1)
  have hgcont : ContinuousOn g C := hf.symm.isPiecewiseAffineOn.continuousOn.mono hCP
  have hcompact : IsCompact (g '' C) := hC.image_of_continuousOn hgcont
  have hconnected : IsConnected (g '' C) := hconn.image g hgcont
  obtain ⟨a, b, heq⟩ : ∃ a b : ℝ, g '' C = Icc a b :=
    ⟨_, _, eq_Icc_of_connected_compact hconnected hcompact⟩
  have hab : a < b := by
    obtain ⟨x, hx, y, hy, hxy⟩ := hne
    have hxi : g x ∈ Icc a b := heq.subset ⟨x, hx, rfl⟩
    have hyi : g y ∈ Icc a b := heq.subset ⟨y, hy, rfl⟩
    by_contra! hba
    exact hxy (hf.symm.bijOn.injOn (hCP hx) (hCP hy) (by
      change g x = g y
      apply le_antisymm <;> linarith [hxi.1, hxi.2, hyi.1, hyi.2]))
  have hsub : Icc a b ⊆ Icc (0 : ℝ) 1 := by
    rw [← heq]
    exact (image_mono hCP).trans hf.symm.image_eq.subset
  have hback : f '' (g '' C) = C := by
    rw [image_image]
    have hfix : EqOn (f ∘ g) id C := fun x hx => hf.bijOn.invOn_invFunOn.2 (hCP hx)
    exact hfix.image_eq.trans (image_id _)
  have hball := (isPLBall_Icc hab).of_isPLHomeomorphOn
    (hf.restrict (isPLBall_Icc hab).isPolyhedron hsub)
  rwa [← heq, hback] at hball

end DifferentialGeometry.Topology.PiecewiseLinear
