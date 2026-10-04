import DifferentialGeometry.Geometry.Comparison.FiniteSoul.ShaveOrthogonalShift

/-!
# General-dimension S-SHAVE, A1: the orthogonal boundary shift from a transverse shift

Lane CMS3-SHAVE (frozen interface A1 of `build-logs/scratch/D-CMS3/FiniteSoulThreeInterfaces.lean`).
For a complete metric `g` of class `C^{r+1}` (`2 ≤ r`, `hnorm`) in ANY dimension, a closed totally
convex set `C` and `x ∈ int C`: if every unit geodesic near any point carries unit normal fields whose
shifted curves `t ↦ exp_{γ t}(h ξ t)` are `1`-Lipschitz (`hshift`, exactly the output shape of CMS-J's
`exists_transverse_shift_lipschitz_dim_two` and of the general S3-SHIFT), then the conclusion of CMS-B's
`exists_orthogonal_boundary_shift_dim_two` holds (`exists_orthogonal_boundary_shift_of_transverseShift`).

The proof is CMS-B's B3 argument (`ShaveOrthogonalShift.lean`) with the 2D supplier replaced by
`hshift`: the shifted curve starts in `int C`, ends outside `int C` by the supporting half space at the
foot point (`IsTotallyConvexFinite.expMap_notMem_interior_of_foot`), and its first exit time
(`exists_mem_frontier_of_lipschitz`) gives a point of `∂C` within `d(y, ∂C)` of the shifted point.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.FiniteSoul

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {r : ℕ∞}

/-- **A1. Orthogonal boundary shift from a transverse shift** (dimension-free; `2 ≤ r`). The
conclusion is the conclusion of CMS-B's `exists_orthogonal_boundary_shift_dim_two`. -/
theorem exists_orthogonal_boundary_shift_of_transverseShift [NeZero (Module.finrank ℝ E)]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hshift : ∀ (x : M) (L : ℝ), ∃ ρ > 0, ∀ p : TangentBundle I M, dist x p.proj < ρ →
      g.inner p.proj p.snd p.snd = 1 → ∀ w : E, g.inner p.proj w w = 1 → g.inner p.proj w p.snd = 0 →
        ∃ ξ : ℝ → E, ξ 0 = w ∧
          (∀ t ∈ Icc 0 L, g.inner (g.geodesicFlow p t).proj (ξ t) (ξ t) = 1 ∧
            g.inner (g.geodesicFlow p t).proj (ξ t) (g.geodesicFlow p t).snd = 0) ∧
          ∀ h ∈ Ico 0 ρ, ∀ t₁ ∈ Icc 0 L, ∀ t₂ ∈ Icc 0 L,
            dist (g.expMap (⟨(g.geodesicFlow p t₁).proj, h • ξ t₁⟩ : TangentBundle I M))
              (g.expMap (⟨(g.geodesicFlow p t₂).proj, h • ξ t₂⟩ : TangentBundle I M)) ≤ |t₁ - t₂|)
    {C : Set M} (hC : IsTotallyConvexFinite g C) (hCcl : IsClosed C) {x : M} (hx : x ∈ interior C) :
    ∃ ρ > 0, ∀ y : M, dist x y < ρ → ∀ u w : E, g.inner y u u = 1 → g.inner y w w = 1 →
      g.inner y u w = 0 →
      g.expMap (⟨y, infDist y (frontier C) • u⟩ : TangentBundle I M) ∈ frontier C →
      ∀ h ∈ Ico 0 ρ, infDist (g.expMap (⟨y, h • w⟩ : TangentBundle I M)) (frontier C) ≤
        infDist y (frontier C) := by
  have hr1 : 1 ≤ r := le_trans (by norm_num) hr
  have hD : g.geodesicFlowDomain = univ := g.geodesicFlowDomain_eq_univ hr hnorm
  obtain ⟨ρ₁, hρ₁, hball₁⟩ := Metric.isOpen_iff.1 isOpen_interior x hx
  set L : ℝ := infDist x (frontier C) + 1 with hL
  obtain ⟨ρ₂, hρ₂, hshiftx⟩ := hshift x L
  refine ⟨min (min (ρ₁ / 2) ρ₂) 1, by positivity, ?_⟩
  intro y hxy u w hu hw huw hend h hh
  have hm1 : min (min (ρ₁ / 2) ρ₂) 1 ≤ ρ₁ / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hm2 : min (min (ρ₁ / 2) ρ₂) 1 ≤ ρ₂ := (min_le_left _ _).trans (min_le_right _ _)
  have hm3 : min (min (ρ₁ / 2) ρ₂) 1 ≤ 1 := min_le_right _ _
  have hyint : y ∈ interior C := hball₁ (by rw [mem_ball, dist_comm]; linarith)
  set l := infDist y (frontier C) with hldef
  have hfne : (frontier C).Nonempty := ⟨_, hend⟩
  have hl : 0 < l :=
    (isClosed_frontier.notMem_iff_infDist_pos hfne).1 (fun hf => hf.2 hyint)
  have hlL : l < L := by
    have h1 : infDist y (frontier C) ≤ infDist x (frontier C) + dist y x :=
      infDist_le_infDist_add_dist
    rw [dist_comm] at h1
    rw [hL]
    linarith
  have hwu : g.inner y w u = 0 := by rw [g.symm y w u]; exact huw
  obtain ⟨ξ, hξ0, hξ, hlip⟩ := hshiftx (⟨y, u⟩ : TangentBundle I M) (lt_of_lt_of_le hxy hm2) hu w hw
    hwu
  have hh2 : h ∈ Ico 0 ρ₂ := ⟨hh.1, lt_of_lt_of_le hh.2 hm2⟩
  set c : ℝ → M := fun t => g.expMap (⟨(g.geodesicFlow (⟨y, u⟩ : TangentBundle I M) t).proj,
    h • ξ t⟩ : TangentBundle I M) with hc
  have hcL : ∀ s ∈ Icc 0 l, ∀ t ∈ Icc 0 l, dist (c s) (c t) ≤ |s - t| := fun s hs t ht =>
    hlip h hh2 s ⟨hs.1, hs.2.trans hlL.le⟩ t ⟨ht.1, ht.2.trans hlL.le⟩
  have hc0 : c 0 = g.expMap (⟨y, h • w⟩ : TangentBundle I M) := by
    simp only [hc, hξ0]
    exact expMap_mk_congr g (by rw [g.geodesicFlow_zero hr1]) (h • w)
  have hc0int : c 0 ∈ interior C := by
    refine hball₁ ?_
    rw [hc0, mem_ball, dist_comm]
    have h1 : dist y (g.expMap (⟨y, h • w⟩ : TangentBundle I M)) ≤ h := by
      have h2 := g.dist_expMap_smul_le_of_completeSpace hr1 hnorm (x := y) w 0 h
      have h3 : g.expMap (⟨y, (0 : ℝ) • w⟩ : TangentBundle I M) = y := by
        rw [zero_smul]; exact g.expMap_zero hr1 y
      calc dist y (g.expMap (⟨y, h • w⟩ : TangentBundle I M))
          = dist (g.expMap (⟨y, (0 : ℝ) • w⟩ : TangentBundle I M))
              (g.expMap (⟨y, h • w⟩ : TangentBundle I M)) := by rw [h3]
        _ ≤ Real.sqrt (g.inner y w w) * |h - 0| := h2
        _ = h := by rw [hw, Real.sqrt_one, one_mul, sub_zero, abs_of_nonneg hh.1]
    have h4 := dist_triangle x y (g.expMap (⟨y, h • w⟩ : TangentBundle I M))
    have h5 : h < ρ₁ / 2 := lt_of_lt_of_le hh.2 hm1
    linarith
  have hfoot : (g.geodesicFlow (⟨y, u⟩ : TangentBundle I M) l).proj ∈ frontier C := by
    rw [← g.expMap_smul_eq_proj_geodesicFlow hr1 y u l (by rw [hD]; exact mem_univ _)]
    exact hend
  have hcl : c l ∉ interior C := by
    have hperp := (hξ l ⟨hl.le, hlL.le⟩).2
    have hnn : 0 ≤ g.inner (g.geodesicFlow (⟨y, u⟩ : TangentBundle I M) l).proj (h • ξ l)
        (g.geodesicFlow (⟨y, u⟩ : TangentBundle I M) l).snd := by
      have h1 : g.inner (g.geodesicFlow (⟨y, u⟩ : TangentBundle I M) l).proj (h • ξ l)
          (g.geodesicFlow (⟨y, u⟩ : TangentBundle I M) l).snd =
          h * g.inner (g.geodesicFlow (⟨y, u⟩ : TangentBundle I M) l).proj (ξ l)
            (g.geodesicFlow (⟨y, u⟩ : TangentBundle I M) l).snd := by
        have h2 : g.inner (g.geodesicFlow (⟨y, u⟩ : TangentBundle I M) l).proj (h • ξ l) =
            h • g.inner (g.geodesicFlow (⟨y, u⟩ : TangentBundle I M) l).proj (ξ l) :=
          (g.inner (g.geodesicFlow (⟨y, u⟩ : TangentBundle I M) l).proj).map_smul h (ξ l)
        rw [h2]
        rfl
      rw [h1, hperp, mul_zero]
    exact hC.expMap_notMem_interior_of_foot hr hnorm (interior_subset hyint) hu hl hfoot
      (h • ξ l) hnn
  obtain ⟨t₀, ht₀, ht₀f⟩ := exists_mem_frontier_of_lipschitz hCcl hl.le hcL hc0int hcl
  calc infDist (g.expMap (⟨y, h • w⟩ : TangentBundle I M)) (frontier C)
      = infDist (c 0) (frontier C) := by rw [hc0]
    _ ≤ dist (c 0) (c t₀) := infDist_le_dist_of_mem ht₀f
    _ ≤ |0 - t₀| := hcL 0 ⟨le_rfl, hl.le⟩ t₀ ht₀
    _ = t₀ := by rw [zero_sub, abs_neg, abs_of_nonneg ht₀.1]
    _ ≤ l := ht₀.2

end DifferentialGeometry.Geometry.FiniteSoul

end
