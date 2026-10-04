import DifferentialGeometry.Geometry.Comparison.FiniteSoul.ShaveFootPoint
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.TransverseShiftNormalConsumers

/-!
# S-SHAVE: the orthogonal boundary shift on a surface (finite metric)

Lane CMS-B. For a complete metric `g` of class `C^{r+1}` (`3 ≤ r`, `hnorm`) with `sec ≥ 0` on a
surface (`finrank ℝ E = 2`), a closed totally convex set `C` and `x ∈ int C`, there is `ρ > 0` such
that for `y` near `x`, a unit direction `u` at `y` reaching `∂C` at time `d(y, ∂C)` and a unit
`w ⊥ u`, the shifted point `exp_y (h w)`, `0 ≤ h < ρ`, is not farther from `∂C` than `y`
(`exists_orthogonal_boundary_shift_dim_two`; the finite form of the smooth
`hasOrthogonalBoundaryShift_relBoundary`, `Nonnegative/BoundaryShift.lean:439`, WITHOUT its
`HasSupportingHalfSpaces` hypothesis — that fact is `expMap_notMem_interior_of_foot`, proved in
`ShaveFootPoint.lean`).

Route: S-SHIFT2 with its normal field (lane CMS-J, `exists_transverse_shift_lipschitz_dim_two`)
gives a unit normal `ξ` along `τ t = exp_y (t u)` with `ξ 0 = w` and a `1`-Lipschitz shifted curve
`c t = exp_{τ t}(h ξ t)`; `c 0 ∈ int C`, `c (d(y, ∂C)) ∉ int C` (supporting half space at the foot
point), and the first exit time `t₀ ≤ d(y, ∂C)` gives a point of `∂C` within `t₀` of `c 0`.
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

omit [I.Boundaryless] [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M] in
/-- Changing the base point of `exp` along an equality of points. -/
theorem expMap_mk_congr {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) {a b : M} (hab : a = b)
    (v : E) : g.expMap (⟨a, v⟩ : TangentBundle I M) = g.expMap (⟨b, v⟩ : TangentBundle I M) := by
  subst hab
  rfl

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [CompleteSpace M] in
/-- **First exit to the frontier.** A curve that is `1`-Lipschitz on `[0, l]`, starts in `int C` and
ends outside `int C` (`C` closed) meets `∂C` at some time `t₀ ∈ (0, l]`. -/
theorem exists_mem_frontier_of_lipschitz {C : Set M} (hCcl : IsClosed C) {c : ℝ → M} {l : ℝ}
    (hl : 0 ≤ l) (hlip : ∀ s ∈ Icc 0 l, ∀ t ∈ Icc 0 l, dist (c s) (c t) ≤ |s - t|)
    (h0 : c 0 ∈ interior C) (hl' : c l ∉ interior C) :
    ∃ t₀ ∈ Icc 0 l, c t₀ ∈ frontier C := by
  have hcont : ContinuousOn c (Icc 0 l) := by
    refine Metric.continuousOn_iff.2 fun s hs ε hε => ⟨ε, hε, fun t ht hts => ?_⟩
    exact (hlip t ht s hs).trans_lt (by rw [← Real.dist_eq]; exact hts)
  set S : Set ℝ := Icc 0 l ∩ c ⁻¹' (interior C)ᶜ with hS
  have hScl : IsClosed S :=
    hcont.preimage_isClosed_of_isClosed isClosed_Icc isOpen_interior.isClosed_compl
  have hSc : IsCompact S := isCompact_Icc.of_isClosed_subset hScl inter_subset_left
  have hSne : S.Nonempty := ⟨l, ⟨hl, le_rfl⟩, hl'⟩
  set t₀ := sInf S with ht₀
  have ht₀S : t₀ ∈ S := hSc.sInf_mem hSne
  have hbefore : ∀ t, 0 ≤ t → t < t₀ → c t ∈ interior C := by
    intro t ht0 htt₀
    by_contra hn
    have hle : t₀ ≤ t := csInf_le hSc.bddBelow ⟨⟨ht0, htt₀.le.trans ht₀S.1.2⟩, hn⟩
    linarith
  have ht₀pos : 0 < t₀ := by
    rcases eq_or_lt_of_le ht₀S.1.1 with h | h
    · exact absurd (h ▸ h0) ht₀S.2
    · exact h
  have hcl : c t₀ ∈ closure (interior C) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    set t := max 0 (t₀ - ε / 2) with ht
    have ht0 : 0 ≤ t := le_max_left _ _
    have htt₀ : t < t₀ := max_lt ht₀pos (by linarith)
    refine ⟨c t, hbefore t ht0 htt₀, ?_⟩
    have h1 := hlip t₀ ht₀S.1 t ⟨ht0, htt₀.le.trans ht₀S.1.2⟩
    have h2 : t₀ - ε / 2 ≤ t := le_max_right _ _
    rw [abs_of_pos (by linarith)] at h1
    linarith
  have hC : c t₀ ∈ C := by
    have h := closure_mono (interior_subset (s := C)) hcl
    rwa [hCcl.closure_eq] at h
  exact ⟨t₀, ht₀S.1, subset_closure hC, ht₀S.2⟩

/-- **The orthogonal boundary shift on a surface** (finite form of the smooth
`hasOrthogonalBoundaryShift_relBoundary`, without its supporting-half-space hypothesis). -/
theorem exists_orthogonal_boundary_shift_dim_two
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 3 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    (hdim : Module.finrank ℝ E = 2) {C : Set M} (hC : IsTotallyConvexFinite g C)
    (hCcl : IsClosed C) {x : M} (hx : x ∈ interior C) :
    ∃ ρ > 0, ∀ y : M, dist x y < ρ → ∀ u w : E, g.inner y u u = 1 → g.inner y w w = 1 →
      g.inner y u w = 0 →
      g.expMap (⟨y, infDist y (frontier C) • u⟩ : TangentBundle I M) ∈ frontier C →
      ∀ h ∈ Ico 0 ρ, infDist (g.expMap (⟨y, h • w⟩ : TangentBundle I M)) (frontier C) ≤
        infDist y (frontier C) := by
  have hr2 : 2 ≤ r := le_trans (by norm_num) hr
  have hr1 : 1 ≤ r := le_trans (by norm_num) hr
  have : NeZero (Module.finrank ℝ E) := ⟨by rw [hdim]; norm_num⟩
  have hD : g.geodesicFlowDomain = univ := g.geodesicFlowDomain_eq_univ hr2 hnorm
  obtain ⟨ρ₁, hρ₁, hball₁⟩ := Metric.isOpen_iff.1 isOpen_interior x hx
  set L : ℝ := infDist x (frontier C) + 1 with hL
  obtain ⟨ρ₂, hρ₂, hshift⟩ := exists_transverse_shift_lipschitz_dim_two g hr hnorm hsec hdim x L
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
  obtain ⟨ξ, hξ0, hξ, hlip⟩ := hshift (⟨y, u⟩ : TangentBundle I M) (lt_of_lt_of_le hxy hm2) hu w hw
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
    exact hC.expMap_notMem_interior_of_foot hr2 hnorm (interior_subset hyint) hu hl hfoot
      (h • ξ l) hnn
  obtain ⟨t₀, ht₀, ht₀f⟩ := exists_mem_frontier_of_lipschitz hCcl hl.le hcL hc0int hcl
  calc infDist (g.expMap (⟨y, h • w⟩ : TangentBundle I M)) (frontier C) = infDist (c 0) (frontier C) := by
        rw [hc0]
    _ ≤ dist (c 0) (c t₀) := infDist_le_dist_of_mem ht₀f
    _ ≤ |0 - t₀| := hcL 0 ⟨le_rfl, hl.le⟩ t₀ ht₀
    _ = t₀ := by rw [zero_sub, abs_neg, abs_of_nonneg ht₀.1]
    _ ≤ l := ht₀.2

end DifferentialGeometry.Geometry.FiniteSoul

end
