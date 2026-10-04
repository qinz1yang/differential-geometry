import DifferentialGeometry.Geometry.Comparison.FiniteSoul.RelativeShaveFoot

/-!
# REL kernel, step (iii): first exit on the whole shift rectangle (CMS3-REL, G1)

Lane CMS3-REL, sub-lemma SL3 of `build-logs/resume/sheet-CMS3-REL.md` (review item 7: the first exit is
handled on the whole `(s, t)` rectangle, not by "total convexity gives the transverse segment in `C`").
Setting: a complete metric `g` of class `C^{r+1}` (`2 ≤ r`, `hnorm`), a closed totally convex `C`,
relative interior `Z`, relative boundary `B = C \ Z`; `γ t = π φ_t (y, u)` is the unit foot segment from
`y ∈ Z` to `B` (length `l = d(y, B)`) and `α s t = exp_{γ t} (s ξ t)` the shift rectangle.

* `exists_mem_relBoundaryOfOrder_of_shift_rectangle`: if `ξ` is unit, tangent to `Z` along `γ [0, l)`,
  every row `t ↦ α s t` (`s ∈ [0, h]`, `h < l`) is `1`-Lipschitz on `[0, l]`, and the corner
  `α h l ∉ Z`, then the top row meets `B` at some `t ∈ [0, l]`. Proof: `t₀ = inf` of the times at which
  some point of the column `s ↦ α s t` (`s ∈ [0, h]`) lies in `B`; `t₀ ≥ l - h > 0`. Columns before
  `t₀` start in `Z` tangent to `Z` and avoid `B`, so they lie in `Z` (no escape, SL1). If `t₀ = l` the
  corner lies in `closure Z ⊆ C` and not in `Z`, so in `B`. If `t₀ < l`, the column `t₀` lies in `C`
  (limits along the rows), starts at `γ t₀ ∈ Z`, and a point of it lies in `B` (infimum + rows
  `1`-Lipschitz); by relative open-core propagation (SLICE (7)) that point is the top one.
* `exists_relative_orthogonal_shift_of_transverseShift` (A1-rel): the relative orthogonal boundary
  shift from the REL kernel's prefix-tangent transverse shift; the corner is excluded by the relative
  foot point (SL2, `expMap_notMem_maxSliceLocusOfOrder_of_foot`).
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

/-- **First exit on the shift rectangle (SL3).** -/
theorem exists_mem_relBoundaryOfOrder_of_shift_rectangle
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {C : Set M} (hCcl : IsClosed C) (hconv : IsTotallyConvexFinite g C) {y : M}
    (hy : y ∈ maxSliceLocusOfOrder I (r : ℕ∞ω) C) {u : E} (hu : g.inner y u u = 1)
    (hfoot : g.expMap (⟨y, infDist y (relBoundaryOfOrder I (r : ℕ∞ω) C) • u⟩ : TangentBundle I M) ∈
      relBoundaryOfOrder I (r : ℕ∞ω) C)
    {ξ : ℝ → E} {h : ℝ} (hh : 0 ≤ h) (hhl : h < infDist y (relBoundaryOfOrder I (r : ℕ∞ω) C))
    (hξu : ∀ t ∈ Icc 0 (infDist y (relBoundaryOfOrder I (r : ℕ∞ω) C)),
      g.inner (g.geodesicFlow (⟨y, u⟩ : TangentBundle I M) t).proj (ξ t) (ξ t) = 1)
    (hξT : ∀ t ∈ Ico 0 (infDist y (relBoundaryOfOrder I (r : ℕ∞ω) C)),
      ξ t ∈ sliceTangent I (maxSliceLocusOfOrder I (r : ℕ∞ω) C)
        (g.geodesicFlow (⟨y, u⟩ : TangentBundle I M) t).proj)
    (hlip : ∀ s ∈ Icc 0 h, ∀ t₁ ∈ Icc 0 (infDist y (relBoundaryOfOrder I (r : ℕ∞ω) C)),
      ∀ t₂ ∈ Icc 0 (infDist y (relBoundaryOfOrder I (r : ℕ∞ω) C)),
        dist (g.expMap (⟨(g.geodesicFlow (⟨y, u⟩ : TangentBundle I M) t₁).proj, s • ξ t₁⟩ :
            TangentBundle I M))
          (g.expMap (⟨(g.geodesicFlow (⟨y, u⟩ : TangentBundle I M) t₂).proj, s • ξ t₂⟩ :
            TangentBundle I M)) ≤ |t₁ - t₂|)
    (hend : g.expMap (⟨(g.geodesicFlow (⟨y, u⟩ : TangentBundle I M)
        (infDist y (relBoundaryOfOrder I (r : ℕ∞ω) C))).proj,
      h • ξ (infDist y (relBoundaryOfOrder I (r : ℕ∞ω) C))⟩ : TangentBundle I M) ∉
        maxSliceLocusOfOrder I (r : ℕ∞ω) C) :
    ∃ t ∈ Icc 0 (infDist y (relBoundaryOfOrder I (r : ℕ∞ω) C)),
      g.expMap (⟨(g.geodesicFlow (⟨y, u⟩ : TangentBundle I M) t).proj, h • ξ t⟩ : TangentBundle I M) ∈
        relBoundaryOfOrder I (r : ℕ∞ω) C := by
  have hr1 : 1 ≤ r := one_le_two.trans hr
  have hD : g.geodesicFlowDomain = univ := g.geodesicFlowDomain_eq_univ hr hnorm
  set Z := maxSliceLocusOfOrder I (r : ℕ∞ω) C with hZdef
  set B := relBoundaryOfOrder I (r : ℕ∞ω) C with hBdef
  set l := infDist y B with hldef
  set γ : ℝ → M := fun t => (g.geodesicFlow (⟨y, u⟩ : TangentBundle I M) t).proj with hγdef
  set α : ℝ → ℝ → M := fun s t => g.expMap (⟨γ t, s • ξ t⟩ : TangentBundle I M) with hαdef
  change ∃ t ∈ Icc 0 l, α h t ∈ B
  have hend' : α h l ∉ Z := hend
  have hlip' : ∀ s ∈ Icc 0 h, ∀ t₁ ∈ Icc 0 l, ∀ t₂ ∈ Icc 0 l, dist (α s t₁) (α s t₂) ≤ |t₁ - t₂| :=
    hlip
  have hBcl : IsClosed B := isClosed_relBoundaryOfOrder g hr hnorm hCcl hconv
  have hBne : B.Nonempty := ⟨_, hfoot⟩
  have hl : 0 < l := (hBcl.notMem_iff_infDist_pos hBne).1 fun hB => hB.2 hy
  have hyC : y ∈ C := maxSliceLocusOfOrder_subset hy
  obtain ⟨hsegC, hsegZ, hsegd⟩ := foot_segment_relBoundaryOfOrder g hr hnorm hconv hyC hu hfoot
  have hclZ : closure Z ⊆ C := closure_minimal maxSliceLocusOfOrder_subset hCcl
  have hmemZ : ∀ x : M, x ∈ C → x ∉ B → x ∈ Z := fun x hxC hxB => by
    by_contra hxZ
    exact hxB ⟨hxC, hxZ⟩
  -- the columns as geodesics
  have hPS : ∀ s t : ℝ, α s t = (g.geodesicFlow (⟨γ t, ξ t⟩ : TangentBundle I M) s).proj :=
    fun s t => g.expMap_smul_eq_proj_geodesicFlow hr1 (γ t) (ξ t) s (by rw [hD]; exact mem_univ _)
  have hα0 : ∀ t : ℝ, α 0 t = γ t := fun t => by
    rw [hPS, g.geodesicFlow_zero hr1]
  have hspeed : ∀ t ∈ Icc 0 l, ∀ s : ℝ, 0 ≤ s → dist (γ t) (α s t) ≤ s := by
    intro t ht s hs
    have h1 := g.dist_proj_geodesicFlow_le hr1 hnorm (p := (⟨γ t, ξ t⟩ : TangentBundle I M))
      (s := 0) (t := s) (fun τ _ => by rw [hD]; exact mem_univ _)
    rw [g.geodesicFlow_zero hr1] at h1
    change dist (γ t) _ ≤ Real.sqrt (g.inner (γ t) (ξ t) (ξ t)) * |s - 0| at h1
    rw [hξu t ht, Real.sqrt_one, one_mul, sub_zero, abs_of_nonneg hs] at h1
    rw [hPS]
    exact h1
  have hcolc : ∀ t : ℝ, Continuous (fun s => α s t) := by
    intro t
    set σ : ℝ := Real.sqrt (g.inner (γ t) (ξ t) (ξ t)) with hσ
    have hσ0 : 0 ≤ σ := Real.sqrt_nonneg _
    have heq : (fun s => α s t) = fun s => (g.geodesicFlow (⟨γ t, ξ t⟩ : TangentBundle I M) s).proj :=
      funext fun s => hPS s t
    rw [heq]
    refine LipschitzWith.continuous (K := ⟨σ, hσ0⟩) (LipschitzWith.of_dist_le_mul fun a b => ?_)
    rw [Real.dist_eq, abs_sub_comm]
    exact g.dist_proj_geodesicFlow_le hr1 hnorm (fun τ _ => by rw [hD]; exact mem_univ _)
  -- the hitting times
  set A : Set ℝ := {t | t ∈ Icc 0 l ∧ ∃ s ∈ Icc 0 h, α s t ∈ B} with hAdef
  have hγl : γ l ∈ B := by
    have h1 : g.expMap (⟨y, l • u⟩ : TangentBundle I M) = γ l :=
      g.expMap_smul_eq_proj_geodesicFlow hr1 y u l (by rw [hD]; exact mem_univ _)
    rw [← h1]
    exact hfoot
  have hlA : l ∈ A := ⟨⟨hl.le, le_rfl⟩, 0, ⟨le_rfl, hh⟩, by rw [hα0]; exact hγl⟩
  have hAne : A.Nonempty := ⟨l, hlA⟩
  have hAbdd : BddBelow A := ⟨0, fun t ht => ht.1.1⟩
  have hAlow : ∀ t ∈ A, l - h ≤ t := by
    rintro t ⟨htI, s, hsI, hsB⟩
    have h1 : infDist (γ t) B ≤ s := (infDist_le_dist_of_mem hsB).trans (hspeed t htI s hsI.1)
    rw [hsegd t htI] at h1
    linarith [hsI.2]
  set t₀ : ℝ := sInf A with ht₀def
  have ht₀ge : l - h ≤ t₀ := le_csInf hAne hAlow
  have ht₀pos : 0 < t₀ := by linarith
  have ht₀l : t₀ ≤ l := csInf_le hAbdd hlA
  have ht₀I : t₀ ∈ Icc 0 l := ⟨ht₀pos.le, ht₀l⟩
  -- columns before `t₀` lie in `Z`
  have hbefore : ∀ t : ℝ, 0 ≤ t → t < t₀ → ∀ s ∈ Icc 0 h, α s t ∈ Z := by
    intro t ht0 htt s hs
    have htl : t < l := lt_of_lt_of_le htt ht₀l
    have hnotA : ∀ s' ∈ Icc 0 h, α s' t ∉ B := fun s' hs' hB =>
      absurd (csInf_le hAbdd ⟨⟨ht0, htl.le⟩, s', hs', hB⟩) (not_le.2 htt)
    have hcol := proj_geodesicFlow_mem_maxSliceLocusOfOrder_of_forall_notMem g hr hnorm hCcl hconv
      (⟨γ t, ξ t⟩ : TangentBundle I M) (hsegZ t ⟨ht0, htl⟩) (hξT t ⟨ht0, htl⟩) (T := h)
      (fun s' hs' => by rw [← hPS]; exact hnotA s' hs')
    rw [hPS]
    exact hcol s hs
  -- a point of the column `t₀` in `B`
  obtain ⟨s₁, hs₁I, hs₁B⟩ : ∃ s ∈ Icc 0 h, α s t₀ ∈ B := by
    have hφc : Continuous fun s => infDist (α s t₀) B := (continuous_infDist_pt B).comp (hcolc t₀)
    obtain ⟨s₁, hs₁mem, hs₁min⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hh)
      hφc.continuousOn
    refine ⟨s₁, hs₁mem, ?_⟩
    rw [hBcl.mem_iff_infDist_zero hBne]
    refine le_antisymm (le_of_forall_pos_le_add fun ε hε => ?_) infDist_nonneg
    obtain ⟨t, htA, htlt⟩ := exists_lt_of_csInf_lt hAne (show t₀ < t₀ + ε by linarith)
    obtain ⟨htI, s, hsI, hsB⟩ := htA
    have ht₀t : t₀ ≤ t := csInf_le hAbdd ⟨htI, s, hsI, hsB⟩
    have hd := hlip' s hsI t₀ ht₀I t htI
    have h1 : infDist (α s t₀) B ≤ dist (α s t₀) (α s t) := infDist_le_dist_of_mem hsB
    have h2 : |t₀ - t| ≤ ε := by rw [abs_of_nonpos (by linarith)]; linarith
    have h3 : infDist (α s₁ t₀) B ≤ infDist (α s t₀) B := hs₁min hsI
    linarith
  -- the column `t₀` lies in `C`
  have hcolC : ∀ s ∈ Icc 0 h, α s t₀ ∈ C := by
    intro s hs
    refine hclZ (Metric.mem_closure_iff.2 fun ε hε => ?_)
    set t : ℝ := max (t₀ / 2) (t₀ - ε / 2) with htdef
    have ht0 : 0 ≤ t := le_trans (by linarith) (le_max_left _ _)
    have htt : t < t₀ := max_lt (by linarith) (by linarith)
    refine ⟨α s t, hbefore t ht0 htt s hs, ?_⟩
    have hd := hlip' s hs t₀ ht₀I t ⟨ht0, htt.le.trans ht₀l⟩
    have hge : t₀ - ε / 2 ≤ t := le_max_right _ _
    rw [abs_of_nonneg (by linarith)] at hd
    linarith
  rcases eq_or_lt_of_le ht₀l with ht₀eq | ht₀lt
  · -- `t₀ = l`: the corner
    refine ⟨l, ⟨hl.le, le_rfl⟩, ⟨?_, hend'⟩⟩
    have h1 := hcolC h ⟨hh, le_rfl⟩
    rwa [ht₀eq] at h1
  · -- `t₀ < l`: the top point of the column `t₀`
    refine ⟨t₀, ht₀I, ?_⟩
    have hγt₀ : γ t₀ ∈ Z := hsegZ t₀ ⟨ht₀pos.le, ht₀lt⟩
    rcases eq_or_lt_of_le hs₁I.2 with hs₁h | hs₁h
    · rw [← hs₁h]; exact hs₁B
    · exfalso
      rcases eq_or_lt_of_le hs₁I.1 with hs₁0 | hs₁0
      · rw [← hs₁0, hα0] at hs₁B
        exact hs₁B.2 hγt₀
      · have hmaps : ∀ s ∈ Icc 0 h,
            (g.geodesicFlow (⟨γ t₀, ξ t₀⟩ : TangentBundle I M) s).proj ∈ C := fun s hs => by
          rw [← hPS]; exact hcolC s hs
        have hstart : (g.geodesicFlow (⟨γ t₀, ξ t₀⟩ : TangentBundle I M) 0).proj ∈ Z := by
          rw [g.geodesicFlow_zero hr1]; exact hγt₀
        have hprop := hconv.proj_geodesicFlow_mem_maxSliceLocusOfOrder hr hnorm _ hmaps
          ⟨le_rfl, hh⟩ hstart s₁ ⟨hs₁0, hs₁h⟩
        rw [← hPS] at hprop
        exact hs₁B.2 hprop

/-- **A1-rel: the relative orthogonal boundary shift** from the REL kernel's prefix-tangent transverse
shift (`2 ≤ r`, `sec ≥ 0`, any dimension). -/
theorem exists_relative_orthogonal_shift_of_transverseShift [NeZero (Module.finrank ℝ E)]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    {C : Set M} (hCcl : IsClosed C) (hconv : IsTotallyConvexFinite g C)
    (hshift : ∀ (x : M) (L : ℝ), ∃ ρ > 0, ∀ p : TangentBundle I M, dist x p.proj < ρ →
      g.inner p.proj p.snd p.snd = 1 → ∀ w : E, g.inner p.proj w w = 1 → g.inner p.proj w p.snd = 0 →
        ∃ ξ : ℝ → E, ξ 0 = w ∧
          (∀ t ∈ Icc 0 L, g.inner (g.geodesicFlow p t).proj (ξ t) (ξ t) = 1 ∧
            g.inner (g.geodesicFlow p t).proj (ξ t) (g.geodesicFlow p t).snd = 0) ∧
          (∀ T ∈ Icc 0 L,
            (∀ t ∈ Icc 0 T, (g.geodesicFlow p t).proj ∈ maxSliceLocusOfOrder I (r : ℕ∞ω) C) →
            w ∈ sliceTangent I (maxSliceLocusOfOrder I (r : ℕ∞ω) C) p.proj →
            ∀ t ∈ Icc 0 T,
              ξ t ∈ sliceTangent I (maxSliceLocusOfOrder I (r : ℕ∞ω) C) (g.geodesicFlow p t).proj) ∧
          ∀ h ∈ Ico 0 ρ, ∀ t₁ ∈ Icc 0 L, ∀ t₂ ∈ Icc 0 L,
            dist (g.expMap (⟨(g.geodesicFlow p t₁).proj, h • ξ t₁⟩ : TangentBundle I M))
              (g.expMap (⟨(g.geodesicFlow p t₂).proj, h • ξ t₂⟩ : TangentBundle I M)) ≤ |t₁ - t₂|)
    {x : M} (hx : x ∈ maxSliceLocusOfOrder I (r : ℕ∞ω) C) :
    ∃ ρ > 0, ∀ y ∈ maxSliceLocusOfOrder I (r : ℕ∞ω) C, dist x y < ρ → ∀ u w : E,
      g.inner y u u = 1 → g.inner y w w = 1 → g.inner y u w = 0 →
      u ∈ sliceTangent I (maxSliceLocusOfOrder I (r : ℕ∞ω) C) y →
      w ∈ sliceTangent I (maxSliceLocusOfOrder I (r : ℕ∞ω) C) y →
      g.expMap (⟨y, infDist y (relBoundaryOfOrder I (r : ℕ∞ω) C) • u⟩ : TangentBundle I M) ∈
        relBoundaryOfOrder I (r : ℕ∞ω) C →
      ∀ h ∈ Ico 0 ρ, infDist (g.expMap (⟨y, h • w⟩ : TangentBundle I M))
          (relBoundaryOfOrder I (r : ℕ∞ω) C) ≤ infDist y (relBoundaryOfOrder I (r : ℕ∞ω) C) := by
  have hr1 : 1 ≤ r := one_le_two.trans hr
  have hD : g.geodesicFlowDomain = univ := g.geodesicFlowDomain_eq_univ hr hnorm
  set Z := maxSliceLocusOfOrder I (r : ℕ∞ω) C with hZdef
  set B := relBoundaryOfOrder I (r : ℕ∞ω) C with hBdef
  have hBcl : IsClosed B := isClosed_relBoundaryOfOrder g hr hnorm hCcl hconv
  rcases B.eq_empty_or_nonempty with hBe | hBne
  · refine ⟨1, one_pos, fun y _ _ u w _ _ _ _ _ hend => ?_⟩
    rw [hBe] at hend
    exact absurd hend (notMem_empty _)
  have hxD : 0 < infDist x B := (hBcl.notMem_iff_infDist_pos hBne).1 fun hB => hB.2 hx
  set L : ℝ := infDist x B + 1 with hLdef
  have : ProperSpace M := Manifold.properSpace_of_isRiemannianManifold I
  obtain ⟨ρ₂, hρ₂, hsh⟩ := hshift x L
  obtain ⟨ρ₃, hρ₃, hRFP⟩ := expMap_notMem_maxSliceLocusOfOrder_of_foot g hr hnorm hsec hCcl hconv
    (isCompact_closedBall x (L + 1))
  refine ⟨min (min (infDist x B / 2) ρ₂) (min ρ₃ 1), by positivity, ?_⟩
  intro y hy hxy u w hu hw huw huT hwT hend h hh
  have hm1 : min (min (infDist x B / 2) ρ₂) (min ρ₃ 1) ≤ infDist x B / 2 :=
    (min_le_left _ _).trans (min_le_left _ _)
  have hm2 : min (min (infDist x B / 2) ρ₂) (min ρ₃ 1) ≤ ρ₂ :=
    (min_le_left _ _).trans (min_le_right _ _)
  have hm3 : min (min (infDist x B / 2) ρ₂) (min ρ₃ 1) ≤ ρ₃ :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hm4 : min (min (infDist x B / 2) ρ₂) (min ρ₃ 1) ≤ 1 :=
    (min_le_right _ _).trans (min_le_right _ _)
  set l : ℝ := infDist y B with hldef
  have hl : 0 < l := (hBcl.notMem_iff_infDist_pos hBne).1 fun hB => hB.2 hy
  have hlL : l < L := by
    have h1 : infDist y B ≤ infDist x B + dist y x := infDist_le_infDist_add_dist
    rw [dist_comm] at h1
    have h2 : dist x y < 1 := lt_of_lt_of_le hxy hm4
    rw [hldef, hLdef]
    linarith
  have hhl : h < l := by
    have h1 : infDist x B ≤ infDist y B + dist x y := infDist_le_infDist_add_dist
    have h2 : dist x y < infDist x B / 2 := lt_of_lt_of_le hxy hm1
    have h3 : h < infDist x B / 2 := lt_of_lt_of_le hh.2 hm1
    rw [hldef]
    linarith
  have hwu : g.inner y w u = 0 := by rw [g.symm y w u]; exact huw
  obtain ⟨ξ, hξ0, hξ, hξpre, hlip⟩ := hsh (⟨y, u⟩ : TangentBundle I M) (lt_of_lt_of_le hxy hm2) hu w
    hw hwu
  have hyC : y ∈ C := maxSliceLocusOfOrder_subset hy
  obtain ⟨-, hsegZ, -⟩ := foot_segment_relBoundaryOfOrder g hr hnorm hconv hyC hu hend
  have hξT : ∀ t ∈ Ico 0 l, ξ t ∈ sliceTangent I Z (g.geodesicFlow (⟨y, u⟩ : TangentBundle I M) t).proj :=
    fun t ht => hξpre t ⟨ht.1, ht.2.le.trans hlL.le⟩
      (fun τ hτ => hsegZ τ ⟨hτ.1, lt_of_le_of_lt hτ.2 ht.2⟩) hwT t ⟨ht.1, le_rfl⟩
  have hhρ₂ : h < ρ₂ := lt_of_lt_of_le hh.2 hm2
  have hlipl : ∀ s ∈ Icc 0 h, ∀ t₁ ∈ Icc 0 l, ∀ t₂ ∈ Icc 0 l,
      dist (g.expMap (⟨(g.geodesicFlow (⟨y, u⟩ : TangentBundle I M) t₁).proj, s • ξ t₁⟩ :
          TangentBundle I M))
        (g.expMap (⟨(g.geodesicFlow (⟨y, u⟩ : TangentBundle I M) t₂).proj, s • ξ t₂⟩ :
          TangentBundle I M)) ≤ |t₁ - t₂| := fun s hs t₁ ht₁ t₂ ht₂ =>
    hlip s ⟨hs.1, lt_of_le_of_lt hs.2 hhρ₂⟩ t₁ ⟨ht₁.1, ht₁.2.trans hlL.le⟩ t₂
      ⟨ht₂.1, ht₂.2.trans hlL.le⟩
  -- the corner is not in `Z` (relative foot point)
  have hfootflow : (g.geodesicFlow (⟨y, u⟩ : TangentBundle I M) l).proj ∈ B := by
    rw [← g.expMap_smul_eq_proj_geodesicFlow hr1 y u l (by rw [hD]; exact mem_univ _)]
    exact hend
  have hξl := hξ l ⟨hl.le, hlL.le⟩
  have hdyP : dist y (g.geodesicFlow (⟨y, u⟩ : TangentBundle I M) l).proj ≤ l := by
    have h1 := g.dist_proj_geodesicFlow_le hr1 hnorm (p := (⟨y, u⟩ : TangentBundle I M)) (s := 0)
      (t := l) (fun τ _ => by rw [hD]; exact mem_univ _)
    rw [g.geodesicFlow_zero hr1] at h1
    change dist y _ ≤ Real.sqrt (g.inner y u u) * |l - 0| at h1
    rw [hu, Real.sqrt_one, one_mul, sub_zero, abs_of_pos hl] at h1
    exact h1
  set P := g.geodesicFlow (⟨y, u⟩ : TangentBundle I M) l with hPdef
  have hPK : P.proj ∈ closedBall x (L + 1) := by
    rw [mem_closedBall]
    have h2 := dist_triangle P.proj y x
    have h3 : dist x y < 1 := lt_of_lt_of_le hxy hm4
    rw [dist_comm P.proj y, dist_comm y x] at h2
    linarith
  have hperp : 0 ≤ g.inner P.proj (h • ξ l) P.snd := by
    have h2 : g.inner P.proj (h • ξ l) = h • g.inner P.proj (ξ l) := (g.inner P.proj).map_smul h (ξ l)
    have h3 : g.inner P.proj (h • ξ l) P.snd = h * g.inner P.proj (ξ l) P.snd := by
      rw [h2]; rfl
    rw [h3, hξl.2, mul_zero]
  have hlen : g.inner P.proj (h • ξ l) (h • ξ l) < ρ₃ ^ 2 := by
    have h2 : g.inner P.proj (h • ξ l) (h • ξ l) = h ^ 2 * g.inner P.proj (ξ l) (ξ l) :=
      DifferentialGeometry.Geometry.Collapse.finite_inner_smul_self g _ h (ξ l)
    rw [h2, hξl.1, mul_one]
    have h1 : h < ρ₃ := lt_of_lt_of_le hh.2 hm3
    nlinarith [hh.1]
  have hcorner := hRFP y hyC u hu hl hfootflow hPK (h • ξ l) hperp hlen
  obtain ⟨t, htI, htB⟩ := exists_mem_relBoundaryOfOrder_of_shift_rectangle g hr hnorm hCcl hconv hy
    hu hend hh.1 hhl (fun t ht => (hξ t ⟨ht.1, ht.2.trans hlL.le⟩).1) hξT hlipl hcorner
  have hc0 : g.expMap (⟨(g.geodesicFlow (⟨y, u⟩ : TangentBundle I M) 0).proj, h • ξ 0⟩ :
      TangentBundle I M) = g.expMap (⟨y, h • w⟩ : TangentBundle I M) := by
    rw [hξ0]
    exact expMap_mk_congr g (by rw [g.geodesicFlow_zero hr1]) (h • w)
  calc infDist (g.expMap (⟨y, h • w⟩ : TangentBundle I M)) B
      = infDist (g.expMap (⟨(g.geodesicFlow (⟨y, u⟩ : TangentBundle I M) 0).proj, h • ξ 0⟩ :
          TangentBundle I M)) B := by rw [hc0]
    _ ≤ dist (g.expMap (⟨(g.geodesicFlow (⟨y, u⟩ : TangentBundle I M) 0).proj, h • ξ 0⟩ :
          TangentBundle I M))
        (g.expMap (⟨(g.geodesicFlow (⟨y, u⟩ : TangentBundle I M) t).proj, h • ξ t⟩ :
          TangentBundle I M)) := infDist_le_dist_of_mem htB
    _ ≤ |0 - t| := hlipl h ⟨hh.1, le_rfl⟩ 0 ⟨le_rfl, hl.le⟩ t htI
    _ = t := by rw [zero_sub, abs_neg, abs_of_nonneg htI.1]
    _ ≤ l := htI.2

end DifferentialGeometry.Geometry.FiniteSoul

end
