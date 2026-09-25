import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedralTubeTraces
import DifferentialGeometry.Topology.PiecewiseLinear.Section34AnnulusDiskLocalization

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem HasPLCrossingAt.exists_connected_inside_slice {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {A X : Set E} {x : E}
    (hcross : HasPLCrossingAt A (frontier X) x)
    (hA : ∀ N ∈ 𝓝 x, ∃ (c : EuclideanSpace ℝ (Fin 2)) (r : ℝ)
      (g : EuclideanSpace ℝ (Fin 2) → E), 0 < r ∧ ContinuousOn g (Metric.ball c r) ∧
        InjOn g (Metric.ball c r) ∧ MapsTo g (Metric.ball c r) (A ∩ N) ∧ g c = x)
    (hXc : IsClosed X) (hX : x ∈ closure (interior X)) :
    ∃ U : Set E, IsOpen U ∧ x ∈ U ∧
      IsPreconnected (A ∩ interior X ∩ U) ∧ x ∈ closure (A ∩ interior X ∩ U) := by
  obtain ⟨U, φ, ρ, hU, hxU, hρ, hφ, hφx, hloc⟩ := hcross.exists_sideChart hA hXc hX
  let ψ := Function.invFunOn φ U
  have hψφ : ∀ y ∈ U, ψ (φ y) = y := fun y hy => hφ.bijOn.invOn_invFunOn.1 hy
  have hφψ : ∀ z ∈ Metric.ball (0 : ℝ × ℝ × ℝ) ρ, φ (ψ z) = z :=
    fun z hz => hφ.bijOn.invOn_invFunOn.2 hz
  have hψU : ∀ z ∈ Metric.ball (0 : ℝ × ℝ × ℝ) ρ, ψ z ∈ U :=
    fun z hz => hφ.symm.bijOn.mapsTo hz
  have hψc : ContinuousOn ψ (Metric.ball (0 : ℝ × ℝ × ℝ) ρ) :=
    hφ.isPiecewiseAffineOn_invFunOn.continuousOn
  have hinside : ∀ y ∈ U, y ∈ interior X ↔ 0 < (φ y).2.1 := by
    intro y hy
    constructor
    · intro hyX
      have hnn := (hloc y hy).2.2.mp (interior_subset hyX)
      refine lt_of_le_of_ne hnn ?_
      intro heq
      exact disjoint_left.mp disjoint_interior_frontier hyX
        ((hloc y hy).2.1.mpr heq.symm)
    · intro hpos
      have hyX := (hloc y hy).2.2.mpr hpos.le
      exact (mem_interior_iff_notMem_frontier hyX).mpr fun hyfr =>
        hpos.ne' ((hloc y hy).2.1.mp hyfr)
  let H : Set (ℝ × ℝ × ℝ) := Metric.ball 0 ρ ∩ {z | z.2.2 = 0 ∧ 0 < z.2.1}
  have hH : IsPreconnected H := by
    refine ((convex_ball (0 : ℝ × ℝ × ℝ) ρ).inter ?_).isPreconnected
    intro a ha b hb s t hs ht hst
    change (s • a + t • b).2.2 = 0 ∧ 0 < (s • a + t • b).2.1
    refine ⟨by simp [ha.1, hb.1], ?_⟩
    have heq : (s • a + t • b).2.1 = s * a.2.1 + t * b.2.1 := by simp
    rw [heq]
    rcases eq_or_lt_of_le hs with hs0 | hs0
    · subst hs0
      have ht1 : t = 1 := by linarith
      simpa only [ht1, zero_mul, zero_add, one_mul] using hb.2
    · have := mul_pos hs0 ha.2
      nlinarith [mul_nonneg ht hb.2.le]
  have himage : ψ '' H = A ∩ interior X ∩ U := by
    apply Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      refine ⟨⟨(hloc (ψ z) (hψU z hz.1)).1.mpr ?_,
        (hinside (ψ z) (hψU z hz.1)).mpr ?_⟩, hψU z hz.1⟩
      · rw [hφψ z hz.1]
        exact hz.2.1
      · rw [hφψ z hz.1]
        exact hz.2.2
    · rintro y ⟨⟨hyA, hyX⟩, hyU⟩
      exact ⟨φ y, ⟨hφ.bijOn.mapsTo hyU, (hloc y hyU).1.mp hyA,
        (hinside y hyU).mp hyX⟩, hψφ y hyU⟩
  have hzero : (0 : ℝ × ℝ × ℝ) ∈ closure H := by
    have hcont : Continuous (fun t : ℝ => ((0 : ℝ), t, (0 : ℝ))) := by fun_prop
    have htend : Filter.Tendsto (fun t : ℝ => ((0 : ℝ), t, (0 : ℝ)))
        (𝓝[>] 0) (𝓝 (0 : ℝ × ℝ × ℝ)) := by
      exact (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
    apply mem_closure_of_tendsto htend
    filter_upwards [htend.eventually_mem (Metric.isOpen_ball.mem_nhds
      (Metric.mem_ball_self hρ)), self_mem_nhdsWithin] with t htball ht
    exact ⟨htball, rfl, ht⟩
  refine ⟨U, hU, hxU, himage ▸ hH.image ψ (hψc.mono inter_subset_left), ?_⟩
  have hψ0 : ψ 0 = x := hφx ▸ hψφ x hxU
  have hmem := (hψc.continuousAt (Metric.isOpen_ball.mem_nhds
    (Metric.mem_ball_self hρ))).continuousWithinAt.mem_closure_image hzero
  rwa [hψ0, himage] at hmem

theorem exists_ball_chart_of_mem_nhdsWithin_surface {M : Type*} [TopologicalSpace M]
    {B A : Set M} [ChartedSpace (EuclideanSpace ℝ (Fin 2)) B] {x : M}
    (hxB : x ∈ B) (hA : A ∈ 𝓝[B] x) {N : Set M} (hN : N ∈ 𝓝 x) :
    ∃ (c : EuclideanSpace ℝ (Fin 2)) (r : ℝ) (g : EuclideanSpace ℝ (Fin 2) → M),
      0 < r ∧ ContinuousOn g (Metric.ball c r) ∧ InjOn g (Metric.ball c r) ∧
        MapsTo g (Metric.ball c r) (A ∩ N) ∧ g c = x := by
  let ch := chartAt (EuclideanSpace ℝ (Fin 2)) (⟨x, hxB⟩ : B)
  have hxch : (⟨x, hxB⟩ : B) ∈ ch.source :=
    mem_chart_source (EuclideanSpace ℝ (Fin 2)) _
  let c := ch ⟨x, hxB⟩
  let g : EuclideanSpace ℝ (Fin 2) → M := fun z => (ch.symm z).val
  have hct : c ∈ ch.target := ch.map_source hxch
  have hgc : ContinuousOn g ch.target := continuous_subtype_val.comp_continuousOn
    ch.symm.continuousOn
  have hgcx : g c = x := congrArg Subtype.val (ch.left_inv hxch)
  obtain ⟨O, hO, hOB⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hA
  have hpre : ch.target ∩ g ⁻¹' (N ∩ O) ∈ 𝓝 c :=
    Filter.inter_mem (ch.open_target.mem_nhds hct)
      ((hgc.continuousAt (ch.open_target.mem_nhds hct)).preimage_mem_nhds
        (hgcx.symm ▸ Filter.inter_mem hN hO))
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hpre
  refine ⟨c, r, g, hr, hgc.mono (hball.trans inter_subset_left), ?_, ?_, hgcx⟩
  · intro y hy z hz hyz
    exact ch.symm.injOn (hball hy).1 (hball hz).1 (Subtype.ext hyz)
  · intro y hy
    exact ⟨hOB ⟨(hball hy).2.2, (ch.symm y).property⟩, (hball hy).2.1⟩

theorem IsPLCellOn.exists_ball_chart_in_annulus {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {S B A A₀ A₁ : Set M} (hS : IsPLCellOn 3 S B) (hA : IsAnnulusOn A A₀ A₁)
    (hAB : A ⊆ B) {x : M} (hx : x ∈ A) (hxends : x ∉ A₀ ∪ A₁)
    {N : Set M} (hN : N ∈ 𝓝 x) :
    ∃ (c : EuclideanSpace ℝ (Fin 2)) (r : ℝ) (g : EuclideanSpace ℝ (Fin 2) → M),
      0 < r ∧ ContinuousOn g (Metric.ball c r) ∧ InjOn g (Metric.ball c r) ∧
        MapsTo g (Metric.ball c r) (A ∩ N) ∧ g c = x := by
  obtain ⟨hchart⟩ := hS.nonempty_chartedSpace_boundary
  let _ := hchart
  have hA' := hA.preimage_subtype hAB
  have hxA : (⟨x, hAB hx⟩ : B) ∈ (Subtype.val : B → M) ⁻¹' A := hx
  have hxint : (⟨x, hAB hx⟩ : B) ∈ interior ((Subtype.val : B → M) ⁻¹' A) :=
    (mem_interior_iff_notMem_frontier hxA).mpr fun hfr =>
      hxends (hA'.frontier_subset hfr)
  obtain ⟨O, hO, hOeq⟩ := isOpen_induced_iff.mp
    (isOpen_interior : IsOpen (interior ((Subtype.val : B → M) ⁻¹' A)))
  have hxO' : (⟨x, hAB hx⟩ : B) ∈ (Subtype.val : B → M) ⁻¹' O :=
    hOeq.symm ▸ hxint
  have hxO : x ∈ O := hxO'
  have hAn : A ∈ 𝓝[B] x := by
    refine mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr ⟨O, hO.mem_nhds hxO, ?_⟩
    rintro y ⟨hyO, hyB⟩
    have hy : (⟨y, hyB⟩ : B) ∈ (Subtype.val : B → M) ⁻¹' O := hyO
    have hyint : (⟨y, hyB⟩ : B) ∈ interior ((Subtype.val : B → M) ⁻¹' A) :=
      hOeq ▸ hy
    exact show (⟨y, hyB⟩ : B) ∈ (Subtype.val : B → M) ⁻¹' A from
      interior_subset hyint
  exact exists_ball_chart_of_mem_nhdsWithin_surface (hAB hx) hAn hN

theorem exists_connected_inside_slice_of_chart_crossing {M : Type*} [TopologicalSpace M]
    {A X : Set M} {x : M} (hXc : IsClosed X) (hX : x ∈ closure (interior X))
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))) (hx : x ∈ c.source)
    (hcross : HasPLCrossingAt (c '' (A ∩ c.source))
      (c '' (frontier X ∩ c.source)) (c x))
    (hA : ∀ N ∈ 𝓝 x, ∃ (a : EuclideanSpace ℝ (Fin 2)) (r : ℝ)
      (g : EuclideanSpace ℝ (Fin 2) → M), 0 < r ∧ ContinuousOn g (Metric.ball a r) ∧
        InjOn g (Metric.ball a r) ∧ MapsTo g (Metric.ball a r) (A ∩ N) ∧ g a = x) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
      IsPreconnected (A ∩ interior X ∩ U) ∧ x ∈ closure (A ∩ interior X ∩ U) := by
  have himage (Z : Set M) : c.IsImage Z (c '' (Z ∩ c.source)) := by
    intro y hy
    constructor
    · rintro ⟨z, ⟨hz, hzs⟩, hzy⟩
      exact c.injOn hzs hy hzy ▸ hz
    · exact fun hyZ => ⟨y, ⟨hyZ, hy⟩, rfl⟩
  let Y := closure (c '' (X ∩ c.source))
  have hY : c.IsImage X Y := by
    have hh := (himage X).closure
    rwa [hXc.closure_eq] at hh
  have hfront : ∀ᶠ z in 𝓝 (c x),
      z ∈ c '' (frontier X ∩ c.source) ↔ z ∈ frontier Y := by
    filter_upwards [c.open_target.mem_nhds (c.map_source hx)] with z hz
    exact ((himage (frontier X)).symm hz).symm.trans (hY.frontier.symm hz)
  have hcross' : HasPLCrossingAt (c '' (A ∩ c.source)) (frontier Y) (c x) :=
    hcross.congr (Filter.Eventually.of_forall fun _ => Iff.rfl) hfront
  have hAc : ∀ N ∈ 𝓝 (c x), ∃ (a : EuclideanSpace ℝ (Fin 2)) (r : ℝ)
      (g : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)),
      0 < r ∧ ContinuousOn g (Metric.ball a r) ∧ InjOn g (Metric.ball a r) ∧
        MapsTo g (Metric.ball a r) ((c '' (A ∩ c.source)) ∩ N) ∧ g a = c x := by
    intro N hN
    have hpre : c.source ∩ c ⁻¹' N ∈ 𝓝 x := Filter.inter_mem
      (c.open_source.mem_nhds hx) ((c.continuousAt hx).preimage_mem_nhds hN)
    obtain ⟨a, r, g, hr, hgc, hgi, hgmap, hga⟩ := hA _ hpre
    have hgs : MapsTo g (Metric.ball a r) c.source := fun y hy => (hgmap hy).2.1
    refine ⟨a, r, c ∘ g, hr, c.continuousOn.comp hgc hgs, ?_, ?_, ?_⟩
    · intro y hy z hz hyz
      exact hgi hy hz (c.injOn (hgs hy) (hgs hz) hyz)
    · intro y hy
      exact ⟨⟨g y, ⟨(hgmap hy).1, (hgmap hy).2.1⟩, rfl⟩, (hgmap hy).2.2⟩
    · change c (g a) = c x
      rw [hga]
  obtain ⟨V, hV, hxV, hconn, hdense⟩ := hcross'.exists_connected_inside_slice hAc
    isClosed_closure ((hY.interior.closure hx).mpr hX)
  let U := c.source ∩ c ⁻¹' V
  have hslice : c.symm '' ((c '' (A ∩ c.source)) ∩ interior Y ∩ V) =
      A ∩ interior X ∩ U := by
    apply Subset.antisymm
    · rintro _ ⟨z, ⟨⟨⟨y, ⟨hyA, hys⟩, rfl⟩, hyY⟩, hyV⟩, rfl⟩
      rw [c.left_inv hys]
      exact ⟨⟨hyA, (hY.interior hys).mp hyY⟩, hys, hyV⟩
    · rintro y ⟨⟨hyA, hyX⟩, hys, hyV⟩
      exact ⟨c y, ⟨⟨⟨y, ⟨hyA, hys⟩, rfl⟩, (hY.interior hys).mpr hyX⟩, hyV⟩,
        c.left_inv hys⟩
  have htarget : (c '' (A ∩ c.source)) ∩ interior Y ∩ V ⊆ c.target := by
    rintro z ⟨⟨⟨y, ⟨-, hys⟩, rfl⟩, -⟩, -⟩
    exact c.map_source hys
  refine ⟨U, c.isOpen_inter_preimage hV, ⟨hx, hxV⟩,
    hslice ▸ hconn.image c.symm (c.symm.continuousOn.mono htarget), ?_⟩
  have hmem := (c.symm.continuousAt (c.map_source hx)).continuousWithinAt.mem_closure_image hdense
  rwa [c.left_inv hx, hslice] at hmem

end DifferentialGeometry.Topology.PiecewiseLinear
