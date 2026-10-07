import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HCX3ExtFinal_S109

set_option autoImplicit false

/-! # CH12-S120: `hCX3ext` v4 = `hCX3ext_S109` plus the conjunct `O ⊆ V` (O54 FINDING F3, ruling (A))

`exists_CkSmall_transfer_field_CX3` (through S99) is a black box whose hypotheses on `Φ`
(`ContMDiffOn Φ O`, displacement `< ρ` on `O`) refer to ITS neighbourhood `O`; restricting `O` to
`O ∩ V` weakens them and cannot be derived from the statement.  So the two lemmas that produce `O`
are re-run with `O := O ∩ U` (`exists_transfer_section_sub_S120`, S15 H1-C; and
`exists_CkSmall_transfer_field_sub_S120`, CX3 H1-E in `riemannianEDistOf g` form), then the S109
core / assembly are repeated with the extra conjunct. -/

noncomputable section
open scoped Manifold ContDiff Topology ENNReal
open Set Function Bundle Filter Metric

namespace GC.LongTime.Ch12
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Geometry.Riemannian.Exponential DifferentialGeometry.Geometry.Hyperbolic

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

section Generic1
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)] [LocallyCompactSpace M]

variable (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)

/-- **H1-C with a prescribed ambient open set** (`exists_transfer_section_S15`, `O := O ∩ U`). -/
theorem exists_transfer_section_sub_S120 {K U : Set M} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) :
    ∃ O : Set M, IsOpen O ∧ K ⊆ O ∧ O ⊆ U ∧ ∃ ρ : ℝ, 0 < ρ ∧
      ∀ Φ : M → M, ContMDiffOn I I ∞ Φ O →
        (∀ p ∈ O, Manifold.riemannianEDist I p (Φ p) < ENNReal.ofReal ρ) →
        ∃ v : M → TangentBundle I M, ContMDiffOn I I.tangent ∞ v O ∧
          ∀ p ∈ O, (v p).proj = p ∧ expMapIntrinsic g hEnorm p (v p).snd = Φ p ∧
            tanLen_S15 g (v p) = (Manifold.riemannianEDist I p (Φ p)).toReal := by
  classical
  let B : ∀ p : M, DiagonalInverseBranch g hEnorm p :=
    fun p => standardDiagonalInverseBranch g hEnorm p
  have htube : ∀ p : M, ∃ W ∈ 𝓝 p, ∃ r : ℝ, 0 < r ∧
      ∀ u : TangentBundle I M, u.proj ∈ W → tanLen_S15 g u < r → u ∈ (B p).hom.source :=
    fun p => exists_short_vectors_subset_S15 g (B p).hom.open_source (B p).zero_mem
  choose W hW r hr hrW using htube
  obtain ⟨t, -, hcov⟩ := hK.elim_nhds_subcover (fun p => interior (W p))
    (fun p _ => interior_mem_nhds.mpr (hW p))
  obtain ⟨ρ, hρ, hρle⟩ := exists_pos_le_finset_S15 t r hr
  refine ⟨(⋃ x ∈ t, interior (W x)) ∩ U, ?_, fun p hp => ⟨hcov hp, hKU hp⟩, inter_subset_right,
    ρ, hρ, ?_⟩
  · exact (isOpen_biUnion fun x _ => isOpen_interior).inter hU
  intro Φ hΦ hd
  set O : Set M := (⋃ x ∈ t, interior (W x)) ∩ U with hO
  have hfib : ∀ x ∈ t, ∀ p ∈ interior (W x), ∀ w : TangentSpace I p,
      Real.sqrt (g.inner p w w) < ρ → (⟨p, w⟩ : TangentBundle I M) ∈ (B x).hom.source :=
    fun x hx p hp w hw => hrW x ⟨p, w⟩ (interior_subset hp) (lt_of_lt_of_le hw (hρle x hx))
  have hmin : ∀ x ∈ t, ∀ p ∈ interior (W x), p ∈ O → ∃ w : TangentSpace I p,
      (p, Φ p) ∈ (B x).dom ∧ (B x).inv (p, Φ p) = (⟨p, w⟩ : TangentBundle I M) ∧
      expMapIntrinsic g hEnorm p w = Φ p ∧
      Real.sqrt (g.inner p w w) = (Manifold.riemannianEDist I p (Φ p)).toReal :=
    fun x hx p hp hpO => (B x).inv_is_min_of_fiber_ball_subset (hd p hpO) (hfib x hx p hp)
  have hex : ∀ p ∈ O, ∃ x ∈ t, p ∈ interior (W x) := fun p hp => by
    obtain ⟨x, hx, h⟩ := mem_iUnion₂.mp hp.1
    exact ⟨x, hx, h⟩
  let c : M → M := fun p => if h : p ∈ O then Classical.choose (hex p h) else p
  have hc : ∀ p ∈ O, c p ∈ t ∧ p ∈ interior (W (c p)) := by
    intro p hp
    simp only [c, hp, ↓reduceDIte]
    exact Classical.choose_spec (hex p hp)
  let v : M → TangentBundle I M := fun p => (B (c p)).inv (p, Φ p)
  have hagree : ∀ x ∈ t, ∀ p ∈ interior (W x), p ∈ O → v p = (B x).inv (p, Φ p) := by
    intro x hx p hp hpO
    obtain ⟨hct, hcp⟩ := hc p hpO
    exact (B (c p)).inv_eq_of_fiber_ball_subset (B x) (hd p hpO) (hfib _ hct p hcp) (hfib x hx p hp)
  refine ⟨v, ?_, ?_⟩
  · apply contMDiffOn_of_locally_contMDiffOn
    intro p0 hp0
    obtain ⟨x, hx, hpx⟩ := hex p0 hp0
    refine ⟨interior (W x), isOpen_interior, hpx, ?_⟩
    have hpair : ContMDiffOn I (I.prod I) ∞ (fun q : M => (q, Φ q)) (O ∩ interior (W x)) :=
      (contMDiffOn_id.prodMk hΦ).mono inter_subset_left
    have hmaps : MapsTo (fun q : M => (q, Φ q)) (O ∩ interior (W x)) (B x).hom.target := by
      intro q hq
      obtain ⟨_, hdom, -⟩ := hmin x hx q hq.2 hq.1
      exact hdom
    have hsm := (B x).inv_contMDiffOn.comp hpair hmaps
    refine hsm.congr ?_
    intro q hq
    exact hagree x hx q hq.2 hq.1
  · intro p hp
    obtain ⟨hct, hcp⟩ := hc p hp
    obtain ⟨w, -, hw1, hw2, hw3⟩ := hmin (c p) hct p hcp hp
    have hvp : v p = (⟨p, w⟩ : TangentBundle I M) := hw1
    rw [hvp]
    exact ⟨rfl, hw2, hw3⟩

/-- **H1-E with a prescribed ambient open set** (`exists_CkSmall_transfer_field_CX3`, in
`riemannianEDistOf g` form, `O := O ∩ U`, v-conjuncts not needed downstream are dropped). -/
theorem exists_CkSmall_transfer_field_sub_S120 (A : CkAtlas_S15 I M)
    {D1 D2 U : Set M} (hD1 : IsCompact D1) (hD2 : IsCompact D2)
    (hD12 : D1 ⊆ interior D2) (hU : IsOpen U) (hD2U : D2 ⊆ U) (k : ℕ) :
    ∃ O : Set M, IsOpen O ∧ D2 ⊆ O ∧ O ⊆ U ∧ ∃ ρ : ℝ, 0 < ρ ∧ ∃ χ : M → ℝ,
      ContMDiff I 𝓘(ℝ, ℝ) ∞ χ ∧ (∀ p ∈ D1, χ p = 1) ∧
      (∀ p, χ p ∈ Icc (0 : ℝ) 1) ∧ tsupport χ ⊆ interior D2 ∧
      ∀ ε : ℝ, 0 < ε → ∃ ε' : ℝ, 0 < ε' ∧
        ∀ Φ : M → M, ContMDiffOn I I ∞ Φ O →
          (∀ p ∈ O, riemannianEDistOf g p (Φ p) < ENNReal.ofReal ρ) →
          CkCloseInAtlas_CX3 A D2 k ε' Φ →
          ∃ v : M → TangentBundle I M,
            ContMDiff I I.tangent ∞ (secBundle_S15 (fun p => χ p • secOf_S15 v p)) ∧
            (∀ p ∈ D1, expMapIntrinsic g hEnorm p (χ p • secOf_S15 v p) = Φ p) ∧
            (∀ p, p ∉ D2 → χ p • secOf_S15 v p = 0) ∧
            CkSmall_S15 g A (fun p => χ p • secOf_S15 v p) k ε := by
  classical
  obtain ⟨O, hO, hD2O, hOU, ρ, hρ, hsec⟩ := exists_transfer_section_sub_S120 g hEnorm hD2 hU hD2U
  obtain ⟨W, hW, hD1W, hWD2, _⟩ :=
    exists_open_between_and_isCompact_closure hD1 isOpen_interior hD12
  obtain ⟨χ, hχ, hrange, hsupp, hone⟩ :=
    exists_contMDiff_support_eq_eq_one_iff I hW hD1.isClosed hD1W
  have hts : tsupport χ ⊆ interior D2 := by rw [tsupport, hsupp]; exact hWD2
  have htsO : tsupport χ ⊆ O := hts.trans (interior_subset.trans hD2O)
  obtain ⟨N, hN, hdiag, hlog, huniq⟩ := exists_transferLog_domain_CX3 g hEnorm
  have hlocal := fun i : Fin A.n => exists_graph_jet_bound_CX3
    (isCompact_closedBall (extChartAt I (A.ctr i) (A.ctr i)) (A.rad i))
    (logChartDom_open_CX3 (A.ctr i) hN)
    (cutoffLogCoord_smooth_CX3 g hEnorm (A.ctr i) hN hlog χ hχ)
    (fun x hx => logChartDom_zero_CX3 (A.ctr i) hdiag (A.closedBall_sub i hx)) k
  choose d C hd hC hlocal using hlocal
  refine ⟨O, hO, hD2O, hOU, ρ, hρ, χ, hχ, fun p hp => (hone p).mp hp,
    fun p => hrange ⟨p, rfl⟩, hts, ?_⟩
  intro ε hε
  have hlength := fun i : Fin A.n => exists_cutoffLog_length_bound_CX3 g hEnorm (A.ctr i)
    hN hdiag hlog χ hχ
    (isCompact_closedBall (extChartAt I (A.ctr i) (A.ctr i)) (A.rad i)) (A.closedBall_sub i) hε
  choose l hl hlength using hlength
  obtain ⟨ε', hε', hε'le⟩ := exists_pos_forall_le_fin_S15 A.n
    (fun i => min (d i) (min (l i) (ε / (2 * C i))))
    (fun i => lt_min (hd i) (lt_min (hl i) (div_pos hε (mul_pos (by norm_num) (hC i)))))
  refine ⟨ε', hε', ?_⟩
  intro Φ hΦ hdist hclose
  obtain ⟨v, hvs, hv⟩ := hsec Φ hΦ (fun p hp =>
    lt_of_eq_of_lt (riemannianEDistOf_eq_riemannianEDist g hEnorm p (Φ p)).symm (hdist p hp))
  refine ⟨v, cutoff_section_smooth_CX3 hO χ hχ htsO v hvs (fun p hp => (hv p hp).1),
    ?_, ?_, ?_⟩
  · intro p hp
    rw [(hone p).mp hp, one_smul]
    exact (hv p (hD2O (interior_subset (hD12 hp)))).2.1
  · intro p hp
    have hz : χ p = 0 := by
      by_contra hn
      exact hp (interior_subset (hts (subset_tsupport _ hn)))
    rw [hz, zero_smul]
  · intro i x hx
    have hxT := A.closedBall_sub i hx
    by_cases hp : (extChartAt I (A.ctr i)).symm x ∈ tsupport χ
    · have hpO := htsO hp
      have hclosex := hclose i x hx (interior_subset (hts hp))
      let c : E → E := chartDisplacement_CX3 (I := I) (A.ctr i) Φ
      have hc : ContDiffAt ℝ ∞ c x :=
        chartDisplacement_contDiffAt_CX3 (A.ctr i) hO hΦ hxT hpO hclosex.1
      have hδd : ε' ≤ d i := (hε'le i).trans (min_le_left _ _)
      have hδl : ε' ≤ l i := (hε'le i).trans ((min_le_right _ _).trans (min_le_left _ _))
      have hδC : ε' ≤ ε / (2 * C i) :=
        (hε'le i).trans ((min_le_right _ _).trans (min_le_right _ _))
      obtain ⟨hdom, hjet⟩ := hlocal i c x hx (hc.of_le (by exact_mod_cast le_top)) ε' hε'.le hδd
        (fun j hj => (hclosex.2 j hj).le)
      have hcx : ‖c x‖ ≤ l i := by
        have hz := (hclosex.2 0 (Nat.zero_le k)).le
        rw [norm_iteratedFDeriv_zero] at hz
        exact hz.trans hδl
      have hb : (fun y => secBundle_S15 (fun p => χ p • secOf_S15 v p)
          ((extChartAt I (A.ctr i)).symm y)) =ᶠ[𝓝 x]
          (fun y => cutoffLogBundle_CX3 g hEnorm (A.ctr i) χ (y, c y)) := by
        have hs : ContinuousAt (extChartAt I (A.ctr i)).symm x :=
          (continuousOn_extChartAt_symm (A.ctr i)).continuousAt
            ((isOpen_extChartAt_target (A.ctr i)).mem_nhds hxT)
        have hq : ContinuousAt (fun y => Φ ((extChartAt I (A.ctr i)).symm y)) x :=
          (hΦ.continuousOn.continuousAt (hO.mem_nhds hpO)).comp hs
        have hgraph : ContinuousAt (fun y : E => (y, c y)) x :=
          continuousAt_id.prodMk hc.continuousAt
        filter_upwards [hs (hO.mem_nhds hpO),
          hq ((isOpen_extChartAt_source (A.ctr i)).mem_nhds hclosex.1),
          hgraph ((logChartDom_open_CX3 (A.ctr i) hN).mem_nhds hdom)] with y hyO hyq hyN
        exact cutoffLog_eq_section_CX3 g hEnorm (A.ctr i) χ huniq v hyq hyN (hv _ hyO)
      refine ⟨?_, ?_⟩
      · rw [hb.eq_of_nhds]
        exact (hlength i x hx (c x) hcx).2
      · intro j hj
        have hcoord : coordSec_S15 (A.ctr i) (fun p => χ p • secOf_S15 v p) =ᶠ[𝓝 x]
            (fun y => cutoffLogCoord_CX3 g hEnorm (A.ctr i) χ (y, c y)) := by
          filter_upwards [hb] with y hy
          exact congrArg (fun u : TangentBundle I M =>
            ((trivializationAt E (TangentSpace I) (A.ctr i)) u).2) hy
        have hz : (fun y => cutoffLogCoord_CX3 g hEnorm (A.ctr i) χ (y, (0 : E))) =ᶠ[𝓝 x]
            (fun _ => (0 : E)) := by
          filter_upwards [(isOpen_extChartAt_target (A.ctr i)).mem_nhds hxT] with y hy
          exact cutoffLogCoord_zero_CX3 g hEnorm (A.ctr i) χ hy
        have hjbound := hjet j hj
        rw [(hz.iteratedFDeriv ℝ j).eq_of_nhds, iteratedFDeriv_fun_zero, Pi.zero_apply,
          sub_zero] at hjbound
        rw [(hcoord.iteratedFDeriv ℝ j).eq_of_nhds]
        refine lt_of_le_of_lt hjbound ?_
        have hmul := (le_div_iff₀ (mul_pos (by norm_num) (hC i))).mp hδC
        nlinarith
    · have hz : χ ((extChartAt I (A.ctr i)).symm x) = 0 :=
        (notMem_tsupport_iff_eventuallyEq.mp hp).eq_of_nhds
      constructor
      · simp only [secBundle_S15, hz, zero_smul, tanLen_S15]
        change Real.sqrt (g.inner ((extChartAt I (A.ctr i)).symm x)
          (0 : TangentSpace I ((extChartAt I (A.ctr i)).symm x))
          (0 : TangentSpace I ((extChartAt I (A.ctr i)).symm x))) < ε
        rw [map_zero, Real.sqrt_zero]
        exact hε
      · intro j _
        rw [((cutoff_coord_zero_germ_CX3 (A.ctr i) χ v hxT hp).iteratedFDeriv ℝ j).eq_of_nhds]
        simpa only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero] using hε

/-- **Core v4** = `hCX3ext_core_S109` with the extra conjunct `O ⊆ V` (`O := O ∩ V` inside). -/
theorem hCX3ext_core_v4_S120 [ConnectedSpace M] (A : CkAtlas_S15 I M)
    {D1 D2 V : Set M} (hD1 : IsCompact D1) (hD2 : IsCompact D2) (hD12 : D1 ⊆ interior D2)
    (hD2A : D2 ⊆ A.cover) (hV : IsOpen V) (hD2V : D2 ⊆ V) (k : ℕ) (hk : 1 ≤ k)
    (ε₁ : ℝ) (hε₁ : 0 < ε₁) :
    ∃ O : Set M, IsOpen O ∧ D2 ⊆ O ∧ O ⊆ V ∧ ∃ ρ : ℝ, 0 < ρ ∧
      ∀ ε : ℝ, 0 < ε → ∃ ε' : ℝ, 0 < ε' ∧
        ∀ Φ : M → M, ContMDiffOn I I ∞ Φ O →
          (∀ p ∈ O, riemannianEDistOf g p (Φ p) < ENNReal.ofReal ρ) →
          CkCloseInAtlas_CX3 A D2 k ε' Φ →
          ∃ (X : ∀ p : M, TangentSpace I p) (G : ℝ → M → M),
            ContMDiff I I.tangent ∞ (secBundle_S15 X) ∧ CkSmall_S15 g A X k ε ∧
            CkSmall_S15 g A X 1 ε₁ ∧
            (∀ p, p ∉ D2 → X p = 0) ∧ (∀ p ∈ D1, expMapIntrinsic g hEnorm p (X p) = Φ p) ∧
            ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => G q.1 q.2) ∧
            (∀ μ x, G μ (scaledExp_S15 g hEnorm X (clamp_S102 μ) x) = x) ∧
            (∀ μ y, scaledExp_S15 g hEnorm X (clamp_S102 μ) (G μ y) = y) ∧
            (∀ t ∈ Icc (0 : ℝ) 1, CkCloseInAtlas_CX3 A D2 k ε (scaledExp_S15 g hEnorm X t)) := by
  obtain ⟨O, hO, hD2O, hOV, ρ, hρ, χ, _, _, _, _, hfield⟩ :=
    exists_CkSmall_transfer_field_sub_S120 g hEnorm A hD1 hD2 hD12 hV hD2V k
  obtain ⟨δ, B, hδ, hB, hbound⟩ := transfer_isotopy_Ck_bound_CX3 g hEnorm A k
  obtain ⟨ε₀, hε₀, hinv⟩ := exists_inverse_family_S102 g hEnorm A hD2 hD2A
  refine ⟨O, hO, hD2O, hOV, ρ, hρ, fun ε hε => ?_⟩
  let σ : ℝ := min ε₀ (min δ (min ε₁ (min ε (ε / (2 * B)))))
  have hσ : 0 < σ := lt_min hε₀ (lt_min hδ (lt_min hε₁ (lt_min hε (by positivity))))
  have hσ₀ : σ ≤ ε₀ := min_le_left _ _
  have hσδ : σ ≤ δ := (min_le_right _ _).trans (min_le_left _ _)
  have hσ₁ : σ ≤ ε₁ := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hσε : σ ≤ ε :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hσB : σ ≤ ε / (2 * B) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨ε', hε', hfield⟩ := hfield σ hσ
  refine ⟨ε', hε', fun Φ hΦ hdist hclose => ?_⟩
  obtain ⟨v, hXs, hXΦ, hX0, hsmall⟩ := hfield Φ hΦ hdist hclose
  let X : ∀ p : M, TangentSpace I p := fun p => χ p • secOf_S15 v p
  obtain ⟨G, hGs, hG1, hG2⟩ := hinv X hXs hX0 (CkSmall_mono_CX3 g hsmall hk hσ₀)
  refine ⟨X, G, hXs, CkSmall_mono_CX3 g hsmall le_rfl hσε, CkSmall_mono_CX3 g hsmall hk hσ₁, hX0,
    hXΦ, hGs, hG1, hG2, ?_⟩
  intro t ht i x hx _
  have hb := hbound X hXs σ hσ.le hσδ hsmall t (abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    i x hx
  refine ⟨hb.1, fun j hj => lt_of_le_of_lt (hb.2 j hj) ?_⟩
  have := (le_div_iff₀ (mul_pos (by norm_num) hB)).mp hσB
  nlinarith

end Generic1

section Generic2
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold 𝓘(ℝ, E) M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)] [LocallyCompactSpace M]

variable (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (hEnorm : IsMetricNorm g)

/-- **`hCX3ext` v4**, generic form (`riemannianEDistOf g` edist clauses): `hCX3ext_edistOf_S109`
with the extra conjunct `O ⊆ V` right after `D2 ⊆ O`.  The binder `_hD : IsCompact D` is unused
(frozen shape); `hV : IsOpen V` is used. -/
theorem hCX3ext_edistOf_v4_S120 [ConnectedSpace M] (A : CkAtlas_S15 𝓘(ℝ, E) M)
    {D D1 D2 V : Set M} (_hD : IsCompact D) (hD1 : IsCompact D1) (hD2 : IsCompact D2)
    (hDD1 : D ⊆ D1) (hD12 : D1 ⊆ interior D2) (hD2A : D2 ⊆ A.cover) (hV : IsOpen V)
    (hD2V : D2 ⊆ V) (k : ℕ) (hk : 1 ≤ k) :
    ∃ O : Set M, IsOpen O ∧ D2 ⊆ O ∧ O ⊆ V ∧ ∃ ρ : ℝ, 0 < ρ ∧
      ∀ ε : ℝ, 0 < ε → ∃ ε' : ℝ, 0 < ε' ∧
        ∀ Φ : M → M, ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ Φ O →
          (∀ p ∈ O, riemannianEDistOf g p (Φ p) < ENNReal.ofReal ρ) →
          CkCloseInAtlas_CX3 A D2 k ε' Φ →
          ∃ (X : ∀ p : M, TangentSpace 𝓘(ℝ, E) p) (Ψ : ℝ → ℝ → M → M) (C : Set M),
            ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent ∞ (secBundle_S15 X) ∧ CkSmall_S15 g A X k ε ∧
            (∀ p, p ∉ D2 → X p = 0) ∧ (∀ p ∈ D1, expMapIntrinsic g hEnorm p (X p) = Φ p) ∧
            IsCompact C ∧ ContMDiff ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
              (fun q : (ℝ × ℝ) × M => Ψ q.1.1 q.1.2 q.2) ∧
            (∀ s y, Ψ s s y = y) ∧ (∀ s t u y, Ψ t u (Ψ s t y) = Ψ s u y) ∧
            (∀ s t y, y ∉ C → Ψ s t y = y) ∧
            (∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ D, Ψ 0 t x = scaledExp_S15 g hEnorm X t x) ∧
            (∀ x ∈ D, Ψ 0 1 x = Φ x) ∧
            C ⊆ V ∧
            (∀ t ∈ Icc (0 : ℝ) 1, ∀ x : M, Ψ 0 t x = scaledExp_S15 g hEnorm X t x) ∧
            (∀ t ∈ Icc (0 : ℝ) 1, CkCloseInAtlas_CX3 A D2 k ε (scaledExp_S15 g hEnorm X t)) ∧
            (∀ μ ∈ Icc (0 : ℝ) 1, ∀ p : M,
              let v := mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun r => Ψ r 0 p) μ
                ((NormedSpace.fromTangentSpace (𝕜 := ℝ) μ).symm (1 : ℝ));
              g.inner (Ψ μ 0 p) v v ≤ ε ^ 2) ∧
            (∀ μ ∈ Icc (0 : ℝ) 1, ∀ p : M,
              riemannianEDistOf g p (Ψ μ 0 p) ≤ ENNReal.ofReal ε) := by
  obtain ⟨ε₀, hε₀, K, hK1, hQI⟩ := quasi_isometry_S109 g hEnorm A hD2 hD2A
  obtain ⟨O, hO, hD2O, hOV, ρ, hρ, hmain⟩ :=
    hCX3ext_core_v4_S120 g hEnorm A hD1 hD2 hD12 hD2A hV hD2V k hk ε₀ hε₀
  have hK0 : 0 < K := by linarith
  refine ⟨O, hO, hD2O, hOV, ρ, hρ, fun ε hε => ?_⟩
  have hεK : ε / K ≤ ε := div_le_self hε.le hK1
  obtain ⟨ε', hε', h⟩ := hmain (ε / K) (div_pos hε hK0)
  refine ⟨ε', hε', fun Φ hΦ hdist hclose => ?_⟩
  obtain ⟨X, G, hXs, hsmall, hsmall1, hX0, hXΦ, hGs, hG1, hG2, hclose2⟩ := h Φ hΦ hdist hclose
  have heq : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x : M,
      psi_S109 g hEnorm X G 0 t x = scaledExp_S15 g hEnorm X t x :=
    fun t ht x => psi_zero_left_S109 g hEnorm X G hG1 ht x
  have htan : ∀ q, tanLen_S15 g (secBundle_S15 X q) < ε / K :=
    fun q => tanLen_lt_of_CkSmall_S102 g A hD2A X hX0 (div_pos hε hK0) hsmall q
  have hfin : K * (ε / K) ^ 2 ≤ ε ^ 2 := by
    have : K * (ε / K) ^ 2 = ε ^ 2 / K := by field_simp
    rw [this]
    exact div_le_self (sq_nonneg ε) hK1
  refine ⟨X, psi_S109 g hEnorm X G, D2, hXs, CkSmall_mono_CX3 g hsmall le_rfl hεK, hX0, hXΦ, hD2,
    contMDiff_psi_S109 g hEnorm X hXs G hGs, psi_self_S109 g hEnorm X G hG2,
    psi_cocycle_S109 g hEnorm X G hG1, fun s t y hy => psi_fixed_S109 g hEnorm X G hX0 hG1 s t hy,
    fun t ht x _ => heq t ht x, ?_, hD2V, heq, ?_, ?_, ?_⟩
  · intro x hx
    rw [heq 1 ⟨zero_le_one, le_rfl⟩ x]
    simp only [scaledExp_S15, one_smul]
    exact hXΦ x (hDD1 hx)
  · intro t ht i x hx hxD
    obtain ⟨h1, h2⟩ := hclose2 t ht i x hx hxD
    exact ⟨h1, fun j hj => (h2 j hj).trans_le hεK⟩
  · intro μ hμ p
    have h := speed_bound_S109 g hEnorm X hXs G hGs hG2 hK0.le
      (fun μ hμ q w => hQI X hXs hX0 hsmall1 μ hμ q w) htan hμ p
    exact le_trans h hfin
  · intro μ hμ p
    exact (psi_displacement_S109 g hEnorm X G hG2 htan hμ p).trans (ENNReal.ofReal_le_ofReal hεK)

end Generic2

universe u

/-- **`hCX3ext_v4_S120` = `hCX3ext_S109` plus the conjunct `O ⊆ V`** (right after `D2 ⊆ O`; O54
FINDING F3, ruling (A)), at `⟨Hm.metric⟩` (`withS99%`, edist clauses `riemannianEDistOf Hm.metric`).
Unused binder (frozen shape): `hD : IsCompact D`. -/
theorem hCX3ext_v4_S120 (Hm : FiniteVolumeHyperbolicModel.{u})
    (A : CkAtlas_S15 (𝓡 3) Hm.Carrier) {D D1 D2 V : Set Hm.Carrier}
    (hD : IsCompact D) (hD1 : IsCompact D1) (hD2 : IsCompact D2)
    (hDD1 : D ⊆ D1) (hD12 : D1 ⊆ interior D2) (hD2A : D2 ⊆ A.cover) (hV : IsOpen V)
    (hD2V : D2 ⊆ V) (k : ℕ) (hk : 1 ≤ k) :
    withS99% Hm as hE,
    ∃ O : Set Hm.Carrier, IsOpen O ∧ D2 ⊆ O ∧ O ⊆ V ∧ ∃ ρ : ℝ, 0 < ρ ∧
      ∀ ε : ℝ, 0 < ε → ∃ ε' : ℝ, 0 < ε' ∧
        ∀ Φ : Hm.Carrier → Hm.Carrier, ContMDiffOn (𝓡 3) (𝓡 3) ∞ Φ O →
          (∀ p ∈ O, riemannianEDistOf Hm.metric p (Φ p) < ENNReal.ofReal ρ) →
          CkCloseInAtlas_CX3 A D2 k ε' Φ →
          ∃ (X : ∀ p : Hm.Carrier, TangentSpace (𝓡 3) p) (Ψ : ℝ → ℝ → Hm.Carrier → Hm.Carrier)
            (C : Set Hm.Carrier),
            ContMDiff (𝓡 3) (𝓡 3).tangent ∞ (secBundle_S15 X) ∧ CkSmall_S15 Hm.metric A X k ε ∧
            (∀ p, p ∉ D2 → X p = 0) ∧ (∀ p ∈ D1, expMapIntrinsic Hm.metric hE p (X p) = Φ p) ∧
            IsCompact C ∧ ContMDiff ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod (𝓡 3)) (𝓡 3) ∞
              (fun q : (ℝ × ℝ) × Hm.Carrier => Ψ q.1.1 q.1.2 q.2) ∧
            (∀ s y, Ψ s s y = y) ∧ (∀ s t u y, Ψ t u (Ψ s t y) = Ψ s u y) ∧
            (∀ s t y, y ∉ C → Ψ s t y = y) ∧
            (∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ D, Ψ 0 t x = scaledExp_S15 Hm.metric hE X t x) ∧
            (∀ x ∈ D, Ψ 0 1 x = Φ x) ∧
            C ⊆ V ∧
            (∀ t ∈ Icc (0 : ℝ) 1, ∀ x : Hm.Carrier, Ψ 0 t x = scaledExp_S15 Hm.metric hE X t x) ∧
            (∀ t ∈ Icc (0 : ℝ) 1, CkCloseInAtlas_CX3 A D2 k ε (scaledExp_S15 Hm.metric hE X t)) ∧
            (∀ μ ∈ Icc (0 : ℝ) 1, ∀ p : Hm.Carrier,
              let v := mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun r => Ψ r 0 p) μ
                ((NormedSpace.fromTangentSpace (𝕜 := ℝ) μ).symm (1 : ℝ));
              Hm.metric.inner (Ψ μ 0 p) v v ≤ ε ^ 2) ∧
            (∀ μ ∈ Icc (0 : ℝ) 1, ∀ p : Hm.Carrier,
              riemannianEDistOf Hm.metric p (Ψ μ 0 p) ≤ ENNReal.ofReal ε) :=
  withS99% Hm as hE,
    hCX3ext_edistOf_v4_S120 Hm.metric hE A hD hD1 hD2 hDD1 hD12 hD2A hV hD2V k hk

end GC.LongTime.Ch12
