import DifferentialGeometry.Geometry.Exponential.DiagonalExponential.LocalInverse
import DifferentialGeometry.Geometry.Exponential.DiagonalExponential.FiberComparison
import DifferentialGeometry.Geometry.Metric.UnitTangentPair

/-!
# CH12-S15, H1 group C: the transfer vector field `v_Φ = exp⁻¹ Φ`
-/

set_option autoImplicit false
open scoped Manifold ContDiff Topology
open Set Function Bundle Filter
noncomputable section
namespace GC.LongTime.Ch12

open DifferentialGeometry DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Geometry.Riemannian.Exponential

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- the `g`-length of a tangent vector, as a function on `TM`. -/
def tanLen_S15 (g : SmoothRiemannianMetric I M) (u : TangentBundle I M) : ℝ :=
  Real.sqrt (g.inner u.proj u.snd u.snd)

theorem continuous_tanLen_S15 (g : SmoothRiemannianMetric I M) :
    Continuous (tanLen_S15 g) := by
  have h := Continuous.clm_bundle_apply₂ (𝕜 := ℝ) (E₃ := fun _ : M => ℝ) (F₁ := E) (F₂ := E)
    (F₃ := ℝ) (g.contMDiff.continuous.comp (FiberBundle.continuous_proj E (TangentSpace I)))
    (continuous_id : Continuous (fun u : TangentBundle I M => u))
    (continuous_id : Continuous (fun u : TangentBundle I M => u))
  have h2 := (continuous_snd.comp (Bundle.Trivial.homeomorphProd M ℝ).continuous).comp h
  exact Real.continuous_sqrt.comp h2


theorem tanLen_smul_S15 (g : SmoothRiemannianMetric I M) (y : M) (c : ℝ) (v : TangentSpace I y) :
    tanLen_S15 g (⟨y, c • v⟩ : TangentBundle I M) = |c| * tanLen_S15 g (⟨y, v⟩ : TangentBundle I M) := by
  unfold tanLen_S15
  simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [show c * (c * g.inner y v v) = c ^ 2 * g.inner y v v by ring, Real.sqrt_mul (sq_nonneg c),
    Real.sqrt_sq_eq_abs]

theorem tanLen_pos_S15 (g : SmoothRiemannianMetric I M) (y : M) (v : TangentSpace I y)
    (hv : v ≠ 0) : 0 < tanLen_S15 g (⟨y, v⟩ : TangentBundle I M) :=
  Real.sqrt_pos.mpr (g.pos y v hv)

/-- **Tube lemma.** An open subset of `TM` containing `0_{p₀}` contains all short vectors over a
neighbourhood of `p₀`. -/
theorem exists_short_vectors_subset_S15 [LocallyCompactSpace M] (g : SmoothRiemannianMetric I M)
    {S : Set (TangentBundle I M)} (hS : IsOpen S) {p₀ : M}
    (h0 : (⟨p₀, (0 : TangentSpace I p₀)⟩ : TangentBundle I M) ∈ S) :
    ∃ W ∈ 𝓝 p₀, ∃ r : ℝ, 0 < r ∧ ∀ u : TangentBundle I M, u.proj ∈ W → tanLen_S15 g u < r → u ∈ S := by
  set e := trivializationAt E (TangentSpace I) p₀ with he
  have hb0 : p₀ ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' p₀
  set f : M × E → TangentBundle I M := fun z => ⟨z.1, e.symm z.1 z.2⟩ with hf
  have hfc : ContinuousOn f (e.baseSet ×ˢ univ) := e.continuousOn_symm
  have hfy : ∀ y ∈ e.baseSet, ∀ w : E, f (y, w) = ⟨y, e.symmL ℝ y w⟩ := by
    intro y hy w
    rw [Bundle.Trivialization.symmL_apply e hy]
  have hf0 : f (p₀, 0) = ⟨p₀, (0 : TangentSpace I p₀)⟩ := by
    rw [hfy p₀ hb0]; simp
  have hopen : IsOpen ((e.baseSet ×ˢ univ) ∩ f ⁻¹' S) :=
    hfc.isOpen_inter_preimage (e.open_baseSet.prod isOpen_univ) hS
  have hmem : (p₀, (0 : E)) ∈ (e.baseSet ×ˢ univ) ∩ f ⁻¹' S :=
    ⟨⟨hb0, trivial⟩, by rw [mem_preimage, hf0]; exact h0⟩
  obtain ⟨W1, hW1, V1, hV1, hsub⟩ := mem_nhds_prod_iff.mp (hopen.mem_nhds hmem)
  obtain ⟨s, hs, hball⟩ := Metric.mem_nhds_iff.mp hV1
  obtain ⟨K, hKn, hKW, hKc⟩ := local_compact_nhds hW1
  have hKb : ∀ y ∈ K, y ∈ e.baseSet := fun y hy =>
    (hsub (show (y, (0 : E)) ∈ W1 ×ˢ V1 from ⟨hKW hy, hball (Metric.mem_ball_self hs)⟩)).1.1
  have hcomp : IsCompact (K ×ˢ Metric.sphere (0 : E) (s / 2)) :=
    hKc.prod (isCompact_sphere _ _)
  have hcont : ContinuousOn (fun z : M × E => tanLen_S15 g (f z)) (K ×ˢ Metric.sphere (0 : E) (s / 2)) :=
    (continuous_tanLen_S15 g).comp_continuousOn
      (hfc.mono (fun z hz => ⟨hKb _ hz.1, trivial⟩))
  have hpos : ∀ z ∈ K ×ˢ Metric.sphere (0 : E) (s / 2), 0 < tanLen_S15 g (f z) := by
    rintro ⟨y, w⟩ ⟨hy, hw⟩
    have hw0 : w ≠ 0 := by
      rintro rfl
      simp at hw
      linarith
    rw [hfy y (hKb y hy)]
    apply tanLen_pos_S15
    intro h0'
    apply hw0
    have := congrArg (e.continuousLinearMapAt ℝ y) h0'
    rwa [Bundle.Trivialization.continuousLinearMapAt_symmL e (hKb y hy), map_zero] at this
  obtain ⟨m, hm, hmle⟩ : ∃ m : ℝ, 0 < m ∧
      ∀ z ∈ K ×ˢ Metric.sphere (0 : E) (s / 2), m ≤ tanLen_S15 g (f z) := by
    by_cases hne : (K ×ˢ Metric.sphere (0 : E) (s / 2)).Nonempty
    · obtain ⟨z0, hz0, hmin⟩ := hcomp.exists_isMinOn hne hcont
      exact ⟨_, hpos z0 hz0, fun z hz => hmin hz⟩
    · exact ⟨1, one_pos, fun z hz => (hne ⟨z, hz⟩).elim⟩
  refine ⟨K, hKn, m, hm, fun u hu hlen => ?_⟩
  obtain ⟨y, v⟩ := u
  have hy : y ∈ e.baseSet := hKb y hu
  set w : E := e.continuousLinearMapAt ℝ y v with hw
  have hv : e.symmL ℝ y w = v := Bundle.Trivialization.symmL_continuousLinearMapAt e hy v
  by_contra hnot
  by_cases hbig : s / 2 ≤ ‖w‖
  · have hwpos : 0 < ‖w‖ := lt_of_lt_of_le (by linarith) hbig
    set c : ℝ := (s / 2) / ‖w‖ with hc
    have hcpos : 0 < c := by positivity
    have hcle : c ≤ 1 := by rw [hc, div_le_one hwpos]; exact hbig
    have hsph : c • w ∈ Metric.sphere (0 : E) (s / 2) := by
      rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs, abs_of_pos hcpos, hc]
      field_simp
    have h1 := hmle (y, c • w) ⟨hu, hsph⟩
    rw [hfy y hy, map_smul] at h1
    have h2 : (e.symmL ℝ y) w = v := hv
    rw [h2] at h1
    have h3 := tanLen_smul_S15 g y c v
    rw [abs_of_pos hcpos] at h3
    have h4 : tanLen_S15 g (⟨y, v⟩ : TangentBundle I M) ≥ 0 := Real.sqrt_nonneg _
    have : tanLen_S15 g (⟨y, c • v⟩ : TangentBundle I M) ≤ tanLen_S15 g ⟨y, v⟩ := by
      rw [h3]; nlinarith
    have hlen' : tanLen_S15 g (⟨y, v⟩ : TangentBundle I M) < m := hlen
    linarith
  · push_neg at hbig
    apply hnot
    have hwV : w ∈ V1 := hball (by rw [Metric.mem_ball, dist_zero_right]; linarith)
    have := (hsub (show (y, w) ∈ W1 ×ˢ V1 from ⟨hKW hu, hwV⟩)).2
    rw [mem_preimage, hfy y hy, hv] at this
    exact this


theorem exists_pos_le_finset_S15 {α : Type*} (t : Finset α) (r : α → ℝ) (hr : ∀ x, 0 < r x) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ x ∈ t, ρ ≤ r x := by
  classical
  induction t using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | insert a t ha ih =>
    obtain ⟨ρ, hρ, h⟩ := ih
    refine ⟨min ρ (r a), lt_min hρ (hr a), ?_⟩
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (h x hx)

section Complete
variable [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)] [LocallyCompactSpace M]

/-- **H1-C.**  Over a neighbourhood `O` of a compact `K`, every smooth map `Φ` that moves points
by less than `ρ` is `exp ∘ v` for a smooth section `v` of `TM`, namely the minimizing inverse;
`ρ` and `O` depend only on `(g, K)`. -/
theorem exists_transfer_section_S15 (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    {K : Set M} (hK : IsCompact K) :
    ∃ O : Set M, IsOpen O ∧ K ⊆ O ∧ ∃ ρ : ℝ, 0 < ρ ∧
      ∀ Φ : M → M, ContMDiffOn I I ∞ Φ O →
        (∀ p ∈ O, Manifold.riemannianEDist I p (Φ p) < ENNReal.ofReal ρ) →
        ∃ v : M → TangentBundle I M, ContMDiffOn I I.tangent ∞ v O ∧
          ∀ p ∈ O, (v p).proj = p ∧ expMapIntrinsic g hEnorm p (v p).snd = Φ p ∧
            tanLen_S15 g (v p) = (Manifold.riemannianEDist I p (Φ p)).toReal := by
  classical
  let B : ∀ p : M, DiagonalInverseBranch g hEnorm p := fun p => standardDiagonalInverseBranch g hEnorm p
  have htube : ∀ p : M, ∃ W ∈ 𝓝 p, ∃ r : ℝ, 0 < r ∧
      ∀ u : TangentBundle I M, u.proj ∈ W → tanLen_S15 g u < r → u ∈ (B p).hom.source :=
    fun p => exists_short_vectors_subset_S15 g (B p).hom.open_source (B p).zero_mem
  choose W hW r hr hrW using htube
  obtain ⟨t, -, hcov⟩ := hK.elim_nhds_subcover (fun p => interior (W p))
    (fun p _ => interior_mem_nhds.mpr (hW p))
  obtain ⟨ρ, hρ, hρle⟩ := exists_pos_le_finset_S15 t r hr
  refine ⟨⋃ x ∈ t, interior (W x), ?_, hcov, ρ, hρ, ?_⟩
  · exact isOpen_biUnion fun x _ => isOpen_interior
  intro Φ hΦ hd
  set O : Set M := ⋃ x ∈ t, interior (W x) with hO
  have hfib : ∀ x ∈ t, ∀ p ∈ interior (W x), ∀ w : TangentSpace I p,
      Real.sqrt (g.inner p w w) < ρ → (⟨p, w⟩ : TangentBundle I M) ∈ (B x).hom.source :=
    fun x hx p hp w hw => hrW x ⟨p, w⟩ (interior_subset hp) (lt_of_lt_of_le hw (hρle x hx))
  have hmin : ∀ x ∈ t, ∀ p ∈ interior (W x), ∃ w : TangentSpace I p,
      (p, Φ p) ∈ (B x).dom ∧ (B x).inv (p, Φ p) = (⟨p, w⟩ : TangentBundle I M) ∧
      expMapIntrinsic g hEnorm p w = Φ p ∧
      Real.sqrt (g.inner p w w) = (Manifold.riemannianEDist I p (Φ p)).toReal := by
    intro x hx p hp
    have hpO : p ∈ O := mem_iUnion₂.mpr ⟨x, hx, hp⟩
    exact (B x).inv_is_min_of_fiber_ball_subset (hd p hpO) (hfib x hx p hp)
  have hex : ∀ p ∈ O, ∃ x ∈ t, p ∈ interior (W x) := fun p hp => by
    obtain ⟨x, hx, h⟩ := mem_iUnion₂.mp hp
    exact ⟨x, hx, h⟩
  let c : M → M := fun p => if h : p ∈ O then Classical.choose (hex p h) else p
  have hc : ∀ p ∈ O, c p ∈ t ∧ p ∈ interior (W (c p)) := by
    intro p hp
    simp only [c, dif_pos hp]
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
      obtain ⟨_, hdom, -⟩ := hmin x hx q hq.2
      exact hdom
    have hsm := (B x).inv_contMDiffOn.comp hpair hmaps
    refine hsm.congr ?_
    intro q hq
    exact hagree x hx q hq.2 hq.1
  · intro p hp
    obtain ⟨hct, hcp⟩ := hc p hp
    obtain ⟨w, -, hw1, hw2, hw3⟩ := hmin (c p) hct p hcp
    have hvp : v p = (⟨p, w⟩ : TangentBundle I M) := hw1
    rw [hvp]
    exact ⟨rfl, hw2, hw3⟩

end Complete
end GC.LongTime.Ch12
