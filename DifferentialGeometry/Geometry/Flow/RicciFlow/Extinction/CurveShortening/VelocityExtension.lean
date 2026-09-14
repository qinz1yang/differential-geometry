import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.LoopFamilyVelocityExtension
import DifferentialGeometry.Analysis.Calculus.Inverse.SmoothLocalInverse
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Topology.Maps.Proper.Basic

noncomputable section

open Bundle Manifold Set Filter Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

open Surgery.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

def graphLift (γ : ℝ → ContinuousFreeLoop E) : ℝ × ℝ → ℝ × E :=
  fun q => (q.1, γ q.1 (q.2 : Surgery.Topology.Circle))

def velocityLift (γ : ℝ → ContinuousFreeLoop E) (q : ℝ × ℝ) : E :=
  deriv (fun s : ℝ => γ s (q.2 : Surgery.Topology.Circle)) q.1

omit [FiniteDimensional ℝ E] in
theorem velocityLift_eq_of_graphLift_eq {γ : ℝ → ContinuousFreeLoop E}
    (hemb : ∀ t, Function.Injective (fun z : Surgery.Topology.Circle => γ t z)) {y y' : ℝ × ℝ}
    (h : graphLift γ y = graphLift γ y') : velocityLift γ y = velocityLift γ y' := by
  have h1 : y.1 = y'.1 := congrArg (fun z : ℝ × E => z.1) h
  have h2 : γ y.1 (y.2 : Surgery.Topology.Circle) =
      γ y'.1 (y'.2 : Surgery.Topology.Circle) := congrArg (fun z : ℝ × E => z.2) h
  have h3 : γ y.1 (y.2 : Surgery.Topology.Circle) =
      γ y.1 (y'.2 : Surgery.Topology.Circle) := by rw [← h1] at h2; exact h2
  have hz : (y.2 : Surgery.Topology.Circle) = (y'.2 : Surgery.Topology.Circle) := hemb y.1 h3
  have hfun : (fun s : ℝ => γ s (y.2 : Surgery.Topology.Circle)) =
      (fun s : ℝ => γ s (y'.2 : Surgery.Topology.Circle)) := by
    funext s
    rw [hz]
  simp only [velocityLift, h1, hfun]

omit [FiniteDimensional ℝ E] in
theorem contDiffOn_graphLift {γ : ℝ → ContinuousFreeLoop E} {O : Set (ℝ × ℝ)}
    (hγ : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => γ q.1 (q.2 : Surgery.Topology.Circle)) O) :
    ContDiffOn ℝ ∞ (graphLift γ) O := by
  have hfst : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => q.1) O := contDiff_fst.contDiffOn
  have h := hfst.prodMk hγ
  exact h

theorem exists_local_velocityExtension {γ : ℝ → ContinuousFreeLoop E} {O : Set (ℝ × ℝ)}
    (hO : IsOpen O) (hγ : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => γ q.1 (q.2 : Surgery.Topology.Circle)) O)
    {p : ℝ × ℝ} (hp : p ∈ O)
    (hinj : Function.Injective (fderiv ℝ (graphLift γ) p)) :
    ∃ V W σ, IsOpen V ∧ p ∈ V ∧ V ⊆ O ∧ IsOpen W ∧ graphLift γ p ∈ W ∧
      ContDiffOn ℝ ∞ σ W ∧ MapsTo (graphLift γ) V W ∧
      (∀ y ∈ V, σ (graphLift γ y) = y) ∧
      (∀ y ∈ V, velocityLift γ (σ (graphLift γ y)) = velocityLift γ y) := by
  obtain ⟨r, U, V, hU, hpU, hV, hpV, hVsub, hr, hleft, -⟩ :=
    DifferentialGeometry.Analysis.exists_smooth_local_leftInverse hO
      (contDiffOn_graphLift hγ) hp hinj
  refine ⟨V ∩ (O ∩ (graphLift γ) ⁻¹' U), U, r, ?_, ?_, ?_, hU, hpU, hr, ?_, ?_, ?_⟩
  · exact hV.inter ((contDiffOn_graphLift hγ).continuousOn.isOpen_inter_preimage hO hU)
  · exact ⟨hpV, hp, hpU⟩
  · intro y hy
    exact hVsub hy.1
  · rintro y ⟨-, -, hyU⟩
    exact hyU
  · rintro y ⟨hyV, -⟩
    exact hleft y hyV
  · rintro y ⟨hyV, -⟩
    rw [hleft y hyV]

theorem coe_add_intCast_period (x : ℝ) (k : ℤ) :
    ((x + (k : ℝ) : ℝ) : Surgery.Topology.Circle) = (x : Surgery.Topology.Circle) := by
  rw [show x + (k : ℝ) = x + k • (1 : ℝ) by simp [zsmul_eq_mul]]
  rw [AddCircle.coe_add, AddCircle.coe_zsmul, AddCircle.coe_period (1 : ℝ), smul_zero, add_zero]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
theorem graphLift_add_intCast {γ : ℝ → ContinuousFreeLoop E} (t x : ℝ) (k : ℤ) :
    graphLift γ (t, x + (k : ℝ)) = graphLift γ (t, x) := by
  simp only [graphLift, Prod.mk.injEq, true_and]
  rw [coe_add_intCast_period]

omit [FiniteDimensional ℝ E] in
theorem velocityLift_add_intCast {γ : ℝ → ContinuousFreeLoop E} (t x : ℝ) (k : ℤ) :
    velocityLift γ (t, x + (k : ℝ)) = velocityLift γ (t, x) := by
  have hfun : (fun s : ℝ => γ s ((x + (k : ℝ) : ℝ) : Surgery.Topology.Circle)) =
      (fun s : ℝ => γ s (x : Surgery.Topology.Circle)) := by
    funext s
    rw [coe_add_intCast_period]
  simp only [velocityLift, hfun]

theorem exists_lift_mem_Ico (z : Surgery.Topology.Circle) :
    ∃ x : ℝ, x ∈ Ico (0 : ℝ) 1 ∧ (x : Surgery.Topology.Circle) = z := by
  have hp : (0 : ℝ) < 1 := by norm_num
  refine ⟨((QuotientAddGroup.equivIcoMod hp 0 z : Set.Ico (0:ℝ) (0 + 1)) : ℝ), ?_, ?_⟩
  · simpa using (QuotientAddGroup.equivIcoMod hp 0 z).2
  · have h := (QuotientAddGroup.equivIcoMod hp 0).symm_apply_apply z
    rw [QuotientAddGroup.equivIcoMod_symm_apply] at h
    exact h

theorem exists_lift_mem_Icc (z : Surgery.Topology.Circle) :
    ∃ x : ℝ, x ∈ Icc (0 : ℝ) 1 ∧ (x : Surgery.Topology.Circle) = z := by
  obtain ⟨x, hx, hxz⟩ := exists_lift_mem_Ico z
  exact ⟨x, ⟨hx.1, hx.2.le⟩, hxz⟩

omit [FiniteDimensional ℝ E] in
theorem continuous_graphLift {γ : ℝ → ContinuousFreeLoop E}
    (hγ : ContDiff ℝ ∞ (fun q : ℝ × ℝ => γ q.1 (q.2 : Surgery.Topology.Circle))) :
    Continuous (graphLift γ) := by
  rw [← continuousOn_univ]
  exact (contDiffOn_graphLift hγ.contDiffOn).continuousOn

omit [FiniteDimensional ℝ E] in
theorem contDiff_velocityLift {γ : ℝ → ContinuousFreeLoop E}
    (hγ : ContDiff ℝ ∞ (fun q : ℝ × ℝ => γ q.1 (q.2 : Surgery.Topology.Circle))) :
    ContDiff ℝ ∞ (velocityLift γ) := by
  have hjoint : ContDiff ℝ ∞
      (fun p : (ℝ × ℝ) × ℝ => γ p.2 (p.1.2 : Surgery.Topology.Circle)) :=
    hγ.comp (contDiff_snd.prodMk contDiff_fst.snd)
  have h1 : ContDiff ℝ ∞
      (fun q : ℝ × ℝ => fderiv ℝ (fun s : ℝ => γ s (q.2 : Surgery.Topology.Circle)) q.1) :=
    ContDiff.fderiv
      (f := fun (q : ℝ × ℝ) (s : ℝ) => γ s (q.2 : Surgery.Topology.Circle))
      hjoint contDiff_fst (by simp : (∞ : ℕ∞ω) + 1 ≤ ∞)
  have h2 : ContDiff ℝ ∞
      (fun q : ℝ × ℝ =>
        (fderiv ℝ (fun s : ℝ => γ s (q.2 : Surgery.Topology.Circle)) q.1) (1 : ℝ)) :=
    h1.clm_apply contDiff_const
  convert h2 using 1
  funext q
  simp only [velocityLift, fderiv_apply_one_eq_deriv]

theorem exists_local_target_extension {γ : ℝ → ContinuousFreeLoop E} {A : Set (ℝ × ℝ)}
    (hA : IsCompact A)
    (hγ : ContDiff ℝ ∞ (fun q : ℝ × ℝ => γ q.1 (q.2 : Surgery.Topology.Circle)))
    (hi : ∀ q : ℝ × ℝ, Function.Injective (fderiv ℝ (graphLift γ) q))
    (hemb : ∀ t, Function.Injective (fun z : Surgery.Topology.Circle => γ t z))
    (p : ℝ × ℝ) :
    ∃ U g, IsOpen U ∧ graphLift γ p ∈ U ∧ ContDiffOn ℝ ∞ g U ∧
      ∀ y ∈ A, graphLift γ y ∈ U → g (graphLift γ y) = velocityLift γ y := by
  obtain ⟨V, W, σ, hV, hpV, -, hW, hpW, hσ, -, hleft, -⟩ :=
    exists_local_velocityExtension isOpen_univ hγ.contDiffOn (mem_univ p) (hi p)
  let V' : Set (ℝ × ℝ) := {y : ℝ × ℝ | ∃ k : ℤ, (y.1, y.2 - (k : ℝ)) ∈ V}
  have hV'open : IsOpen V' := by
    have : V' = ⋃ k : ℤ, {y : ℝ × ℝ | (y.1, y.2 - (k : ℝ)) ∈ V} := by
      ext y; simp [V']
    rw [this]
    refine isOpen_iUnion fun k => hV.preimage ?_
    exact continuous_fst.prodMk (continuous_snd.sub continuous_const)
  have hpV' : p ∈ V' := ⟨0, by simpa using hpV⟩
  have hV'val : ∀ y ∈ V', velocityLift γ (σ (graphLift γ y)) = velocityLift γ y := by
    rintro y ⟨k, hk⟩
    have hgraph : graphLift γ y = graphLift γ (y.1, y.2 - (k : ℝ)) := by
      conv_lhs => rw [show y = (y.1, (y.2 - (k : ℝ)) + (k : ℝ)) by simp]
      exact graphLift_add_intCast y.1 (y.2 - (k : ℝ)) k
    rw [hgraph, hleft _ hk]
    simpa using (velocityLift_add_intCast (γ := γ) y.1 (y.2 - (k : ℝ)) k).symm
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hW.mem_nhds hpW)
  have hBclosed : IsClosed (A ∩ (V'ᶜ ∩ (graphLift γ) ⁻¹' Metric.closedBall (graphLift γ p) r)) :=
    (hA.isClosed.inter (hV'open.isClosed_compl.inter
      (Metric.isClosed_closedBall.preimage (continuous_graphLift hγ))))
  have hBcomp : IsCompact (A ∩ (V'ᶜ ∩ (graphLift γ) ⁻¹' Metric.closedBall (graphLift γ p) r)) :=
    hA.of_isClosed_subset hBclosed fun y hy => hy.1
  have hgp : graphLift γ p ∉
      graphLift γ '' (A ∩ (V'ᶜ ∩ (graphLift γ) ⁻¹' Metric.closedBall (graphLift γ p) r)) := by
    rintro ⟨y, hy, hyeq⟩
    have h1 : y.1 = p.1 := congrArg (fun z : ℝ × E => z.1) hyeq
    have h2 : γ p.1 (y.2 : Surgery.Topology.Circle) =
        γ p.1 (p.2 : Surgery.Topology.Circle) := by
      have := congrArg (fun z : ℝ × E => z.2) hyeq
      simpa only [graphLift, h1] using this
    have h3 : (y.2 : Surgery.Topology.Circle) = (p.2 : Surgery.Topology.Circle) := hemb p.1 h2
    have h4 : y.2 - p.2 ∈ AddSubgroup.zmultiples (1 : ℝ) :=
      (QuotientAddGroup.eq_iff_sub_mem.mp h3)
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp h4
    have hk' : (k : ℝ) = y.2 - p.2 := by simpa using hk
    have : y.2 - (k : ℝ) = p.2 := by linarith
    exact hy.2.1 ⟨k, by
      rw [show (y.1, y.2 - (k : ℝ)) = p by ext <;> simp [h1, this]]
      exact hpV⟩
  refine ⟨Metric.ball (graphLift γ p) r ∩
      (graphLift γ '' (A ∩ (V'ᶜ ∩ (graphLift γ) ⁻¹' Metric.closedBall (graphLift γ p) r)))ᶜ,
    fun q => velocityLift γ (σ q),
    Metric.isOpen_ball.inter (hBcomp.image (continuous_graphLift hγ)).isClosed.isOpen_compl,
    ⟨Metric.mem_ball_self hr, hgp⟩, ?_, ?_⟩
  · refine ContDiffOn.comp (t := univ) (contDiff_velocityLift hγ).contDiffOn (hσ.mono ?_) ?_
    · exact fun q hq => hball hq.1
    exact fun q _ => mem_univ _
  · intro y hyA hyU
    have hyB : ¬ (y ∈ A ∩ (V'ᶜ ∩ (graphLift γ) ⁻¹' Metric.closedBall (graphLift γ p) r)) :=
      fun h => hyU.2 ⟨y, h, rfl⟩
    have hyV' : y ∈ V' := by
      by_contra h
      exact hyB ⟨hyA, h, Metric.ball_subset_closedBall hyU.1⟩
    exact hV'val y hyV'

omit [FiniteDimensional ℝ E] in
private theorem contDiff_smul_of_tsupport_subset {ρ : ℝ × E → ℝ} {g : ℝ × E → E}
    {O : Set (ℝ × E)}
    (hρ : ContDiff ℝ ∞ ρ) (hg : ContDiffOn ℝ ∞ g O) (hO : IsOpen O)
    (hsub : tsupport ρ ⊆ O) : ContDiff ℝ ∞ (fun y => ρ y • g y) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y ∈ tsupport ρ
  · exact (hρ.contDiffAt.smul ((hg y (hsub hy)).contDiffAt (hO.mem_nhds (hsub hy))))
  · refine (contDiffAt_const (c := (0 : E))).congr_of_eventuallyEq ?_
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hy] with z hz
    simp only [hz, Pi.zero_apply, zero_smul]

theorem exists_contDiff_eqOn_of_localCover {ι : Type*} {K : Set (ℝ × E)} (hK : IsCompact K)
    (s : Finset ι) (U : ι → Set (ℝ × E)) (hUo : ∀ i, IsOpen (U i))
    (hcover : K ⊆ ⋃ i ∈ s, U i) {g : ι → ℝ × E → E} (hg : ∀ i, ContDiffOn ℝ ∞ (g i) (U i))
    (hcons : ∀ i ∈ s, ∀ j ∈ s, ∀ q ∈ (K ∩ U i) ∩ U j, g i q = g j q) :
    ∃ G : ℝ × E → E, ContDiff ℝ ∞ G ∧ ∀ i ∈ s, ∀ q ∈ K ∩ U i, G q = g i q := by
  classical
  let U' : Option {i // i ∈ s} → Set (ℝ × E) := fun o =>
    match o with
    | none => Kᶜ
    | some i => U i.1
  have hU'o : ∀ o, IsOpen (U' o) := by
    rintro (_ | i)
    · exact hK.isClosed.isOpen_compl
    · exact hUo i.1
  have hcover' : (univ : Set (ℝ × E)) ⊆ ⋃ o, U' o := by
    intro q _
    by_cases hq : q ∈ K
    · obtain ⟨i, his, hqi⟩ := mem_iUnion₂.mp (hcover hq)
      exact mem_iUnion.mpr ⟨some ⟨i, his⟩, hqi⟩
    · exact mem_iUnion.mpr ⟨none, hq⟩
  obtain ⟨ρ, hρ⟩ :=
    SmoothPartitionOfUnity.exists_isSubordinate (𝓘(ℝ, ℝ × E)) isClosed_univ U' hU'o hcover'
  let G' : Option {i // i ∈ s} → ℝ × E → E := fun o =>
    match o with
    | none => fun _ => 0
    | some i => g i.1
  have hG' : ∀ o, ContDiffOn ℝ ∞ (G' o) (U' o) := by
    rintro (_ | i)
    · exact contDiffOn_const
    · exact hg i.1
  refine ⟨fun q => ∑ o, ρ o q • G' o q, ?_, ?_⟩
  · refine ContDiff.sum fun o _ =>
      contDiff_smul_of_tsupport_subset (contMDiff_iff_contDiff.mp (ρ o).2) (hG' o) (hU'o o) (hρ o)
  · intro i his q hqi
    have hsum : ∑ o, ρ o q = 1 := by
      have h := ρ.sum_eq_one (mem_univ q)
      rwa [finsum_eq_sum_of_fintype] at h
    have hcongr : ∑ o, ρ o q • G' o q = ∑ o, ρ o q • g i q := by
      refine Finset.sum_congr rfl fun o _ => ?_
      by_cases h0 : ρ o q = 0
      · rw [h0, zero_smul, zero_smul]
      · have hmem : q ∈ U' o := hρ o (subset_closure (Function.mem_support.mpr h0))
        cases o with
        | none => exact absurd hqi.1 hmem
        | some j =>
          have hj := hcons j.1 j.2 i his q ⟨⟨hqi.1, hmem⟩, hqi.2⟩
          simp only [G']
          rw [hj]
    change (∑ o, ρ o q • G' o q) = g i q
    rw [hcongr, ← Finset.sum_smul, hsum, one_smul]

theorem exists_contDiff_loopFamilyVelocity (a b : ℝ) (γ : ℝ → ContinuousFreeLoop E)
    (hemb : ∀ t, Function.Injective (fun z : Surgery.Topology.Circle => γ t z))
    (hγ : ContDiff ℝ ∞ (fun q : ℝ × ℝ => γ q.1 (q.2 : Surgery.Topology.Circle)))
    (hi : ∀ q : ℝ × ℝ, Function.Injective (fderiv ℝ (graphLift γ) q)) :
    ∃ X : ℝ → E → E, ContDiff ℝ ∞ (fun q : ℝ × E => X q.1 q.2) ∧
      ∀ t ∈ Icc a b, ∀ z : Surgery.Topology.Circle,
        X t (γ t z) = deriv (fun s : ℝ => γ s z) t := by
  classical
  set A : Set (ℝ × ℝ) := Icc a b ×ˢ Icc (0 : ℝ) 1 with hAdef
  have hA : IsCompact A := isCompact_Icc.prod isCompact_Icc
  have hloc : ∀ p : A, ∃ U g, IsOpen U ∧ graphLift γ p.1 ∈ U ∧ ContDiffOn ℝ ∞ g U ∧
      ∀ y ∈ A, graphLift γ y ∈ U → g (graphLift γ y) = velocityLift γ y :=
    fun p => exists_local_target_extension hA hγ hi hemb p.1
  choose U g hUo hUp hgs hgval using hloc
  have hK : IsCompact (graphLift γ '' A) := hA.image (continuous_graphLift hγ)
  have hcover : graphLift γ '' A ⊆ ⋃ p : A, U p := by
    rintro _ ⟨y, hyA, rfl⟩
    exact mem_iUnion.mpr ⟨⟨y, hyA⟩, hUp ⟨y, hyA⟩⟩
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover U hUo hcover
  have hcons : ∀ i ∈ s, ∀ j ∈ s, ∀ q ∈ ((graphLift γ '' A) ∩ U i) ∩ U j,
      g i q = g j q := by
    rintro i _ j _ q ⟨⟨⟨y, hyA, hyq⟩, hqi⟩, hqj⟩
    have h1 : g i (graphLift γ y) = velocityLift γ y := hgval i y hyA (by rw [hyq]; exact hqi)
    have h2 : g j (graphLift γ y) = velocityLift γ y := hgval j y hyA (by rw [hyq]; exact hqj)
    rw [← hyq, h1, h2]
  obtain ⟨G, hG, hGeq⟩ := exists_contDiff_eqOn_of_localCover hK s U hUo hs hgs hcons
  refine ⟨fun t p => G (t, p), hG, ?_⟩
  suffices hGvel : ∀ y ∈ A, G (graphLift γ y) = velocityLift γ y by
    intro t ht z
    obtain ⟨x, hxIcc, hxz⟩ := exists_lift_mem_Icc z
    have hyA : (t, x) ∈ A := ⟨ht, hxIcc⟩
    have hGx := hGvel (t, x) hyA
    have hfun : (fun s : ℝ => γ s (x : Surgery.Topology.Circle)) = (fun s : ℝ => γ s z) := by
      funext s
      rw [hxz]
    have hpair : (t, γ t z) = graphLift γ (t, x) := by
      simp only [graphLift]
      rw [← hxz]
    change G (t, γ t z) = deriv (fun s : ℝ => γ s z) t
    rw [hpair, hGx]
    exact congrArg (fun f : ℝ → E => deriv f t) hfun
  intro y hyA
  obtain ⟨p, hps, hyp⟩ := mem_iUnion₂.mp (hs ⟨y, hyA, rfl⟩)
  exact (hGeq p hps (graphLift γ y) ⟨⟨y, hyA, rfl⟩, hyp⟩).trans (hgval p y hyA hyp)

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
