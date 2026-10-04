import DifferentialGeometry.External.CanonicalTopology.Topology.LoopSpace.Basic
import DifferentialGeometry.Analysis.Calculus.Inverse.SmoothLocalInverse
import DifferentialGeometry.Analysis.Calculus.SmoothExtension.Closed
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Topology.Maps.Proper.Basic

section


noncomputable section

open Bundle Manifold Set Filter Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

def graphLift (γ : ℝ → DifferentialGeometry.Topology.freeLoop E) : ℝ × ℝ → ℝ × E :=
  fun q => (q.1, γ q.1 (q.2 : DifferentialGeometry.Topology.loopCircle))

def velocityLift (γ : ℝ → DifferentialGeometry.Topology.freeLoop E) (q : ℝ × ℝ) : E :=
  deriv (fun s : ℝ => γ s (q.2 : DifferentialGeometry.Topology.loopCircle)) q.1

omit [FiniteDimensional ℝ E] in
theorem velocityLift_eq_of_graphLift_eq {γ : ℝ → DifferentialGeometry.Topology.freeLoop E}
    (hemb : ∀ t, Function.Injective (fun z : DifferentialGeometry.Topology.loopCircle => γ t z)) {y y' : ℝ × ℝ}
    (h : graphLift γ y = graphLift γ y') : velocityLift γ y = velocityLift γ y' := by
  have h1 : y.1 = y'.1 := congrArg (fun z : ℝ × E => z.1) h
  have h2 : γ y.1 (y.2 : DifferentialGeometry.Topology.loopCircle) =
      γ y'.1 (y'.2 : DifferentialGeometry.Topology.loopCircle) := congrArg (fun z : ℝ × E => z.2) h
  have h3 : γ y.1 (y.2 : DifferentialGeometry.Topology.loopCircle) =
      γ y.1 (y'.2 : DifferentialGeometry.Topology.loopCircle) := by rw [← h1] at h2; exact h2
  have hz : (y.2 : DifferentialGeometry.Topology.loopCircle) = (y'.2 : DifferentialGeometry.Topology.loopCircle) := hemb y.1 h3
  have hfun : (fun s : ℝ => γ s (y.2 : DifferentialGeometry.Topology.loopCircle)) =
      (fun s : ℝ => γ s (y'.2 : DifferentialGeometry.Topology.loopCircle)) := by
    funext s
    rw [hz]
  simp only [velocityLift, h1, hfun]

omit [FiniteDimensional ℝ E] in
theorem contDiffOn_graphLift {γ : ℝ → DifferentialGeometry.Topology.freeLoop E} {O : Set (ℝ × ℝ)}
    (hγ : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => γ q.1 (q.2 : DifferentialGeometry.Topology.loopCircle)) O) :
    ContDiffOn ℝ ∞ (graphLift γ) O := by
  have hfst : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => q.1) O := contDiff_fst.contDiffOn
  have h := hfst.prodMk hγ
  exact h

theorem exists_local_velocityExtension {γ : ℝ → DifferentialGeometry.Topology.freeLoop E} {O : Set (ℝ × ℝ)}
    (hO : IsOpen O) (hγ : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => γ q.1 (q.2 : DifferentialGeometry.Topology.loopCircle)) O)
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
    ((x + (k : ℝ) : ℝ) : DifferentialGeometry.Topology.loopCircle) = (x : DifferentialGeometry.Topology.loopCircle) := by
  rw [show x + (k : ℝ) = x + k • (1 : ℝ) by simp [zsmul_eq_mul]]
  rw [AddCircle.coe_add, AddCircle.coe_zsmul, AddCircle.coe_period (1 : ℝ), smul_zero, add_zero]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
theorem graphLift_add_intCast {γ : ℝ → DifferentialGeometry.Topology.freeLoop E} (t x : ℝ) (k : ℤ) :
    graphLift γ (t, x + (k : ℝ)) = graphLift γ (t, x) := by
  simp only [graphLift, Prod.mk.injEq, true_and]
  rw [coe_add_intCast_period]

omit [FiniteDimensional ℝ E] in
theorem velocityLift_add_intCast {γ : ℝ → DifferentialGeometry.Topology.freeLoop E} (t x : ℝ) (k : ℤ) :
    velocityLift γ (t, x + (k : ℝ)) = velocityLift γ (t, x) := by
  have hfun : (fun s : ℝ => γ s ((x + (k : ℝ) : ℝ) : DifferentialGeometry.Topology.loopCircle)) =
      (fun s : ℝ => γ s (x : DifferentialGeometry.Topology.loopCircle)) := by
    funext s
    rw [coe_add_intCast_period]
  simp only [velocityLift, hfun]

theorem exists_lift_mem_Ico (z : DifferentialGeometry.Topology.loopCircle) :
    ∃ x : ℝ, x ∈ Ico (0 : ℝ) 1 ∧ (x : DifferentialGeometry.Topology.loopCircle) = z := by
  have hp : (0 : ℝ) < 1 := by norm_num
  refine ⟨((QuotientAddGroup.equivIcoMod hp 0 z : Set.Ico (0:ℝ) (0 + 1)) : ℝ), ?_, ?_⟩
  · simpa using (QuotientAddGroup.equivIcoMod hp 0 z).2
  · have h := (QuotientAddGroup.equivIcoMod hp 0).symm_apply_apply z
    rw [QuotientAddGroup.equivIcoMod_symm_apply] at h
    exact h

theorem exists_lift_mem_Icc (z : DifferentialGeometry.Topology.loopCircle) :
    ∃ x : ℝ, x ∈ Icc (0 : ℝ) 1 ∧ (x : DifferentialGeometry.Topology.loopCircle) = z := by
  obtain ⟨x, hx, hxz⟩ := exists_lift_mem_Ico z
  exact ⟨x, ⟨hx.1, hx.2.le⟩, hxz⟩

omit [FiniteDimensional ℝ E] in
theorem continuous_graphLift {γ : ℝ → DifferentialGeometry.Topology.freeLoop E}
    (hγ : ContDiff ℝ ∞ (fun q : ℝ × ℝ => γ q.1 (q.2 : DifferentialGeometry.Topology.loopCircle))) :
    Continuous (graphLift γ) := by
  rw [← continuousOn_univ]
  exact (contDiffOn_graphLift hγ.contDiffOn).continuousOn

omit [FiniteDimensional ℝ E] in
theorem contDiff_velocityLift {γ : ℝ → DifferentialGeometry.Topology.freeLoop E}
    (hγ : ContDiff ℝ ∞ (fun q : ℝ × ℝ => γ q.1 (q.2 : DifferentialGeometry.Topology.loopCircle))) :
    ContDiff ℝ ∞ (velocityLift γ) := by
  have hjoint : ContDiff ℝ ∞
      (fun p : (ℝ × ℝ) × ℝ => γ p.2 (p.1.2 : DifferentialGeometry.Topology.loopCircle)) :=
    hγ.comp (contDiff_snd.prodMk contDiff_fst.snd)
  have h1 : ContDiff ℝ ∞
      (fun q : ℝ × ℝ => fderiv ℝ (fun s : ℝ => γ s (q.2 : DifferentialGeometry.Topology.loopCircle)) q.1) :=
    ContDiff.fderiv
      (f := fun (q : ℝ × ℝ) (s : ℝ) => γ s (q.2 : DifferentialGeometry.Topology.loopCircle))
      hjoint contDiff_fst (by simp : (∞ : ℕ∞ω) + 1 ≤ ∞)
  have h2 : ContDiff ℝ ∞
      (fun q : ℝ × ℝ =>
        (fderiv ℝ (fun s : ℝ => γ s (q.2 : DifferentialGeometry.Topology.loopCircle)) q.1) (1 : ℝ)) :=
    h1.clm_apply contDiff_const
  convert h2 using 1
  funext q
  simp only [velocityLift, fderiv_apply_one_eq_deriv]

theorem exists_local_target_extension {γ : ℝ → DifferentialGeometry.Topology.freeLoop E} {A : Set (ℝ × ℝ)}
    (hA : IsCompact A)
    (hγ : ContDiff ℝ ∞ (fun q : ℝ × ℝ => γ q.1 (q.2 : DifferentialGeometry.Topology.loopCircle)))
    (hi : ∀ q : ℝ × ℝ, Function.Injective (fderiv ℝ (graphLift γ) q))
    (hemb : ∀ t, Function.Injective (fun z : DifferentialGeometry.Topology.loopCircle => γ t z))
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
    have h2 : γ p.1 (y.2 : DifferentialGeometry.Topology.loopCircle) =
        γ p.1 (p.2 : DifferentialGeometry.Topology.loopCircle) := by
      have := congrArg (fun z : ℝ × E => z.2) hyeq
      simpa only [graphLift, h1] using this
    have h3 : (y.2 : DifferentialGeometry.Topology.loopCircle) = (p.2 : DifferentialGeometry.Topology.loopCircle) := hemb p.1 h2
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

theorem exists_contDiff_loopFamilyVelocity (a b : ℝ) (γ : ℝ → DifferentialGeometry.Topology.freeLoop E)
    (hemb : ∀ t, Function.Injective (fun z : DifferentialGeometry.Topology.loopCircle => γ t z))
    (hγ : ContDiff ℝ ∞ (fun q : ℝ × ℝ => γ q.1 (q.2 : DifferentialGeometry.Topology.loopCircle)))
    (hi : ∀ q : ℝ × ℝ, Function.Injective (fderiv ℝ (graphLift γ) q)) :
    ∃ X : ℝ → E → E, ContDiff ℝ ∞ (fun q : ℝ × E => X q.1 q.2) ∧
      ∀ t ∈ Icc a b, ∀ z : DifferentialGeometry.Topology.loopCircle,
        X t (γ t z) = deriv (fun s : ℝ => γ s z) t := by
  let A : Set (ℝ × ℝ) := Icc a b ×ˢ Icc (0 : ℝ) 1
  have hA : IsCompact A := isCompact_Icc.prod isCompact_Icc
  have hK : IsClosed (graphLift γ '' A) :=
    (hA.image (continuous_graphLift hγ)).isClosed
  have hlocal : ∀ p ∈ A, ∃ U ∈ 𝓝 (graphLift γ p), ∃ g : ℝ × E → E,
      ContDiffOn ℝ ∞ g U ∧ ∀ y ∈ A, graphLift γ y ∈ U → g (graphLift γ y) = velocityLift γ y := by
    intro p _
    obtain ⟨U, g, hU, hpU, hg, hgeq⟩ := exists_local_target_extension hA hγ hi hemb p
    exact ⟨U, hU.mem_nhds hpU, g, hg, hgeq⟩
  obtain ⟨G, hG, hGeq⟩ := DifferentialGeometry.Analysis.exists_contDiff_extension_of_local
    (f := graphLift γ) (g := velocityLift γ) (K := A) hK hlocal
  refine ⟨fun t p => G (t, p), hG, ?_⟩
  intro t ht z
  obtain ⟨x, hx, hxz⟩ := exists_lift_mem_Icc z
  have hGx := hGeq (show (t, x) ∈ A from ⟨ht, hx⟩)
  change G (t, γ t (x : DifferentialGeometry.Topology.loopCircle)) =
    deriv (fun r : ℝ => γ r (x : DifferentialGeometry.Topology.loopCircle)) t at hGx
  simpa only [hxz] using hGx

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

end

end

