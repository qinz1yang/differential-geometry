import DifferentialGeometry.Geometry.Connection.ParallelTransport.HessianSupport
import DifferentialGeometry.Geometry.Metric.BundleLipschitz
import DifferentialGeometry.Geometry.Metric.BundleContinuity
import DifferentialGeometry.Bundle.Fiberwise
import DifferentialGeometry.Analysis.ODE.InvariantSetLocal
import DifferentialGeometry.Analysis.Calculus.Extrema

noncomputable section

open Bundle Set Filter CovariantDerivative
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.Analysis.Parabolic

open DifferentialGeometry.Analysis.Convex
open DifferentialGeometry.Analysis.ODE
open DifferentialGeometry.Geometry.Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [CompactSpace M] [BoundarylessManifold I M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  [IsContMDiffRiemannianBundle I 1 F V] [ContMDiffVectorBundle ∞ F V I]

theorem hamilton_weak_maximum_principle_of_supporting_normal
    (g : ℝ → SmoothRiemannianMetric I M) (cov : ℝ → CovariantDerivative I F V)
    (X : ℝ → ∀ x : M, TangentSpace I x) (reaction : ℝ → ∀ x : M, V x → V x)
    {a b : ℝ} {K : Set (TotalSpace F V)} {u : ℝ → ∀ x : M, V x}
    (hcov : ∀ t ∈ Ico a b, ContMDiffCovariantDerivative (cov t) ∞)
    (hmetric : ∀ t ∈ Ico a b, (cov t).IsMetricCompatible)
    (hK : ∀ t ∈ Ico a b, (cov t).IsParallelSet K)
    (hclosed : ∀ x, IsClosed {v : V x | (⟨x, v⟩ : TotalSpace F V) ∈ K})
    (hconvex : ∀ x, Convex ℝ {v : V x | (⟨x, v⟩ : TotalSpace F V) ∈ K})
    (hreaction : ContMDiffOn (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, F))) (I.prod 𝓘(ℝ, F)) 1
      (fun q : ℝ × TotalSpace F V =>
        (⟨q.2.proj, reaction q.1 q.2.proj q.2.2⟩ : TotalSpace F V)) (Ico a b ×ˢ univ))
    (hinward : ∀ t ∈ Ioo a b, ∀ x, ∀ p ν : V x,
      ν ∈ normalCone {v : V x | (⟨x, v⟩ : TotalSpace F V) ∈ K} p →
        inner ℝ ν (reaction t x p) ≤ 0)
    (hu : ContinuousOn (fun q : ℝ × M =>
      (⟨q.2, u q.1 q.2⟩ : TotalSpace F V)) (Ico a b ×ˢ univ))
    (hspace : ∀ t ∈ Ioo a b, ∀ x, ContMDiffAt I (I.prod 𝓘(ℝ, F)) 2 (T% (u t)) x)
    (hequation : ∀ t ∈ Ioo a b, ∀ x, HasDerivAt (fun s => u s x)
      (rawBundleConnLap (g t) (cov t) (u t) x + (cov t) (u t) x (X t x) +
        reaction t x (u t x)) t)
    (hinitial : ∀ x, (⟨x, u a x⟩ : TotalSpace F V) ∈ K) :
    ∀ t ∈ Ico a b, ∀ x, (⟨x, u t x⟩ : TotalSpace F V) ∈ K := by
  have hne (x : M) : {v : V x | (⟨x, v⟩ : TotalSpace F V) ∈ K}.Nonempty :=
    ⟨u a x, hinitial x⟩
  intro τ hτ x₁
  by_cases hτa : τ = a
  · simpa only [hτa] using hinitial x₁
  have haτ : a < τ := lt_of_le_of_ne hτ.1 (Ne.symm hτa)
  have ha : a ∈ Ico a b := ⟨le_rfl, haτ.trans hτ.2⟩
  let _ : ∀ x, FiniteDimensional ℝ (V x) := fun x => by
    let L := VectorBundle.continuousLinearEquivAt ℝ F V x
    exact FiniteDimensional.of_injective L.toLinearMap L.injective
  let _ : ∀ x, CompleteSpace (V x) := fun x => FiniteDimensional.complete ℝ (V x)
  let _ : IsContinuousRiemannianBundle F V :=
    IsContMDiffRiemannianBundle.isContinuousRiemannianBundle (I := I) (n := 1)
  let Q := Icc a τ ×ˢ (univ : Set M)
  have hQ : IsCompact Q := isCompact_Icc.prod CompactSpace.isCompact_univ
  have hQsub : Q ⊆ Ico a b ×ˢ (univ : Set M) :=
    fun q hq => ⟨⟨hq.1.1, hq.1.2.trans_lt hτ.2⟩, hq.2⟩
  have hucont := hu.mono hQsub
  have hunorm : ContinuousOn (fun q : ℝ × M => ‖u q.1 q.2‖) Q := by
    have hi := hucont.inner_bundle hucont
    simpa only [← norm_eq_sqrt_real_inner] using hi.sqrt
  obtain ⟨A, hA⟩ := hQ.exists_bound_of_continuousOn hunorm
  let R := 3 * max A 0 + 1
  have hbound (t : ℝ) (ht : t ∈ Icc a τ) (x : M) : ‖u t x‖ ≤ max A 0 := by
    have h := hA (t, x) ⟨ht, mem_univ _⟩
    rw [norm_norm] at h
    exact h.trans (le_max_left _ _)
  have hreactionSlab := hreaction.mono
    (show Icc a τ ×ˢ (univ : Set (TotalSpace F V)) ⊆ Ico a b ×ˢ univ from
      fun q hq => ⟨⟨hq.1.1, hq.1.2.trans_lt hτ.2⟩, hq.2⟩)
  obtain ⟨L, hL⟩ := hreactionSlab.exists_fiberwise_lipschitzOnWith
    isCompact_Icc (convex_Icc a τ) CompactSpace.isCompact_univ R
  let C : ℝ := L + 1
  let d : ℝ × M → ℝ := fun q => Real.exp (-C * q.1) *
    fiberInfDist K (⟨q.2, u q.1 q.2⟩ : TotalSpace F V)
  have hdcont : ContinuousOn d Q :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_fst)).continuousOn.mul
      (((hK a ha).continuous_fiberInfDist (hcov a ha) (hmetric a ha)).comp_continuousOn hucont)
  by_contra hout
  have hdistpos : 0 < fiberInfDist K (⟨x₁, u τ x₁⟩ : TotalSpace F V) :=
    (hclosed x₁).notMem_iff_infDist_pos (hne x₁) |>.mp hout
  obtain ⟨q₀, hq₀, hmax⟩ := hQ.exists_isMaxOn
    ⟨(τ, x₁), ⟨⟨hτ.1, le_rfl⟩, mem_univ _⟩⟩ hdcont
  have hdpos : 0 < d q₀ := calc
    0 < d (τ, x₁) := mul_pos (Real.exp_pos _) hdistpos
    _ ≤ d q₀ := hmax (show (τ, x₁) ∈ Q from ⟨⟨hτ.1, le_rfl⟩, mem_univ _⟩)
  have hqt : a < q₀.1 := by
    by_contra hn
    have heq : q₀.1 = a := le_antisymm (not_lt.mp hn) hq₀.1.1
    have hz : fiberInfDist K (⟨q₀.2, u a q₀.2⟩ : TotalSpace F V) = 0 :=
      Metric.infDist_zero_of_mem (hinitial q₀.2)
    have : d q₀ = 0 := by simp only [d, heq, hz, mul_zero]
    linarith
  have hqb : q₀.1 < b := hq₀.1.2.trans_lt hτ.2
  have hqt' : q₀.1 ∈ Ico a b := ⟨hqt.le, hqb⟩
  have hr : 0 < fiberInfDist K (⟨q₀.2, u q₀.1 q₀.2⟩ : TotalSpace F V) :=
    (mul_pos_iff_of_pos_left (Real.exp_pos _)).mp hdpos
  have hout₀ : u q₀.1 q₀.2 ∉ {v : V q₀.2 | (⟨q₀.2, v⟩ : TotalSpace F V) ∈ K} := by
    intro h
    have hz := Metric.infDist_zero_of_mem h
    exact hr.ne' hz
  obtain ⟨p, hp, hmin, hunit, hnormal, hsupport⟩ :=
    exists_unit_mem_normalCone_of_notMem (hne q₀.2) (hclosed q₀.2).isComplete
      (hconvex q₀.2) hout₀
  let ν := ‖u q₀.1 q₀.2 - p‖⁻¹ • (u q₀.1 q₀.2 - p)
  have htouch : inner ℝ ν (u q₀.1 q₀.2 - p) =
      fiberInfDist K (⟨q₀.2, u q₀.1 q₀.2⟩ : TotalSpace F V) := by
    have hpos : 0 < ‖u q₀.1 q₀.2 - p‖ := hmin.symm ▸ hr
    dsimp only [ν]
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq, pow_two,
      ← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul]
    exact hmin
  have hspatial : IsLocalMax (fun y =>
      fiberInfDist K (⟨y, u q₀.1 y⟩ : TotalSpace F V)) q₀.2 := by
    apply Filter.Eventually.of_forall
    intro y
    exact (mul_le_mul_iff_right₀ (Real.exp_pos (-C * q₀.1))).mp
      (hmax (show (q₀.1, y) ∈ Q from ⟨hq₀.1, mem_univ _⟩))
  have hslice₂ := hspace q₀.1 ⟨hqt, hqb⟩ q₀.2
  have hlap := (hK q₀.1 hqt').inner_rawBundleConnLap_nonpos_of_fiberInfDist_localMax
    (hcov q₀.1 hqt') (hmetric q₀.1 hqt') (g q₀.1)
    BoundarylessManifold.isInteriorPoint hslice₂ p ν hnormal hunit.le
    htouch hspatial
  have hdrift := (hK q₀.1 hqt').inner_covariantDerivative_eq_zero_of_fiberInfDist_localMax
    (hcov q₀.1 hqt') (hmetric q₀.1 hqt') BoundarylessManifold.isInteriorPoint
    (hslice₂.mdifferentiableAt (by simp)) p ν hnormal hunit.le htouch hspatial (X q₀.1 q₀.2)
  have hFnorm : inner ℝ ν (reaction q₀.1 q₀.2 p) ≤ 0 :=
    hinward q₀.1 ⟨hqt, hqb⟩ q₀.2 p ν hnormal
  have hpbound : ‖p‖ ≤ R := by
    have hdist : ‖u q₀.1 q₀.2 - p‖ ≤ ‖u q₀.1 q₀.2 - u a q₀.2‖ := by
      rw [hmin]
      simpa only [dist_eq_norm] using Metric.infDist_le_dist_of_mem (x := u q₀.1 q₀.2)
        (show u a q₀.2 ∈ {v : V q₀.2 | (⟨q₀.2, v⟩ : TotalSpace F V) ∈ K} from hinitial q₀.2)
    have hu₀ := hbound q₀.1 hq₀.1 q₀.2
    have hua := hbound a ⟨le_rfl, haτ.le⟩ q₀.2
    have htri := norm_sub_le (u q₀.1 q₀.2) (u a q₀.2)
    have hp' := norm_le_norm_sub_add p (u q₀.1 q₀.2)
    rw [norm_sub_rev p] at hp'
    dsimp only [R]
    linarith
  have hubound : ‖u q₀.1 q₀.2‖ ≤ R := by
    have h := hbound q₀.1 hq₀.1 q₀.2
    dsimp only [R]
    linarith [le_max_right A 0]
  have hreactdist := (hL q₀.1 hq₀.1 q₀.2 (mem_univ _)).norm_sub_le
    (by simpa only [Metric.mem_closedBall, dist_zero_right] using hubound)
    (by simpa only [Metric.mem_closedBall, dist_zero_right] using hpbound)
  have hreactionBound : inner ℝ ν (reaction q₀.1 q₀.2 (u q₀.1 q₀.2)) ≤
      L * fiberInfDist K (⟨q₀.2, u q₀.1 q₀.2⟩ : TotalSpace F V) := by
    have hinner := real_inner_le_norm ν
      (reaction q₀.1 q₀.2 (u q₀.1 q₀.2) - reaction q₀.1 q₀.2 p)
    rw [hunit, one_mul, inner_sub_right] at hinner
    rw [hmin] at hreactdist
    change inner ℝ ν (reaction q₀.1 q₀.2 (u q₀.1 q₀.2)) ≤
      L * Metric.infDist (u q₀.1 q₀.2) {v : V q₀.2 | (⟨q₀.2, v⟩ : TotalSpace F V) ∈ K}
    linarith
  let B := rawBundleConnLap (g q₀.1) (cov q₀.1) (u q₀.1) q₀.2 +
    (cov q₀.1) (u q₀.1) q₀.2 (X q₀.1 q₀.2) + reaction q₀.1 q₀.2 (u q₀.1 q₀.2)
  have hB : inner ℝ ν B ≤ L * fiberInfDist K (⟨q₀.2, u q₀.1 q₀.2⟩ : TotalSpace F V) := by
    simp only [B, inner_add_right, hdrift, add_zero]
    linarith
  let ψ : ℝ → ℝ := fun t => Real.exp (-C * t) * inner ℝ ν (u t q₀.2 - p)
  have hψ₀ : ψ q₀.1 = d q₀ := by dsimp only [ψ, d]; rw [htouch]
  have hψmax : IsMaxOn ψ (Icc a q₀.1) q₀.1 := by
    intro t ht
    calc
      ψ t ≤ d (t, q₀.2) :=
        mul_le_mul_of_nonneg_left (hsupport (u t q₀.2)) (Real.exp_pos _).le
      _ ≤ ψ q₀.1 := by
        rw [hψ₀]
        exact hmax ⟨⟨ht.1, ht.2.trans hq₀.1.2⟩, mem_univ _⟩
  have hinnerderiv : HasDerivAt (fun t => inner ℝ ν (u t q₀.2 - p)) (inner ℝ ν B) q₀.1 := by
    have h := (hasDerivAt_const q₀.1 ν).inner ℝ
      ((hequation q₀.1 ⟨hqt, hqb⟩ q₀.2).sub_const p)
    simpa only [inner_zero_left, add_zero] using h
  have hexp : HasDerivAt (fun t : ℝ => Real.exp (-C * t))
      (Real.exp (-C * q₀.1) * (-C)) q₀.1 := by
    simpa only [id_eq, mul_one] using ((hasDerivAt_id q₀.1).const_mul (-C)).exp
  have hψderiv := hexp.mul hinnerderiv
  have hsign := DifferentialGeometry.Analysis.Calculus.deriv_nonneg_of_isMaxOn_left
    (by
      filter_upwards [Icc_mem_nhdsLE_of_mem (show q₀.1 ∈ Ioc a q₀.1 from ⟨hqt, le_rfl⟩)]
        with t ht
      exact hψmax ht) hψderiv.differentiableAt
  rw [hψderiv.deriv, htouch] at hsign
  have hweighted := mul_le_mul_of_nonneg_left hB (Real.exp_pos (-C * q₀.1)).le
  have hpositive := mul_pos (Real.exp_pos (-C * q₀.1)) hr
  dsimp only [C] at hsign
  nlinarith

theorem hamilton_weak_maximum_principle
    (g : ℝ → SmoothRiemannianMetric I M) (cov : ℝ → CovariantDerivative I F V)
    (X : ℝ → ∀ x : M, TangentSpace I x) (reaction : ℝ → ∀ x : M, V x → V x)
    {a b : ℝ} {K : Set (TotalSpace F V)} {u : ℝ → ∀ x : M, V x}
    (hcov : ∀ t ∈ Ico a b, ContMDiffCovariantDerivative (cov t) ∞)
    (hmetric : ∀ t ∈ Ico a b, (cov t).IsMetricCompatible)
    (hK : ∀ t ∈ Ico a b, (cov t).IsParallelSet K)
    (hclosed : ∀ x, IsClosed {v : V x | (⟨x, v⟩ : TotalSpace F V) ∈ K})
    (hconvex : ∀ x, Convex ℝ {v : V x | (⟨x, v⟩ : TotalSpace F V) ∈ K})
    (hreaction : ContMDiffOn (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, F))) (I.prod 𝓘(ℝ, F)) 1
      (fun q : ℝ × TotalSpace F V =>
        (⟨q.2.proj, reaction q.1 q.2.proj q.2.2⟩ : TotalSpace F V)) (Ico a b ×ˢ univ))
    (hinvariant : ∀ x, IsForwardInvariantForODEOn (fun t v => reaction t x v)
      {v : V x | (⟨x, v⟩ : TotalSpace F V) ∈ K} (Ico a b))
    (hu : ContinuousOn (fun q : ℝ × M =>
      (⟨q.2, u q.1 q.2⟩ : TotalSpace F V)) (Ico a b ×ˢ univ))
    (hspace : ∀ t ∈ Ioo a b, ∀ x, ContMDiffAt I (I.prod 𝓘(ℝ, F)) 2 (T% (u t)) x)
    (hequation : ∀ t ∈ Ioo a b, ∀ x, HasDerivAt (fun s => u s x)
      (rawBundleConnLap (g t) (cov t) (u t) x + (cov t) (u t) x (X t x) +
        reaction t x (u t x)) t)
    (hinitial : ∀ x, (⟨x, u a x⟩ : TotalSpace F V) ∈ K) :
    ∀ t ∈ Ico a b, ∀ x, (⟨x, u t x⟩ : TotalSpace F V) ∈ K := by
  apply hamilton_weak_maximum_principle_of_supporting_normal g cov X reaction hcov hmetric hK
    hclosed hconvex hreaction _ hu hspace hequation hinitial
  intro t ht x p ν hν
  let _ : FiniteDimensional ℝ (V x) := by
    let L := VectorBundle.continuousLinearEquivAt ℝ F V x
    exact FiniteDimensional.of_injective L.toLinearMap L.injective
  let _ : CompleteSpace (V x) := FiniteDimensional.complete ℝ (V x)
  have hf : ContDiffAt ℝ 1 (fun q : ℝ × V x => reaction q.1 x q.2) (t, p) :=
    (hreaction.contDiffOn_fiberwise x).contDiffAt
      (prod_mem_nhds (Ico_mem_nhds ht.1 ht.2) univ_mem)
  exact (hinvariant x).inner_nonpos_of_contDiffAt (Ico_mem_nhds ht.1 ht.2) hf hν

theorem hamilton_weak_maximum_principle_of_contMDiffOn
    (g : ℝ → SmoothRiemannianMetric I M) (cov : ℝ → CovariantDerivative I F V)
    (X : ℝ → ∀ x : M, TangentSpace I x) (reaction : ℝ → ∀ x : M, V x → V x)
    {a b : ℝ} {K : Set (TotalSpace F V)} {u : ℝ → ∀ x : M, V x}
    (hcov : ∀ t ∈ Ico a b, ContMDiffCovariantDerivative (cov t) ∞)
    (hmetric : ∀ t ∈ Ico a b, (cov t).IsMetricCompatible)
    (hK : ∀ t ∈ Ico a b, (cov t).IsParallelSet K)
    (hclosed : ∀ x, IsClosed {v : V x | (⟨x, v⟩ : TotalSpace F V) ∈ K})
    (hconvex : ∀ x, Convex ℝ {v : V x | (⟨x, v⟩ : TotalSpace F V) ∈ K})
    (hreaction : ContMDiffOn (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, F))) (I.prod 𝓘(ℝ, F)) 1
      (fun q : ℝ × TotalSpace F V =>
        (⟨q.2.proj, reaction q.1 q.2.proj q.2.2⟩ : TotalSpace F V)) (Ico a b ×ˢ univ))
    (hinvariant : ∀ x, IsForwardInvariantForODEOn (fun t v => reaction t x v)
      {v : V x | (⟨x, v⟩ : TotalSpace F V) ∈ K} (Ico a b))
    (hu : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, F)) 2
      (fun q : ℝ × M => (⟨q.2, u q.1 q.2⟩ : TotalSpace F V)) (Ico a b ×ˢ univ))
    (hequation : ∀ t ∈ Ioo a b, ∀ x, HasDerivAt (fun s => u s x)
      (rawBundleConnLap (g t) (cov t) (u t) x + (cov t) (u t) x (X t x) +
        reaction t x (u t x)) t)
    (hinitial : ∀ x, (⟨x, u a x⟩ : TotalSpace F V) ∈ K) :
    ∀ t ∈ Ico a b, ∀ x, (⟨x, u t x⟩ : TotalSpace F V) ∈ K := by
  apply hamilton_weak_maximum_principle g cov X reaction hcov hmetric hK hclosed hconvex
    hreaction hinvariant hu.continuousOn _ hequation hinitial
  intro t ht x
  have hslice : ContMDiffOn I (I.prod 𝓘(ℝ, F)) 2 (T% (u t)) univ :=
    hu.comp (contMDiff_const.prodMk contMDiff_id).contMDiffOn
      (fun y _ => ⟨⟨ht.1.le, ht.2⟩, mem_univ y⟩)
  exact hslice.contMDiffAt univ_mem

end DifferentialGeometry.Analysis.Parabolic
