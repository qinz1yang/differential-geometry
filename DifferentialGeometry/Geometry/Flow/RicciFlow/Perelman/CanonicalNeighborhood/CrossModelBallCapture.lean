import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ModelWitness
import DifferentialGeometry.Geometry.Comparison.DistanceHessianLocal
import DifferentialGeometry.Geometry.Metric.DirectLimit.Distance
import DifferentialGeometry.Topology.FirstExit

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood

open Bundle Filter MeasureTheory Set
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff Topology ENNReal

variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [FiniteDimensional ℝ E']
  {H H' : Type*} [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'}
  {M N : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] [T2Space N]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem ball_subset_image_of_metric_lower_crossModel
    (h : SmoothRiemannianMetric J N) (g : SmoothRiemannianMetric I M)
    (F : PartialDiffeomorph J I N M ∞) (p : N)
    {R L : ℝ} (hR : 0 < R) (hL : 0 < L)
    (hcpt : IsCompact (riemannianClosedBallOf h p R))
    (hsource : riemannianClosedBallOf h p R ⊆ F.source)
    (hlower : ∀ y ∈ riemannianClosedBallOf h p R,
      ∀ v : TangentSpace J y, h.inner y v v ≤
        L ^ 2 * g.inner (F y) (mfderiv J I (F : N → M) y v)
          (mfderiv J I (F : N → M) y v)) :
    riemannianBallOf g (F p) (R / L) ⊆
      (F : N → M) '' riemannianClosedBallOf h p R := by
  classical
  let B := riemannianClosedBallOf (I := J) h p R
  let U := riemannianBallOf (I := J) h p R
  let K := (F : N → M) '' B
  have hUB : U ⊆ B := by
    intro y hy
    change riemannianEDistOf (I := J) h p y ≤ ENNReal.ofReal R
    exact le_of_lt hy
  have hUopen : IsOpen U := isOpen_lt (continuous_riemannianEDist (I := J) h p) continuous_const
  have hpU : p ∈ U := by
    change riemannianEDistOf (I := J) h p p < ENNReal.ofReal R
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr hR
  have hKcpt : IsCompact K :=
    hcpt.image_of_continuousOn (F.contMDiffOn_toFun.continuousOn.mono hsource)
  have hFKopen : IsOpen ((F : N → M) '' U) :=
    F.toOpenPartialHomeomorph.isOpen_image_of_subset_source hUopen (hUB.trans hsource)
  have hFKint : (F : N → M) '' U ⊆ interior K :=
    interior_maximal (Set.image_mono hUB) hFKopen
  have hKtarget : K ⊆ F.target := by
    rintro z ⟨y, hy, rfl⟩
    exact F.map_source' (hsource hy)
  intro z hz
  by_contra hzK
  have hzlt : riemannianEDistOf (I := I) g (F p) z < ENNReal.ofReal (R / L) :=
    hz
  obtain ⟨γ, hγ0, hγ1, hγ, hlen⟩ := exists_lt_of_edistOf_lt (I := I) g hzlt
  obtain ⟨t, ht, hstay, hfront⟩ := exists_first_exit_frontier
    hKcpt.isClosed zero_lt_one hγ.continuousOn
    (hγ0 ▸ hFKint ⟨p, hpU, rfl⟩) (by simpa only [hγ1] using hzK)
  have hfront' : γ t ∈ K ∧ γ t ∉ interior K := by
    simpa only [frontier, hKcpt.isClosed.closure_eq, Set.mem_sdiff] using hfront
  let β : ℝ → N := (F.symm : M → N) ∘ γ
  have hβball : ∀ s ∈ Set.Icc (0 : ℝ) t, β s ∈ B := by
    intro s hs
    obtain ⟨y, hy, hFy⟩ := hstay s hs
    change (F.symm : M → N) (γ s) ∈ B
    have hleft : (F.symm : M → N) (F y) = y := F.left_inv' (hsource hy)
    rw [← hFy, hleft]
    exact hy
  have hβ : ContMDiffOn 𝓘(ℝ, ℝ) J 1 β (Set.Icc 0 t) :=
    (F.symm.contMDiffOn_toFun.of_le (by simp)).comp
      (hγ.mono (Set.Icc_subset_Icc le_rfl ht.2)) (fun s hs => hKtarget (hstay s hs))
  have hβ0 : β 0 = p := by
    change (F.symm : M → N) (γ 0) = p
    rw [hγ0]
    exact F.left_inv' (hsource (hUB hpU))
  have hexit : ENNReal.ofReal R ≤ riemannianEDistOf (I := J) h p (β t) := by
    apply le_of_not_gt
    intro hdist
    apply hfront'.2
    apply hFKint
    exact ⟨β t, hdist, F.right_inv' (hKtarget hfront'.1)⟩
  have hspeed : ∀ s ∈ Set.Ioo (0 : ℝ) t,
      Real.sqrt (h.inner (β s) (mfderiv 𝓘(ℝ, ℝ) J β s 1)
        (mfderiv 𝓘(ℝ, ℝ) J β s 1)) ≤
      L * Real.sqrt (g.inner (γ s) (mfderiv 𝓘(ℝ, ℝ) I γ s 1)
        (mfderiv 𝓘(ℝ, ℝ) I γ s 1)) := by
    intro s hs
    have hscc : s ∈ Set.Icc (0 : ℝ) t := ⟨hs.1.le, hs.2.le⟩
    have hstgt : γ s ∈ F.target := hKtarget (hstay s hscc)
    have hβd : MDifferentiableAt 𝓘(ℝ, ℝ) J β s :=
      (hβ.contMDiffAt (Icc_mem_nhds hs.1 hs.2)).mdifferentiableAt (by norm_num)
    have hFd : MDifferentiableAt J I (F : N → M) (β s) :=
      (F.contMDiffOn_toFun.contMDiffAt
        (F.open_source.mem_nhds (hsource (hβball s hscc)))).mdifferentiableAt (by simp)
    have heq : (F : N → M) ∘ β =ᶠ[nhds s] γ := by
      have hγc : ContinuousAt γ s := hγ.continuousOn.continuousAt
        (Icc_mem_nhds hs.1 (hs.2.trans_le ht.2))
      filter_upwards [hγc.preimage_mem_nhds (F.open_target.mem_nhds hstgt)] with q hq
      exact F.right_inv' hq
    have hderiv : mfderiv J I (F : N → M) (β s) (mfderiv 𝓘(ℝ, ℝ) J β s 1) =
        mfderiv 𝓘(ℝ, ℝ) I γ s 1 := by
      rw [← mfderiv_comp_apply s hFd hβd, heq.mfderiv_eq]
      rfl
    have hcompval : F (β s) = γ s := F.right_inv' hstgt
    have hinnerEq :
        g.inner (F (β s)) (mfderiv J I (F : N → M) (β s)
          (mfderiv 𝓘(ℝ, ℝ) J β s 1))
          (mfderiv J I (F : N → M) (β s) (mfderiv 𝓘(ℝ, ℝ) J β s 1)) =
        g.inner (γ s) (mfderiv 𝓘(ℝ, ℝ) I γ s 1) (mfderiv 𝓘(ℝ, ℝ) I γ s 1) := by
      rw [hderiv, hcompval]
    have hbd := hlower (β s) (hβball s hscc) (mfderiv 𝓘(ℝ, ℝ) J β s 1)
    rw [hinnerEq] at hbd
    calc
      _ ≤ Real.sqrt (L ^ 2 * g.inner (γ s) (mfderiv 𝓘(ℝ, ℝ) I γ s 1)
          (mfderiv 𝓘(ℝ, ℝ) I γ s 1)) := Real.sqrt_le_sqrt hbd
      _ = _ := by rw [Real.sqrt_mul (sq_nonneg L), Real.sqrt_sq hL.le]
  have hlift : metricPathELength (I := J) h β 0 t ≤
      ENNReal.ofReal L * metricPathELength (I := I) g γ 0 t := by
    rw [metricPathELength_eq, metricPathELength_eq, ← lintegral_const_mul' _ _
      ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' measurableSet_Ioo fun s hs => ?_
    rw [← ENNReal.ofReal_mul hL.le]
    exact ENNReal.ofReal_le_ofReal (hspeed s hs)
  have hliftlt : metricPathELength (I := J) h β 0 t < ENNReal.ofReal R := by
    calc
      _ ≤ ENNReal.ofReal L * metricPathELength (I := I) g γ 0 t := hlift
      _ ≤ ENNReal.ofReal L * metricPathELength (I := I) g γ 0 1 :=
        mul_le_mul_right (metricPathELength_mono (I := I) g γ le_rfl ht.2) _
      _ < ENNReal.ofReal L * ENNReal.ofReal (R / L) :=
        ENNReal.mul_lt_mul_right (ENNReal.ofReal_ne_zero_iff.mpr hL)
          ENNReal.ofReal_ne_top hlen
      _ = ENNReal.ofReal R := by
        rw [← ENNReal.ofReal_mul hL.le, mul_div_cancel₀ R hL.ne']
  have hdist := edistOf_le_metricPathELength (I := J) h ht.1.le hβ
  rw [hβ0] at hdist
  exact (not_lt_of_ge hexit) (hdist.trans_lt hliftlt)

theorem closedBall_subset_image_of_metric_lower_crossModel
    (h : SmoothRiemannianMetric J N) (g : SmoothRiemannianMetric I M)
    (F : PartialDiffeomorph J I N M ∞) (p : N)
    {R L r : ℝ} (hR : 0 < R) (hL : 0 < L) (hr : r < R / L)
    (hcpt : IsCompact (riemannianClosedBallOf h p R))
    (hsource : riemannianClosedBallOf h p R ⊆ F.source)
    (hlower : ∀ y ∈ riemannianClosedBallOf h p R,
      ∀ v : TangentSpace J y, h.inner y v v ≤
        L ^ 2 * g.inner (F y) (mfderiv J I (F : N → M) y v)
          (mfderiv J I (F : N → M) y v)) :
    riemannianClosedBallOf g (F p) r ⊆
      (F : N → M) '' riemannianClosedBallOf h p R := by
  intro z hz
  apply ball_subset_image_of_metric_lower_crossModel h g F p hR hL hcpt hsource hlower
  exact lt_of_le_of_lt hz ((ENNReal.ofReal_lt_ofReal_iff (div_pos hR hL)).mpr hr)

theorem short_curve_mem_image_of_metric_lower_crossModel
    (h : SmoothRiemannianMetric J N) (g : SmoothRiemannianMetric I M)
    (F : PartialDiffeomorph J I N M ∞) (p : N)
    {R L : ℝ} (hR : 0 < R) (hL : 0 < L)
    (hcpt : IsCompact (riemannianClosedBallOf h p R))
    (hsource : riemannianClosedBallOf h p R ⊆ F.source)
    (hlower : ∀ y ∈ riemannianClosedBallOf h p R,
      ∀ v : TangentSpace J y, h.inner y v v ≤
        L ^ 2 * g.inner (F y) (mfderiv J I (F : N → M) y v)
          (mfderiv J I (F : N → M) y v))
    {gamma : ℝ → M} {a b : ℝ}
    (hgamma : ContMDiffOn 𝓘(ℝ, ℝ) I 1 gamma (Icc a b))
    (hstart : gamma a = F p)
    (hlen : metricPathELength g gamma a b < ENNReal.ofReal (R / L)) :
    ∀ s ∈ Icc a b, gamma s ∈ (F : N → M) '' riemannianClosedBallOf h p R := by
  intro s hs
  apply ball_subset_image_of_metric_lower_crossModel h g F p hR hL hcpt hsource hlower
  have hdist := edistOf_le_metricPathELength g hs.1
    (hgamma.mono (Icc_subset_Icc le_rfl hs.2))
  rw [hstart] at hdist
  exact (hdist.trans (metricPathELength_mono g gamma le_rfl hs.2)).trans_lt hlen

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
