import DifferentialGeometry.Geometry.Comparison.Distance.Calabi

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set Topology
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry

open Geometry.Riemannian
open Geometry.Riemannian.Exponential
open Geometry.Riemannian.HopfRinow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_calabiTail_fraction
    [RiemannianBundle (fun y : M => TangentSpace I y)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {O x : M} {r : Real} (v : TangentSpace I O)
    (hexp : expMapIntrinsic (I := I) g hEnorm O v = x)
    (hlen : Real.sqrt (g.inner O v v) = r)
    (hr : 0 < r)
    (hr_def : r = (riemannianEDist I O x).toReal)
    (s₀ : Real) (hs₀_pos : 0 < s₀) (hs₀_half : s₀ ≤ 1 / 2) :
    ∃ tail : CalabiTail (I := I) g hEnorm O x r,
      tail.initialLength = s₀ * r ∧ tail.terminalLength = (1 - s₀) * r := by
  classical
  let z : TangentBundle I M :=
    intrinsicVelocityLift (I := I) g hEnorm O v s₀
  let u : TangentSpace I z.proj := (1 - s₀) • z.snd
  let zE : E := tangentSpaceModelContinuousLinearEquiv (I := I) z.proj z.snd
  let uE : E := (1 - s₀) • zE
  have huE :
      uE = tangentSpaceModelContinuousLinearEquiv (I := I) z.proj u := by
    dsimp only [uE, zE, u]
    rw [map_smul]
  let left : Real := s₀ * r
  let ell : Real := (1 - s₀) * r
  have hs₀ : s₀ ∈ Set.Ioo (0 : Real) 1 :=
    ⟨hs₀_pos, lt_of_le_of_lt hs₀_half (by norm_num)⟩
  have hs₀_closed : s₀ ∈ Set.Icc (0 : Real) 1 :=
    ⟨hs₀.1.le, hs₀.2.le⟩
  have hfin : riemannianEDist I O x ≠ (⊤ : ENNReal) := by
    intro htop
    rw [htop, ENNReal.toReal_top] at hr_def
    linarith
  have hlen_dist :
      Real.sqrt (g.inner O v v) =
        (riemannianEDist I O x).toReal :=
    hlen.trans hr_def
  have hnot :
      ¬ IsConjVec (I := I) g hEnorm z.proj
        (tangentSpaceModelContinuousLinearEquiv (I := I) z.proj u) := by
    with_unfolding_all
      exact Geometry.Riemannian.Variation.tail_not_conj_of_min
        (I := I) g hEnorm v hexp hlen_dist (hr_def ▸ hr) hs₀
  obtain ⟨B, hsource⟩ :=
    branch_of_not_conj (I := I) g hEnorm hnot
  have hexp_tail :
      expMapIntrinsic (I := I) g hEnorm z.proj u = x := by
    have hcontinue :=
      congrFun
        (intrinsicGeodesic_continuation
          (I := I) g hEnorm O v s₀) (1 - s₀)
    have hend :
        intrinsicGeodesic (I := I) g hEnorm O v 1 = x := by
      simpa only [expMapIntrinsic_def] using hexp
    change intrinsicGeodesic (I := I) g hEnorm z.proj u 1 = x
    dsimp only [u]
    rw [intrinsicGeodesic_smul (I := I) g hEnorm]
    change intrinsicGeodesic (I := I) g hEnorm
      (intrinsicGeodesic (I := I) g hEnorm O v s₀)
      (mfderiv 𝓘(Real, Real) I
        (intrinsicGeodesic (I := I) g hEnorm O v) s₀ 1) (1 - s₀) = x
    calc
      intrinsicGeodesic (I := I) g hEnorm
          (intrinsicGeodesic (I := I) g hEnorm O v s₀)
          (mfderiv 𝓘(Real, Real) I
            (intrinsicGeodesic (I := I) g hEnorm O v) s₀ 1)
          (1 - s₀) =
          intrinsicGeodesic (I := I) g hEnorm O v (1 - s₀ + s₀) :=
        hcontinue.symm
      _ = intrinsicGeodesic (I := I) g hEnorm O v 1 := by
        congr 1
        ring
      _ = x := hend
  have hmap_eq : B.hom uE = x :=
    by
      rw [huE]
      exact (B.hom_eq hsource).symm.trans hexp_tail
  have hscale_cont : Continuous (fun t : Real => t • uE) :=
    continuous_id.smul continuous_const
  have hsource_nhds :
      {t : Real | t • uE ∈ B.hom.source} ∈ 𝓝 (1 : Real) := by
    apply hscale_cont.continuousAt.preimage_mem_nhds
    rw [huE]
    simpa only [one_smul] using B.hom.open_source.mem_nhds hsource
  obtain ⟨ε, hε, hε_sub⟩ := Metric.mem_nhds_iff.mp hsource_nhds
  let b : Real := 1 + ε / 2
  have hb : 1 < b := by
    dsimp [b]
    linarith
  have hsource_tail :
      ∀ t ∈ Set.Icc (1 : Real) b,
        t • uE ∈ B.hom.source := by
    intro t ht
    apply hε_sub
    rw [Metric.mem_ball, Real.dist_eq,
      abs_of_nonneg (sub_nonneg.mpr ht.1)]
    dsimp [b] at ht
    calc
      t - 1 ≤ ε / 2 := by linarith [ht.2]
      _ < ε := by linarith [hε]
  have htail_no :
      ∀ t ∈ Set.Ioc (0 : Real) 1,
        ¬ IsConjVec (I := I) g hEnorm z.proj
          (t • uE) := by
    intro t ht
    have htModel :
        t • uE = tangentSpaceModelContinuousLinearEquiv (I := I) z.proj (t • u) := by
      dsimp only [uE, zE, u]
      rw [map_smul, map_smul]
    rw [htModel]
    with_unfolding_all
      exact Geometry.Riemannian.Variation.tail_no_conj
        (I := I) g hEnorm v hexp hlen_dist (hr_def ▸ hr) hs₀ t ht
  have hno :
      ∀ t ∈ Set.Ioo (0 : Real) b,
        ¬ IsConjVec (I := I) g hEnorm z.proj
          (t • uE) := by
    intro t ht
    rcases le_total t 1 with ht1 | h1t
    · exact htail_no t ⟨ht.1, ht1⟩
    · exact B.not_conj (hsource_tail t ⟨h1t, ht.2.le⟩)
  have hspeed :
      g.inner z.proj z.snd z.snd = g.inner O v v := by
    with_unfolding_all exact intrinsicGeodesic_speedSq_eq (I := I) g hEnorm O v s₀
  have hu_norm :
      Real.sqrt (g.inner z.proj u u) = ell := by
    dsimp only [u]
    rw [sqrt_gInner_smul_self (I := I) g z.proj
      (sub_nonneg.mpr hs₀.2.le) z.snd, hspeed, hlen]
  have hleft :
      riemannianEDist I O z.proj = ENNReal.ofReal left := by
    change riemannianEDist I O
      (intrinsicGeodesic (I := I) g hEnorm O v s₀) = ENNReal.ofReal (s₀ * r)
    exact Geometry.Riemannian.Variation.minSegment_edist
      (I := I) g hEnorm v hexp hlen hr_def hfin hs₀_closed
  have hleftPos : 0 < left := mul_pos hs₀_pos hr
  refine ⟨{
    splitPoint := z.proj
    endpointVector := u
    initialLength := left
    terminalLength := ell
    branch := B
    conjugateScale := b
    initialLength_pos := hleftPos
    initialLength_nonneg := hleftPos.le
    terminalLength_pos := mul_pos (sub_pos.mpr hs₀.2) hr
    length_sum := by
      dsimp [left, ell]
      ring
    half_le_terminalLength := by
      dsimp only [ell]
      nlinarith [mul_le_mul_of_nonneg_right hs₀_half hr.le]
    initial_edist := hleft
    endpointVector_norm := hu_norm
    source_mem := hsource
    map_eq := hmap_eq
    one_lt_conjugateScale := hb
    no_conjugate := hno
  }, rfl, rfl⟩

end DifferentialGeometry

end
