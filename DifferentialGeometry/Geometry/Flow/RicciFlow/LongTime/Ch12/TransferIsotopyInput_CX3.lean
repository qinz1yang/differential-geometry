import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TransferIsotopyLogChart_CX3
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TransferIsotopyBounds_CX3

set_option autoImplicit false

/-!
# CH12-CX3: map-level chart closeness supplies the S15 smallness hypothesis

The original S15 smoothness and normal-radius assumptions on `O` are retained.
The new higher-order input concerns only the actual displacement of `Φ` on `D2`.
The cutoff is supported in `interior D2`, so no jets of `Φ` outside `D2` are used.
-/

noncomputable section
open scoped Manifold ContDiff Topology ENNReal
open Set Function Bundle Filter Metric

namespace GC.LongTime.Ch12
open DifferentialGeometry DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Geometry.Riemannian.Exponential

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Actual coordinate-displacement jets, with the chart-source condition stated
explicitly.  This definition mentions neither a logarithm nor a vector field. -/
def CkCloseInAtlas_CX3 (A : CkAtlas_S15 I M) (D : Set M) (k : ℕ) (δ : ℝ) (Φ : M → M) : Prop :=
  ∀ i : Fin A.n, ∀ x ∈ closedBall (extChartAt I (A.ctr i) (A.ctr i)) (A.rad i),
    (extChartAt I (A.ctr i)).symm x ∈ D →
      Φ ((extChartAt I (A.ctr i)).symm x) ∈ (extChartAt I (A.ctr i)).source ∧
      ∀ j ≤ k, ‖iteratedFDeriv ℝ j (chartDisplacement_CX3 (I := I) (A.ctr i) Φ) x‖ < δ

omit [FiniteDimensional ℝ E] in
theorem chartDisplacement_contDiffAt_CX3 (c : M) {Φ : M → M} {O : Set M}
    (hO : IsOpen O) (hΦ : ContMDiffOn I I ∞ Φ O) {x : E}
    (hx : x ∈ (extChartAt I c).target) (hp : (extChartAt I c).symm x ∈ O)
    (hq : Φ ((extChartAt I c).symm x) ∈ (extChartAt I c).source) :
    ContDiffAt ℝ ∞ (chartDisplacement_CX3 (I := I) c Φ) x := by
  have hsym : ContMDiffAt 𝓘(ℝ, E) I ∞ (extChartAt I c).symm x :=
    (contMDiffOn_extChartAt_symm c).contMDiffAt ((isOpen_extChartAt_target c).mem_nhds hx)
  have hmap := (hΦ.contMDiffAt (hO.mem_nhds hp)).comp x hsym
  have hext : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I c) (extChartAt I c).source := by
    rw [extChartAt_source]; exact contMDiffOn_extChartAt
  have hcoord : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞
      (fun y => extChartAt I c (Φ ((extChartAt I c).symm y))) x :=
    (hext.contMDiffAt ((isOpen_extChartAt_source c).mem_nhds hq)).comp x hmap
  exact (contMDiffAt_iff_contDiffAt.mp hcoord).sub contDiffAt_id

section Complete
variable [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)] [LocallyCompactSpace M]

theorem cutoff_section_smooth_CX3 {O : Set M} (hO : IsOpen O)
    (χ : M → ℝ) (hχ : ContMDiff I 𝓘(ℝ, ℝ) ∞ χ) (hsupp : tsupport χ ⊆ O)
    (v : M → TangentBundle I M) (hv : ContMDiffOn I I.tangent ∞ v O)
    (hproj : ∀ p ∈ O, (v p).proj = p) :
    ContMDiff I I.tangent ∞ (secBundle_S15 (fun p => χ p • secOf_S15 v p)) := by
  intro p
  by_cases hp : p ∈ O
  · have hV : ContMDiffAt I I.tangent ∞ (secBundle_S15 (secOf_S15 v)) p := by
      refine (hv.contMDiffAt (hO.mem_nhds hp)).congr_of_eventuallyEq ?_
      filter_upwards [hO.mem_nhds hp] with y hy
      exact secBundle_secOf_S15 v (hproj y hy)
    exact contMDiffAt_smul_tangent_S15 (secBundle_S15 (secOf_S15 v)) χ hV (hχ p)
  · have hpt : p ∉ tsupport χ := fun ht => hp (hsupp ht)
    have hz : ContMDiffAt I I.tangent ∞ (fun y : M => (⟨y, (0 : E)⟩ : TangentBundle I M)) p :=
      (Bundle.contMDiff_zeroSection ℝ (TangentSpace I (M := M))) p
    refine hz.congr_of_eventuallyEq ?_
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hpt] with y hy
    simp only [secBundle_S15, hy, Pi.zero_apply, zero_smul]
    rfl

omit [LocallyCompactSpace M] in
theorem cutoff_coord_zero_germ_CX3 (c : M) (χ : M → ℝ) (v : M → TangentBundle I M)
    {x : E} (hx : x ∈ (extChartAt I c).target)
    (hp : (extChartAt I c).symm x ∉ tsupport χ) :
    coordSec_S15 c (fun p => χ p • secOf_S15 v p) =ᶠ[𝓝 x] (fun _ => (0 : E)) := by
  have hc : ContinuousAt (extChartAt I c).symm x :=
    (continuousOn_extChartAt_symm c).continuousAt ((isOpen_extChartAt_target c).mem_nhds hx)
  have hz : ∀ᶠ y in 𝓝 x, χ ((extChartAt I c).symm y) = 0 :=
    hc (notMem_tsupport_iff_eventuallyEq.mp hp)
  filter_upwards [hz, (isOpen_extChartAt_target c).mem_nhds hx] with y hy hyT
  have hb : (extChartAt I c).symm y ∈ (trivializationAt E (TangentSpace I) c).baseSet := by
    rw [baseSet_eq_source_S15]; exact (extChartAt I c).map_target hyT
  dsimp only [coordSec_S15, secBundle_S15]
  rw [hy, zero_smul]
  change ((trivializationAt E (TangentSpace I) c)
    (zeroSection E (TangentSpace I) ((extChartAt I c).symm y))).2 = 0
  rw [(trivializationAt E (TangentSpace I) c).zeroSection (R := ℝ) hb]

variable (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)

theorem cutoffLog_eq_section_CX3 (c : M) (χ : M → ℝ) {Φ : M → M}
    {N : Set (M × M)}
    (huniq : ∀ z ∈ N, ∀ w : TangentSpace I z.1,
      expMapIntrinsic g hEnorm z.1 w = z.2 →
      Real.sqrt (g.inner z.1 w w) = (Manifold.riemannianEDist I z.1 z.2).toReal →
      transferLog_CX3 g hEnorm z = (⟨z.1, w⟩ : TangentBundle I M))
    (v : M → TangentBundle I M) {x : E}
    (hq : Φ ((extChartAt I c).symm x) ∈ (extChartAt I c).source)
    (hdom : (x, chartDisplacement_CX3 (I := I) c Φ x) ∈ logChartDom_CX3 (I := I) c N)
    (hv : (v ((extChartAt I c).symm x)).proj = (extChartAt I c).symm x ∧
      expMapIntrinsic g hEnorm ((extChartAt I c).symm x) (v ((extChartAt I c).symm x)).snd =
        Φ ((extChartAt I c).symm x) ∧
      tanLen_S15 g (v ((extChartAt I c).symm x)) =
        (Manifold.riemannianEDist I ((extChartAt I c).symm x) (Φ ((extChartAt I c).symm x))).toReal) :
    secBundle_S15 (fun p => χ p • secOf_S15 v p) ((extChartAt I c).symm x) =
      cutoffLogBundle_CX3 g hEnorm c χ (x, chartDisplacement_CX3 (I := I) c Φ x) := by
  have hpair : logPair_CX3 (I := I) c (x, chartDisplacement_CX3 (I := I) c Φ x) =
      ((extChartAt I c).symm x, Φ ((extChartAt I c).symm x)) := by
    unfold logPair_CX3 chartDisplacement_CX3
    dsimp only
    rw [add_sub_cancel, (extChartAt I c).left_inv hq]
  have hlen := hv.2.2
  rw [← secBundle_secOf_S15 v hv.1] at hlen
  have hzN : ((extChartAt I c).symm x, Φ ((extChartAt I c).symm x)) ∈ N := by
    have ht := hdom.2
    change logPair_CX3 (I := I) c (x, chartDisplacement_CX3 (I := I) c Φ x) ∈ N at ht
    rwa [hpair] at ht
  have hlog := huniq ((extChartAt I c).symm x, Φ ((extChartAt I c).symm x)) hzN
    (secOf_S15 v ((extChartAt I c).symm x)) hv.2.1 hlen
  unfold cutoffLogBundle_CX3
  rw [hpair, hlog]
  rfl

/-- **H1-E, Φ-level input.**  For the fixed atlas and nested compact domains,
choose the cutoff and normal neighborhood first.  Every requested `ε > 0` then
has an input tolerance chosen before `Φ`; the S15 logarithmic section multiplied
by this cutoff is globally smooth and `CkSmall_S15`. -/
theorem exists_CkSmall_transfer_field_CX3 (A : CkAtlas_S15 I M)
    {D1 D2 : Set M} (hD1 : IsCompact D1) (hD2 : IsCompact D2)
    (hD12 : D1 ⊆ interior D2) (k : ℕ) :
    ∃ O : Set M, IsOpen O ∧ D2 ⊆ O ∧ ∃ ρ : ℝ, 0 < ρ ∧ ∃ χ : M → ℝ,
      ContMDiff I 𝓘(ℝ, ℝ) ∞ χ ∧ (∀ p ∈ D1, χ p = 1) ∧
      (∀ p, χ p ∈ Icc (0 : ℝ) 1) ∧ tsupport χ ⊆ interior D2 ∧
      ∀ ε : ℝ, 0 < ε → ∃ ε' : ℝ, 0 < ε' ∧
        ∀ Φ : M → M, ContMDiffOn I I ∞ Φ O →
          (∀ p ∈ O, Manifold.riemannianEDist I p (Φ p) < ENNReal.ofReal ρ) →
          CkCloseInAtlas_CX3 A D2 k ε' Φ →
          ∃ v : M → TangentBundle I M, ContMDiffOn I I.tangent ∞ v O ∧
            (∀ p ∈ O, (v p).proj = p ∧ expMapIntrinsic g hEnorm p (v p).snd = Φ p ∧
              tanLen_S15 g (v p) = (Manifold.riemannianEDist I p (Φ p)).toReal) ∧
            ContMDiff I I.tangent ∞ (secBundle_S15 (fun p => χ p • secOf_S15 v p)) ∧
            (∀ p ∈ D1, expMapIntrinsic g hEnorm p (χ p • secOf_S15 v p) = Φ p) ∧
            (∀ p, p ∉ D2 → χ p • secOf_S15 v p = 0) ∧
            CkSmall_S15 g A (fun p => χ p • secOf_S15 v p) k ε := by
  classical
  obtain ⟨O, hO, hD2O, ρ, hρ, hsec⟩ := exists_transfer_section_S15 g hEnorm hD2
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
  refine ⟨O, hO, hD2O, ρ, hρ, χ, hχ, fun p hp => (hone p).mp hp,
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
  obtain ⟨v, hvs, hv⟩ := hsec Φ hΦ hdist
  refine ⟨v, hvs, hv, cutoff_section_smooth_CX3 hO χ hχ htsO v hvs (fun p hp => (hv p hp).1),
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
      have hc : ContDiffAt ℝ ∞ c x := chartDisplacement_contDiffAt_CX3 (A.ctr i) hO hΦ hxT hpO hclosex.1
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
        have hgraph : ContinuousAt (fun y : E => (y, c y)) x := continuousAt_id.prodMk hc.continuousAt
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
          exact congrArg (fun u : TangentBundle I M => ((trivializationAt E (TangentSpace I) (A.ctr i)) u).2) hy
        have hz : (fun y => cutoffLogCoord_CX3 g hEnorm (A.ctr i) χ (y, (0 : E))) =ᶠ[𝓝 x]
            (fun _ => (0 : E)) := by
          filter_upwards [(isOpen_extChartAt_target (A.ctr i)).mem_nhds hxT] with y hy
          exact cutoffLogCoord_zero_CX3 g hEnorm (A.ctr i) χ hy
        have hjbound := hjet j hj
        rw [(hz.iteratedFDeriv ℝ j).eq_of_nhds, iteratedFDeriv_fun_zero, Pi.zero_apply, sub_zero] at hjbound
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

end Complete
end GC.LongTime.Ch12
