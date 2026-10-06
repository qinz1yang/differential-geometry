import DifferentialGeometry.Analysis.Calculus.Hadamard.NormalizedFactor
import DifferentialGeometry.Topology.Manifold.AffineCharts
import DifferentialGeometry.Topology.Manifold.OpenSubtype
import DifferentialGeometry.Geometry.Metric.Pullback.PartialDiffeomorph.OpenSubtype
import Mathlib.Analysis.Normed.Module.FiniteDimension
import DifferentialGeometry.Analysis.Calculus.SmoothExtension.Compact
import DifferentialGeometry.Geometry.Metric.FiniteChartBounds
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.HomogeneousRegularity
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph
import Mathlib.Analysis.Normed.Operator.Banach

set_option autoImplicit false
noncomputable section

open Set Filter Manifold DifferentialGeometry
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Geometry.Metric.PositiveDomainCharts

open DifferentialGeometry.Topology

variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

/-- The actual affine chart with its target restricted to an open submanifold. -/
def liftedAffineChart (c : OpenPartialHomeomorph V M) (U : TopologicalSpace.Opens M)
    (hU : Nonempty U) (a : V) (L : V ≃L[ℝ] V) : OpenPartialHomeomorph V U :=
  (affineChart c a L).trans (U.openPartialHomeomorphSubtypeCoe hU).symm

theorem liftedAffineChart_val (c : OpenPartialHomeomorph V M)
    (U : TopologicalSpace.Opens M) (hU : Nonempty U) (a : V) (L : V ≃L[ℝ] V)
    {z : V} (hz : z ∈ (liftedAffineChart c U hU a L).source) :
    ((liftedAffineChart c U hU a L) z : M) = c (a + L z) := by
  change z ∈ (affineChart c a L).source ∩
    (affineChart c a L) ⁻¹' (U.openPartialHomeomorphSubtypeCoe hU).target at hz
  exact (U.openPartialHomeomorphSubtypeCoe hU).right_inv hz.2

theorem liftedAffineChart_mfderiv (c : OpenPartialHomeomorph V M)
    (U : TopologicalSpace.Opens M) (hU : Nonempty U) (a : V) (L : V ≃L[ℝ] V)
    {z : V} (hz : z ∈ (liftedAffineChart c U hU a L).source) :
    (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) (liftedAffineChart c U hU a L) z : V →L[ℝ] E) =
      mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) (affineChart c a L) z := by
  have heq : (fun y => ((liftedAffineChart c U hU a L) y : M)) =ᶠ[𝓝 z]
      (affineChart c a L : V → M) := by
    filter_upwards [(liftedAffineChart c U hU a L).open_source.mem_nhds hz] with y hy
    exact liftedAffineChart_val c U hU a L hy
  exact (DifferentialGeometry.mfderiv_subtypeVal_comp
    (liftedAffineChart c U hU a L) z).symm.trans heq.mfderiv_eq

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ V] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

/-- Exact coefficients of the completed metric in the actual rescaled chart.
The radius is the value of the same defining function at the chart center.
The factorization hypothesis is the scalar identity supplied by Hadamard's
lemma; neither a coefficient estimate nor a pullback identity is assumed. -/
theorem completedMetric_rescaled_chart_coefficient
    (c : OpenPartialHomeomorph V M) (U : TopologicalSpace.Opens M) (hU : Nonempty U)
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (gComplete : SmoothRiemannianMetric 𝓘(ℝ, E) U) (δ : M → ℝ)
    (hcomplete : ∀ (x : U) (v w : TangentSpace 𝓘(ℝ, E) x),
      gComplete.inner x v w = (δ (x : M))⁻¹ ^ 2 * (g.restrictOpen U).inner x v w)
    (a : V) (dilation : ℝ) (hdilation : dilation ≠ 0) (hr : δ (c a) ≠ 0)
    (z : V)
    (hz : z ∈ (liftedAffineChart c U hU a
      (LinearEquiv.smulOfNeZero ℝ V (dilation * δ (c a)) (mul_ne_zero hdilation hr)).toContinuousLinearEquiv).source)
    (hc : MDifferentiableAt 𝓘(ℝ, V) 𝓘(ℝ, E) c (a + (dilation * δ (c a)) • z))
    (q : ℝ) (hq : q ≠ 0)
    (hfactor : δ (c (a + (dilation * δ (c a)) • z)) = δ (c a) * q)
    (v w : V) :
    let ψ := liftedAffineChart c U hU a
      (LinearEquiv.smulOfNeZero ℝ V (dilation * δ (c a)) (mul_ne_zero hdilation hr)).toContinuousLinearEquiv
    gComplete.inner (ψ z)
      (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) ψ z v)
      (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) ψ z w) =
      (dilation ^ 2 / q ^ 2) * g.inner (c (a + (dilation * δ (c a)) • z))
        (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) c (a + (dilation * δ (c a)) • z) v)
        (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) c (a + (dilation * δ (c a)) • z) w) := by
  let r : ℝ := δ (c a)
  let L := (LinearEquiv.smulOfNeZero ℝ V (dilation * r) (mul_ne_zero hdilation hr)).toContinuousLinearEquiv
  let ψ := liftedAffineChart c U hU a L
  let x : M := c (a + (dilation * r) • z)
  let B (p : M) : E →L[ℝ] E →L[ℝ] ℝ := g.inner p
  let H : E →L[ℝ] E →L[ℝ] ℝ := gComplete.inner (ψ z)
  let D : V →L[ℝ] E := mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) c (a + (dilation * r) • z)
  let Dψ : V →L[ℝ] E := mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) ψ z
  have hL (u : V) : L u = (dilation * r) • u := rfl
  have hval : (ψ z : M) = x := liftedAffineChart_val c U hU a L hz
  have hD (u : V) : Dψ u = (dilation * r) • D u := by
    let Da : V →L[ℝ] E := mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) (affineChart c a L) z
    have hdf : Dψ = Da := liftedAffineChart_mfderiv c U hU a L hz
    have ha : Da u = D (L u) := affineChart_mfderiv a L hc u
    have hscale : D (L u) = (dilation * r) • D u := by rw [hL, map_smul]
    exact (congrArg (fun A : V →L[ℝ] E => A u) hdf).trans (ha.trans hscale)
  have hH (u₁ u₂ : E) : H u₁ u₂ = (r * q)⁻¹ ^ 2 * B x u₁ u₂ := by
    have hh : H u₁ u₂ = (δ (ψ z : M))⁻¹ ^ 2 * B (ψ z) u₁ u₂ :=
      hcomplete (ψ z) u₁ u₂
    rw [hval] at hh
    have hδ : δ x = r * q := hfactor
    rwa [hδ] at hh
  change H (Dψ v) (Dψ w) = (dilation ^ 2 / q ^ 2) * B x (D v) (D w)
  rw [hH, hD, hD]
  simp only [map_smul, smul_apply, smul_eq_mul]
  have hr' : r ≠ 0 := hr
  field_simp [hr', hq]

end DifferentialGeometry.Geometry.Metric.PositiveDomainCharts

namespace DifferentialGeometry.Geometry.Metric.PositiveDomainCharts

open Bundle Manifold Set Filter
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry
open DifferentialGeometry.Analysis
open DifferentialGeometry.Analysis.Calculus.Hadamard DifferentialGeometry.Geometry.Metric.PositiveDomainCharts
open scoped _root_.Topology Manifold ContDiff

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M]

omit [FiniteDimensional ℝ E] [T2Space M] in
private theorem finite_buffered_charts {K : Set M} (hK : IsCompact K)
    (hne : K.Nonempty) (e : V ≃L[ℝ] E) :
    ∃ t : Finset M, t.Nonempty ∧
      ∃ c : t → OpenPartialHomeomorph V M, ∃ A B : t → Set V, ∃ ε : ℝ, 0 < ε ∧
        (∀ i, ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, E) ∞ (c i) (c i).source ∧
          ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, V) ∞ (c i).symm (c i).target ∧
          IsCompact (A i) ∧ IsCompact (B i) ∧ A i ⊆ B i ∧ B i ⊆ (c i).source ∧
          ∀ a ∈ A i, MapsTo (fun z => a + z) (Metric.closedBall (0 : V) ε) (B i)) ∧
        ∃ j : K → t, ∃ a : K → V, ∀ p : K,
          c (j p) (a p) = (p : M) ∧ a p ∈ A (j p) := by
  classical
  let c : M → OpenPartialHomeomorph V M := fun p => affineChart (chartAt E p).symm 0 e
  have hct (p : M) : p ∈ (c p).target := by
    change p ∈ (affineChart (chartAt E p).symm 0 e).target
    rw [affineChart_target]
    exact mem_chart_source E p
  have hcs (p : M) : (c p).symm p ∈ (c p).source := (c p).map_target (hct p)
  have hlocal (p : M) : ∃ r : ℝ, 0 < r ∧
      Metric.closedBall ((c p).symm p) (3 * r) ⊆ (c p).source := by
    obtain ⟨ρ, hρ, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
      ((c p).open_source.mem_nhds (hcs p))
    refine ⟨ρ / 3, by positivity, ?_⟩
    simpa only [mul_div_cancel₀ _ (by norm_num : (3 : ℝ) ≠ 0)] using hsub
  choose r hr hrs using hlocal
  let O : M → Set M := fun p => (c p).target ∩
    (c p).symm ⁻¹' Metric.ball ((c p).symm p) (r p)
  have hO (p : M) : IsOpen (O p) := (c p).symm.isOpen_inter_preimage Metric.isOpen_ball
  have hcover : K ⊆ ⋃ p, O p := by
    intro p _
    exact mem_iUnion.mpr ⟨p, hct p, Metric.mem_ball_self (hr p)⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover O hO hcover
  have htn : t.Nonempty := by
    obtain ⟨p, hp⟩ := hne
    obtain ⟨q, hq, _⟩ := mem_iUnion₂.mp (ht hp)
    exact ⟨q, hq⟩
  let ε : ℝ := t.inf' htn r
  have hε : 0 < ε := (Finset.lt_inf'_iff _).mpr (fun p _ => hr p)
  have hεr (i : t) : ε ≤ r i := Finset.inf'_le _ i.property
  let A : t → Set V := fun i => Metric.closedBall ((c i).symm i) (r i)
  let B : t → Set V := fun i => Metric.closedBall ((c i).symm i) (2 * r i)
  have hchoose (p : K) : ∃ i : t, p.val ∈ O i := by
    obtain ⟨i, hi, hp⟩ := mem_iUnion₂.mp (ht p.property)
    exact ⟨⟨i, hi⟩, hp⟩
  choose j hj using hchoose
  let a : K → V := fun p => (c (j p)).symm p
  refine ⟨t, htn, fun i => c i, A, B, ε, hε, ?_, j, a, ?_⟩
  · intro i
    have hs := contMDiffOn_affineChart
      (contMDiffOn_chart_symm (I := 𝓘(ℝ, E)) (x := (i : M)))
      (contMDiffOn_chart (I := 𝓘(ℝ, E)) (x := (i : M))) (0 : E) e
    refine ⟨hs.1, hs.2, isCompact_closedBall _ _, isCompact_closedBall _ _, ?_, ?_, ?_⟩
    · exact Metric.closedBall_subset_closedBall (by linarith [hr i])
    · exact (Metric.closedBall_subset_closedBall (by linarith [hr i])).trans (hrs i)
    · intro a ha z hz
      have hzε : ‖z‖ ≤ ε := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
      have ha' : dist a ((c i).symm i) ≤ r i := ha
      have hd := dist_triangle (a + z) a ((c i).symm i)
      have hzdist : dist (a + z) a = ‖z‖ := by simp [dist_eq_norm]
      change dist (a + z) ((c i).symm i) ≤ 2 * r i
      rw [hzdist] at hd
      linarith [hεr i]
  · intro p
    exact ⟨(c (j p)).right_inv (hj p).1, Metric.ball_subset_closedBall (hj p).2⟩

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ V]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] in
private theorem liftedAffineChart_smooth
    (c : OpenPartialHomeomorph V M)
    (hc : ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, E) ∞ c c.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, V) ∞ c.symm c.target)
    (U : TopologicalSpace.Opens M) (hU : Nonempty U) (a : V) (L : V ≃L[ℝ] V) :
    ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, E) ∞ (liftedAffineChart c U hU a L)
      (liftedAffineChart c U hU a L).source ∧
    ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, V) ∞ (liftedAffineChart c U hU a L).symm
      (liftedAffineChart c U hU a L).target := by
  obtain ⟨hs, ht⟩ := contMDiffOn_affineChart hc hi a L
  let φ : _root_.PartialDiffeomorph 𝓘(ℝ, V) 𝓘(ℝ, E) V M ∞ :=
    { toPartialEquiv := (affineChart c a L).toPartialEquiv
      open_source := (affineChart c a L).open_source
      open_target := (affineChart c a L).open_target
      contMDiffOn_toFun := hs
      contMDiffOn_invFun := ht }
  let ψ := φ.trans (PartialDiffeomorph.subtypeVal (I := 𝓘(ℝ, E)) U hU).symm
  exact ⟨ψ.contMDiffOn_toFun, ψ.contMDiffOn_invFun⟩

omit [FiniteDimensional ℝ V] in
private theorem bound_normalized_coeff
    {d G : V → ℝ} (hd : ContDiff ℝ ∞ d) {s : Set V}
    (hs : IsOpen s) (hG : ContDiffOn ℝ ∞ G s)
    {K : Set (V × ℝ)} {Z : Set V} (hK : IsCompact K) (hZ : IsCompact Z)
    (dilation : ℝ)
    (hmap : ∀ p ∈ K, ∀ z ∈ Z, p.1 + (dilation * p.2) • z ∈ s)
    (hpos : ∀ p ∈ K, ∀ z ∈ Z, 0 < normalizedFactor d dilation p.1 p.2 z)
    (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ K, ∀ z ∈ Z,
      ‖iteratedFDeriv ℝ k (fun y =>
        dilation ^ 2 / (normalizedFactor d dilation p.1 p.2 y) ^ 2 * G (p.1 + (dilation * p.2) • y)) z‖ ≤ C := by
  let A : (V × ℝ) × V → V := fun p => p.1.1 + (dilation * p.1.2) • p.2
  let R : (V × ℝ) × V → ℝ := fun p => normalizedFactor d dilation p.1.1 p.1.2 p.2
  have hA : ContDiff ℝ ∞ A :=
    contDiff_fst.fst.add ((contDiff_const.mul contDiff_fst.snd).smul contDiff_snd)
  have hR : ContDiff ℝ ∞ R :=
    (contDiff_normalizedFactor hd).comp (contDiff_const.prodMk contDiff_id)
  let Ω : Set ((V × ℝ) × V) := A ⁻¹' s ∩ R ⁻¹' ({0}ᶜ : Set ℝ)
  have hΩ : IsOpen Ω :=
    (hs.preimage hA.continuous).inter (isClosed_singleton.isOpen_compl.preimage hR.continuous)
  have hF : ContDiffOn ℝ ∞ (fun p => dilation ^ 2 / (R p) ^ 2 * G (A p)) Ω :=
    (contDiffOn_const.div (hR.pow 2).contDiffOn (fun _ hp => pow_ne_zero 2 hp.2)).mul
      (hG.comp hA.contDiffOn (fun _ hp => hp.1))
  have hsub : K ×ˢ Z ⊆ Ω := by
    rintro ⟨p, z⟩ ⟨hp, hz⟩
    exact ⟨hmap p hp z hz, (hpos p hp z hz).ne'⟩
  obtain ⟨C, hC, hb⟩ := exists_bound_iteratedFDeriv_comp_affine_on_compact
    (G := V) hΩ hF (hK.prod hZ) hsub k
  let L : V →L[ℝ] (V × ℝ) × V := ContinuousLinearMap.inr ℝ (V × ℝ) V
  refine ⟨C * ‖L‖ ^ k, mul_nonneg hC (by positivity), ?_⟩
  intro p hp z hz
  have hm : (p, (0 : V)) + L z ∈ K ×ˢ Z := by
    simpa only [L, ContinuousLinearMap.inr_apply, Prod.mk_add_mk, add_zero, zero_add]
      using (show (p, z) ∈ K ×ˢ Z from ⟨hp, hz⟩)
  simpa only [L, ContinuousLinearMap.inr_apply, Prod.mk_add_mk, add_zero, zero_add]
    using hb (p, (0 : V)) L z hm


private theorem cube_subset_ball_three :
    plateauClosedCube ⊆ Metric.ball (0 : plateauCoordinateSpace) 3 := by
  intro y hy
  have hb : y ∈ Metric.closedBall (0 : plateauCoordinateSpace) 2 := by
    rw [EuclideanSpace.closedBall_zero_eq 2 (by norm_num)]
    change ∑ i : Fin 3, y i ^ 2 ≤ (2 : ℝ) ^ 2
    have hs : ∑ i : Fin 3, y i ^ 2 ≤ ∑ _ : Fin 3, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      have hi := abs_le.mp (hy i)
      nlinarith
    norm_num at hs ⊢
    linarith
  change dist y 0 ≤ 2 at hb
  change dist y 0 < 3
  exact lt_of_le_of_lt hb (by norm_num)

/-- The actual conformal completion on a relatively compact positive domain
has uniformly elliptic smooth coordinate coefficients of every order. All
charts are constructed from finitely many buffered ambient charts. No
regular-level or nonvanishing-gradient assumption on the defining function
is needed. -/
theorem homogeneouslyRegularMetric_positive_domain
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {δ : M → ℝ}
    (hδ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ δ)
    (U : TopologicalSpace.Opens M) (hU : ∀ x : M, x ∈ U ↔ 0 < δ x)
    (hK : IsCompact (closure (U : Set M)))
    (G : SmoothRiemannianMetric 𝓘(ℝ, E) U)
    (hG : ∀ (x : U) (v w : TangentSpace 𝓘(ℝ, E) x),
      G.inner x v w = (δ (x : M))⁻¹ ^ 2 * (g.restrictOpen U).inner x v w)
    (hdim : Module.finrank ℝ E = 3) : HomogeneouslyRegularMetric G := by
  classical
  by_cases hne : Nonempty U
  swap
  · let : IsEmpty U := not_nonempty_iff.mp hne
    refine ⟨1, 1, zero_lt_one, le_rfl, (fun p => isEmptyElim p), ?_, ?_⟩
    · exact fun p => isEmptyElim p
    · exact fun _ => ⟨0, le_rfl, fun p => isEmptyElim p⟩
  have : Nonempty U := hne
  let K : Set M := closure (U : Set M)
  have hKn : K.Nonempty := by
    obtain ⟨p⟩ := hne
    exact ⟨p, subset_closure p.property⟩
  let e : plateauCoordinateSpace ≃L[ℝ] E :=
    ContinuousLinearEquiv.ofFinrankEq (by simp [hdim, plateauCoordinateSpace])
  obtain ⟨t, ht, c, A, B, ε, hε, hcdata, j₀, a₀, hcenter⟩ :=
    finite_buffered_charts hK hKn e
  have : Nonempty t := by
    obtain ⟨x, hx⟩ := ht
    exact ⟨⟨x, hx⟩⟩
  have hc i := (hcdata i).1
  have hi i := (hcdata i).2.1
  have hAc i := (hcdata i).2.2.1
  have hBc i := (hcdata i).2.2.2.1
  have hAB i := (hcdata i).2.2.2.2.1
  have hBs i := (hcdata i).2.2.2.2.2.1
  have hbuffer i := (hcdata i).2.2.2.2.2.2
  obtain ⟨⟨m, M₀, hm, hmM, hell⟩, _⟩ := exists_uniform_metric_chart_bounds
    g c hc hi B hBc hBs (fun i : Fin 3 => EuclideanSpace.single i (1 : ℝ))
  obtain ⟨b₀, hb₀⟩ := hK.exists_bound_of_continuousOn hδ.continuous.continuousOn
  let b : ℝ := max b₀ 1
  have hb : 0 < b := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hδb (p : U) : δ (p : M) ≤ b := by
    have hh := hb₀ (p : M) (subset_closure p.property)
    rw [Real.norm_eq_abs] at hh
    exact (le_abs_self _).trans (hh.trans (le_max_left _ _))
  have hext (i : t) : ∃ d : plateauCoordinateSpace → ℝ,
      ContDiff ℝ ∞ d ∧ EqOn d (fun z => δ (c i z)) (B i) := by
    have hs : ContDiffOn ℝ ∞ (fun z => δ (c i z)) (c i).source :=
      contMDiffOn_iff_contDiffOn.mp (hδ.comp_contMDiffOn (hc i))
    obtain ⟨d, hd, _, heq⟩ := exists_contDiff_compactSupport_extension_on_isCompact
      (hBc i) (c i).open_source (hBs i) hs
    exact ⟨d, hd, heq.self_of_nhdsSet⟩
  choose d hd hdEq using hext
  let P : t → Set (plateauCoordinateSpace × ℝ) := fun i => A i ×ˢ Icc 0 b
  let Z : Set plateauCoordinateSpace := Metric.closedBall 0 3
  have hPc (i : t) : IsCompact (P i) := (hAc i).prod isCompact_Icc
  have hZc : IsCompact Z := isCompact_closedBall _ _
  have hsmall (i : t) := exists_uniform_small_scale_normalizedFactor (hd i) (hPc i) hZc
  choose η hη hηR using hsmall
  let η₀ : ℝ := Finset.univ.inf' Finset.univ_nonempty η
  have hη₀ : 0 < η₀ := (Finset.lt_inf'_iff _).mpr (fun i _ => hη i)
  let dilation : ℝ := min (η₀ / 2) (ε / (6 * b))
  have hdilation : 0 < dilation := lt_min (by positivity) (by positivity)
  have hdilationη (i : t) : |dilation| < η i := by
    rw [abs_of_pos hdilation]
    have hiη : η₀ ≤ η i := Finset.inf'_le _ (Finset.mem_univ i)
    have hdilation₀ : dilation ≤ η₀ / 2 := min_le_left _ _
    linarith
  have hdilationb : dilation * b * 3 ≤ ε := by
    have hh : dilation ≤ ε / (6 * b) := min_le_right _ _
    have hh' := (le_div_iff₀ (by positivity : 0 < 6 * b)).mp hh
    nlinarith
  have hR (i : t) (p) (hp : p ∈ P i) (z) (hz : z ∈ Z) :=
    hηR i dilation (hdilationη i) p hp z hz
  have hshift (i : t) (p) (hp : p ∈ P i) (z) (hz : z ∈ Z) :
      p.1 + (dilation * p.2) • z ∈ B i := by
    apply hbuffer i p.1 hp.1
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hdilation.le hp.2.1)]
    have hz' : ‖z‖ ≤ 3 := by simpa only [Z, Metric.mem_closedBall, dist_zero_right] using hz
    calc
      (dilation * p.2) * ‖z‖ ≤ (dilation * b) * 3 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hp.2.2 hdilation.le) hz'
          (norm_nonneg _) (mul_nonneg hdilation.le hb.le)
      _ ≤ ε := hdilationb
  let j : U → t := fun p => j₀ ⟨p, subset_closure p.property⟩
  let a : U → plateauCoordinateSpace := fun p => a₀ ⟨p, subset_closure p.property⟩
  have hca (p : U) : c (j p) (a p) = (p : M) := (hcenter _).1
  have ha (p : U) : a p ∈ A (j p) := (hcenter _).2
  let r : U → ℝ := fun p => δ (c (j p) (a p))
  have hr (p : U) : 0 < r p := by
    dsimp only [r]
    rw [hca]
    exact (hU p).1 p.property
  have hpar (p : U) : (a p, r p) ∈ P (j p) := by
    refine ⟨ha p, (hr p).le, ?_⟩
    simpa only [r, hca] using hδb p
  have hrd (p : U) : r p = d (j p) (a p) :=
    (hdEq (j p) (hAB (j p) (ha p))).symm
  have hfactor (p : U) (z) (hz : z ∈ Z) :
      δ (c (j p) (a p + (dilation * r p) • z)) =
        r p * normalizedFactor (d (j p)) dilation (a p) (r p) z := by
    have heq : d (j p) (a p + (dilation * r p) • z) =
        δ (c (j p) (a p + (dilation * r p) • z)) :=
      hdEq (j p) (hshift (j p) (a p, r p) (hpar p) z hz)
    exact heq.symm.trans
      (defining_function_eq_scale_mul_normalizedFactor (hd (j p)) dilation (a p) (r p) z (hrd p))
  let L (p : U) : plateauCoordinateSpace ≃L[ℝ] plateauCoordinateSpace :=
    (LinearEquiv.smulOfNeZero ℝ plateauCoordinateSpace (dilation * r p)
      (mul_ne_zero hdilation.ne' (hr p).ne')).toContinuousLinearEquiv
  let ψ (p : U) := liftedAffineChart (c (j p)) U hne (a p) (L p)
  have hsource (p : U) : Z ⊆ (ψ p).source := by
    intro z hz
    change z ∈ (affineChart (c (j p)) (a p) (L p)).source ∩
      (affineChart (c (j p)) (a p) (L p)) ⁻¹' (U.openPartialHomeomorphSubtypeCoe hne).target
    constructor
    · rw [affineChart_source]
      change a p + (dilation * r p) • z ∈ (c (j p)).source
      exact hBs (j p) (hshift (j p) (a p, r p) (hpar p) z hz)
    · rw [TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target]
      change c (j p) (a p + (dilation * r p) • z) ∈ U
      apply (hU _).2
      rw [hfactor p z hz]
      exact mul_pos (hr p) (lt_trans (by norm_num) (hR (j p) _ (hpar p) z hz).1)
  have hzero : (0 : plateauCoordinateSpace) ∈ Z := Metric.mem_closedBall_self (by norm_num)
  have hψzero (p : U) : ψ p 0 = p := by
    apply Subtype.ext
    rw [liftedAffineChart_val _ U hne _ _ (hsource p hzero)]
    simpa only [map_zero, add_zero] using hca p
  have hψsmooth (p : U) := liftedAffineChart_smooth
    (c (j p)) (hc (j p)) (hi (j p)) U hne (a p) (L p)
  have hcoeff (p : U) (z) (hz : z ∈ Z) (v w : plateauCoordinateSpace) :
      G.inner (ψ p z)
        (mfderiv 𝓘(ℝ, plateauCoordinateSpace) 𝓘(ℝ, E) (ψ p) z v)
        (mfderiv 𝓘(ℝ, plateauCoordinateSpace) 𝓘(ℝ, E) (ψ p) z w) =
      (dilation ^ 2 / (normalizedFactor (d (j p)) dilation (a p) (r p) z) ^ 2) *
        g.inner (c (j p) (a p + (dilation * r p) • z))
          (mfderiv 𝓘(ℝ, plateauCoordinateSpace) 𝓘(ℝ, E) (c (j p))
            (a p + (dilation * r p) • z) v)
          (mfderiv 𝓘(ℝ, plateauCoordinateSpace) 𝓘(ℝ, E) (c (j p))
            (a p + (dilation * r p) • z) w) := by
    apply completedMetric_rescaled_chart_coefficient
      (c (j p)) U hne g G δ hG (a p) dilation hdilation.ne' (hr p).ne' z (hsource p hz)
    · exact (((hc (j p)) _ (hBs (j p) (hshift (j p) _ (hpar p) z hz))).contMDiffAt
        ((c (j p)).open_source.mem_nhds (hBs (j p) (hshift (j p) _ (hpar p) z hz)))).mdifferentiableAt
          (by simp)
    · exact (lt_trans (by norm_num) (hR (j p) _ (hpar p) z hz).1).ne'
    · exact hfactor p z hz
  have hscale (p : U) (z) (hz : z ∈ Z) :
      dilation ^ 2 / 3 ≤ dilation ^ 2 / (normalizedFactor (d (j p)) dilation (a p) (r p) z) ^ 2 ∧
      dilation ^ 2 / (normalizedFactor (d (j p)) dilation (a p) (r p) z) ^ 2 ≤ 4 * dilation ^ 2 := by
    let q := normalizedFactor (d (j p)) dilation (a p) (r p) z
    have hq := hR (j p) _ (hpar p) z hz
    have hqpos : 0 < q := lt_trans (by norm_num) hq.1
    have hq2 : (1 / 4 : ℝ) ≤ q ^ 2 ∧ q ^ 2 ≤ 3 := by
      have hlo := mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 1 / 2) hq.1.le
      have hhi := mul_self_le_mul_self hqpos.le hq.2.le
      constructor <;> nlinarith
    change dilation ^ 2 / 3 ≤ dilation ^ 2 / q ^ 2 ∧ dilation ^ 2 / q ^ 2 ≤ 4 * dilation ^ 2
    constructor
    · apply (le_div_iff₀ (sq_pos_of_pos hqpos)).2
      nlinarith [mul_le_mul_of_nonneg_left hq2.2 (sq_nonneg dilation)]
    · apply (div_le_iff₀ (sq_pos_of_pos hqpos)).2
      nlinarith [mul_le_mul_of_nonneg_left hq2.1 (sq_nonneg dilation)]
  have hcube : plateauClosedCube ⊆ Z := cube_subset_ball_three.trans Metric.ball_subset_closedBall
  refine ⟨dilation ^ 2 / 3 * m, 4 * dilation ^ 2 * M₀, by positivity, ?_, ψ, ?_, ?_⟩
  · have hM : 0 < M₀ := hm.trans_le hmM
    calc
      dilation ^ 2 / 3 * m ≤ dilation ^ 2 / 3 * M₀ :=
        mul_le_mul_of_nonneg_left hmM (by positivity)
      _ ≤ 4 * dilation ^ 2 * M₀ :=
        mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg dilation]) hM.le
  · intro p
    refine ⟨hcube.trans (hsource p), hψzero p, (hψsmooth p).1, (hψsmooth p).2, ?_⟩
    intro z hz v
    have hzZ : z ∈ Z := hcube (fun i => (hz i).le)
    rw [hcoeff p z hzZ v v]
    have hq := hell (j p) _ (hshift (j p) _ (hpar p) z hzZ) v
    have hs := hscale p z hzZ
    have hgnonneg := metric_inner_self_nonneg g
      (c (j p) (a p + (dilation * r p) • z))
      (mfderiv 𝓘(ℝ, plateauCoordinateSpace) 𝓘(ℝ, E) (c (j p))
        (a p + (dilation * r p) • z) v)
    constructor
    · calc
        dilation ^ 2 / 3 * m * ‖v‖ ^ 2 = (dilation ^ 2 / 3) * (m * ‖v‖ ^ 2) := by ring
        _ ≤ _ := mul_le_mul hs.1 hq.1 (mul_nonneg hm.le (sq_nonneg _))
          (div_nonneg (sq_nonneg _) (sq_nonneg _))
    · calc
        _ ≤ (4 * dilation ^ 2) * (M₀ * ‖v‖ ^ 2) :=
          mul_le_mul hs.2 hq.2 hgnonneg (by positivity)
        _ = _ := by ring
  · intro k
    let v : Fin 3 → plateauCoordinateSpace := fun i => EuclideanSpace.single i (1 : ℝ)
    have hbnd (i : t) (u w : Fin 3) := bound_normalized_coeff
      (hd i) (c i).open_source (contDiffOn_sourceMetricPairing g (c i).open_source (hc i) (v u) (v w))
      (hPc i) hZc dilation (fun p hp z hz => hBs i (hshift i p hp z hz))
      (fun p hp z hz => lt_trans (by norm_num) (hR i p hp z hz).1) k
    choose C hC hbound using hbnd
    let C₀ : ℝ := ∑ i, ∑ u, ∑ w, C i u w
    have hC₀ : 0 ≤ C₀ := Finset.sum_nonneg (fun i _ =>
      Finset.sum_nonneg (fun u _ => Finset.sum_nonneg (fun w _ => hC i u w)))
    have hCC (i : t) (u w : Fin 3) : C i u w ≤ C₀ :=
      (Finset.single_le_sum (fun q _ => hC i u q) (Finset.mem_univ w)).trans
        ((Finset.single_le_sum (fun q _ => Finset.sum_nonneg (fun s _ => hC i q s))
          (Finset.mem_univ u)).trans
          (Finset.single_le_sum (fun q _ => Finset.sum_nonneg (fun s _ =>
            Finset.sum_nonneg (fun z _ => hC q s z))) (Finset.mem_univ i)))
    refine ⟨C₀, hC₀, ?_⟩
    intro p u w z hz
    have hzb : z ∈ Metric.ball (0 : plateauCoordinateSpace) 3 :=
      cube_subset_ball_three (fun i => (hz i).le)
    have heq : plateauChartCoefficient G (ψ p) u w =ᶠ[𝓝 z]
        (fun y => dilation ^ 2 / (normalizedFactor (d (j p)) dilation (a p) (r p) y) ^ 2 *
          g.inner (c (j p) (a p + (dilation * r p) • y))
            (mfderiv 𝓘(ℝ, plateauCoordinateSpace) 𝓘(ℝ, E) (c (j p))
              (a p + (dilation * r p) • y) (v u))
            (mfderiv 𝓘(ℝ, plateauCoordinateSpace) 𝓘(ℝ, E) (c (j p))
              (a p + (dilation * r p) • y) (v w))) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hzb] with y hy
      exact hcoeff p y (Metric.ball_subset_closedBall hy) (v u) (v w)
    rw [(heq.iteratedFDeriv ℝ k).eq_of_nhds]
    exact (hbound (j p) u w (a p, r p) (hpar p) z
      (Metric.ball_subset_closedBall hzb)).trans (hCC (j p) u w)

end DifferentialGeometry.Geometry.Metric.PositiveDomainCharts
