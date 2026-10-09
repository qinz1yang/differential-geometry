import DifferentialGeometry.Geometry.Collapse.SublevelCore.SoulSublevelType
import DifferentialGeometry.Geometry.Collapse.SublevelCore.DistanceBallIsotopy

/-!
# Consumer of LC38 (noncompact alternative): the distance ball is a closed disc bundle

LC38's last clause (master207A, A:21622): LC34 (`radial_distance_sublevel_isotopy`, which needs
`ε < 1/2`) gives a homeomorphism of the closed distance ball `B̄(p, ρ)` with the compact domain,
including its boundary and interior. Composed with the diffeomorphism of manifolds with boundary
of `lc38_noncompact_sublevel_diffeomorph`, the closed unit disc bundle is homeomorphic to
`B̄(p, ρ)`, its sphere bundle going onto the distance sphere and its open disc bundle onto the
open ball (`lc38_noncompact_distance_ball_homeomorph`). The boundary correspondence uses that
diffeomorphisms of manifolds with boundary preserve boundary points.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle Manifold
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Topology.Morse DifferentialGeometry.Manifold.RegularLevel
open DifferentialGeometry.Topology.VectorBundle
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Geometry.Operator

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

variable {EB F : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [FiniteDimensional ℝ EB] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners ℝ EB HB} [IB.Boundaryless]
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B] [IsManifold IB ∞ B] [CompactSpace B]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ b, NormedAddCommGroup (V b)] [∀ b, InnerProductSpace ℝ (V b)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V IB]
  [IsContMDiffRiemannianBundle IB ∞ F V]

/-- **LC38 with LC34: the closed distance ball is the closed unit disc bundle.** Under the LC38
packet hypotheses with the LC34 smoothing bound `ε < 1/2`, the closed unit disc bundle is
homeomorphic to `B̄(p, ρ)` for every `ρ ∈ [1/5, 2]`, the unit sphere bundle corresponding to the
distance sphere and the open disc bundle to the open ball. -/
theorem lc38_noncompact_distance_ball_homeomorph (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) {p : M} {η : M → ℝ} {ε : ℝ≥0} {e : ℝ}
    (hε : (ε : ℝ) < 1 / 2) (he : e < 1 / 40) (hclose : ∀ x, |η x - dist p x| < e)
    (hlip : LipschitzWith ε (fun x => η x - dist p x))
    {W : Set M} (hW : IsOpen W) (hCW : ∀ x, 1 / 10 ≤ dist p x → dist p x ≤ 10 → x ∈ W)
    (hηW : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ η W)
    (hgrad : ∀ x, 1 / 10 ≤ dist p x → dist p x ≤ 10 →
      (1 - (ε : ℝ)) ^ 2 ≤
        g.inner x (gradientFun (I := I) g η x) (gradientFun (I := I) g η x))
    {N : Type*} [TopologicalSpace N] [ChartedSpace H N]
    (j : PartialDiffeomorph I I N M ∞)
    (eN : PartialDiffeomorph (IB.prod 𝓘(ℝ, F)) I (TotalSpace F V) N ∞)
    (hdisc : {z : TotalSpace F V | ‖z.2‖ ≤ 1} ⊆ eN.source)
    (hDN : (eN : TotalSpace F V → N) '' {z | ‖z.2‖ ≤ 1} ⊆ j.source)
    (hAD : {x | η x ≤ 1 / 8} ⊆
      interior ((j : N → M) '' ((eN : TotalSpace F V → N) '' {z | ‖z.2‖ ≤ 1})))
    (hDb : (j : N → M) '' ((eN : TotalSpace F V → N) '' {z | ‖z.2‖ ≤ 1}) ⊆ {x | η x < 3})
    (hdef : ∀ q ∈ frontier ((j : N → M) '' ((eN : TotalSpace F V → N) '' {z | ‖z.2‖ ≤ 1})),
      ∃ U : Set M, IsOpen U ∧ q ∈ U ∧ ∃ f : M → ℝ,
        ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f U ∧
        ((j : N → M) '' ((eN : TotalSpace F V → N) '' {z | ‖z.2‖ ≤ 1})) ∩ U =
          {x | f x ≤ 0} ∩ U ∧
        0 < mvfderiv (I := I) f q
          ((g.inner q (gradientFun (I := I) g η q) (gradientFun (I := I) g η q))⁻¹ •
            gradientFun (I := I) g η q))
    {m : ℕ} (hd : Module.finrank ℝ (EB × F) = m + 1) (hE : Module.finrank ℝ E = m + 1)
    {ρ : ℝ} (hρ : ρ ∈ Icc (1 / 5 : ℝ) 2) :
    ∃ h : {z : TotalSpace F V // ‖z.2‖ ≤ 1} ≃ₜ Metric.closedBall p ρ,
      ∀ z, ((h z : M) ∈ Metric.sphere p ρ ↔ ‖z.1.2‖ = 1) ∧
        ((h z : M) ∈ Metric.ball p ρ ↔ ‖z.1.2‖ < 1) := by
  obtain ⟨f, hf, hr, hle, heq, -, Hs, -, -, -, -, hΦ⟩ :=
    lc38_noncompact_sublevel_diffeomorph g hEnorm (by linarith) he hclose hlip hW hCW hηW hgrad
      j eN hdisc hDN hAD hDb hdef hd hE hρ
  let I' := I.transContinuousLinearEquiv
    (ContinuousLinearEquiv.ofFinrankEq (hE.trans (Module.finrank_fin_fun ℝ).symm) :
      E ≃L[ℝ] MorseModel (m + 1))
  let _ := normClosedDiscBundleChartedSpace (IB := IB) (V := V) hd 1 one_pos
  have := normClosedDiscBundle_isManifold (IB := IB) (V := V) hd 1 one_pos
  let _ := sublevelChartedSpace I' hf hr
  have := sublevelIsManifold I' hf hr
  obtain ⟨Φ, -⟩ := hΦ
  obtain ⟨G, -, -, -, -, -, hGball, hGsph, hGb⟩ :=
    radial_distance_sublevel_isotopy g hEnorm hε he hclose hlip hW hCW hηW hgrad hρ
  obtain ⟨gB, hgB, hgBeq⟩ :=
    (inferInstance : IsContMDiffRiemannianBundle IB ∞ F V).exists_contMDiff
  have : IsContinuousRiemannianBundle F V := ⟨gB, hgB.continuous, hgBeq⟩
  have : CompactSpace {z : TotalSpace F V // ‖z.2‖ ≤ 1} :=
    isCompact_iff_compactSpace.mp (isCompact_closedDiscBundle 1)
  have hmem : ∀ z, G 1 (Φ z) ∈ Metric.closedBall p ρ := by
    intro z
    rw [← hGball]
    exact ⟨Φ z, (hle _).1 (Φ z).2, rfl⟩
  let k : {z : TotalSpace F V // ‖z.2‖ ≤ 1} → Metric.closedBall p ρ :=
    fun z => ⟨G 1 (Φ z), hmem z⟩
  have hk : Continuous k :=
    ((G 1).continuous.comp (continuous_subtype_val.comp Φ.continuous)).subtype_mk _
  have hinj : Function.Injective k := by
    intro z w hzw
    have h1 : G 1 (Φ z) = G 1 (Φ w) := congrArg Subtype.val hzw
    exact Φ.injective (Subtype.ext ((G 1).injective h1))
  have hsurj : Function.Surjective k := by
    rintro ⟨y, hy⟩
    rw [← hGball] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    refine ⟨Φ.symm ⟨x, (hle x).2 hx⟩, Subtype.ext ?_⟩
    change G 1 (Φ (Φ.symm ⟨x, (hle x).2 hx⟩) : M) = G 1 x
    rw [Φ.apply_symm_apply]
  let h := hk.homeoOfEquivCompactToT2 (f := Equiv.ofBijective k ⟨hinj, hsurj⟩)
  have hbd : ∀ z : {z : TotalSpace F V // ‖z.2‖ ≤ 1}, η (Φ z : M) = ρ ↔ ‖z.1.2‖ = 1 := by
    intro z
    have hb : (morseModelWithCornersHalfSpace m).IsBoundaryPoint (Φ z) ↔ f (Φ z) = ρ :=
      sublevelBoundary_iff I' hf hr (Φ z)
    have hz : (morseModelWithCornersHalfSpace m).IsBoundaryPoint z ↔ ‖z.1.2‖ = 1 :=
      normClosedDiscBundle_boundary_iff (IB := IB) hd 1 one_pos z
    exact (heq _).symm.trans (hb.symm.trans
      (((Φ.isLocalDiffeomorph z).isBoundaryPoint_iff (by simp)).symm.trans hz))
  have himg : ∀ (T : Set M) (z : {z : TotalSpace F V // ‖z.2‖ ≤ 1}),
      G 1 (Φ z : M) ∈ G 1 '' T ↔ (Φ z : M) ∈ T := fun T z =>
    (G 1).injective.mem_set_image
  refine ⟨h, fun z => ⟨?_, ?_⟩⟩
  · change G 1 (Φ z : M) ∈ Metric.sphere p ρ ↔ _
    rw [← hGsph, himg]
    exact hbd z
  · change G 1 (Φ z : M) ∈ Metric.ball p ρ ↔ _
    rw [← hGb, himg]
    change η (Φ z : M) < ρ ↔ ‖z.1.2‖ < 1
    have hle1 : η (Φ z : M) ≤ ρ := (hle _).1 (Φ z).2
    rw [lt_iff_le_and_ne, lt_iff_le_and_ne]
    exact ⟨fun h' => ⟨z.2, fun h1 => h'.2 ((hbd z).2 h1)⟩,
      fun h' => ⟨hle1, fun h1 => h'.2 ((hbd z).1 h1)⟩⟩

end DifferentialGeometry.Geometry.Collapse
