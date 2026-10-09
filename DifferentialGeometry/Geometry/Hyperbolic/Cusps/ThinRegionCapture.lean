import DifferentialGeometry.Geometry.Hyperbolic.Cusps.ApproximationThinness
import DifferentialGeometry.Geometry.Hyperbolic.ThinRegionMembership
import DifferentialGeometry.Geometry.Metric.Approximation.Inverse

noncomputable section

open scoped Manifold ContDiff Bundle ENNReal Topology
open DifferentialGeometry.Integral.Measure (riemannianVolumeMeasure)

namespace DifferentialGeometry.Geometry.Hyperbolic

open Riemannian.Topology (UniversalCover SemilocallySimplyConnectedSpace
  manifold_semilocallySimplyConnectedSpace)
open OrbifoldThinRegions (thinRegion)

local notation "E₃" => EuclideanSpace ℝ (Fin 3)
local notation "H₃" => DifferentialGeometry.Hyperbolic.HUpper 3
local notation "B₃" => HyperbolicBoundary.BoundaryH 3

private instance : NeZero (Module.finrank ℝ E₃) := ⟨by simp⟩

private theorem isConnected_union_balls_of_isConnected_range
    {E Y A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace Y] [ChartedSpace H Y] [IsManifold I ∞ Y]
    (h : SmoothRiemannianMetric I Y) (f : A → Y) (hf : IsConnected (Set.range f)) :
    IsConnected (⋃ c, riemannianBallOf h (f c) 2) := by
  have hm (c : A) : f c ∈ riemannianBallOf h (f c) 2 := by
    change riemannianEDistOf h (f c) (f c) < ENNReal.ofReal 2
    simp [riemannianEDistOf_self]
  have hK (c : A) : IsConnected (Set.range f ∪ riemannianBallOf h (f c) 2) :=
    hf.union ⟨f c, ⟨c, rfl⟩, hm c⟩ (isPathConnected_riemannianBallOf h (f c) (by norm_num)).isConnected
  obtain ⟨y, c₀, rfl⟩ := hf.nonempty
  have hcommon : (⋂ c, (Set.range f ∪ riemannianBallOf h (f c) 2)).Nonempty :=
    ⟨f c₀, Set.mem_iInter.mpr (fun _ => Or.inl ⟨c₀, rfl⟩)⟩
  have hconn : IsConnected (⋃ c, (Set.range f ∪ riemannianBallOf h (f c) 2)) :=
    ⟨⟨f c₀, Set.mem_iUnion.mpr ⟨c₀, Or.inl ⟨c₀, rfl⟩⟩⟩,
      isPreconnected_iUnion hcommon (fun c => (hK c).isPreconnected)⟩
  have he : (⋃ c, (Set.range f ∪ riemannianBallOf h (f c) 2)) =
      ⋃ c, riemannianBallOf h (f c) 2 := by
    ext y
    constructor
    · intro hy
      obtain ⟨c, hc⟩ := Set.mem_iUnion.mp hy
      rcases hc with ⟨d, rfl⟩ | hc
      · exact Set.mem_iUnion.mpr ⟨d, hm d⟩
      · exact Set.mem_iUnion.mpr ⟨c, hc⟩
    · intro hy
      obtain ⟨c, hc⟩ := Set.mem_iUnion.mp hy
      exact Set.mem_iUnion.mpr ⟨c, Or.inr hc⟩
  exact he ▸ hconn

private theorem nearby_closedBall_subset
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (g : SmoothRiemannianMetric I M) {p q : M} {r : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) (hq : q ∈ riemannianClosedBallOf g p 4) :
    riemannianClosedBallOf g q (4 * r) ⊆ riemannianClosedBallOf g p 9 := by
  intro z hz
  have hd := (riemannianEDistOf_triangle g p q z).trans (add_le_add hq hz)
  rw [← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 4) (by positivity)] at hd
  exact hd.trans (ENNReal.ofReal_le_ofReal (by linarith))

universe u v

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E₃ H} [I.Boundaryless]
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
  (g : SmoothRiemannianMetric I M) (hg : RiemannianMetricComplete (I := I) g)
  (κ : ℝ) (hκ : κ < 0) (x₀ : M)
  (hsec : ∀ (x : M) (X Y : TangentSpace I x),
    Curvature.metricRm04StandardAt g x X Y Y X =
      κ * (g.inner x X X * g.inner x Y Y - g.inner x X Y * g.inner x X Y))

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_depth_ball_subset_image_interior_thinRegion_of_metric_approximation :
    letI : Inhabited M := ⟨x₀⟩
    letI : LocallyPathConnectedSpace H := I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
    letI : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace H M
    letI : SemilocallySimplyConnectedSpace M := manifold_semilocallySimplyConnectedSpace (I := I)
    letI : SecondCountableTopology H := ModelWithCorners.secondCountableTopology I
    letI : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
    let gN := scaleMetric (-κ) (neg_pos.mpr hκ) g
    let ĝ := UniversalCover.liftedMetric (I := I) gN
    let hĝ : RiemannianMetricComplete ĝ := UniversalCover.liftedMetric_complete gN (hg.scaleMetric _ _)
    letI : IsManifold I 1 (UniversalCover M) :=
      IsManifold.of_le (I := I) (M := UniversalCover M) (n := ∞) (by decide)
    letI : TopologicalSpace.MetrizableSpace (UniversalCover M) := Manifold.metrizableSpace I (UniversalCover M)
    letI : T3Space (UniversalCover M) := inferInstance
    letI : Bundle.RiemannianBundle (TangentSpace I : UniversalCover M → Type _) := ⟨ĝ.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E₃ (TangentSpace I : UniversalCover M → Type _) :=
      ⟨⟨ĝ.inner, ĝ.contMDiff.continuous, by intro x v w; rfl⟩⟩
    letI : EMetricSpace (UniversalCover M) := EMetricSpace.ofRiemannianMetric I (UniversalCover M)
    letI : PseudoEMetricSpace (UniversalCover M) :=
      (EMetricSpace.ofRiemannianMetric I (UniversalCover M)).toPseudoEMetricSpace
    letI : CompleteSpace (UniversalCover M) := hĝ.complete
    ∀ (i : E₃ ≃ₗᵢ[ℝ] TangentSpace I (UniversalCover.basePoint (X := M))),
      let ρs := normalizedUniversalCoverDeckRepresentation g hg κ hκ x₀ hsec i
      let σs := (Hyperboloid.projectiveOrthogonalGroupEquiv 2 :
        (Hyperboloid E₃ ≃ᵢ Hyperboloid E₃) →* ProjectiveOrthogonalGroup.PO 3 1).comp ρs
      ∀ {r : ℝ} (D : CuspTruncation.FiniteCuspTruncation (by decide : 1 ≤ 3) σs.range r),
        let e (ξ : D.centers) := normalizedUniversalCoverCuspCylinderMap g hg κ hκ x₀ hsec i D ξ
        (∀ ξ : D.centers, riemannianVolumeMeasure I M g (Set.range (e ξ)) ≠ ⊤) →
        ∀ (r : ℝ), 0 < r → r ≤ 1 → ∃ T : ℝ, 0 ≤ T ∧
        ∀ (N : Type v) [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
          [T2Space N] [SigmaCompactSpace N] [ConnectedSpace N]
          (h : SmoothRiemannianMetric I N) (hh : RiemannianMetricComplete h) (y₀ : N)
          (hcurv : ∀ (q : N) (v w : TangentSpace I q),
            Curvature.metricRm04StandardAt h q v w w v =
              (-1 / 4 : ℝ) * (h.inner q v v * h.inner q w w - h.inner q v w * h.inner q v w)),
    letI : Inhabited N := ⟨y₀⟩
    letI : LocallyPathConnectedSpace H := I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
    letI : LocallyPathConnectedSpace N := ChartedSpace.locallyPathConnectedSpace H N
    letI : SemilocallySimplyConnectedSpace N := manifold_semilocallySimplyConnectedSpace (I := I)
    letI : SecondCountableTopology H := ModelWithCorners.secondCountableTopology I
    letI : SecondCountableTopology N := ChartedSpace.secondCountable_of_sigmaCompact H N
    let gN := scaleMetric (-(-1 / 4 : ℝ)) (neg_pos.mpr (by norm_num : (-1 / 4 : ℝ) < 0)) h
    let ĝ := UniversalCover.liftedMetric (I := I) gN
    let hĝ : RiemannianMetricComplete ĝ := UniversalCover.liftedMetric_complete gN (hh.scaleMetric _ _)
    letI : IsManifold I 1 (UniversalCover N) :=
      IsManifold.of_le (I := I) (M := UniversalCover N) (n := ∞) (by decide)
    letI : TopologicalSpace.MetrizableSpace (UniversalCover N) := Manifold.metrizableSpace I (UniversalCover N)
    letI : T3Space (UniversalCover N) := inferInstance
    letI : Bundle.RiemannianBundle (TangentSpace I : UniversalCover N → Type _) := ⟨ĝ.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E₃ (TangentSpace I : UniversalCover N → Type _) :=
      ⟨⟨ĝ.inner, ĝ.contMDiff.continuous, by intro x v w; rfl⟩⟩
    letI : EMetricSpace (UniversalCover N) := EMetricSpace.ofRiemannianMetric I (UniversalCover N)
    letI : PseudoEMetricSpace (UniversalCover N) :=
      (EMetricSpace.ofRiemannianMetric I (UniversalCover N)).toPseudoEMetricSpace
    letI : CompleteSpace (UniversalCover N) := hĝ.complete
    ∀ (j : E₃ ≃ₗᵢ[ℝ] TangentSpace I (UniversalCover.basePoint (X := N))),
      let ρt := normalizedUniversalCoverDeckRepresentation h hh (-1 / 4) (by norm_num) y₀ hcurv j
      let σt := (Hyperboloid.projectiveOrthogonalGroupEquiv 2 :
        (Hyperboloid E₃ ≃ᵢ Hyperboloid E₃) →* ProjectiveOrthogonalGroup.PO 3 1).comp ρt
      let pH := normalizedUniversalCoverProjection h hh (-1 / 4) (by norm_num) y₀ hcurv j
      ∀ (εMargulis : ℝ), r < εMargulis →
        (∀ z : H₃, BoundaryStabilizer.ElementaryGeometry (by decide : 1 ≤ 3)
          (Margulis.smallSubgroup (by decide : 1 ≤ 3) σt.range εMargulis z)) →
        ∀ (Φ : PartialDiffeomorph I I M N ∞) (k : ℕ) (ε : ℝ), ε ≤ 1 / 2 →
        ∀ ξ : D.centers,
        let P := CuspCrossSections.endStabilizer (by decide : 1 ≤ 3) σs.range {ξ.val}
        letI := EquivariantMap.subAction (by decide : 1 ≤ 3) P
        let C := (Quotient.mk (MulAction.orbitRel P H₃)) '' Busemann.horosphere ξ.val (D.level ξ)
        ∀ t : Set.Ici (0 : ℝ), T ≤ t.val →
          (∀ c : C, DifferentialGeometry.PartialDiffeomorph.isMetricApproximationOn Φ
            (riemannianClosedBallOf g (e ξ (c, t)) 9) k ε g h) →
          ∃ S : Set B₃, ∀ c : C,
            riemannianBallOf h (Φ (e ξ (c, t))) 2 ⊆
              pH '' interior (thinRegion (by decide : 1 ≤ 3) σt.range r S) := by
  let _ : Inhabited M := ⟨x₀⟩
  let _ : LocallyPathConnectedSpace H := I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  let _ : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace H M
  let _ : SemilocallySimplyConnectedSpace M := manifold_semilocallySimplyConnectedSpace (I := I)
  let _ : SecondCountableTopology H := ModelWithCorners.secondCountableTopology I
  let _ : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
  let gN := scaleMetric (-κ) (neg_pos.mpr hκ) g
  let ĝ := UniversalCover.liftedMetric (I := I) gN
  let hĝ : RiemannianMetricComplete ĝ := UniversalCover.liftedMetric_complete gN (hg.scaleMetric _ _)
  let _ : IsManifold I 1 (UniversalCover M) :=
    IsManifold.of_le (I := I) (M := UniversalCover M) (n := ∞) (by decide)
  let _ : TopologicalSpace.MetrizableSpace (UniversalCover M) := Manifold.metrizableSpace I (UniversalCover M)
  let _ : T3Space (UniversalCover M) := inferInstance
  let _ : Bundle.RiemannianBundle (TangentSpace I : UniversalCover M → Type _) := ⟨ĝ.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E₃ (TangentSpace I : UniversalCover M → Type _) :=
    ⟨⟨ĝ.inner, ĝ.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let _ : EMetricSpace (UniversalCover M) := EMetricSpace.ofRiemannianMetric I (UniversalCover M)
  let _ : PseudoEMetricSpace (UniversalCover M) :=
    (EMetricSpace.ofRiemannianMetric I (UniversalCover M)).toPseudoEMetricSpace
  let _ : CompleteSpace (UniversalCover M) := hĝ.complete
  dsimp only
  intro i rSource D hfinite r hr hr1
  have hdeep := exists_depth_deck_displacement_lt_of_metric_approximation g hg κ hκ x₀ hsec i D hfinite r hr
  obtain ⟨T₀, hT₀, hthin⟩ := hdeep
  refine ⟨T₀ + Real.sqrt (-κ) * 5, add_nonneg hT₀ (mul_nonneg (Real.sqrt_nonneg _) (by norm_num)), ?_⟩
  intro N topN chartN smoothN t2N sigmaN connN h hh y₀ hcurv
  let _ : Inhabited N := ⟨y₀⟩
  let _ : LocallyPathConnectedSpace H := I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  let _ : LocallyPathConnectedSpace N := ChartedSpace.locallyPathConnectedSpace H N
  let _ : SemilocallySimplyConnectedSpace N := manifold_semilocallySimplyConnectedSpace (I := I)
  let _ : SecondCountableTopology H := ModelWithCorners.secondCountableTopology I
  let _ : SecondCountableTopology N := ChartedSpace.secondCountable_of_sigmaCompact H N
  let gN := scaleMetric (-(-1 / 4 : ℝ)) (neg_pos.mpr (by norm_num : (-1 / 4 : ℝ) < 0)) h
  let ĝ := UniversalCover.liftedMetric (I := I) gN
  let hĝ : RiemannianMetricComplete ĝ := UniversalCover.liftedMetric_complete gN (hh.scaleMetric _ _)
  let _ : IsManifold I 1 (UniversalCover N) :=
    IsManifold.of_le (I := I) (M := UniversalCover N) (n := ∞) (by decide)
  let _ : TopologicalSpace.MetrizableSpace (UniversalCover N) := Manifold.metrizableSpace I (UniversalCover N)
  let _ : T3Space (UniversalCover N) := inferInstance
  let _ : Bundle.RiemannianBundle (TangentSpace I : UniversalCover N → Type _) := ⟨ĝ.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E₃ (TangentSpace I : UniversalCover N → Type _) :=
    ⟨⟨ĝ.inner, ĝ.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let _ : EMetricSpace (UniversalCover N) := EMetricSpace.ofRiemannianMetric I (UniversalCover N)
  let _ : PseudoEMetricSpace (UniversalCover N) :=
    (EMetricSpace.ofRiemannianMetric I (UniversalCover N)).toPseudoEMetricSpace
  let _ : CompleteSpace (UniversalCover N) := hĝ.complete
  intro j εMargulis hrMargulis hgeom Φ k ε hε ξ t ht happrox
  let ρs := normalizedUniversalCoverDeckRepresentation g hg κ hκ x₀ hsec i
  let σs := (Hyperboloid.projectiveOrthogonalGroupEquiv 2 :
    (Hyperboloid E₃ ≃ᵢ Hyperboloid E₃) →* ProjectiveOrthogonalGroup.PO 3 1).comp ρs
  let P := CuspCrossSections.endStabilizer (by decide : 1 ≤ 3) σs.range {ξ.val}
  let _ := EquivariantMap.subAction (by decide : 1 ≤ 3) P
  let C := (Quotient.mk (MulAction.orbitRel P H₃)) '' Busemann.horosphere ξ.val (D.level ξ)
  let e := normalizedUniversalCoverCuspCylinderMap g hg κ hκ x₀ hsec i D ξ
  let f : C → N := fun c => Φ (e (c, t))
  let _ : ConnectedSpace C := isConnected_iff_connectedSpace.mp (D.isConnected_quotient_horosphere ξ)
  have hCsource (c : C) : e (c, t) ∈ Φ.source := by
    apply (happrox c).1
    change riemannianEDistOf g (e (c, t)) (e (c, t)) ≤ ENNReal.ofReal 9
    simp [riemannianEDistOf_self]
  have hslice : Continuous (fun c : C => e (c, t)) :=
    e.continuous.comp (continuous_id.prodMk continuous_const)
  have hf : Continuous f := by
    apply continuous_iff_continuousAt.mpr
    intro c
    have ha : ContinuousAt (Φ : M → N) (e (c,t)) :=
      (Φ.contMDiffOn_toFun.continuousOn (e (c,t)) (hCsource c)).continuousAt
        (Φ.open_source.mem_nhds (hCsource c))
    exact ha.comp (f := fun c : C => e (c,t)) hslice.continuousAt
  have hconn := isConnected_union_balls_of_isConnected_range h f (isConnected_range hf)
  have hones (c : C) (y : N) (hy : y ∈ riemannianBallOf h (f c) 2)
      (x : UniversalCover N) (hx : UniversalCover.proj x = y) :
      ∃ γ : FundamentalGroup N y₀, γ ≠ 1 ∧
        riemannianEDistOf (UniversalCover.liftedMetric (I := I)
          (scaleMetric (1 / 4) (by norm_num) h)) x (UniversalCover.deckDiffeo (I := I) γ x) < ENNReal.ofReal r := by
    have hcapture := DifferentialGeometry.PartialDiffeomorph.inverse_mem_closedBall_of_metric_approximation
      g h Φ (e (c,t)) (A := 2) (R := 9) (by norm_num) (by norm_num) (by linarith)
        (hg.closedEBall_isCompact (e (c,t)) 9) (happrox c) y
        (show y ∈ riemannianClosedBallOf h (f c) 2 from
          (show riemannianEDistOf h (f c) y < ENNReal.ofReal 2 from hy).le)
    let q := Φ.symm y
    have hq : q ∈ riemannianClosedBallOf g (e (c,t)) 4 := by
      simpa only [show (2 : ℝ) * 2 = 4 by norm_num] using hcapture.2.2
    have htail := riemannianClosedBallOf_normalizedUniversalCoverCuspCylinderMap_subset_tail
      g hg κ hκ x₀ hsec i D ξ c t T₀ 1 hT₀ zero_lt_one (by simpa only [mul_one] using ht)
    have htailq := htail (by simpa only [mul_one] using hq)
    obtain ⟨⟨c', t'⟩, ht', hpoint⟩ := htailq
    have hnear := nearby_closedBall_subset g hr hr1 hq
    have happq := (happrox c).mono hnear le_rfl le_rfl
    have happ' : DifferentialGeometry.PartialDiffeomorph.isMetricApproximationOn Φ
        (riemannianClosedBallOf g (e (c',t')) (4*r)) k ε g h := by
      exact (congrArg (fun z : M => DifferentialGeometry.PartialDiffeomorph.isMetricApproximationOn Φ
        (riemannianClosedBallOf g z (4*r)) k ε g h) hpoint).mpr happq
    have heq : UniversalCover.proj x = Φ (e (c',t')) :=
      hx.trans ((Φ.right_inv hcapture.1).symm.trans (congrArg Φ hpoint).symm)
    exact hthin N h hh y₀ hcurv Φ k ε hε ξ c' t' ht' happ' x heq
  have hresult := exists_subset_image_interior_thinRegion_of_isConnected_of_short_deck_displacement
    h hh (-1 / 4) (by norm_num) y₀ hcurv j r εMargulis hrMargulis hgeom
      (⋃ c, riemannianBallOf h (f c) 2) hconn
  dsimp only at hresult
  simp only [neg_div, neg_neg] at hresult
  have hshort : ∀ x : UniversalCover N, UniversalCover.proj x ∈ (⋃ c, riemannianBallOf h (f c) 2) →
      ∃ γ : FundamentalGroup N y₀, γ ≠ 1 ∧
        riemannianEDistOf (UniversalCover.liftedMetric (I := I)
          (scaleMetric (1 / 4) (by norm_num) h)) x (UniversalCover.deckDiffeo (I := I) γ x) < ENNReal.ofReal r := by
    intro x hx
    obtain ⟨c, hc⟩ := Set.mem_iUnion.mp hx
    exact hones c (UniversalCover.proj x) hc x rfl
  have hlabels := hresult hshort
  obtain ⟨S, hS⟩ := hlabels
  exact ⟨S, fun c => (Set.subset_iUnion (fun d => riemannianBallOf h (f d) 2) c).trans hS⟩

end DifferentialGeometry.Geometry.Hyperbolic
