import DifferentialGeometry.Geometry.Exponential.Intrinsic.Framed.BallChart
import DifferentialGeometry.Geometry.Exponential.MinimizingGeodesic
import DifferentialGeometry.Analysis.Calculus.Compactness.DiagonalSubsequence

section

set_option autoImplicit false

noncomputable section

open Bundle Set
open scoped Bundle Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

open Exponential

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [CompleteSpace E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  [T2Space (TangentBundle I M)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [PseudoEMetricSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

variable (g : SmoothRiemannianMetric I M)
variable (hEnorm : ∀ (x : M) (v : TangentSpace I x),
  ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))

omit [CompleteSpace E] [T2Space (TangentBundle I M)] in
theorem IntrinsicBallChart.mem_target_and_norm_symm
    (p : M) {r : Real} (c : IntrinsicBallChart (I := I) g hEnorm p r)
    {y : M} (hy : Manifold.riemannianEDist I p y < ENNReal.ofReal r) :
    y ∈ c.hom.target ∧ ‖c.hom.symm y‖ = (Manifold.riemannianEDist I p y).toReal := by
  have hyFin : Manifold.riemannianEDist I p y ≠ (⊤ : ENNReal) :=
    ne_of_lt (hy.trans ENNReal.ofReal_lt_top)
  obtain ⟨v, hvExp, hvLen⟩ :=
    hopf_rinow_expMapIntrinsic_surjective_minimizing_of_ne_top (I := I) g hEnorm p y hyFin
  let z : E := (normalFrame (I := I) g p).symm v
  have hzFrame : normalFrame (I := I) g p z = v :=
    (normalFrame (I := I) g p).apply_symm_apply v
  have hzNorm : ‖z‖ = Real.sqrt (g.inner p v v) := by
    have h := normalFrame_sqrt (I := I) g p z
    rw [hzFrame] at h
    exact h.symm
  have hzBall : z ∈ Metric.ball (0 : E) r := by
    rw [Metric.mem_ball, dist_zero_right, hzNorm, hvLen]
    exact (ENNReal.lt_ofReal_iff_toReal_lt hyFin).mp hy
  have hmap : c.hom z = y := by
    calc c.hom z = intrinsicFramedExp (I := I) g hEnorm p z := c.hom_eq hzBall
      _ = expMapIntrinsic (I := I) g hEnorm p (normalFrame (I := I) g p z) := by
        rw [intrinsicFrame_apply]
      _ = expMapIntrinsic (I := I) g hEnorm p v := by rw [hzFrame]
      _ = y := hvExp
  have hzSource : z ∈ c.hom.source := by rwa [c.source_eq]
  refine ⟨hmap ▸ c.hom.map_source hzSource, ?_⟩
  have hinv : c.hom.symm y = z := by
    rw [← hmap]
    exact c.hom.left_inv hzSource
  rw [hinv, hzNorm, hvLen]

omit [CompleteSpace E] [T2Space (TangentBundle I M)] in
theorem IntrinsicBallChart.target_eq_eball
    (p : M) {r : Real} (c : IntrinsicBallChart (I := I) g hEnorm p r) :
    c.hom.target = Metric.eball p (ENNReal.ofReal r) := by
  ext y
  constructor
  · intro hy
    rw [c.target_eq] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    exact intrinsicFrame_mem_eball (I := I) g hEnorm p
      (by simpa only [Metric.mem_ball, dist_zero_right] using hz)
  · intro hy
    apply (c.mem_target_and_norm_symm (I := I) g hEnorm p ?_).1
    rw [Metric.mem_eball'] at hy
    simpa only [IsRiemannianManifold.out (I := I)] using hy

end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

end

end

section

set_option autoImplicit false

noncomputable section

open Bundle Set Filter
open scoped Bundle Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [PseudoEMetricSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

variable (g : SmoothRiemannianMetric I M)
variable (hEnorm : ∀ (x : M) (v : TangentSpace I x),
  ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))

theorem IntrinsicBallChart.image_ball_eq_eball
    (p : M) {r s : Real} (c : IntrinsicBallChart (I := I) g hEnorm p r)
    (hsr : s ≤ r) :
    c.hom '' Metric.ball (0 : E) s = Metric.eball p (ENNReal.ofReal s) := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [c.hom_eq (Metric.ball_subset_ball hsr hz)]
    exact intrinsicFrame_mem_eball (I := I) g hEnorm p
      (by simpa only [Metric.mem_ball, dist_zero_right] using hz)
  · intro hy
    have hydist : Manifold.riemannianEDist I p y < ENNReal.ofReal s := by
      rw [Metric.mem_eball'] at hy
      simpa only [IsRiemannianManifold.out (I := I)] using hy
    obtain ⟨hytarget, hynorm⟩ := c.mem_target_and_norm_symm g hEnorm p
      (hydist.trans_le (ENNReal.ofReal_le_ofReal hsr))
    refine ⟨c.hom.symm y, ?_, c.hom.right_inv hytarget⟩
    rw [Metric.mem_ball, dist_zero_right, hynorm]
    exact (ENNReal.lt_ofReal_iff_toReal_lt
      (ne_of_lt (hydist.trans ENNReal.ofReal_lt_top))).mp hydist

theorem IntrinsicBallChart.transition_maps_to_ball_of_edist_add_le
    (p q : M) {r r' s t : Real}
    (c : IntrinsicBallChart (I := I) g hEnorm p r)
    (d : IntrinsicBallChart (I := I) g hEnorm q r')
    (hr : 0 < r) (hr' : 0 < r') (hsr : s ≤ r) (htr : t ≤ r')
    (hmargin : edist p q + ENNReal.ofReal s ≤ ENNReal.ofReal t) :
    Set.MapsTo ((c.toNormalBallChart g hEnorm p hr).transition
      (d.toNormalBallChart g hEnorm q hr'))
      (Metric.ball (0 : E) s) (Metric.ball (0 : E) t) := by
  intro z hz
  have hfin : edist p q ≠ (⊤ : ENNReal) :=
    ne_of_lt ((le_add_right (le_refl (edist p q))).trans_lt
      (hmargin.trans_lt ENNReal.ofReal_lt_top))
  have hcz : c.hom z ∈ Metric.eball p (ENNReal.ofReal s) := by
    rw [← c.image_ball_eq_eball g hEnorm p hsr]
    exact ⟨z, hz, rfl⟩
  have hdz : c.hom z ∈ d.hom '' Metric.ball (0 : E) t := by
    rw [d.image_ball_eq_eball g hEnorm q htr]
    exact Metric.eball_subset hmargin hfin hcz
  obtain ⟨w, hw, hmap⟩ := hdz
  change d.hom.symm (c.hom z) ∈ Metric.ball (0 : E) t
  rw [show c.hom z = d.hom w by exact hmap.symm]
  exact (d.hom.left_inv (by rw [d.source_eq]; exact Metric.ball_subset_ball htr hw)).symm ▸ hw

theorem IntrinsicBallChart.overlap_on_ball_of_edist_add_le
    (p q : M) {r r' s : Real}
    (c : IntrinsicBallChart (I := I) g hEnorm p r)
    (d : IntrinsicBallChart (I := I) g hEnorm q r')
    (hr : 0 < r) (hr' : 0 < r') (hsr : s ≤ r)
    (hmargin : edist p q + ENNReal.ofReal s ≤ ENNReal.ofReal r') :
    (c.toNormalBallChart g hEnorm p hr).OverlapOn
      (d.toNormalBallChart g hEnorm q hr') (Metric.ball (0 : E) s) := by
  intro z hz
  refine ⟨Metric.ball_subset_ball hsr hz, ?_⟩
  change c.hom z ∈ d.hom '' Metric.ball (0 : E) r'
  have hfin : edist p q ≠ (⊤ : ENNReal) :=
    ne_of_lt ((le_add_right (le_refl (edist p q))).trans_lt
      (hmargin.trans_lt ENNReal.ofReal_lt_top))
  rw [d.image_ball_eq_eball g hEnorm q le_rfl]
  apply Metric.eball_subset hmargin hfin
  rw [← c.image_ball_eq_eball g hEnorm p hsr]
  exact ⟨z, hz, rfl⟩

end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

end

end

section

namespace DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

open Bundle Filter Topology
open scoped Manifold ContDiff ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [PseudoEMetricSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

variable (g : SmoothRiemannianMetric I M)
variable (hEnorm : ∀ (x : M) (v : TangentSpace I x),
  ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))

theorem IntrinsicBallChart.disjoint_image_ball_of_add_le_edist
    (p q : M) {r r' a b : Real}
    (c : IntrinsicBallChart (I := I) g hEnorm p r)
    (d : IntrinsicBallChart (I := I) g hEnorm q r')
    (har : a ≤ r) (hbr : b ≤ r')
    (hmargin : ENNReal.ofReal a + ENNReal.ofReal b ≤ edist p q) :
    Disjoint (c.hom '' Metric.ball (0 : E) a)
      (d.hom '' Metric.ball (0 : E) b) := by
  rw [c.image_ball_eq_eball g hEnorm p har, d.image_ball_eq_eball g hEnorm q hbr]
  exact Metric.eball_disjoint hmargin

end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

namespace EMetric

open Filter Topology
open scoped ENNReal

theorem exists_subseq_eventually_edist_lt_or_ge
    {ι : Type*} [Finite ι] {M : ℕ → Type*} [∀ k, PseudoEMetricSpace (M k)]
    (c : ι → ∀ k, M k) (r : ℝ≥0∞) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧ ∃ near : ι → ι → Bool,
      ∀ᶠ k in atTop, ∀ i j,
        (near i j = true → edist (c i (phi k)) (c j (phi k)) < r) ∧
        (near i j = false → r ≤ edist (c i (phi k)) (c j (phi k))) := by
  classical
  obtain ⟨phi, hphi, h⟩ :=
    DifferentialGeometry.CheegerGromovCompactness.exists_subseq_eventually_eq
      (fun p : ι × ι => fun k => decide (edist (c p.1 k) (c p.2 k) < r))
  choose near hnear using h
  refine ⟨phi, hphi, fun i j => near (i, j), ?_⟩
  have htail : ∀ᶠ k in atTop, ∀ i j,
      decide (edist (c i (phi k)) (c j (phi k)) < r) = near (i, j) := by
    exact Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr fun j => hnear (i, j)
  filter_upwards [htail] with k hk
  intro i j
  constructor
  · intro hij
    have heq := (hk i j).trans hij
    exact of_decide_eq_true heq
  · intro hij
    have heq := (hk i j).trans hij
    exact le_of_not_gt (of_decide_eq_false heq)

end EMetric


end
