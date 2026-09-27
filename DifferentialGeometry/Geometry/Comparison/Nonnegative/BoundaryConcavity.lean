import DifferentialGeometry.Geometry.Comparison.Soul.SoulConvexCore
import DifferentialGeometry.Geometry.Comparison.Busemann.Support.ApproximateSupportConvexity
import Mathlib.Topology.MetricSpace.HausdorffDistance

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open scoped Topology ContDiff Manifold NNReal
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.HopfRinow
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace DifferentialGeometry.Geometry.Topology

theorem concaveOn_of_linear_upper_support {D : Set ℝ} {f : ℝ → ℝ}
    (hD : Convex ℝ D) (hf : ContinuousOn f D)
    (hsupport : ∀ x ∈ interior D, ∃ c : ℝ, ∀ᶠ y in 𝓝 x, f y ≤ f x + c * (y - x)) :
    ConcaveOn ℝ D f := by
  have hconv : ConvexOn ℝ D (fun y => -f y) := by
    refine convexOn_of_approximate_lower_support hD hf.neg ?_
    intro x hx ε hε
    obtain ⟨c, hc⟩ := hsupport x hx
    refine ⟨fun y => -f x - c * (y - x) - ε / 4 * ((y - x) * (y - x)), ?_, by ring_nf, ?_, ?_⟩
    · exact ContDiff.contDiffAt (by fun_prop)
    · filter_upwards [hc] with y hy
      nlinarith [mul_self_nonneg (y - x), hε.le]
    · have hderiv : ∀ y : ℝ,
          HasDerivAt (fun z : ℝ => -f x - c * (z - x) - ε / 4 * ((z - x) * (z - x)))
            (-c - ε / 2 * (y - x)) y := by
        intro y
        have h0 : HasDerivAt (fun z : ℝ => z - x) 1 y := (hasDerivAt_id y).sub_const x
        have h1 : HasDerivAt (fun z : ℝ => c * (z - x)) c y := by
          simpa using h0.const_mul c
        have h2 : HasDerivAt (fun z : ℝ => (z - x) * (z - x)) (2 * (y - x)) y := by
          convert! h0.mul h0 using 1
          ring
        have h3 := ((hasDerivAt_const y (-f x)).sub h1).sub (h2.const_mul (ε / 4))
        convert! h3 using 1
        ring
      have hd1 : deriv (fun z : ℝ => -f x - c * (z - x) - ε / 4 * ((z - x) * (z - x)))
          = fun y : ℝ => -c - ε / 2 * (y - x) := funext fun y => (hderiv y).deriv
      rw [hd1]
      have hd2 : HasDerivAt (fun y : ℝ => -c - ε / 2 * (y - x)) (-(ε / 2)) x := by
        have h0 : HasDerivAt (fun z : ℝ => z - x) 1 x := (hasDerivAt_id x).sub_const x
        have h1 := (hasDerivAt_const x (-c)).sub (h0.const_mul (ε / 2))
        convert! h1 using 1
        ring
      rw [hd2.deriv]
      linarith
  have hneg := hconv.neg
  have heq : (-fun y => -f y) = f := by funext y; simp
  rwa [heq] at hneg

private theorem hinge_foot_start_aux {D a b t : ℝ} (ha : 0 < a) (hb : 0 < b)
    (ht : 0 < t) (hge : b ≤ D) (hab : a ≤ b * t)
    (hhinge : D ^ 2 ≤ a ^ 2 + b ^ 2 - 2 * a * b * t) : False := by
  nlinarith [mul_pos (mul_pos ha hb) ht, mul_self_le_mul_self hb.le hge,
    mul_le_mul_of_nonneg_left hab ha.le]

private theorem hinge_perp_aux {D a b t : ℝ} (ha : 0 < a) (hb : 0 < b) (ht : 0 < t)
    (hge : a ≤ D) (hba : b ≤ a * t)
    (hhinge : D ^ 2 ≤ a ^ 2 + b ^ 2 - 2 * a * b * t) : False := by
  nlinarith [mul_pos (mul_pos ha hb) ht, mul_self_le_mul_self ha.le hge,
    mul_le_mul_of_nonneg_left hba hb.le]


private theorem hinge_pyth_aux {h a b K : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hK : K ≤ 0)
    (hhinge : h ^ 2 ≤ a ^ 2 + b ^ 2 - 2 * a * b * -K) : h ^ 2 ≤ a ^ 2 + b ^ 2 := by
  nlinarith [mul_nonneg ha hb]


private theorem hinge_foot_lower_aux {a h c b : ℝ} (ha : 0 < a)
    (h1 : b ^ 2 ≤ a ^ 2 + h ^ 2 - 2 * a * h * c) (h2 : h ^ 2 ≤ a ^ 2 + b ^ 2) :
    h * c ≤ a := by
  nlinarith [ha]

private theorem sub_le_sub_mul_aux {l h c : ℝ} (hh : 0 ≤ h) (hc : c ≤ 1) :
    l - h ≤ l - h * c := by nlinarith

private theorem infDist_support_aux {A D n c y s : ℝ} (h : A ≤ D - n * (y - s) * c) :
    A ≤ D + -(n * c) * (y - s) := by linarith

private theorem infDist_support_aux' {A D n c y s : ℝ}
    (h : A ≤ D - n * (s - y) * (-1 * c)) : A ≤ D + -(n * c) * (y - s) := by linarith

private theorem superlevel_aux {t A D F α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hsum : α + β = 1) (hA : t ≤ A) (hD : t ≤ D) (hkey : α * A + β * D ≤ F) :
    t ≤ F := by
  have h1 : 0 ≤ α * (A - t) := mul_nonneg hα (sub_nonneg.2 hA)
  have h2 : 0 ≤ β * (D - t) := mul_nonneg hβ (sub_nonneg.2 hD)
  have h3 : α * t + β * t = t := by linear_combination t * hsum
  linarith

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [ConnectedSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [ConnectedSpace M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)] in
private theorem boundary_toReal_eq_dist (p q : M) :
    (riemannianEDist I p q).toReal = dist p q := by
  rw [← IsRiemannianManifold.out (I := I), edist_dist,
    ENNReal.toReal_ofReal dist_nonneg]

def HasSupportingHalfSpaces (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (C B : Set M) : Prop :=
  ∀ q ∈ C \ B, ∀ u : TangentSpace I q, g.inner q u u = 1 →
    intrinsicGeodesic (I := I) g hEnorm q u (Metric.infDist q B) ∈ B →
    ∀ v : TangentSpace I
        (intrinsicGeodesic (I := I) g hEnorm q u (Metric.infDist q B)),
      0 ≤ g.inner (intrinsicGeodesic (I := I) g hEnorm q u (Metric.infDist q B)) v
          (curveVelocity (I := I) (intrinsicGeodesic (I := I) g hEnorm q u)
            (Metric.infDist q B)) →
      ∀ᶠ s in 𝓝[>] (0 : ℝ),
        expMapIntrinsic (I := I) g hEnorm
            (intrinsicGeodesic (I := I) g hEnorm q u (Metric.infDist q B)) (s • v)
          ∉ C \ B

def HasOrthogonalBoundaryShift (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (C B : Set M) : Prop :=
  ∀ x ∈ C \ B, ∃ ρ : ℝ, 0 < ρ ∧ ∀ y ∈ C \ B, dist x y < ρ →
    ∀ u w : TangentSpace I y, g.inner y u u = 1 → g.inner y w w = 1 →
      g.inner y u w = 0 →
      intrinsicGeodesic (I := I) g hEnorm y u (Metric.infDist y B) ∈ B →
      ∀ h : ℝ, 0 ≤ h → h < ρ →
        Metric.infDist (intrinsicGeodesic (I := I) g hEnorm y w h) B
          ≤ Metric.infDist y B

def HasOpenCore (g : SmoothRiemannianMetric I M) (C B : Set M) : Prop :=
  ∀ {γ : ℝ → M} {a b : ℝ}, a ≤ b →
    Geodesic.IsGeodesicOn (I := I) g γ (Icc a b) → ContinuousOn γ (Icc a b) →
    MapsTo γ (Icc a b) C → (∃ t ∈ Icc a b, γ t ∉ B) → ∀ t ∈ Ioo a b, γ t ∉ B

omit [ConnectedSpace M] in
private theorem dist_intrinsicGeodesic_le
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (v : TangentSpace I p) {s t : ℝ} (hst : s ≤ t) :
    dist (intrinsicGeodesic (I := I) g hEnorm p v s)
        (intrinsicGeodesic (I := I) g hEnorm p v t)
      ≤ Real.sqrt (g.inner p v v) * (t - s) := by
  have h := intrinsicGeodesic_riemannianEDist_le (I := I) g hEnorm p v hst
  rw [← boundary_toReal_eq_dist (I := I)]
  refine (ENNReal.toReal_mono ENNReal.ofReal_ne_top h).trans ?_
  rw [ENNReal.toReal_ofReal (mul_nonneg (Real.sqrt_nonneg _) (by linarith))]

omit [ConnectedSpace M] in
private theorem infDist_intrinsicGeodesic_of_minimizing
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {B : Set M} {x : M} {u : TangentSpace I x} (hu : g.inner x u u = 1)
    (hmem : intrinsicGeodesic (I := I) g hEnorm x u (Metric.infDist x B) ∈ B)
    {t : ℝ} (ht0 : 0 ≤ t) (htl : t ≤ Metric.infDist x B) :
    dist x (intrinsicGeodesic (I := I) g hEnorm x u t) = t ∧
      Metric.infDist (intrinsicGeodesic (I := I) g hEnorm x u t) B
        = Metric.infDist x B - t := by
  set l : ℝ := Metric.infDist x B with hldef
  set τ : ℝ → M := intrinsicGeodesic (I := I) g hEnorm x u with hτdef
  have hsp : Real.sqrt (g.inner x u u) = 1 := by rw [hu, Real.sqrt_one]
  have hτ0 : τ 0 = x := intrinsicGeodesic_zero (I := I) g hEnorm x u
  have hl0 : 0 ≤ l := Metric.infDist_nonneg
  have h1 : dist x (τ t) ≤ t := by
    have h := dist_intrinsicGeodesic_le (I := I) g hEnorm x u ht0
    rw [← hτdef, hτ0, hsp, one_mul, sub_zero] at h
    exact h
  have h2 : dist (τ t) (τ l) ≤ l - t := by
    have h := dist_intrinsicGeodesic_le (I := I) g hEnorm x u htl
    rw [← hτdef, hsp, one_mul] at h
    exact h
  have h3 : dist x (τ l) ≤ l := by
    have h := dist_intrinsicGeodesic_le (I := I) g hEnorm x u hl0
    rw [← hτdef, hτ0, hsp, one_mul, sub_zero] at h
    exact h
  have h4 : l ≤ dist x (τ l) := Metric.infDist_le_dist_of_mem hmem
  have h5 : dist x (τ l) ≤ dist x (τ t) + dist (τ t) (τ l) := dist_triangle _ _ _
  have hxt : dist x (τ t) = t := by linarith
  have htl' : dist (τ t) (τ l) = l - t := by linarith
  refine ⟨hxt, le_antisymm ?_ ?_⟩
  · have := Metric.infDist_le_dist_of_mem (x := τ t) hmem
    linarith [this, htl'.le, htl'.ge]
  · have h6 : Metric.infDist x B ≤ Metric.infDist (τ t) B + dist x (τ t) :=
      Metric.infDist_le_infDist_add_dist
    rw [hxt] at h6
    linarith

omit [ConnectedSpace M] in
private theorem exists_unit_direction_to_boundary
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {B : Set M} (hB : IsClosed B) (hBne : B.Nonempty) {x : M} (hx : x ∉ B) :
    0 < Metric.infDist x B ∧ ∃ u : TangentSpace I x, g.inner x u u = 1 ∧
      intrinsicGeodesic (I := I) g hEnorm x u (Metric.infDist x B) ∈ B := by
  have hproper : ProperSpace M := ⟨soul_isCompact_closedBall (I := I) g hEnorm⟩
  obtain ⟨z, hz, hdist⟩ := hB.exists_infDist_eq_dist hBne x
  have hpos : 0 < dist x z := by
    rcases eq_or_lt_of_le (dist_nonneg : (0 : ℝ) ≤ dist x z) with h | h
    · exact absurd (by rw [dist_eq_zero.1 h.symm]; exact hz) hx
    · exact h
  obtain ⟨u, hu, huz⟩ := soul_unit_minimizing_initial (I := I) g hEnorm x z hpos
  refine ⟨by rw [hdist]; exact hpos, u, hu, ?_⟩
  rw [hdist, huz]
  exact hz


private theorem hinge_dist_sq
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hsec : ∀ y : M, metricRm04At (I := I) g y ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    (o : M) (u v : TangentSpace I o) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hu : g.inner o u u = 1) (hv : g.inner o v v = 1)
    (hmin : dist o (intrinsicGeodesic (I := I) g hEnorm o u a) = a) :
    dist (intrinsicGeodesic (I := I) g hEnorm o u a)
        (intrinsicGeodesic (I := I) g hEnorm o v b) ^ 2
      ≤ a ^ 2 + b ^ 2 - 2 * a * b * g.inner o u v := by
  have hmin' : (riemannianEDist I o
      (intrinsicGeodesic (I := I) g hEnorm o u a)).toReal = a := by
    rw [boundary_toReal_eq_dist (I := I)]; exact hmin
  have h := complete_hinge_sq (I := I) g hEnorm hsec o u v a b ha hb hu hv hmin'
  rwa [boundary_toReal_eq_dist (I := I)] at h

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [ConnectedSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M] [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)] in
private theorem gInner_smul_left (g : SmoothRiemannianMetric I M) (p : M)
    (r : ℝ) (a b : TangentSpace I p) : g.inner p (r • a) b = r * g.inner p a b := by
  rw [(g.inner p).map_smul r a, smul_apply, smul_eq_mul]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [ConnectedSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M] [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)] in
private theorem gInner_smul_right (g : SmoothRiemannianMetric I M) (p : M)
    (r : ℝ) (a b : TangentSpace I p) : g.inner p a (r • b) = r * g.inner p a b := by
  rw [(g.inner p a).map_smul r b, smul_eq_mul]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [ConnectedSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M] [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)] in
private theorem gInner_sub_left (g : SmoothRiemannianMetric I M) (p : M)
    (a b d : TangentSpace I p) :
    g.inner p (a - b) d = g.inner p a d - g.inner p b d := by
  rw [ContinuousLinearMap.map_sub₂]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [ConnectedSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M] [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)] in
private theorem gInner_sub_right (g : SmoothRiemannianMetric I M) (p : M)
    (a b d : TangentSpace I p) :
    g.inner p a (b - d) = g.inner p a b - g.inner p a d := by
  rw [(g.inner p a).map_sub]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [ConnectedSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M] [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)] in
private theorem gInner_unit_sq_le_one (g : SmoothRiemannianMetric I M) {p : M}
    {a b : TangentSpace I p} (ha : g.inner p a a = 1) (hb : g.inner p b b = 1) :
    g.inner p a b ^ 2 ≤ 1 := by
  have hexp : g.inner p (b - g.inner p a b • a) (b - g.inner p a b • a)
      = 1 - g.inner p a b ^ 2 := by
    simp only [gInner_sub_left, gInner_sub_right, gInner_smul_left, gInner_smul_right,
      ha, hb, g.symm p b a]
    ring
  have hnn := gInner_self_nonneg (I := I) g p (b - g.inner p a b • a)
  rw [hexp] at hnn
  linarith

omit [ConnectedSpace M] in
private theorem exists_radial_dist_radius
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ {u : TangentSpace I p}, g.inner p u u = 1 →
      ∀ {δ : ℝ}, 0 ≤ δ → δ < ρ →
        dist p (intrinsicGeodesic (I := I) g hEnorm p u δ) = δ := by
  obtain ⟨ρ, hρ, hradial⟩ := radial_riemannianEDist_eq_of_small (I := I) g hEnorm p
  refine ⟨ρ, hρ, ?_⟩
  intro u hu δ hδ0 hδ
  have h := hradial hu hδ0 hδ
  rw [expMapIntrinsic_def, intrinsicGeodesic_smul] at h
  rw [← boundary_toReal_eq_dist (I := I), h, ENNReal.toReal_ofReal hδ0]

private theorem infDist_step_of_inner_nonpos
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hsec : ∀ y : M, metricRm04At (I := I) g y ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    {C B : Set M} (hshift : HasOrthogonalBoundaryShift (I := I) g hEnorm C B)
    {x : M} (hx : x ∈ C \ B)
    {u : TangentSpace I x} (hu : g.inner x u u = 1)
    (hmem : intrinsicGeodesic (I := I) g hEnorm x u (Metric.infDist x B) ∈ B)
    {e : TangentSpace I x} (he : g.inner x e e = 1)
    (hcnonpos : g.inner x u e ≤ 0) :
    ∀ᶠ h in 𝓝[>] (0 : ℝ),
      Metric.infDist (intrinsicGeodesic (I := I) g hEnorm x e h) B
        ≤ Metric.infDist x B - h * g.inner x u e := by
  obtain ⟨ρ₀, hρ₀, hshiftx⟩ := hshift x hx
  obtain ⟨ρ₁, hρ₁, hradx⟩ := exists_radial_dist_radius (I := I) g hEnorm x
  set c : ℝ := g.inner x u e with hcdef
  have hsmul₂ : ∀ (r : ℝ) (a b : TangentSpace I x),
      g.inner x (r • a) b = r * g.inner x a b := by
    intro r a b
    rw [(g.inner x).map_smul r a, smul_apply, smul_eq_mul]
  have hsmulr : ∀ (r : ℝ) (a b : TangentSpace I x),
      g.inner x a (r • b) = r * g.inner x a b := by
    intro r a b
    rw [(g.inner x a).map_smul r b, smul_eq_mul]
  have hsub₂ : ∀ (a b d : TangentSpace I x),
      g.inner x (a - b) d = g.inner x a d - g.inner x b d := by
    intro a b d
    rw [ContinuousLinearMap.map_sub₂]
  have hsubr : ∀ (a b d : TangentSpace I x),
      g.inner x a (b - d) = g.inner x a b - g.inner x a d := by
    intro a b d
    rw [(g.inner x a).map_sub]
  have hue : g.inner x u e = c := hcdef.symm
  have heu : g.inner x e u = c := (g.symm x e u).trans hcdef.symm
  have hw2 : g.inner x (e - c • u) (e - c • u) = 1 - c ^ 2 := by
    simp only [hsub₂, hsubr, hsmul₂, hsmulr, he, hu, hue, heu]
    ring
  have hc2 : c ^ 2 ≤ 1 := by
    have hnn := gInner_self_nonneg (I := I) g x (e - c • u)
    rw [hw2] at hnn
    linarith
  set n : ℝ := Real.sqrt (1 - c ^ 2) with hndef
  have hn0 : 0 ≤ n := Real.sqrt_nonneg _
  have hnsq : n ^ 2 = 1 - c ^ 2 := Real.sq_sqrt (by linarith)
  have hn1 : n ≤ 1 := by nlinarith [sq_nonneg c]
  rcases eq_or_lt_of_le hn0 with hnzero | hnpos
  · have hn0' : n = 0 := hnzero.symm
    have hcsq : c ^ 2 = 1 := by
      have h := hnsq
      rw [hn0'] at h
      linear_combination h
    have hfac : (c - 1) * (c + 1) = 0 := by linear_combination hcsq
    have hc1 : c = -1 := by
      rcases mul_eq_zero.1 hfac with h | h
      · linarith
      · linarith
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hh0 : (0 : ℝ) < h := hh
    have hdle : dist (intrinsicGeodesic (I := I) g hEnorm x e h) x ≤ h := by
      have hd := dist_intrinsicGeodesic_le (I := I) g hEnorm x e hh0.le
      rw [intrinsicGeodesic_zero (I := I) g hEnorm x e, he, Real.sqrt_one, one_mul,
        sub_zero] at hd
      rw [dist_comm]
      exact hd
    have htri := Metric.infDist_le_infDist_add_dist
      (x := intrinsicGeodesic (I := I) g hEnorm x e h) (y := x) (s := B)
    rw [hc1]
    linarith
  · have hne : n ≠ 0 := ne_of_gt hnpos
    set w : TangentSpace I x := n⁻¹ • (e - c • u) with hwdef
    have hw : g.inner x w w = 1 := by
      rw [hwdef, gInner_smul_self (I := I) g x, hw2, ← hnsq, inv_pow,
        inv_mul_cancel₀ (pow_ne_zero 2 hne)]
    have huw : g.inner x u w = 0 := by
      rw [hwdef, hsmulr, hsubr, hsmulr, hu, hue]
      ring
    have hwe : g.inner x w e = n := by
      have haux : g.inner x (e - c • u) e = n ^ 2 := by
        rw [hsub₂, hsmul₂, he, hue, hnsq]
        ring
      rw [hwdef, hsmul₂, haux, pow_two, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
    have hδ : 0 < min ρ₀ ρ₁ := lt_min hρ₀ hρ₁
    filter_upwards [Ioo_mem_nhdsGT hδ] with h hh
    obtain ⟨hh0, hhδ⟩ := hh
    have hhρ₀ : h < ρ₀ := lt_of_lt_of_le hhδ (min_le_left _ _)
    have hhρ₁ : h < ρ₁ := lt_of_lt_of_le hhδ (min_le_right _ _)
    have hhn0 : 0 < h * n := mul_pos hh0 hnpos
    have hhnle : h * n ≤ h := by nlinarith
    have hshiftbound :
        Metric.infDist (intrinsicGeodesic (I := I) g hEnorm x w (h * n)) B
          ≤ Metric.infDist x B :=
      hshiftx x hx (by simpa using hρ₀) u w hu hw huw hmem (h * n) hhn0.le
        (lt_of_le_of_lt hhnle hhρ₀)
    have hminw : dist x (intrinsicGeodesic (I := I) g hEnorm x w (h * n)) = h * n :=
      hradx hw hhn0.le (lt_of_le_of_lt hhnle hhρ₁)
    have hhinge := hinge_dist_sq (I := I) g hEnorm hsec x w e hhn0 hh0 hw he hminw
    rw [hwe] at hhinge
    have hnn : (0 : ℝ) ≤ h * (-c) := mul_nonneg hh0.le (by linarith)
    have heqq : (h * n) ^ 2 + h ^ 2 - 2 * (h * n) * h * n = (h * (-c)) ^ 2 := by
      linear_combination (-h ^ 2) * hnsq
    have hsq : dist (intrinsicGeodesic (I := I) g hEnorm x w (h * n))
        (intrinsicGeodesic (I := I) g hEnorm x e h) ^ 2 ≤ (h * (-c)) ^ 2 :=
      hhinge.trans_eq heqq
    have hdle : dist (intrinsicGeodesic (I := I) g hEnorm x w (h * n))
        (intrinsicGeodesic (I := I) g hEnorm x e h) ≤ h * (-c) := by
      have hroot := Real.sqrt_le_sqrt hsq
      rwa [Real.sqrt_sq dist_nonneg, Real.sqrt_sq hnn] at hroot
    have hfinal := Metric.infDist_le_infDist_add_dist
      (x := intrinsicGeodesic (I := I) g hEnorm x e h)
      (y := intrinsicGeodesic (I := I) g hEnorm x w (h * n)) (s := B)
    rw [dist_comm] at hfinal
    linarith

private theorem exists_perp_unit_of_local_min
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hsec : ∀ y : M, metricRm04At (I := I) g y ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    {y q : M} {u : TangentSpace I y} (hu : g.inner y u u = 1)
    (hpos : 0 < dist y q)
    (hloc : ∀ᶠ s in 𝓝 (0 : ℝ),
      dist q y ≤ dist q (intrinsicGeodesic (I := I) g hEnorm y u s)) :
    ∃ w : TangentSpace I y, g.inner y w w = 1 ∧ g.inner y u w = 0 ∧
      intrinsicGeodesic (I := I) g hEnorm y w (dist y q) = q := by
  obtain ⟨W, hW, hWq⟩ := soul_unit_minimizing_initial (I := I) g hEnorm y q hpos
  set d : ℝ := dist y q with hddef
  refine ⟨W, hW, ?_, hWq⟩
  have hsmulr : ∀ (r : ℝ) (a b : TangentSpace I y),
      g.inner y a (r • b) = r * g.inner y a b := by
    intro r a b
    rw [(g.inner y a).map_smul r b, smul_eq_mul]
  have hmin : dist y (intrinsicGeodesic (I := I) g hEnorm y W d) = d := by rw [hWq]
  have hqy : dist q y = d := by rw [hddef, dist_comm]
  obtain ⟨δ, hδ, hδloc⟩ := Metric.eventually_nhds_iff.1 hloc
  have key : ∀ v : TangentSpace I y, g.inner y v v = 1 →
      (∀ s : ℝ, 0 < s → s < δ →
        dist q y ≤ dist q (intrinsicGeodesic (I := I) g hEnorm y v s)) →
      g.inner y W v ≤ 0 := by
    intro v hv hcond
    by_contra hcon
    rw [not_le] at hcon
    set s : ℝ := min (δ / 2) (d * g.inner y W v) with hsdef
    have hs0 : 0 < s := lt_min (by linarith) (mul_pos hpos hcon)
    have hsδ : s < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hsdk : s ≤ d * g.inner y W v := min_le_right _ _
    have hhinge := hinge_dist_sq (I := I) g hEnorm hsec y W v hpos hs0 hW hv hmin
    rw [hWq] at hhinge
    have hge := hcond s hs0 hsδ
    have hsq : d ^ 2 ≤ dist q (intrinsicGeodesic (I := I) g hEnorm y v s) ^ 2 := by
      have h1 : d ≤ dist q (intrinsicGeodesic (I := I) g hEnorm y v s) := by
        rw [← hqy]; exact hge
      nlinarith [hpos.le, h1]
    have h2 : 2 * d * s * g.inner y W v ≤ s ^ 2 := by nlinarith [hhinge, hsq]
    have h3 : s ^ 2 ≤ s * (d * g.inner y W v) := by nlinarith [hsdk, hs0.le]
    nlinarith [mul_pos (mul_pos hpos hs0) hcon]
  have hpos1 : g.inner y W u ≤ 0 := by
    refine key u hu fun s hs0 hsδ => hδloc ?_
    rw [Real.dist_eq, sub_zero, abs_of_pos hs0]
    exact hsδ
  have hneg1 : g.inner y W ((-1 : ℝ) • u) ≤ 0 := by
    refine key ((-1 : ℝ) • u) ?_ fun s hs0 hsδ => ?_
    · rw [gInner_smul_self (I := I) g y, hu]
      norm_num
    · have hgeo : intrinsicGeodesic (I := I) g hEnorm y ((-1 : ℝ) • u) s
          = intrinsicGeodesic (I := I) g hEnorm y u (-s) := by
        rw [intrinsicGeo_smul_apply (I := I) g hEnorm y u (-1) s]
        norm_num
      rw [hgeo]
      refine hδloc ?_
      rw [Real.dist_eq, sub_zero, abs_of_neg (neg_neg_iff_pos.mpr hs0), neg_neg]
      exact hsδ
  rw [hsmulr] at hneg1
  have hzero : g.inner y W u = 0 := by linarith
  rw [g.symm y u W]
  exact hzero

private theorem infDist_step_of_inner_pos
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hsec : ∀ y : M, metricRm04At (I := I) g y ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    {C B : Set M} (hconv : IsTotallyConvex (I := I) g C) (hBC : B ⊆ C)
    (hshift : HasOrthogonalBoundaryShift (I := I) g hEnorm C B)
    {x : M} (hx : x ∈ C \ B)
    {u : TangentSpace I x} (hu : g.inner x u u = 1)
    (hmem : intrinsicGeodesic (I := I) g hEnorm x u (Metric.infDist x B) ∈ B)
    {e : TangentSpace I x} (he : g.inner x e e = 1)
    (hcpos : 0 < g.inner x u e) :
    ∀ᶠ h in 𝓝[>] (0 : ℝ),
      Metric.infDist (intrinsicGeodesic (I := I) g hEnorm x e h) B
        ≤ Metric.infDist x B - h * g.inner x u e := by
  have hlpos : 0 < Metric.infDist x B := by
    rcases eq_or_lt_of_le (Metric.infDist_nonneg (x := x) (s := B)) with hzero | hposl
    · exfalso
      apply hx.2
      rw [← hzero, intrinsicGeodesic_zero (I := I) g hEnorm x u] at hmem
      exact hmem
    · exact hposl
  have hc1 : g.inner x u e ≤ 1 := by
    have h := gInner_unit_sq_le_one (I := I) g hu he
    nlinarith
  obtain ⟨ρ₀, hρ₀, hshiftx⟩ := hshift x hx
  obtain ⟨ρ₁, hρ₁, hradx⟩ := exists_radial_dist_radius (I := I) g hEnorm x
  set l : ℝ := Metric.infDist x B with hldef
  set c : ℝ := g.inner x u e with hcdef
  set τ : ℝ → M := intrinsicGeodesic (I := I) g hEnorm x u with hτdef
  have hτ0 : τ 0 = x := intrinsicGeodesic_zero (I := I) g hEnorm x u
  have hτcont : Continuous τ := intrinsicGeodesic_continuous (I := I) g hEnorm x u
  have hτfacts : ∀ t : ℝ, 0 ≤ t → t ≤ l →
      dist x (τ t) = t ∧ Metric.infDist (τ t) B = l - t := fun t ht0 htl =>
    infDist_intrinsicGeodesic_of_minimizing (I := I) g hEnorm hu hmem ht0 htl
  have hτC : ∀ t ∈ Icc (0 : ℝ) l, τ t ∈ C := by
    have h0 : intrinsicGeodesic (I := I) g hEnorm x u 0 ∈ C := by
      rw [intrinsicGeodesic_zero (I := I) g hEnorm x u]
      exact hx.1
    have hlc : intrinsicGeodesic (I := I) g hEnorm x u l ∈ C := hBC hmem
    exact fun t ht => hconv hlpos.le
      ((intrinsicGeodesic_isGeodesic (I := I) g hEnorm x u).isGeodesicOn _)
      hτcont.continuousOn h0 hlc ht
  have hτshift : ∀ t₀ s : ℝ, intrinsicGeodesic (I := I) g hEnorm (τ t₀)
      (curveVelocity (I := I) τ t₀) s = τ (s + t₀) := fun t₀ s =>
    (congrFun (intrinsicGeodesic_continuation (I := I) g hEnorm x u t₀) s).symm
  have hτvel : ∀ t₀ : ℝ, g.inner (τ t₀) (curveVelocity (I := I) τ t₀)
      (curveVelocity (I := I) τ t₀) = 1 := fun t₀ =>
    (intrinsicGeodesic_speedSq_eq (I := I) g hEnorm x u t₀).trans hu
  have hδpos : 0 < min (min (ρ₀ / 4) ρ₁) (l / 4) :=
    lt_min (lt_min (by linarith) hρ₁) (by linarith)
  filter_upwards [Ioo_mem_nhdsGT hδpos] with h hh
  obtain ⟨hh0, hhδ⟩ := hh
  have hhρ₀ : h < ρ₀ / 4 := lt_of_lt_of_le hhδ ((min_le_left _ _).trans (min_le_left _ _))
  have hhρ₁ : h < ρ₁ := lt_of_lt_of_le hhδ ((min_le_left _ _).trans (min_le_right _ _))
  have hhl : h < l / 4 := lt_of_lt_of_le hhδ (min_le_right _ _)
  set z : M := intrinsicGeodesic (I := I) g hEnorm x e h with hzdef
  have hxz : dist x z = h := hradx he hh0.le hhρ₁
  have hcontf : ContinuousOn (fun t => dist z (τ t)) (Icc 0 l) :=
    (continuous_const.dist hτcont).continuousOn
  obtain ⟨t₀, ht₀mem, ht₀min⟩ :=
    isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hlpos.le) hcontf
  have ht₀0 : 0 ≤ t₀ := ht₀mem.1
  have ht₀l : t₀ ≤ l := ht₀mem.2
  have hxt₀ : dist x (τ t₀) = t₀ := (hτfacts t₀ ht₀0 ht₀l).1
  have hψt₀ : Metric.infDist (τ t₀) B = l - t₀ := (hτfacts t₀ ht₀0 ht₀l).2
  set r : ℝ := dist z (τ t₀) with hrdef
  have hrnn : 0 ≤ r := by rw [hrdef]; exact dist_nonneg
  have hmin0 : dist z (τ t₀) ≤ dist z (τ 0) := ht₀min ⟨le_rfl, hlpos.le⟩
  have hzτ0 : dist z (τ 0) = h := by rw [hτ0, dist_comm]; exact hxz
  have hr_le_h : r ≤ h := by rw [hrdef]; exact hmin0.trans hzτ0.le
  have ht₀_le : t₀ ≤ 2 * h := by
    have htri : dist x (τ t₀) ≤ dist x z + dist z (τ t₀) := dist_triangle _ _ _
    rw [hxt₀, hxz] at htri
    linarith
  have ht₀pos : 0 < t₀ := by
    rcases eq_or_lt_of_le ht₀0 with hzero | hposi
    · exfalso
      have hr_eq : r = h := by rw [hrdef, ← hzero]; exact hzτ0
      obtain ⟨s, hs⟩ : ∃ s : ℝ, s = min l (h * c) := ⟨_, rfl⟩
      have hspos : 0 < s := by rw [hs]; exact lt_min hlpos (mul_pos hh0 hcpos)
      have hsl : s ≤ l := by rw [hs]; exact min_le_left _ _
      have hshc : s ≤ h * c := by rw [hs]; exact min_le_right _ _
      have hminu : dist x (τ s) = s := (hτfacts s hspos.le hsl).1
      have hhinge : dist (τ s) z ^ 2 ≤ s ^ 2 + h ^ 2 - 2 * s * h * c :=
        hinge_dist_sq (I := I) g hEnorm hsec x u e hspos hh0 hu he hminu
      rw [dist_comm (τ s) z] at hhinge
      have hmins : r ≤ dist z (τ s) := by rw [hrdef]; exact ht₀min ⟨hspos.le, hsl⟩
      have hge : h ≤ dist z (τ s) := hr_eq ▸ hmins
      exact hinge_foot_start_aux hspos hh0 hcpos hge hshc hhinge
    · exact hposi
  have ht₀lt : t₀ < l := by linarith
  rcases eq_or_lt_of_le hrnn with hr0 | hrpos
  · have hzeq : z = τ t₀ := by
      have hd0 : dist z (τ t₀) = 0 := by rw [← hrdef]; exact hr0.symm
      exact dist_eq_zero.1 hd0
    have ht₀h : t₀ = h := by
      have hxz' := hxz
      rw [hzeq, hxt₀] at hxz'
      exact hxz'
    rw [hzeq, hψt₀, ht₀h]
    exact sub_le_sub_mul_aux hh0.le hc1
  · have hrz : 0 < dist (τ t₀) z := by rw [dist_comm, ← hrdef]; exact hrpos
    have hdrz : dist (τ t₀) z = r := by rw [dist_comm, ← hrdef]
    obtain ⟨W, hW, hWz⟩ := soul_unit_minimizing_initial (I := I) g hEnorm (τ t₀) z hrz
    rw [hdrz] at hWz
    have hminW : dist (τ t₀) (intrinsicGeodesic (I := I) g hEnorm (τ t₀) W r) = r := by
      rw [hWz]; exact hdrz
    have hWcv : g.inner (τ t₀) W (curveVelocity (I := I) τ t₀) ≤ 0 := by
      by_contra hcon
      rw [not_le] at hcon
      obtain ⟨s, hs⟩ : ∃ s : ℝ, s = min ((l - t₀) / 2)
          (r * g.inner (τ t₀) W (curveVelocity (I := I) τ t₀)) := ⟨_, rfl⟩
      have hs0 : 0 < s := by
        rw [hs]; exact lt_min (by linarith) (mul_pos hrpos hcon)
      have hsl : s ≤ (l - t₀) / 2 := by rw [hs]; exact min_le_left _ _
      have hsr : s ≤ r * g.inner (τ t₀) W (curveVelocity (I := I) τ t₀) := by
        rw [hs]; exact min_le_right _ _
      have hhinge : dist (intrinsicGeodesic (I := I) g hEnorm (τ t₀) W r)
          (intrinsicGeodesic (I := I) g hEnorm (τ t₀) (curveVelocity (I := I) τ t₀) s) ^ 2
            ≤ r ^ 2 + s ^ 2
              - 2 * r * s * g.inner (τ t₀) W (curveVelocity (I := I) τ t₀) :=
        hinge_dist_sq (I := I) g hEnorm hsec (τ t₀) W (curveVelocity (I := I) τ t₀)
          hrpos hs0 hW (hτvel t₀) hminW
      rw [hWz, hτshift t₀ s] at hhinge
      have hge : r ≤ dist z (τ (s + t₀)) := by
        rw [hrdef]
        exact ht₀min ⟨by linarith, by linarith⟩
      exact hinge_perp_aux hrpos hs0 hcon hge hsr hhinge
    have hnegcv : g.inner (τ t₀) ((-1 : ℝ) • curveVelocity (I := I) τ t₀)
        ((-1 : ℝ) • curveVelocity (I := I) τ t₀) = 1 := by
      rw [gInner_smul_self (I := I) g (τ t₀), hτvel t₀]
      norm_num
    have hbackeq : intrinsicGeodesic (I := I) g hEnorm (τ t₀)
        ((-1 : ℝ) • curveVelocity (I := I) τ t₀) t₀ = x := by
      rw [intrinsicGeo_smul_apply (I := I) g hEnorm (τ t₀) (curveVelocity (I := I) τ t₀) (-1) t₀,
        hτshift t₀ (-1 * t₀), show (-1 : ℝ) * t₀ + t₀ = 0 by ring, hτ0]
    have hminback : dist (τ t₀) (intrinsicGeodesic (I := I) g hEnorm (τ t₀)
        ((-1 : ℝ) • curveVelocity (I := I) τ t₀) t₀) = t₀ := by
      rw [hbackeq, dist_comm]; exact hxt₀
    have hhinge2 : dist x z ^ 2 ≤ t₀ ^ 2 + r ^ 2
        - 2 * t₀ * r * g.inner (τ t₀) ((-1 : ℝ) • curveVelocity (I := I) τ t₀) W := by
      have hraw := hinge_dist_sq (I := I) g hEnorm hsec (τ t₀)
        ((-1 : ℝ) • curveVelocity (I := I) τ t₀) W ht₀pos hrpos hnegcv hW hminback
      rwa [hbackeq, hWz] at hraw
    have hinner2 : g.inner (τ t₀) ((-1 : ℝ) • curveVelocity (I := I) τ t₀) W
        = -g.inner (τ t₀) W (curveVelocity (I := I) τ t₀) := by
      rw [gInner_smul_left, g.symm (τ t₀) (curveVelocity (I := I) τ t₀) W]
      ring
    rw [hinner2, hxz] at hhinge2
    have hpyth : h ^ 2 ≤ t₀ ^ 2 + r ^ 2 :=
      hinge_pyth_aux ht₀pos.le hrpos.le hWcv hhinge2
    have hhinge1 : dist (τ t₀) z ^ 2 ≤ t₀ ^ 2 + h ^ 2 - 2 * t₀ * h * c :=
      hinge_dist_sq (I := I) g hEnorm hsec x u e ht₀pos hh0 hu he hxt₀
    rw [hdrz] at hhinge1
    have ht₀ge : h * c ≤ t₀ := hinge_foot_lower_aux ht₀pos hhinge1 hpyth
    have hτt₀mem : τ t₀ ∈ C \ B := by
      refine ⟨hτC t₀ ⟨ht₀0, ht₀l⟩, fun hb => ?_⟩
      have hzero : Metric.infDist (τ t₀) B = 0 := Metric.infDist_zero_of_mem hb
      rw [hψt₀] at hzero
      linarith
    have hloc : ∀ᶠ s in 𝓝 (0 : ℝ),
        dist z (τ t₀) ≤ dist z (intrinsicGeodesic (I := I) g hEnorm (τ t₀)
          (curveVelocity (I := I) τ t₀) s) := by
      filter_upwards [Ioo_mem_nhds (by linarith : -t₀ < (0 : ℝ))
        (by linarith : (0 : ℝ) < l - t₀)] with s hs
      rw [hτshift t₀ s]
      exact ht₀min ⟨by linarith [hs.1], by linarith [hs.2]⟩
    obtain ⟨w, hw, hperp, hwz⟩ :=
      exists_perp_unit_of_local_min (I := I) g hEnorm hsec (hτvel t₀) hrz hloc
    rw [hdrz] at hwz
    have hmemB : intrinsicGeodesic (I := I) g hEnorm (τ t₀)
        (curveVelocity (I := I) τ t₀) (Metric.infDist (τ t₀) B) ∈ B := by
      rw [hψt₀, hτshift t₀ (l - t₀), show l - t₀ + t₀ = l by ring]
      exact hmem
    have hshiftres :
        Metric.infDist (intrinsicGeodesic (I := I) g hEnorm (τ t₀) w r) B
          ≤ Metric.infDist (τ t₀) B :=
      hshiftx (τ t₀) hτt₀mem (by rw [hxt₀]; linarith)
        (curveVelocity (I := I) τ t₀) w (hτvel t₀) hw hperp hmemB r hrnn
        (by linarith)
    rw [hwz, hψt₀] at hshiftres
    linarith

private theorem infDist_step
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hsec : ∀ y : M, metricRm04At (I := I) g y ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    {C B : Set M} (hconv : IsTotallyConvex (I := I) g C) (hBC : B ⊆ C)
    (hshift : HasOrthogonalBoundaryShift (I := I) g hEnorm C B)
    {x : M} (hx : x ∈ C \ B)
    {u : TangentSpace I x} (hu : g.inner x u u = 1)
    (hmem : intrinsicGeodesic (I := I) g hEnorm x u (Metric.infDist x B) ∈ B)
    {e : TangentSpace I x} (he : g.inner x e e = 1) :
    ∀ᶠ h in 𝓝[>] (0 : ℝ),
      Metric.infDist (intrinsicGeodesic (I := I) g hEnorm x e h) B
        ≤ Metric.infDist x B - h * g.inner x u e := by
  rcases le_or_gt (g.inner x u e) 0 with hc | hc
  · exact infDist_step_of_inner_nonpos (I := I) g hEnorm hsec hshift hx hu hmem he hc
  · exact infDist_step_of_inner_pos (I := I) g hEnorm hsec hconv hBC hshift hx hu hmem he hc

omit [ConnectedSpace M] in
private theorem geodesicSegment_eqOn_intrinsic'
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {gamma : ℝ → M} {a b : ℝ} (hab : a < b)
    (hgeo : Geodesic.IsGeodesicOn (I := I) g gamma (Icc a b))
    (hcont : ContinuousOn gamma (Icc a b)) :
    ∃ (q : M) (v : TangentSpace I q) (r : ℝ),
      EqOn gamma (fun t => intrinsicGeodesic (I := I) g hEnorm q v (t - r)) (Icc a b) := by
  let r : ℝ := (a + b) / 2
  let delta : ℝ → M := fun t => gamma (t + r)
  let q : M := delta 0
  let v : TangentSpace I q := mfderiv 𝓘(ℝ, ℝ) I delta 0 1
  let eta := intrinsicGeodesic (I := I) g hEnorm q v
  have hrleft : a < r := by dsimp [r]; linarith
  have hrright : r < b := by dsimp [r]; linarith
  have hmap : MapsTo (fun t : ℝ => t + r) (Icc (a - r) (b - r)) (Icc a b) := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hdcont : ContinuousOn delta (Icc (a - r) (b - r)) :=
    hcont.comp (continuous_id.add continuous_const).continuousOn hmap
  have hdgeo : Geodesic.IsGeodesicOn (I := I) g delta (Ioo (a - r) (b - r)) := by
    have h := Geodesic.isGeodesicOn_comp_affine (I := I) (c := 1) (d := r) hgeo
    intro t ht
    simpa only [one_mul] using h t (by
      change 1 * t + r ∈ Icc a b
      simpa only [one_mul] using hmap (Ioo_subset_Icc_self ht))
  have heq : EqOn delta eta (Ioo (a - r) (b - r)) := by
    apply geo_eqOn_of_initial (I := I) g isOpen_Ioo isPreconnected_Ioo
      (show (0 : ℝ) ∈ Ioo (a - r) (b - r) by constructor <;> linarith)
      hdgeo ((intrinsicGeodesic_isGeodesic (I := I) g hEnorm q v).isGeodesicOn _)
      (hdcont.mono Ioo_subset_Icc_self)
      (intrinsicGeodesic_continuous g hEnorm q v).continuousOn
    · exact (intrinsicGeodesic_zero (I := I) g hEnorm q v).symm
    · exact (intrinsicGeodesic_mfderiv_zero (I := I) g hEnorm q v).symm
  have heqClosed : EqOn delta eta (Icc (a - r) (b - r)) := by
    apply heq.of_subset_closure hdcont
      (intrinsicGeodesic_continuous g hEnorm q v).continuousOn Ioo_subset_Icc_self
    rw [closure_Ioo (by linarith : a - r ≠ b - r)]
  refine ⟨q, v, r, ?_⟩
  intro t ht
  have ht' : t - r ∈ Icc (a - r) (b - r) := by constructor <;> linarith [ht.1, ht.2]
  simpa only [delta, sub_add_cancel] using heqClosed ht'

private theorem exists_local_upper_support
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hsec : ∀ y : M, metricRm04At (I := I) g y ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    {C B : Set M} (hconv : IsTotallyConvex (I := I) g C) (hB : IsClosed B)
    (hBne : B.Nonempty) (hBC : B ⊆ C)
    (hshift : HasOrthogonalBoundaryShift (I := I) g hEnorm C B)
    {γ : ℝ → M} {a b : ℝ} (hab : a < b)
    (hgeo : Geodesic.IsGeodesicOn (I := I) g γ (Icc a b))
    (hcont : ContinuousOn γ (Icc a b)) (hmaps : MapsTo γ (Icc a b) C)
    {s : ℝ} (hs : s ∈ Ioo a b) (hsB : γ s ∉ B) :
    ∃ c : ℝ, ∀ᶠ y in 𝓝 s,
      Metric.infDist (γ y) B ≤ Metric.infDist (γ s) B + c * (y - s) := by
  obtain ⟨q, v, r, heq⟩ := geodesicSegment_eqOn_intrinsic' (I := I) g hEnorm hab hgeo hcont
  set σ : ℝ → M := intrinsicGeodesic (I := I) g hEnorm q v with hσdef
  have hγeq : ∀ y ∈ Icc a b, γ y = σ (y - r) := fun y hy => heq hy
  have hγs : γ s = σ (s - r) := hγeq s (Ioo_subset_Icc_self hs)
  have hsB' : σ (s - r) ∉ B := by rw [← hγs]; exact hsB
  have hxC : σ (s - r) ∈ C := by
    rw [← hγs]; exact hmaps (Ioo_subset_Icc_self hs)
  have hx : σ (s - r) ∈ C \ B := ⟨hxC, hsB'⟩
  rw [hγs]
  rcases eq_or_lt_of_le (gInner_self_nonneg (I := I) g q v) with hv0 | hvpos
  · have hveq : v = 0 := by
      by_contra hne
      exact absurd hv0.symm (ne_of_gt (g.pos q v hne))
    have hσconst : ∀ t : ℝ, σ t = q := by
      intro t
      have hz := intrinsicGeo_smul_apply (I := I) g hEnorm q (0 : TangentSpace I q) 0 t
      rw [smul_zero, zero_mul, intrinsicGeodesic_zero] at hz
      rw [hσdef, hveq]
      exact hz
    refine ⟨0, ?_⟩
    filter_upwards [Ioo_mem_nhds hs.1 hs.2] with y hy
    rw [hγeq y (Ioo_subset_Icc_self hy), hσconst (y - r), hσconst (s - r)]
    simp
  · have hn : 0 < Real.sqrt (g.inner q v v) := Real.sqrt_pos.mpr hvpos
    obtain ⟨n, hndef⟩ : ∃ n : ℝ, n = Real.sqrt (g.inner q v v) := ⟨_, rfl⟩
    rw [← hndef] at hn
    have hnne : n ≠ 0 := ne_of_gt hn
    have hnsq : n ^ 2 = g.inner q v v := by rw [hndef]; exact Real.sq_sqrt hvpos.le
    have hcvsq : g.inner (σ (s - r)) (curveVelocity (I := I) σ (s - r))
        (curveVelocity (I := I) σ (s - r)) = n ^ 2 := by
      rw [hnsq]
      exact intrinsicGeodesic_speedSq_eq (I := I) g hEnorm q v (s - r)
    have he : g.inner (σ (s - r)) (n⁻¹ • curveVelocity (I := I) σ (s - r))
        (n⁻¹ • curveVelocity (I := I) σ (s - r)) = 1 := by
      rw [gInner_smul_self (I := I) g (σ (s - r)), hcvsq, inv_pow,
        inv_mul_cancel₀ (pow_ne_zero 2 hnne)]
    have hgeoe : ∀ t : ℝ, intrinsicGeodesic (I := I) g hEnorm (σ (s - r))
        (n⁻¹ • curveVelocity (I := I) σ (s - r)) t = σ (n⁻¹ * t + (s - r)) := by
      intro t
      rw [intrinsicGeo_smul_apply (I := I) g hEnorm (σ (s - r))
        (curveVelocity (I := I) σ (s - r)) n⁻¹ t]
      exact (congrFun (intrinsicGeodesic_continuation (I := I) g hEnorm q v (s - r))
        (n⁻¹ * t)).symm
    have hnege : g.inner (σ (s - r))
        ((-1 : ℝ) • (n⁻¹ • curveVelocity (I := I) σ (s - r)))
        ((-1 : ℝ) • (n⁻¹ • curveVelocity (I := I) σ (s - r))) = 1 := by
      rw [gInner_smul_self (I := I) g (σ (s - r)), he]
      norm_num
    have hgeone : ∀ t : ℝ, intrinsicGeodesic (I := I) g hEnorm (σ (s - r))
        ((-1 : ℝ) • (n⁻¹ • curveVelocity (I := I) σ (s - r))) t
          = σ (n⁻¹ * (-1 * t) + (s - r)) := by
      intro t
      rw [intrinsicGeo_smul_apply (I := I) g hEnorm (σ (s - r))
        (n⁻¹ • curveVelocity (I := I) σ (s - r)) (-1) t, hgeoe (-1 * t)]
    obtain ⟨hlpos, u, hu, humem⟩ :=
      exists_unit_direction_to_boundary (I := I) g hEnorm hB hBne hsB'
    have hstep1 := infDist_step (I := I) g hEnorm hsec hconv hBC hshift hx hu humem he
    have hstep2 := infDist_step (I := I) g hEnorm hsec hconv hBC hshift hx hu humem hnege
    obtain ⟨δ₁, hδ₁, hP₁⟩ :=
      Metric.eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 hstep1)
    obtain ⟨δ₂, hδ₂, hP₂⟩ :=
      Metric.eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 hstep2)
    obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ,
        ε = min (min (s - a) (b - s)) (min δ₁ δ₂ / n) := ⟨_, rfl⟩
    have hεa : ε ≤ s - a := by rw [hεdef]; exact (min_le_left _ _).trans (min_le_left _ _)
    have hεb : ε ≤ b - s := by rw [hεdef]; exact (min_le_left _ _).trans (min_le_right _ _)
    have hεδ : ε ≤ min δ₁ δ₂ / n := by rw [hεdef]; exact min_le_right _ _
    have hε : 0 < ε := by
      rw [hεdef]
      exact lt_min (lt_min (by linarith [hs.1]) (by linarith [hs.2]))
        (div_pos (lt_min hδ₁ hδ₂) hn)
    have hndiv : n * (min δ₁ δ₂ / n) = min δ₁ δ₂ := by field_simp
    refine ⟨-(n * g.inner (σ (s - r)) u (n⁻¹ • curveVelocity (I := I) σ (s - r))), ?_⟩
    filter_upwards [Ioo_mem_nhds (show s - ε < s by linarith) (show s < s + ε by linarith)]
      with y hy
    have hyab : y ∈ Icc a b := ⟨by linarith [hy.1], by linarith [hy.2]⟩
    rw [hγeq y hyab]
    rcases lt_trichotomy y s with hlt | hyeq | hgt
    · have hh0 : (0 : ℝ) < n * (s - y) := mul_pos hn (by linarith)
      have hlt2 : n * (s - y) < min δ₁ δ₂ := by
        have h1 : s - y < min δ₁ δ₂ / n := lt_of_lt_of_le (by linarith [hy.1]) hεδ
        have h2 := mul_lt_mul_of_pos_left h1 hn
        rwa [hndiv] at h2
      have hres := hP₂ (by
        rw [Real.dist_eq, sub_zero, abs_of_pos hh0]
        exact lt_of_lt_of_le hlt2 (min_le_right _ _)) hh0
      rw [hgeone, gInner_smul_right,
        show n⁻¹ * (-1 * (n * (s - y))) + (s - r) = y - r by
          rw [show (-1 : ℝ) * (n * (s - y)) = n * (-1 * (s - y)) by ring,
            inv_mul_cancel_left₀ hnne]; ring] at hres
      exact infDist_support_aux' hres
    · rw [hyeq, sub_self, mul_zero, add_zero]
    · have hh0 : (0 : ℝ) < n * (y - s) := mul_pos hn (by linarith)
      have hlt2 : n * (y - s) < min δ₁ δ₂ := by
        have h1 : y - s < min δ₁ δ₂ / n := lt_of_lt_of_le (by linarith [hy.2]) hεδ
        have h2 := mul_lt_mul_of_pos_left h1 hn
        rwa [hndiv] at h2
      have hres := hP₁ (by
        rw [Real.dist_eq, sub_zero, abs_of_pos hh0]
        exact lt_of_lt_of_le hlt2 (min_le_left _ _)) hh0
      rw [hgeoe, show n⁻¹ * (n * (y - s)) + (s - r) = y - r by
        rw [inv_mul_cancel_left₀ hnne]; ring] at hres
      exact infDist_support_aux hres

theorem concaveOn_infDist_boundary
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hsec : ∀ y : M, metricRm04At (I := I) g y ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    {C B : Set M} (hconv : IsTotallyConvex (I := I) g C) (hB : IsClosed B)
    (hBne : B.Nonempty) (hBC : B ⊆ C)
    (hshift : HasOrthogonalBoundaryShift (I := I) g hEnorm C B)
    (hcore : HasOpenCore (I := I) g C B)
    {γ : ℝ → M} {a b : ℝ} (hab : a ≤ b)
    (hgeo : Geodesic.IsGeodesicOn (I := I) g γ (Icc a b))
    (hcont : ContinuousOn γ (Icc a b)) (hmaps : MapsTo γ (Icc a b) C) :
    ConcaveOn ℝ (Icc a b) (fun s => Metric.infDist (γ s) B) := by
  rcases eq_or_lt_of_le hab with rfl | hab'
  · refine ⟨convex_Icc a a, ?_⟩
    intro p hp z hz α β hα hβ hsum
    have hpa : p = a := le_antisymm hp.2 hp.1
    have hza : z = a := le_antisymm hz.2 hz.1
    rw [hpa, hza]
    have hpt : α • a + β • a = a := by
      simp only [smul_eq_mul]
      linear_combination a * hsum
    rw [hpt]
    simp only [smul_eq_mul]
    have hone : α * Metric.infDist (γ a) B + β * Metric.infDist (γ a) B
        = Metric.infDist (γ a) B := by
      linear_combination Metric.infDist (γ a) B * hsum
    linarith
  · refine concaveOn_of_linear_upper_support (convex_Icc a b)
      ((Metric.continuous_infDist_pt B).comp_continuousOn hcont) ?_
    intro s hs
    rw [interior_Icc] at hs
    by_cases hex : ∃ t ∈ Icc a b, γ t ∉ B
    · exact exists_local_upper_support (I := I) g hEnorm hsec hconv hB hBne hBC hshift
        hab' hgeo hcont hmaps hs (hcore hab hgeo hcont hmaps hex s hs)
    · have hall : ∀ t ∈ Icc a b, γ t ∈ B := by
        intro t ht
        by_contra hb
        exact hex ⟨t, ht, hb⟩
      refine ⟨0, ?_⟩
      filter_upwards [Ioo_mem_nhds hs.1 hs.2] with y hy
      rw [Metric.infDist_zero_of_mem (hall y (Ioo_subset_Icc_self hy)),
        Metric.infDist_zero_of_mem (hall s (Ioo_subset_Icc_self hs))]
      simp

theorem concaveOn_infDist_intrinsicGeodesic
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hsec : ∀ y : M, metricRm04At (I := I) g y ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    {C B : Set M} (hconv : IsTotallyConvex (I := I) g C) (hB : IsClosed B)
    (hBne : B.Nonempty) (hBC : B ⊆ C)
    (hshift : HasOrthogonalBoundaryShift (I := I) g hEnorm C B)
    (hcore : HasOpenCore (I := I) g C B)
    (q : M) (v : TangentSpace I q) {a b : ℝ} (hab : a ≤ b)
    (hmaps : MapsTo (intrinsicGeodesic (I := I) g hEnorm q v) (Icc a b) C) :
    ConcaveOn ℝ (Icc a b)
      (fun s => Metric.infDist (intrinsicGeodesic (I := I) g hEnorm q v s) B) :=
  concaveOn_infDist_boundary (I := I) g hEnorm hsec hconv hB hBne hBC hshift hcore hab
    ((intrinsicGeodesic_isGeodesic (I := I) g hEnorm q v).isGeodesicOn _)
    (intrinsicGeodesic_continuous (I := I) g hEnorm q v).continuousOn hmaps

theorem isTotallyConvex_superlevel_infDist
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hsec : ∀ y : M, metricRm04At (I := I) g y ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    {C B : Set M} (hconv : IsTotallyConvex (I := I) g C) (hB : IsClosed B)
    (hBne : B.Nonempty) (hBC : B ⊆ C)
    (hshift : HasOrthogonalBoundaryShift (I := I) g hEnorm C B)
    (hcore : HasOpenCore (I := I) g C B) (t : ℝ) :
    IsTotallyConvex (I := I) g {x ∈ C | t ≤ Metric.infDist x B} := by
  intro γ a b hab hgeo hcont ha hbb y hy
  have hmaps : MapsTo γ (Icc a b) C := hconv hab hgeo hcont ha.1 hbb.1
  refine ⟨hmaps hy, ?_⟩
  have hconc := concaveOn_infDist_boundary (I := I) g hEnorm hsec hconv hB hBne hBC
    hshift hcore hab hgeo hcont hmaps
  rw [← segment_eq_Icc hab] at hy
  obtain ⟨α, β, hα, hβ, hsum, hyeq⟩ := hy
  have hkey := hconc.2 (left_mem_Icc.2 hab) (right_mem_Icc.2 hab) hα hβ hsum
  rw [hyeq] at hkey
  simp only [smul_eq_mul] at hkey
  exact superlevel_aux hα hβ hsum ha.2 hbb.2 hkey

end DifferentialGeometry.Geometry.Topology

end
