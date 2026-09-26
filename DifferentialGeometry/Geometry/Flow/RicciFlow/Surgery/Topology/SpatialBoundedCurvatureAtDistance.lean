import DifferentialGeometry.Geometry.Comparison.DistanceHessianLocal
import DifferentialGeometry.Geometry.Comparison.Distance.Continuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalNeighborhoodInduction

set_option autoImplicit false

noncomputable section

open Set Bundle
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [FiniteDimensional ℝ E] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem mem_connectedComponent_of_riemannianEDistOf_lt_top (g : SmoothRiemannianMetric I M)
    {x z : M} (h : riemannianEDistOf (I := I) g x z < ⊤) : z ∈ connectedComponent x := by
  obtain ⟨γ, hγ0, hγ1, hγ, _⟩ := exists_lt_of_edistOf_lt g h
  have hpre : IsPreconnected (γ '' Icc (0 : ℝ) 1) :=
    isPreconnected_Icc.image γ hγ.continuousOn
  have hx : x ∈ γ '' Icc (0 : ℝ) 1 := ⟨0, ⟨le_rfl, zero_le_one⟩, hγ0⟩
  have hz : z ∈ γ '' Icc (0 : ℝ) 1 := ⟨1, ⟨zero_le_one, le_rfl⟩, hγ1⟩
  exact hpre.subset_connectedComponent hx hz

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_riemannianEDistOf_lt_of_lt_add [T2Space M] (g : SmoothRiemannianMetric I M)
    {x z : M} {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (h : riemannianEDistOf (I := I) g x z < ENNReal.ofReal (r₁ + r₂)) :
    ∃ w, riemannianEDistOf (I := I) g x w < ENNReal.ofReal r₁ ∧
      riemannianEDistOf (I := I) g w z < ENNReal.ofReal r₂ := by
  by_cases hxz : riemannianEDistOf (I := I) g x z < ENNReal.ofReal r₁
  · refine ⟨z, hxz, ?_⟩
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr hr₂
  rw [not_lt] at hxz
  obtain ⟨γ, hγ0, hγ1, hγ, hlen⟩ := exists_lt_of_edistOf_lt g h
  set L := metricPathELength (I := I) g γ 0 1 with hL
  have hLtop : L ≠ ⊤ := ne_top_of_lt hlen
  have hLr : L.toReal < r₁ + r₂ := by
    have h' := (ENNReal.toReal_lt_toReal hLtop ENNReal.ofReal_ne_top).mpr hlen
    rwa [ENNReal.toReal_ofReal (by linarith)] at h'
  set m : ℝ := max (L.toReal - r₂) 0 with hm
  have hmr : m < r₁ := max_lt (by linarith) hr₁
  set c : ℝ := (m + r₁) / 2 with hc
  have hc0 : 0 ≤ c := by
    have : 0 ≤ m := le_max_right _ _
    rw [hc]
    linarith
  have hcr₁ : c < r₁ := by
    rw [hc]
    linarith
  have hcL : L.toReal - r₂ < c := by
    have : L.toReal - r₂ ≤ m := le_max_left _ _
    rw [hc]
    linarith
  have hcont : ContinuousOn (fun s => riemannianEDistOf (I := I) g x (γ s)) (Icc 0 1) :=
    (Geometry.Riemannian.continuous_riemannianEDist g x).comp_continuousOn hγ.continuousOn
  have hmem : ENNReal.ofReal c ∈ Icc (riemannianEDistOf (I := I) g x (γ 0))
      (riemannianEDistOf (I := I) g x (γ 1)) := by
    rw [hγ0, hγ1, riemannianEDistOf_self]
    exact ⟨bot_le, (ENNReal.ofReal_le_ofReal hcr₁.le).trans hxz⟩
  obtain ⟨s, hs, hsc⟩ := intermediate_value_Icc zero_le_one hcont hmem
  refine ⟨γ s, ?_, ?_⟩
  · change riemannianEDistOf (I := I) g x (γ s) = _ at hsc
    rw [hsc]
    exact (ENNReal.ofReal_lt_ofReal_iff hr₁).mpr hcr₁
  · have h0 : riemannianEDistOf (I := I) g x (γ s) ≤ metricPathELength (I := I) g γ 0 s := by
      have h' := edistOf_le_metricPathELength g hs.1 (hγ.mono (Icc_subset_Icc le_rfl hs.2))
      rwa [hγ0] at h'
    have h1 : riemannianEDistOf (I := I) g (γ s) z ≤ metricPathELength (I := I) g γ s 1 := by
      have h' := edistOf_le_metricPathELength g hs.2 (hγ.mono (Icc_subset_Icc hs.1 le_rfl))
      rwa [hγ1] at h'
    have hadd : metricPathELength (I := I) g γ 0 s + metricPathELength (I := I) g γ s 1 = L := by
      let _ : RiemannianBundle (fun y : M => TangentSpace I y) := ⟨g.toRiemannianMetric⟩
      exact Manifold.pathELength_add hs.1 hs.2
    have hsum : ENNReal.ofReal c + riemannianEDistOf (I := I) g (γ s) z <
        ENNReal.ofReal c + ENNReal.ofReal r₂ := by
      calc
        _ ≤ metricPathELength (I := I) g γ 0 s + metricPathELength (I := I) g γ s 1 := by
          rw [← hsc]
          exact add_le_add h0 h1
        _ = L := hadd
        _ < ENNReal.ofReal (c + r₂) := by
          rw [← ENNReal.ofReal_toReal hLtop]
          exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith)
        _ = _ := ENNReal.ofReal_add hc0 hr₂.le
    exact (ENNReal.add_lt_add_iff_left ENNReal.ofReal_ne_top).mp hsum

end DifferentialGeometry

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {g : SmoothRiemannianMetric I3 M} {eps C C1 C2 : ℝ} {x : M} {U : Set M}

def SpatialCanonicalAlternative.isWholeComponent :
    SpatialCanonicalAlternative g eps C x U → Prop
  | .positive _ _ _ => True
  | .round _ _ => True
  | _ => False

omit [T2Space M] [SigmaCompactSpace M] in
theorem SpatialCanonicalAlternative.eq_connectedComponent_of_isWholeComponent
    (A : SpatialCanonicalAlternative g eps C x U) (h : A.isWholeComponent) :
    U = connectedComponent x := by
  cases A with
  | neck data => exact h.elim
  | cap data deep => exact h.elim
  | positive whole data sec => exact whole
  | round whole data => exact whole

theorem SpatialCanonicalWitness.scalar_bounds_of_mem_ball
    (W : SpatialCanonicalWitness g eps C1 C2 x) {z : M}
    (hz : z ∈ riemannianBallOf (I := I3) g x (Real.sqrt (metricScalarAt g x))⁻¹) :
    C2⁻¹ * metricScalarAt g x ≤ metricScalarAt g z ∧
      metricScalarAt g z ≤ C2 * metricScalarAt g x :=
  W.scalar_bounds z (W.ball_inside (riemannianBallOf_mono g x W.radius_lower hz))

theorem SpatialCanonicalWitness.scalar_bounds_of_isWholeComponent
    (W : SpatialCanonicalWitness g eps C1 C2 x) (h : W.alternative.isWholeComponent) {z : M}
    (hz : riemannianEDistOf (I := I3) g x z < ⊤) :
    C2⁻¹ * metricScalarAt g x ≤ metricScalarAt g z ∧
      metricScalarAt g z ≤ C2 * metricScalarAt g x := by
  apply W.scalar_bounds z
  rw [W.alternative.eq_connectedComponent_of_isWholeComponent h]
  exact mem_connectedComponent_of_riemannianEDistOf_lt_top g hz

private theorem sum_range_succ_inv_sqrt_pow (C2 : ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (Real.sqrt C2 ^ k)⁻¹ =
      (Real.sqrt C2)⁻¹ * ∑ k ∈ Finset.range n, (Real.sqrt C2 ^ k)⁻¹ + 1 := by
  rw [Finset.sum_range_succ', Finset.mul_sum]
  simp only [pow_succ, mul_inv, pow_zero, inv_one]
  congr 1
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

private theorem one_le_sum_range_inv_sqrt_pow (C2 : ℝ) {n : ℕ} (hn : 0 < n) :
    1 ≤ ∑ k ∈ Finset.range n, (Real.sqrt C2 ^ k)⁻¹ := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hn
  rw [zero_add, sum_range_succ_inv_sqrt_pow]
  have : 0 ≤ (Real.sqrt C2)⁻¹ * ∑ k ∈ Finset.range m, (Real.sqrt C2 ^ k)⁻¹ :=
    mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))
      (Finset.sum_nonneg fun k _ => inv_nonneg.mpr (pow_nonneg (Real.sqrt_nonneg _) k))
  linarith

theorem exists_le_sum_range_inv_sqrt_pow {C2 A : ℝ} (hC2 : 1 ≤ C2)
    (hA : A * (Real.sqrt C2 - 1) < Real.sqrt C2) :
    ∃ n : ℕ, A ≤ ∑ k ∈ Finset.range n, (Real.sqrt C2 ^ k)⁻¹ := by
  have hs : 1 ≤ Real.sqrt C2 := Real.one_le_sqrt.mpr hC2
  rcases hs.eq_or_lt with heq | hlt
  · obtain ⟨n, hn⟩ := exists_nat_ge A
    refine ⟨n, ?_⟩
    rw [← heq]
    simpa using hn
  · set s := Real.sqrt C2 with hsdef
    have hs0 : 0 < s := zero_lt_one.trans hlt
    set r := s⁻¹ with hr
    have hr0 : 0 ≤ r := inv_nonneg.mpr hs0.le
    have hr1 : r < 1 := inv_lt_one_of_one_lt₀ hlt
    have hAr : A * (1 - r) < 1 := by
      have h1 : A * (1 - r) = (A * (s - 1)) / s := by
        rw [hr]
        field_simp
      rw [h1, div_lt_one hs0]
      exact hA
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (sub_pos.mpr hAr) hr1
    refine ⟨n, ?_⟩
    have hsum : ∑ k ∈ Finset.range n, (s ^ k)⁻¹ = (1 - r ^ n) / (1 - r) := by
      have hgeom := geom_sum_eq hr1.ne n
      have hrew : ∑ k ∈ Finset.range n, (s ^ k)⁻¹ = ∑ k ∈ Finset.range n, r ^ k :=
        Finset.sum_congr rfl fun k _ => by rw [hr, inv_pow]
      rw [hrew, hgeom]
      have hne : r - 1 ≠ 0 := sub_ne_zero.mpr hr1.ne
      have hne' : 1 - r ≠ 0 := sub_ne_zero.mpr hr1.ne'
      field_simp
      ring
    rw [hsum, le_div_iff₀ (sub_pos.mpr hr1)]
    linarith

theorem scalar_bounds_of_riemannianEDistOf_lt_of_spatialCanonicalWitness {q : ℝ} (hq : 0 ≤ q)
    (hC2 : 1 ≤ C2)
    (hW : ∀ x : M, q < metricScalarAt g x → Nonempty (SpatialCanonicalWitness g eps C1 C2 x)) :
    ∀ (n : ℕ) {y z : M}, C2 ^ n * q < metricScalarAt g y →
      riemannianEDistOf (I := I3) g y z < ENNReal.ofReal
        ((∑ k ∈ Finset.range n, (Real.sqrt C2 ^ k)⁻¹) / Real.sqrt (metricScalarAt g y)) →
      (C2 ^ n)⁻¹ * metricScalarAt g y ≤ metricScalarAt g z ∧
        metricScalarAt g z ≤ C2 ^ n * metricScalarAt g y := by
  intro n
  induction n with
  | zero =>
    intro y z _ hz
    simp at hz
  | succ n ih =>
    intro y z hy hz
    have hqy : q < metricScalarAt g y :=
      (le_mul_of_one_le_left hq (one_le_pow₀ hC2)).trans_lt hy
    obtain ⟨W⟩ := hW y hqy
    have hRy : 0 < metricScalarAt g y := W.Q_pos
    have hC2pos : 0 < C2 := zero_lt_one.trans_le hC2
    have hs : 0 < Real.sqrt C2 := Real.sqrt_pos.mpr hC2pos
    have hsy : 0 < Real.sqrt (metricScalarAt g y) := Real.sqrt_pos.mpr hRy
    rw [sum_range_succ_inv_sqrt_pow] at hz
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      have hz' : z ∈ riemannianBallOf (I := I3) g y (Real.sqrt (metricScalarAt g y))⁻¹ := by
        change riemannianEDistOf (I := I3) g y z < _
        simpa using hz
      simpa using W.scalar_bounds_of_mem_ball hz'
    · set S := ∑ k ∈ Finset.range n, (Real.sqrt C2 ^ k)⁻¹ with hS
      have hS1 : 1 ≤ S := one_le_sum_range_inv_sqrt_pow C2 hn
      have hr₂ : 0 < (Real.sqrt C2)⁻¹ * S / Real.sqrt (metricScalarAt g y) :=
        div_pos (mul_pos (inv_pos.mpr hs) (zero_lt_one.trans_le hS1)) hsy
      have hsplit : ((Real.sqrt C2)⁻¹ * S + 1) / Real.sqrt (metricScalarAt g y) =
          (Real.sqrt (metricScalarAt g y))⁻¹ +
            (Real.sqrt C2)⁻¹ * S / Real.sqrt (metricScalarAt g y) := by
        field_simp
        ring
      rw [hsplit] at hz
      obtain ⟨w, hyw, hwz⟩ :=
        exists_riemannianEDistOf_lt_of_lt_add g (inv_pos.mpr hsy) hr₂ hz
      obtain ⟨hwl, hwu⟩ := W.scalar_bounds_of_mem_ball (z := w) hyw
      have hqw : C2 ^ n * q < metricScalarAt g w := by
        have h1 : C2 ^ n * q = C2⁻¹ * (C2 ^ (n + 1) * q) := by
          rw [pow_succ]
          field_simp
        rw [h1]
        exact (mul_lt_mul_of_pos_left hy (inv_pos.mpr hC2pos)).trans_le hwl
      have hRw : 0 < metricScalarAt g w := (mul_nonneg (pow_nonneg hC2pos.le n) hq).trans_lt hqw
      have hsw : 0 < Real.sqrt (metricScalarAt g w) := Real.sqrt_pos.mpr hRw
      have hradius : (Real.sqrt C2)⁻¹ * S / Real.sqrt (metricScalarAt g y) ≤
          S / Real.sqrt (metricScalarAt g w) := by
        have hsq : Real.sqrt (metricScalarAt g w) ≤
            Real.sqrt C2 * Real.sqrt (metricScalarAt g y) := by
          rw [← Real.sqrt_mul hC2pos.le]
          exact Real.sqrt_le_sqrt hwu
        rw [mul_div_assoc, inv_mul_eq_div, div_div, div_le_div_iff_of_pos_left
          (zero_lt_one.trans_le hS1) (mul_pos hsy hs) hsw, mul_comm]
        exact hsq
      obtain ⟨hzl, hzu⟩ := ih hqw (hwz.trans_le (ENNReal.ofReal_le_ofReal hradius))
      have hpow : (0 : ℝ) < C2 ^ n := pow_pos hC2pos n
      constructor
      · calc
          (C2 ^ (n + 1))⁻¹ * metricScalarAt g y =
              (C2 ^ n)⁻¹ * (C2⁻¹ * metricScalarAt g y) := by
            rw [pow_succ, mul_inv, mul_assoc]
          _ ≤ (C2 ^ n)⁻¹ * metricScalarAt g w :=
            mul_le_mul_of_nonneg_left hwl (inv_nonneg.mpr hpow.le)
          _ ≤ _ := hzl
      · calc
          metricScalarAt g z ≤ C2 ^ n * metricScalarAt g w := hzu
          _ ≤ C2 ^ n * (C2 * metricScalarAt g y) := mul_le_mul_of_nonneg_left hwu hpow.le
          _ = C2 ^ (n + 1) * metricScalarAt g y := by rw [pow_succ, mul_assoc]

theorem ofReal_le_riemannianEDistOf_of_scalar_lt_of_spatialCanonicalWitness {q : ℝ}
    (hq : 0 ≤ q) (hC2 : 1 ≤ C2)
    (hW : ∀ x : M, q < metricScalarAt g x → Nonempty (SpatialCanonicalWitness g eps C1 C2 x))
    (n : ℕ) {y z : M} (hz : C2 ^ n * q < metricScalarAt g z)
    (hyz : C2 ^ n * metricScalarAt g y < metricScalarAt g z) :
    ENNReal.ofReal ((∑ k ∈ Finset.range n, (Real.sqrt C2 ^ k)⁻¹) /
      Real.sqrt (metricScalarAt g z)) ≤ riemannianEDistOf (I := I3) g y z := by
  by_contra hlt
  rw [not_le] at hlt
  rw [riemannianEDistOf_comm] at hlt
  have hlow := (scalar_bounds_of_riemannianEDistOf_lt_of_spatialCanonicalWitness hq hC2 hW
    n hz hlt).1
  have hpow : (0 : ℝ) < C2 ^ n := pow_pos (zero_lt_one.trans_le hC2) n
  have h1 : metricScalarAt g z ≤ C2 ^ n * metricScalarAt g y := by
    have h2 := mul_le_mul_of_nonneg_left hlow hpow.le
    rwa [← mul_assoc, mul_inv_cancel₀ hpow.ne', one_mul] at h2
  exact absurd hyz (not_lt.mpr h1)

theorem exists_scalar_bound_at_distance_of_spatialCanonicalWitness (hC2 : 1 ≤ C2) {A : ℝ}
    (hA : A * (Real.sqrt C2 - 1) < Real.sqrt C2) :
    ∃ Q : ℝ, 1 ≤ Q ∧ ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
      [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
      (g : SmoothRiemannianMetric I3 M) (eps C1 q : ℝ), 0 ≤ q →
      (∀ x : M, q < metricScalarAt g x → Nonempty (SpatialCanonicalWitness g eps C1 C2 x)) →
      ∀ y : M, Q * q < metricScalarAt g y →
      ∀ z ∈ riemannianBallOf (I := I3) g y (A / Real.sqrt (metricScalarAt g y)),
        Q⁻¹ * metricScalarAt g y ≤ metricScalarAt g z ∧
          metricScalarAt g z ≤ Q * metricScalarAt g y := by
  obtain ⟨n, hn⟩ := exists_le_sum_range_inv_sqrt_pow hC2 hA
  refine ⟨C2 ^ n, one_le_pow₀ hC2, ?_⟩
  intro M _ _ _ _ _ g eps C1 q hq hW y hy z hz
  apply scalar_bounds_of_riemannianEDistOf_lt_of_spatialCanonicalWitness hq hC2 hW n hy
  exact hz.trans_le (ENNReal.ofReal_le_ofReal
    (div_le_div_of_nonneg_right hn (Real.sqrt_nonneg _)))

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

universe u

variable {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s)

theorem scalar_bounds_of_riemannianEDistOf_lt_of_spatiallyCanonicalBefore
    {ε C1 C2 q t₀ t : ℝ} (ht : t ∈ Ioo a t₀) (hq : 0 ≤ q) (hC2 : 1 ≤ C2)
    (hG : G.SpatiallyCanonicalBefore ε C1 C2 q t₀) (n : ℕ) {y z : P.Carrier}
    (hy : C2 ^ n * q < G.flow.scalar t y)
    (hz : riemannianEDistOf (I := I3) (G.flow.base.metric t) y z < ENNReal.ofReal
      ((∑ k ∈ Finset.range n, (Real.sqrt C2 ^ k)⁻¹) / Real.sqrt (G.flow.scalar t y))) :
    (C2 ^ n)⁻¹ * G.flow.scalar t y ≤ G.flow.scalar t z ∧
      G.flow.scalar t z ≤ C2 ^ n * G.flow.scalar t y :=
  scalar_bounds_of_riemannianEDistOf_lt_of_spatialCanonicalWitness hq hC2
    (fun x hx => (hG x t ht hx).elim fun W _ => ⟨W⟩) n hy hz

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab
