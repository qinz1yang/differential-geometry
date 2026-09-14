import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.GoodPointNeckArmFrontier

set_option autoImplicit false
noncomputable section
open Bundle Manifold Set
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem windowedModelWitness_of_orientedWitness {M : Type u} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M] {D : RealTimeInterval}
    {S : SolutionOn (I := I3) (M := M) D} {o : TangentOrientationSection M} {eps kappa : ℝ}
    {x : M} {t : ℝ} (h : OrientedWitness S o eps kappa x t) :
    Nonempty (WindowedModelWitness eps kappa S x t) :=
  ⟨h.choose⟩

def GoodPointNeckArmStructure (kappa alpha theta epsStar Lmin Lmax : ℝ) : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
    (D : RealTimeInterval) (S : SolutionOn (I := I3) (M := M) D)
    (o : TangentOrientationSection M) (x : M) (t : ℝ),
    OrientedWitness S o epsStar kappa x t →
    ∀ a b : MinimizingArm (S.base.metric t) x, ∀ s v : ℝ,
      s ∈ Set.Ioc 0 a.length → v ∈ Set.Ioc 0 b.length →
      Real.sqrt (S.scalar t x) * s ∈ Set.Icc Lmin Lmax →
      Real.sqrt (S.scalar t x) * v ∈ Set.Icc Lmin Lmax →
      theta ≤ Real.arccos ((s ^ 2 + v ^ 2 -
        metricDistance (S.base.metric t) (a.point s) (b.point v) ^ 2) / (2 * s * v)) →
      ∃ neck : StrongNeck S (2 * alpha) x t, ArmNeckHeights neck a b s v

theorem goodPointNeckArmStructure_of_frontier {kappa alpha theta C epsStar Lmin Lmax : ℝ}
    (h : GoodPointNeckArmFrontier.{u} kappa alpha theta C epsStar Lmin Lmax) :
    GoodPointNeckArmStructure.{u} kappa alpha theta epsStar Lmin Lmax := by
  intro M _ _ _ _ _ D S o x t hw a b s v hs hv hsL hvL hang
  obtain ⟨neck, hheights, _⟩ := h M D S o x t hw a b s v hs hv hsL hvL hang
  exact ⟨neck, hheights⟩

theorem goodPointNeckArmFrontier_of_structure_and_coreDiameterBound {kappa alpha theta : ℝ}
    {epsStar : ℝ} {Lmin Lmax : ℝ}
    (hstructure : GoodPointNeckArmStructure.{u} kappa alpha theta epsStar Lmin Lmax)
    (hdiameter : NeckCoreDiameterBound.{u}) :
    ∃ C : ℝ, 0 < C ∧ GoodPointNeckArmFrontier.{u} kappa alpha theta C epsStar Lmin Lmax := by
  obtain ⟨C, hC, hbound⟩ := metricDistance_core_le_of_neckCoreDiameterBound hdiameter
  refine ⟨C, hC, ?_⟩
  intro M _ _ _ _ _ D S o x t hw a b s v hs hv hsL hvL hang
  obtain ⟨neck, hheights⟩ := hstructure M D S o x t hw a b s v hs hv hsL hvL hang
  exact ⟨neck, hheights,
    fun y hy z hz => hbound M D S (2 * alpha) x t neck y hy z hz⟩

theorem goodPointNeckArmFrontier_of_lt {kappa alpha theta C epsStar Lmin Lmax : ℝ}
    (h : Lmax < Lmin) :
    GoodPointNeckArmFrontier.{u} kappa alpha theta C epsStar Lmin Lmax := by
  intro M _ _ _ _ _ D S o x t _hw a b s v _hs _hv hsL _hvL _hang
  exfalso
  linarith [hsL.1, hsL.2, h]

theorem goodPointNeckArmStructure_of_lt {kappa alpha theta epsStar Lmin Lmax : ℝ}
    (h : Lmax < Lmin) : GoodPointNeckArmStructure.{u} kappa alpha theta epsStar Lmin Lmax := by
  intro M _ _ _ _ _ D S o x t _hw a b s v _hs _hv hsL _hvL _hang
  exfalso
  linarith [hsL.1, hsL.2, h]

theorem goodPointNeckArmFrontier_of_epsStar_nonpos {kappa alpha theta C epsStar Lmin Lmax : ℝ}
    (h : epsStar ≤ 0) :
    GoodPointNeckArmFrontier.{u} kappa alpha theta C epsStar Lmin Lmax := by
  intro M _ _ _ _ _ D S o x t hw a b s v _hs _hv _hsL _hvL _hang
  obtain ⟨W, _⟩ := hw
  exact absurd W.eps_pos (not_lt.mpr h)

theorem goodPointNeckArmStructure_of_epsStar_nonpos {kappa alpha theta epsStar Lmin Lmax : ℝ}
    (h : epsStar ≤ 0) : GoodPointNeckArmStructure.{u} kappa alpha theta epsStar Lmin Lmax := by
  intro M _ _ _ _ _ D S o x t hw a b s v _hs _hv _hsL _hvL _hang
  obtain ⟨W, _⟩ := hw
  exact absurd W.eps_pos (not_lt.mpr h)

theorem twoArmNoReturnDepth_lt_inv_of_armNeckHeights {M : Type u} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M] [T2Space M] {D : RealTimeInterval}
    {S : SolutionOn (I := I3) (M := M) D} {alpha : ℝ} {x : M} {t : ℝ}
    (neck : StrongNeck S (2 * alpha) x t) (a b : MinimizingArm (S.base.metric t) x) {s v : ℝ}
    (h : ArmNeckHeights neck a b s v) : twoArmNoReturnDepth (M := M) < (2 * alpha)⁻¹ := by
  obtain ⟨p, q, k, l, _hpt, _hqt, _hkl, hk, hk', _hl, _hl'⟩ := h
  exact lt_of_le_of_lt hk hk'

theorem twoArmNoReturnDepth_le_four_mul_of_armNeckHeights {M : Type u} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M] [T2Space M] {D : RealTimeInterval}
    {S : SolutionOn (I := I3) (M := M) D} {alpha : ℝ} {x : M} {t : ℝ}
    (neck : StrongNeck S (2 * alpha) x t) (a b : MinimizingArm (S.base.metric t) x) {s v : ℝ}
    (hs : s ∈ Set.Icc 0 a.length) (h : ArmNeckHeights neck a b s v) :
    twoArmNoReturnDepth (M := M) ≤ 4 * (Real.sqrt (S.scalar t x) * s) := by
  obtain ⟨p, q, k, l, hpt, _hqt, _hkl, hk, hk', _hl, _hl'⟩ := h
  have hHpos : 0 < twoArmNoReturnDepth (M := M) := twoArmNoReturnDepth_pos (M := M)
  have hdeep : twoArmNoReturnDepth (M := M) / 2 < |k| := by
    have := abs_nonneg k
    linarith
  have hbase := neck.le_edistOf_of_height (R := twoArmNoReturnDepth (M := M) / 2)
    (q := p) (l := k) (by linarith) hdeep hk'
  rw [← hpt] at hbase
  rw [edistOf_rescaledMetric_zero S t (S.scalar t x) neck.Q_pos x (a.point s),
    a.edistOf_start hs, ← ENNReal.ofReal_mul (Real.sqrt_nonneg (S.scalar t x))] at hbase
  have hle : twoArmNoReturnDepth (M := M) / 2 / 2 ≤ Real.sqrt (S.scalar t x) * s :=
    (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (Real.sqrt_nonneg (S.scalar t x)) hs.1)).mp hbase
  linarith

theorem twoArmNoReturnDepth_le_four_mul_of_armNeckHeights_le {M : Type u} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M] [T2Space M] {D : RealTimeInterval}
    {S : SolutionOn (I := I3) (M := M) D} {alpha : ℝ} {x : M} {t Lmax : ℝ}
    (neck : StrongNeck S (2 * alpha) x t) (a b : MinimizingArm (S.base.metric t) x) {s v : ℝ}
    (hs : s ∈ Set.Icc 0 a.length) (h : ArmNeckHeights neck a b s v)
    (hsL : Real.sqrt (S.scalar t x) * s ≤ Lmax) :
    twoArmNoReturnDepth (M := M) ≤ 4 * Lmax := by
  have h1 := twoArmNoReturnDepth_le_four_mul_of_armNeckHeights neck a b hs h
  linarith

def BufferedCanonical.enlarge_constants {M : Type u} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
    {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D} {alpha C H : ℝ} {x : M}
    {t : ℝ} (B : BufferedCanonical S alpha C H x t) {C' : ℝ} (hC' : C < C') :
    BufferedCanonical S alpha C' H x t := by
  have hC : 0 < C := zero_lt_one.trans_le B.witness.one_le_comparison_constant
  have hC'pos : 0 < C' := lt_trans hC hC'
  have hinv : C'⁻¹ < C⁻¹ := (inv_lt_inv₀ hC'pos hC).mpr hC'
  have hmul : C * S.scalar t x < C' * S.scalar t x :=
    mul_lt_mul_of_pos_right hC' B.witness.Q_pos
  refine ⟨B.tolerance, B.tolerance_pos, B.tolerance_lt,
    B.witness.enlarge_constants hC'.le hC'.le, B.a, B.b, B.margin, B.a_pos,
    B.margin_pos, B.radial_margin, B.inner_ball, B.outer_ball, ?_, ?_, ?_, ?_⟩
  · intro y hy
    exact ⟨(mul_lt_mul_of_pos_right hinv B.witness.Q_pos).trans (B.scalar_reserve y hy).1,
      (B.scalar_reserve y hy).2.trans hmul⟩
  · intro y hy
    exact (B.rm_reserve y hy).trans hmul
  · intro hv
    exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal
        (div_le_div_of_nonneg_right hinv.le
          (mul_nonneg B.witness.Q_pos.le (Real.sqrt_nonneg _))))
      (B.volume_reserve (by
        simpa only [CanonicalWitness.enlarge_constants_requiresVolume] using hv))
  · intro cap hc
    obtain ⟨hdepth, halteq⟩ := hc
    have hmono : (B.witness.enlarge_constants hC'.le hC'.le).alternative =
        B.witness.alternative.mono_constant hC hC'.le B.witness.Q_pos.le := rfl
    rw [hmono] at halteq
    have halteq' : B.witness.alternative = CanonicalAlternative.cap cap hdepth := by
      cases hW : B.witness.alternative with
      | neck data =>
          rw [hW] at halteq
          simp only [CanonicalAlternative.mono_constant] at halteq
          exact absurd halteq (by simp)
      | cap data deep =>
          rw [hW] at halteq
          simp only [CanonicalAlternative.mono_constant] at halteq
          cases halteq
          rfl
      | positive whole data hsec =>
          rw [hW] at halteq
          simp only [CanonicalAlternative.mono_constant] at halteq
          exact absurd halteq (by simp)
      | round whole data =>
          rw [hW] at halteq
          simp only [CanonicalAlternative.mono_constant] at halteq
          exact absurd halteq (by simp)
    obtain ⟨v, neck, hv, hlo, hhi, hfar, hdiam⟩ := B.cap_collar cap ⟨hdepth, halteq'⟩
    exact ⟨v, neck, hv,
      (mul_le_mul_of_nonneg_right hinv.le B.witness.Q_pos.le).trans hlo,
      hhi.trans hmul.le,
      hfar,
      fun y hy z hz =>
        (hdiam y hy z hz).trans (div_le_div_of_nonneg_right hC'.le (Real.sqrt_nonneg _))⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
