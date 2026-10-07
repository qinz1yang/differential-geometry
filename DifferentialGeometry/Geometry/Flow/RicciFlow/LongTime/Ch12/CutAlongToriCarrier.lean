import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CutAlongTori
import DifferentialGeometry.Topology.Manifold.SmoothBoundaryAtlas.Inclusion
import DifferentialGeometry.Topology.Manifold.SmoothBoundaryAtlas.Orientation
import DifferentialGeometry.Topology.Manifold.SmoothBoundaryAtlas.Tangent
import DifferentialGeometry.Topology.Manifold.SmoothBoundaryAtlas.LocalMaps
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph

set_option autoImplicit false
noncomputable section
open Set Function Manifold GC.Endpoint DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff
universe u
namespace GC.LongTime.Ch12

abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- A chart of a 3-manifold around `x ∈ W` (`W` open) with image in the open half space `x₀ > 0`. -/
theorem exists_positive_chart_C2a {N : Type*} [TopologicalSpace N] [ChartedSpace E3 N]
    [IsManifold (𝓡 3) ∞ N] {W : Set N} (hW : IsOpen W) {x : N} (hx : x ∈ W) :
    ∃ φ : PartialDiffeomorph (𝓡 3) (𝓡 3) N E3 ∞,
      x ∈ φ.source ∧ φ.source ⊆ W ∧ ∀ y ∈ φ.source, 0 < φ y 0 := by
  let e := DifferentialGeometry.Topology.PartialDiffeomorph.extendedChart (I := 𝓡 3) x
  let v : E3 := EuclideanSpace.single 0 1 - e x
  let T : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞ :=
    { toEquiv := Equiv.addRight v
      contMDiff_toFun := (contDiff_id.add contDiff_const).contMDiff
      contMDiff_invFun := (contDiff_id.sub contDiff_const).contMDiff }
  let φ0 : PartialDiffeomorph (𝓡 3) (𝓡 3) N E3 ∞ := e.trans T.toPartialDiffeomorph
  have hx0 : x ∈ φ0.source := ⟨mem_extChartAt_source x, trivial⟩
  have hφ0x : φ0 x = EuclideanSpace.single 0 1 := by
    change e x + v = _
    simp [v]
  let U : Set N := W ∩ (φ0.toOpenPartialHomeomorph.source ∩
    φ0.toOpenPartialHomeomorph ⁻¹' Metric.ball (EuclideanSpace.single 0 (1:ℝ) : E3) (1/2))
  have hU : IsOpen U :=
    hW.inter (φ0.toOpenPartialHomeomorph.isOpen_inter_preimage Metric.isOpen_ball)
  refine ⟨φ0.restrict U hU, ⟨hx0, ⟨hx, hx0, ?_⟩⟩, ?_, ?_⟩
  · change φ0 x ∈ Metric.ball _ _
    rw [hφ0x]; exact Metric.mem_ball_self (by norm_num)
  · intro y hy; exact hy.2.1
  · intro y hy
    have h := hy.2.2.2
    have h2 : dist (φ0 y) (EuclideanSpace.single 0 (1:ℝ) : E3) < 1/2 := h
    have h3 : |φ0 y 0 - 1| ≤ dist (φ0 y) (EuclideanSpace.single 0 (1:ℝ) : E3) := by
      have := PiLp.norm_apply_le (φ0 y - EuclideanSpace.single 0 (1:ℝ)) 0
      rw [dist_eq_norm]
      simpa using this
    have := abs_lt.mp (lt_of_le_of_lt h3 h2)
    change 0 < φ0 y 0
    linarith [this.1]

section Sets

variable {N : Type*} [TopologicalSpace N] [ChartedSpace E3 N] (F : CollaredTorusFamily_C2a N)

/-- The open tube `σ_i (T² × (-1/2, 1/2))` removed by the cut. -/
def tubeOpen_C2a (i : Fin F.count) : Set N := F.collar i '' (univ ×ˢ Ioo (-1/2 : ℝ) (1/2))

/-- The closed tube `σ_i (T² × [-1/2, 1/2])`. -/
def tubeClosed_C2a (i : Fin F.count) : Set N := F.collar i '' (univ ×ˢ Icc (-1/2 : ℝ) (1/2))

/-- The cut region `K = N ∖ ⋃ tubes`. -/
def cutSet_C2a : Set N := (⋃ i, tubeOpen_C2a F i)ᶜ

/-- The part of `K` away from the cut tori. -/
def cutInt_C2a : Set N := (⋃ i, tubeClosed_C2a F i)ᶜ

variable {F}

theorem Ioo_subset_collar_C2a : (univ ×ˢ Ioo (-1/2 : ℝ) (1/2) : Set (Torus × ℝ)) ⊆
    signedCollarSource := by
  rintro ⟨t, s⟩ ⟨-, h1, h2⟩
  exact ⟨by linarith, by linarith⟩

theorem Icc_subset_collar_C2a : (univ ×ˢ Icc (-1/2 : ℝ) (1/2) : Set (Torus × ℝ)) ⊆
    signedCollarSource := by
  rintro ⟨t, s⟩ ⟨-, h1, h2⟩
  exact ⟨by linarith, by linarith⟩

theorem isOpen_tubeOpen_C2a (i : Fin F.count) : IsOpen (tubeOpen_C2a F i) := by
  refine (F.collar i).toOpenPartialHomeomorph.isOpen_image_of_subset_source ?_ ?_
  · exact isOpen_univ.prod isOpen_Ioo
  · change _ ⊆ (F.collar i).source
    rw [F.source_eq]; exact Ioo_subset_collar_C2a

theorem isClosed_tubeClosed_C2a [T2Space N] (i : Fin F.count) : IsClosed (tubeClosed_C2a F i) := by
  have hc : IsCompact (univ ×ˢ Icc (-1/2 : ℝ) (1/2) : Set (Torus × ℝ)) :=
    isCompact_univ.prod isCompact_Icc
  refine (hc.image_of_continuousOn ?_).isClosed
  exact (F.collar i).toOpenPartialHomeomorph.continuousOn.mono (by change _ ⊆ (F.collar i).source; rw [F.source_eq]; exact Icc_subset_collar_C2a)

theorem isClosed_cutSet_C2a : IsClosed (cutSet_C2a F) :=
  (isOpen_iUnion isOpen_tubeOpen_C2a).isClosed_compl

theorem isOpen_cutInt_C2a [T2Space N] : IsOpen (cutInt_C2a F) :=
  (isClosed_iUnion_of_finite isClosed_tubeClosed_C2a).isOpen_compl

theorem tubeOpen_subset_tubeClosed_C2a (i : Fin F.count) : tubeOpen_C2a F i ⊆ tubeClosed_C2a F i :=
  image_mono (prod_mono subset_rfl Ioo_subset_Icc_self)

theorem cutInt_subset_cutSet_C2a : cutInt_C2a F ⊆ cutSet_C2a F := by
  intro x hx hx'
  obtain ⟨i, hi⟩ := mem_iUnion.mp hx'
  exact hx (mem_iUnion.mpr ⟨i, tubeOpen_subset_tubeClosed_C2a i hi⟩)

theorem tubeClosed_subset_target_C2a (i : Fin F.count) : tubeClosed_C2a F i ⊆ (F.collar i).target := by
  rintro _ ⟨p, hp, rfl⟩
  exact (F.collar i).map_source (by rw [F.source_eq]; exact Icc_subset_collar_C2a hp)

/-- A point of a collar lies in the `i`-th open tube iff `|s| < 1/2`. -/
theorem collar_mem_tubeOpen_iff_C2a (i : Fin F.count) {p : Torus × ℝ} (hp : p ∈ signedCollarSource) :
    F.collar i p ∈ tubeOpen_C2a F i ↔ -1/2 < p.2 ∧ p.2 < 1/2 := by
  constructor
  · rintro ⟨q, ⟨-, hq⟩, hqp⟩
    have hqs : q ∈ (F.collar i).source := by
      rw [F.source_eq]; exact Ioo_subset_collar_C2a ⟨trivial, hq⟩
    have hps : p ∈ (F.collar i).source := by rw [F.source_eq]; exact hp
    have : q = p := (F.collar i).toOpenPartialHomeomorph.injOn hqs hps hqp
    subst this; exact hq
  · intro h
    exact ⟨p, ⟨trivial, h⟩, rfl⟩

theorem collar_not_mem_tube_other_C2a {i j : Fin F.count} (hij : j ≠ i) {y : N}
    (hy : y ∈ (F.collar i).target) : y ∉ tubeOpen_C2a F j := by
  intro h
  have : y ∈ (F.collar j).target := by
    obtain ⟨q, hq, rfl⟩ := h
    exact (F.collar j).map_source (by rw [F.source_eq]; exact Ioo_subset_collar_C2a hq)
  exact (Set.disjoint_left.mp (F.disjoint hij.symm)) hy this

/-- A point of the cut region outside `cutInt` is a point `σ_i(p)` with `|p.2| = 1/2`. -/
theorem exists_boundary_param_C2a {x : N} (hx : x ∈ cutSet_C2a F) (hx' : x ∉ cutInt_C2a F) :
    ∃ (i : Fin F.count) (p : Torus × ℝ), p ∈ signedCollarSource ∧ F.collar i p = x ∧
      (p.2 = 1/2 ∨ p.2 = -1/2) := by
  have : ∃ i, x ∈ tubeClosed_C2a F i := by
    by_contra hcon
    push Not at hcon
    exact hx' (by simpa [cutInt_C2a] using hcon)
  obtain ⟨i, q, hq, rfl⟩ := this
  refine ⟨i, q, Icc_subset_collar_C2a hq, rfl, ?_⟩
  obtain ⟨-, h1, h2⟩ := hq
  by_contra hne
  push Not at hne
  apply hx
  refine mem_iUnion.mpr ⟨i, ?_⟩
  rw [collar_mem_tubeOpen_iff_C2a i (Icc_subset_collar_C2a ⟨trivial, h1, h2⟩)]
  exact ⟨lt_of_le_of_ne h1 (Ne.symm hne.2), lt_of_le_of_ne h2 hne.1⟩

/-- A collar point with `1/2 ≤ |s| < 1` lies in the cut region. -/
theorem collar_mem_cutSet_C2a (i : Fin F.count) {p : Torus × ℝ} (hp : p ∈ signedCollarSource)
    (h : 1/2 ≤ |p.2|) : F.collar i p ∈ cutSet_C2a F := by
  simp only [cutSet_C2a, mem_compl_iff, mem_iUnion, not_exists]
  intro j
  by_cases hj : j = i
  · subst hj
    rw [collar_mem_tubeOpen_iff_C2a j hp]
    intro hc
    have := abs_lt.mpr ⟨by linarith [hc.1], hc.2⟩
    linarith [this]
  · exact collar_not_mem_tube_other_C2a hj
      ((F.collar i).map_source (by rw [F.source_eq]; exact hp))

theorem collar_pm_not_mem_cutInt_C2a (i : Fin F.count) (t : Torus) {s : ℝ}
    (hs : s = 1/2 ∨ s = -1/2) : F.collar i (t, s) ∉ cutInt_C2a F := by
  intro h
  apply h
  refine mem_iUnion.mpr ⟨i, (t, s), ⟨trivial, ?_⟩, rfl⟩
  rcases hs with rfl | rfl <;> constructor <;> norm_num

theorem collar_pm_mem_cutSet_C2a (i : Fin F.count) (t : Torus) {s : ℝ}
    (hs : s = 1/2 ∨ s = -1/2) : F.collar i (t, s) ∈ cutSet_C2a F := by
  have hp : (t, s) ∈ signedCollarSource := by
    rcases hs with rfl | rfl <;> exact ⟨by norm_num, by norm_num⟩
  refine collar_mem_cutSet_C2a i hp ?_
  rcases hs with rfl | rfl <;> norm_num [abs_of_neg]

end Sets

abbrev E1 := EuclideanSpace ℝ (Fin 1)

def coordLinear_C2a : ((E1 × E1) × ℝ) ≃ₗ[ℝ] E3 where
  toFun x := WithLp.toLp 2 ![x.2, x.1.1 0, x.1.2 0]
  invFun v := ((WithLp.toLp 2 ![v 1], WithLp.toLp 2 ![v 2]), v 0)
  map_add' x y := by ext i; fin_cases i <;> simp
  map_smul' c x := by ext i; fin_cases i <;> simp
  left_inv x := by
    obtain ⟨⟨a, b⟩, r⟩ := x
    refine Prod.ext (Prod.ext ?_ ?_) rfl
    · ext i; fin_cases i; simp
    · ext i; fin_cases i; simp
  right_inv v := by ext i; fin_cases i <;> simp

def coordEquiv_C2a : ((E1 × E1) × ℝ) ≃L[ℝ] E3 := coordLinear_C2a.toContinuousLinearEquiv

theorem coordEquiv_zero_C2a (x : (E1 × E1) × ℝ) : coordEquiv_C2a x 0 = x.2 := rfl

def coordDiffeo_C2a : Diffeomorph ((modelWithCornersSelf ℝ (E1 × E1)).prod 𝓘(ℝ, ℝ)) (𝓡 3)
    ((E1 × E1) × ℝ) E3 ∞ where
  toEquiv := coordEquiv_C2a.toEquiv
  contMDiff_toFun := by
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
    exact coordEquiv_C2a.contDiff.contMDiff
  contMDiff_invFun := by
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
    exact coordEquiv_C2a.symm.contDiff.contMDiff

/-- The affine height diffeomorphism `s ↦ ε s - 1/2` of the line (`ε = ±1`). -/
def heightAffine_C2a (ε : ℝ) (hε : ε = 1 ∨ ε = -1) : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞ where
  toFun s := ε * s - 1/2
  invFun r := ε * (r + 1/2)
  left_inv s := by rcases hε with rfl | rfl <;> ring
  right_inv r := by rcases hε with rfl | rfl <;> ring
  contMDiff_toFun := ((contDiff_const.mul contDiff_id).sub contDiff_const).contMDiff
  contMDiff_invFun := (contDiff_const.mul (contDiff_id.add contDiff_const)).contMDiff

section BoundaryChart

variable {N : Type*} [TopologicalSpace N] [ChartedSpace E3 N] [IsManifold (𝓡 3) ∞ N]
  (F : CollaredTorusFamily_C2a N)

omit [IsManifold (𝓡 3) ∞ N] in
/-- Chart at the cut torus `σ_i(t0, ε/2)` whose first coordinate is `ε s - 1/2`, with `K`
exactly `{x₀ ≥ 0}` inside its source. -/
theorem exists_boundary_chart_C2a (i : Fin F.count) (ε : ℝ) (hε : ε = 1 ∨ ε = -1) (t0 : Torus) :
    ∃ φ : PartialDiffeomorph (𝓡 3) (𝓡 3) N E3 ∞,
      F.collar i (t0, ε/2) ∈ φ.source ∧
      (∀ y ∈ φ.source, y ∈ cutSet_C2a F ↔ 0 ≤ φ y 0) ∧
      φ (F.collar i (t0, ε/2)) 0 = 0 := by
  let sh : PartialDiffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞ :=
    (heightAffine_C2a ε hε).toPartialDiffeomorph.restrict {s | 0 < ε * s}
      (isOpen_lt continuous_const (continuous_const.mul continuous_id))
  let ch := DifferentialGeometry.Topology.PartialDiffeomorph.extendedChart (I := torusModel) t0
  let pc := DifferentialGeometry.Topology.PartialDiffeomorph.prod ch sh
  let φ : PartialDiffeomorph (𝓡 3) (𝓡 3) N E3 ∞ :=
    (((F.collar i).symm.trans pc).trans coordDiffeo_C2a.toPartialDiffeomorph)
  have hform : ∀ y ∈ φ.source, ∃ p ∈ signedCollarSource, F.collar i p = y ∧ 0 < ε * p.2 ∧
      φ y 0 = ε * p.2 - 1/2 := by
    intro y hy
    have h1 : y ∈ (F.collar i).target := hy.1.1
    have h2 : (F.collar i).symm y ∈ pc.source := hy.1.2
    refine ⟨(F.collar i).symm y, ?_, (F.collar i).right_inv h1, ?_, ?_⟩
    · have := (F.collar i).map_target h1
      rwa [F.source_eq] at this
    · exact h2.2.2
    · change coordEquiv_C2a ((ch ((F.collar i).symm y).1), (heightAffine_C2a ε hε ((F.collar i).symm y).2)) 0 = _
      rfl
  have hp0 : (t0, ε/2) ∈ signedCollarSource := by
    rcases hε with rfl | rfl <;> exact ⟨by norm_num, by norm_num⟩
  have hsrc : F.collar i (t0, ε/2) ∈ φ.source := by
    have h1 : F.collar i (t0, ε/2) ∈ (F.collar i).target :=
      (F.collar i).map_source (by rw [F.source_eq]; exact hp0)
    have hs : (F.collar i).symm (F.collar i (t0, ε/2)) = (t0, ε/2) :=
      (F.collar i).left_inv (by rw [F.source_eq]; exact hp0)
    have h2 : (F.collar i).symm (F.collar i (t0, ε/2)) ∈ pc.source := by
      rw [hs]
      refine ⟨mem_extChartAt_source t0, trivial, ?_⟩
      change 0 < ε * (ε / 2)
      rcases hε with rfl | rfl <;> norm_num
    exact ⟨⟨h1, h2⟩, trivial⟩
  refine ⟨φ, hsrc, ?_, ?_⟩
  · intro y hy
    obtain ⟨p, hp, rfl, hpos, hv⟩ := hform y hy
    rw [hv]
    have hiff : F.collar i p ∈ cutSet_C2a F ↔ ¬ (-1/2 < p.2 ∧ p.2 < 1/2) := by
      simp only [cutSet_C2a, mem_compl_iff, mem_iUnion, not_exists]
      constructor
      · intro h
        exact (collar_mem_tubeOpen_iff_C2a i hp).not.mp (h i)
      · intro h j
        by_cases hj : j = i
        · subst hj; exact (collar_mem_tubeOpen_iff_C2a j hp).not.mpr h
        · exact collar_not_mem_tube_other_C2a hj ((F.collar i).map_source (by rw [F.source_eq]; exact hp))
    rw [hiff]
    rcases hε with rfl | rfl
    · simp only [one_mul] at hpos ⊢
      constructor
      · intro h; by_contra h'; apply h; constructor <;> linarith
      · intro h h'; linarith [h'.2]
    · simp only [neg_mul, one_mul] at hpos ⊢
      constructor
      · intro h; by_contra h'; apply h; constructor <;> linarith
      · intro h h'; linarith [h'.1]
  · have hs : (F.collar i).symm (F.collar i (t0, ε/2)) = (t0, ε/2) :=
      (F.collar i).left_inv (by rw [F.source_eq]; exact hp0)
    change coordEquiv_C2a (ch ((F.collar i).symm (F.collar i (t0, ε/2))).1,
      heightAffine_C2a ε hε ((F.collar i).symm (F.collar i (t0, ε/2))).2) 0 = 0
    rw [hs]
    change ε * (ε / 2) - 1/2 = 0
    rcases hε with rfl | rfl <;> norm_num

/-- Every point of the cut region has a chart in which the region is `{x₀ ≥ 0}`; the point is a
boundary point of the region iff it lies on a cut torus. -/
theorem exists_cut_chart_C2a [T2Space N] (x : N) (hx : x ∈ cutSet_C2a F) :
    ∃ φ : PartialDiffeomorph (𝓡 3) (𝓡 3) N E3 ∞,
      x ∈ φ.source ∧ (∀ y ∈ φ.source, y ∈ cutSet_C2a F ↔ 0 ≤ φ y 0) ∧
      (x ∈ cutInt_C2a F → 0 < φ x 0) ∧ (x ∉ cutInt_C2a F → φ x 0 = 0) := by
  by_cases hint : x ∈ cutInt_C2a F
  · obtain ⟨φ, hxφ, hsub, hpos⟩ := exists_positive_chart_C2a isOpen_cutInt_C2a hint
    refine ⟨φ, hxφ, fun y hy => ?_, fun _ => hpos x hxφ, fun h => absurd hint h⟩
    exact ⟨fun _ => (hpos y hy).le, fun _ => cutInt_subset_cutSet_C2a (hsub hy)⟩
  · obtain ⟨i, p, hp, rfl, hp2⟩ := exists_boundary_param_C2a hx hint
    obtain ⟨t0, s0⟩ := p
    have hε : ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ s0 = ε / 2 := by
      rcases hp2 with h | h
      · exact ⟨1, Or.inl rfl, by change s0 = 1/2 at h; rw [h]⟩
      · exact ⟨-1, Or.inr rfl, by change s0 = -1/2 at h; rw [h]⟩
    obtain ⟨ε, hε1, rfl⟩ := hε
    obtain ⟨φ, hxφ, hiff, hzero⟩ := exists_boundary_chart_C2a F i ε hε1 t0
    exact ⟨φ, hxφ, hiff, fun h => absurd h hint, fun _ => hzero⟩

end BoundaryChart

section Atlas

variable {N : Type*} [TopologicalSpace N] [ChartedSpace E3 N] [IsManifold (𝓡 3) ∞ N] [T2Space N]
  (F : CollaredTorusFamily_C2a N)

/-- The smooth boundary atlas of the cut region `N ∖ ⋃ tubes`. -/
def cutAtlas_C2a : SmoothBoundaryAtlas (𝓡 3) 3 (cutSet_C2a F) where
  ambientChart x := Classical.choose (exists_cut_chart_C2a F x.1 x.2)
  mem_source x := (Classical.choose_spec (exists_cut_chart_C2a F x.1 x.2)).1
  mem_iff x := (Classical.choose_spec (exists_cut_chart_C2a F x.1 x.2)).2.1

theorem cutAtlas_zero_iff_C2a (x : cutSet_C2a F) :
    (cutAtlas_C2a F).ambientChart x x.1 0 = 0 ↔ x.1 ∉ cutInt_C2a F := by
  have h := Classical.choose_spec (exists_cut_chart_C2a F x.1 x.2)
  by_cases hx : x.1 ∈ cutInt_C2a F
  · have := h.2.2.1 hx
    exact ⟨fun h0 => absurd h0 this.ne', fun h' => absurd hx h'⟩
  · exact ⟨fun _ => hx, fun _ => h.2.2.2 hx⟩

end Atlas

section Carrier

variable {M : ConnectedClosedOrientedManifold.{u} 3} (F : CollaredTorusFamily_C2a M.Carrier)

/-- **S1: the cut carrier.** `K = M ∖ ⋃ σ_i(T² × (-1/2,1/2))` as a compact oriented 3-manifold with
boundary. -/
def cutCarrier_C2a : CompactCarrier.{u} :=
  letI : SecondCountableTopology M.Carrier :=
    ChartedSpace.secondCountable_of_sigmaCompact (EuclideanSpace ℝ (Fin 3)) M.Carrier
  letI : CompactSpace (cutSet_C2a F) := isCompact_iff_compactSpace.mp isClosed_cutSet_C2a.isCompact
  { kind := .withBoundary
    Carrier := cutSet_C2a F
    charts := (cutAtlas_C2a F).toChartedSpace
    smooth := (cutAtlas_C2a F).isManifold
    secondCountable := inferInstance
    orientation := (cutAtlas_C2a F).orientation M.orientation }

/-- The inclusion of the cut carrier into `M`. -/
def cutIncl_C2a : (cutCarrier_C2a F).Carrier → M.Carrier := Subtype.val

theorem cutCarrier_kind_C2a : (cutCarrier_C2a F).kind = .withBoundary := rfl

theorem cutIncl_range_C2a : range (cutIncl_C2a F) = cutSet_C2a F := Subtype.range_coe

theorem cutIncl_isSmoothEmbedding_C2a :
    IsSmoothEmbedding (cutCarrier_C2a F).model (𝓡 3) ∞ (cutIncl_C2a F) :=
  (cutAtlas_C2a F).isSmoothEmbedding_subtype_val

theorem cutIncl_mfderiv_bijective_C2a (x : (cutCarrier_C2a F).Carrier) :
    Function.Bijective (mfderiv (cutCarrier_C2a F).model (𝓡 3) (cutIncl_C2a F) x) :=
  (cutAtlas_C2a F).mfderiv_subtypeVal_bijective x

theorem cutIncl_oriented_C2a (x : (cutCarrier_C2a F).Carrier) :
    ∃ D : TangentSpace (cutCarrier_C2a F).model x ≃L[ℝ]
        TangentSpace (𝓡 3) (cutIncl_C2a F x),
      D.toContinuousLinearMap = mfderiv (cutCarrier_C2a F).model (𝓡 3) (cutIncl_C2a F) x ∧
      Orientation.map (Fin 3) D.toLinearEquiv ((cutCarrier_C2a F).orientation.orientation x) =
        M.orientation.orientation (cutIncl_C2a F x) :=
  ⟨(cutAtlas_C2a F).inclusionDifferentialEquiv x, rfl,
    (cutAtlas_C2a F).orientation_map_inclusion M.orientation x⟩

/-- Boundary points of the cut carrier are exactly the points on the cut tori. -/
theorem cutIncl_boundary_C2a (x : (cutCarrier_C2a F).Carrier) :
    x ∈ (cutCarrier_C2a F).model.boundary (cutCarrier_C2a F).Carrier ↔ x.1 ∉ cutInt_C2a F :=
  ((cutAtlas_C2a F).isBoundaryPoint_iff x).trans (cutAtlas_zero_iff_C2a F x)

theorem cutIncl_boundary_iff_C2a (x : (cutCarrier_C2a F).Carrier) :
    x ∈ (cutCarrier_C2a F).model.boundary (cutCarrier_C2a F).Carrier ↔
      ∃ i, (∃ t, x.1 = F.collar i (t, 1/2)) ∨ (∃ t, x.1 = F.collar i (t, -1/2)) := by
  rw [cutIncl_boundary_C2a]
  constructor
  · intro h
    obtain ⟨i, ⟨t, s⟩, hp, hx, hs⟩ := exists_boundary_param_C2a x.2 h
    refine ⟨i, ?_⟩
    rcases hs with hs | hs
    · exact Or.inl ⟨t, by rw [← hx]; exact congrArg _ (Prod.ext rfl hs)⟩
    · exact Or.inr ⟨t, by rw [← hx]; exact congrArg _ (Prod.ext rfl hs)⟩
  · rintro ⟨i, ⟨t, ht⟩ | ⟨t, ht⟩⟩
    · rw [ht]; exact collar_pm_not_mem_cutInt_C2a i t (Or.inl rfl)
    · rw [ht]; exact collar_pm_not_mem_cutInt_C2a i t (Or.inr rfl)

end Carrier

end GC.LongTime.Ch12
