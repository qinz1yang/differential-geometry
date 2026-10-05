import DifferentialGeometry.Geometry.Collapse.ZeroModel.ZeroModelRowEnds
import DifferentialGeometry.Geometry.Collapse.ZeroModel.ZeroModelRowLFR51
import DifferentialGeometry.Geometry.Collapse.ZeroModel.PuncturedRP3ZeroModelApplications
import DifferentialGeometry.Geometry.Collapse.ZeroModel.KleinZeroModelApplications
import DifferentialGeometry.Topology.VectorBundle.SphereBundleEndsApplications

/-!
# Row LFR52: explicit twisted cores and their ends

Lane LFR54-ROW, group G3. Frozen blueprint master207A, LFR52
(`lem:collapse-twisted-core-identifications`, A:29380–29437):

"In (LFR51.1), `D(o(ℝP²))` is diffeomorphic, including boundary, to `ℝP³ ∖ int D³`. The bundle
`D(o(K))` is the orientable twisted interval bundle over the Klein bottle and has one torus boundary
component. The first, second, fifth and sixth total spaces in (LFR51.1) have one end; the third and
fourth have two ends."

The row `lfr52_twisted_core_identifications_and_ends` is the conjunction of
1. (`ℝP²` clause) for an antipodal unit map (row five of LFR51): `D(V)` embeds smoothly in the fixed
   `ℝP³` (`projectiveThreeSpaceLift`) onto the complement of an open oriented ball chart, its boundary
   unit sphere bundle going exactly onto the boundary sphere `c.chart '' S²`, which is `ν(S²)` through
   a homeomorphism `S² ≃ₜ c.chart '' S²` (`exists_puncturedRP3_embedding_sphere_of_antipodal_unit_map`);
2. (Klein clause) for a Klein unit map (row six): `D(V) ≅ {Q ≤ 0} = mobiusBundleSet` (the orientable
   twisted `I`-bundle over the Klein bottle, oriented as a regular sublevel of `L(4, -1)`), boundary
   onto `{Q = 0}`, which is ONE torus: `T² ≃ₜ {Q = 0}` through `ν`
   (`exists_mobiusBundleSet_diffeomorph_torus_of_klein_unit_map`);
3. (ends, LC77's language) rank `≥ 2` (rows one, two) and a unit sphere bundle covered by a connected
   space (rows five, six) give exactly one end; a norm-preserving product `B₀ × ℝ` with `B₀`
   preconnected and nonempty (rows three, four) gives exactly two ends
   (`exactly_two_ends_of_normPreserving_prod`).

Deviation D4 (sheet): "one end" = for every compact `K ⊆ N` an unbounded component of `Kᶜ` exists and
all coincide; "two ends" = some compact `K` has two distinct unbounded components, and for every `K`
any three unbounded components contain two equal ones.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Function Module
open scoped ContDiff Topology Manifold
open DifferentialGeometry.Topology.Morse

namespace DifferentialGeometry.Geometry.Collapse.ZeroModel

open DifferentialGeometry.Topology DifferentialGeometry.Topology.VectorBundle
open DifferentialGeometry.Topology.VectorBundle.RankOneQuotient

universe u uB uF uV uN uS

local notation "E1" => EuclideanSpace ℝ (Fin 1)
local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "S2" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
local notation "T2" => AddCircle (1 : ℝ) × AddCircle (1 : ℝ)

section Twisted

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {B : Type*} [TopologicalSpace B] [ChartedSpace E2 B] [IsManifold (𝓡 2) ∞ B]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ b, NormedAddCommGroup (V b)] [∀ b, InnerProductSpace ℝ (V b)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V (𝓡 2)]
  [IsContMDiffRiemannianBundle (𝓡 2) ∞ F V]

/-- **LFR52, `ℝP²` clause.** For an antipodal unit map the closed unit disc bundle (native boundary
charts) embeds smoothly in `ℝP³` onto the complement of an open oriented ball chart; the boundary
unit sphere bundle goes exactly onto the boundary sphere, and `x ↦ f (ν x)` is a homeomorphism of
`S²` onto that boundary sphere. -/
theorem exists_puncturedRP3_embedding_sphere_of_antipodal_unit_map
    (hd : finrank ℝ (E2 × F) = 2 + 1)
    (ν : S2 → TotalSpace F V) (hν : ContMDiff (𝓡 2) ((𝓡 2).prod 𝓘(ℝ, F)) ∞ ν)
    (hνS : ∀ x, ‖(ν x).2‖ = 1) (hνinj : Injective ν)
    (hνsurj : ∀ z : TotalSpace F V, ‖z.2‖ = 1 → ∃ x, ν x = z)
    (hνneg : ∀ x, ν (-x) = ⟨(ν x).proj, -(ν x).2⟩)
    (hνloc : IsLocalDiffeomorph (𝓡 2) (𝓡 2) ∞ (fun x => (ν x).proj)) :
    letI := normClosedDiscBundleChartedSpace (IB := 𝓡 2) (V := V) hd 1 one_pos
    ∃ (c : OrientedBallChart projectiveThreeSpaceLift.{u}.toClosedOrientedManifold)
      (f : {z : TotalSpace F V // ‖z.2‖ ≤ 1} → projectiveThreeSpaceLift.{u}.Carrier),
      IsSmoothEmbedding (morseModelWithCornersHalfSpace 2) (𝓡 3) ∞ f ∧
      range f = {x | x ∉ c.chart '' Metric.ball (0 : E3) 1} ∧
      (∀ z, f z ∈ c.chart '' Metric.sphere (0 : E3) 1 ↔ ‖z.val.2‖ = 1) ∧
      ∃ j : S2 ≃ₜ (c.chart '' Metric.sphere (0 : E3) 1 : Set projectiveThreeSpaceLift.{u}.Carrier),
        ∀ x, (j x).val = f ⟨ν x, (hνS x).le⟩ := by
  let csNorm_LFR54ROW := normClosedDiscBundleChartedSpace (IB := 𝓡 2) (V := V) hd 1 one_pos
  obtain ⟨c, f, hf, hrange, hbd⟩ :=
    exists_puncturedRP3_embedding_boundary_of_antipodal_unit_map.{u} hd ν hν hνS hνinj hνsurj
      hνneg hνloc
  refine ⟨c, f, hf, hrange, hbd, ?_⟩
  let g : S2 → (c.chart '' Metric.sphere (0 : E3) 1 : Set projectiveThreeSpaceLift.{u}.Carrier) :=
    fun x => ⟨f ⟨ν x, (hνS x).le⟩, (hbd ⟨ν x, (hνS x).le⟩).mpr (hνS x)⟩
  have hg : Continuous g :=
    (hf.contMDiff.continuous.comp (hν.continuous.subtype_mk _)).subtype_mk _
  have hginj : Injective g := by
    intro x y hxy
    have h := hf.isEmbedding.injective (congrArg Subtype.val hxy)
    exact hνinj (congrArg Subtype.val h)
  have hgsurj : Surjective g := by
    rintro ⟨y, hy⟩
    have hyr : y ∈ range f := by
      rw [hrange]
      rintro ⟨w, hw, hwy⟩
      obtain ⟨w', hw', hw'y⟩ := hy
      have hw'2 : w' ∈ c.chart.source := c.closedBall_subset_source (by
        rw [Metric.mem_closedBall]
        rw [Metric.mem_sphere] at hw'
        linarith)
      have hw2 : w ∈ c.chart.source := c.closedBall_subset_source (by
        rw [Metric.mem_closedBall]
        rw [Metric.mem_ball] at hw
        linarith)
      have := c.chart.toPartialEquiv.injOn hw'2 hw2 (hw'y.trans hwy.symm)
      rw [this, Metric.mem_sphere] at hw'
      rw [Metric.mem_ball] at hw
      linarith
    obtain ⟨z, rfl⟩ := hyr
    have hz : ‖z.val.2‖ = 1 := (hbd z).mp hy
    obtain ⟨x, hx⟩ := hνsurj z.val hz
    refine ⟨x, Subtype.ext ?_⟩
    change f ⟨ν x, _⟩ = f z
    congr 1
    exact Subtype.ext hx
  exact ⟨hg.homeoOfEquivCompactToT2 (f := Equiv.ofBijective g ⟨hginj, hgsurj⟩), fun x => rfl⟩

/-- **LFR52, Klein clause.** For a Klein unit map the closed unit disc bundle (native boundary charts)
is diffeomorphic to `{Q ≤ 0} = mobiusBundleSet` (the orientable twisted `I`-bundle over the Klein
bottle; it carries the orientation of `L(4, -1)`), the boundary unit sphere bundle going exactly
onto `{Q = 0}`, and `p ↦ Φ (ν p)` is a homeomorphism of the torus onto `{Q = 0}`: ONE torus
boundary component. -/
theorem exists_mobiusBundleSet_diffeomorph_torus_of_klein_unit_map
    (hd : finrank ℝ (E2 × F) = 2 + 1)
    (ν : T2 → TotalSpace F V) (hν : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, F)) ∞ ν)
    (hνS : ∀ p, ‖(ν p).2‖ = 1) (hνinj : Injective ν)
    (hνsurj : ∀ z : TotalSpace F V, ‖z.2‖ = 1 → ∃ p, ν p = z)
    (hνneg : ∀ x y : AddCircle (1 : ℝ),
      ν (x + ((1 / 2 : ℝ) : AddCircle (1 : ℝ)), -y) = ⟨(ν (x, y)).proj, -(ν (x, y)).2⟩)
    (hνloc : IsLocalDiffeomorph (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓡 2) ∞ (fun p => (ν p).proj)) :
    letI := normClosedDiscBundleChartedSpace (IB := 𝓡 2) (V := V) hd 1 one_pos
    Nonempty (ManifoldOrientation (𝓡∂ 3) GC.Seifert.mobiusBundleSet.{u} 3) ∧
    ∃ Φ : Diffeomorph (morseModelWithCornersHalfSpace 2) (𝓡∂ 3)
        {z : TotalSpace F V // ‖z.2‖ ≤ 1} GC.Seifert.mobiusBundleSet.{u} ∞,
      (∀ z, ‖z.val.2‖ = 1 ↔ GC.Seifert.mobiusBundleFunction (Φ z).val = 0) ∧
      ∃ j : T2 ≃ₜ {y : GC.Seifert.mobiusBundleSet.{u} // GC.Seifert.mobiusBundleFunction y.val = 0},
        ∀ p, (j p).val = Φ ⟨ν p, (hνS p).le⟩ := by
  let csNorm_LFR54ROW := normClosedDiscBundleChartedSpace (IB := 𝓡 2) (V := V) hd 1 one_pos
  obtain ⟨Φ, hΦ⟩ :=
    exists_mobiusBundleSet_diffeomorph_boundary_of_klein_unit_map.{u} hd ν hν hνS hνinj hνsurj
      hνneg hνloc
  refine ⟨⟨GC.Seifert.mobiusBundleCarrier.{u}.orientation⟩, Φ, hΦ, ?_⟩
  let g : T2 → {y : GC.Seifert.mobiusBundleSet.{u} // GC.Seifert.mobiusBundleFunction y.val = 0} :=
    fun p => ⟨Φ ⟨ν p, (hνS p).le⟩, (hΦ ⟨ν p, (hνS p).le⟩).mp (hνS p)⟩
  have hg : Continuous g :=
    (Φ.continuous.comp (hν.continuous.subtype_mk _)).subtype_mk _
  have hginj : Injective g := by
    intro p q hpq
    have h := Φ.injective (congrArg Subtype.val hpq)
    exact hνinj (congrArg Subtype.val h)
  have hgsurj : Surjective g := by
    rintro ⟨y, hy⟩
    have hz : ‖(Φ.symm y).val.2‖ = 1 := by
      rw [hΦ, Diffeomorph.apply_symm_apply]
      exact hy
    obtain ⟨p, hp⟩ := hνsurj (Φ.symm y).val hz
    refine ⟨p, Subtype.ext ?_⟩
    change Φ ⟨ν p, _⟩ = y
    have : (⟨ν p, (hνS p).le⟩ : {z : TotalSpace F V // ‖z.2‖ ≤ 1}) = Φ.symm y := Subtype.ext hp
    rw [this, Diffeomorph.apply_symm_apply]
  exact ⟨hg.homeoOfEquivCompactToT2 (f := Equiv.ofBijective g ⟨hginj, hgsurj⟩), fun p => rfl⟩

end Twisted

section Ends

variable {B : Type*} [TopologicalSpace B] [CompactSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ b, NormedAddCommGroup (V b)] [∀ b, InnerProductSpace ℝ (V b)]
  [FiberBundle F V] [VectorBundle ℝ F V] [IsContinuousRiemannianBundle F V]
  {N : Type*} [MetricSpace N] [ProperSpace N]

/-- In `ℝ¹` a vector of norm one is `± e₀`. -/
theorem eq_single_or_eq_neg_single_of_norm_eq_one {w : E1} (hw : ‖w‖ = 1) :
    w = EuclideanSpace.single 0 1 ∨ w = -EuclideanSpace.single 0 1 := by
  have hn : ‖w‖ = |w 0| := by
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_one, Real.norm_eq_abs, sq_abs, Real.sqrt_sq_eq_abs]
  rw [hn] at hw
  rcases abs_eq (zero_le_one' ℝ) |>.mp hw with h | h
  · left
    ext i
    fin_cases i
    simp [h]
  · right
    ext i
    fin_cases i
    simp [h]

/-- **Two ends of a norm-preserving product `B₀ × ℝ`** (rows `S² × ℝ`, `T² × ℝ` of (LFR51.1)). -/
theorem exactly_two_ends_of_normPreserving_prod {B₀ : Type*} [TopologicalSpace B₀]
    [PreconnectedSpace B₀] [Nonempty B₀] (Ψ : (B₀ × E1) ≃ₜ TotalSpace F V)
    (hΨ : ∀ z, ‖(Ψ z).2‖ = ‖z.2‖) (e : TotalSpace F V ≃ₜ N) :
    (∃ K : Set N, IsCompact K ∧ ∃ a b : N,
      ¬ Bornology.IsBounded (connectedComponentIn Kᶜ a) ∧
      ¬ Bornology.IsBounded (connectedComponentIn Kᶜ b) ∧
      connectedComponentIn Kᶜ a ≠ connectedComponentIn Kᶜ b) ∧
    ∀ K : Set N, IsCompact K → ∀ a b c : N,
      ¬ Bornology.IsBounded (connectedComponentIn Kᶜ a) →
      ¬ Bornology.IsBounded (connectedComponentIn Kᶜ b) →
      ¬ Bornology.IsBounded (connectedComponentIn Kᶜ c) →
      connectedComponentIn Kᶜ a = connectedComponentIn Kᶜ b ∨
      connectedComponentIn Kᶜ a = connectedComponentIn Kᶜ c ∨
      connectedComponentIn Kᶜ b = connectedComponentIn Kᶜ c := by
  set u : E1 := EuclideanSpace.single 0 1 with hu
  have hun : ‖u‖ = 1 := by simp [hu]
  have hu0 : u 0 = 1 := by simp [hu]
  let P : Set (TotalSpace F V) := Ψ '' (univ ×ˢ {u})
  let Q : Set (TotalSpace F V) := Ψ '' (univ ×ˢ {-u})
  have hP : IsPreconnected P :=
    (isPreconnected_univ.prod isPreconnected_singleton).image _ Ψ.continuous.continuousOn
  have hQ : IsPreconnected Q :=
    (isPreconnected_univ.prod isPreconnected_singleton).image _ Ψ.continuous.continuousOn
  have hPQ : {z : TotalSpace F V | ‖z.2‖ = 1} = P ∪ Q := by
    ext z
    constructor
    · intro hz
      have hw : ‖(Ψ.symm z).2‖ = 1 := by
        rw [← hΨ (Ψ.symm z), Homeomorph.apply_symm_apply]
        exact hz
      rcases eq_single_or_eq_neg_single_of_norm_eq_one hw with h | h
      · exact Or.inl ⟨Ψ.symm z, ⟨mem_univ _, h⟩, Ψ.apply_symm_apply z⟩
      · exact Or.inr ⟨Ψ.symm z, ⟨mem_univ _, h⟩, Ψ.apply_symm_apply z⟩
    · rintro (⟨w, ⟨-, hw⟩, rfl⟩ | ⟨w, ⟨-, hw⟩, rfl⟩)
      · change ‖(Ψ w).2‖ = 1
        rw [hΨ, mem_singleton_iff.mp hw, hun]
      · change ‖(Ψ w).2‖ = 1
        rw [hΨ, mem_singleton_iff.mp hw, norm_neg, hun]
  have hnc : ¬ IsPreconnected {z : TotalSpace F V | ‖z.2‖ = 1} := by
    intro hS
    let g : TotalSpace F V → ℝ := fun z => (Ψ.symm z).2 0
    have hgc : Continuous g :=
      ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp continuous_snd).comp Ψ.symm.continuous
    obtain ⟨b₀⟩ := (inferInstance : Nonempty B₀)
    have h1 : (1 : ℝ) ∈ g '' {z : TotalSpace F V | ‖z.2‖ = 1} :=
      ⟨Ψ (b₀, u), by change ‖(Ψ (b₀, u)).2‖ = 1; rw [hΨ, hun], by
        simp only [g, Homeomorph.symm_apply_apply, hu0]⟩
    have h2 : (-1 : ℝ) ∈ g '' {z : TotalSpace F V | ‖z.2‖ = 1} :=
      ⟨Ψ (b₀, -u), by change ‖(Ψ (b₀, -u)).2‖ = 1; rw [hΨ, norm_neg, hun], by
        simp only [g, Homeomorph.symm_apply_apply, PiLp.neg_apply, hu0]⟩
    have h0 : (0 : ℝ) ∈ g '' {z : TotalSpace F V | ‖z.2‖ = 1} :=
      (hS.image g hgc.continuousOn).Icc_subset h2 h1 ⟨by norm_num, by norm_num⟩
    obtain ⟨z, hz, hz0⟩ := h0
    have hw : ‖(Ψ.symm z).2‖ = 1 := by
      rw [← hΨ (Ψ.symm z), Homeomorph.apply_symm_apply]
      exact hz
    rcases eq_single_or_eq_neg_single_of_norm_eq_one hw with h | h
    · have : g z = 1 := by
        simp only [g, h, ← hu, hu0]
      linarith
    · have : g z = -1 := by
        simp only [g, h, ← hu, PiLp.neg_apply, hu0]
      linarith
  exact exactly_two_ends_of_sphereBundle_eq_union e hP hQ hPQ hnc

/-- **One end of a unit sphere bundle covered by a connected space** (rows `o(ℝP²)`, `o(K)`). -/
theorem exactly_one_end_of_connected_unit_cover {Sc : Type*}
    [TopologicalSpace Sc] [ConnectedSpace Sc] (ν : Sc → TotalSpace F V) (hν : Continuous ν)
    (hνS : ∀ p, ‖(ν p).2‖ = 1) (hνsurj : ∀ z : TotalSpace F V, ‖z.2‖ = 1 → ∃ p, ν p = z)
    (e : TotalSpace F V ≃ₜ N) :
    ∀ K : Set N, IsCompact K →
      (∃ a : N, ¬ Bornology.IsBounded (connectedComponentIn Kᶜ a)) ∧
      ∀ a b : N, ¬ Bornology.IsBounded (connectedComponentIn Kᶜ a) →
        ¬ Bornology.IsBounded (connectedComponentIn Kᶜ b) →
        connectedComponentIn Kᶜ a = connectedComponentIn Kᶜ b := by
  have hrange : {z : TotalSpace F V | ‖z.2‖ = 1} = range ν := by
    ext z
    exact ⟨fun hz => hνsurj z hz, by rintro ⟨p, rfl⟩; exact hνS p⟩
  apply exactly_one_end_of_isConnected_sphereBundle e
  rw [hrange]
  exact isConnected_range hν

omit [CompactSpace B] in
/-- **One end in rank at least two** (rows `ℝ³`, `S¹ × ℝ²`). -/
theorem exactly_one_end_of_one_lt_finrank [CompactSpace B] [ConnectedSpace B]
    (hF : 1 < finrank ℝ F) (e : TotalSpace F V ≃ₜ N) :
    ∀ K : Set N, IsCompact K →
      (∃ a : N, ¬ Bornology.IsBounded (connectedComponentIn Kᶜ a)) ∧
      ∀ a b : N, ¬ Bornology.IsBounded (connectedComponentIn Kᶜ a) →
        ¬ Bornology.IsBounded (connectedComponentIn Kᶜ b) →
        connectedComponentIn Kᶜ a = connectedComponentIn Kᶜ b :=
  exactly_one_end_of_isConnected_sphereBundle e (isConnected_sphereBundle_of_one_lt_finrank hF)

end Ends

/-- **Row LFR52 (explicit twisted cores and their ends).**
1. `ℝP²` row: `D(o(ℝP²))` embeds smoothly in `ℝP³` onto the complement of an open oriented ball
   chart, boundary onto the boundary sphere `≃ₜ S²` (through `ν`);
2. Klein row: `D(o(K)) ≅ {Q ≤ 0}` (oriented twisted `I`-bundle over `K`), boundary onto `{Q = 0}`,
   ONE torus `T² ≃ₜ {Q = 0}` (through `ν`);
3. rank `≥ 2` over a compact connected base: exactly one end (rows one, two);
4. rank one with the unit sphere bundle covered by a connected space (`S²` resp. `T²` through the
   unit map): exactly one end (rows five, six);
5. a norm-preserving product `B₀ × ℝ`, `B₀` preconnected nonempty: exactly two ends (rows three,
   four). -/
theorem lfr52_twisted_core_identifications_and_ends :
    (∀ {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
      {B : Type uB} [TopologicalSpace B] [ChartedSpace E2 B] [IsManifold (𝓡 2) ∞ B]
      {V : B → Type uV} [TopologicalSpace (TotalSpace F V)]
      [∀ b, NormedAddCommGroup (V b)] [∀ b, InnerProductSpace ℝ (V b)]
      [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V (𝓡 2)]
      [IsContMDiffRiemannianBundle (𝓡 2) ∞ F V]
      (hd : finrank ℝ (E2 × F) = 2 + 1) (ν : S2 → TotalSpace F V),
      ContMDiff (𝓡 2) ((𝓡 2).prod 𝓘(ℝ, F)) ∞ ν → ∀ (hνS : ∀ x, ‖(ν x).2‖ = 1), Injective ν →
      (∀ z : TotalSpace F V, ‖z.2‖ = 1 → ∃ x, ν x = z) →
      (∀ x, ν (-x) = ⟨(ν x).proj, -(ν x).2⟩) →
      IsLocalDiffeomorph (𝓡 2) (𝓡 2) ∞ (fun x => (ν x).proj) →
      letI := normClosedDiscBundleChartedSpace (IB := 𝓡 2) (V := V) hd 1 one_pos
      ∃ (c : OrientedBallChart projectiveThreeSpaceLift.{u}.toClosedOrientedManifold)
        (f : {z : TotalSpace F V // ‖z.2‖ ≤ 1} → projectiveThreeSpaceLift.{u}.Carrier),
        IsSmoothEmbedding (morseModelWithCornersHalfSpace 2) (𝓡 3) ∞ f ∧
        range f = {x | x ∉ c.chart '' Metric.ball (0 : E3) 1} ∧
        (∀ z, f z ∈ c.chart '' Metric.sphere (0 : E3) 1 ↔ ‖z.val.2‖ = 1) ∧
        ∃ j : S2 ≃ₜ (c.chart '' Metric.sphere (0 : E3) 1 : Set projectiveThreeSpaceLift.{u}.Carrier),
          ∀ x, (j x).val = f ⟨ν x, (hνS x).le⟩) ∧
    (∀ {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
      {B : Type uB} [TopologicalSpace B] [ChartedSpace E2 B] [IsManifold (𝓡 2) ∞ B]
      {V : B → Type uV} [TopologicalSpace (TotalSpace F V)]
      [∀ b, NormedAddCommGroup (V b)] [∀ b, InnerProductSpace ℝ (V b)]
      [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V (𝓡 2)]
      [IsContMDiffRiemannianBundle (𝓡 2) ∞ F V]
      (hd : finrank ℝ (E2 × F) = 2 + 1) (ν : T2 → TotalSpace F V),
      ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, F)) ∞ ν →
      ∀ (hνS : ∀ p, ‖(ν p).2‖ = 1), Injective ν →
      (∀ z : TotalSpace F V, ‖z.2‖ = 1 → ∃ p, ν p = z) →
      (∀ x y : AddCircle (1 : ℝ),
        ν (x + ((1 / 2 : ℝ) : AddCircle (1 : ℝ)), -y) = ⟨(ν (x, y)).proj, -(ν (x, y)).2⟩) →
      IsLocalDiffeomorph (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓡 2) ∞ (fun p => (ν p).proj) →
      letI := normClosedDiscBundleChartedSpace (IB := 𝓡 2) (V := V) hd 1 one_pos
      Nonempty (ManifoldOrientation (𝓡∂ 3) GC.Seifert.mobiusBundleSet.{u} 3) ∧
      ∃ Φ : Diffeomorph (morseModelWithCornersHalfSpace 2) (𝓡∂ 3)
          {z : TotalSpace F V // ‖z.2‖ ≤ 1} GC.Seifert.mobiusBundleSet.{u} ∞,
        (∀ z, ‖z.val.2‖ = 1 ↔ GC.Seifert.mobiusBundleFunction (Φ z).val = 0) ∧
        ∃ j : T2 ≃ₜ {y : GC.Seifert.mobiusBundleSet.{u} // GC.Seifert.mobiusBundleFunction y.val = 0},
          ∀ p, (j p).val = Φ ⟨ν p, (hνS p).le⟩) ∧
    (∀ {B : Type uB} [TopologicalSpace B] [CompactSpace B] [ConnectedSpace B]
      {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
      {V : B → Type uV} [TopologicalSpace (TotalSpace F V)]
      [∀ b, NormedAddCommGroup (V b)] [∀ b, InnerProductSpace ℝ (V b)]
      [FiberBundle F V] [VectorBundle ℝ F V] [IsContinuousRiemannianBundle F V]
      {N : Type uN} [MetricSpace N] [ProperSpace N],
      1 < finrank ℝ F → TotalSpace F V ≃ₜ N → ∀ K : Set N, IsCompact K →
      (∃ a : N, ¬ Bornology.IsBounded (connectedComponentIn Kᶜ a)) ∧
      ∀ a b : N, ¬ Bornology.IsBounded (connectedComponentIn Kᶜ a) →
        ¬ Bornology.IsBounded (connectedComponentIn Kᶜ b) →
        connectedComponentIn Kᶜ a = connectedComponentIn Kᶜ b) ∧
    (∀ {B : Type uB} [TopologicalSpace B] [CompactSpace B]
      {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
      {V : B → Type uV} [TopologicalSpace (TotalSpace F V)]
      [∀ b, NormedAddCommGroup (V b)] [∀ b, InnerProductSpace ℝ (V b)]
      [FiberBundle F V] [VectorBundle ℝ F V] [IsContinuousRiemannianBundle F V]
      {N : Type uN} [MetricSpace N] [ProperSpace N]
      {Sc : Type uS} [TopologicalSpace Sc] [ConnectedSpace Sc] (ν : Sc → TotalSpace F V),
      Continuous ν → (∀ p, ‖(ν p).2‖ = 1) → (∀ z : TotalSpace F V, ‖z.2‖ = 1 → ∃ p, ν p = z) →
      TotalSpace F V ≃ₜ N → ∀ K : Set N, IsCompact K →
      (∃ a : N, ¬ Bornology.IsBounded (connectedComponentIn Kᶜ a)) ∧
      ∀ a b : N, ¬ Bornology.IsBounded (connectedComponentIn Kᶜ a) →
        ¬ Bornology.IsBounded (connectedComponentIn Kᶜ b) →
        connectedComponentIn Kᶜ a = connectedComponentIn Kᶜ b) ∧
    (∀ {B : Type uB} [TopologicalSpace B] [CompactSpace B]
      {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
      {V : B → Type uV} [TopologicalSpace (TotalSpace F V)]
      [∀ b, NormedAddCommGroup (V b)] [∀ b, InnerProductSpace ℝ (V b)]
      [FiberBundle F V] [VectorBundle ℝ F V] [IsContinuousRiemannianBundle F V]
      {N : Type uN} [MetricSpace N] [ProperSpace N]
      {B₀ : Type uS} [TopologicalSpace B₀] [PreconnectedSpace B₀] [Nonempty B₀]
      (Ψ : (B₀ × E1) ≃ₜ TotalSpace F V), (∀ z, ‖(Ψ z).2‖ = ‖z.2‖) → TotalSpace F V ≃ₜ N →
      (∃ K : Set N, IsCompact K ∧ ∃ a b : N,
        ¬ Bornology.IsBounded (connectedComponentIn Kᶜ a) ∧
        ¬ Bornology.IsBounded (connectedComponentIn Kᶜ b) ∧
        connectedComponentIn Kᶜ a ≠ connectedComponentIn Kᶜ b) ∧
      ∀ K : Set N, IsCompact K → ∀ a b c : N,
        ¬ Bornology.IsBounded (connectedComponentIn Kᶜ a) →
        ¬ Bornology.IsBounded (connectedComponentIn Kᶜ b) →
        ¬ Bornology.IsBounded (connectedComponentIn Kᶜ c) →
        connectedComponentIn Kᶜ a = connectedComponentIn Kᶜ b ∨
        connectedComponentIn Kᶜ a = connectedComponentIn Kᶜ c ∨
        connectedComponentIn Kᶜ b = connectedComponentIn Kᶜ c) :=
  ⟨fun hd ν hν hνS hνinj hνsurj hνneg hνloc =>
      exists_puncturedRP3_embedding_sphere_of_antipodal_unit_map.{u} hd ν hν hνS hνinj hνsurj hνneg
        hνloc,
    fun hd ν hν hνS hνinj hνsurj hνneg hνloc =>
      exists_mobiusBundleSet_diffeomorph_torus_of_klein_unit_map.{u} hd ν hν hνS hνinj hνsurj hνneg
        hνloc,
    fun hF e => exactly_one_end_of_one_lt_finrank hF e,
    fun ν hν hνS hνsurj e => exactly_one_end_of_connected_unit_cover ν hν hνS hνsurj e,
    fun Ψ hΨ e => exactly_two_ends_of_normPreserving_prod Ψ hΨ e⟩

end DifferentialGeometry.Geometry.Collapse.ZeroModel
