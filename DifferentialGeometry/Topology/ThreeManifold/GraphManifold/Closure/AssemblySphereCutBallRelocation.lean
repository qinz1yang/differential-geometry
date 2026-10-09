import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereCutBallChart
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereCutRelocationApplications
import DifferentialGeometry.Topology.Manifold.AffineBallIsotopy
import DifferentialGeometry.Topology.Manifold.ConnectedInterior
import DifferentialGeometry.Topology.Manifold.InteriorChart

/-!
# Chapter-14 assembly, L2-relative: relocation of an interior cap ball

Lane ASM-L2b, group G2b. The V2 statement `exists_capRelocation_into_fibrePiece`
(`build-logs/scratch/ASM-FIX/AssemblyInterfacesV2.lean:912–924`, review item 6, D9): in a connected
carrier with a raw presentation, a smoothly embedded closed ball in the interior is moved, by a
jointly smooth ambient isotopy that is fixed on an open neighbourhood of the whole boundary, into
the relocation target `capRelocationTarget R j b` of G2a.

* `interiorIsotopy_comp`: two isotopies supported in compact subsets of the interior compose
  pointwise in time (no time concatenation is needed).
* `exists_interiorIsotopy_translate_in_chart`: a compactly supported translation inside a chart.
* `isInteriorPoint_imp_of_chart_moves`: a property of points that propagates along straight
  segments in interior charts holds on the whole interior of a connected manifold.
* `exists_interiorIsotopy_image_subset_of_ballChart`: the image of the closed unit ball of an
  interior ball chart is pushed into any nonempty open subset of the interior (contraction to the
  centre, then chart moves).
* `exists_capRelocation_into_fibrePiece` (V2 text).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

section Isotopy

variable {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] in
/-- Pointwise-in-time composition of two isotopies supported in compact subsets of the interior. -/
theorem interiorIsotopy_comp {Ψ₁ Ψ₂ : ℝ → Diffeomorph I I M M ∞}
    (h₁ : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Ψ₁ q.1 q.2))
    (h₂ : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Ψ₂ q.1 q.2))
    (h₁0 : Ψ₁ 0 = Diffeomorph.refl I M ∞) (h₂0 : Ψ₂ 0 = Diffeomorph.refl I M ∞)
    {K₁ K₂ : Set M} (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂)
    (hK₁I : K₁ ⊆ I.interior M) (hK₂I : K₂ ⊆ I.interior M)
    (hfix₁ : ∀ t x, x ∉ K₁ → Ψ₁ t x = x) (hfix₂ : ∀ t x, x ∉ K₂ → Ψ₂ t x = x) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => ((Ψ₁ q.1).trans (Ψ₂ q.1)) q.2) ∧
      (fun t => (Ψ₁ t).trans (Ψ₂ t)) 0 = Diffeomorph.refl I M ∞ ∧
      ∃ K : Set M, IsCompact K ∧ K ⊆ I.interior M ∧
        ∀ t x, x ∉ K → ((Ψ₁ t).trans (Ψ₂ t)) x = x := by
  refine ⟨?_, ?_, K₁ ∪ K₂, hK₁.union hK₂, union_subset hK₁I hK₂I, ?_⟩
  · exact h₂.comp (contMDiff_fst.prodMk h₁)
  · apply Diffeomorph.ext
    intro x
    change Ψ₂ 0 (Ψ₁ 0 x) = x
    rw [h₁0, h₂0]
    rfl
  · intro t x hx
    change Ψ₂ t (Ψ₁ t x) = x
    rw [hfix₁ t x (fun h => hx (Or.inl h)), hfix₂ t x (fun h => hx (Or.inr h))]

omit [IsManifold I ∞ M] in
/-- A compactly supported translation inside a chart whose image lies in the interior. -/
theorem exists_interiorIsotopy_translate_in_chart
    (φ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞) (hφI : ∀ y ∈ φ.target, I.IsInteriorPoint y)
    {a b : E} {ε δ : ℝ} (hε : 0 ≤ ε) (hεδ : ε < δ)
    (htube : ∀ t ∈ Icc (0 : ℝ) 1, closedBall (a + t • (b - a)) δ ⊆ φ.source) :
    ∃ Ψ : ℝ → Diffeomorph I I M M ∞,
      ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Ψ q.1 q.2) ∧
      Ψ 0 = Diffeomorph.refl I M ∞ ∧
      (∃ K : Set M, IsCompact K ∧ K ⊆ I.interior M ∧ ∀ t x, x ∉ K → Ψ t x = x) ∧
      ∀ y ∈ closedBall a ε, Ψ 1 (φ y) = φ (y + (b - a)) := by
  classical
  obtain ⟨T, hT, hTi, hT0, hT1, K, hK, hKs, hTfix⟩ :=
    DifferentialGeometry.Analysis.exists_compact_isotopy_translate_of_tube hε hεδ htube
  let e := φ.symm.toOpenPartialHomeomorph
  have hKt : K ⊆ e.target := hKs
  obtain ⟨J, hJ, -, hJe, hKi, hKit, hJfix⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_diffeomorph_extension_of_partial_chart_family e
      φ.contMDiffOn_invFun φ.contMDiffOn_toFun T hT hTi hK hKt hTfix
  refine ⟨J, hJ, ?_, ⟨e.symm '' K, hKi, fun y hy => hφI y (hKit hy), fun t x hx =>
    (hJfix t x hx).1⟩, ?_⟩
  · apply Diffeomorph.ext
    intro x
    rw [(hJe 0 x).1, hT0]
    by_cases hx : x ∈ e.source
    · change (if x ∈ e.source then e.symm (e x) else x) = x
      rw [ite_eq_left hx, e.left_inv hx]
    · exact ite_eq_right hx
  · intro y hy
    have hyS : y ∈ φ.source := htube 0 ⟨le_rfl, zero_le_one⟩
      (by simpa only [zero_smul, add_zero] using closedBall_subset_closedBall hεδ.le hy)
    have hφy : φ y ∈ e.source := φ.map_source hyS
    rw [(hJe 1 (φ y)).1]
    rw [show DifferentialGeometry.Topology.Manifold.extendChartById e (T 1) (φ y) =
      e.symm (T 1 (e (φ y))) from ite_eq_left hφy]
    change φ (T 1 (φ.symm (φ y))) = _
    have hi : φ.symm.toPartialEquiv (φ.toPartialEquiv y) = y := φ.left_inv hyS
    rw [hi, hT1 y hy]

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- **Chart moves.** A property of points that passes from `φ a` to `φ b` whenever the segment
from `a` to `b`, thickened by some `δ > 0`, lies in the source of an interior chart `φ`, holds at
every interior point once it holds at one interior point (the interior of a connected manifold is
connected). -/
theorem isInteriorPoint_imp_of_chart_moves [PreconnectedSpace M] {P : M → Prop}
    (hmove : ∀ (φ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞) (a b : E) (δ : ℝ), 0 < δ →
      (∀ y ∈ φ.target, I.IsInteriorPoint y) →
      (∀ t ∈ Icc (0 : ℝ) 1, closedBall (a + t • (b - a)) δ ⊆ φ.source) → P (φ a) → P (φ b))
    {q₀ : M} (hq₀ : I.IsInteriorPoint q₀) (h₀ : P q₀) {q : M} (hq : I.IsInteriorPoint q) :
    P q := by
  -- the interior chart neighbourhood of an interior point, on which `P` is constant
  have hloc : ∀ p : M, I.IsInteriorPoint p → ∃ N : Set M, IsOpen N ∧ p ∈ N ∧
      ∀ p' ∈ N, (P p ↔ P p') := by
    intro p hp
    let φ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞ :=
      (DifferentialGeometry.Manifold.interiorChart I ∞ p).symm
    have hpS : p ∈ (DifferentialGeometry.Manifold.interiorChart I ∞ p).source :=
      (DifferentialGeometry.Manifold.mem_interiorChart_source_iff I ∞ p).mpr hp
    let a₀ : E := DifferentialGeometry.Manifold.interiorChart I ∞ p p
    have ha₀ : a₀ ∈ φ.source :=
      (DifferentialGeometry.Manifold.interiorChart I ∞ p).map_source hpS
    have hφa₀ : φ a₀ = p := (DifferentialGeometry.Manifold.interiorChart I ∞ p).left_inv hpS
    have hφI : ∀ y ∈ φ.target, I.IsInteriorPoint y := fun y hy =>
      DifferentialGeometry.Manifold.isInteriorPoint_of_mem_interiorChart_source I ∞
        (by simp) hy
    obtain ⟨r₀, hr₀, hball⟩ := Metric.isOpen_iff.mp φ.open_source a₀ ha₀
    let r := r₀ / 2
    have hr : 0 < r := half_pos hr₀
    have htube : ∀ c d : E, c ∈ ball a₀ r → d ∈ ball a₀ r →
        ∀ t ∈ Icc (0 : ℝ) 1, closedBall (c + t • (d - c)) (r / 2) ⊆ φ.source := by
      intro c d hc hd t ht z hz
      apply hball
      have hct : dist (c + t • (d - c)) a₀ < r := by
        have hseg : c + t • (d - c) = (1 - t) • c + t • d := by
          rw [smul_sub, sub_smul, one_smul]; abel
        rw [hseg]
        exact (convex_ball a₀ r) hc hd (sub_nonneg.mpr ht.2) ht.1 (by ring)
      rw [mem_ball]
      calc dist z a₀ ≤ dist z (c + t • (d - c)) + dist (c + t • (d - c)) a₀ :=
            dist_triangle _ _ _
        _ < r / 2 + r := by
            have := mem_closedBall.mp hz
            linarith
        _ < r₀ := by simp only [r]; linarith
    refine ⟨φ '' ball a₀ r, φ.toOpenPartialHomeomorph.isOpen_image_of_subset_source
      isOpen_ball (fun z hz => hball (ball_subset_ball (by simp only [r]; linarith) hz)),
      ⟨a₀, mem_ball_self hr, hφa₀⟩, ?_⟩
    rintro _ ⟨d, hd, rfl⟩
    have ha₀b : a₀ ∈ ball a₀ r := mem_ball_self hr
    constructor
    · intro hP
      rw [← hφa₀] at hP
      exact hmove φ a₀ d (r / 2) (half_pos hr) hφI (htube a₀ d ha₀b hd) hP
    · intro hP
      rw [← hφa₀]
      exact hmove φ d a₀ (r / 2) (half_pos hr) hφI (htube d a₀ hd ha₀b) hP
  choose N hNo hpN hNP using hloc
  let U : Set M := ⋃ (p : M) (hp : I.IsInteriorPoint p) (_ : P p), N p hp
  let V : Set M := ⋃ (p : M) (hp : I.IsInteriorPoint p) (_ : ¬ P p), N p hp
  have hU : IsOpen U := isOpen_iUnion fun p => isOpen_iUnion fun hp => isOpen_iUnion fun _ =>
    hNo p hp
  have hV : IsOpen V := isOpen_iUnion fun p => isOpen_iUnion fun hp => isOpen_iUnion fun _ =>
    hNo p hp
  have hcover : I.interior M ⊆ U ∪ V := by
    intro p hp
    by_cases hPp : P p
    · exact Or.inl (mem_iUnion.mpr ⟨p, mem_iUnion.mpr ⟨hp, mem_iUnion.mpr ⟨hPp, hpN p hp⟩⟩⟩)
    · exact Or.inr (mem_iUnion.mpr ⟨p, mem_iUnion.mpr ⟨hp, mem_iUnion.mpr ⟨hPp, hpN p hp⟩⟩⟩)
  have hmemU : ∀ p ∈ U, P p := by
    intro p hpU
    obtain ⟨p₁, hp₁⟩ := mem_iUnion.mp hpU
    obtain ⟨hp₁I, hp₁'⟩ := mem_iUnion.mp hp₁
    obtain ⟨hP₁, hpN₁⟩ := mem_iUnion.mp hp₁'
    exact (hNP p₁ hp₁I p hpN₁).mp hP₁
  by_contra hPq
  have hqV : q ∈ V :=
    mem_iUnion.mpr ⟨q, mem_iUnion.mpr ⟨hq, mem_iUnion.mpr ⟨hPq, hpN q hq⟩⟩⟩
  have hq₀U : q₀ ∈ U :=
    mem_iUnion.mpr ⟨q₀, mem_iUnion.mpr ⟨hq₀, mem_iUnion.mpr ⟨h₀, hpN q₀ hq₀⟩⟩⟩
  obtain ⟨p, -, hpU, hpV⟩ :=
    DifferentialGeometry.Topology.Manifold.isPreconnected_manifold_interior (I := I) (M := M)
      U V hU hV hcover ⟨q₀, hq₀, hq₀U⟩ ⟨q, hq, hqV⟩
  obtain ⟨p₂, hp₂⟩ := mem_iUnion.mp hpV
  obtain ⟨hp₂I, hp₂'⟩ := mem_iUnion.mp hp₂
  obtain ⟨hP₂, hpN₂⟩ := mem_iUnion.mp hp₂'
  exact hP₂ ((hNP p₂ hp₂I p hpN₂).mpr (hmemU p hpU))

/-- **Relocation of an interior ball.** In a connected manifold, the image of the closed unit ball
of a ball chart with image in the interior is moved, by a jointly smooth isotopy supported in a
compact subset of the interior, into any open set meeting the interior. -/
theorem exists_interiorIsotopy_image_subset_of_ballChart [PreconnectedSpace M]
    (φ₀ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞) (hφ₀ : closedBall (0 : E) 1 ⊆ φ₀.source)
    (hφ₀I : ∀ y ∈ φ₀.target, I.IsInteriorPoint y) {O : Set M} (hO : IsOpen O)
    (hOI : (O ∩ I.interior M).Nonempty) :
    ∃ Ψ : ℝ → Diffeomorph I I M M ∞,
      ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Ψ q.1 q.2) ∧
      Ψ 0 = Diffeomorph.refl I M ∞ ∧
      (∃ K : Set M, IsCompact K ∧ K ⊆ I.interior M ∧ ∀ t x, x ∉ K → Ψ t x = x) ∧
      Ψ 1 '' (φ₀ '' closedBall 0 1) ⊆ O := by
  let A : Set M := φ₀ '' closedBall 0 1
  -- `P p`: the ball can be pushed into every open neighbourhood of `p`
  let P : M → Prop := fun p => ∀ O' : Set M, IsOpen O' → p ∈ O' →
    ∃ Ψ : ℝ → Diffeomorph I I M M ∞,
      ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Ψ q.1 q.2) ∧
      Ψ 0 = Diffeomorph.refl I M ∞ ∧
      (∃ K : Set M, IsCompact K ∧ K ⊆ I.interior M ∧ ∀ t x, x ∉ K → Ψ t x = x) ∧
      Ψ 1 '' A ⊆ O'
  have h0S : (0 : E) ∈ φ₀.source := hφ₀ (mem_closedBall_self zero_le_one)
  -- base: contraction towards the centre
  have hbase : P (φ₀ 0) := by
    intro O' hO' h0O'
    obtain ⟨ε₀, hε₀, hε₀O⟩ := Metric.isOpen_iff.mp
      (φ₀.toOpenPartialHomeomorph.isOpen_inter_preimage hO') 0 ⟨h0S, h0O'⟩
    let ε := ε₀ / 2
    have hε : 0 < ε := half_pos hε₀
    obtain ⟨J, hJ, -, hJ0, hJrad, K, hK, -, hKt, hJfix⟩ :=
      DifferentialGeometry.Topology.Manifold.exists_diffeomorphs_contracting_embedded_closedBall
        φ₀ zero_lt_one hφ₀ φ₀.open_target
        (by rintro _ ⟨x, hx, rfl⟩; exact φ₀.map_source (hφ₀ hx))
    let T₀ : ℝ := max 0 (-Real.log ε)
    have hT₀ : 0 ≤ T₀ := le_max_left _ _
    have hexp : Real.exp (-T₀) ≤ ε := by
      have h1 : -T₀ ≤ Real.log ε := by
        have := le_max_right 0 (-Real.log ε)
        linarith
      calc Real.exp (-T₀) ≤ Real.exp (Real.log ε) := Real.exp_le_exp.mpr h1
        _ = ε := Real.exp_log hε
    refine ⟨fun s => J (T₀ * s), ?_, ?_, ⟨K, hK, fun y hy => hφ₀I y (hKt hy),
      fun t x hx => (hJfix (T₀ * t) x hx).1⟩, ?_⟩
    · have hlin : ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) ∞
          (fun q : ℝ × M => (T₀ * q.1, q.2)) :=
        ((contDiff_const.mul contDiff_id).contMDiff.comp contMDiff_fst).prodMk contMDiff_snd
      exact hJ.comp hlin
    · change J (T₀ * 0) = _
      rw [mul_zero, hJ0]
    · rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      change J (T₀ * 1) (φ₀ x) ∈ O'
      rw [mul_one, hJrad T₀ x hT₀ hx]
      have hsmall : Real.exp (-T₀) • x ∈ ball (0 : E) ε₀ := by
        rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        have hx1 : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.mp hx
        calc Real.exp (-T₀) * ‖x‖ ≤ Real.exp (-T₀) * 1 :=
              mul_le_mul_of_nonneg_left hx1 (Real.exp_pos _).le
          _ ≤ ε := by rw [mul_one]; exact hexp
          _ < ε₀ := half_lt_self hε₀
      exact (hε₀O hsmall).2
  -- chart moves
  have hmove : ∀ (φ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞) (a b : E) (δ : ℝ), 0 < δ →
      (∀ y ∈ φ.target, I.IsInteriorPoint y) →
      (∀ t ∈ Icc (0 : ℝ) 1, closedBall (a + t • (b - a)) δ ⊆ φ.source) →
      P (φ a) → P (φ b) := by
    intro φ a b δ hδ hφI htube hPa O' hO' hbO'
    have hbS : b ∈ φ.source := htube 1 ⟨zero_le_one, le_rfl⟩
      (by rw [one_smul, add_sub_cancel]; exact mem_closedBall_self hδ.le)
    have haS : a ∈ φ.source := htube 0 ⟨le_rfl, zero_le_one⟩
      (by rw [zero_smul, add_zero]; exact mem_closedBall_self hδ.le)
    obtain ⟨ε₀, hε₀, hε₀O⟩ := Metric.isOpen_iff.mp
      (φ.toOpenPartialHomeomorph.isOpen_inter_preimage hO') b ⟨hbS, hbO'⟩
    let ε := min (ε₀ / 2) (δ / 2)
    have hε : 0 < ε := lt_min (half_pos hε₀) (half_pos hδ)
    have hεδ : ε < δ := (min_le_right _ _).trans_lt (half_lt_self hδ)
    have hεε₀ : ε < ε₀ := (min_le_left _ _).trans_lt (half_lt_self hε₀)
    have haball : ball a ε ⊆ φ.source := fun z hz => htube 0 ⟨le_rfl, zero_le_one⟩
      (by rw [zero_smul, add_zero]; exact ball_subset_closedBall (ball_subset_ball hεδ.le hz))
    obtain ⟨Ψ₁, h₁, h₁0, ⟨K₁, hK₁, hK₁I, hfix₁⟩, hA₁⟩ :=
      hPa (φ '' ball a ε) (φ.toOpenPartialHomeomorph.isOpen_image_of_subset_source
        isOpen_ball haball) ⟨a, mem_ball_self hε, rfl⟩
    obtain ⟨Ψ₂, h₂, h₂0, ⟨K₂, hK₂, hK₂I, hfix₂⟩, hT⟩ :=
      exists_interiorIsotopy_translate_in_chart φ hφI hε.le hεδ htube
    obtain ⟨hs, h0, hK⟩ := interiorIsotopy_comp h₁ h₂ h₁0 h₂0 hK₁ hK₂ hK₁I hK₂I hfix₁ hfix₂
    refine ⟨fun t => (Ψ₁ t).trans (Ψ₂ t), hs, h0, hK, ?_⟩
    rintro _ ⟨p, hpA, rfl⟩
    obtain ⟨y, hy, hyp⟩ := hA₁ ⟨p, hpA, rfl⟩
    change Ψ₂ 1 (Ψ₁ 1 p) ∈ O'
    rw [← hyp, hT y (ball_subset_closedBall hy)]
    have hyb : y + (b - a) ∈ ball b ε₀ := by
      rw [mem_ball]
      have : dist (y + (b - a)) b = dist y a := by
        rw [dist_eq_norm, dist_eq_norm]
        congr 1
        abel
      rw [this]
      exact (mem_ball.mp hy).trans hεε₀
    exact (hε₀O hyb).2
  obtain ⟨q, hqO, hqI⟩ := hOI
  exact isInteriorPoint_imp_of_chart_moves hmove (hφ₀I _ (φ₀.map_source h0S)) hbase hqI O hO hqO

end Isotopy

section Cap

local instance relocationCellCharts_ASML2b : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
  Handle.closedCellChartedSpaceSucc 2

local instance relocationCellSmooth_ASML2b : IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) :=
  Handle.closedCellIsManifold 2

/-- **V2 (review item 6, D9): relative plug reassembly input — move the cap ball into a fibre
piece.** In a connected carrier with a raw presentation, a cap ball in the interior is moved by a
smooth ambient isotopy, fixed on an open neighbourhood of the whole boundary (so the support of the
WHOLE operation avoids the old ports, not only the initial ball), into the interior of one local
trivialization domain of one fibred piece. The comparison with the original fold is then
`Ψ 1 ∘ core`. -/
theorem exists_capRelocation_into_fibrePiece (Q : CompactCarrier.{u}) [ConnectedSpace Q.Carrier]
    (R : RawGraphPresentation Q) (c : ClosedCell 3 → Q.Carrier)
    (hc : IsSmoothEmbedding (𝓡∂ 3) Q.model ∞ c) (hcI : range c ⊆ Q.interior) :
    ∃ Ψ : ℝ → (Q.Carrier ≃ₘ⟮Q.model, Q.model⟯ Q.Carrier),
      ContMDiff (Q.model.prod 𝓘(ℝ, ℝ)) Q.model ∞ (fun x : Q.Carrier × ℝ => Ψ x.2 x.1) ∧
      (∀ x, Ψ 0 x = x) ∧
      (∃ U : Set Q.Carrier, IsOpen U ∧ Q.model.boundary Q.Carrier ⊆ U ∧
        ∀ t, ∀ x ∈ U, Ψ t x = x) ∧
      ∃ (j : Fin R.components.count) (b : (R.fibration j).base.Carrier),
        range (Ψ 1 ∘ c) ⊆ (R.reconstruction ∘ R.pairing.quotientMap) ''
          ((Subtype.val '' (TopologicalSpace.Opens.comap (R.fibration j).projection
              ((R.fibration j).neighborhood b) : Set (R.components.piece j))) ∩
            (R.cutCarrier.interior : Set R.cutCarrier.Carrier)) := by
  have hcI' : ∀ x, Q.model.IsInteriorPoint (c x) := fun x => hcI ⟨x, rfl⟩
  obtain ⟨φ₀, hφ₀, hφ₀I, hφ₀c⟩ := exists_ballChart_of_closedCell_interior c hc hcI'
  obtain ⟨j, b, hOpen, hne⟩ := exists_capRelocationTarget_inter_interior R
  obtain ⟨Ψ, hΨ, hΨ0, ⟨K, hK, hKI, hfix⟩, hA⟩ :=
    exists_interiorIsotopy_image_subset_of_ballChart φ₀ hφ₀ hφ₀I
      (isOpen_capRelocationTarget R j b) hne
  refine ⟨Ψ, hΨ.comp (contMDiff_snd.prodMk contMDiff_fst), fun x => by rw [hΨ0]; rfl,
    ⟨Kᶜ, hK.isClosed.isOpen_compl, fun x hx hxK => ?_, fun t x hx => hfix t x hx⟩, j, b, ?_⟩
  · exact ((Q.model.isBoundaryPoint_iff_not_isInteriorPoint x).mp hx) (hKI hxK)
  · rintro _ ⟨x, rfl⟩
    apply hA
    refine ⟨c x, ⟨x.val, mem_closedBall_zero_iff.mpr x.property, hφ₀c x⟩, rfl⟩

end Cap

end GC.GraphManifold.Assembly
