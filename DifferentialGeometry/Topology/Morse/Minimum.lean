import DifferentialGeometry.Topology.Morse.Attachment.ManifoldHandle
import DifferentialGeometry.Topology.Handle.Embedding
import DifferentialGeometry.Topology.Embedding.LocalDiffeomorph
import Mathlib.Topology.Connected.Clopen
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Topology.OpenPartialHomeomorph.Composition

open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Topology.Morse.ManifoldCellAttachment

open CellAttachment
open DifferentialGeometry.Topology.Handle

noncomputable section

attribute [local instance] closedCellChartedSpace cellBoundaryChartedSpace

private theorem interior_range_cell_chart
    {n : ℕ} {E M : Type*} [TopologicalSpace E] [TopologicalSpace M]
    (A : EuclideanSpace ℝ (Fin n) ≃ₜ E) (Φ : OpenPartialHomeomorph E M)
    (hsource : ∀ x : ClosedCell n, A x.val ∈ Φ.source) :
    interior (Set.range (fun x : ClosedCell n => Φ (A x.val))) =
      Set.range ((fun x : ClosedCell n => Φ (A x.val)) ∘ cellInteriorInclusion n) := by
  let Ξ := A.toOpenPartialHomeomorph.trans Φ
  have hΞsource (x : ClosedCell n) : x.val ∈ Ξ.source := by
    change x.val ∈ Set.univ ∩ A ⁻¹' Φ.source
    exact ⟨Set.mem_univ _, hsource x⟩
  have himage : Ξ.IsImage {x : EuclideanSpace ℝ (Fin n) | ‖x‖ ≤ 1}
      (Set.range (fun x : ClosedCell n => Φ (A x.val))) := by
    intro x hx
    constructor
    · rintro ⟨y, hy⟩
      have hxy : y.val = x := Ξ.injOn (hΞsource y) hx hy
      exact hxy ▸ y.property
    · intro h
      exact ⟨⟨x, h⟩, rfl⟩
  have hunit : interior {x : EuclideanSpace ℝ (Fin n) | ‖x‖ ≤ 1} =
      {x : EuclideanSpace ℝ (Fin n) | ‖x‖ < 1} := by
    simpa only [Metric.closedBall, Metric.ball, dist_zero_right] using
      (interior_closedBall (0 : EuclideanSpace ℝ (Fin n)) (one_ne_zero : (1 : ℝ) ≠ 0))
  apply Set.Subset.antisymm
  · intro y hy
    obtain ⟨x, rfl⟩ := interior_subset hy
    have hx := (himage.interior (hΞsource x)).mp hy
    rw [hunit] at hx
    exact ⟨⟨x.val, hx⟩, rfl⟩
  · rintro y ⟨x, rfl⟩
    apply (himage.interior (hΞsource (cellInteriorInclusion n x))).mpr
    rw [hunit]
    exact x.property

private theorem morseNormalForm_zero_eq {n : ℕ} (c : ℝ) (y : MorseModel n) :
    morseNormalForm (Nat.zero_le n) c y = c + morseNorm n y ^ 2 / 2 := by
  rw [morseNormalForm_split, negPart_bot, norm_zero, zero_pow (by omega), sub_zero]
  have hp : posPart (Nat.zero_le n) y = WithLp.toLp 2 y := by
    apply (EuclideanSpace.equiv (Fin n) ℝ).injective
    exact posPart_bot y
  rw [hp]
  dsimp only [morseNorm]
  ring

private theorem exists_smooth_ball_of_morseChart_zero
    {n : ℕ} [NeZero n] {H : Type} [TopologicalSpace H]
    {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel n) H} [I.Boundaryless] [IsManifold I ∞ M]
    {f : M → ℝ} {c r : ℝ} (data : MorseChart n 0 (Nat.zero_le n) c I f)
    (hr : 0 < r) (hR : 2 * r < data.R) (hR' : 2 * r < data.smoothRadius) :
    ∃ e : ClosedCell n → M,
      Manifold.IsSmoothEmbedding (modelWithCornersEuclideanHalfSpace ((n - 1) + 1)) I ∞ e ∧
      (∀ x, e x = data.χ ((EuclideanSpace.equiv (Fin n) ℝ) (r • x.val))) ∧
      (∀ x, f (e x) = c + r ^ 2 * ‖x.val‖ ^ 2 / 2) ∧
      e (closedCellCenter n) = data.p ∧
      ∃ U : Set M, IsOpen U ∧ data.p ∈ U ∧
        U = data.χ '' {y | morseNorm n y < 2 * r} ∧
        Set.range e = U ∩ {y | f y ≤ c + r ^ 2 / 2} ∧
        Set.range (e ∘ cellBoundaryInclusion n) = U ∩ {y | f y = c + r ^ 2 / 2} ∧
        Set.range (e ∘ cellInteriorInclusion n) = U ∩ {y | f y < c + r ^ 2 / 2} ∧
        Manifold.IsSmoothEmbedding (𝓡 (n - 1)) I ∞ (e ∘ cellBoundaryInclusion n) ∧
        interior (Set.range e) = Set.range (e ∘ cellInteriorInclusion n) := by
  let L := EuclideanSpace.equiv (Fin n) ℝ
  let S : Set (MorseModel n) := {y | morseNorm n y < 2 * r}
  have hS : IsOpen S := isOpen_lt (L.symm.continuous.norm) continuous_const
  have hSsrc : S ⊆ data.χ.source := fun y hy => data.closedBall_subset_source y (hy.trans hR).le
  let Φ := data.χ.restr S
  have hsource : Φ.source = S := by
    rw [data.χ.restr_source' S hS]
    exact Set.inter_eq_right.mpr hSsrc
  have hχ : ContMDiffOn 𝓘(ℝ, MorseModel n) I ∞ Φ Φ.source := by
    apply data.contMDiffOn.mono
    intro y hy
    rw [hsource] at hy
    have hh := (morseNorm_piNorm_le y).trans_lt (hy.trans hR')
    simpa only [Metric.mem_ball, dist_zero_right] using hh
  have hχi : ContMDiffOn I 𝓘(ℝ, MorseModel n) ∞ Φ.symm Φ.target := by
    apply data.symm_contMDiffOn.mono
    intro x hx
    have hy : Φ.symm x ∈ S := hsource ▸ Φ.map_target hx
    refine ⟨Φ.symm x, ?_, Φ.right_inv hx⟩
    have hh := (morseNorm_piNorm_le (Φ.symm x)).trans_lt (hy.trans hR')
    simpa only [Metric.mem_ball, dist_zero_right] using hh
  let Ψ : PartialDiffeomorph 𝓘(ℝ, MorseModel n) I (MorseModel n) M ∞ :=
    { toPartialEquiv := Φ.toPartialEquiv
      open_source := Φ.open_source
      open_target := Φ.open_target
      contMDiffOn_toFun := hχ
      contMDiffOn_invFun := hχi }
  let A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] MorseModel n :=
    (LinearEquiv.smulOfNeZero ℝ (EuclideanSpace ℝ (Fin n)) r hr.ne').toContinuousLinearEquiv.trans L
  let j : ClosedCell n → MorseModel n := fun x => A x.val
  have hj : Manifold.IsSmoothEmbedding (modelWithCornersEuclideanHalfSpace ((n - 1) + 1))
      𝓘(ℝ, MorseModel n) ∞ j := (isSmoothEmbedding_coe_closedCell n).continuousLinearEquiv_comp A
  have hnorm (x : ClosedCell n) : morseNorm n (j x) = r * ‖x.val‖ := by
    change ‖r • x.val‖ = r * ‖x.val‖
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
  have hjS (x : ClosedCell n) : j x ∈ Φ.source := by
    rw [hsource]
    change morseNorm n (j x) < 2 * r
    rw [hnorm]
    have hn : ‖x.val‖ ≤ 1 := x.property
    nlinarith
  have hlocal : IsLocalDiffeomorphOn 𝓘(ℝ, MorseModel n) I ∞ Φ (Set.range j) := by
    rintro ⟨y, x, rfl⟩
    exact Ψ.isLocalDiffeomorphAt _ _ _ (hjS x)
  have himm := hj.isImmersion.isLocalDiffeomorphOn_comp_of_ne_zero hlocal (by simp)
  let j' : ClosedCell n → Φ.source := fun x => ⟨j x, hjS x⟩
  have hj' : Topology.IsEmbedding j' := Topology.IsEmbedding.subtypeVal.of_comp_iff.mp hj.isEmbedding
  let e : ClosedCell n → M := fun x => Φ (j x)
  have he : Manifold.IsSmoothEmbedding (modelWithCornersEuclideanHalfSpace ((n - 1) + 1)) I ∞ e :=
    ⟨himm, Φ.isEmbedding_restrict.comp hj'⟩
  have htopInterior : interior (Set.range e) = Set.range (e ∘ cellInteriorInclusion n) :=
    interior_range_cell_chart A.toHomeomorph Φ hjS
  let jb : CellBoundary n → MorseModel n := fun x => A x.val
  have hjb : Manifold.IsSmoothEmbedding (𝓡 (n - 1)) 𝓘(ℝ, MorseModel n) ∞ jb :=
    (isSmoothEmbedding_coe_cellBoundary n).continuousLinearEquiv_comp A
  have hlocalb : IsLocalDiffeomorphOn 𝓘(ℝ, MorseModel n) I ∞ Φ (Set.range jb) := by
    rintro ⟨y, x, rfl⟩
    exact Ψ.isLocalDiffeomorphAt _ _ _ (hjS (cellBoundaryInclusion n x))
  let jb' : CellBoundary n → Φ.source :=
    fun x => ⟨jb x, hjS (cellBoundaryInclusion n x)⟩
  have hjb' : Topology.IsEmbedding jb' :=
    Topology.IsEmbedding.subtypeVal.of_comp_iff.mp hjb.isEmbedding
  have hboundaryEmbedding : Manifold.IsSmoothEmbedding (𝓡 (n - 1)) I ∞
      (e ∘ cellBoundaryInclusion n) :=
    ⟨hjb.isImmersion.isLocalDiffeomorphOn_comp_of_ne_zero hlocalb (by simp),
      Φ.isEmbedding_restrict.comp hjb'⟩
  have hheight (x : ClosedCell n) : f (e x) = c + r ^ 2 * ‖x.val‖ ^ 2 / 2 := by
    change f (data.χ (j x)) = _
    rw [data.normalForm_on (j x) ((hsource ▸ hjS x).trans hR).le, morseNormalForm_zero_eq, hnorm]
    ring
  have hcenter : e (closedCellCenter n) = data.p := by
    change data.χ (A 0) = data.p
    rw [map_zero]
    exact data.map_zero
  have hrange : Set.range e = Φ.target ∩ {y | f y ≤ c + r ^ 2 / 2} := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨Φ.map_source (hjS x), ?_⟩
      change f (e x) ≤ _
      rw [hheight]
      have hn : ‖x.val‖ ≤ 1 := x.property
      have hs : ‖x.val‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg x.val]
      nlinarith [sq_nonneg r]
    · rintro ⟨hy, hfy⟩
      let z := Φ.symm y
      have hz : z ∈ S := hsource ▸ Φ.map_target hy
      have hzy : data.χ z = y := Φ.right_inv hy
      have hfz : f y = c + morseNorm n z ^ 2 / 2 := by
        rw [← hzy, data.normalForm_on z (hz.trans hR).le, morseNormalForm_zero_eq]
      change f y ≤ c + r ^ 2 / 2 at hfy
      have hzn : morseNorm n z ≤ r := by
        rw [hfz] at hfy
        nlinarith [norm_nonneg (L.symm z)]
      have hAn : ‖A.symm z‖ = r⁻¹ * morseNorm n z := by
        change ‖r⁻¹ • L.symm z‖ = r⁻¹ * morseNorm n z
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
        rfl
      have hA1 : ‖A.symm z‖ ≤ 1 := by
        rw [hAn, inv_mul_eq_div]
        exact (div_le_one hr).mpr hzn
      refine ⟨⟨A.symm z, hA1⟩, ?_⟩
      change Φ (A (A.symm z)) = y
      rw [A.apply_symm_apply]
      exact hzy
  have hboundary : Set.range (e ∘ cellBoundaryInclusion n) =
      Φ.target ∩ {y | f y = c + r ^ 2 / 2} := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨Φ.map_source (hjS (cellBoundaryInclusion n x)), ?_⟩
      change f (e (cellBoundaryInclusion n x)) = _
      rw [hheight]
      change c + r ^ 2 * ‖x.val‖ ^ 2 / 2 = _
      rw [x.property]
      ring
    · rintro ⟨hy, hfy⟩
      have hmem : y ∈ Set.range e := hrange.symm ▸ ⟨hy, hfy.le⟩
      obtain ⟨x, rfl⟩ := hmem
      change f (e x) = c + r ^ 2 / 2 at hfy
      rw [hheight] at hfy
      have hxnorm : ‖x.val‖ = 1 := by
        have hprod : r ^ 2 * ‖x.val‖ ^ 2 = r ^ 2 * 1 := by linarith only [hfy]
        have hn2 := mul_left_cancel₀ (pow_ne_zero 2 hr.ne') hprod
        nlinarith [norm_nonneg x.val]
      refine ⟨⟨x.val, hxnorm⟩, ?_⟩
      rfl
  have hinterior : Set.range (e ∘ cellInteriorInclusion n) =
      Φ.target ∩ {y | f y < c + r ^ 2 / 2} := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨Φ.map_source (hjS (cellInteriorInclusion n x)), ?_⟩
      change f (e (cellInteriorInclusion n x)) < _
      rw [hheight]
      change c + r ^ 2 * ‖x.val‖ ^ 2 / 2 < _
      have hn2 : ‖x.val‖ ^ 2 < 1 := by nlinarith [x.property, norm_nonneg x.val]
      have hmul := mul_lt_mul_of_pos_left hn2 (sq_pos_of_pos hr)
      linarith only [hmul]
    · rintro ⟨hy, hfy⟩
      change f y < c + r ^ 2 / 2 at hfy
      have hmem : y ∈ Set.range e := hrange.symm ▸ ⟨hy, hfy.le⟩
      obtain ⟨x, rfl⟩ := hmem
      change f (e x) < c + r ^ 2 / 2 at hfy
      rw [hheight] at hfy
      have hxnorm : ‖x.val‖ < 1 := by
        have hprod : r ^ 2 * ‖x.val‖ ^ 2 < r ^ 2 * 1 := by linarith only [hfy]
        have hn2 := (mul_lt_mul_iff_right₀ (sq_pos_of_pos hr)).mp hprod
        nlinarith [norm_nonneg x.val]
      exact ⟨⟨x.val, hxnorm⟩, rfl⟩
  have htarget : Φ.target = data.χ '' S := by
    ext y
    constructor
    · intro hy
      exact ⟨Φ.symm y, hsource ▸ Φ.map_target hy, Φ.right_inv hy⟩
    · rintro ⟨x, hx, rfl⟩
      exact Φ.map_source (hsource.symm ▸ hx)
  exact ⟨e, he, fun _ => rfl, hheight, hcenter, Φ.target, Φ.open_target,
    hcenter ▸ Φ.map_source (hjS (closedCellCenter n)), htarget, hrange, hboundary, hinterior, hboundaryEmbedding, htopInterior⟩

end

end DifferentialGeometry.Topology.Morse.ManifoldCellAttachment

namespace DifferentialGeometry.Topology.Morse

open CellAttachment
open DifferentialGeometry.Topology.Handle
open ManifoldCellAttachment

noncomputable section

attribute [local instance] closedCellChartedSpace cellBoundaryChartedSpace

theorem IsNondegenerateCriticalPointAt.exists_smooth_ball_sublevel_of_index_zero
    {n : ℕ} [NeZero n] {H : Type} [TopologicalSpace H]
    {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel n) H} [I.Boundaryless] [IsManifold I ∞ M]
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) {p : M}
    (hnd : IsNondegenerateCriticalPointAt I f p)
    (hindex : _root_.sigNeg (chartHessianAt
      (fun z => f ((extChartAt I p).symm z)) (extChartAt I p p)) = 0)
    {W : Set M} (hW : IsOpen W) (hpW : p ∈ W) :
    ∃ ε > 0, ∃ e : ClosedCell n → M,
      Manifold.IsSmoothEmbedding (modelWithCornersEuclideanHalfSpace ((n - 1) + 1)) I ∞ e ∧
      e (closedCellCenter n) = p ∧
      (∀ x, f (e x) = f p + ε * ‖x.val‖ ^ 2) ∧
      ∃ U : Set M, IsOpen U ∧ p ∈ U ∧ U ⊆ W ∧
        Set.range e = U ∩ {y | f y ≤ f p + ε} ∧
        Set.range (e ∘ cellBoundaryInclusion n) = U ∩ {y | f y = f p + ε} ∧
        Set.range (e ∘ cellInteriorInclusion n) = U ∩ {y | f y < f p + ε} ∧
        Manifold.IsSmoothEmbedding (𝓡 (n - 1)) I ∞ (e ∘ cellBoundaryInclusion n) ∧
        interior (Set.range e) = Set.range (e ∘ cellInteriorInclusion n) := by
  let data := morseChart I f hf p (f p) 0 (Nat.zero_le n) hnd hindex rfl
  have hdata : data.p = p := by
    have hAnd {P Q : Prop} {α : Type} (F : P → Q → α) (h : P ∧ Q) :
        And.rec F h = F h.1 h.2 := by
      cases h
      rfl
    simp only [data, morseChart, hAnd]
  have h0src : (0 : MorseModel n) ∈ data.χ.source :=
    data.closedBall_subset_source 0 (by
      change ‖(0 : EuclideanSpace ℝ (Fin n))‖ ≤ data.R
      simpa only [norm_zero] using data.radius_pos.le)
  have hpre : data.χ ⁻¹' W ∈ 𝓝 (0 : MorseModel n) :=
    (data.χ.continuousAt h0src) (hW.mem_nhds (by rw [data.map_zero, hdata]; exact hpW))
  obtain ⟨τ, hτ, hτW⟩ := Metric.mem_nhds_iff.mp hpre
  let ρ := min data.R (min data.smoothRadius τ)
  have hρ : 0 < ρ := lt_min data.radius_pos (lt_min data.smoothRadius_pos hτ)
  let r := ρ / 4
  have hr : 0 < r := by dsimp [r]; positivity
  have h2r : 2 * r < ρ := by dsimp [r]; linarith
  have hR : 2 * r < data.R := h2r.trans_le (min_le_left _ _)
  have hR' : 2 * r < data.smoothRadius := h2r.trans_le
    ((min_le_right _ _).trans (min_le_left _ _))
  have hrt : 2 * r < τ := h2r.trans_le
    ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨e, he, _, hheight, hcenter, U, hU, hpU, hUeq, hrange, hboundary, hinterior, hboundaryEmbedding, htopInterior⟩ :=
    exists_smooth_ball_of_morseChart_zero data hr hR hR'
  refine ⟨r ^ 2 / 2, by positivity, e, he, hcenter.trans hdata, ?_,
    U, hU, hdata ▸ hpU, ?_, hrange, hboundary, hinterior, hboundaryEmbedding, htopInterior⟩
  · intro x
    rw [hheight]
    ring
  · rw [hUeq]
    rintro y ⟨z, hz, rfl⟩
    apply hτW
    have hh := (morseNorm_piNorm_le z).trans_lt (hz.trans hrt)
    simpa only [Metric.mem_ball, dist_zero_right] using hh

end

end DifferentialGeometry.Topology.Morse

namespace DifferentialGeometry.Topology.Morse

open CellAttachment
open DifferentialGeometry.Topology.Handle

noncomputable section

attribute [local instance] closedCellChartedSpace cellBoundaryChartedSpace

private theorem connectedComponentIn_eq_of_isCompact
    {X : Type*} [TopologicalSpace X] [T2Space X] {A B U : Set X} {x : X}
    (hAc : IsCompact A) (hAconn : IsPreconnected A) (hU : IsOpen U)
    (hA : A = U ∩ B) (hx : x ∈ A) : connectedComponentIn B x = A := by
  have hAB : A ⊆ B := hA ▸ Set.inter_subset_right
  have hxB := hAB hx
  have heq : (Subtype.val : B → X) ⁻¹' A = Subtype.val ⁻¹' U := by
    ext y
    simp only [Set.mem_preimage, hA, Set.mem_inter_iff, y.property, and_true]
  have hclopen : IsClopen ((Subtype.val : B → X) ⁻¹' A) := by
    refine ⟨hAc.isClosed.preimage continuous_subtype_val, ?_⟩
    rw [heq]
    exact hU.preimage continuous_subtype_val
  apply Set.Subset.antisymm
  · rw [connectedComponentIn_eq_image hxB]
    rintro y ⟨z, hz, rfl⟩
    exact hclopen.connectedComponent_subset (show (⟨x, hxB⟩ : B) ∈
      (Subtype.val : B → X) ⁻¹' A from hx) hz
  · exact hAconn.subset_connectedComponentIn hx hAB

theorem IsNondegenerateCriticalPointAt.exists_smooth_ball_sublevel_component_of_index_zero
    {n : ℕ} [NeZero n] {H : Type} [TopologicalSpace H]
    {M : Type} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    {I : ModelWithCorners ℝ (MorseModel n) H} [I.Boundaryless] [IsManifold I ∞ M]
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) {p : M}
    (hnd : IsNondegenerateCriticalPointAt I f p)
    (hindex : _root_.sigNeg (chartHessianAt
      (fun z => f ((extChartAt I p).symm z)) (extChartAt I p p)) = 0)
    {W : Set M} (hW : IsOpen W) (hpW : p ∈ W) :
    ∃ ε > 0, ∃ e : ClosedCell n → M,
      Manifold.IsSmoothEmbedding (modelWithCornersEuclideanHalfSpace ((n - 1) + 1)) I ∞ e ∧
      e (closedCellCenter n) = p ∧
      (∀ x, f (e x) = f p + ε * ‖x.val‖ ^ 2) ∧
      Set.range e = connectedComponentIn {y | f y ≤ f p + ε} p ∧ Set.range e ⊆ W ∧
      Set.range (e ∘ cellBoundaryInclusion n) =
        connectedComponentIn {y | f y ≤ f p + ε} p ∩ {y | f y = f p + ε} ∧
      Set.range (e ∘ cellInteriorInclusion n) =
        connectedComponentIn {y | f y ≤ f p + ε} p ∩ {y | f y < f p + ε} ∧
      Manifold.IsSmoothEmbedding (𝓡 (n - 1)) I ∞ (e ∘ cellBoundaryInclusion n) ∧
      interior (Set.range e) = Set.range (e ∘ cellInteriorInclusion n) ∧
      frontier (Set.range e) = Set.range (e ∘ cellBoundaryInclusion n) := by
  obtain ⟨ε, hε, e, he, hcenter, hheight, U, hU, hpU, hUW, hrange, hboundary, hinterior, hboundaryEmbedding, htopInterior⟩ :=
    hnd.exists_smooth_ball_sublevel_of_index_zero hf hindex hW hpW
  have hconv : Convex ℝ ({x : EuclideanSpace ℝ (Fin n) | ‖x‖ ≤ 1} : Set _) := by
    simpa only [Metric.closedBall, dist_zero_right] using
      (convex_closedBall (0 : EuclideanSpace ℝ (Fin n)) (1 : ℝ))
  let _ : PreconnectedSpace (ClosedCell n) := Subtype.preconnectedSpace hconv.isPreconnected
  have hpre : IsPreconnected (Set.range e) := by
    simpa only [Set.image_univ] using isPreconnected_univ.image e he.isEmbedding.continuous.continuousOn
  have hcompact : IsCompact (Set.range e) := isCompact_range he.isEmbedding.continuous
  have htopBoundary : frontier (Set.range e) = Set.range (e ∘ cellBoundaryInclusion n) := by
    rw [hcompact.isClosed.frontier_eq, htopInterior, hrange, hinterior, hboundary]
    ext y
    constructor
    · rintro ⟨⟨hyU, hyf⟩, hnot⟩
      exact ⟨hyU, le_antisymm hyf (le_of_not_gt (fun hlt => hnot ⟨hyU, hlt⟩))⟩
    · rintro ⟨hyU, hyf⟩
      refine ⟨⟨hyU, hyf.le⟩, ?_⟩
      rintro ⟨_, hlt⟩
      exact (lt_irrefl (f p + ε)) (hyf ▸ hlt)
  have hp : p ∈ Set.range e := ⟨closedCellCenter n, hcenter⟩
  have hcomp := connectedComponentIn_eq_of_isCompact hcompact hpre hU hrange hp
  refine ⟨ε, hε, e, he, hcenter, hheight, hcomp.symm, ?_, ?_, ?_, hboundaryEmbedding, htopInterior, htopBoundary⟩
  · rw [hrange]
    exact Set.inter_subset_left.trans hUW
  · rw [hcomp, hrange, hboundary]
    ext y
    constructor
    · intro hy
      exact ⟨⟨hy.1, hy.2.le⟩, hy.2⟩
    · exact fun hy => ⟨hy.1.1, hy.2⟩
  · rw [hcomp, hrange, hinterior]
    ext y
    constructor
    · intro hy
      have hfy : f y < f p + ε := hy.2
      exact ⟨⟨hy.1, hfy.le⟩, hy.2⟩
    · exact fun hy => ⟨hy.1.1, hy.2⟩

end

end DifferentialGeometry.Topology.Morse
