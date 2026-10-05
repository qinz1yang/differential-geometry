import DifferentialGeometry.Geometry.Collapse.ZeroModel.ZeroModelRowLFR54

/-!
# Consumer of row LFR54: zero models paired with their boundary types (ZSP02)

Lane LFR54-ROW, group G4. Chapter 14, ZSP02 (master207B:6374–6400) uses LFR54 as "each [core] has its
LPA05/LFR54 smooth type, including the boundary … Every nonempty boundary is a connected `S²` or
`T²`." On every actual disc core `D_T` of a finite soul carrier `e` (`T > 0`):

* `discCoreBoundaryHomeomorph`: the boundary level `{‖(e⁻¹ x).2‖ = T}` is the unit sphere bundle,
  `z ↦ e (T • z)`;
* `lfr54_discCore_types_with_boundary`: the LFR54 type of `D_T` (the SAME diffeomorphism/embedding
  as in the row, boundary onto the model boundary) together with the boundary type: `S²` for `D³`
  (the restriction of the row's `Ψ` to the boundary sphere) and for `ℝP³ ∖ int D³`, a torus for
  `S¹ × D²` (`S¹ × S¹` through the isometric trivialization) and for `D(o(K))` (`T²`).
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Function Module
open scoped ContDiff Topology Manifold
open DifferentialGeometry.Topology.Morse

namespace DifferentialGeometry.Geometry.Collapse.ZeroModel

open DifferentialGeometry.Topology DifferentialGeometry.Topology.VectorBundle
open DifferentialGeometry.Topology.Manifold

universe u uEB uHB uB uF uV uEN uHN uN

local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "S2" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
local notation "T2" => AddCircle (1 : ℝ) × AddCircle (1 : ℝ)

/-- The boundary charts of the closed ball `ClosedCell 3` (`𝓡∂ 3`). -/
local instance ballChartsBd_LFR54ROW : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 2

/-- The closed ball is a smooth manifold with boundary. -/
local instance ballSmoothBd_LFR54ROW : IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 2

section Boundary

variable {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ b, NormedAddCommGroup (V b)] [∀ b, InnerProductSpace ℝ (V b)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  {N : Type*} [TopologicalSpace N]

omit [TopologicalSpace B] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiberBundle F V]
  [VectorBundle ℝ F V] in
/-- `‖e⁻¹ (e (T • z))‖ = T` for a unit vector `z`. -/
theorem norm_symm_apply_smul_unit (e : TotalSpace F V ≃ₜ N) {T : ℝ} (hT : 0 < T)
    (z : {z : TotalSpace F V // ‖z.2‖ = 1}) :
    ‖(e.symm (e ⟨z.val.proj, T • z.val.2⟩)).2‖ = T := by
  rw [e.symm_apply_apply]
  change ‖T • z.val.2‖ = T
  rw [norm_smul, z.property, mul_one, Real.norm_eq_abs, abs_of_pos hT]

omit [TopologicalSpace B] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiberBundle F V]
  [VectorBundle ℝ F V] in
/-- `‖T⁻¹ • e⁻¹ x‖ = 1` on the boundary level `T`. -/
theorem norm_inv_smul_symm_eq_one (e : TotalSpace F V ≃ₜ N) {T : ℝ} (hT : 0 < T)
    (x : {x : N // ‖(e.symm x).2‖ = T}) :
    ‖((⟨(e.symm x.val).proj, T⁻¹ • (e.symm x.val).2⟩ : TotalSpace F V)).2‖ = 1 := by
  change ‖T⁻¹ • (e.symm x.val).2‖ = 1
  rw [norm_smul, x.property, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hT),
    inv_mul_cancel₀ hT.ne']

/-- The boundary level `{‖(e⁻¹ x).2‖ = T}` of a disc core is the unit sphere bundle, through
`z ↦ e (T • z)`. -/
def discCoreBoundaryHomeomorph (e : TotalSpace F V ≃ₜ N) {T : ℝ} (hT : 0 < T) :
    {z : TotalSpace F V // ‖z.2‖ = 1} ≃ₜ {x : N // ‖(e.symm x).2‖ = T} where
  toFun z := ⟨e ⟨z.val.proj, T • z.val.2⟩, norm_symm_apply_smul_unit e hT z⟩
  invFun x := ⟨⟨(e.symm x.val).proj, T⁻¹ • (e.symm x.val).2⟩, norm_inv_smul_symm_eq_one e hT x⟩
  left_inv z := by
    apply Subtype.ext
    change (⟨(e.symm (e ⟨z.val.proj, T • z.val.2⟩)).proj,
      T⁻¹ • (e.symm (e ⟨z.val.proj, T • z.val.2⟩)).2⟩ : TotalSpace F V) = z.val
    rw [e.symm_apply_apply]
    change (⟨z.val.proj, T⁻¹ • T • z.val.2⟩ : TotalSpace F V) = ⟨z.val.proj, z.val.2⟩
    rw [smul_smul, inv_mul_cancel₀ hT.ne', one_smul]
  right_inv x := by
    apply Subtype.ext
    change e ⟨(e.symm x.val).proj, T • T⁻¹ • (e.symm x.val).2⟩ = x.val
    rw [smul_smul, mul_inv_cancel₀ hT.ne', one_smul]
    exact e.apply_symm_apply x.val
  continuous_toFun :=
    (e.continuous.comp ((_root_.VectorBundle.continuous_totalSpace_smul (𝕜 := ℝ) (F := F)
      (V := V)).comp (continuous_const.prodMk continuous_subtype_val))).subtype_mk _
  continuous_invFun :=
    ((_root_.VectorBundle.continuous_totalSpace_smul (𝕜 := ℝ) (F := F) (V := V)).comp
      (continuous_const.prodMk (e.symm.continuous.comp continuous_subtype_val))).subtype_mk _

@[simp] theorem discCoreBoundaryHomeomorph_apply (e : TotalSpace F V ≃ₜ N) {T : ℝ} (hT : 0 < T)
    (z : {z : TotalSpace F V // ‖z.2‖ = 1}) :
    (discCoreBoundaryHomeomorph e hT z).val = e ⟨z.val.proj, T • z.val.2⟩ := rfl

omit [TopologicalSpace B] [NormedAddCommGroup F] [NormedSpace ℝ F] [∀ b, InnerProductSpace ℝ (V b)]
  [FiberBundle F V] [VectorBundle ℝ F V] in
/-- A continuous bijection from a compact space onto the unit sphere bundle of a bundle with
Hausdorff total space is a homeomorphism onto it. -/
theorem nonempty_homeomorph_unitSphere_of_unit_map [T2Space (TotalSpace F V)] {X : Type*}
    [TopologicalSpace X] [CompactSpace X] (ν : X → TotalSpace F V) (hν : Continuous ν)
    (hνS : ∀ p, ‖(ν p).2‖ = 1) (hνinj : Injective ν)
    (hνsurj : ∀ z : TotalSpace F V, ‖z.2‖ = 1 → ∃ p, ν p = z) :
    Nonempty (X ≃ₜ {z : TotalSpace F V // ‖z.2‖ = 1}) := by
  let g : X → {z : TotalSpace F V // ‖z.2‖ = 1} := fun p => ⟨ν p, hνS p⟩
  have hginj : Injective g := fun p q h => hνinj (congrArg Subtype.val h)
  have hgsurj : Surjective g := by
    rintro ⟨z, hz⟩
    obtain ⟨p, hp⟩ := hνsurj z hz
    exact ⟨p, Subtype.ext hp⟩
  exact ⟨(hν.subtype_mk hνS).homeoOfEquivCompactToT2 (f := Equiv.ofBijective g ⟨hginj, hgsurj⟩)⟩

end Boundary

/-- **Consumer of LFR54 (ZSP02's boundary types).** On every actual disc core `D_T`, `T > 0`, the
LFR54 type with its boundary correspondence, paired with the type of the boundary
`∂D_T = {‖(e⁻¹ x).2‖ = T}`:
1. point soul: `D_T ≅ ClosedCell 3`, and `∂D_T ≃ₜ S²` (the row's `Ψ` on the boundary);
2. circle soul: `solidTorusCarrier ≅ D_T`, and `∂D_T ≃ₜ S¹ × S¹` (`AddCircle 1 × unit circle`);
3. surface soul with LC77: `D_T ↪ ℝP³` onto `ℝP³ ∖ (open ball)` with `∂D_T ≃ₜ S²`, or
   `D_T ≅ {Q ≤ 0}` with `∂D_T ≃ₜ T²`. -/
theorem lfr54_discCore_types_with_boundary :
    (∀ {EB : Type uEB} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [FiniteDimensional ℝ EB]
      {HB : Type uHB} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} [IB.Boundaryless]
      {B : Type uB} [TopologicalSpace B] [ChartedSpace HB B] [IsManifold IB ∞ B]
      {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
      {V : B → Type uV} [TopologicalSpace (TotalSpace F V)]
      [∀ b, NormedAddCommGroup (V b)] [∀ b, InnerProductSpace ℝ (V b)]
      [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V IB]
      [IsContMDiffRiemannianBundle IB ∞ F V] [Subsingleton B] [Nonempty B]
      {EN : Type uEN} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
      {HN : Type uHN} [TopologicalSpace HN] {IN : ModelWithCorners ℝ EN HN}
      {N : Type uN} [TopologicalSpace N] [ChartedSpace HN N]
      (hd : finrank ℝ (EB × F) = 2 + 1), finrank ℝ EB = 0 →
      ∀ (e : Diffeomorph (IB.prod 𝓘(ℝ, F)) IN (TotalSpace F V) N ∞) (T : ℝ) (hT : 0 < T),
      letI := discCoreChartedSpace e hd T hT
      ∃ Ψ : Diffeomorph (morseModelWithCornersHalfSpace 2) (𝓡∂ 3)
          {x : N // ‖(e.symm x).2‖ ≤ T} (ClosedCell 3) ∞,
        (∀ x, ‖(e.symm x.val).2‖ = T ↔ ‖(Ψ x).val‖ = 1) ∧
        ∃ j : {x : N // ‖(e.symm x).2‖ = T} ≃ₜ S2, ∀ x hx, (j ⟨x, hx⟩).val = (Ψ ⟨x, hx.le⟩).val) ∧
    (∀ {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
      {V : AddCircle (1 : ℝ) → Type uV} [TopologicalSpace (TotalSpace F V)]
      [∀ b, NormedAddCommGroup (V b)] [∀ b, InnerProductSpace ℝ (V b)]
      [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℝ)]
      [IsContMDiffRiemannianBundle 𝓘(ℝ, ℝ) ∞ F V]
      {EN : Type uEN} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
      {HN : Type uHN} [TopologicalSpace HN] {IN : ModelWithCorners ℝ EN HN}
      {N : Type uN} [TopologicalSpace N] [ChartedSpace HN N]
      (hF : finrank ℝ F = 2), SmoothOrientation (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) (TotalSpace F V) →
      ∀ (e : Diffeomorph (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) IN (TotalSpace F V) N ∞) (T : ℝ) (hT : 0 < T),
      letI := discCoreChartedSpace e (finrank_real_prod_eq_three hF) T hT
      (∃ Φ : Diffeomorph GC.GraphManifold.solidTorusCarrier.{u}.model
          (morseModelWithCornersHalfSpace 2) GC.GraphManifold.solidTorusCarrier.{u}.Carrier
          {x : N // ‖(e.symm x).2‖ ≤ T} ∞,
        ∀ x : GC.GraphManifold.solidTorusCarrier.{u}.Carrier,
          GC.GraphManifold.cliffordHeight (x : GC.GraphManifold.solidTorusSet.{u}).val = 0 ↔
            ‖(e.symm (Φ x).val).2‖ = T) ∧
      Nonempty ({x : N // ‖(e.symm x).2‖ = T} ≃ₜ
        (AddCircle (1 : ℝ) × Metric.sphere (0 : E2) 1))) ∧
    (∀ {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
      {B : Type uB} [TopologicalSpace B] [ChartedSpace E2 B] [IsManifold (𝓡 2) ∞ B]
      {V : B → Type uV} [TopologicalSpace (TotalSpace F V)]
      [∀ b, NormedAddCommGroup (V b)] [∀ b, InnerProductSpace ℝ (V b)]
      [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V (𝓡 2)]
      [IsContMDiffRiemannianBundle (𝓡 2) ∞ F V] [CompactSpace B] [ConnectedSpace B] [T2Space B]
      {EN : Type uEN} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
      {HN : Type uHN} [TopologicalSpace HN] {IN : ModelWithCorners ℝ EN HN}
      {N : Type uN} [MetricSpace N] [ProperSpace N] [ChartedSpace HN N]
      (hd : finrank ℝ (E2 × F) = 2 + 1),
      SmoothOrientation ((𝓡 2).prod 𝓘(ℝ, F)) (TotalSpace F V) →
      ∀ {n : ℕ∞ω}, (2 : ℕ∞ω) ≤ n →
      ∀ (k : Bundle.ContMDiffRiemannianMetric (𝓡 2) n E2 (TangentSpace (𝓡 2) : B → Type _)),
      (∀ x (v w : TangentSpace (𝓡 2) x), 0 ≤ k.sectionalCurvature x v w) →
      ∀ (e : Diffeomorph ((𝓡 2).prod 𝓘(ℝ, F)) IN (TotalSpace F V) N ∞),
      (∀ K : Set N, IsCompact K → ∀ a b : N,
        ¬ Bornology.IsBounded (connectedComponentIn Kᶜ a) →
        ¬ Bornology.IsBounded (connectedComponentIn Kᶜ b) →
        connectedComponentIn Kᶜ a = connectedComponentIn Kᶜ b) →
      ∀ (T : ℝ) (hT : 0 < T),
      letI := discCoreChartedSpace e hd T hT
      ((∃ (c : OrientedBallChart projectiveThreeSpaceLift.{u}.toClosedOrientedManifold)
        (f : {x : N // ‖(e.symm x).2‖ ≤ T} → projectiveThreeSpaceLift.{u}.Carrier),
        IsSmoothEmbedding (morseModelWithCornersHalfSpace 2) (𝓡 3) ∞ f ∧
        range f = {y | y ∉ c.chart '' Metric.ball (0 : E3) 1} ∧
        ∀ x, f x ∈ c.chart '' Metric.sphere (0 : E3) 1 ↔ ‖(e.symm x.val).2‖ = T) ∧
        Nonempty ({x : N // ‖(e.symm x).2‖ = T} ≃ₜ S2)) ∨
      ((∃ Φ : Diffeomorph (morseModelWithCornersHalfSpace 2) (𝓡∂ 3)
          {x : N // ‖(e.symm x).2‖ ≤ T} GC.Seifert.mobiusBundleSet.{u} ∞,
        ∀ x, ‖(e.symm x.val).2‖ = T ↔ GC.Seifert.mobiusBundleFunction (Φ x).val = 0) ∧
        Nonempty ({x : N // ‖(e.symm x).2‖ = T} ≃ₜ T2))) := by
  obtain ⟨hP, hC, -, -⟩ := lfr54_classified_finite_zero_packet.{u, uEB, uHB, uB, uF, uV, uEN, uHN, uN}
  refine ⟨?_, ?_, ?_⟩
  · intro EB _ _ _ HB _ IB _ B _ _ _ F _ _ _ V _ _ _ _ _ _ _ _ _ EN _ _ HN _ IN N _ _ hd h0 e T hT
    let csCore_LFR54ROW := discCoreChartedSpace e hd T hT
    obtain ⟨Ψ, -, hbd⟩ := hP (IB := IB) (V := V) hd h0 e T hT
    refine ⟨Ψ, hbd, ?_⟩
    -- the boundary of the core is carried onto the boundary sphere by the same `Ψ`
    let incl : {x : N // ‖(e.symm x).2‖ = T} → {x : N // ‖(e.symm x).2‖ ≤ T} :=
      fun x => ⟨x.val, x.property.le⟩
    have hincl : Continuous incl := continuous_subtype_val.subtype_mk _
    let g : {x : N // ‖(e.symm x).2‖ = T} → S2 := fun x =>
      ⟨(Ψ (incl x)).val, by
        rw [mem_sphere_zero_iff_norm]
        exact (hbd (incl x)).mp x.property⟩
    have hg : Continuous g :=
      ((continuous_subtype_val.comp Ψ.continuous).comp hincl).subtype_mk _
    let ginv : S2 → {x : N // ‖(e.symm x).2‖ = T} := fun y =>
      ⟨(Ψ.symm ⟨y.val, (mem_sphere_zero_iff_norm.mp y.property).le⟩).val, by
        have h := (hbd (Ψ.symm ⟨y.val, (mem_sphere_zero_iff_norm.mp y.property).le⟩)).mpr (by
          rw [Diffeomorph.apply_symm_apply]
          exact mem_sphere_zero_iff_norm.mp y.property)
        exact h⟩
    have hginv : Continuous ginv :=
      (continuous_subtype_val.comp (Ψ.symm.continuous.comp
        (continuous_subtype_val.subtype_mk _))).subtype_mk _
    have hli : ∀ x, ginv (g x) = x := by
      intro x
      apply Subtype.ext
      change (Ψ.symm ⟨(Ψ (incl x)).val, _⟩).val = x.val
      have : (⟨(Ψ (incl x)).val, _⟩ : ClosedCell 3) = Ψ (incl x) := rfl
      rw [this, Diffeomorph.symm_apply_apply]
    have hri : ∀ y, g (ginv y) = y := by
      intro y
      apply Subtype.ext
      change (Ψ (incl (ginv y))).val = y.val
      have : incl (ginv y) = Ψ.symm ⟨y.val, (mem_sphere_zero_iff_norm.mp y.property).le⟩ := rfl
      rw [this, Diffeomorph.apply_symm_apply]
    exact ⟨⟨⟨g, ginv, hli, hri⟩, hg, hginv⟩, fun x hx => rfl⟩
  · intro F _ _ _ V _ _ _ _ _ _ _ EN _ _ HN _ IN N _ _ hF oV e T hT
    refine ⟨hC hF oV e T hT, ?_⟩
    obtain ⟨⟨Φ, -, hΦn⟩, -⟩ := exists_circle_soul_bundle_type.{u} hF oV
    -- `S(V) ≃ₜ S¹ × S¹` through the isometric trivialization
    let p : {z : TotalSpace F V // ‖z.2‖ = 1} → AddCircle (1 : ℝ) × Metric.sphere (0 : E2) 1 :=
      fun z => ((Φ.symm z.val).1, ⟨(Φ.symm z.val).2, by
        rw [mem_sphere_zero_iff_norm, ← hΦn, Diffeomorph.apply_symm_apply]
        exact z.property⟩)
    let q : AddCircle (1 : ℝ) × Metric.sphere (0 : E2) 1 → {z : TotalSpace F V // ‖z.2‖ = 1} :=
      fun w => ⟨Φ (w.1, w.2.val), by rw [hΦn]; exact mem_sphere_zero_iff_norm.mp w.2.property⟩
    have hp : Continuous p :=
      (continuous_fst.comp (Φ.symm.continuous.comp continuous_subtype_val)).prodMk
        ((continuous_snd.comp (Φ.symm.continuous.comp continuous_subtype_val)).subtype_mk _)
    have hq : Continuous q :=
      (Φ.continuous.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _
    let hS : {z : TotalSpace F V // ‖z.2‖ = 1} ≃ₜ AddCircle (1 : ℝ) × Metric.sphere (0 : E2) 1 :=
      { toFun := p
        invFun := q
        left_inv := fun z => by
          apply Subtype.ext
          change Φ ((Φ.symm z.val).1, (Φ.symm z.val).2) = z.val
          rw [Prod.mk.eta, Diffeomorph.apply_symm_apply]
        right_inv := fun w => by
          change ((Φ.symm (Φ (w.1, w.2.val))).1, (⟨(Φ.symm (Φ (w.1, w.2.val))).2, _⟩ :
            Metric.sphere (0 : E2) 1)) = w
          ext
          · simp only [Diffeomorph.symm_apply_apply]
          · simp only [Diffeomorph.symm_apply_apply]
        continuous_toFun := hp
        continuous_invFun := hq }
    exact ⟨(discCoreBoundaryHomeomorph e.toHomeomorph hT).symm.trans hS⟩
  · intro F _ _ _ B _ _ _ V _ _ _ _ _ _ _ _ _ _ EN _ _ HN _ IN N _ _ _ hd oN n hn k hK e hLC77 T hT
    let contMetric_LFR54ROW : IsContinuousRiemannianBundle F V :=
      RankOneQuotient.isContinuousRiemannianBundle_of_contMDiff (EB := E2)
    rcases lfr52_lc77_surface_soul_twisted hd oN hn k hK e.toHomeomorph hLC77 with
      ⟨ν, hν, hνS, hνinj, hνsurj, hνneg, hνloc⟩ | ⟨ν, hν, hνS, hνinj, hνsurj, hνneg, hνloc⟩
    · left
      refine ⟨exists_puncturedRP3_embedding_discCore_of_antipodal_unit_map.{u} e hd ν hν hνS hνinj
        hνsurj hνneg hνloc T hT, ?_⟩
      obtain ⟨j⟩ := nonempty_homeomorph_unitSphere_of_unit_map ν hν.continuous hνS hνinj hνsurj
      exact ⟨(discCoreBoundaryHomeomorph e.toHomeomorph hT).symm.trans j.symm⟩
    · right
      refine ⟨exists_mobiusBundleSet_diffeomorph_discCore_of_klein_unit_map.{u} e hd ν hν hνS hνinj
        hνsurj hνneg hνloc T hT, ?_⟩
      obtain ⟨j⟩ := nonempty_homeomorph_unitSphere_of_unit_map ν hν.continuous hνS hνinj hνsurj
      exact ⟨(discCoreBoundaryHomeomorph e.toHomeomorph hT).symm.trans j.symm⟩

end DifferentialGeometry.Geometry.Collapse.ZeroModel
