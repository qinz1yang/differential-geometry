import DifferentialGeometry.Geometry.Collapse.LocalExport.SlimPacket
import DifferentialGeometry.Geometry.Collapse.LocalExport.SlimChartApplications
import DifferentialGeometry.Topology.Ehresmann.CompactTransverseTransport

/-!
# The smooth fibre type of an original slim piece (GAF07's smooth-type bridge)

Lane C14-FIBRE-PRE, class-(b) derived lemma of dispositions-task53 / review 53 §2.1 (GAF07 remark:
`SlimPacket.zeroLevel_type` is a HOMEOMORPHISM, not a `Diffeomorph`; the smooth identification is
a separate lemma and the homeomorphism field is never used as a diffeomorphism). Blueprint GAF07
(`thm:fibration-whole-closed-fiber-bundles`, master207B B:6049–6170): "It identifies `h₁⁻¹(a)` with
the original smooth fiber, which is … `S²` or `T²`".

For a slim chart `c` (`L = 10⁶Δ`, `a' = 905·10³Δ`) and `r ≤ a'`, the restricted coordinate
`η : {x ∈ B(p, L) | |η x| < r} → (-r, r)` is a smooth submersion (`slabMap_FPRE`); its fibre over
`a` carries the regular-fibre smooth structure (`fibreChartedSpace_FPRE`).

* `nonempty_diffeomorph_regularFiber_of_iff_FPRE` (generic): regular fibres with the same points are
  diffeomorphic.
* `SlimChart.nonempty_diffeomorph_fibre_FPRE`: EVERY whole fibre of EVERY slab is diffeomorphic to
  the zero fibre `F₀` of the `a'`-slab (LFR20's trivialization restricted to `F₀ × {a}`, then the
  slab inclusion `nonempty_diffeomorph_fibre_slab_FPRE`).
* `SlimChart.zeroFibreHomeomorph_FPRE`: `F₀` and the zero level `{x ∈ B(p, L) | η x = 0}` of
  `zeroLevel_type` are the same points (a homeomorphism of subtypes, nothing smooth is claimed).
* `SlimChart.range_fibre_FPRE`: the points of the fibre over `a` are the WHOLE level set.
* `SlimChart.exists_embedding_fibre_FPRE`: every whole level set `{x ∈ B(p, L) | η x = a}`,
  `|a| < a'`, is the image of a smooth embedding of `F₀` (smooth, topological embedding, injective
  differential).
* `SlimChart.closedSlab_product_FPRE` (relative version, with boundary): the closed slab
  `{|η| ≤ r}` is `Θ(F₀ × [-r, r])` and its boundary fibres `{|η| = r}` are `Θ(F₀ × {±r})` for
  LFR20's diffeomorphism `Θ : F₀ × (-R, R) ≅ {|η| < R}`, `r < R < a'`.
* `SlimPacket.smooth_fibre_type_FPRE` (the bridge): every whole fibre `F_a` is a smooth manifold
  diffeomorphic to `F₀`, compact, connected and homeomorphic to `S²` or `T²`, with the whole level
  set as its points.
* consumer `SlimPacket.gaf07_slim_fibre_type_FPRE`: with FC34a
  (`nonempty_diffeomorph_levelSet_of_compact_transport`), the whole end level of a regular family
  starting at the original coordinate with compact trace (GAF07's straight line) is diffeomorphic to
  `F₀`, compact, connected, `S²` or `T²`.

NOT provided (obstruction, recorded in `build-logs/resume/sheet-C14-FIBRE-PRE.md`): a
DIFFEOMORPHISM `F₀ ≃ₘ S²` or `F₀ ≃ₘ T²`. It needs the smooth classification of closed surfaces
(homeomorphic closed surfaces are diffeomorphic), which is in neither the tree nor Mathlib; the
producer of `zeroLevel_type` (`SlimFibreTypeSequence`, flow of LFR18's vertical field of a
finite-order limit metric) yields only a homeomorphism, and `SlimProductModel`'s factor `W` is a
metric space only.
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set Metric Function
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

section Generic

variable {E₁ H₁ F₁ G₁ G₂ Y₁ N₁ N₂ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [FiniteDimensional ℝ E₁] [TopologicalSpace H₁] {I₁ : ModelWithCorners ℝ E₁ H₁}
  [I₁.Boundaryless] [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [FiniteDimensional ℝ F₁]
  [TopologicalSpace G₁] [TopologicalSpace G₂] {J₁ : ModelWithCorners ℝ F₁ G₁}
  {J₂ : ModelWithCorners ℝ F₁ G₂} [J₁.Boundaryless] [J₂.Boundaryless]
  [TopologicalSpace Y₁] [ChartedSpace H₁ Y₁] [IsManifold I₁ ∞ Y₁]
  [TopologicalSpace N₁] [ChartedSpace G₁ N₁] [IsManifold J₁ ∞ N₁]
  [TopologicalSpace N₂] [ChartedSpace G₂ N₂] [IsManifold J₂ ∞ N₂]

/-- **Regular fibres with the same points are diffeomorphic**: two smooth maps `f₁ : Y → N₁`,
`f₂ : Y → N₂` (same model fibre `F`) regular along levels `b₁`, `b₂` with
`f₁ y = b₁ ↔ f₂ y = b₂` have diffeomorphic regular fibres (identity on points). -/
theorem nonempty_diffeomorph_regularFiber_of_iff_FPRE (f₁ : Y₁ → N₁) (b₁ : N₁)
    (hf₁ : ContMDiff I₁ J₁ ∞ f₁) (hr₁ : ∀ y, f₁ y = b₁ → Surjective (mfderiv I₁ J₁ f₁ y))
    (f₂ : Y₁ → N₂) (b₂ : N₂) (hf₂ : ContMDiff I₁ J₂ ∞ f₂)
    (hr₂ : ∀ y, f₂ y = b₂ → Surjective (mfderiv I₁ J₂ f₂ y))
    (hiff : ∀ y, f₁ y = b₁ ↔ f₂ y = b₂) :
    letI := regularFiberChartedSpace f₁ b₁ hf₁ hr₁
    letI := regularFiberChartedSpace f₂ b₂ hf₂ hr₂
    Nonempty ({y // f₁ y = b₁} ≃ₘ⟮𝓘(ℝ, Fin (Module.finrank ℝ E₁ - Module.finrank ℝ F₁) → ℝ),
      𝓘(ℝ, Fin (Module.finrank ℝ E₁ - Module.finrank ℝ F₁) → ℝ)⟯ {y // f₂ y = b₂}) := by
  let _ := regularFiberChartedSpace f₁ b₁ hf₁ hr₁
  let _ := regularFiberChartedSpace f₂ b₂ hf₂ hr₂
  let φ : {y // f₁ y = b₁} → {y // f₂ y = b₂} := fun y => ⟨y.1, (hiff y.1).mp y.2⟩
  let ψ : {y // f₂ y = b₂} → {y // f₁ y = b₁} := fun y => ⟨y.1, (hiff y.1).mpr y.2⟩
  exact ⟨{ toFun := φ
           invFun := ψ
           left_inv := fun y => rfl
           right_inv := fun y => rfl
           contMDiff_toFun := (contMDiff_regularFiber_iff f₂ b₂ hf₂ hr₂ φ).mpr
             (contMDiff_regularFiberInclusion f₁ b₁ hf₁ hr₁)
           contMDiff_invFun := (contMDiff_regularFiber_iff f₁ b₁ hf₁ hr₁ ψ).mpr
             (contMDiff_regularFiberInclusion f₂ b₂ hf₂ hr₂) }⟩

end Generic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {Δ σ : ℝ}
  {Y : Type*} [MetricSpace Y] {p : M} {y₀ : Y} {β : ℝ}
  {α : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), y₀)) β}

/-- The model of the fibres (`dim M - 1`). -/
local notation "𝓘F" => 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ ℝ) → ℝ)

namespace SlimChart

/-- The restricted coordinate `η : {x ∈ B(p, L) | |η x| < r} → (-r, r)` of a slim chart. -/
abbrev slabMap_FPRE (c : SlimChart g hEnorm Δ σ α) (r : ℝ) :
    realSlabOpens (ball p (10 ^ 6 * Δ)) isOpen_ball c.coord c.lipschitz.continuous.continuousOn r →
      lineBallOpens r :=
  realSlabMap (ball p (10 ^ 6 * Δ)) isOpen_ball c.coord c.lipschitz.continuous.continuousOn r

/-- The restricted coordinate is smooth. -/
theorem contMDiff_slabMap_FPRE (c : SlimChart g hEnorm Δ σ α) (r : ℝ) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (c.slabMap_FPRE r) :=
  contMDiff_realSlabMap isOpen_ball
    (c.contMDiffOn_coord.mono (ball_subset_closedBall.trans c.closedBall_subset_domain)) r

/-- The restricted coordinate is a submersion for `r ≤ 905·10³Δ`. -/
theorem surjective_mfderiv_slabMap_FPRE (c : SlimChart g hEnorm Δ σ α) {r : ℝ}
    (hr : r ≤ 905 * 10 ^ 3 * Δ)
    (x : realSlabOpens (ball p (10 ^ 6 * Δ)) isOpen_ball c.coord
      c.lipschitz.continuous.continuousOn r) :
    Surjective (mfderiv I 𝓘(ℝ, ℝ) (c.slabMap_FPRE r) x) :=
  surjective_mfderiv_realSlabMap isOpen_ball
    (c.contMDiffOn_coord.mono (ball_subset_closedBall.trans c.closedBall_subset_domain))
    (fun y hy hyr => c.regular y hy (hyr.trans_le hr)) x

/-- The regular-fibre smooth structure on the whole fibre `{x ∈ B(p, L) | |η x| < r, η x = a}`. -/
abbrev fibreChartedSpace_FPRE (c : SlimChart g hEnorm Δ σ α) {r : ℝ}
    (hr : r ≤ 905 * 10 ^ 3 * Δ) (a : lineBallOpens r) :
    ChartedSpace (Fin (Module.finrank ℝ E - Module.finrank ℝ ℝ) → ℝ)
      {x // c.slabMap_FPRE r x = a} :=
  regularFiberChartedSpace (c.slabMap_FPRE r) a (c.contMDiff_slabMap_FPRE r)
    (fun x _ => c.surjective_mfderiv_slabMap_FPRE hr x)

/-- The base point `0 ∈ (-905·10³Δ, 905·10³Δ)`. -/
abbrev zeroPoint_FPRE (hΔ : 0 < Δ) : lineBallOpens (905 * 10 ^ 3 * Δ) :=
  ⟨0, zero_mem_lineBallOpens (by positivity)⟩

/-- A point of `(-r, r)` as a point of `(-r', r')`, `r ≤ r'`. -/
abbrev liftPoint_FPRE {r r' : ℝ} (h : r ≤ r') (a : lineBallOpens r) : lineBallOpens r' :=
  ⟨a.1, mem_lineBallOpens_iff.mpr ((mem_lineBallOpens_iff.mp a.2).trans_le h)⟩

/-- Every slab `{x ∈ B(p, L) | |η x| < r}` is σ-compact (open in a σ-compact finite-dimensional
manifold). -/
theorem sigmaCompactSpace_slab_FPRE (c : SlimChart g hEnorm Δ σ α) (r : ℝ) :
    SigmaCompactSpace (realSlabOpens (ball p (10 ^ 6 * Δ)) isOpen_ball c.coord
      c.lipschitz.continuous.continuousOn r) := by
  have : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional I
  have : LocallyCompactSpace (realSlabOpens (ball p (10 ^ 6 * Δ)) isOpen_ball c.coord
      c.lipschitz.continuous.continuousOn r) :=
    (realSlabOpens _ _ _ _ r).isOpen.locallyCompactSpace
  infer_instance

/-- **The whole-fibre slab inclusion**: for `r ≤ r' ≤ 905·10³Δ` and `|a| < r`, the fibre of the
`r`-slab over `a` and the fibre of the `r'`-slab over `a` are diffeomorphic (identity on points). -/
theorem nonempty_diffeomorph_fibre_slab_FPRE (c : SlimChart g hEnorm Δ σ α) {r r' : ℝ}
    (hrr : r ≤ r') (hr' : r' ≤ 905 * 10 ^ 3 * Δ) (a : lineBallOpens r) :
    letI := c.fibreChartedSpace_FPRE (hrr.trans hr') a
    letI := c.fibreChartedSpace_FPRE hr' (liftPoint_FPRE hrr a)
    Nonempty ({x // c.slabMap_FPRE r x = a} ≃ₘ⟮𝓘F, 𝓘F⟯
      {x // c.slabMap_FPRE r' x = liftPoint_FPRE hrr a}) := by
  let _ := c.fibreChartedSpace_FPRE (hrr.trans hr') a
  let _ := c.fibreChartedSpace_FPRE hr' (liftPoint_FPRE hrr a)
  have hsub : realSlabOpens (ball p (10 ^ 6 * Δ)) isOpen_ball c.coord
      c.lipschitz.continuous.continuousOn r ≤ realSlabOpens (ball p (10 ^ 6 * Δ)) isOpen_ball
      c.coord c.lipschitz.continuous.continuousOn r' := fun x hx =>
    mem_realSlabOpens_iff.mpr ⟨(mem_realSlabOpens_iff.mp hx).1,
      (mem_realSlabOpens_iff.mp hx).2.trans_le hrr⟩
  have hval : ∀ y : {x // c.slabMap_FPRE r' x = liftPoint_FPRE hrr a}, c.coord y.1.1 = a.1 :=
    fun y => congrArg Subtype.val y.2
  have hback : ∀ y : {x // c.slabMap_FPRE r' x = liftPoint_FPRE hrr a},
      y.1.1 ∈ realSlabOpens (ball p (10 ^ 6 * Δ)) isOpen_ball c.coord
        c.lipschitz.continuous.continuousOn r := fun y =>
    mem_realSlabOpens_iff.mpr ⟨(mem_realSlabOpens_iff.mp y.1.2).1, by
      rw [hval y]; exact mem_lineBallOpens_iff.mp a.2⟩
  let φ : {x // c.slabMap_FPRE r x = a} → {x // c.slabMap_FPRE r' x = liftPoint_FPRE hrr a} :=
    fun x => ⟨TopologicalSpace.Opens.inclusion hsub x.1,
      Subtype.ext (show c.coord x.1.1 = a.1 from congrArg Subtype.val x.2)⟩
  let ψ : {x // c.slabMap_FPRE r' x = liftPoint_FPRE hrr a} → {x // c.slabMap_FPRE r x = a} :=
    fun y => ⟨⟨y.1.1, hback y⟩, Subtype.ext (hval y)⟩
  have hφ : ContMDiff 𝓘F 𝓘F ∞ φ := by
    refine (contMDiff_regularFiber_iff (c.slabMap_FPRE r') (liftPoint_FPRE hrr a)
      (c.contMDiff_slabMap_FPRE r') (fun x _ => c.surjective_mfderiv_slabMap_FPRE hr' x) φ).mpr ?_
    exact (contMDiff_inclusion hsub).comp (contMDiff_regularFiberInclusion (c.slabMap_FPRE r) a
      (c.contMDiff_slabMap_FPRE r)
      (fun x _ => c.surjective_mfderiv_slabMap_FPRE (hrr.trans hr') x))
  have hψ : ContMDiff 𝓘F 𝓘F ∞ ψ := by
    refine (contMDiff_regularFiber_iff (c.slabMap_FPRE r) a
      (c.contMDiff_slabMap_FPRE r)
      (fun x _ => c.surjective_mfderiv_slabMap_FPRE (hrr.trans hr') x) ψ).mpr ?_
    refine (ContMDiff.subtypeVal_comp_iff _ _).mp ?_
    change ContMDiff 𝓘F I ∞ (fun y : {x // c.slabMap_FPRE r' x = liftPoint_FPRE hrr a} => y.1.1)
    exact contMDiff_subtype_val.comp (contMDiff_regularFiberInclusion (c.slabMap_FPRE r')
      (liftPoint_FPRE hrr a) (c.contMDiff_slabMap_FPRE r')
      (fun x _ => c.surjective_mfderiv_slabMap_FPRE hr' x))
  exact ⟨{ toFun := φ
           invFun := ψ
           left_inv := fun x => rfl
           right_inv := fun y => rfl
           contMDiff_toFun := hφ
           contMDiff_invFun := hψ }⟩

/-- **The whole fibres of the `905·10³Δ`-slab are diffeomorphic to the zero fibre** (LFR20's
trivialization `Θ : F₀ × (-R, R) ≅ U`, restricted to `F₀ × {a}`; `|a| < R < 905·10³Δ`). -/
theorem nonempty_diffeomorph_zeroFibre_FPRE (c : SlimChart g hEnorm Δ σ α) (hΔ : 0 < Δ)
    (a : lineBallOpens (905 * 10 ^ 3 * Δ)) :
    letI := c.fibreChartedSpace_FPRE le_rfl (zeroPoint_FPRE hΔ)
    letI := c.fibreChartedSpace_FPRE le_rfl a
    Nonempty ({x // c.slabMap_FPRE (905 * 10 ^ 3 * Δ) x = zeroPoint_FPRE hΔ} ≃ₘ⟮𝓘F, 𝓘F⟯
      {x // c.slabMap_FPRE (905 * 10 ^ 3 * Δ) x = a}) := by
  let _ := c.fibreChartedSpace_FPRE le_rfl (zeroPoint_FPRE hΔ)
  let _ := c.fibreChartedSpace_FPRE le_rfl a
  have ha : |(a : ℝ)| < 905 * 10 ^ 3 * Δ := mem_lineBallOpens_iff.mp a.2
  have hR : 0 < (|(a : ℝ)| + 905 * 10 ^ 3 * Δ) / 2 := by
    have := abs_nonneg (a : ℝ); linarith
  have hRr : (|(a : ℝ)| + 905 * 10 ^ 3 * Δ) / 2 < 905 * 10 ^ 3 * Δ := by linarith
  obtain ⟨-, Θ, hΘ1, -⟩ := c.trivial _ hR hRr
  have haR : a ∈ lineBallInner (905 * 10 ^ 3 * Δ) ((|(a : ℝ)| + 905 * 10 ^ 3 * Δ) / 2) :=
    mem_lineBallInner_iff.mpr (by linarith)
  let φ : {x // c.slabMap_FPRE (905 * 10 ^ 3 * Δ) x = zeroPoint_FPRE hΔ} →
      {x // c.slabMap_FPRE (905 * 10 ^ 3 * Δ) x = a} :=
    fun x => ⟨(Θ (x, ⟨a, haR⟩)).1, hΘ1 _⟩
  let ψ : {x // c.slabMap_FPRE (905 * 10 ^ 3 * Δ) x = a} →
      {x // c.slabMap_FPRE (905 * 10 ^ 3 * Δ) x = zeroPoint_FPRE hΔ} :=
    fun y => (Θ.symm ⟨y.1, show c.slabMap_FPRE _ y.1 ∈ lineBallInner _ _ by
      rw [y.2]; exact haR⟩).1
  have hφ : ContMDiff 𝓘F 𝓘F ∞ φ := by
    refine (contMDiff_regularFiber_iff (c.slabMap_FPRE (905 * 10 ^ 3 * Δ)) a
      (c.contMDiff_slabMap_FPRE _) (fun x _ => c.surjective_mfderiv_slabMap_FPRE le_rfl x)
      φ).mpr ?_
    exact contMDiff_subtype_val.comp (Θ.contMDiff.comp (contMDiff_id.prodMk contMDiff_const))
  have hψ : ContMDiff 𝓘F 𝓘F ∞ ψ := by
    refine contMDiff_fst.comp (Θ.symm.contMDiff.comp ?_)
    refine (ContMDiff.subtypeVal_comp_iff _ _).mp ?_
    exact contMDiff_regularFiberInclusion (c.slabMap_FPRE (905 * 10 ^ 3 * Δ)) a
      (c.contMDiff_slabMap_FPRE _) (fun x _ => c.surjective_mfderiv_slabMap_FPRE le_rfl x)
  refine ⟨{ toFun := φ
            invFun := ψ
            left_inv := fun x => ?_
            right_inv := fun y => ?_
            contMDiff_toFun := hφ
            contMDiff_invFun := hψ }⟩
  · change (Θ.symm ⟨(Θ (x, ⟨a, haR⟩)).1, _⟩).1 = x
    rw [show (⟨(Θ (x, ⟨a, haR⟩)).1, _⟩ : _) = Θ (x, ⟨a, haR⟩) from rfl, Θ.symm_apply_apply]
  · apply Subtype.ext
    change (Θ ((Θ.symm ⟨y.1, _⟩).1, ⟨a, haR⟩)).1 = y.1
    set q := Θ.symm ⟨y.1, show c.slabMap_FPRE _ y.1 ∈ lineBallInner _ _ by
      rw [y.2]; exact haR⟩ with hq
    have hq2 : q.2 = ⟨a, haR⟩ := by
      apply Subtype.ext
      have h1 := hΘ1 q
      rw [hq, Θ.apply_symm_apply] at h1
      exact h1.symm.trans y.2
    have : (q.1, (⟨a, haR⟩ : lineBallInner _ _)) = q := by rw [← hq2]
    rw [this, hq, Θ.apply_symm_apply]

/-- **Every whole fibre of every slab is diffeomorphic to the zero fibre**: for `r ≤ 905·10³Δ` and
`|a| < r`, the fibre `{x ∈ B(p, L) | |η x| < r, η x = a}` with its regular-fibre structure is
diffeomorphic to the zero fibre `F₀` of the `905·10³Δ`-slab. -/
theorem nonempty_diffeomorph_fibre_FPRE (c : SlimChart g hEnorm Δ σ α) (hΔ : 0 < Δ) {r : ℝ}
    (hr : r ≤ 905 * 10 ^ 3 * Δ) (a : lineBallOpens r) :
    letI := c.fibreChartedSpace_FPRE le_rfl (zeroPoint_FPRE hΔ)
    letI := c.fibreChartedSpace_FPRE hr a
    Nonempty ({x // c.slabMap_FPRE (905 * 10 ^ 3 * Δ) x = zeroPoint_FPRE hΔ} ≃ₘ⟮𝓘F, 𝓘F⟯
      {x // c.slabMap_FPRE r x = a}) := by
  let _ := c.fibreChartedSpace_FPRE le_rfl (zeroPoint_FPRE hΔ)
  let _ := c.fibreChartedSpace_FPRE hr a
  let _ := c.fibreChartedSpace_FPRE le_rfl (liftPoint_FPRE hr a)
  obtain ⟨Φ⟩ := c.nonempty_diffeomorph_zeroFibre_FPRE hΔ (liftPoint_FPRE hr a)
  obtain ⟨Ψ⟩ := c.nonempty_diffeomorph_fibre_slab_FPRE hr le_rfl a
  exact ⟨Φ.trans Ψ.symm⟩

/-- The zero fibre `F₀` of the slab map, as a subtype of the slab, is homeomorphic to the zero
level `{x ∈ B(p, L) | η x = 0}` (the subtype of `SlimPacket.zeroLevel_connected` /
`zeroLevel_type`); identity on points. -/
def zeroFibreHomeomorph_FPRE (c : SlimChart g hEnorm Δ σ α) (hΔ : 0 < Δ) :
    {x // c.slabMap_FPRE (905 * 10 ^ 3 * Δ) x = zeroPoint_FPRE hΔ} ≃ₜ
      {x // x ∈ ball p (10 ^ 6 * Δ) ∧ c.coord x = 0} where
  toFun x := ⟨x.1.1, (mem_realSlabOpens_iff.mp x.1.2).1, congrArg Subtype.val x.2⟩
  invFun y := ⟨⟨y.1, mem_realSlabOpens_iff.mpr ⟨y.2.1, by rw [y.2.2, abs_zero]; positivity⟩⟩,
    Subtype.ext y.2.2⟩
  left_inv x := rfl
  right_inv y := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

/-- **The whole fibre is the whole level set**: for `|a| < r`, the points of the fibre of the
`r`-slab over `a` are exactly the points of `B(p, L)` where `η = a`. -/
theorem range_fibre_FPRE (c : SlimChart g hEnorm Δ σ α) {r : ℝ} (a : lineBallOpens r) :
    range (fun x : {x // c.slabMap_FPRE r x = a} => (x.1 : M)) =
      {x | x ∈ ball p (10 ^ 6 * Δ) ∧ c.coord x = a} := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨(mem_realSlabOpens_iff.mp y.1.2).1, congrArg Subtype.val y.2⟩
  · rintro ⟨hx, hxa⟩
    have hxS : x ∈ realSlabOpens (ball p (10 ^ 6 * Δ)) isOpen_ball c.coord
        c.lipschitz.continuous.continuousOn r :=
      mem_realSlabOpens_iff.mpr ⟨hx, by rw [hxa]; exact mem_lineBallOpens_iff.mp a.2⟩
    exact ⟨⟨⟨x, hxS⟩, Subtype.ext hxa⟩, rfl⟩

/-- The part `{|η| < R}` of the `905·10³Δ`-slab, as an open subset of the slab (the codomain of
LFR20's trivialization over `(-R, R)`). -/
abbrev slabInner_FPRE (c : SlimChart g hEnorm Δ σ α) (R : ℝ) :
    TopologicalSpace.Opens (realSlabOpens (ball p (10 ^ 6 * Δ)) isOpen_ball c.coord
      c.lipschitz.continuous.continuousOn (905 * 10 ^ 3 * Δ)) :=
  ⟨c.slabMap_FPRE (905 * 10 ^ 3 * Δ) ⁻¹' lineBallInner (905 * 10 ^ 3 * Δ) R,
    (lineBallInner (905 * 10 ^ 3 * Δ) R).isOpen.preimage (continuous_realSlabMap isOpen_ball _ _)⟩

/-- Images of `F₀ × {t : P t}` under a trivialization over `(-R, R)`: if `P t → |t| < R`, the image
is exactly `{x ∈ B(p, L) | P (η x)}` (WHOLE level sets, no point of the ball is missed). -/
theorem image_trivialization_FPRE (c : SlimChart g hEnorm Δ σ α) (hΔ : 0 < Δ) {R : ℝ}
    (hRr : R < 905 * 10 ^ 3 * Δ)
    (Θ : {x // c.slabMap_FPRE (905 * 10 ^ 3 * Δ) x = zeroPoint_FPRE hΔ} ×
      lineBallInner (905 * 10 ^ 3 * Δ) R ≃ c.slabInner_FPRE R)
    (hΘ : ∀ q, c.slabMap_FPRE (905 * 10 ^ 3 * Δ) (Θ q).1 = q.2.1) {P : ℝ → Prop}
    (hP : ∀ t, P t → |t| < R) :
    (fun q => ((Θ q).1 : M)) '' {q | P (q.2 : ℝ)} =
      {x | x ∈ ball p (10 ^ 6 * Δ) ∧ P (c.coord x)} := by
  have hc : ∀ q, c.coord (Θ q).1.1 = q.2.1.1 := fun q => congrArg Subtype.val (hΘ q)
  ext x
  constructor
  · rintro ⟨q, hq, rfl⟩
    refine ⟨(mem_realSlabOpens_iff.mp (Θ q).1.2).1, ?_⟩
    change P (c.coord (Θ q).1.1)
    rw [hc q]
    exact hq
  · rintro ⟨hx, hPx⟩
    have hxR := hP _ hPx
    have hxS : x ∈ realSlabOpens (ball p (10 ^ 6 * Δ)) isOpen_ball c.coord
        c.lipschitz.continuous.continuousOn (905 * 10 ^ 3 * Δ) :=
      mem_realSlabOpens_iff.mpr ⟨hx, hxR.trans hRr⟩
    have hxU : (⟨x, hxS⟩ : realSlabOpens _ _ _ _ _) ∈ c.slabInner_FPRE R :=
      mem_lineBallInner_iff.mpr hxR
    refine ⟨Θ.symm ⟨⟨x, hxS⟩, hxU⟩, ?_, ?_⟩
    · have h := hc (Θ.symm ⟨⟨x, hxS⟩, hxU⟩)
      rw [Θ.apply_symm_apply] at h
      change P ((Θ.symm ⟨⟨x, hxS⟩, hxU⟩).2 : ℝ)
      rw [← h]
      exact hPx
    · change ((Θ (Θ.symm ⟨⟨x, hxS⟩, hxU⟩)).1 : M) = x
      rw [Θ.apply_symm_apply]

/-- **Relative (boundary) version of the slab bundle**: for `0 ≤ r < 905·10³Δ` there are
`r < R < 905·10³Δ` and LFR20's diffeomorphism `Θ : F₀ × (-R, R) ≅ {|η| < R}` (`η ∘ Θ = pr₂`,
`Θ(·, 0)` the inclusion of `F₀`) carrying `F₀ × [-r, r]` ONTO the whole closed slab
`{x ∈ B(p, L) | |η x| ≤ r}` and `F₀ × {±r}` ONTO its boundary fibres `{x ∈ B(p, L) | |η x| = r}`;
so the closed slab is the image of `F₀ × [-r, r]` under a diffeomorphism defined on the open
neighbourhood `F₀ × (-R, R)`. -/
theorem closedSlab_product_FPRE (c : SlimChart g hEnorm Δ σ α) (hΔ : 0 < Δ) {r : ℝ}
    (hr0 : 0 ≤ r) (hr : r < 905 * 10 ^ 3 * Δ) :
    letI := c.fibreChartedSpace_FPRE le_rfl (zeroPoint_FPRE hΔ)
    ∃ R, r < R ∧ R < 905 * 10 ^ 3 * Δ ∧
      ∃ (hy : zeroPoint_FPRE hΔ ∈ lineBallInner (905 * 10 ^ 3 * Δ) R)
        (Θ : ({x // c.slabMap_FPRE (905 * 10 ^ 3 * Δ) x = zeroPoint_FPRE hΔ} ×
          lineBallInner (905 * 10 ^ 3 * Δ) R) ≃ₘ⟮ModelWithCorners.prod 𝓘F 𝓘(ℝ, ℝ), I⟯
            c.slabInner_FPRE R),
        (∀ q, c.slabMap_FPRE (905 * 10 ^ 3 * Δ) (Θ q).1 = q.2.1) ∧
        (∀ x, (Θ (x, ⟨zeroPoint_FPRE hΔ, hy⟩)).1 = x.1) ∧
        (fun q => ((Θ q).1 : M)) '' {q | |(q.2 : ℝ)| ≤ r} =
          {x | x ∈ ball p (10 ^ 6 * Δ) ∧ |c.coord x| ≤ r} ∧
        (fun q => ((Θ q).1 : M)) '' {q | |(q.2 : ℝ)| = r} =
          {x | x ∈ ball p (10 ^ 6 * Δ) ∧ |c.coord x| = r} := by
  let _ := c.fibreChartedSpace_FPRE le_rfl (zeroPoint_FPRE hΔ)
  have hR : 0 < (r + 905 * 10 ^ 3 * Δ) / 2 := by linarith
  have hRr : (r + 905 * 10 ^ 3 * Δ) / 2 < 905 * 10 ^ 3 * Δ := by linarith
  obtain ⟨hy, Θ, hΘ1, hΘ2⟩ := c.trivial _ hR hRr
  refine ⟨(r + 905 * 10 ^ 3 * Δ) / 2, by linarith, hRr, hy, Θ, hΘ1, hΘ2, ?_, ?_⟩
  · exact c.image_trivialization_FPRE hΔ hRr Θ.toEquiv hΘ1 (P := fun t => |t| ≤ r)
      (fun t ht => by linarith)
  · exact c.image_trivialization_FPRE hΔ hRr Θ.toEquiv hΘ1 (P := fun t => |t| = r)
      (fun t ht => by linarith)

/-- **Every whole fibre is a smoothly embedded copy of the zero fibre**: for `|a| < 905·10³Δ` there
is a smooth embedding `ι : F₀ → M` (smooth, topological embedding, injective differential) whose
image is the WHOLE level set `{x ∈ B(p, L) | η x = a}`. -/
theorem exists_embedding_fibre_FPRE (c : SlimChart g hEnorm Δ σ α) (hΔ : 0 < Δ)
    (a : lineBallOpens (905 * 10 ^ 3 * Δ)) :
    letI := c.fibreChartedSpace_FPRE le_rfl (zeroPoint_FPRE hΔ)
    ∃ ι : {x // c.slabMap_FPRE (905 * 10 ^ 3 * Δ) x = zeroPoint_FPRE hΔ} → M,
      ContMDiff 𝓘F I ∞ ι ∧ Topology.IsEmbedding ι ∧ (∀ y, Injective (mfderiv 𝓘F I ι y)) ∧
      range ι = {x | x ∈ ball p (10 ^ 6 * Δ) ∧ c.coord x = a} := by
  let _ := c.fibreChartedSpace_FPRE le_rfl (zeroPoint_FPRE hΔ)
  let _ := c.fibreChartedSpace_FPRE le_rfl a
  have _ := regularFiberIsManifold (c.slabMap_FPRE (905 * 10 ^ 3 * Δ)) (zeroPoint_FPRE hΔ)
    (c.contMDiff_slabMap_FPRE _) (fun x _ => c.surjective_mfderiv_slabMap_FPRE le_rfl x)
  have _ := regularFiberIsManifold (c.slabMap_FPRE (905 * 10 ^ 3 * Δ)) a
    (c.contMDiff_slabMap_FPRE _) (fun x _ => c.surjective_mfderiv_slabMap_FPRE le_rfl x)
  obtain ⟨Φ⟩ := c.nonempty_diffeomorph_fibre_FPRE hΔ le_rfl a
  have hinc := contMDiff_regularFiberInclusion (c.slabMap_FPRE (905 * 10 ^ 3 * Δ)) a
    (c.contMDiff_slabMap_FPRE _) (fun x _ => c.surjective_mfderiv_slabMap_FPRE le_rfl x)
  refine ⟨(Subtype.val : realSlabOpens (ball p (10 ^ 6 * Δ)) isOpen_ball c.coord
      c.lipschitz.continuous.continuousOn (905 * 10 ^ 3 * Δ) → M) ∘
    (Subtype.val : {x // c.slabMap_FPRE (905 * 10 ^ 3 * Δ) x = a} → _) ∘ Φ,
    contMDiff_subtype_val.comp (hinc.comp Φ.contMDiff),
    Topology.IsEmbedding.subtypeVal.comp
      (Topology.IsEmbedding.subtypeVal.comp Φ.toHomeomorph.isEmbedding), fun y => ?_, ?_⟩
  · have hΦd : MDifferentiableAt 𝓘F 𝓘F Φ y :=
      Φ.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
    have hFd := (hinc (Φ y)).mdifferentiableAt (by simp)
    have h2 := (hasMFDerivAt_subtype_val (I := I) _ _).comp y
      (hFd.hasMFDerivAt.comp y hΦd.hasMFDerivAt)
    rw [h2.mfderiv]
    have hd1 : MDifferentiableAt 𝓘F 𝓘F Φ.symm (Φ y) :=
      Φ.symm.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
    have hcomp : (mfderiv 𝓘F 𝓘F Φ.symm (Φ y)).comp (mfderiv 𝓘F 𝓘F Φ y) =
        ContinuousLinearMap.id ℝ _ := by
      rw [← mfderiv_comp y hd1 hΦd]
      have hid : (Φ.symm ∘ Φ) = id := funext Φ.symm_apply_apply
      rw [hid, mfderiv_id]
    have hinjF := mfderiv_regularFiberInclusion_injective (c.slabMap_FPRE (905 * 10 ^ 3 * Δ)) a
      (c.contMDiff_slabMap_FPRE _) (fun x _ => c.surjective_mfderiv_slabMap_FPRE le_rfl x) (Φ y)
    have key : ∀ w, mfderiv 𝓘F 𝓘F Φ.symm (Φ y) (mfderiv 𝓘F 𝓘F Φ y w) = w :=
      fun w => congrArg (fun L => L w) hcomp
    intro u v huv
    rw [← key u, ← key v]
    exact congrArg _ (hinjF huv)
  · change range ((fun x : {x // c.slabMap_FPRE (905 * 10 ^ 3 * Δ) x = a} => (x.1 : M)) ∘ Φ) = _
    rw [(show Surjective Φ from Φ.surjective).range_comp, c.range_fibre_FPRE a]

end SlimChart

namespace SlimPacket

/-- **GAF07's smooth-type bridge for an original slim piece** (review 53 §2.1, GAF07 remark: the
field `zeroLevel_type` is a homeomorphism and is NOT used as a diffeomorphism). For `r ≤ 905·10³Δ`
and `|a| < r`, the WHOLE fibre `F_a = {x ∈ B(p, L) | |η x| < r, η x = a}` with its regular-fibre
smooth structure is a smooth manifold DIFFEOMORPHIC to the zero fibre `F₀` (via LFR20's
trivialization); `F_a` is compact, connected and homeomorphic to `S²` or to `T²`; and the points of
`F_a` are exactly the level set `{x ∈ B(p, L) | η x = a}`. -/
theorem smooth_fibre_type_FPRE (P : SlimPacket g hEnorm Δ σ α) (hΔ : 0 < Δ) {r : ℝ}
    (hr : r ≤ 905 * 10 ^ 3 * Δ) (a : lineBallOpens r) :
    letI := P.fibreChartedSpace_FPRE le_rfl (SlimChart.zeroPoint_FPRE hΔ)
    letI := P.fibreChartedSpace_FPRE hr a
    IsManifold 𝓘F ∞ {x // P.slabMap_FPRE r x = a} ∧
      Nonempty ({x // P.slabMap_FPRE (905 * 10 ^ 3 * Δ) x = SlimChart.zeroPoint_FPRE hΔ}
        ≃ₘ⟮𝓘F, 𝓘F⟯ {x // P.slabMap_FPRE r x = a}) ∧
      CompactSpace {x // P.slabMap_FPRE r x = a} ∧
      ConnectedSpace {x // P.slabMap_FPRE r x = a} ∧
      (Nonempty ({x // P.slabMap_FPRE r x = a} ≃ₜ
          Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∨
        Nonempty ({x // P.slabMap_FPRE r x = a} ≃ₜ (AddCircle (1 : ℝ) × AddCircle (1 : ℝ)))) ∧
      range (fun x : {x // P.slabMap_FPRE r x = a} => (x.1 : M)) =
        {x | x ∈ ball p (10 ^ 6 * Δ) ∧ P.coord x = a} := by
  let _ := P.fibreChartedSpace_FPRE le_rfl (SlimChart.zeroPoint_FPRE hΔ)
  let _ := P.fibreChartedSpace_FPRE hr a
  obtain ⟨Φ⟩ := P.nonempty_diffeomorph_fibre_FPRE hΔ hr a
  let ψ := (P.zeroFibreHomeomorph_FPRE hΔ).symm.trans Φ.toHomeomorph
  have hcpt : CompactSpace {x // x ∈ ball p (10 ^ 6 * Δ) ∧ P.coord x = 0} :=
    isCompact_iff_compactSpace.mp (SlimChart.isCompact_zeroLevel hΔ P.toSlimChart).1
  have hconn := P.zeroLevel_connected
  refine ⟨regularFiberIsManifold (P.slabMap_FPRE r) a (P.contMDiff_slabMap_FPRE r)
      (fun x _ => P.surjective_mfderiv_slabMap_FPRE hr x), ⟨Φ⟩, ψ.compactSpace,
    ψ.connectedSpace_iff.mp hconn, ?_, P.range_fibre_FPRE a⟩
  rcases P.zeroLevel_type with ⟨⟨d⟩⟩ | ⟨⟨d⟩⟩
  · exact Or.inl ⟨ψ.symm.trans d⟩
  · exact Or.inr ⟨ψ.symm.trans d⟩

/-- **Consumer: GAF07's slim fibre type through FC34a.** Let `h : Y × ℝ → ℝ` be a smooth family on
the slab `Y = {x ∈ B(p, L) | |η x| < r}` (`r ≤ 905·10³Δ`) starting at the ORIGINAL coordinate
(`h(·, 0) = η`), regular along the level `a` (`|a| < r`) for `τ ∈ [0, 1]`, with its whole trace in
one compact `Q` (GAF07's straight line `h_τ = (1-τ)η + τg` with these inputs). Then the WHOLE level
`{h(·, 1) = a}` with its regular-fibre structure is diffeomorphic to the original zero fibre `F₀`,
and is compact, connected and homeomorphic to `S²` or `T²`. -/
theorem gaf07_slim_fibre_type_FPRE (P : SlimPacket g hEnorm Δ σ α) (hΔ : 0 < Δ) {r : ℝ}
    (hr : r ≤ 905 * 10 ^ 3 * Δ) (a : lineBallOpens r)
    (h : realSlabOpens (ball p (10 ^ 6 * Δ)) isOpen_ball P.coord
      P.lipschitz.continuous.continuousOn r × ℝ → ℝ)
    (hh : ContMDiff (I.prod 𝓘(ℝ)) 𝓘(ℝ, ℝ) ∞ h) (h0 : ∀ y, h (y, 0) = P.coord y.1)
    (hreg : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ y, h (y, τ) = a.1 →
      Surjective (mfderiv I 𝓘(ℝ, ℝ) (fun z => h (z, τ)) y))
    {Q : Set (realSlabOpens (ball p (10 ^ 6 * Δ)) isOpen_ball P.coord
      P.lipschitz.continuous.continuousOn r)} (hQ : IsCompact Q)
    (hloc : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ y, h (y, τ) = a.1 → y ∈ Q) :
    letI := P.fibreChartedSpace_FPRE le_rfl (SlimChart.zeroPoint_FPRE hΔ)
    letI := regularFiberChartedSpace (fun y => h (y, 1)) a.1 (contMDiff_familySlice hh 1)
      (hreg 1 (right_mem_Icc.mpr zero_le_one))
    Nonempty ({x // P.slabMap_FPRE (905 * 10 ^ 3 * Δ) x = SlimChart.zeroPoint_FPRE hΔ}
        ≃ₘ⟮𝓘F, 𝓘F⟯ {y // h (y, 1) = a.1}) ∧
      CompactSpace {y // h (y, 1) = a.1} ∧ ConnectedSpace {y // h (y, 1) = a.1} ∧
      (Nonempty ({y // h (y, 1) = a.1} ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∨
        Nonempty ({y // h (y, 1) = a.1} ≃ₜ (AddCircle (1 : ℝ) × AddCircle (1 : ℝ)))) := by
  have := P.sigmaCompactSpace_slab_FPRE r
  let _ := P.fibreChartedSpace_FPRE le_rfl (SlimChart.zeroPoint_FPRE hΔ)
  let _ := P.fibreChartedSpace_FPRE hr a
  let _ := regularFiberChartedSpace (fun y => h (y, 0)) a.1 (contMDiff_familySlice hh 0)
    (hreg 0 (left_mem_Icc.mpr zero_le_one))
  let _ := regularFiberChartedSpace (fun y => h (y, 1)) a.1 (contMDiff_familySlice hh 1)
    (hreg 1 (right_mem_Icc.mpr zero_le_one))
  obtain ⟨-, ⟨Φ₁⟩, hcpt, hconn, htype, -⟩ := P.smooth_fibre_type_FPRE hΔ hr a
  obtain ⟨Φ₂⟩ := nonempty_diffeomorph_regularFiber_of_iff_FPRE (P.slabMap_FPRE r) a
    (P.contMDiff_slabMap_FPRE r) (fun x _ => P.surjective_mfderiv_slabMap_FPRE hr x)
    (fun y => h (y, 0)) a.1 (contMDiff_familySlice hh 0)
    (hreg 0 (left_mem_Icc.mpr zero_le_one)) (fun y => by
      rw [h0 y]
      exact ⟨fun hy => congrArg Subtype.val hy, fun hy => Subtype.ext hy⟩)
  obtain ⟨Φ₃⟩ := nonempty_diffeomorph_levelSet_of_compact_transport h hh a.1 hreg hQ hloc
  let ψ := Φ₃.toHomeomorph.symm.trans Φ₂.toHomeomorph.symm
  have := hcpt
  refine ⟨⟨(Φ₁.trans Φ₂).trans Φ₃⟩, ψ.symm.compactSpace, ψ.symm.connectedSpace_iff.mp hconn, ?_⟩
  rcases htype with ⟨⟨d⟩⟩ | ⟨⟨d⟩⟩
  · exact Or.inl ⟨ψ.trans d⟩
  · exact Or.inr ⟨ψ.trans d⟩

end SlimPacket

end DifferentialGeometry.Geometry.Collapse
