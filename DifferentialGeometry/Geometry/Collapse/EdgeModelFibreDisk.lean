import DifferentialGeometry.Geometry.Collapse.EdgeInterpolationDiskBundle
import DifferentialGeometry.Geometry.Collapse.FiniteSurface.EdgeCoreBinding
import DifferentialGeometry.Topology.Embedding.Lift
import DifferentialGeometry.Topology.Manifold.OpenSubtype

/-!
# LFR28 I6: the model fibre is a closed smooth disk

Blueprint 207A, LFR28 (`thm:collapse-finite-source-edge-packet`, A:27223), step 1 last paragraph
("Its whole `4Δ` sublevel is the compact smooth disk there") and step 4 ("The model fiber is a smooth
disk by LFR24 ... This also proves connectedness"), item I6(d) of build-logs/worker-F7-LFR28B.md.

* `nonempty_diffeomorph_regularSublevel_of_lift` (kernel): a regular sublevel `{Ψ = 0, 0 ≤ B}` (lane
  SUB-BDY's manifold with boundary) is diffeomorphic to `P` when a smooth `σ : P → M` maps onto it and
  a smooth `π : M → Z` carries `σ` to a smooth embedding `b : P → Z`. The inverse is the lift of
  `π ∘ val` through `b` (`IsSmoothEmbedding.lift`), so no inverse function theorem is needed.
* `nonempty_diffeomorph_cylinderFibre_of_embedding`: the product form on an open `U ⊆ ℝ × Z` with the
  model map `(t, Δ g)`, for any surface model `J`.
* `edgeModelCylinder` (LFR24's buffered cylinder `(-6Δ, 6Δ) × B_Z(z₀, 9)`) with the smoothness and
  regularity of the model map `(t, Δ h)` from LFR24's clauses (`dh ≠ 0` on `{r < 9, h = 4}`).
* `edgeModelCylinder_fibre_closedCell` (**I6 assembly**): the model fibre `{t = 0, Δ h ≤ 4Δ}` in that
  cylinder is diffeomorphic to `ClosedCell 2`, compact, connected, with boundary exactly `h = 4`.
* `finiteSurface_edge_model_fibre_closedCell`: the same with LFR24 (`finiteSurface_edge_model_core`)
  supplying `h` and the disk embedding, in the row's quantifier order.
* `edgeModelCylinder_disk_bundle` (**LFR28.1 with disk fibre, abstract**): combined with F7-LFR28B's
  `edgeInterp_disk_bundle`, the source fibre `{f = 0, H ≤ 4Δ}` is a closed smooth disk (compact,
  connected), `f` is trivial over `(a₀, b₀)` with that fibre, and its boundary is `H = 4Δ`.

The orientation of the surface (U4) enters only as LFR24's own hypothesis `o`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Manifold.RegularLevel DifferentialGeometry.Topology

section Kernel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] {d : ℕ}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {H' : Type*} [TopologicalSpace H']
  {J : ModelWithCorners ℝ F H'} {Z : Type*} [TopologicalSpace Z] [ChartedSpace H' Z]
  {P : Type*} [TopologicalSpace P] [ChartedSpace (EuclideanHalfSpace (d + 1)) P]

/-- **A regular sublevel parametrized through a smooth embedding.** If a smooth `σ : P → M` maps
onto the regular sublevel `{Ψ = 0, 0 ≤ B}` and a smooth `π : M → Z` carries `σ` to a smooth
embedding `b`, then `P` and the sublevel (lane SUB-BDY's structure) are diffeomorphic. -/
theorem nonempty_diffeomorph_regularSublevel_of_lift
    (hdim : Module.finrank ℝ E = d + 1 + Module.finrank ℝ G)
    {Ψ : M → G} (hΨ : ContMDiff I 𝓘(ℝ, G) ∞ Ψ) {B : M → ℝ} (hB : ContMDiff I 𝓘(ℝ, ℝ) ∞ B)
    (hreg : ∀ x, Ψ x = 0 → 0 ≤ B x → Surjective (mfderiv I 𝓘(ℝ, G) Ψ x))
    (hregb : ∀ x, Ψ x = 0 → B x = 0 →
      Surjective (mfderiv I 𝓘(ℝ, G × ℝ) (fun y => (Ψ y, B y)) x))
    {b : P → Z} (hb : IsSmoothEmbedding (𝓡∂ (d + 1)) J ∞ b)
    {π : M → Z} (hπ : ContMDiff I J ∞ π) {σ : P → M} (hσ : ContMDiff (𝓡∂ (d + 1)) I ∞ σ)
    (hσS : ∀ c, Ψ (σ c) = 0 ∧ 0 ≤ B (σ c)) (hπσ : ∀ c, π (σ c) = b c)
    (hSσ : ∀ x, Ψ x = 0 → 0 ≤ B x → ∃ c, σ c = x) :
    letI := regularSublevelChartedSpace hdim hΨ hB hreg hregb
    Nonempty (P ≃ₘ⟮𝓡∂ (d + 1), 𝓡∂ (d + 1)⟯ {x : M // Ψ x = 0 ∧ 0 ≤ B x}) := by
  let _ := regularSublevelChartedSpace hdim hΨ hB hreg hregb
  let φ : P → {x : M // Ψ x = 0 ∧ 0 ≤ B x} := fun c => ⟨σ c, hσS c⟩
  have hφ : ContMDiff (𝓡∂ (d + 1)) (𝓡∂ (d + 1)) ∞ φ :=
    (regularSublevel_contMDiff_iff hdim hΨ hB hreg hregb).mpr hσ
  let g : {x : M // Ψ x = 0 ∧ 0 ≤ B x} → Z := fun y => π y
  have hg : ContMDiff (𝓡∂ (d + 1)) J ∞ g :=
    hπ.comp (regularSublevel_contMDiff_val hdim hΨ hB hreg hregb)
  have hgb : range g ⊆ range b := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨c, hc⟩ := hSσ y y.2.1 y.2.2
    exact ⟨c, by rw [← hπσ, hc]⟩
  have hbψ : ∀ y, b (hb.lift g hgb y) = π y := hb.comp_lift hgb
  have hleft : ∀ c, hb.lift g hgb (φ c) = c := fun c =>
    hb.isEmbedding.injective (by rw [hbψ]; exact hπσ c)
  have hright : ∀ y, φ (hb.lift g hgb y) = y := by
    intro y
    obtain ⟨c, hc⟩ := hSσ y y.2.1 y.2.2
    have hy : hb.lift g hgb y = c :=
      hb.isEmbedding.injective (by rw [hbψ, ← hπσ, hc])
    apply Subtype.ext
    change σ (hb.lift g hgb y) = (y : M)
    rw [hy, hc]
  exact ⟨{ toFun := φ
           invFun := hb.lift g hgb
           left_inv := hleft
           right_inv := hright
           contMDiff_toFun := hφ
           contMDiff_invFun := hb.contMDiff_lift hg hgb }⟩

end Kernel

section Cylinder

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}

/-- **Product form.** On an open `U ⊆ ℝ × Z` with model map `(t, Δ g)`, a smooth embedding `b`
onto the slice `{z | (0, z) ∈ U, Δ g z ≤ e}` parametrizes the regular sublevel
`{t = 0, Δ g ≤ e}` diffeomorphically. -/
theorem nonempty_diffeomorph_cylinderFibre_of_embedding [J.Boundaryless] {Z : Type*}
    [TopologicalSpace Z] [ChartedSpace H' Z] [IsManifold J ∞ Z] {d : ℕ} {P : Type*}
    [TopologicalSpace P] [ChartedSpace (EuclideanHalfSpace (d + 1)) P]
    (hdim : Module.finrank ℝ (ℝ × F) = d + 1 + Module.finrank ℝ ℝ)
    (U : TopologicalSpace.Opens (ℝ × Z)) {g : Z → ℝ} {Δ e : ℝ}
    (hΨ : ContMDiff (𝓘(ℝ, ℝ).prod J) 𝓘(ℝ, ℝ) ∞
      (fun x : U => (((x : ℝ × Z).1, Δ * g (x : ℝ × Z).2) : ℝ × ℝ).1))
    (hB : ContMDiff (𝓘(ℝ, ℝ).prod J) 𝓘(ℝ, ℝ) ∞
      (fun x : U => e - (((x : ℝ × Z).1, Δ * g (x : ℝ × Z).2) : ℝ × ℝ).2))
    (hreg : ∀ x : U, (((x : ℝ × Z).1, Δ * g (x : ℝ × Z).2) : ℝ × ℝ).1 = 0 →
      0 ≤ e - (((x : ℝ × Z).1, Δ * g (x : ℝ × Z).2) : ℝ × ℝ).2 →
      Surjective (mfderiv (𝓘(ℝ, ℝ).prod J) 𝓘(ℝ, ℝ)
        (fun x : U => (((x : ℝ × Z).1, Δ * g (x : ℝ × Z).2) : ℝ × ℝ).1) x))
    (hregb : ∀ x : U, (((x : ℝ × Z).1, Δ * g (x : ℝ × Z).2) : ℝ × ℝ).1 = 0 →
      e - (((x : ℝ × Z).1, Δ * g (x : ℝ × Z).2) : ℝ × ℝ).2 = 0 →
      Surjective (mfderiv (𝓘(ℝ, ℝ).prod J) 𝓘(ℝ, ℝ × ℝ)
        (fun y : U => ((((y : ℝ × Z).1, Δ * g (y : ℝ × Z).2) : ℝ × ℝ).1,
          e - (((y : ℝ × Z).1, Δ * g (y : ℝ × Z).2) : ℝ × ℝ).2)) x))
    {b : P → Z} (hb : IsSmoothEmbedding (𝓡∂ (d + 1)) J ∞ b)
    (hrange : range b = {z | ((0 : ℝ), z) ∈ U ∧ Δ * g z ≤ e}) :
    letI := regularSublevelChartedSpace hdim hΨ hB hreg hregb
    Nonempty (P ≃ₘ⟮𝓡∂ (d + 1), 𝓡∂ (d + 1)⟯
      {x : U // (((x : ℝ × Z).1, Δ * g (x : ℝ × Z).2) : ℝ × ℝ).1 = 0 ∧
        0 ≤ e - (((x : ℝ × Z).1, Δ * g (x : ℝ × Z).2) : ℝ × ℝ).2}) := by
  have hmem : ∀ c, ((0 : ℝ), b c) ∈ U ∧ Δ * g (b c) ≤ e := fun c => by
    have h := mem_range_self (f := b) c
    rw [hrange] at h
    exact h
  let σ : P → U := fun c => ⟨((0 : ℝ), b c), (hmem c).1⟩
  have hσ : ContMDiff (𝓡∂ (d + 1)) (𝓘(ℝ, ℝ).prod J) ∞ σ :=
    (ContMDiff.subtypeVal_comp_iff U σ).mp (contMDiff_const.prodMk hb.contMDiff)
  refine nonempty_diffeomorph_regularSublevel_of_lift hdim hΨ hB hreg hregb hb
    (π := fun x : U => (x : ℝ × Z).2) (contMDiff_snd.comp contMDiff_subtype_val) hσ
    (fun c => ⟨rfl, sub_nonneg.mpr (hmem c).2⟩) (fun c => rfl) ?_
  intro x hx1 hx2
  have hx1' : (x : ℝ × Z).1 = 0 := hx1
  have hx2' : Δ * g (x : ℝ × Z).2 ≤ e := sub_nonneg.mp hx2
  have hz : (x : ℝ × Z).2 ∈ range b := by
    rw [hrange]
    refine ⟨?_, hx2'⟩
    have hxe : (((0 : ℝ), (x : ℝ × Z).2) : ℝ × Z) = (x : ℝ × Z) := Prod.ext hx1'.symm rfl
    rw [hxe]
    exact x.2
  obtain ⟨c, hc⟩ := hz
  exact ⟨c, Subtype.ext (Prod.ext hx1'.symm hc)⟩

/-- LFR24's buffered model cylinder `(-6Δ, 6Δ) × B_Z(z₀, 9)`, open in `ℝ × Z`. -/
def edgeModelCylinder {Z : Type*} [PseudoMetricSpace Z] (z₀ : Z) (Δ : ℝ) :
    TopologicalSpace.Opens (ℝ × Z) :=
  ⟨{p | p.1 ∈ Ioo (-(6 * Δ)) (6 * Δ) ∧ dist p.2 z₀ < 9},
    (isOpen_Ioo.preimage continuous_fst).inter
      (isOpen_lt (continuous_snd.dist continuous_const) continuous_const)⟩

variable {Z : Type*} [MetricSpace Z] [ChartedSpace H' Z]

omit [FiniteDimensional ℝ F] in
variable (J) in
/-- The time coordinate of the model map is smooth on the cylinder. -/
theorem edgeModelCylinder_contMDiff_time (z₀ : Z) (Δ : ℝ) (h : Z → ℝ) :
    ContMDiff (𝓘(ℝ, ℝ).prod J) 𝓘(ℝ, ℝ) ∞
      (fun x : edgeModelCylinder z₀ Δ => (((x : ℝ × Z).1, Δ * h (x : ℝ × Z).2) : ℝ × ℝ).1) := by
  have hf : ContMDiff (𝓘(ℝ, ℝ).prod J) 𝓘(ℝ, ℝ) ∞
      (fun x : edgeModelCylinder z₀ Δ => (x : ℝ × Z).1) :=
    contMDiff_fst.comp contMDiff_subtype_val
  exact hf

omit [FiniteDimensional ℝ F] in
/-- LFR24's `h` is smooth at the surface point of every cylinder point. -/
theorem edgeModelCylinder_contMDiffAt_height {z₀ : Z} {h : Z → ℝ} {W : Set Z} (hW : IsOpen W)
    (hW9 : closedBall z₀ 9 ⊆ W) (hh : ContMDiffOn J 𝓘(ℝ, ℝ) ∞ h W) {Δ : ℝ}
    (x : edgeModelCylinder z₀ Δ) : ContMDiffAt J 𝓘(ℝ, ℝ) ∞ h (x : ℝ × Z).2 := by
  have hx : (x : ℝ × Z).2 ∈ W := hW9 (mem_closedBall.mpr x.2.2.le)
  exact (hh _ hx).contMDiffAt (hW.mem_nhds hx)

omit [FiniteDimensional ℝ F] in
/-- The sublevel function `e - Δ h` is smooth on the cylinder. -/
theorem edgeModelCylinder_contMDiff_height {z₀ : Z} {h : Z → ℝ} {W : Set Z} (hW : IsOpen W)
    (hW9 : closedBall z₀ 9 ⊆ W) (hh : ContMDiffOn J 𝓘(ℝ, ℝ) ∞ h W) (Δ e : ℝ) :
    ContMDiff (𝓘(ℝ, ℝ).prod J) 𝓘(ℝ, ℝ) ∞
      (fun x : edgeModelCylinder z₀ Δ =>
        e - (((x : ℝ × Z).1, Δ * h (x : ℝ × Z).2) : ℝ × ℝ).2) := by
  intro x
  have hhx := edgeModelCylinder_contMDiffAt_height hW hW9 hh x
  have hs : ContMDiffAt (𝓘(ℝ, ℝ).prod J) J ∞
      (fun y : edgeModelCylinder z₀ Δ => (y : ℝ × Z).2) x :=
    (contMDiff_snd.comp contMDiff_subtype_val).contMDiffAt
  have hl : ContDiff ℝ ∞ (fun s : ℝ => e - Δ * s) :=
    contDiff_const.sub (contDiff_const.mul contDiff_id)
  exact hl.contMDiff.contMDiffAt.comp x (hhx.comp x hs)

omit [FiniteDimensional ℝ F] in
variable (J) in
/-- Interior regularity of the model fibre: the time coordinate is a submersion. -/
theorem edgeModelCylinder_regular (z₀ : Z) (Δ e : ℝ) (h : Z → ℝ) :
    ∀ x : edgeModelCylinder z₀ Δ, (((x : ℝ × Z).1, Δ * h (x : ℝ × Z).2) : ℝ × ℝ).1 = 0 →
      0 ≤ e - (((x : ℝ × Z).1, Δ * h (x : ℝ × Z).2) : ℝ × ℝ).2 →
      Surjective (mfderiv (𝓘(ℝ, ℝ).prod J) 𝓘(ℝ, ℝ)
        (fun x : edgeModelCylinder z₀ Δ =>
          (((x : ℝ × Z).1, Δ * h (x : ℝ × Z).2) : ℝ × ℝ).1) x) := by
  intro x _ _
  have hd : HasMFDerivAt (𝓘(ℝ, ℝ).prod J) 𝓘(ℝ, ℝ)
      (fun y : edgeModelCylinder z₀ Δ => (y : ℝ × Z).1) x
      ((ContinuousLinearMap.fst ℝ ℝ F).comp (ContinuousLinearMap.id ℝ (ℝ × F))) :=
    (hasMFDerivAt_fst (x : ℝ × Z)).comp x (hasMFDerivAt_subtype_val _ x)
  change Surjective (mfderiv (𝓘(ℝ, ℝ).prod J) 𝓘(ℝ, ℝ)
    (fun y : edgeModelCylinder z₀ Δ => (y : ℝ × Z).1) x)
  rw [hd.mfderiv]
  intro y
  exact ⟨((y : ℝ), (0 : F)), rfl⟩

omit [FiniteDimensional ℝ F] in
/-- The model map `(t, Δ h)` is smooth on the cylinder. -/
theorem edgeModelCylinder_contMDiff_map {z₀ : Z} {h : Z → ℝ} {W : Set Z} (hW : IsOpen W)
    (hW9 : closedBall z₀ 9 ⊆ W) (hh : ContMDiffOn J 𝓘(ℝ, ℝ) ∞ h W) (Δ : ℝ) :
    ContMDiff (𝓘(ℝ, ℝ).prod J) 𝓘(ℝ, ℝ × ℝ) ∞
      (fun x : edgeModelCylinder z₀ Δ => (((x : ℝ × Z).1, Δ * h (x : ℝ × Z).2) : ℝ × ℝ)) := by
  intro x
  have hhx := edgeModelCylinder_contMDiffAt_height hW hW9 hh x
  have hs : ContMDiffAt (𝓘(ℝ, ℝ).prod J) J ∞
      (fun y : edgeModelCylinder z₀ Δ => (y : ℝ × Z).2) x :=
    (contMDiff_snd.comp contMDiff_subtype_val).contMDiffAt
  have ht : ContMDiffAt (𝓘(ℝ, ℝ).prod J) 𝓘(ℝ, ℝ) ∞
      (fun y : edgeModelCylinder z₀ Δ => (y : ℝ × Z).1) x :=
    (contMDiff_fst.comp contMDiff_subtype_val).contMDiffAt
  have hl : ContDiff ℝ ∞ (fun s : ℝ => Δ * s) := contDiff_const.mul contDiff_id
  exact ht.prodMk_space (hl.contMDiff.contMDiffAt.comp x (hhx.comp x hs))

omit [FiniteDimensional ℝ F] in
/-- Boundary regularity of the model fibre: `(t, 4Δ - Δ h)` is a submersion on `{t = 0, h = 4}`,
from LFR24's `dh ≠ 0` on `{r < 9, h = 4}`. -/
theorem edgeModelCylinder_regular_boundary {z₀ : Z} {h : Z → ℝ} {W : Set Z} (hW : IsOpen W)
    (hW9 : closedBall z₀ 9 ⊆ W) (hh : ContMDiffOn J 𝓘(ℝ, ℝ) ∞ h W)
    (h4 : ∀ x, dist x z₀ < 9 → h x = 4 → mvfderiv J h x ≠ 0) {Δ : ℝ} (hΔ : 0 < Δ) :
    ∀ x : edgeModelCylinder z₀ Δ, (((x : ℝ × Z).1, Δ * h (x : ℝ × Z).2) : ℝ × ℝ).1 = 0 →
      4 * Δ - (((x : ℝ × Z).1, Δ * h (x : ℝ × Z).2) : ℝ × ℝ).2 = 0 →
      Surjective (mfderiv (𝓘(ℝ, ℝ).prod J) 𝓘(ℝ, ℝ × ℝ)
        (fun y : edgeModelCylinder z₀ Δ => ((((y : ℝ × Z).1, Δ * h (y : ℝ × Z).2) : ℝ × ℝ).1,
          4 * Δ - (((y : ℝ × Z).1, Δ * h (y : ℝ × Z).2) : ℝ × ℝ).2)) x) := by
  intro x _ hx2
  have hx2' : 4 * Δ - Δ * h (x : ℝ × Z).2 = 0 := hx2
  have hx4 : h (x : ℝ × Z).2 = 4 := by
    have : Δ * (4 - h (x : ℝ × Z).2) = 0 := by linarith
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd h0 hΔ.ne'
    · linarith
  obtain ⟨w, hw⟩ : ∃ w, mvfderiv J h (x : ℝ × Z).2 w ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact h4 _ x.2.2 hx4 (ContinuousLinearMap.ext hcon)
  have hhx := (edgeModelCylinder_contMDiffAt_height hW hW9 hh x).mdifferentiableAt (by simp)
  have hs : HasMFDerivAt (𝓘(ℝ, ℝ).prod J) J
      (fun y : edgeModelCylinder z₀ Δ => (y : ℝ × Z).2) x
      ((ContinuousLinearMap.snd ℝ ℝ F).comp (ContinuousLinearMap.id ℝ (ℝ × F))) :=
    (hasMFDerivAt_snd (x : ℝ × Z)).comp x (hasMFDerivAt_subtype_val _ x)
  have hf : HasMFDerivAt (𝓘(ℝ, ℝ).prod J) 𝓘(ℝ, ℝ)
      (fun y : edgeModelCylinder z₀ Δ => (y : ℝ × Z).1) x
      ((ContinuousLinearMap.fst ℝ ℝ F).comp (ContinuousLinearMap.id ℝ (ℝ × F))) :=
    (hasMFDerivAt_fst (x : ℝ × Z)).comp x (hasMFDerivAt_subtype_val _ x)
  have hg := (hhx.hasMFDerivAt.comp x hs).const_smul Δ
  have hv : HasMFDerivAt (𝓘(ℝ, ℝ).prod J) 𝓘(ℝ, ℝ × ℝ)
      (fun y : edgeModelCylinder z₀ Δ => (((y : ℝ × Z).1, Δ * h (y : ℝ × Z).2) : ℝ × ℝ)) x
      (((ContinuousLinearMap.fst ℝ ℝ F).comp (ContinuousLinearMap.id ℝ (ℝ × F))).prod
        (Δ • (mfderiv J 𝓘(ℝ, ℝ) h (x : ℝ × Z).2).comp
          ((ContinuousLinearMap.snd ℝ ℝ F).comp (ContinuousLinearMap.id ℝ (ℝ × F))))) :=
    ⟨hf.1.prodMk hg.1, hf.2.prodMk hg.2⟩
  refine surjective_mfderiv_fst_sub_snd_of_apply (e := 4 * Δ) hv ((1 : ℝ), (0 : F))
    ((0 : ℝ), w) ?_
  change 1 * (Δ * mvfderiv J h (x : ℝ × Z).2 w) -
    0 * (Δ * mvfderiv J h (x : ℝ × Z).2 (0 : F)) ≠ 0
  rw [zero_mul, sub_zero, one_mul]
  exact mul_ne_zero hΔ.ne' hw

omit [ChartedSpace H' Z] in
/-- The closed unit `2`-cell is connected. -/
theorem closedCell_two_connectedSpace : ConnectedSpace (ClosedCell 2) := by
  have hset : {x : EuclideanSpace ℝ (Fin 2) | ‖x‖ ≤ 1} = closedBall 0 1 := by
    ext x
    simp
  have hc : IsConnected {x : EuclideanSpace ℝ (Fin 2) | ‖x‖ ≤ 1} := by
    rw [hset]
    exact (convex_closedBall 0 1).isConnected (nonempty_closedBall.mpr zero_le_one)
  exact isConnected_iff_connectedSpace.mp hc

omit [ChartedSpace H' Z] in
/-- The closed unit `2`-cell is compact. -/
theorem closedCell_two_compactSpace : CompactSpace (ClosedCell 2) := by
  have hset : {x : EuclideanSpace ℝ (Fin 2) | ‖x‖ ≤ 1} = closedBall 0 1 := by
    ext x
    simp
  have hc : IsCompact {x : EuclideanSpace ℝ (Fin 2) | ‖x‖ ≤ 1} := by
    rw [hset]
    exact isCompact_closedBall 0 1
  exact isCompact_iff_compactSpace.mp hc

attribute [local instance] Handle.closedCellChartedSpaceSucc Handle.closedCellIsManifold

/-- **LFR28 I6: the model fibre is a closed smooth disk.** With LFR24's clauses (`h` smooth on an
open `W ⊇ B̄(z₀, 9)`, `dh ≠ 0` on `{r < 9, h = 4}`, a smooth embedding `b` of `ClosedCell 2` onto
`{r < 9, h ≤ 4}`), the regular sublevel `{t = 0, Δ h ≤ 4Δ}` of the model map `(t, Δ h)` on the
cylinder `(-6Δ, 6Δ) × B_Z(z₀, 9)` is diffeomorphic to `ClosedCell 2`; it is compact and connected,
and its boundary points are exactly those with `h = 4`. -/
theorem edgeModelCylinder_fibre_closedCell [J.Boundaryless] [IsManifold J ∞ Z]
    (hF : Module.finrank ℝ (ℝ × F) = 1 + 1 + Module.finrank ℝ ℝ)
    {z₀ : Z} {h : Z → ℝ} {W : Set Z} (hW : IsOpen W) (hW9 : closedBall z₀ 9 ⊆ W)
    (hh : ContMDiffOn J 𝓘(ℝ, ℝ) ∞ h W) (h4 : ∀ x, dist x z₀ < 9 → h x = 4 → mvfderiv J h x ≠ 0)
    {b : ClosedCell 2 → Z} (hb : IsSmoothEmbedding (𝓡∂ 2) J ∞ b)
    (hrange : range b = {x | dist x z₀ < 9 ∧ h x ≤ 4}) {Δ : ℝ} (hΔ : 0 < Δ) :
    letI := regularSublevelChartedSpace hF (edgeModelCylinder_contMDiff_time J z₀ Δ h)
      (edgeModelCylinder_contMDiff_height hW hW9 hh Δ (4 * Δ))
      (edgeModelCylinder_regular J z₀ Δ (4 * Δ) h)
      (edgeModelCylinder_regular_boundary hW hW9 hh h4 hΔ)
    Nonempty (ClosedCell 2 ≃ₘ⟮𝓡∂ (1 + 1), 𝓡∂ (1 + 1)⟯ {x : edgeModelCylinder z₀ Δ //
        (((x : ℝ × Z).1, Δ * h (x : ℝ × Z).2) : ℝ × ℝ).1 = 0 ∧
        0 ≤ 4 * Δ - (((x : ℝ × Z).1, Δ * h (x : ℝ × Z).2) : ℝ × ℝ).2}) ∧
    CompactSpace {x : edgeModelCylinder z₀ Δ //
        (((x : ℝ × Z).1, Δ * h (x : ℝ × Z).2) : ℝ × ℝ).1 = 0 ∧
        0 ≤ 4 * Δ - (((x : ℝ × Z).1, Δ * h (x : ℝ × Z).2) : ℝ × ℝ).2} ∧
    ConnectedSpace {x : edgeModelCylinder z₀ Δ //
        (((x : ℝ × Z).1, Δ * h (x : ℝ × Z).2) : ℝ × ℝ).1 = 0 ∧
        0 ≤ 4 * Δ - (((x : ℝ × Z).1, Δ * h (x : ℝ × Z).2) : ℝ × ℝ).2} ∧
    ∀ y : {x : edgeModelCylinder z₀ Δ //
        (((x : ℝ × Z).1, Δ * h (x : ℝ × Z).2) : ℝ × ℝ).1 = 0 ∧
        0 ≤ 4 * Δ - (((x : ℝ × Z).1, Δ * h (x : ℝ × Z).2) : ℝ × ℝ).2},
      (𝓡∂ (1 + 1)).IsBoundaryPoint y ↔ h ((y : edgeModelCylinder z₀ Δ) : ℝ × Z).2 = 4 := by
  let _ := regularSublevelChartedSpace hF (edgeModelCylinder_contMDiff_time J z₀ Δ h)
    (edgeModelCylinder_contMDiff_height hW hW9 hh Δ (4 * Δ))
    (edgeModelCylinder_regular J z₀ Δ (4 * Δ) h)
    (edgeModelCylinder_regular_boundary hW hW9 hh h4 hΔ)
  have hrange' : range b = {z | ((0 : ℝ), z) ∈ edgeModelCylinder z₀ Δ ∧ Δ * h z ≤ 4 * Δ} := by
    rw [hrange]
    ext z
    constructor
    · rintro ⟨hz, h4z⟩
      exact ⟨⟨⟨by linarith, by linarith⟩, hz⟩, by nlinarith⟩
    · rintro ⟨⟨-, hz⟩, h4z⟩
      exact ⟨hz, le_of_mul_le_mul_left (by linarith) hΔ⟩
  obtain ⟨φ⟩ := nonempty_diffeomorph_cylinderFibre_of_embedding hF (edgeModelCylinder z₀ Δ)
    (edgeModelCylinder_contMDiff_time J z₀ Δ h)
    (edgeModelCylinder_contMDiff_height hW hW9 hh Δ (4 * Δ))
    (edgeModelCylinder_regular J z₀ Δ (4 * Δ) h)
    (edgeModelCylinder_regular_boundary hW hW9 hh h4 hΔ) hb hrange'
  have _ := closedCell_two_compactSpace
  have _ := closedCell_two_connectedSpace
  refine ⟨⟨φ⟩, φ.toHomeomorph.compactSpace,
    φ.toHomeomorph.surjective.connectedSpace φ.toHomeomorph.continuous, fun y => ?_⟩
  refine (regularSublevel_isBoundaryPoint_iff hF (edgeModelCylinder_contMDiff_time J z₀ Δ h)
    (edgeModelCylinder_contMDiff_height hW hW9 hh Δ (4 * Δ))
    (edgeModelCylinder_regular J z₀ Δ (4 * Δ) h)
    (edgeModelCylinder_regular_boundary hW hW9 hh h4 hΔ)).trans ?_
  change 4 * Δ - Δ * h ((y : edgeModelCylinder z₀ Δ) : ℝ × Z).2 = 0 ↔
    h ((y : edgeModelCylinder z₀ Δ) : ℝ × Z).2 = 4
  constructor
  · intro h0
    have : Δ * (4 - h ((y : edgeModelCylinder z₀ Δ) : ℝ × Z).2) = 0 := by linarith
    rcases mul_eq_zero.mp this with h1 | h1
    · exact absurd h1 hΔ.ne'
    · linarith
  · intro h0
    rw [h0]
    ring

end Cylinder

section DiskBundle

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'} [J.Boundaryless]
  {Z : Type} [MetricSpace Z] [ChartedSpace H' Z] [IsManifold J ∞ Z] [LocallyCompactSpace Z]
  [SecondCountableTopology Z]
  {Y : Type} [TopologicalSpace Y] [ChartedSpace (ModelProd ℝ H') Y]
  [IsManifold (𝓘(ℝ, ℝ).prod J) ∞ Y] [T2Space Y] [SigmaCompactSpace Y]

attribute [local instance] Handle.closedCellChartedSpaceSucc Handle.closedCellIsManifold

/-- **LFR28.1 with the closed-disk fibre (abstract).** Model: LFR24's cylinder `(-6Δ, 6Δ) × B_Z(z₀, 9)`
with `u₀ = (t, Δ h)` and LFR24's clauses for `h` and the disk embedding `b`; source `u = (f, H)` on
`Y`, an actual `C^r` model-to-source map `j` (`3 ≤ r`) and the hypotheses of F7-LFR28B's
`edgeInterp_disk_bundle` with `e = 4Δ`. Then the source fibre `{f = 0, H ≤ 4Δ}` is diffeomorphic to
`ClosedCell 2`, compact and connected; `f` restricted to `{a₀ < f < b₀, H ≤ 4Δ}` is trivial with that
fibre; and its boundary points are exactly those with `H = 4Δ`. -/
theorem edgeModelCylinder_disk_bundle
    (hF : Module.finrank ℝ (ℝ × F) = 1 + 1 + Module.finrank ℝ ℝ)
    {z₀ : Z} {h : Z → ℝ} {W : Set Z} (hW : IsOpen W) (hW9 : closedBall z₀ 9 ⊆ W)
    (hh : ContMDiffOn J 𝓘(ℝ, ℝ) ∞ h W) (h4 : ∀ x, dist x z₀ < 9 → h x = 4 → mvfderiv J h x ≠ 0)
    {b : ClosedCell 2 → Z} (hb : IsSmoothEmbedding (𝓡∂ 2) J ∞ b)
    (hrange : range b = {x | dist x z₀ < 9 ∧ h x ≤ 4}) {Δ : ℝ} (hΔ : 0 < Δ)
    {r : ℕ} (hr : 3 ≤ r)
    (j : PartialDiffeomorph (𝓘(ℝ, ℝ).prod J) (𝓘(ℝ, ℝ).prod J) (edgeModelCylinder z₀ Δ) Y r)
    (hj : j.source = univ)
    {u : Y → ℝ × ℝ} (hu : ContMDiff (𝓘(ℝ, ℝ).prod J) 𝓘(ℝ, ℝ × ℝ) ∞ u) {β δ : ℝ}
    (hval : ∀ x : edgeModelCylinder z₀ Δ,
      |(u (j x)).1 - (((x : ℝ × Z).1, Δ * h (x : ℝ × Z).2) : ℝ × ℝ).1| ≤ δ ∧
      |(u (j x)).2 - (((x : ℝ × Z).1, Δ * h (x : ℝ × Z).2) : ℝ × ℝ).2| ≤ δ)
    (hrow : ∀ x : edgeModelCylinder z₀ Δ,
      |(((x : ℝ × Z).1, Δ * h (x : ℝ × Z).2) : ℝ × ℝ).1| ≤ β + δ →
      (((x : ℝ × Z).1, Δ * h (x : ℝ × Z).2) : ℝ × ℝ).2 ≤ 4 * Δ + δ →
      ∃ X : TangentSpace (𝓘(ℝ, ℝ).prod J) x,
        (mfderiv (𝓘(ℝ, ℝ).prod J) 𝓘(ℝ, ℝ × ℝ)
          (fun y : edgeModelCylinder z₀ Δ => (((y : ℝ × Z).1, Δ * h (y : ℝ × Z).2) : ℝ × ℝ))
          x X).1 = 1 ∧
        |(mfderiv (𝓘(ℝ, ℝ).prod J) 𝓘(ℝ, ℝ × ℝ) (fun z => u (j z)) x X).1 - 1| ≤ 1 / 1000)
    (hpair : ∀ x : edgeModelCylinder z₀ Δ,
      |(((x : ℝ × Z).1, Δ * h (x : ℝ × Z).2) : ℝ × ℝ).1| ≤ β + δ →
      |(((x : ℝ × Z).1, Δ * h (x : ℝ × Z).2) : ℝ × ℝ).2 - 4 * Δ| ≤ δ →
      ∃ X₁ X₂ : TangentSpace (𝓘(ℝ, ℝ).prod J) x,
        (mfderiv (𝓘(ℝ, ℝ).prod J) 𝓘(ℝ, ℝ × ℝ)
          (fun y : edgeModelCylinder z₀ Δ => (((y : ℝ × Z).1, Δ * h (y : ℝ × Z).2) : ℝ × ℝ))
          x X₁).1 = 1 ∧
        (mfderiv (𝓘(ℝ, ℝ).prod J) 𝓘(ℝ, ℝ × ℝ)
          (fun y : edgeModelCylinder z₀ Δ => (((y : ℝ × Z).1, Δ * h (y : ℝ × Z).2) : ℝ × ℝ))
          x X₂).1 = 0 ∧
        (mfderiv (𝓘(ℝ, ℝ).prod J) 𝓘(ℝ, ℝ × ℝ)
          (fun y : edgeModelCylinder z₀ Δ => (((y : ℝ × Z).1, Δ * h (y : ℝ × Z).2) : ℝ × ℝ))
          x X₁).2 = 0 ∧
        1 / 2 ≤ (mfderiv (𝓘(ℝ, ℝ).prod J) 𝓘(ℝ, ℝ × ℝ)
          (fun y : edgeModelCylinder z₀ Δ => (((y : ℝ × Z).1, Δ * h (y : ℝ × Z).2) : ℝ × ℝ))
          x X₂).2 ∧
        |(mfderiv (𝓘(ℝ, ℝ).prod J) 𝓘(ℝ, ℝ × ℝ) (fun z => u (j z)) x X₁).1 - 1| ≤ 1 / 1000 ∧
        |(mfderiv (𝓘(ℝ, ℝ).prod J) 𝓘(ℝ, ℝ × ℝ) (fun z => u (j z)) x X₂).1| ≤ 1 / 1000 ∧
        |(mfderiv (𝓘(ℝ, ℝ).prod J) 𝓘(ℝ, ℝ × ℝ) (fun z => u (j z)) x X₁).2| ≤ 1 / 1000 ∧
        |(mfderiv (𝓘(ℝ, ℝ).prod J) 𝓘(ℝ, ℝ × ℝ) (fun z => u (j z)) x X₂).2 -
          (mfderiv (𝓘(ℝ, ℝ).prod J) 𝓘(ℝ, ℝ × ℝ)
            (fun y : edgeModelCylinder z₀ Δ => (((y : ℝ × Z).1, Δ * h (y : ℝ × Z).2) : ℝ × ℝ))
            x X₂).2| ≤ 1 / 1000)
    {Q : Set (edgeModelCylinder z₀ Δ)} (hQ : IsCompact Q)
    (hQw : ∀ x : edgeModelCylinder z₀ Δ,
      |(((x : ℝ × Z).1, Δ * h (x : ℝ × Z).2) : ℝ × ℝ).1| ≤ δ →
      (((x : ℝ × Z).1, Δ * h (x : ℝ × Z).2) : ℝ × ℝ).2 ≤ 4 * Δ + δ → x ∈ Q)
    (henc : ∀ y, |(u y).1| < β → (u y).2 ≤ 4 * Δ → y ∈ j.target)
    (hprop : ∀ K : Set ℝ, IsCompact K → K ⊆ Ioo (-β) β →
      IsCompact ((fun y => (u y).1) ⁻¹' K ∩ {y | 0 ≤ 4 * Δ - (u y).2}))
    {a₀ b₀ : ℝ} (ha₀ : -β < a₀) (h0 : (0 : ℝ) ∈ Ioo a₀ b₀) (hb₀ : b₀ < β) :
    letI := regularSublevelChartedSpace (Ψ := fun y : Y => (u y).1)
      (B := fun y => 4 * Δ - (u y).2) hF (contDiff_fst.contMDiff.comp hu)
      ((contDiff_const.sub contDiff_snd).contMDiff.comp hu)
      (fun y hy hB => edgeInterp_source_regular (by omega) j hj hu hval hrow henc y
        (by rw [hy]; exact ⟨by linarith [h0.1, h0.2], by linarith [h0.1, h0.2]⟩) hB)
      (fun y hy hB => edgeInterp_source_regular_boundary (by omega) j hj hu hval hpair henc y
        (by rw [hy]; exact ⟨by linarith [h0.1, h0.2], by linarith [h0.1, h0.2]⟩) hB)
    let Q₀ : TopologicalSpace.Opens ℝ := ⟨Ioo a₀ b₀, isOpen_Ioo⟩
    Nonempty (ClosedCell 2 ≃ₘ⟮𝓡∂ (1 + 1), 𝓡∂ (1 + 1)⟯
      {y : Y // (u y).1 = 0 ∧ 0 ≤ 4 * Δ - (u y).2}) ∧
    CompactSpace {y : Y // (u y).1 = 0 ∧ 0 ≤ 4 * Δ - (u y).2} ∧
    ConnectedSpace {y : Y // (u y).1 = 0 ∧ 0 ≤ 4 * Δ - (u y).2} ∧
    (∃ Θ : {y : Y // (u y).1 = 0 ∧ 0 ≤ 4 * Δ - (u y).2} × Q₀ → Y,
      ContMDiff ((𝓡∂ (1 + 1)).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod J) ∞ Θ ∧
      (∀ p, (u (Θ p)).1 = p.2 ∧ 0 ≤ 4 * Δ - (u (Θ p)).2) ∧
      (∀ x, Θ (x, ⟨0, h0⟩) = x) ∧ Injective Θ ∧
      ∃ O : Set Y, IsOpen O ∧ (∀ y, (u y).1 ∈ Ioo a₀ b₀ → 0 ≤ 4 * Δ - (u y).2 → y ∈ O) ∧
        ∃ R : Y → Y, ContMDiffOn (𝓘(ℝ, ℝ).prod J) (𝓘(ℝ, ℝ).prod J) ∞ R O ∧
          ∀ y (hy : (u y).1 ∈ Ioo a₀ b₀), 0 ≤ 4 * Δ - (u y).2 →
            ∃ hR : (u (R y)).1 = 0 ∧ 0 ≤ 4 * Δ - (u (R y)).2,
              Θ (⟨R y, hR⟩, ⟨(u y).1, hy⟩) = y) ∧
    ∀ y : {y : Y // (u y).1 = 0 ∧ 0 ≤ 4 * Δ - (u y).2},
      (𝓡∂ (1 + 1)).IsBoundaryPoint y ↔ (u y).2 = 4 * Δ := by
  have _ : LocallyCompactSpace (edgeModelCylinder z₀ Δ) :=
    (edgeModelCylinder z₀ Δ).isOpen.locallyCompactSpace
  let _ := regularSublevelChartedSpace hF (edgeModelCylinder_contMDiff_time J z₀ Δ h)
    (edgeModelCylinder_contMDiff_height hW hW9 hh Δ (4 * Δ))
    (edgeModelCylinder_regular J z₀ Δ (4 * Δ) h)
    (edgeModelCylinder_regular_boundary hW hW9 hh h4 hΔ)
  let _ := regularSublevelChartedSpace (Ψ := fun y : Y => (u y).1)
    (B := fun y => 4 * Δ - (u y).2) hF (contDiff_fst.contMDiff.comp hu)
    ((contDiff_const.sub contDiff_snd).contMDiff.comp hu)
    (fun y hy hB => edgeInterp_source_regular (by omega) j hj hu hval hrow henc y
      (by rw [hy]; exact ⟨by linarith [h0.1, h0.2], by linarith [h0.1, h0.2]⟩) hB)
    (fun y hy hB => edgeInterp_source_regular_boundary (by omega) j hj hu hval hpair henc y
      (by rw [hy]; exact ⟨by linarith [h0.1, h0.2], by linarith [h0.1, h0.2]⟩) hB)
  obtain ⟨⟨e₀⟩, hΘ, hbd⟩ := edgeInterp_disk_bundle hr hF j hj
    (edgeModelCylinder_contMDiff_map hW hW9 hh Δ) hu hval hrow hpair hQ hQw henc hprop ha₀ h0 hb₀
  obtain ⟨⟨e₁⟩, -, -, -⟩ := edgeModelCylinder_fibre_closedCell hF hW hW9 hh h4 hb hrange hΔ
  let φ := e₁.trans e₀
  have _ := closedCell_two_compactSpace
  have _ := closedCell_two_connectedSpace
  exact ⟨⟨φ⟩, φ.toHomeomorph.compactSpace,
    φ.toHomeomorph.surjective.connectedSpace φ.toHomeomorph.continuous, hΘ, hbd⟩

end DiskBundle

section LFR24

open Bundle
open scoped ENNReal

local notation "E2" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] Handle.closedCellChartedSpaceSucc Handle.closedCellIsManifold

/-- The dimension count of the model cylinder `ℝ × Z` over a surface modelled on `E2`. -/
theorem finrank_real_prod_euclideanTwo :
    Module.finrank ℝ (ℝ × E2) = 1 + 1 + Module.finrank ℝ ℝ := by
  simp

variable {Z : Type*} [MetricSpace Z] [ChartedSpace E2 Z] [IsManifold (𝓡 2) ∞ Z]
  [RiemannianBundle (fun x : Z => TangentSpace (𝓡 2) x)] [IsRiemannianManifold (𝓡 2) Z]
  [CompleteSpace Z] [ConnectedSpace Z]

/-- **LFR24 + I6: LFR24's model fibre is a closed smooth disk**, in the row's quantifier order. On
the LFR23 surface (orientation `o`, `C^{r+1}` metric `k`, `r ≥ 3`, `K ≥ 0`) with an endpoint model of
error `δ ≤ δ₀`, LFR24's function `h` (smooth near `B̄(z₀, 9)`, `|h - r| < μ` and the gradient clause on
the collar, `dh ≠ 0` on `{r < 9, h = 4}`) has, for every `Δ > 0`, model fibre
`{t = 0, Δ h ≤ 4Δ}` in the cylinder `(-6Δ, 6Δ) × B_Z(z₀, 9)` diffeomorphic to `ClosedCell 2`,
compact, connected, with boundary exactly `h = 4`. -/
theorem finiteSurface_edge_model_fibre_closedCell (o : ManifoldOrientation (𝓡 2) Z 2) {r : ℕ∞}
    (k : ContMDiffRiemannianMetric (𝓡 2) ((r : ℕ∞ω) + 1) E2 (TangentSpace (𝓡 2) : Z → Type _))
    (hr : 3 ≤ r)
    (hnorm : ∀ (x : Z) (w : TangentSpace (𝓡 2) x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (k.inner x w w)))
    (hK : ∀ x (v w : TangentSpace (𝓡 2) x), 0 ≤ k.sectionalCurvature x v w)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1 / 100) :
    ∃ δ₀ > 0, ∀ (z₀ : Z) (q : Z → ℝ) (δ : ℝ), 0 < δ → δ ≤ δ₀ → q z₀ = 0 →
      (∀ y ∈ closedBall z₀ 10, 0 ≤ q y) →
      (∀ y ∈ closedBall z₀ 10, ∀ y' ∈ closedBall z₀ 10, |dist (q y) (q y') - dist y y'| ≤ δ) →
      (∀ t ∈ Icc (0 : ℝ) 10, ∃ y ∈ closedBall z₀ 10, |q y - t| ≤ δ) →
      ∀ μ : ℝ, 0 < μ → μ < 1 / 100 →
      ∃ (h : Z → ℝ) (W : Set Z) (hW : IsOpen W) (hW9 : closedBall z₀ 9 ⊆ W)
        (hh : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ h W)
        (h4 : ∀ x, dist x z₀ < 9 → h x = 4 → mvfderiv (𝓡 2) h x ≠ 0),
        (∀ x, 21 / 10 ≤ dist x z₀ → dist x z₀ ≤ 9 → |h x - dist x z₀| < μ ∧
          ∀ v ∈ k.finiteMinimizingDirectionsTo ({z₀} : Set Z) x, ∀ w : TangentSpace (𝓡 2) x,
            |mvfderiv (𝓡 2) h x w + k.inner x v w| ≤ ε / 25 * Real.sqrt (k.inner x w w)) ∧
        ∀ (Δ : ℝ) (hΔ : 0 < Δ),
          letI := regularSublevelChartedSpace finrank_real_prod_euclideanTwo
            (edgeModelCylinder_contMDiff_time (𝓡 2) z₀ Δ h)
            (edgeModelCylinder_contMDiff_height hW hW9 hh Δ (4 * Δ))
            (edgeModelCylinder_regular (𝓡 2) z₀ Δ (4 * Δ) h)
            (edgeModelCylinder_regular_boundary hW hW9 hh h4 hΔ)
          Nonempty (ClosedCell 2 ≃ₘ⟮𝓡∂ (1 + 1), 𝓡∂ (1 + 1)⟯ {x : edgeModelCylinder z₀ Δ //
              (((x : ℝ × Z).1, Δ * h (x : ℝ × Z).2) : ℝ × ℝ).1 = 0 ∧
              0 ≤ 4 * Δ - (((x : ℝ × Z).1, Δ * h (x : ℝ × Z).2) : ℝ × ℝ).2}) ∧
          CompactSpace {x : edgeModelCylinder z₀ Δ //
              (((x : ℝ × Z).1, Δ * h (x : ℝ × Z).2) : ℝ × ℝ).1 = 0 ∧
              0 ≤ 4 * Δ - (((x : ℝ × Z).1, Δ * h (x : ℝ × Z).2) : ℝ × ℝ).2} ∧
          ConnectedSpace {x : edgeModelCylinder z₀ Δ //
              (((x : ℝ × Z).1, Δ * h (x : ℝ × Z).2) : ℝ × ℝ).1 = 0 ∧
              0 ≤ 4 * Δ - (((x : ℝ × Z).1, Δ * h (x : ℝ × Z).2) : ℝ × ℝ).2} ∧
          ∀ y : {x : edgeModelCylinder z₀ Δ //
              (((x : ℝ × Z).1, Δ * h (x : ℝ × Z).2) : ℝ × ℝ).1 = 0 ∧
              0 ≤ 4 * Δ - (((x : ℝ × Z).1, Δ * h (x : ℝ × Z).2) : ℝ × ℝ).2},
            (𝓡∂ (1 + 1)).IsBoundaryPoint y ↔
              h ((y : edgeModelCylinder z₀ Δ) : ℝ × Z).2 = 4 := by
  obtain ⟨δ₀, hδ₀, hrow⟩ := finiteSurface_edge_model_core o k hr hnorm hK hε hε1
  refine ⟨δ₀, hδ₀, fun z₀ q δ hδ hδ0 hq0 hqnn hdist hdense μ hμ hμ1 => ?_⟩
  obtain ⟨h, ⟨W, hW, hW9, hh⟩, -, -, hcollar, hdisks, -, h4, -⟩ :=
    hrow z₀ q δ hδ hδ0 hq0 hqnn hdist hdense μ hμ hμ1
  obtain ⟨-, -, -, b, hb, hrange, -⟩ := hdisks 4 ⟨by norm_num, by norm_num⟩
  exact ⟨h, W, hW, hW9, hh, h4, hcollar, fun Δ hΔ =>
    edgeModelCylinder_fibre_closedCell finrank_real_prod_euclideanTwo hW hW9 hh h4 hb hrange hΔ⟩

end LFR24

end DifferentialGeometry.Geometry.Collapse
