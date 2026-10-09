import DifferentialGeometry.Geometry.Comparison.FiniteSoul.InducedMetricGauss
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.InducedMetricPullback
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.FiniteParallelSlice
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Chart
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Basic

/-!
# EXIT-51: the induced metric of a totally geodesic soul and its curvature (CMS3-CARRIER, G3)

Frozen interface `exists_inducedMetric_sectional_eq` (D-CMS3 §13, review §14: correct; the immersion
pullback metric and the finite Gauss identity are real proof leaves, disposition D10). On the smooth
carrier `B` of a totally geodesic `C^r` soul (`r ≥ 4`, base contract with left inverse `R`), the
induced metric `b^* g` has order `r − 2` and its sectional curvature is the sectional curvature of the
ORIGINAL ambient metric `g` on the image planes (so `K ≥ 0` for LFR51). LFR47 is not re-applied.

Route at `s₀` (slice chart `c` onto `A` at `b s₀`, `D = A.direction`, `J : D ↪ E`):
* the chart coefficients of `b^* g` at `s₀` are the pullback of the restricted slice coefficients
  `C_A z = C (a₀ + J z)|_{J D}` along `Φ₀ = proj_D ∘ (c ∘ b ∘ ψ⁻¹ − a₀)`, whose derivative is
  invertible (injective because `dR ∘ db = id`; onto because `Φ₀ ∘ (ψ ∘ R ∘ c⁻¹ ∘ (a₀ + J ·)) = id`
  near the base point, `finrank_eq_of_local_rightInverse`);
* `CrossSpaceTransition.coefficientSectional_transition_cross` (F7-LFR11b) moves the curvature to
  `C_A`;
* total geodesy gives `Γ_C (J D, J D) ⊆ J D` along `A` (`projection_sliceChristoffelFinite_eq_zero`,
  CMS3-PT), and the finite Gauss identity `coefficientSectional_affineSliceCoeff` moves it to `C`,
  which is `g` read in the slice chart (`sectionalCurvature_eq_coefficientSectional`).

Deviation (linter-forced): the frozen `[NeZero (finrank ℝ E)]`, `[CompactSpace B]`, `[T2Space B]` and
`hbinj` are not used (injectivity follows from `R`); the verbatim statement is an `example` in
`InducedMetricApplications.lean`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter Function Metric
open scoped Manifold ContDiff Topology InnerProductSpace

namespace DifferentialGeometry.Geometry.FiniteSoul

open DifferentialGeometry.Analysis (affineSliceCoeff affineSliceCoeff_apply
  coefficientSectional_affineSliceCoeff coefficientSectional_transition_cross)

/-- **Dimension from a local right inverse.** If `Φ₀ ∘ Ψ = id` near `z₀`, `Ψ z₀ = u₀`, both are
differentiable there and `dΦ₀ (u₀)` is injective, the two model spaces have the same dimension. -/
theorem finrank_eq_of_local_rightInverse {V P : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    {Φ₀ : V → P} {Ψ : P → V} {u₀ : V} {z₀ : P} (hΨ : Ψ z₀ = u₀)
    (hcomp : ∀ᶠ z in 𝓝 z₀, Φ₀ (Ψ z) = z) (hΦd : DifferentiableAt ℝ Φ₀ u₀)
    (hΨd : DifferentiableAt ℝ Ψ z₀) (hinj : Injective (fderiv ℝ Φ₀ u₀)) :
    Module.finrank ℝ V = Module.finrank ℝ P := by
  have hΦd' : DifferentiableAt ℝ Φ₀ (Ψ z₀) := hΨ ▸ hΦd
  have hc : fderiv ℝ (Φ₀ ∘ Ψ) z₀ = (fderiv ℝ Φ₀ (Ψ z₀)).comp (fderiv ℝ Ψ z₀) :=
    fderiv_comp z₀ hΦd' hΨd
  have hid : fderiv ℝ (Φ₀ ∘ Ψ) z₀ = ContinuousLinearMap.id ℝ P := by
    have hev : (Φ₀ ∘ Ψ) =ᶠ[𝓝 z₀] id := hcomp
    rw [hev.fderiv_eq, fderiv_id]
  rw [hΨ] at hc
  have hsurj : Surjective (fderiv ℝ Φ₀ u₀) := fun z =>
    ⟨fderiv ℝ Ψ z₀ z, by
      have h := congrArg (fun L : P →L[ℝ] P => L z) (hc.symm.trans hid)
      simpa using h⟩
  exact (LinearEquiv.ofBijective (fderiv ℝ Φ₀ u₀ : V →ₗ[ℝ] P) ⟨hinj, hsurj⟩).finrank_eq

section Pointwise

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [FiniteDimensional ℝ EB]
  {B : Type*} [TopologicalSpace B] [ChartedSpace EB B] [IsManifold 𝓘(ℝ, EB) ∞ B]

variable {r : ℕ∞}

omit [FiniteDimensional ℝ E] [I.Boundaryless] [FiniteDimensional ℝ EB] [IsManifold I ∞ M]
  [IsManifold 𝓘(ℝ, EB) ∞ B] in
/-- `dR ∘ db = id` makes `db` injective. -/
theorem injective_mfderiv_of_leftInverse_soulCarrier {n : ℕ∞ω} (hn : n ≠ 0) {b : B → M} {R : M → B}
    (hRb : ∀ s, R (b s) = s) {s : B} (hbs : ContMDiffAt 𝓘(ℝ, EB) I n b s)
    (hRs : ContMDiffAt I 𝓘(ℝ, EB) n R (b s)) : Injective (mfderiv 𝓘(ℝ, EB) I b s) := by
  have hcomp := mfderiv_comp s (hRs.mdifferentiableAt hn) (hbs.mdifferentiableAt hn)
  have hid : mfderiv 𝓘(ℝ, EB) 𝓘(ℝ, EB) (R ∘ b) s = ContinuousLinearMap.id ℝ _ := by
    rw [show R ∘ b = id from funext hRb, mfderiv_id]
  have key : ∀ u, mfderiv I 𝓘(ℝ, EB) R (b s) (mfderiv 𝓘(ℝ, EB) I b s u) = u := fun u => by
    have h := congrArg (fun L : TangentSpace 𝓘(ℝ, EB) s →L[ℝ] TangentSpace 𝓘(ℝ, EB) ((R ∘ b) s) =>
      L u) hcomp
    rw [hid] at h
    exact h.symm
  intro v w hvw
  rw [← key v, ← key w, hvw]


omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [FiniteDimensional ℝ EB]
  [IsManifold 𝓘(ℝ, EB) ∞ B] in
/-- Order bookkeeping for `4 ≤ r`. -/
theorem soulCarrier_orders_of_four_le {k : ℕ∞} (hk : 4 ≤ k) :
    (3 : ℕ∞ω) ≤ ((k - 1 : ℕ∞) : ℕ∞ω) ∧ (2 : ℕ∞ω) ≤ ((k - 2 : ℕ∞) : ℕ∞ω) ∧
      ((k - 2 : ℕ∞) : ℕ∞ω) + 1 ≤ ((k - 1 : ℕ∞) : ℕ∞ω) ∧
      ((k - 2 : ℕ∞) : ℕ∞ω) ≤ (k : ℕ∞ω) + 1 ∧ ((k - 1 : ℕ∞) : ℕ∞ω) ≤ (k : ℕ∞ω) ∧
      (3 : ℕ∞ω) ≤ (k : ℕ∞ω) := by
  have a1 : (3 : ℕ∞) ≤ k - 1 := by
    induction k using ENat.recTopCoe with
    | top => simp
    | coe n =>
      have hn : 4 ≤ n := by exact_mod_cast hk
      rw [← ENat.natCast_one, ← ENat.natCast_sub]
      exact_mod_cast (by omega : 3 ≤ n - 1)
  have a2 : (2 : ℕ∞) ≤ k - 2 := by
    induction k using ENat.recTopCoe with
    | top => simp
    | coe n =>
      have hn : 4 ≤ n := by exact_mod_cast hk
      rw [show (2 : ℕ∞) = ((2 : ℕ) : ℕ∞) from rfl, ← ENat.natCast_sub]
      exact_mod_cast (by omega : 2 ≤ n - 2)
  have a3 : (k - 2) + 1 ≤ k - 1 := by
    induction k using ENat.recTopCoe with
    | top => simp
    | coe n =>
      have hn : 4 ≤ n := by exact_mod_cast hk
      rw [← ENat.natCast_one, show (2 : ℕ∞) = ((2 : ℕ) : ℕ∞) from rfl, ← ENat.natCast_sub,
        ← ENat.natCast_sub]
      exact_mod_cast (by omega : n - 2 + 1 ≤ n - 1)
  have a4 : k - 2 ≤ k + 1 := tsub_le_self.trans le_self_add
  have a5 : k - 1 ≤ k := tsub_le_self
  have a6 : (3 : ℕ∞) ≤ k := le_trans (by norm_num) hk
  refine ⟨WithTop.coe_le_coe.mpr a1, WithTop.coe_le_coe.mpr a2, by exact_mod_cast a3,
    by exact_mod_cast a4, by exact_mod_cast a5, WithTop.coe_le_coe.mpr a6⟩

/-- **EXIT-51, pointwise curvature identity.** For any metric `gS` on the carrier with
`gS = b^* g`, the sectional curvature of `gS` at `s₀` is the sectional curvature of `g` on the image
plane. -/
theorem sectionalCurvature_eq_of_totallyGeodesic_carrier [T2Space M]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 4 ≤ r) (hD : g.geodesicFlowDomain = univ)
    {S : Set M} {d : ℕ} (hS : IsEmbeddedSliceOfOrder I (r : ℕ∞ω) d S)
    (htg : IsTotallyGeodesicFinite g S)
    {b : B → M} (hb : ContMDiff 𝓘(ℝ, EB) I ((r - 1 : ℕ∞) : ℕ∞ω) b) (hbS : range b = S)
    {R : M → B} (hRb : ∀ s, R (b s) = s)
    (hR : ∀ x ∈ S, ContMDiffAt I 𝓘(ℝ, EB) ((r - 1 : ℕ∞) : ℕ∞ω) R x)
    {m : ℕ∞ω} (hm : 2 ≤ m)
    (gS : ContMDiffRiemannianMetric 𝓘(ℝ, EB) m EB (TangentSpace 𝓘(ℝ, EB) : B → Type _))
    (hinner : ∀ (s : B) (v w : TangentSpace 𝓘(ℝ, EB) s),
      gS.inner s v w = g.inner (b s) (mfderiv 𝓘(ℝ, EB) I b s v) (mfderiv 𝓘(ℝ, EB) I b s w))
    (s₀ : B) (v w : TangentSpace 𝓘(ℝ, EB) s₀) :
    gS.sectionalCurvature s₀ v w =
      g.sectionalCurvature (b s₀) (mfderiv 𝓘(ℝ, EB) I b s₀ v) (mfderiv 𝓘(ℝ, EB) I b s₀ w) := by
  classical
  obtain ⟨h3n1, -, -, -, hn1r, h3r⟩ := soulCarrier_orders_of_four_le hr
  have hr1 : 1 ≤ r := le_trans (by norm_num) hr
  have hk0 : (r : ℕ∞ω) ≠ 0 := (lt_of_lt_of_le (by norm_num) h3r).ne'
  have hn10 : ((r - 1 : ℕ∞) : ℕ∞ω) ≠ 0 := (lt_of_lt_of_le (by norm_num) h3n1).ne'
  have h30 : (3 : ℕ∞ω) ≠ 0 := by norm_num
  have hbS' : ∀ s, b s ∈ S := fun s => hbS ▸ mem_range_self s
  set x₀ : M := b s₀ with hx₀
  obtain ⟨c, A, hA, hx₀c, -, himage⟩ := hS x₀ (hbS' s₀)
  have hAfd : FiniteDimensional ℝ A.direction := hA
  set D : Submodule ℝ E := A.direction with hDdef
  set J : D →L[ℝ] E := D.subtypeL with hJdef
  have hJinj : Injective J := Subtype.val_injective
  set a₀ : E := c x₀ with ha₀
  have ha₀A : a₀ ∈ A := (himage.apply_mem_iff hx₀c).2 (hbS' s₀)
  have hJA : ∀ z : D, a₀ + J z ∈ A := fun z => by
    have h := AffineSubspace.vadd_mem_of_mem_direction z.2 ha₀A
    rwa [vadd_eq_add, add_comm] at h
  set C := sliceCoeffFinite g c with hCdef
  have hC2 : ContDiffOn ℝ 2 C c.target :=
    contDiffOn_sliceCoeffFinite g (le_trans (by norm_num) (le_self_add.trans' h3r))
      (le_trans (by norm_num) h3r) c
  have hCsymm : ∀ y ∈ c.target, ∀ u v : E, C y u v = C y v u := fun y _ u v =>
    sliceCoeffFinite_symm g c y u v
  have hCco : ∀ y ∈ c.target, IsCoercive (C y) := fun y hy => isCoercive_sliceCoeffFinite hk0 g hy
  set W : Set D := (fun z : D => a₀ + J z) ⁻¹' c.target with hWdef
  have hWo : IsOpen W := c.open_target.preimage (continuous_const.add J.continuous)
  have hWU : MapsTo (fun z : D => a₀ + J z) W c.target := fun z hz => hz
  -- vanishing second fundamental form along the slice
  have htg' : ∀ z ∈ W, ∀ X u : D, ∃ Z : D,
      MetricKoszul.raisedKoszulOp (C (a₀ + J z)) (fderiv ℝ C (a₀ + J z)) (J X) (J u) = J Z := by
    intro z hz X u
    have hy : c.symm (a₀ + J z) ∈ c.source := c.toPartialEquiv.map_target hz
    have hyS : c.symm (a₀ + J z) ∈ S := (himage.symm_apply_mem_iff hz).2 (hJA z)
    have hcy : c (c.symm (a₀ + J z)) = a₀ + J z := c.toPartialEquiv.right_inv hz
    have h0 := projection_sliceChristoffelFinite_eq_zero hr1 g (le_trans (by norm_num) h3r) hD htg
      hA himage hyS hy (Dᗮ).starProjection
      (fun w hw => Submodule.starProjection_orthogonal_apply_eq_zero hw) X.2 u.2
    rw [hcy] at h0
    have h1 := (Submodule.starProjection_apply_eq_zero_iff Dᗮ).mp h0
    rw [Submodule.orthogonal_orthogonal] at h1
    exact ⟨⟨_, h1⟩, rfl⟩
  -- the chart of the carrier
  set ψ := DifferentialGeometry.PartialDiffeomorph.extChartAt 𝓘(ℝ, EB) 3 s₀ with hψ
  have hψs₀ : s₀ ∈ ψ.source := mem_extChartAt_source s₀
  have hψl : ∀ p ∈ ψ.source, ψ.symm (ψ p) = p := fun p hp => ψ.toPartialEquiv.left_inv hp
  have hcl : ∀ x ∈ c.source, c.symm (c x) = x := fun x hx => c.toPartialEquiv.left_inv hx
  have hcr : ∀ y ∈ c.target, c (c.symm y) = y := fun y hy => c.toPartialEquiv.right_inv hy
  set u₀ : EB := ψ s₀ with hu₀def
  have hps : ψ.symm u₀ = s₀ := hψl s₀ hψs₀
  rw [gS.sectionalCurvature_eq_coefficientSectional hm ψ hψs₀ v w]
  set c3 := DifferentialGeometry.PartialDiffeomorph.ofLE c h3r with hc3
  rw [g.sectionalCurvature_eq_coefficientSectional (le_trans (by norm_num) (le_self_add.trans' h3r))
    c3 hx₀c]
  -- the transition map `Φ₀`
  set U : Set EB := ψ.target ∩ ψ.symm ⁻¹' (b ⁻¹' c.source) with hUdef
  have hUo : IsOpen U :=
    ψ.symm.contMDiffOn.continuousOn.isOpen_inter_preimage ψ.open_target
      (c.open_source.preimage hb.continuous)
  have hu₀U : u₀ ∈ U := ⟨ψ.toPartialEquiv.map_source hψs₀, by
    change b (ψ.symm u₀) ∈ c.source
    rw [hps]; exact hx₀c⟩
  set Φ : EB → E := fun y => c (b (ψ.symm y)) with hΦdef
  set prD : E →L[ℝ] D := D.orthogonalProjectionOnto with hprD
  set Φ₀ : EB → D := fun y => prD (Φ y - a₀) with hΦ₀def
  have hΦA : ∀ y ∈ U, Φ y ∈ A := fun y hy => (himage.apply_mem_iff hy.2).2 (hbS' _)
  have hΦeq : ∀ y ∈ U, a₀ + J (Φ₀ y) = Φ y := by
    intro y hy
    have hmem : Φ y - a₀ ∈ D := AffineSubspace.vsub_mem_direction (hΦA y hy) ha₀A
    have hJ : (J (Φ₀ y) : E) = Φ y - a₀ := by
      change ((D.orthogonalProjectionOnto (Φ y - a₀) : D) : E) = Φ y - a₀
      rw [Submodule.coe_orthogonalProjectionOnto_apply,
        Submodule.starProjection_eq_self_iff.mpr hmem]
    rw [hJ]
    abel
  have hΦs : ContMDiffOn 𝓘(ℝ, EB) 𝓘(ℝ, E) 3 Φ U := by
    have h1 : ContMDiffOn 𝓘(ℝ, EB) I 3 (fun y => b (ψ.symm y)) U :=
      (hb.of_le h3n1).comp_contMDiffOn (ψ.symm.contMDiffOn.mono inter_subset_left)
    exact (c.contMDiffOn.of_le h3r).comp h1 (fun y hy => hy.2)
  have hΦd : ContDiffOn ℝ 3 Φ U := contMDiffOn_iff_contDiffOn.mp hΦs
  have hΦ₀d : ContDiffOn ℝ 3 Φ₀ U := prD.contDiff.comp_contDiffOn (hΦd.sub contDiffOn_const)
  have hΦ₀diff : ∀ y ∈ U, DifferentiableAt ℝ Φ₀ y := fun y hy =>
    (hΦ₀d.contDiffAt (hUo.mem_nhds hy)).differentiableAt (by norm_num)
  have hfd : ∀ y ∈ U, fderiv ℝ Φ y = J.comp (fderiv ℝ Φ₀ y) := by
    intro y hy
    have hev : Φ =ᶠ[𝓝 y] fun y => a₀ + J (Φ₀ y) := by
      filter_upwards [hUo.mem_nhds hy] with y' hy' using (hΦeq y' hy').symm
    rw [hev.fderiv_eq]
    exact ((J.hasFDerivAt.comp y (hΦ₀diff y hy).hasFDerivAt).const_add a₀).fderiv
  have hchain : ∀ y ∈ U, ∀ X : EB, fderiv ℝ Φ y X =
      mfderiv I 𝓘(ℝ, E) c (b (ψ.symm y)) (mfderiv 𝓘(ℝ, EB) I b (ψ.symm y)
        (mfderiv 𝓘(ℝ, EB) 𝓘(ℝ, EB) ψ.symm y X)) := by
    intro y hy X
    have hψd : MDifferentiableAt 𝓘(ℝ, EB) 𝓘(ℝ, EB) ψ.symm y := ψ.symm.mdifferentiableAt h30 hy.1
    have hbd : MDifferentiableAt 𝓘(ℝ, EB) I b (ψ.symm y) := (hb _).mdifferentiableAt hn10
    have hcd : MDifferentiableAt I 𝓘(ℝ, E) c (b (ψ.symm y)) := c.mdifferentiableAt hk0 hy.2
    have h1 := mfderiv_comp y hbd hψd
    have h2 := mfderiv_comp y hcd (hbd.comp y hψd)
    have h3 : mfderiv 𝓘(ℝ, EB) 𝓘(ℝ, E) (c ∘ (b ∘ ψ.symm)) y X =
        mfderiv I 𝓘(ℝ, E) c (b (ψ.symm y)) (mfderiv 𝓘(ℝ, EB) I b (ψ.symm y)
          (mfderiv 𝓘(ℝ, EB) 𝓘(ℝ, EB) ψ.symm y X)) := by
      have e1 := congrArg (fun L : TangentSpace 𝓘(ℝ, EB) y →L[ℝ]
        TangentSpace 𝓘(ℝ, E) (c (b (ψ.symm y))) => L X) h2
      have e2 := congrArg (fun L : TangentSpace 𝓘(ℝ, EB) y →L[ℝ] TangentSpace I (b (ψ.symm y)) =>
        mfderiv I 𝓘(ℝ, E) c (b (ψ.symm y)) (L X)) h1
      exact e1.trans e2
    have h4 : fderiv ℝ Φ y X = mfderiv 𝓘(ℝ, EB) 𝓘(ℝ, E) (c ∘ (b ∘ ψ.symm)) y X := by
      rw [mfderiv_eq_fderiv]
      rfl
    exact h4.trans h3
  have hpull : ∀ y ∈ U, ∀ X Y : EB,
      (gS.inner (ψ.symm y) : EB →L[ℝ] EB →L[ℝ] ℝ).bilinearComp
        (mfderiv 𝓘(ℝ, EB) 𝓘(ℝ, EB) ψ.symm y : EB →L[ℝ] EB)
        (mfderiv 𝓘(ℝ, EB) 𝓘(ℝ, EB) ψ.symm y : EB →L[ℝ] EB) X Y =
      affineSliceCoeff C a₀ J (Φ₀ y) (fderiv ℝ Φ₀ y X) (fderiv ℝ Φ₀ y Y) := by
    intro y hy X Y
    have hX : J (fderiv ℝ Φ₀ y X) = _ :=
      (congrArg (fun L : EB →L[ℝ] E => L X) (hfd y hy)).symm.trans (hchain y hy X)
    have hY : J (fderiv ℝ Φ₀ y Y) = _ :=
      (congrArg (fun L : EB →L[ℝ] E => L Y) (hfd y hy)).symm.trans (hchain y hy Y)
    have e1 := hinner (ψ.symm y) (mfderiv 𝓘(ℝ, EB) 𝓘(ℝ, EB) ψ.symm y X)
      (mfderiv 𝓘(ℝ, EB) 𝓘(ℝ, EB) ψ.symm y Y)
    have e2 := inner_eq_sliceCoeffFinite hk0 g hy.2
      (mfderiv 𝓘(ℝ, EB) I b (ψ.symm y) (mfderiv 𝓘(ℝ, EB) 𝓘(ℝ, EB) ψ.symm y X))
      (mfderiv 𝓘(ℝ, EB) I b (ψ.symm y) (mfderiv 𝓘(ℝ, EB) 𝓘(ℝ, EB) ψ.symm y Y))
    have e3 : affineSliceCoeff C a₀ J (Φ₀ y) (fderiv ℝ Φ₀ y X) (fderiv ℝ Φ₀ y Y) =
        C (Φ y) (J (fderiv ℝ Φ₀ y X)) (J (fderiv ℝ Φ₀ y Y)) := by
      rw [affineSliceCoeff_apply, hΦeq y hy]
    refine e1.trans (e2.trans ((congrArg₂ (fun a a' => C (Φ y) a a') hX.symm hY.symm).trans
      e3.symm))
  -- invertibility of `dΦ₀`
  have hDbinj : ∀ s, Injective (mfderiv 𝓘(ℝ, EB) I b s) := fun s =>
    injective_mfderiv_of_leftInverse_soulCarrier hn10 hRb (hb s) (hR _ (hbS' s))
  have hinj : ∀ y ∈ U, Injective (fderiv ℝ Φ₀ y) := by
    intro y hy X Y hXY
    have h1 : fderiv ℝ Φ y X = fderiv ℝ Φ y Y := by
      rw [hfd y hy, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hXY]
    rw [hchain y hy, hchain y hy] at h1
    have hcinj : Injective (mfderiv I 𝓘(ℝ, E) c (b (ψ.symm y))) := fun a a' h => by
      rw [← mfderiv_symm_apply_mfderiv_ofOrder hk0 hy.2 a,
        ← mfderiv_symm_apply_mfderiv_ofOrder hk0 hy.2 a', h]
    have hψinj : Injective (mfderiv 𝓘(ℝ, EB) 𝓘(ℝ, EB) ψ.symm y) := fun a a' h => by
      rw [← mfderiv_apply_mfderiv_symm_ofOrder h30 hy.1 a,
        ← mfderiv_apply_mfderiv_symm_ofOrder h30 hy.1 a', h]
    exact hψinj (hDbinj _ (hcinj h1))
  set z₀ : D := Φ₀ u₀ with hz₀def
  have hcx₀ : c.symm (a₀ + J z₀) = x₀ := by
    rw [hΦeq u₀ hu₀U]
    change c.symm (c (b (ψ.symm u₀))) = x₀
    rw [hps]
    exact hcl x₀ hx₀c
  have hz₀W : z₀ ∈ W := by
    change a₀ + J z₀ ∈ c.target
    rw [hΦeq u₀ hu₀U]
    exact c.toPartialEquiv.map_source hu₀U.2
  set Ψ : D → EB := fun z => ψ (R (c.symm (a₀ + J z))) with hΨdef
  have hΨz₀ : Ψ z₀ = u₀ := by
    change ψ (R (c.symm (a₀ + J z₀))) = u₀
    rw [hcx₀, hx₀, hRb]
  have hRc : ContinuousAt R x₀ := (hR x₀ (hbS' s₀)).continuousAt
  have hcsc : ContinuousAt (fun z : D => c.symm (a₀ + J z)) z₀ :=
    ContinuousAt.comp (g := c.symm) (f := fun z : D => a₀ + J z)
      (c.symm.contMDiffOn.continuousOn.continuousAt (c.open_target.mem_nhds hz₀W))
      (by fun_prop : Continuous fun z : D => a₀ + J z).continuousAt
  have hRz : ContinuousAt (fun z : D => R (c.symm (a₀ + J z))) z₀ := by
    have hRc' : ContinuousAt R (c.symm (a₀ + J z₀)) := by rw [hcx₀]; exact hRc
    exact ContinuousAt.comp (g := R) (f := fun z : D => c.symm (a₀ + J z)) hRc' hcsc
  have hcomp : ∀ᶠ z in 𝓝 z₀, Φ₀ (Ψ z) = z := by
    have h2 : ∀ᶠ z in 𝓝 z₀, R (c.symm (a₀ + J z)) ∈ ψ.source :=
      hRz.preimage_mem_nhds (ψ.open_source.mem_nhds (by rw [hcx₀, hx₀, hRb]; exact hψs₀))
    filter_upwards [hWo.mem_nhds hz₀W, h2] with z hzW hzψ
    have hyS : c.symm (a₀ + J z) ∈ S := (himage.symm_apply_mem_iff hzW).2 (hJA z)
    obtain ⟨s, hs⟩ : c.symm (a₀ + J z) ∈ range b := hbS ▸ hyS
    have hbR : b (R (c.symm (a₀ + J z))) = c.symm (a₀ + J z) := by rw [← hs, hRb]
    have hΦΨ : Φ (Ψ z) = a₀ + J z := by
      change c (b (ψ.symm (ψ (R (c.symm (a₀ + J z)))))) = a₀ + J z
      rw [hψl _ hzψ, hbR]
      exact hcr _ hzW
    change prD (Φ (Ψ z) - a₀) = z
    rw [hΦΨ, add_sub_cancel_left]
    exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self z
  have hΨd : DifferentiableAt ℝ Ψ z₀ := by
    have h1 : MDifferentiableAt 𝓘(ℝ, D) 𝓘(ℝ, E) (fun z : D => a₀ + J z) z₀ :=
      ((contDiff_const.add J.contDiff).contMDiff (n := 1)).mdifferentiableAt one_ne_zero
    have h2 : MDifferentiableAt 𝓘(ℝ, E) I c.symm (a₀ + J z₀) := c.symm.mdifferentiableAt hk0 hz₀W
    have h3 : MDifferentiableAt I 𝓘(ℝ, EB) R (c.symm (a₀ + J z₀)) := by
      rw [hcx₀]; exact (hR x₀ (hbS' s₀)).mdifferentiableAt hn10
    have h4 : MDifferentiableAt 𝓘(ℝ, EB) 𝓘(ℝ, EB) ψ (R (c.symm (a₀ + J z₀))) := by
      rw [hcx₀, hx₀, hRb]; exact ψ.mdifferentiableAt h30 hψs₀
    exact mdifferentiableAt_iff_differentiableAt.mp (h4.comp z₀ (h3.comp z₀ (h2.comp z₀ h1)))
  have hdim := finrank_eq_of_local_rightInverse hΨz₀ hcomp (hΦ₀diff u₀ hu₀U) hΨd (hinj u₀ hu₀U)
  have hinv : ∀ y ∈ U, (fderiv ℝ Φ₀ y).IsInvertible := by
    intro y hy
    have hbij : Bijective (fderiv ℝ Φ₀ y : EB →ₗ[ℝ] D) :=
      ⟨hinj y hy, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp (hinj y hy)⟩
    exact ⟨(LinearEquiv.ofBijective (fderiv ℝ Φ₀ y : EB →ₗ[ℝ] D) hbij).toContinuousLinearEquiv,
      by ext; rfl⟩
  have hΦUW : MapsTo Φ₀ U W := fun y hy => by
    change a₀ + J (Φ₀ y) ∈ c.target
    rw [hΦeq y hy]
    exact c.toPartialEquiv.map_source hy.2
  have hCAsymm : ∀ z ∈ W, ∀ u v : D, affineSliceCoeff C a₀ J z u v = affineSliceCoeff C a₀ J z v u :=
    fun z hz u v => by rw [affineSliceCoeff_apply, affineSliceCoeff_apply, hCsymm _ (hWU hz)]
  have hCAco : ∀ z ∈ W, IsCoercive (affineSliceCoeff C a₀ J z) := by
    intro z hz
    apply ContinuousLinearMap.isCoercive_of_posDef
    intro u hu
    rw [affineSliceCoeff_apply]
    obtain ⟨κ, hκ, hκu⟩ := hCco _ (hWU hz)
    have hJu : J u ≠ 0 := fun h => hu (hJinj (h.trans (map_zero J).symm))
    exact lt_of_lt_of_le (mul_pos (mul_pos hκ (norm_pos_iff.mpr hJu)) (norm_pos_iff.mpr hJu))
      (hκu _)
  refine (coefficientSectional_transition_cross
    (b := fun y => (gS.inner (ψ.symm y) : EB →L[ℝ] EB →L[ℝ] ℝ).bilinearComp
      (mfderiv 𝓘(ℝ, EB) 𝓘(ℝ, EB) ψ.symm y : EB →L[ℝ] EB)
      (mfderiv 𝓘(ℝ, EB) 𝓘(ℝ, EB) ψ.symm y : EB →L[ℝ] EB))
    hUo hWo (DifferentialGeometry.Analysis.contDiffOn_affineSliceCoeff hC2 a₀ J hWU) hCAsymm hCAco
    hΦ₀d hΦUW hinv hpull hu₀U (mfderiv 𝓘(ℝ, EB) 𝓘(ℝ, EB) ψ s₀ v)
    (mfderiv 𝓘(ℝ, EB) 𝓘(ℝ, EB) ψ s₀ w)).trans ?_
  refine (coefficientSectional_affineSliceCoeff c.open_target hC2 hCsymm hCco a₀ hJinj hWo hWU htg'
    (hΦUW hu₀U) _ _).trans ?_
  have key : ∀ p, ψ.symm u₀ = p → ∀ a : TangentSpace 𝓘(ℝ, EB) s₀, p = s₀ →
      J (fderiv ℝ Φ₀ u₀ (mfderiv 𝓘(ℝ, EB) 𝓘(ℝ, EB) ψ s₀ a)) =
        mfderiv I 𝓘(ℝ, E) c (b p) (mfderiv 𝓘(ℝ, EB) I b p a) := by
    rintro p rfl a -
    have h := (congrArg (fun L : EB →L[ℝ] E => L (mfderiv 𝓘(ℝ, EB) 𝓘(ℝ, EB) ψ s₀ a))
      (hfd u₀ hu₀U)).symm.trans (hchain u₀ hu₀U (mfderiv 𝓘(ℝ, EB) 𝓘(ℝ, EB) ψ s₀ a))
    have hid : mfderiv 𝓘(ℝ, EB) 𝓘(ℝ, EB) ψ.symm u₀ (mfderiv 𝓘(ℝ, EB) 𝓘(ℝ, EB) ψ s₀ a) = a :=
      mfderiv_symm_apply_mfderiv_ofOrder h30 hψs₀ a
    refine h.trans ?_
    exact congrArg (fun t => mfderiv I 𝓘(ℝ, E) c (b (ψ.symm u₀)) (mfderiv 𝓘(ℝ, EB) I b
      (ψ.symm u₀) t)) hid
  have hJv : ∀ a : TangentSpace 𝓘(ℝ, EB) s₀,
      J (fderiv ℝ Φ₀ u₀ (mfderiv 𝓘(ℝ, EB) 𝓘(ℝ, EB) ψ s₀ a)) =
        mfderiv I 𝓘(ℝ, E) c x₀ (mfderiv 𝓘(ℝ, EB) I b s₀ a) := fun a => key s₀ hps a rfl
  have hpt : a₀ + J (Φ₀ u₀) = a₀ := by
    rw [hΦeq u₀ hu₀U]
    change c (b (ψ.symm u₀)) = c x₀
    rw [hps]
  rw [hpt, hJv v, hJv w]
  rfl

end Pointwise

section Frozen

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [FiniteDimensional ℝ EB]
  {B : Type*} [TopologicalSpace B] [ChartedSpace EB B] [IsManifold 𝓘(ℝ, EB) ∞ B]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {r : ℕ∞}

/-- **EXIT-51** (`4 ≤ r`): the frozen statement minus the unused `[NeZero (finrank ℝ E)]`,
`[CompactSpace B]`, `[T2Space B]`, `hbinj` (verbatim form: `InducedMetricApplications.lean`). The
induced metric is `finiteImmersionPullbackMetric g b` of order `r − 2`. -/
theorem exists_inducedMetric_sectional_eq
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 4 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {S : Set M} {d : ℕ} (hS : IsEmbeddedSliceOfOrder I (r : ℕ∞ω) d S)
    (htg : IsTotallyGeodesicFinite g S)
    (b : B → M) (hb : ContMDiff 𝓘(ℝ, EB) I ((r - 1 : ℕ∞) : ℕ∞ω) b) (hbS : range b = S)
    (hbinv : ∃ R : M → B, (∀ s, R (b s) = s) ∧
      ∀ x ∈ S, ContMDiffAt I 𝓘(ℝ, EB) ((r - 1 : ℕ∞) : ℕ∞ω) R x) :
    ∃ gS : ContMDiffRiemannianMetric 𝓘(ℝ, EB) ((r - 2 : ℕ∞) : ℕ∞ω) EB
        (TangentSpace 𝓘(ℝ, EB) : B → Type _),
      (∀ (s : B) (v w : TangentSpace 𝓘(ℝ, EB) s), gS.inner s v w =
        g.inner (b s) (mfderiv 𝓘(ℝ, EB) I b s v) (mfderiv 𝓘(ℝ, EB) I b s w)) ∧
      ∀ (s : B) (v w : TangentSpace 𝓘(ℝ, EB) s), gS.sectionalCurvature s v w =
        g.sectionalCurvature (b s) (mfderiv 𝓘(ℝ, EB) I b s v) (mfderiv 𝓘(ℝ, EB) I b s w) := by
  obtain ⟨R, hRb, hR⟩ := hbinv
  obtain ⟨h3n1, h2n2, hn2n1, hn2r, -, -⟩ := soulCarrier_orders_of_four_le hr
  have hD : g.geodesicFlowDomain = univ :=
    Bundle.ContMDiffRiemannianMetric.geodesicFlowDomain_eq_univ g (le_trans (by norm_num) hr)
      hnorm
  have hn10 : ((r - 1 : ℕ∞) : ℕ∞ω) ≠ 0 := (lt_of_lt_of_le (by norm_num) h3n1).ne'
  have hbS' : ∀ s, b s ∈ S := fun s => hbS ▸ mem_range_self s
  have hinj : ∀ s, Injective (mfderiv 𝓘(ℝ, EB) I b s) := fun s =>
    injective_mfderiv_of_leftInverse_soulCarrier hn10 hRb (hb s) (hR _ (hbS' s))
  refine ⟨finiteImmersionPullbackMetric g b hb hinj hn2r hn2n1, fun s v w => rfl,
    fun s v w => ?_⟩
  exact sectionalCurvature_eq_of_totallyGeodesic_carrier g hr hD hS htg hb hbS hRb hR h2n2 _
    (fun _ _ _ => rfl) s v w

end Frozen

end DifferentialGeometry.Geometry.FiniteSoul
