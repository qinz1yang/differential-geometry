import DifferentialGeometry.Geometry.Comparison.FiniteSoul.NormalTube
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.SoulBaseSheet
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.SoulBaseUnitNormal
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.SliceOfOrderManifold
import DifferentialGeometry.Geometry.Metric.Path.RiemannianHopfRinow
import DifferentialGeometry.Topology.FiberBundle.Separation

/-!
# The unit-normal double cover of a codimension-one slice: tube data for W-SUB (CMS3-FLOW, G3)

Design `docs/geometrization/chapter13/design-finite-soul-three-20261004.md` §3 "BASE" and §8 (the input
shape of W-SUB's one-sided kernel `exists_smooth_hypersurface_one_sided`, `Hypersurface/OneSided.lean`;
disposition D4). For a compact `C^r` slice `S` of codimension one (`r ≥ 2`):

* `unitNormalCover g S` — the unit normal vectors `S̃ ⊆ TM` (subtype), with the projection
  `unitNormalCoverProj : S̃ → S`, the antipodal map `unitNormalCoverNeg` (`v ↦ −v`) and the tube map
  `unitNormalTube (v, t) = exp (t v)`;
* `isCompact_unitNormalSet` — `S̃` is compact (image of the level set `{d_S = ε/2}` under `ψ / (ε/2)`);
* `exists_unitNormalCover_tube_data` (**main**) — a charted space on `S̃` over the model of the order-`r`
  structure of `S` (sheets of local unit normal fields, `SoulBaseSheet.lean`) for which, for every
  `1 ≤ n ≤ r − 1`, the tube map is a `C^n` local diffeomorphism on `S̃ × (−ε, ε)`, injective modulo
  `(v, t) ↦ (−v, −t)`, and the projection is a `C^n` local diffeomorphism. The local inverses of the
  tube map are explicit, `x ↦ (ν (π ψ x), g(ψ x, ν (π ψ x)))` from S3-TUBE's `ψ`, so no differential is
  computed.
* equivariance, involution, surjectivity and fibres of the projection.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter Function Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.FiniteSoul

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

section Defs

/-- The unit normal vectors of `S` (the unit-normal double cover `S̃ ⊆ TM`). -/
abbrev unitNormalCover {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) (S : Set M) : Type _ :=
  {v : TangentBundle I M // v ∈ normalSetFinite g S ∧ g.inner v.proj v.snd v.snd = 1}

/-- The projection `S̃ → S`. -/
def unitNormalCoverProj {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) (S : Set M) :
    unitNormalCover g S → S :=
  fun v => ⟨v.1.proj, v.2.1.1⟩

/-- The antipodal map `v ↦ −v` of `S̃`. -/
def unitNormalCoverNeg {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) (S : Set M) :
    unitNormalCover g S → unitNormalCover g S :=
  fun v => ⟨⟨v.1.proj, (-1 : ℝ) • v.1.snd⟩, smul_mem_normalSetFinite g v.2.1 (-1), by
    change g.inner v.1.proj ((-1 : ℝ) • v.1.snd) ((-1 : ℝ) • v.1.snd) = 1
    rw [map_smul, map_smul, smul_apply, smul_smul]
    norm_num
    exact v.2.2⟩

/-- The tube map `(v, t) ↦ exp (t v)` on `S̃ × ℝ`. -/
def unitNormalTube {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) (S : Set M) :
    unitNormalCover g S × ℝ → M :=
  fun q => g.expMap (⟨q.1.1.proj, q.2 • q.1.1.snd⟩ : TangentBundle I M)

omit [FiniteDimensional ℝ E] [I.Boundaryless] in
theorem unitNormalCoverNeg_neg {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) (S : Set M)
    (v : unitNormalCover g S) : unitNormalCoverNeg g S (unitNormalCoverNeg g S v) = v := by
  apply Subtype.ext
  change (⟨v.1.proj, (-1 : ℝ) • (-1 : ℝ) • v.1.snd⟩ : TangentBundle I M) = v.1
  rw [smul_smul]
  norm_num

omit [I.Boundaryless] in
theorem unitNormalTube_neg {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) (S : Set M)
    (v : unitNormalCover g S) (t : ℝ) :
    unitNormalTube g S (unitNormalCoverNeg g S v, -t) = unitNormalTube g S (v, t) := by
  change g.expMap (⟨v.1.proj, (-t) • (-1 : ℝ) • v.1.snd⟩ : TangentBundle I M) =
    g.expMap (⟨v.1.proj, t • v.1.snd⟩ : TangentBundle I M)
  rw [smul_smul]
  norm_num

omit [FiniteDimensional ℝ E] [I.Boundaryless] in
theorem continuous_unitNormalCoverProj {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) (S : Set M) :
    Continuous (unitNormalCoverProj g S) :=
  ((FiberBundle.continuous_proj E (TangentSpace I : M → Type _)).comp
    continuous_subtype_val).subtype_mk _

omit [FiniteDimensional ℝ E] [I.Boundaryless] in
theorem continuous_unitNormalCoverNeg {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) (S : Set M) :
    Continuous (unitNormalCoverNeg g S) := by
  have h : ContMDiff I.tangent I.tangent ∞
      (fun v : TangentBundle I M => (⟨v.proj, (-1 : ℝ) • v.snd⟩ : TangentBundle I M)) :=
    fun v => contMDiffAt_smul_tube contMDiffAt_id contMDiffAt_const
  exact (h.continuous.comp continuous_subtype_val).subtype_mk _

end Defs

variable [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {r : ℕ∞}

omit [I.Boundaryless] [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M] in
/-- The projection `S̃ → S` is onto and its fibres are the antipodal pairs. -/
theorem unitNormalCoverProj_surjective_and_fibres
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r) {S : Set M} {d : ℕ} (hcodim : Module.finrank ℝ E = d + 1)
    (hS : IsEmbeddedSliceOfOrder I (r : ℕ∞ω) d S) :
    Surjective (unitNormalCoverProj g S) ∧
      ∀ v w, unitNormalCoverProj g S v = unitNormalCoverProj g S w ↔
        w = v ∨ w = unitNormalCoverNeg g S v := by
  refine ⟨fun s => ?_, fun v w => ⟨fun h => ?_, fun h => ?_⟩⟩
  · obtain ⟨O, -, hsO, ν, -, hunit, hnormal, -⟩ := exists_local_unitNormal_field g hr hcodim hS s.2
    exact ⟨⟨⟨s, ν s⟩, hnormal s ⟨hsO, s.2⟩, hunit s hsO⟩, rfl⟩
  · have hproj : v.1.proj = w.1.proj := congrArg Subtype.val h
    rcases unit_normal_eq_or_neg g hr hcodim hS v.2.1 w.2.1 hproj v.2.2 w.2.2 with h1 | h1
    · left
      exact Subtype.ext (tangentBundle_mk_eq hproj.symm h1)
    · right
      apply Subtype.ext
      change w.1 = (⟨v.1.proj, (-1 : ℝ) • v.1.snd⟩ : TangentBundle I M)
      exact tangentBundle_mk_eq hproj.symm (by rw [h1, neg_one_smul])
  · rcases h with rfl | rfl
    · rfl
    · rfl

/-- **The unit normal set is compact.** -/
theorem isCompact_unitNormalSet [NeZero (Module.finrank ℝ E)]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {S : Set M} (hSc : IsCompact S) (hSne : S.Nonempty) {d : ℕ}
    (hS : IsEmbeddedSliceOfOrder I (r : ℕ∞ω) d S) :
    IsCompact {v : TangentBundle I M | v ∈ normalSetFinite g S ∧ g.inner v.proj v.snd v.snd = 1} := by
  have : ProperSpace M := Manifold.properSpace_of_isRiemannianManifold I
  obtain ⟨ε, hε, ψ, hψs, hψ, hψexp, -, -⟩ := exists_normalTube_finite g hr hnorm hSc hSne hS
  set ε₀ : ℝ := ε / 2 with hε₀
  have hε₀pos : 0 < ε₀ := by positivity
  have hε₀ε : ε₀ < ε := by rw [hε₀]; linarith
  set L : Set M := {x | infDist x S = ε₀} with hL
  have hLc : IsCompact L := by
    refine (hSc.cthickening (r := ε₀)).of_isClosed_subset
      (isClosed_eq (continuous_infDist_pt S) continuous_const) fun x hx => ?_
    obtain ⟨s, hs, hds⟩ := hSc.exists_infDist_eq_dist hSne x
    exact mem_cthickening_of_dist_le x s ε₀ S hs (by rw [← hds]; exact le_of_eq hx)
  set F : M → TangentBundle I M := fun x => ⟨(ψ x).proj, ε₀⁻¹ • (ψ x).snd⟩ with hF
  have hFc : ContinuousOn F L := by
    intro x hx
    have hxt : infDist x S < ε := by rw [show infDist x S = ε₀ from hx]; exact hε₀ε
    have hψx : ContMDiffAt I I.tangent ((r - 1 : ℕ∞) : ℕ∞ω) ψ x :=
      hψs.contMDiffAt ((isOpen_lt (continuous_infDist_pt S) continuous_const).mem_nhds hxt)
    exact (contMDiffAt_smul_tube hψx contMDiffAt_const).continuousAt.continuousWithinAt
  have himage : F '' L =
      {v : TangentBundle I M | v ∈ normalSetFinite g S ∧ g.inner v.proj v.snd v.snd = 1} := by
    ext v
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hxt : infDist x S < ε := by rw [show infDist x S = ε₀ from hx]; exact hε₀ε
      obtain ⟨hn, -, hlen⟩ := hψ x hxt
      refine ⟨smul_mem_normalSetFinite g hn ε₀⁻¹, ?_⟩
      change g.inner (ψ x).proj (ε₀⁻¹ • (ψ x).snd) (ε₀⁻¹ • (ψ x).snd) = 1
      rw [DifferentialGeometry.Geometry.Collapse.finite_inner_smul_self]
      have h0 := DifferentialGeometry.Geometry.Collapse.finite_inner_self_nonneg g (ψ x).proj
        (ψ x).snd
      have hsq : g.inner (ψ x).proj (ψ x).snd (ψ x).snd = ε₀ ^ 2 := by
        rw [← Real.sq_sqrt h0, hlen, show infDist x S = ε₀ from hx]
      rw [hsq]
      field_simp
    · rintro ⟨hvn, hv1⟩
      set a : TangentBundle I M := ⟨v.proj, ε₀ • v.snd⟩ with ha
      have han : a ∈ normalSetFinite g S := smul_mem_normalSetFinite g hvn ε₀
      have halen : Real.sqrt (g.inner a.proj a.snd a.snd) = ε₀ := by
        change Real.sqrt (g.inner v.proj (ε₀ • v.snd) (ε₀ • v.snd)) = ε₀
        rw [DifferentialGeometry.Geometry.Collapse.finite_inner_smul_self, hv1, mul_one,
          Real.sqrt_sq hε₀pos.le]
      obtain ⟨hψa, hda⟩ := hψexp a han (by rw [halen]; exact hε₀ε)
      refine ⟨g.expMap a, ?_, ?_⟩
      · change infDist (g.expMap a) S = ε₀
        rw [hda, halen]
      · change (⟨(ψ (g.expMap a)).proj, ε₀⁻¹ • (ψ (g.expMap a)).snd⟩ : TangentBundle I M) = v
        rw [hψa]
        change (⟨v.proj, ε₀⁻¹ • ε₀ • v.snd⟩ : TangentBundle I M) = v
        rw [smul_smul, inv_mul_cancel₀ hε₀pos.ne', one_smul]
  rw [← himage]
  exact hLc.image_of_continuousOn hFc

end DifferentialGeometry.Geometry.FiniteSoul
