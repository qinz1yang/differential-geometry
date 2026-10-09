import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0SphereCircleChart

/-!
# FC39 producer, packet P0 (gate 1): the S³ circle kind, the circle bundle

Part A of the circle kind of the S³ inhabitant: the circle bundle of §5.5 on the band
`1 ≤ ψ ≤ 4`, `1 ≤ r ≤ 4` (`C₁ = [1, 4]²` in the base coordinates `(ψ, r)`; `ψ = ‖stereo_N θ‖`,
`r = ‖y‖`), built from the global chart `J = sphereCircleChart` of `FC39P0SphereCircleChart.lean`:

* `Base` = the open square `(1/2, 8)²` of `ℝ²` (`sphereCircleBaseOpens`);
* `domain = J((1/2, 8)² × Circle)` (`sphereCircleDomain`), `proj = fst ∘ J⁻¹`;
* one global trivialisation `J⁻¹ : domain ≃ₘ (1/2, 8)² × Circle` (`sphereCircleTriv`, from the
  tree's `PartialDiffeomorph.toOpensDiffeo`), every neighbourhood `⊤`;
* `cbase = [1, 4]²`.

Result: `sphereCircleBundle : CircleBundle sphereW`, with the closed forms of its projection,
region, fibres and tubes.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open DifferentialGeometry.Topology.Manifold Manifold
open scoped Manifold ContDiff Topology InnerProductSpace

namespace GC.GraphManifold.Assembly.FC39P0

local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## The domain and the global trivialisation -/

/-- The source `(1/2, 8)² × Circle` of the chart, as an open subset. -/
def sphereCircleSource : TopologicalSpace.Opens (E2 × Circle) :=
  ⟨sphereCircleChart.source, sphereCircleChart.open_source⟩

theorem mem_sphereCircleSource_iff {p : E2 × Circle} :
    p ∈ sphereCircleSource ↔ p.1 ∈ sphereCircleBaseOpens := by
  change p ∈ sphereCircleChart.source ↔ p.1 ∈ sphereCircleBaseSet
  rw [sphereCircleChart_source]
  exact ⟨fun h => h.1, fun h => ⟨h, mem_univ _⟩⟩

/-- **The circle domain** `J((1/2, 8)² × Circle)`. -/
def sphereCircleDomain : TopologicalSpace.Opens sphereW.Carrier :=
  ⟨sphereCircleChart '' sphereCircleChart.source,
    image_opens_isOpen sphereCircleChart (U := sphereCircleSource) subset_rfl⟩

/-- The chart as a diffeomorphism of the open source onto the domain. -/
def sphereCircleChartDiffeo :
    sphereCircleSource ≃ₘ⟮(𝓡 2).prod (𝓡 1), 𝓡 3⟯ sphereCircleDomain :=
  DifferentialGeometry.PartialDiffeomorph.toOpensDiffeo sphereCircleChart
    (U := sphereCircleSource) subset_rfl

/-- **The global trivialisation** `J⁻¹ : domain ≃ₘ (1/2, 8)² × Circle`. -/
def sphereCircleTriv :
    sphereCircleDomain ≃ₘ⟮𝓡 3, (𝓡 2).prod (𝓡 1)⟯ (sphereCircleBaseOpens × Circle) :=
  sphereCircleChartDiffeo.symm.trans
    (opensProdDiffeo_CIRCA sphereCircleBaseOpens sphereCircleSource
      fun _ => mem_sphereCircleSource_iff)

theorem sphereCircleTriv_apply (x : sphereCircleDomain) :
    ((sphereCircleTriv x).1 : E2) = (sphereCircleChart.symm x.val).1 ∧
      (sphereCircleTriv x).2 = (sphereCircleChart.symm x.val).2 :=
  ⟨rfl, rfl⟩

theorem sphereCircleTriv_symm_apply (q : sphereCircleBaseOpens × Circle) :
    (sphereCircleTriv.symm q : sphereW.Carrier) = sphereCircleChart (q.1.val, q.2) :=
  rfl

theorem sphereCircleChart_mem_domain {p : E2 × Circle} (hp : p ∈ sphereCircleChart.source) :
    sphereCircleChart p ∈ sphereCircleDomain :=
  ⟨p, hp, rfl⟩

theorem mem_sphereCircleDomain_iff {x : sphereW.Carrier} :
    x ∈ sphereCircleDomain ↔ x ∈ sphereCircleChart.target := by
  change x ∈ sphereCircleChart '' sphereCircleChart.source ↔ _
  rw [sphereCircleChart.toPartialEquiv.image_source_eq_target]

/-! ## The projection -/

/-- **The bundle projection** `x ↦ (ψ, r)` (the base part of `J⁻¹`). -/
def sphereCircleProj (x : sphereCircleDomain) : sphereCircleBaseOpens :=
  (sphereCircleTriv x).1

theorem sphereCircleProj_val (x : sphereCircleDomain) :
    (sphereCircleProj x : E2) = (sphereCircleChart.symm x.val).1 :=
  rfl

/-- The projection in closed form: `ψ = ‖stereo_N θ‖`, `r = ‖y‖` for `x = cycleBallAmbient false y`
and `θ = y / ‖y‖`. -/
theorem sphereCircleEquiv_proj (x : sphereCircleDomain) :
    sphereCircleEquiv (sphereCircleProj x : E2) =
      (‖Handle.stereoChart northPole
          (sphereDirection southPole ((cycleBallAmbient false).symm x.val))‖,
        ‖(cycleBallAmbient false).symm x.val‖) := by
  rw [sphereCircleProj_val, sphereCircleChart_symm_apply, sphereCirclePolar_symm_apply,
    ContinuousLinearEquiv.apply_symm_apply]
  rfl

/-- The projection of a chart point is its base coordinate. -/
theorem sphereCircleProj_chart {p : E2 × Circle} (hp : p ∈ sphereCircleChart.source) :
    (sphereCircleProj ⟨sphereCircleChart p, sphereCircleChart_mem_domain hp⟩ : E2) = p.1 := by
  rw [sphereCircleProj_val]
  exact congrArg Prod.fst (sphereCircleChart.left_inv hp)

/-- The projection of `J((ψ, r), c)` is `(ψ, r)`. -/
theorem sphereCircleEquiv_proj_chart {ψ r : ℝ} (hψ : ψ ∈ sphereCircleWide)
    (hr : r ∈ sphereCircleWide) (c : Circle)
    (hx : sphereCircleChart (sphereCircleEquiv.symm (ψ, r), c) ∈ sphereCircleDomain) :
    sphereCircleEquiv (sphereCircleProj ⟨_, hx⟩ : E2) = (ψ, r) := by
  have hp : (sphereCircleEquiv.symm (ψ, r), c) ∈ sphereCircleChart.source := by
    rw [sphereCircleChart_source]
    exact ⟨sphereCircleEquiv_symm_mem hψ hr, mem_univ _⟩
  rw [sphereCircleProj_chart hp, ContinuousLinearEquiv.apply_symm_apply]

theorem contMDiff_sphereCircleProj : ContMDiff (𝓡 3) (𝓡 2) ∞ sphereCircleProj :=
  contMDiff_fst.comp sphereCircleTriv.contMDiff

/-- **The projection is a submersion** (`fst ∘` a diffeomorphism). -/
theorem sphereCircleProj_submersion (x : sphereCircleDomain) :
    Surjective (mfderiv (𝓡 3) (𝓡 2) sphereCircleProj x) := by
  have hΦ : MDifferentiableAt (𝓡 3) ((𝓡 2).prod (𝓡 1)) sphereCircleTriv x :=
    sphereCircleTriv.contMDiff.mdifferentiableAt (by simp)
  have hfst : MDifferentiableAt ((𝓡 2).prod (𝓡 1)) (𝓡 2)
      (Prod.fst : sphereCircleBaseOpens × Circle → sphereCircleBaseOpens) (sphereCircleTriv x) :=
    mdifferentiableAt_fst
  have h := mfderiv_comp x hfst hΦ
  change Surjective (mfderiv (𝓡 3) (𝓡 2) (Prod.fst ∘ sphereCircleTriv) x)
  rw [h, mfderiv_fst]
  intro v
  obtain ⟨w, hw⟩ := (sphereCircleTriv.mfderivToContinuousLinearEquiv (by simp) x).surjective
    (v, 0)
  have hw' : mfderiv (𝓡 3) ((𝓡 2).prod (𝓡 1)) sphereCircleTriv x w = (v, 0) := hw
  exact ⟨w, congrArg Prod.fst hw'⟩

/-- The projection as a continuous map. -/
def sphereCircleProjMap : C(sphereCircleDomain, sphereCircleBaseOpens) :=
  ⟨sphereCircleProj, contMDiff_sphereCircleProj.continuous⟩

/-- **The trivialisation over `⊤`** in the shape of the contract field. -/
def sphereCircleTrivTop :
    (TopologicalSpace.Opens.comap sphereCircleProjMap
        (⊤ : TopologicalSpace.Opens sphereCircleBaseOpens))
      ≃ₘ⟮𝓡 3, (𝓡 2).prod (𝓡 1)⟯
        ((⊤ : TopologicalSpace.Opens sphereCircleBaseOpens) × Circle) :=
  (opensDiffeoOfForall_CIRCA (TopologicalSpace.Opens.comap sphereCircleProjMap ⊤)
    (fun _ => trivial)).trans (sphereCircleTriv.trans
    ((opensDiffeoOfForall_CIRCA ⊤ (fun _ => trivial)).symm.prodCongr
      (Diffeomorph.refl (𝓡 1) Circle ∞)))

theorem sphereCircleTrivTop_fst (x : TopologicalSpace.Opens.comap sphereCircleProjMap
    (⊤ : TopologicalSpace.Opens sphereCircleBaseOpens)) :
    ((sphereCircleTrivTop x).1).val = sphereCircleProj x.val :=
  rfl

/-! ## The closed base `C₁ = [1, 4]²` -/

/-- The closed square `[1, 4]²` in `ℝ²` (base coordinates `(ψ, r)`). -/
def sphereCircleCbaseSet : Set E2 :=
  sphereCircleEquiv ⁻¹' (Icc 1 4 ×ˢ Icc 1 4)

theorem sphereCircleCbaseSet_subset : sphereCircleCbaseSet ⊆ sphereCircleBaseSet := by
  intro c hc
  exact ⟨⟨by linarith [hc.1.1], by linarith [hc.1.2]⟩, ⟨by linarith [hc.2.1], by linarith [hc.2.2]⟩⟩

/-- **The closed circle base `C₁ = [1, 4]²`.** -/
def sphereCircleCbase : Set sphereCircleBaseOpens :=
  Subtype.val ⁻¹' sphereCircleCbaseSet

theorem image_val_sphereCircleCbase :
    Subtype.val '' sphereCircleCbase = sphereCircleCbaseSet := by
  ext c
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact hc
  · intro hc
    exact ⟨⟨c, sphereCircleCbaseSet_subset hc⟩, hc, rfl⟩

theorem isCompact_sphereCircleCbase : IsCompact sphereCircleCbase := by
  rw [Subtype.isCompact_iff, image_val_sphereCircleCbase]
  exact sphereCircleEquiv.toHomeomorph.isCompact_preimage.2 (isCompact_Icc.prod isCompact_Icc)

/-! ## The S³ circle bundle -/

/-- **The S³ circle bundle** (§5.5, the circle kind of the one S³ configuration): base the open
square `(1/2, 8)²` in the coordinates `(ψ, r)`, domain `J((1/2, 8)² × Circle)`, projection
`fst ∘ J⁻¹`, one global trivialisation `J⁻¹`, closed base `C₁ = [1, 4]²`. -/
def sphereCircleBundle : CircleBundle sphereW where
  Base := sphereCircleBaseOpens
  domain := sphereCircleDomain
  domain_interior _ _ := BoundarylessManifold.isInteriorPoint
  proj := sphereCircleProjMap
  proj_smooth := contMDiff_sphereCircleProj
  proj_submersion := sphereCircleProj_submersion
  neighborhood _ := ⊤
  mem_neighborhood _ := trivial
  trivialization _ := sphereCircleTrivTop
  projection_trivialization _ x := sphereCircleTrivTop_fst x
  cbase := sphereCircleCbase
  cbase_compact := isCompact_sphereCircleCbase

theorem sphereCircleBundle_proj (x : sphereCircleDomain) :
    sphereCircleBundle.proj x = sphereCircleProj x :=
  rfl

theorem sphereCircleBundle_domain : sphereCircleBundle.domain = sphereCircleDomain :=
  rfl

theorem sphereCircleBundle_cbase : sphereCircleBundle.cbase = sphereCircleCbase :=
  rfl

/-! ## Region, fibres and tubes in the chart -/

/-- **Tubes in the chart**: the full circle preimage of a base set `V` is `J(V × Circle)`. -/
theorem sphereCircleBundle_tube (V : Set sphereCircleBaseOpens) :
    sphereCircleBundle.tube V = sphereCircleChart '' ((Subtype.val '' V) ×ˢ univ) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨p, hp, hpy⟩ := y.2
    refine ⟨p, ⟨⟨sphereCircleProj y, hy, ?_⟩, mem_univ _⟩, hpy⟩
    have hy' : y = ⟨sphereCircleChart p, sphereCircleChart_mem_domain hp⟩ := Subtype.ext hpy.symm
    rw [hy']
    exact sphereCircleProj_chart hp
  · rintro ⟨p, ⟨⟨c, hc, hcp⟩, -⟩, rfl⟩
    have hp : p ∈ sphereCircleChart.source := by
      rw [sphereCircleChart_source]
      refine ⟨?_, mem_univ _⟩
      rw [← hcp]
      exact c.2
    refine ⟨⟨sphereCircleChart p, sphereCircleChart_mem_domain hp⟩, ?_, rfl⟩
    change sphereCircleProj ⟨sphereCircleChart p, sphereCircleChart_mem_domain hp⟩ ∈ V
    have he : sphereCircleProj ⟨sphereCircleChart p, sphereCircleChart_mem_domain hp⟩ = c :=
      Subtype.ext ((sphereCircleProj_chart hp).trans hcp.symm)
    rw [he]
    exact hc

/-- **The region** `M₃ = E⁻¹(C₁) = J([1, 4]² × Circle)`. -/
theorem sphereCircleBundle_region :
    sphereCircleBundle.region = sphereCircleChart '' (sphereCircleCbaseSet ×ˢ univ) := by
  have h := sphereCircleBundle_tube sphereCircleCbase
  rw [image_val_sphereCircleCbase] at h
  exact h

/-- **The whole circle fibre** over `c` is `J({c} × Circle)`. -/
theorem sphereCircleBundle_fibre (c : sphereCircleBaseOpens) :
    sphereCircleBundle.fibre c = range fun s : Circle => sphereCircleChart (c.val, s) := by
  have h := sphereCircleBundle_tube {c}
  rw [image_singleton] at h
  refine h.trans ?_
  ext x
  constructor
  · rintro ⟨p, ⟨hp, -⟩, rfl⟩
    refine ⟨p.2, ?_⟩
    rw [show p = (c.val, p.2) from Prod.ext hp rfl]
  · rintro ⟨s, rfl⟩
    exact ⟨(c.val, s), ⟨rfl, mem_univ _⟩, rfl⟩

end GC.GraphManifold.Assembly.FC39P0
