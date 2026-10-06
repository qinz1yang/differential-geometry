import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Regularity.ProfileFiniteCriticalSet
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Regularity.FiniteFibers
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Embeddedness.CoincidentGermClosure
import DifferentialGeometry.Topology.Maps.ProperCollisionProjection
import DifferentialGeometry.Topology.Maps.LocalCoincidentGerms
import DifferentialGeometry.Geometry.EuclideanDisk.FinitePunctures
import DifferentialGeometry.Topology.Manifold.ImmersionCriterion
import DifferentialGeometry.Topology.Manifold.OpenSubtype

set_option autoImplicit false
noncomputable section

open Bundle Filter Manifold Set Metric TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Geometry.Metric.BarrierProfile
open scoped Manifold ContDiff Topology

namespace DiskRegularity.ConsumerAudit

-- Private receiving mechanics for the supplied original disk and extension.
-- The final profile consumer discharges both rank and singleton assumptions.
private theorem isLocallyInjective_regular_value_restriction
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    (q : C(closedDisk, M)) {Q : ℂ → M}
    (hQ : SmoothDiskExtension (E := E) q Q) (V : Set M)
    (hrank : ∀ z : closedDisk, q z ∈ V →
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Q z)) :
    IsLocallyInjective (V.restrictPreimage (q : closedDisk → M)) := by
  obtain ⟨hQeq, S, hS, hDS, hQs⟩ := hQ
  let Sopen : TopologicalSpace.Opens ℂ := ⟨S, hS⟩
  let F : Sopen → M := fun z => Q z
  have hF : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ F :=
    hQs.comp_contMDiff contMDiff_subtype_val (fun z => z.property)
  let ι : (q ⁻¹' V) → Sopen := fun z => ⟨z.val, hDS z.val.property⟩
  have hι : Continuous ι :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk
      (fun z => hDS z.val.property)
  have hFq (z : q ⁻¹' V) : F (ι z) = q z.val := hQeq z.val
  intro x
  have hDF : Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F (ι x)) := by
    change Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun z : Sopen => Q z) (ι x) : ℂ →L[ℝ] E)
    rw [DifferentialGeometry.mfderiv_restrict_open]
    exact hrank x.val x.property
  have hImm := DifferentialGeometry.Topology.Manifold.isImmersionAt_of_injective_mfderiv
    (by simp : (∞ : ℕ∞ω) ≠ 0) hF (ι x) hDF
  have hnormal (z : Sopen) (hz : z ∈ hImm.domChart.source) :
      (hImm.codChart.extend 𝓘(ℝ, E)) (F z) =
        hImm.equiv ((hImm.domChart.extend 𝓘(ℝ, ℂ)) z, 0) := by
    have hz' : z ∈ (hImm.domChart.extend 𝓘(ℝ, ℂ)).source := by
      rwa [OpenPartialHomeomorph.extend_source]
    have hh := hImm.writtenInCharts ((hImm.domChart.extend 𝓘(ℝ, ℂ)).map_source hz')
    simpa only [Function.comp_apply,
      (hImm.domChart.extend 𝓘(ℝ, ℂ)).left_inv hz'] using hh
  have hinj : Set.InjOn F hImm.domChart.source := by
    intro z hz w hw hzw
    have hh := (hnormal z hz).symm.trans
      ((congrArg (hImm.codChart.extend 𝓘(ℝ, E)) hzw).trans (hnormal w hw))
    apply (hImm.domChart.extend 𝓘(ℝ, ℂ)).injOn
    · rwa [OpenPartialHomeomorph.extend_source]
    · rwa [OpenPartialHomeomorph.extend_source]
    · exact congrArg Prod.fst (hImm.equiv.injective hh)
  refine ⟨ι ⁻¹' hImm.domChart.source, hImm.domChart.open_source.preimage hι,
    hImm.mem_domChart_source, ?_⟩
  intro z hz w hw hzw
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun t : Sopen => (t : ℂ))
    (hinj hz hw ((hFq z).trans
      ((congrArg Subtype.val hzw).trans (hFq w).symm)))

private theorem regular_value_coincident_germs_isClosed
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M}
    {γ : freeLoop M} {q : C(closedDisk, M)}
    (hq : IsMorreyDisk g γ q) (hd3 : Module.finrank ℝ E = 3)
    {Q : ℂ → M} (hQ : SmoothDiskExtension (E := E) q Q)
    (V : Set M) (hV : IsOpen V)
    (hrank : ∀ z : closedDisk, q z ∈ V →
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Q z))
    (hsingle : ∀ z : closedDisk, ‖(z : ℂ)‖ = 1 →
      ∀ w, q w = q z → w = z) :
    IsClosed {p : orderedCollisionPairs (V.restrictPreimage (q : closedDisk → M)) |
      Filter.map (V.restrictPreimage (q : closedDisk → M)) (𝓝 p.1.1) =
        Filter.map (V.restrictPreimage (q : closedDisk → M)) (𝓝 p.1.2)} := by
  classical
  let R : Set closedDisk := q ⁻¹' V
  let qr := V.restrictPreimage (q : closedDisk → M)
  have hR : IsOpen R := hV.preimage q.continuous
  have hsource (z : R) :
      Filter.map (Subtype.val : R → closedDisk) (𝓝 z) = 𝓝 z.val :=
    hR.isOpenEmbedding_subtypeVal.map_nhds_eq z
  have hmap (z : R) :
      Filter.map (Subtype.val : V → M) (Filter.map qr (𝓝 z)) =
        Filter.map q (𝓝 z.val) := by
    rw [Filter.map_map]
    change Filter.map ((q : closedDisk → M) ∘ (Subtype.val : R → closedDisk))
      (𝓝 z) = Filter.map q (𝓝 z.val)
    rw [← Filter.map_map, hsource]
  have hinterior (x y : closedDisk) (hne : x ≠ y) (hxy : q x = q y) :
      (x : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
    apply mem_ball_zero_iff.mpr
    by_contra hnot
    have hnorm : ‖(x : ℂ)‖ = 1 :=
      le_antisymm (mem_closedBall_zero_iff.mp x.property) (le_of_not_gt hnot)
    exact hne (hsingle x hnorm y hxy.symm).symm
  have hrankInterior (z : R) (hz : (z.val : ℂ) ∈ Metric.ball (0 : ℂ) 1) :
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension q) z.val) := by
    have hder :
        (show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Q z.val) =
          (show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension q) z.val) := by
      ext v
      exact congrArg (fun L => L v)
        ((hQ.eventuallyEq_diskExtension hz).mfderiv_eq
          (I := 𝓘(ℝ, ℂ)) (I' := 𝓘(ℝ, E)))
    have hQrank : Function.Injective
        (show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Q z.val) :=
      hrank z.val z.property
    change Function.Injective
      (show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension q) z.val)
    intro v w hvw
    apply hQrank
    exact (congrArg (fun L : ℂ →L[ℝ] E => L v) hder).trans
      (hvw.trans (congrArg (fun L : ℂ →L[ℝ] E => L w) hder).symm)
  have hrestriction : diskExtension q ∘ (Subtype.val : closedDisk → ℂ) =
      (q : closedDisk → M) := funext (diskExtension_coe q)
  have hdisk (z : closedDisk) (hz : (z : ℂ) ∈ Metric.ball (0 : ℂ) 1) :
      Filter.map q (𝓝 z) = Filter.map (diskExtension q) (𝓝 (z : ℂ)) := by
    calc
      Filter.map q (𝓝 z) =
          Filter.map (diskExtension q ∘ (Subtype.val : closedDisk → ℂ)) (𝓝 z) :=
        congrArg (fun f : closedDisk → M => Filter.map f (𝓝 z)) hrestriction.symm
      _ = Filter.map (diskExtension q) (𝓝 (z : ℂ)) := by
        rw [← Filter.map_map, map_nhds_subtype_val]
        rw [nhdsWithin_eq_nhds.2
          (Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hz)
            Metric.ball_subset_closedBall)]
  have hfull (z : R) (hz : (z.val : ℂ) ∈ Metric.ball (0 : ℂ) 1) :
      Filter.map (Subtype.val : V → M) (Filter.map qr (𝓝 z)) =
        Filter.map (diskExtension q) (𝓝 (z.val : ℂ)) :=
    (hmap z).trans (hdisk z.val hz)
  apply IsSeqClosed.isClosed
  intro seq p hseq hlim
  have hne (s : orderedCollisionPairs qr) : s.1.1.val ≠ s.1.2.val :=
    fun h => s.2.1 (Subtype.ext h)
  have heq (s : orderedCollisionPairs qr) : q s.1.1.val = q s.1.2.val :=
    congrArg Subtype.val s.2.2
  have ha := hinterior p.1.1.val p.1.2.val (hne p) (heq p)
  have hb := hinterior p.1.2.val p.1.1.val (Ne.symm (hne p)) (heq p).symm
  have hα : Tendsto (fun n => ((seq n).1.1.val : ℂ)) atTop
      (𝓝 (p.1.1.val : ℂ)) :=
    (continuous_subtype_val.comp (continuous_subtype_val.comp
      (continuous_fst.comp continuous_subtype_val))).continuousAt.tendsto.comp hlim
  have hβ : Tendsto (fun n => ((seq n).1.2.val : ℂ)) atTop
      (𝓝 (p.1.2.val : ℂ)) :=
    (continuous_subtype_val.comp (continuous_subtype_val.comp
      (continuous_snd.comp continuous_subtype_val))).continuousAt.tendsto.comp hlim
  have hgerms : ∀ᶠ n in atTop,
      Filter.map (diskExtension q) (𝓝 ((seq n).1.1.val : ℂ)) =
        Filter.map (diskExtension q) (𝓝 ((seq n).1.2.val : ℂ)) := by
    apply Filter.Eventually.of_forall
    intro n
    have hna := hinterior (seq n).1.1.val (seq n).1.2.val (hne (seq n)) (heq (seq n))
    have hnb := hinterior (seq n).1.2.val (seq n).1.1.val
      (Ne.symm (hne (seq n))) (heq (seq n)).symm
    exact (hfull _ hna).symm.trans
      ((congrArg (Filter.map (Subtype.val : V → M)) (hseq n)).trans (hfull _ hnb))
  have hvalue : diskExtension q p.1.1.val = diskExtension q p.1.2.val := by
    simpa only [diskExtension_coe] using heq p
  have hneC : (p.1.1.val : ℂ) ≠ (p.1.2.val : ℂ) :=
    fun h => hne p (Subtype.ext h)
  have hgerm :=
    CuspIncompressibility.ConsumerAudit.morrey_image_germs_eq_of_regular_interior_collision_limit
      hq hd3 ha hb hneC hvalue
      (hrankInterior _ ha) (hrankInterior _ hb) hα hβ hgerms
  apply Filter.map_injective (Subtype.val_injective : Function.Injective (Subtype.val : V → M))
  exact (hfull _ ha).trans (hgerm.trans (hfull _ hb).symm)

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

/-- The same original profile disk, restricted over its regular values, is proper
and has no distinct coincident image germs. All removed fibers are finite;
rank, analytic closure, openness and connectedness are derived for this literal
restriction. No assertion of global rank or exclusion of transverse collisions
is made. -/
theorem profile_regular_value_restriction_no_coincident_germs
    (hd3 : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (a : ℝ) (ha : 0 < a)
    (ρ : M → ℝ) (hρ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ ρ)
    (hbase : ∀ x : M, 0 < ρ x → ρ x < a →
      ∀ v : TangentSpace 𝓘(ℝ, E) x, 0 ≤ hessFun g ρ x v v)
    (hcontact : ∀ x : M, ρ x = 0 → ∀ v : TangentSpace 𝓘(ℝ, E) x,
      v ≠ 0 → 0 < hessFun g ρ x v v) :
    let U : Opens M := ⟨{x | ρ x < a}, isOpen_lt hρ.continuous continuous_const⟩
    let δ : M → ℝ := fun x => cutoff a (ρ x)
    let hδ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ δ :=
      (cutoff_smooth a).contMDiff.comp hρ
    let hU : ∀ x : M, x ∈ U ↔ 0 < δ x :=
      fun x => (cutoff_pos_iff ha (ρ x)).symm
    let G := canonicalPositiveDomainMetric g hδ U hU
    ∀ (γU : freeLoop U) (q : C(closedDisk, U)),
      IsSmoothEmbeddedLoop (E := E) γU → IsMorreyDisk G γU q →
      (∀ θ : loopCircle, ρ (γU θ : M) = 0) →
      ∀ (Q : ℂ → U), SmoothDiskExtension (E := E) q Q →
      let B : Set closedDisk := {z | ¬ Function.Injective
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Q z)}
      let V : Set U := (q '' B)ᶜ
      (q ⁻¹' (q '' B)).Finite ∧
        IsProperMap (V.restrictPreimage (q : closedDisk → U)) ∧
        coincidentGermPairs (V.restrictPreimage (q : closedDisk → U)) = ∅ := by
  classical
  let U : Opens M := ⟨{x | ρ x < a}, isOpen_lt hρ.continuous continuous_const⟩
  dsimp only
  intro γU q hγ hq hγzero Q hQ
  let B : Set closedDisk := {z | ¬ Function.Injective
    (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Q z)}
  let V : Set U := (q '' B)ᶜ
  let D : Set closedDisk := q ⁻¹' (q '' B)
  let R : Set closedDisk := q ⁻¹' V
  let qr := V.restrictPreimage (q : closedDisk → U)
  have hprofile := profile_boundary_singletons_and_finite_critical_set
    g a ha ρ hρ hbase hcontact γU q hγ hq hγzero Q hQ
  obtain ⟨_, hsingle, r₀, _, hr₀, _, _, hBfinite, hDinner⟩ := hprofile
  have hB : B.Finite := hBfinite
  have hfibers := morrey_finite_fibers_of_boundary_fibers_singleton hq hγ hsingle
  have hD : D.Finite := by
    apply (hB.biUnion (fun b _ => hfibers (q b))).subset
    intro z hz
    obtain ⟨b, hb, hbz⟩ := hz
    exact Set.mem_iUnion.mpr ⟨b, Set.mem_iUnion.mpr ⟨hb, hbz.symm⟩⟩
  have hDinner (z : closedDisk) (hz : z ∈ D) : ‖(z : ℂ)‖ < 1 :=
    (hDinner z hz).trans_lt hr₀
  have hV : IsOpen V := (hB.image q).isClosed.isOpen_compl
  have hR : IsOpen R := hV.preimage q.continuous
  have hconnected : IsPreconnected R := by
    change IsPreconnected (Dᶜ : Set closedDisk)
    exact isPreconnected_closedDisk_compl_of_finite hD hDinner
  let : PreconnectedSpace R := Subtype.preconnectedSpace hconnected
  let : LocallyCompactSpace R := hR.locallyCompactSpace
  have hrank (z : closedDisk) (hz : q z ∈ V) :
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Q z) := by
    by_contra hnot
    exact hz ⟨z, hnot, rfl⟩
  have hloc : IsLocallyInjective qr :=
    isLocallyInjective_regular_value_restriction q hQ V hrank
  have hanalytic : IsClosed {p : orderedCollisionPairs qr |
      Filter.map qr (𝓝 p.1.1) = Filter.map qr (𝓝 p.1.2)} :=
    regular_value_coincident_germs_isClosed hq hd3 hQ V hV hrank hsingle
  obtain ⟨hproper, hclosed⟩ :=
    proper_and_isClosed_coincidentGerm_projection_restrictPreimage q V hloc hanalytic
  refine ⟨hD, hproper, ?_⟩
  let S : Set R := Prod.fst '' coincidentGermPairs qr
  have hS : IsClopen S :=
    ⟨hclosed, isOpen_fst_image_coincidentGermPairs_of_locallyCompact
      hproper.continuous hloc⟩
  let z₀ : closedDisk := ⟨1, by simp⟩
  have hz₀norm : ‖(z₀ : ℂ)‖ = 1 := norm_one
  have hz₀R : z₀ ∈ R := by
    change z₀ ∉ D
    intro hz
    have hlt := hDinner z₀ hz
    rw [hz₀norm] at hlt
    exact (lt_irrefl (1 : ℝ)) hlt
  let x₀ : R := ⟨z₀, hz₀R⟩
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro p hp
  have hSuniv : S = Set.univ := hS.eq_univ ⟨p.1, p, hp, rfl⟩
  have hx₀S : x₀ ∈ S := Set.eq_univ_iff_forall.mp hSuniv x₀
  obtain ⟨⟨x, y⟩, hxy, hxx₀⟩ := hx₀S
  change x = x₀ at hxx₀
  subst x
  have hy : y.val = z₀ :=
    hsingle z₀ hz₀norm y.val (congrArg Subtype.val hxy.2.1).symm
  exact hxy.1 (Subtype.ext hy).symm

end DiskRegularity.ConsumerAudit
