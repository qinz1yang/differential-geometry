import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.P2AdapterReal1_HC2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.P2AdapterReal2_HC2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.P2AdapterReal3_HC2
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Existence
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.HomogeneousRegularity
import DifferentialGeometry.Geometry.Metric.Completeness.PseudoEMetric
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.ComponentDisk
import DifferentialGeometry.Topology.Manifold.BoundaryExtrema
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.P2AdapterOwnDisk

/-!
# S-MIRRORS G4 (`_HC2`): Top Morrey-disk chain on the real IMS03 theorems

Copy of `P2AdapterImportedTop.lean` (Top versions, `PrescribedCuspMeridianTop_CPQ`, of IMS03's
M-version profile/Morrey chain `CuspProfileConfinement.lean:25,153`, `CuspProfileDisk.lean:21`),
with the imports of `P2AdapterImportedLemmas` replaced by the three real theorems of
`P2AdapterReal{1,2,3}_HC2` (so the three placeholder mirrors are no longer used): every use of
`exists_eventual_convex_profiles_P2A`, `canonicalPositiveDomainMetric_complete_homogeneous_P2A`
and `IsMorreyDisk.profile_confinement_P2A` is now the corresponding `_P2A_HC2` theorem, and every
declaration of the file carries the suffix `_P2A_HC2` instead of `_P2A` (the helper definitions
`cutoff_P2A`, `canonicalPositiveDomainMetric_P2A`, ... of `P2AdapterImportedDefs` keep their
names).
No proof is changed.  The two uses of `spans` of the IMS03 originals are replaced:
* the frontier use (`hu₀.2.1`): by `transported_subset_frontier_eventually_P2A_HC2` /
  `frontier_of_profile_P2A_HC2` (from `ρ = 0`, `dρ ≠ 0`);
* the competitor use (`spans` -> disk -> `spanningDiskCompetitors` nonempty): by the explicit
  hypotheses `hcomp` and `hloop` of `exists_eventual_confined_morrey_disk_P2A_HC2`, discharged in
  `P2AdapterImportedMorreyHC2.lean`.
Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
-/

set_option autoImplicit false
noncomputable section

open Bundle Filter Manifold Set TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Geometry.MinimalSurface
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.Endpoint GC.LongTime
open DifferentialGeometry.Geometry.Hyperbolic
open scoped Manifold ContDiff Topology

namespace GC.LongTime.CuspP1

universe u

section Frontier

variable {X : Type*} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]

/-- A smooth function with nonvanishing differential at a zero is on the frontier of its
closed zero sublevel set (no local maximum can have nonzero differential in a boundaryless
manifold). -/
theorem frontier_of_profile_P2A_HC2 {ρ : X → ℝ} {x : X} (hx0 : ρ x = 0)
    (hd : mfderiv (𝓡 3) 𝓘(ℝ) ρ x ≠ 0) (hcont : Continuous ρ) :
    x ∈ frontier {y | ρ y ≤ 0} := by
  have hclosed : IsClosed {y | ρ y ≤ 0} := isClosed_le hcont continuous_const
  rw [frontier, hclosed.closure_eq]
  refine ⟨hx0.le, fun hint => ?_⟩
  have hmax : IsLocalMax ρ x := by
    filter_upwards [mem_interior_iff_mem_nhds.mp hint] with y hy
    exact hx0 ▸ hy
  have hb :=
    DifferentialGeometry.Topology.Manifold.isBoundaryPoint_of_isLocalMax_of_mfderiv_ne_zero
      (I := 𝓡 3) hmax hd
  exact ((𝓡 3).isBoundaryPoint_iff_not_isInteriorPoint x).mp hb
    (BoundarylessManifold.isInteriorPoint (I := 𝓡 3) (x := x))

end Frontier

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {K : ℕ}
  {cores : PersistentHyperbolicCores F K}

/-- For late `t`, the transported prescribed meridian lies on the frontier of the exterior region
(from `ρ = 0` on the port tori and `dρ ≠ 0` on `0 ≤ ρ < a`, both in
`exists_eventual_convex_profiles`). -/
theorem PrescribedCuspMeridianTop_CPQ.transported_subset_frontier_eventually_P2A_HC2
    (M : PrescribedCuspMeridianTop_CPQ cores) (tmin : ℝ) :
    ∃ T₀ : ℝ, ∃ h₀ : M.exterior.start ≤ T₀, tmin ≤ T₀ ∧ 1 ≤ T₀ ∧
      ∀ (t : ℝ) (ht : T₀ ≤ t),
        Set.range (M.transported t (h₀.trans ht)) ⊆ frontier (M.exterior.region t) := by
  obtain ⟨a, ha, T₀, h₀, htmin, htime, hprofiles⟩ :=
    PersistentCuspExterior.exists_eventual_convex_profiles_P2A_HC2 cores M.exterior tmin
  refine ⟨T₀, h₀, htmin, htime, fun t ht => ?_⟩
  obtain ⟨ρ, hρ, hregion, _, hzero, hpos⟩ := hprofiles t ht
  rintro _ ⟨θ, rfl⟩
  rw [hregion, M.prescribed t (h₀.trans ht) θ]
  have hz := hzero M.model M.port (M.loop θ)
  exact frontier_of_profile_P2A_HC2 hz
    (hpos _ (hz.symm.le) (hz ▸ ha)).1 hρ.continuous

/-- Top version of IMS03 `PrescribedCuspMeridian.profile_disk_confinement`
(`CuspProfileConfinement.lean:25` @ 981d9a8cd): the `spans` frontier use is replaced by the
explicit hypothesis `hfront` (supplied by `transported_subset_frontier_eventually_P2A_HC2`-type
facts).  Proof is the IMS03 proof with that one replacement. -/
theorem PrescribedCuspMeridianTop_CPQ.profile_disk_confinement_P2A_HC2
    (M : PrescribedCuspMeridianTop_CPQ cores)
    (T : ℝ) (hT : M.exterior.start ≤ T) (t : ℝ) (ht : T ≤ t)
    (a : ℝ) (ha : 0 < a)
    (ρ : (postStage F.observation t).Carrier → ℝ)
    (hρ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ ρ)
    (hregion : M.exterior.region t = {x | ρ x ≤ 0})
    (hfront : Set.range (M.transported t (hT.trans ht)) ⊆ frontier (M.exterior.region t))
    (hbase : ∀ x : (postStage F.observation t).Carrier,
      0 < ρ x → ρ x < a → ∀ v : TangentSpace (𝓡 3) x,
        0 ≤ hessFun (postMetric F.observation t) ρ x v v)
    (hcontact : ∀ x : (postStage F.observation t).Carrier,
      ρ x = 0 → ∀ v : TangentSpace (𝓡 3) x, v ≠ 0 →
        0 < hessFun (postMetric F.observation t) ρ x v v) :
    let U : Opens (postStage F.observation t).Carrier :=
      ⟨{x | ρ x < a}, isOpen_lt hρ.continuous continuous_const⟩
    let δ : (postStage F.observation t).Carrier → ℝ := fun x => cutoff_P2A a (ρ x)
    let hδ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ δ :=
      (cutoff_smooth_P2A a).contMDiff.comp hρ
    let hU : ∀ x : (postStage F.observation t).Carrier, x ∈ U ↔ 0 < δ x :=
      fun x => (cutoff_pos_iff_P2A ha (ρ x)).symm
    let G := canonicalPositiveDomainMetric_P2A (postMetric F.observation t) hδ U hU
    let ι : C(U, (postStage F.observation t).Carrier) :=
      ⟨Subtype.val, continuous_subtype_val⟩
    ∀ (γU : freeLoop U) (q : C(closedDisk, U)),
      ι.comp γU = M.transported t (hT.trans ht) →
      IsSmoothEmbeddedLoop (E := EuclideanSpace ℝ (Fin 3)) γU →
      IsMorreyDisk G γU q →
      range (ι.comp q) ⊆ M.exterior.region t ∧
      (∀ z : closedDisk, ‖(z : ℂ)‖ < 1 →
        (ι.comp q) z ∈ interior (M.exterior.region t)) ∧
      (∀ z : closedDisk, ‖(z : ℂ)‖ < 1 → ρ ((ι.comp q) z) < 0) ∧
      (∀ θ : loopCircle, ρ ((ι.comp q) (diskBoundary θ)) = 0) ∧
      DiskWeakJordanTrace (M.transported t (hT.trans ht)) (ι.comp q) ∧
      ∀ z : closedDisk, ∀ᶠ y : U in 𝓝 (q z),
        G.inner y = ((postMetric F.observation t).restrictOpen U).inner y ∧
          barrier_P2A a (ρ (y : (postStage F.observation t).Carrier)) =
            ρ (y : (postStage F.observation t).Carrier) := by
  intro U δ hδ hU G ι γU q hγeq hγ hq
  let ρU : U → ℝ := fun x => ρ (x : (postStage F.observation t).Carrier)
  have hρU : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ ρU :=
    hρ.comp contMDiff_subtype_val
  have hρUa : ∀ x : U, ρU x < a := fun x => x.property
  have hG : G = profileMetric_P2A ((postMetric F.observation t).restrictOpen U)
      a ha ρU hρU hρUa := rfl
  have hqProfile : IsMorreyDisk
      (profileMetric_P2A ((postMetric F.observation t).restrictOpen U) a ha ρU hρU hρUa)
      γU q := hG ▸ hq
  have hbaseU (x : U) (hx : 0 < ρU x) (v : TangentSpace (𝓡 3) x) :
      0 ≤ hessFun ((postMetric F.observation t).restrictOpen U) ρU x v v := by
    rw [hessFun_restrictOpen_of_contMDiff (postMetric F.observation t) U ρ hρ]
    exact hbase (x : (postStage F.observation t).Carrier) hx x.property
      (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → (postStage F.observation t).Carrier) x v)
  have hcontactU (x : U) (hx : ρU x = 0) (v : TangentSpace (𝓡 3) x)
      (hv : v ≠ 0) :
      0 < hessFun ((postMetric F.observation t).restrictOpen U) ρU x v v := by
    rw [hessFun_restrictOpen_of_contMDiff (postMetric F.observation t) U ρ hρ]
    simpa only [mfderiv_subtype_val_apply] using
      hcontact (x : (postStage F.observation t).Carrier) hx v hv
  have hγpoint (θ : loopCircle) :
      (γU θ : (postStage F.observation t).Carrier) = M.transported t (hT.trans ht) θ :=
    congrArg (fun η => η θ) hγeq
  have hclosed : IsClosed (M.exterior.region t) := by
    rw [hregion]
    exact isClosed_le hρ.continuous continuous_const
  have hboundary (θ : loopCircle) : ρU (γU θ) ≤ 0 := by
    have hfr : M.transported t (hT.trans ht) θ ∈ frontier (M.exterior.region t) :=
      hfront (mem_range_self θ)
    have hmem := frontier_subset_closure hfr
    rw [hclosed.closure_eq, hregion] at hmem
    change ρ (γU θ : (postStage F.observation t).Carrier) ≤ 0
    rw [hγpoint θ]
    exact hmem
  obtain ⟨hweak, hstrict, hgerms⟩ :=
    IsMorreyDisk.profile_confinement_P2A_HC2 ((postMetric F.observation t).restrictOpen U)
      a ha ρU hρU hρUa hbaseU hcontactU hqProfile hγ hboundary
  have hstrictRegion : {x : (postStage F.observation t).Carrier | ρ x < 0} ⊆
      interior (M.exterior.region t) := by
    apply interior_maximal
    · intro x hx
      rw [hregion]
      exact (show ρ x < 0 from hx).le
    · exact isOpen_lt hρ.continuous continuous_const
  have hloopZero (θ : loopCircle) : ρ (M.transported t (hT.trans ht) θ) = 0 := by
    have hle := hboundary θ
    change ρ (γU θ : (postStage F.observation t).Carrier) ≤ 0 at hle
    rw [hγpoint θ] at hle
    apply le_antisymm hle
    apply le_of_not_gt
    intro hneg
    have hfr : M.transported t (hT.trans ht) θ ∈ frontier (M.exterior.region t) :=
      hfront (mem_range_self θ)
    exact hfr.2 (hstrictRegion hneg)
  obtain ⟨σ, hσ, htrace⟩ := hq.trace
  have hprojectTrace : diskTrace (ι.comp q) = (M.transported t (hT.trans ht)).comp σ := by
    ext θ
    exact (congrArg Subtype.val (congrArg (fun η => η θ) htrace)).trans
      (hγpoint (σ θ))
  refine ⟨?_, ?_, ?_, ?_, ⟨σ, hσ, hprojectTrace⟩, ?_⟩
  · rintro x ⟨z, rfl⟩
    rw [hregion]
    exact hweak z
  · intro z hz
    exact hstrictRegion (hstrict z hz)
  · exact hstrict
  · intro θ
    have hvalue : (ι.comp q) (diskBoundary θ) = M.transported t (hT.trans ht) (σ θ) :=
      congrArg (fun η => η θ) hprojectTrace
    rw [hvalue]
    exact hloopZero (σ θ)
  · intro z
    rw [hG]
    exact hgerms z

/-- Top version of IMS03 `PrescribedCuspMeridian.exists_eventual_profile_disk_confinement`
(`CuspProfileConfinement.lean:153` @ 981d9a8cd).  No `hfront` parameter: it is produced inside
from `ρ = 0` on the port tori and `dρ ≠ 0` (no `spans`). -/
theorem PrescribedCuspMeridianTop_CPQ.exists_eventual_profile_disk_confinement_P2A_HC2
    (M : PrescribedCuspMeridianTop_CPQ cores) (tmin : ℝ) :
    ∃ a : ℝ, ∃ ha : 0 < a, ∃ T₀ : ℝ, ∃ h₀ : M.exterior.start ≤ T₀,
      tmin ≤ T₀ ∧ 1 ≤ T₀ ∧ ∀ (T : ℝ) (h : T₀ ≤ T) (t : ℝ) (ht : T ≤ t),
        ∃ ρ : (postStage F.observation t).Carrier → ℝ,
        ∃ hρ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ ρ,
          M.exterior.region t = {x | ρ x ≤ 0} ∧
          IsCompact (closure {x | ρ x < a}) ∧
          Set.range (M.transported t ((h₀.trans h).trans ht)) ⊆
            frontier (M.exterior.region t) ∧
          (∀ x, 0 ≤ ρ x → ρ x < a →
            mfderiv (𝓡 3) 𝓘(ℝ) ρ x ≠ 0 ∧
            ∀ v : TangentSpace (𝓡 3) x, v ≠ 0 →
              0 < hessFun (postMetric F.observation t) ρ x v v) ∧
          let U : Opens (postStage F.observation t).Carrier :=
            ⟨{x | ρ x < a}, isOpen_lt hρ.continuous continuous_const⟩
          let δ : (postStage F.observation t).Carrier → ℝ := fun x => cutoff_P2A a (ρ x)
          let hδ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ δ :=
            (cutoff_smooth_P2A a).contMDiff.comp hρ
          let hU : ∀ x : (postStage F.observation t).Carrier, x ∈ U ↔ 0 < δ x :=
            fun x => (cutoff_pos_iff_P2A ha (ρ x)).symm
          let G := canonicalPositiveDomainMetric_P2A (postMetric F.observation t) hδ U hU
          let ι : C(U, (postStage F.observation t).Carrier) :=
            ⟨Subtype.val, continuous_subtype_val⟩
          ∀ (γU : freeLoop U) (q : C(closedDisk, U)),
            ι.comp γU = M.transported t ((h₀.trans h).trans ht) →
            IsSmoothEmbeddedLoop (E := EuclideanSpace ℝ (Fin 3)) γU →
            IsMorreyDisk G γU q →
            range (ι.comp q) ⊆ M.exterior.region t ∧
            (∀ z : closedDisk, ‖(z : ℂ)‖ < 1 →
              (ι.comp q) z ∈ interior (M.exterior.region t)) ∧
            (∀ z : closedDisk, ‖(z : ℂ)‖ < 1 → ρ ((ι.comp q) z) < 0) ∧
            (∀ θ : loopCircle, ρ ((ι.comp q) (diskBoundary θ)) = 0) ∧
            DiskWeakJordanTrace (M.transported t ((h₀.trans h).trans ht)) (ι.comp q) ∧
            ∀ z : closedDisk, ∀ᶠ y : U in 𝓝 (q z),
              G.inner y = ((postMetric F.observation t).restrictOpen U).inner y ∧
                barrier_P2A a (ρ (y : (postStage F.observation t).Carrier)) =
                  ρ (y : (postStage F.observation t).Carrier) := by
  obtain ⟨a, ha, T₀, h₀, htmin, htime, hprofiles⟩ :=
    PersistentCuspExterior.exists_eventual_convex_profiles_P2A_HC2 cores M.exterior tmin
  refine ⟨a, ha, T₀, h₀, htmin, htime, ?_⟩
  intro T h t ht
  obtain ⟨ρ, hρ, hregion, hcompact, hzero, hpositive⟩ := hprofiles t (h.trans ht)
  have hfront : Set.range (M.transported t ((h₀.trans h).trans ht)) ⊆
      frontier (M.exterior.region t) := by
    rintro _ ⟨θ, rfl⟩
    rw [hregion, M.prescribed t ((h₀.trans h).trans ht) θ]
    have hz := hzero M.model M.port (M.loop θ)
    exact frontier_of_profile_P2A_HC2 hz (hpositive _ hz.symm.le (hz ▸ ha)).1 hρ.continuous
  refine ⟨ρ, hρ, hregion, hcompact, hfront, hpositive, ?_⟩
  apply M.profile_disk_confinement_P2A_HC2 T (h₀.trans h) t ht a ha ρ hρ hregion hfront
  · intro x hx hxa v
    by_cases hv : v = 0
    · subst v
      simp
    · exact ((hpositive x hx.le hxa).2 v hv).le
  · intro x hx v hv
    exact (hpositive x (by rw [hx]) (hx.trans_lt ha)).2 v hv

/-- Top version of IMS03 `PrescribedCuspMeridian.exists_eventual_confined_morrey_disk`
(`CuspProfileDisk.lean:21` @ 981d9a8cd).  The proof follows the IMS03 structure; the two uses of
`spans` are replaced by (1) the frontier fact produced above and (2) `hcomp`, the explicit
competitor non-emptiness input (shape of lane P2A-13's `spanningDiskCompetitors_nonempty_P2A`;
the Morrey disk is obtained from `exists_morrey_disk` with the mirrored completeness/regularity),
and `hloop` (smooth embedded transported loop).  Both hypotheses are to be discharged by P2A-13.
-/
theorem PrescribedCuspMeridianTop_CPQ.exists_eventual_confined_morrey_disk_P2A_HC2
    (M : PrescribedCuspMeridianTop_CPQ cores) (tmin : ℝ)
    (hloop : ∀ (t : ℝ) (ht : M.exterior.start ≤ t),
      IsSmoothEmbeddedLoop (E := EuclideanSpace ℝ (Fin 3)) (M.transported t ht))
    (hcomp : ∀ (t : ℝ) (ht : M.exterior.start ≤ t)
      (U : Opens (postStage F.observation t).Carrier)
      (G : SmoothRiemannianMetric (𝓡 3) U) (γU : freeLoop U),
      (⟨Subtype.val, continuous_subtype_val⟩ :
        C(U, (postStage F.observation t).Carrier)).comp γU = M.transported t ht →
      IsSmoothEmbeddedLoop (E := EuclideanSpace ℝ (Fin 3)) γU →
      M.exterior.region t ⊆ U → (spanningDiskCompetitors G γU).Nonempty) :
    ∃ a : ℝ, ∃ ha : 0 < a, ∃ T₀ : ℝ, ∃ h₀ : M.exterior.start ≤ T₀,
      tmin ≤ T₀ ∧ 1 ≤ T₀ ∧ ∀ (T : ℝ) (h : T₀ ≤ T) (t : ℝ) (ht : T ≤ t),
        ∃ ρ : (postStage F.observation t).Carrier → ℝ,
        ∃ hρ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ ρ,
          M.exterior.region t = {x | ρ x ≤ 0} ∧
          IsCompact (closure {x | ρ x < a}) ∧
          (∀ x, 0 ≤ ρ x → ρ x < a →
            mfderiv (𝓡 3) 𝓘(ℝ) ρ x ≠ 0 ∧
            ∀ v : TangentSpace (𝓡 3) x, v ≠ 0 →
              0 < hessFun (postMetric F.observation t) ρ x v v) ∧
          let U : Opens (postStage F.observation t).Carrier :=
            ⟨{x | ρ x < a}, isOpen_lt hρ.continuous continuous_const⟩
          let δ : (postStage F.observation t).Carrier → ℝ := fun x => cutoff_P2A a (ρ x)
          let hδ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ δ :=
            (cutoff_smooth_P2A a).contMDiff.comp hρ
          let hU : ∀ x : (postStage F.observation t).Carrier, x ∈ U ↔ 0 < δ x :=
            fun x => (cutoff_pos_iff_P2A ha (ρ x)).symm
          let G := canonicalPositiveDomainMetric_P2A (postMetric F.observation t) hδ U hU
          let ι : C(U, (postStage F.observation t).Carrier) :=
            ⟨Subtype.val, continuous_subtype_val⟩
          ∃ (γU : freeLoop U) (q : C(closedDisk, U)),
            ι.comp γU = M.transported t ((h₀.trans h).trans ht) ∧
            IsSmoothEmbeddedLoop (E := EuclideanSpace ℝ (Fin 3)) γU ∧
            IsMorreyDisk G γU q ∧
            range (ι.comp q) ⊆ M.exterior.region t ∧
            (∀ z : closedDisk, ‖(z : ℂ)‖ < 1 →
              (ι.comp q) z ∈ interior (M.exterior.region t)) ∧
            (∀ z : closedDisk, ‖(z : ℂ)‖ < 1 → ρ ((ι.comp q) z) < 0) ∧
            (∀ θ : loopCircle, ρ ((ι.comp q) (diskBoundary θ)) = 0) ∧
            DiskWeakJordanTrace (M.transported t ((h₀.trans h).trans ht)) (ι.comp q) ∧
            ∀ z : closedDisk, ∀ᶠ y : U in 𝓝 (q z),
              G.inner y = ((postMetric F.observation t).restrictOpen U).inner y ∧
                barrier_P2A a (ρ (y : (postStage F.observation t).Carrier)) =
                  ρ (y : (postStage F.observation t).Carrier) := by
  obtain ⟨a, ha, T₀, h₀, htmin, htime, hprofiles⟩ :=
    M.exists_eventual_profile_disk_confinement_P2A_HC2 tmin
  refine ⟨a, ha, T₀, h₀, htmin, htime, ?_⟩
  intro T h t ht
  obtain ⟨ρ, hρ, hregion, hcompact, hfront, hpositive, hconfine⟩ := hprofiles T h t ht
  refine ⟨ρ, hρ, hregion, hcompact, hpositive, ?_⟩
  let U : Opens (postStage F.observation t).Carrier :=
    ⟨{x | ρ x < a}, isOpen_lt hρ.continuous continuous_const⟩
  let δ : (postStage F.observation t).Carrier → ℝ := fun x => cutoff_P2A a (ρ x)
  have hδ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ δ :=
    (cutoff_smooth_P2A a).contMDiff.comp hρ
  have hU : ∀ x : (postStage F.observation t).Carrier, x ∈ U ↔ 0 < δ x :=
    fun x => (cutoff_pos_iff_P2A ha (ρ x)).symm
  have hWU : M.exterior.region t ⊆ U := by
    intro x hx
    have hxρ : ρ x ≤ 0 := by
      simpa only [hregion, mem_ofPred_eq] using hx
    exact hxρ.trans_lt ha
  let : SecondCountableTopology (postStage F.observation t).Carrier :=
    ChartedSpace.secondCountable_of_sigmaCompact (EuclideanSpace ℝ (Fin 3))
      (postStage F.observation t).Carrier
  let ι : C(U, (postStage F.observation t).Carrier) :=
    ⟨Subtype.val, continuous_subtype_val⟩
  have hts : M.exterior.start ≤ t := (h₀.trans h).trans ht
  -- the transported loop lies in the region (frontier of a closed set), hence in `U`
  have hclosed : IsClosed (M.exterior.region t) := by
    rw [hregion]
    exact isClosed_le hρ.continuous continuous_const
  have hrangeU (θ : loopCircle) : M.transported t hts θ ∈ U :=
    hWU (hclosed.frontier_subset (hfront (mem_range_self θ)))
  let γU : freeLoop U :=
    ⟨fun θ => ⟨M.transported t hts θ, hrangeU θ⟩,
      (M.transported t hts).continuous.subtype_mk _⟩
  have hγeq : ι.comp γU = M.transported t hts := by ext θ; rfl
  have hγ : IsSmoothEmbeddedLoop (E := EuclideanSpace ℝ (Fin 3)) γU :=
    (isSmoothEmbeddedLoop_open_inclusion_iff U γU).mp (hγeq.symm ▸ hloop t hts)
  obtain ⟨hcomplete, hregular⟩ :=
    canonicalPositiveDomainMetric_complete_homogeneous_P2A_HC2 (postMetric F.observation t) hδ U hU
      hcompact (by simp)
  have hfinite := hcomp t hts U
    (canonicalPositiveDomainMetric_P2A (postMetric F.observation t) hδ U hU)
    γU hγeq hγ hWU
  obtain ⟨q, hq⟩ := exists_morrey_disk
    (canonicalPositiveDomainMetric_P2A (postMetric F.observation t) hδ U hU)
    hcomplete hregular γU hγ hfinite
  exact ⟨γU, q, hγeq, hγ, hq, hconfine γU q hγeq hγ hq⟩

end GC.LongTime.CuspP1
