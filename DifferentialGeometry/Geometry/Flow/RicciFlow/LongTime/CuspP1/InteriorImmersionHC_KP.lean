import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.P2AdapterImportedMorreyHC2
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Regularity.ProfileInteriorRank

/-!
# S-K16B-PORT G_final: no interior branch point for the confined Morrey disks of `_HC2`

IMS03 `interior_immersion_of_completed_profile` (K16b, ported verbatim in B1–B4) applied to the
Morrey disk `q` produced by
`PrescribedCuspMeridianTop_CPQ.exists_eventual_confined_morrey_disk_HC2`.

* `cutoff_P2A_eq_cutoff_KP`, `canonicalPositiveDomainMetric_P2A_eq_KP`: the ch15 `_P2A` copies
  and the IMS03 `cutoff` / `canonicalPositiveDomainMetric` are defeq (`rfl`).
* `interior_immersion_of_HC_clauses_KP`: the `_HC2` clauses actually used (`hcvx`, the smooth
  embedded loop, `IsMorreyDisk`, and the boundary clause `ρ = 0`) imply that every smooth
  extension `Q` of `q` is injective on the derivative at each interior point.
* `exists_eventual_confined_morrey_disk_interior_immersion_HC_KP`: the conclusion of
  `exists_eventual_confined_morrey_disk_HC2` with this one more conjunct.
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

theorem cutoff_P2A_eq_cutoff_KP (a r : ℝ) :
    cutoff_P2A a r = DifferentialGeometry.Geometry.Metric.BarrierProfile.cutoff a r :=
  rfl

theorem canonicalPositiveDomainMetric_P2A_eq_KP
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (a : ℝ) (ha : 0 < a) (ρ : M → ℝ)
    (hρ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ ρ) :
    let U : Opens M := ⟨{x | ρ x < a}, isOpen_lt hρ.continuous continuous_const⟩
    canonicalPositiveDomainMetric_P2A g
        ((cutoff_smooth_P2A a).contMDiff.comp hρ) U
        (fun x => (cutoff_pos_iff_P2A ha (ρ x)).symm) =
      canonicalPositiveDomainMetric g
        ((DifferentialGeometry.Geometry.Metric.BarrierProfile.cutoff_smooth a).contMDiff.comp hρ)
        U (fun x => (DifferentialGeometry.Geometry.Metric.BarrierProfile.cutoff_pos_iff ha
          (ρ x)).symm) :=
  rfl

/-- The two Hessian clauses of K16b (`hbase`, `hcontact`) from the single clause `hcvx` of
`exists_eventual_confined_morrey_disk_HC2` (for `v = 0` the Hessian form vanishes). -/
theorem hessian_clauses_of_hcvx_KP
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} (t : ℝ)
    (a : ℝ) (ha : 0 < a) (ρ : (postStage F.observation t).Carrier → ℝ)
    (hcvx : ∀ x, 0 ≤ ρ x → ρ x < a →
      mfderiv (𝓡 3) 𝓘(ℝ) ρ x ≠ 0 ∧
        ∀ v : TangentSpace (𝓡 3) x, v ≠ 0 →
          0 < hessFun (postMetric F.observation t) ρ x v v) :
    (∀ x : (postStage F.observation t).Carrier, 0 < ρ x → ρ x < a →
      ∀ v : TangentSpace (𝓡 3) x, 0 ≤ hessFun (postMetric F.observation t) ρ x v v) ∧
    (∀ x : (postStage F.observation t).Carrier, ρ x = 0 →
      ∀ v : TangentSpace (𝓡 3) x, v ≠ 0 →
        0 < hessFun (postMetric F.observation t) ρ x v v) := by
  refine ⟨fun x h0 h1 v => ?_, fun x hx v hv => (hcvx x hx.ge (hx ▸ ha)).2 v hv⟩
  by_cases hv : v = 0
  · subst hv
    simp
  · exact ((hcvx x h0.le h1).2 v hv).le

/-- The weak Jordan trace identifies the boundary values of `q` with the loop `γ`:
`ρ = 0` on `q ∘ diskBoundary` gives `ρ = 0` on `γ` (the trace parametrization is onto). -/
theorem boundary_zero_of_weak_trace_KP {M : Type*} [TopologicalSpace M] (ρ : M → ℝ)
    {γ : freeLoop M} {q : C(closedDisk, M)} (htr : DiskWeakJordanTrace γ q)
    (hbd : ∀ θ : loopCircle, ρ (q (diskBoundary θ)) = 0) (θ : loopCircle) : ρ (γ θ) = 0 := by
  obtain ⟨σ, hσ, hσtr⟩ := htr
  obtain ⟨θ₀, rfl⟩ := hσ.surjective θ
  have h := congrArg (fun γ' : freeLoop M => ρ (γ' θ₀)) hσtr
  exact h ▸ hbd θ₀

/-- K16b applied to the clauses of `exists_eventual_confined_morrey_disk_HC2`: at a time `t`, with
`ρ` the barrier function of the confining profile (clause `hcvx`: `ρ` has no critical point and a
positive Hessian on `0 ≤ ρ < a`), a Morrey disk `q` of the completed profile metric `G` on
`U = {ρ < a}` with smooth embedded boundary loop `γU` and boundary clause `ρ = 0` has a smooth
extension, and every smooth extension is an immersion at each interior point of the disk, i.e.
`q` has no interior branch point. -/
theorem interior_immersion_of_HC_clauses_KP
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} (t : ℝ)
    (a : ℝ) (ha : 0 < a)
    (ρ : (postStage F.observation t).Carrier → ℝ) (hρ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ ρ)
    (hcvx : ∀ x, 0 ≤ ρ x → ρ x < a →
      mfderiv (𝓡 3) 𝓘(ℝ) ρ x ≠ 0 ∧
        ∀ v : TangentSpace (𝓡 3) x, v ≠ 0 →
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
      IsSmoothEmbeddedLoop (E := EuclideanSpace ℝ (Fin 3)) γU →
      IsMorreyDisk G γU q →
      (∀ θ : loopCircle, ρ ((ι.comp q) (diskBoundary θ)) = 0) →
      (∃ Q : ℂ → U, SmoothDiskExtension (E := EuclideanSpace ℝ (Fin 3)) q Q) ∧
        ∀ Q : ℂ → U, SmoothDiskExtension (E := EuclideanSpace ℝ (Fin 3)) q Q →
          ∀ z ∈ Metric.ball (0 : ℂ) 1,
            Function.Injective (mfderiv 𝓘(ℝ, ℂ) (𝓡 3) Q z) := by
  intro U δ hδ hU G ι γU q hsm hMor hbd
  have hd3 : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := finrank_euclideanSpace_fin
  obtain ⟨hbase, hcontact⟩ := hessian_clauses_of_hcvx_KP t a ha ρ hcvx
  have hγzero : ∀ θ : loopCircle, ρ (γU θ : (postStage F.observation t).Carrier) = 0 :=
    fun θ => boundary_zero_of_weak_trace_KP
      (fun x : U => ρ (x : (postStage F.observation t).Carrier)) hMor.trace hbd θ
  have key := interior_immersion_of_completed_profile hd3 (postMetric F.observation t) a ha ρ hρ
    hbase hcontact
  refine ⟨?_, fun Q hQ z hz => ?_⟩
  · obtain ⟨Q, hQ⟩ := IsMorreyDisk.exists_smooth_extension G hd3 hsm hMor
    exact ⟨Q, hQ⟩
  · exact key γU q hsm hMor hγzero Q hQ z hz

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {K : ℕ}
  {cores : PersistentHyperbolicCores F K}

/-- The conclusion of `exists_eventual_confined_morrey_disk_HC2` with one more conjunct on the
Morrey disk `q`: it has a smooth extension, and every smooth extension is an immersion at each
interior point of the disk (no interior branch point). This is the Route W input for the
stability-radius estimates. -/
theorem PrescribedCuspMeridianTop_CPQ.exists_eventual_confined_morrey_disk_interior_immersion_HC_KP
    (M : PrescribedCuspMeridianTop_CPQ cores) (tmin : ℝ) :
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
            (∀ z : closedDisk, ∀ᶠ y : U in 𝓝 (q z),
              G.inner y = ((postMetric F.observation t).restrictOpen U).inner y ∧
                barrier_P2A a (ρ (y : (postStage F.observation t).Carrier)) =
                  ρ (y : (postStage F.observation t).Carrier)) ∧
            (∃ Q : ℂ → U, SmoothDiskExtension (E := EuclideanSpace ℝ (Fin 3)) q Q) ∧
              ∀ Q : ℂ → U, SmoothDiskExtension (E := EuclideanSpace ℝ (Fin 3)) q Q →
                ∀ z ∈ Metric.ball (0 : ℂ) 1,
                  Function.Injective (mfderiv 𝓘(ℝ, ℂ) (𝓡 3) Q z) := by
  obtain ⟨a, ha, T₀, h₀, h1, h2, hHC⟩ := M.exists_eventual_confined_morrey_disk_HC2 tmin
  refine ⟨a, ha, T₀, h₀, h1, h2, fun T h t ht => ?_⟩
  obtain ⟨ρ, hρ, hreg, hcpt, hcvx, hrest⟩ := hHC T h t ht
  refine ⟨ρ, hρ, hreg, hcpt, hcvx, ?_⟩
  intro U δ hδ hU G ι
  obtain ⟨γU, q, hγι, hsm, hMor, hrange, hint, hneg, hbd, hweak, hloc⟩ := hrest
  exact ⟨γU, q, hγι, hsm, hMor, hrange, hint, hneg, hbd, hweak, hloc,
    interior_immersion_of_HC_clauses_KP t a ha ρ hρ hcvx γU q hsm hMor hbd⟩

/-- Consumer: the interior half of the (frozen) `hMY` rank clause, extracted from the theorem
above: for all late `T ≤ t`, an open `U` (`{ρ < a}`), a Morrey disk `q : C(closedDisk, U)` inside
the exterior region `M.exterior.region t`, and a smooth extension `Q` of `q` that is an immersion
on the open unit disk. -/
example (M : PrescribedCuspMeridianTop_CPQ cores) (tmin : ℝ) :
    ∃ T₀ : ℝ, M.exterior.start ≤ T₀ ∧ ∀ (T : ℝ) (_ : T₀ ≤ T) (t : ℝ) (_ : T ≤ t),
      ∃ (U : Opens (postStage F.observation t).Carrier) (q : C(closedDisk, U)) (Q : ℂ → U),
        range (((⟨Subtype.val, continuous_subtype_val⟩ :
          C(U, (postStage F.observation t).Carrier))).comp q) ⊆ M.exterior.region t ∧
        SmoothDiskExtension (E := EuclideanSpace ℝ (Fin 3)) q Q ∧
        ∀ z ∈ Metric.ball (0 : ℂ) 1, Function.Injective (mfderiv 𝓘(ℝ, ℂ) (𝓡 3) Q z) := by
  obtain ⟨a, ha, T₀, h₀, -, -, hH⟩ :=
    M.exists_eventual_confined_morrey_disk_interior_immersion_HC_KP tmin
  refine ⟨T₀, h₀, fun T h t ht => ?_⟩
  obtain ⟨ρ, hρ, -, -, -, γU, q, -, -, -, hrange, -, -, -, -, -, ⟨Q, hQ⟩, hinj⟩ := hH T h t ht
  exact ⟨_, q, Q, hrange, hQ, hinj Q hQ⟩

end GC.LongTime.CuspP1
