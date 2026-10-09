import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TimeSmoothingDomain_CX5
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TimeSmoothingSpeed_CX5
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.PersistentHyperbolicCores

set_option autoImplicit false

/-! # H2's actual-flow formula and the `static_patches` producer interface

The discrete maps are explicit H3 inputs, with their actual time-dependent
post-stage codomains. The formula below is defined before any history lift is
chosen. A local history supplies fixed-codomain static representatives, their
exact transition relation, and their projection to these actual maps. The
producer proves joint smoothness, agreement, and the *physical* speed field.

Remaining history statement (not an admitted declaration): for every
`start ≤ t₀` and `p₀ ∈ sourceSlice_CX5 Ω t₀`, produce the local data quantified
in `persistentModelPatch_of_dyadic_lifts_CX5` below: `n, first, last, ordered,
a, b, U, A, φ`, with the stage bounds, the `hraw` HEq identifications and the
exact `hjoin` relation in the same backward-survivor carrier. The maps `φ`
must be static representatives on the *whole source box*, only for indices
whose dyadic windows meet `(a,b)`; a finite history is never asked to cover
an infinite future tail. Source
boxes themselves are supplied by `exists_sourceBox_CX5`; their existence
does not prove survival. The physical differential comparison `hmetric` is
the transported H3 normalized pullback bound (`physical_bound_of_normalized_CX5`).
No `PersistentModelPatch`, smoothed-map speed bound, or `static_patches` field
is an input. Producing these actual history lifts from H3 unscathed-window
data remains a separate 250--450 line estimate, including tower casts and
common surviving source neighbourhoods at event crossings.
-/

noncomputable section
open Set Filter Topology DifferentialGeometry
open DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff

namespace GC.LongTime.Ch12

universe u
variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}

/-- The explicit discrete H3 maps have the correct actual post-stage codomain.
The start-time proof is not used to choose a different point or map. -/
def smoothedPhysicalMap_CX5 (H : FiniteVolumeHyperbolicModel.{u}) (T : ℝ) (hT : 0 < T) (θ : ℝ → ℝ)
    (f : (j : ℕ) → (t : ℝ) → t ∈ Icc (dyadicTime_CX5 T j) (dyadicTime_CX5 T (j + 1)) →
      H.Carrier → (postStage F.observation t).Carrier)
    (E : ℕ → ℝ × H.Carrier → H.Carrier) (t : ℝ) (ht : T ≤ t) (p : H.Carrier) :
    (postStage F.observation t).Carrier :=
  let j := dyadicIndex_CX5 T t
  f j t ⟨(dyadicIndex_mem_CX5 hT ht).1, (dyadicIndex_mem_CX5 hT ht).2.le⟩
    (E j (θ (t / dyadicTime_CX5 T j), p))

/-- Exact local producer for CH12-R1 section 5.3. All history and H3 inputs are
visible; smoothness and the squared physical speed of the resulting patch are
proved from the formula rather than supplied as final-field assumptions. -/
theorem persistentModelPatch_of_dyadic_lifts_CX5
    (H : FiniteVolumeHyperbolicModel.{u}) {T start : ℝ} (hT : 0 < T) (hTstart : T ≤ start)
    (α θ : ℝ → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hθ : ContDiff ℝ ∞ θ) (hθrange : ∀ s, θ s ∈ Icc (0 : ℝ) 1)
    (hθ0 : ∀ s, s ≤ 7 / 4 → θ s = 0) (hθ1 : ∀ s, 15 / 8 ≤ s → θ s = 1)
    (hθderiv : ∀ s, |deriv θ s| ≤ B)
    (f : (j : ℕ) → (t : ℝ) → t ∈ Icc (dyadicTime_CX5 T j) (dyadicTime_CX5 T (j + 1)) →
      H.Carrier → (postStage F.observation t).Carrier)
    (E : ℕ → ℝ × H.Carrier → H.Carrier) (η : ℕ → ℝ) (hη : ∀ j, 0 ≤ η j)
    (Ω : TopologicalSpace.Opens (ℝ × H.Carrier)) (t₀ : ℝ) (p₀ : H.Carrier)
    (n : ℕ) (first last : Fin ((F.tower.history n).eventCount + 1)) (ordered : first ≤ last)
    (a b : ℝ) (ha : T < a) (hbefore : a < t₀) (hafter : t₀ < b)
    (horizon : b ≤ (F.tower.history n).horizon) (U : TopologicalSpace.Opens H.Carrier)
    (hp₀ : p₀ ∈ U) (hbox : ∀ t ∈ Ioo a b, (U : Set H.Carrier) ⊆ sourceSlice_CX5 Ω t)
    (stages : ∀ t : Icc (0 : ℝ) (F.tower.history n).horizon, (t : ℝ) ∈ Ioo a b →
      first ≤ (F.tower.history n).toHistory.activeStage t ∧
        (F.tower.history n).toHistory.activeStage t ≤ last)
    (A : ℕ → TopologicalSpace.Opens H.Carrier)
    (φ : ℕ → H.Carrier → (F.tower.history n).toHistory.backwardSurvivorDomain first last ordered)
    (hφ : ∀ j, dyadicTime_CX5 T j < b → a < dyadicTime_CX5 T (j + 1) →
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ (φ j) (A j))
    (hE : ∀ j, ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) ∞ (E j))
    (himage : ∀ j, dyadicTime_CX5 T j < b → a < dyadicTime_CX5 T (j + 1) →
      ∀ μ ∈ Icc (0 : ℝ) 1, ∀ p ∈ U, E j (μ, p) ∈ A j)
    (hE0 : ∀ j, dyadicTime_CX5 T j < b → a < dyadicTime_CX5 T (j + 1) →
      ∀ p ∈ U, E j (0, p) = p)
    (hjoin : ∀ j, a < dyadicTime_CX5 T (j + 1) → dyadicTime_CX5 T (j + 1) < b →
      ∀ p ∈ U, φ j (E j (1, p)) = φ (j + 1) p)
    (hispeed : ∀ j, dyadicTime_CX5 T j < b → a < dyadicTime_CX5 T (j + 1) →
      ∀ μ ∈ Icc (0 : ℝ) 1, ∀ p ∈ U,
      let v := mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun r => E j (r, p)) μ (timeVector_CX5 μ);
      H.metric.inner (E j (μ, p)) v v ≤ η j ^ 2)
    (hbudget : ∀ j (t : ℝ), t ∈ Ico (dyadicTime_CX5 T j) (dyadicTime_CX5 T (j + 1)) →
      t ∈ Ioo a b → start ≤ t → 4 * B * η j < α t)
    (hraw : ∀ (t : Icc (0 : ℝ) (F.tower.history n).horizon) (ht : (t : ℝ) ∈ Ioo a b),
      start ≤ t → ∀ j (hj : (t : ℝ) ∈ Ico (dyadicTime_CX5 T j) (dyadicTime_CX5 T (j + 1))),
      ∀ p ∈ A j,
        HEq ((F.tower.history n).toHistory.backwardSurvivorMap first last ordered
          ((F.tower.history n).toHistory.activeStage t) (stages t ht).1 (stages t ht).2 (φ j p))
          (f j t ⟨hj.1, hj.2.le⟩ p))
    (hmetric : ∀ (t : Icc (0 : ℝ) (F.tower.history n).horizon) (ht : (t : ℝ) ∈ Ioo a b),
      ∀ j, (t : ℝ) ∈ Ico (dyadicTime_CX5 T j) (dyadicTime_CX5 T (j + 1)) →
      ∀ p ∈ A j, ∀ w : TangentSpace (𝓡 3) p,
        let history := (F.tower.history n).toHistory;
        let ψ := history.backwardSurvivorMap first last ordered (history.activeStage t)
          (stages t ht).1 (stages t ht).2 ∘ φ j;
        (history.stageMetric (history.activeStage t) t).inner (ψ p)
          (mfderiv (𝓡 3) (𝓡 3) ψ p w) (mfderiv (𝓡 3) (𝓡 3) ψ p w) ≤
            4 * (t : ℝ) * H.metric.inner p w w) :
    Nonempty (PersistentModelPatch F H start α (sourceSlice_CX5 Ω)
      (fun t ht => smoothedPhysicalMap_CX5 H T hT θ f E t (hTstart.trans ht)) t₀ p₀) := by
  let G := dyadicSmoothing_CX5 T θ φ E
  have hG : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) ∞ G (Ioo a b ×ˢ (U : Set H.Carrier)) :=
    contMDiffOn_windowSmoothing_CX5 hT ha.le hθ hθrange hθ0 hθ1 φ E U.isOpen
      (fun j => (A j : Set H.Carrier)) hφ hE himage hE0 hjoin
  refine ⟨{
    n := n
    first := first
    last := last
    ordered := ordered
    a := a
    b := b
    a_nonneg := (hT.trans ha).le
    before := hbefore
    after := hafter
    horizon := horizon
    neighborhood := U
    mem_neighborhood := hp₀
    in_domain := fun t ht _ => hbox t ht
    stages := stages
    map := G
    smooth := hG
    agrees := ?_
    speed := ?_
  }⟩
  · intro t ht hstart p hp
    have hj := dyadicIndex_mem_CX5 hT (ha.trans ht.1).le
    have hjb : dyadicTime_CX5 T (dyadicIndex_CX5 T t) < b := hj.1.trans_lt ht.2
    have haj : a < dyadicTime_CX5 T (dyadicIndex_CX5 T t + 1) := ht.1.trans hj.2
    exact hraw t ht hstart (dyadicIndex_CX5 T t) hj _
      (himage _ hjb haj _ (hθrange _) p hp)
  · intro t ht hstart p hp
    let history := (F.tower.history n).toHistory
    let π := history.backwardSurvivorMap first last ordered (history.activeStage t)
      (stages t ht).1 (stages t ht).2
    let ψ : ℕ → H.Carrier → (history.stage (history.activeStage t)).Carrier := fun j => π ∘ φ j
    let j := dyadicIndex_CX5 T t
    have hj := dyadicIndex_mem_CX5 hT (ha.trans ht.1).le
    have hjb : dyadicTime_CX5 T j < b := hj.1.trans_lt ht.2
    have haj : a < dyadicTime_CX5 T (j + 1) := ht.1.trans hj.2
    have hwindow : (t : ℝ) ∈ Icc (dyadicTime_CX5 T j) (2 * dyadicTime_CX5 T j) :=
      ⟨hj.1, by simpa only [dyadicTime_succ_CX5] using hj.2.le⟩
    have hproj : ContMDiff (𝓡 3) (𝓡 3) ∞ π :=
      (history.backwardSurvivorMap_isLocalDiffeomorph first last ordered
        (history.activeStage t) (stages t ht).1 (stages t ht).2).contMDiff
    have hψ : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (ψ j) (A j) :=
      (show ContMDiffOn (𝓡 3) (𝓡 3) ∞ π univ from hproj.contMDiffOn).comp
        (hφ j hjb haj) (fun _ _ => mem_univ _)
    have hpoint := himage j hjb haj _ (hθrange ((t : ℝ) / dyadicTime_CX5 T j)) p hp
    have hspeed := smoothingPiece_physical_speed_CX5 H.metric
      (history.stageMetric (history.activeStage t) t)
      (dyadicTime_pos_CX5 hT j) hwindow hB (hη j) (hbudget j t hj ht hstart) (hθderiv _)
      (hθ.differentiable (by simp) _)
      ((hE j).mdifferentiableAt (by simp))
      ((hψ.contMDiffAt ((A j).isOpen.mem_nhds hpoint)).mdifferentiableAt (by simp))
      (hmetric t ht j hj _ hpoint) (hispeed j hjb haj _ (hθrange _) p hp)
    have hjoin' : ∀ k, a < dyadicTime_CX5 T (k + 1) → dyadicTime_CX5 T (k + 1) < b →
        ∀ x ∈ U, ψ k (E k (1, x)) = ψ (k + 1) x :=
      fun k hka hkb x hx => congrArg π (hjoin k hka hkb x hx)
    have heq := dyadicSmoothing_eventuallyEq_localPiece_CX5 hT ha.le θ hθ0 hθ1 ψ E U.isOpen hE0
      hjoin' (q := ((t : ℝ), p)) ⟨ht, hp⟩
    exact (energy_eq_of_eventuallyEq_CX5 (history.stageMetric (history.activeStage t) t)
      heq (1, 0)).trans_lt hspeed

end GC.LongTime.Ch12
