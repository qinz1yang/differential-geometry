import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.PersistentHyperbolicCores
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.StageTransportBasic

set_option autoImplicit false
noncomputable section
open Set Manifold
open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Topology GC.Topology
open scoped Manifold ContDiff

namespace GC.LongTime.CuspP1

universe u

section Survivor

variable (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)

/-- The backward survivor map as a continuous map. -/
def survivorCM (j : Fin (H.eventCount + 1)) (hj : first ≤ j) (hl : j ≤ last) :
    C(H.backwardSurvivorDomain first last hle, (H.stage j).Carrier) :=
  ⟨H.backwardSurvivorMap first last hle j hj hl,
    continuous_iff_continuousAt.mpr fun x =>
      ((H.backwardSurvivorMap_isLocalDiffeomorph first last hle j hj hl) x).contMDiffAt.continuousAt⟩

@[simp] theorem survivorCM_apply (j : Fin (H.eventCount + 1)) (hj : first ≤ j) (hl : j ≤ last)
    (x : H.backwardSurvivorDomain first last hle) :
    survivorCM H first last hle j hj hl x = H.backwardSurvivorMap first last hle j hj hl x := rfl

end Survivor

section ActiveStage

variable (H : ObservedHistory.{u})

/-- Surgery-free intervals have constant active stage: if no event time lies in `(s, t]`
then the active stage at `s` and at `t` coincide. -/
theorem activeStage_eq_of_no_event (s t : Icc (0 : ℝ) H.horizon) (hst : (s : ℝ) ≤ t)
    (hno : ∀ i : Fin (H.eventCount + 1), H.time i ∉ Ioc (s : ℝ) t) :
    H.activeStage s = H.activeStage t := by
  apply le_antisymm (H.activeStage_mono hst)
  by_contra hlt
  have hle : ¬ H.activeStage t ≤ H.activeStage s := hlt
  have hs : H.time (H.activeStage t) ≤ s := by
    by_contra hh
    exact hno _ ⟨lt_of_not_ge hh, H.activeStage_time_le t⟩
  exact hle (H.le_activeStage s _ hs)

end ActiveStage

section Patch

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
  {H : FiniteVolumeHyperbolicModel.{u}} {T₀ : ℝ} {α : ℝ → ℝ}
  {domain : ℝ → TopologicalSpace.Opens H.Carrier}
  {f : (t : ℝ) → T₀ ≤ t → H.Carrier → (postStage F.observation t).Carrier}
  {t₀ : ℝ} {x₀ : H.Carrier}
  {X : Type*} [TopologicalSpace X]

/-- The torus (any space `X`) mapped into the model patch neighbourhood, pushed through the
patch's smooth map `(t, x) ↦ map (t, x)` into the survivor domain: a continuous family. For
`t ∉ (a, b)` the value is a harmless fallback (the value at `t₀`). -/
def patchTorusMap (p : PersistentModelPatch F H T₀ α domain f t₀ x₀)
    (ι : C(X, H.Carrier)) (hι : ∀ y, ι y ∈ p.neighborhood) (t : ℝ) :
    C(X, (F.tower.history p.n).toHistory.backwardSurvivorDomain p.first p.last p.ordered) := by
  classical
  refine ⟨fun y => p.map ((if t ∈ Ioo p.a p.b then t else t₀), ι y), ?_⟩
  have ht : (if t ∈ Ioo p.a p.b then t else t₀) ∈ Ioo p.a p.b := by
    split_ifs with h
    · exact h
    · exact ⟨p.before, p.after⟩
  refine p.smooth.continuousOn.comp_continuous (by fun_prop) ?_
  intro y
  exact ⟨ht, hι y⟩

theorem patchTorusMap_apply (p : PersistentModelPatch F H T₀ α domain f t₀ x₀)
    (ι : C(X, H.Carrier)) (hι : ∀ y, ι y ∈ p.neighborhood) {t : ℝ} (ht : t ∈ Ioo p.a p.b)
    (y : X) : patchTorusMap p ι hι t y = p.map (t, ι y) := by
  simp [patchTorusMap, ht]

theorem patchTorusMap_continuousOn (p : PersistentModelPatch F H T₀ α domain f t₀ x₀)
    (ι : C(X, H.Carrier)) (hι : ∀ y, ι y ∈ p.neighborhood) :
    ContinuousOn (fun q : ℝ × X => patchTorusMap p ι hι q.1 q.2) (Ioo p.a p.b ×ˢ univ) := by
  have h : ContinuousOn (fun q : ℝ × X => p.map (q.1, ι q.2)) (Ioo p.a p.b ×ˢ univ) := by
    refine p.smooth.continuousOn.comp (by fun_prop) ?_
    rintro ⟨t, y⟩ ⟨ht, -⟩
    exact ⟨ht, hι y⟩
  refine h.congr ?_
  rintro ⟨t, y⟩ ⟨ht, -⟩
  exact patchTorusMap_apply p ι hι ht y

/-- IMS01 smooth segment (frozen interface).  Let `p` be a `PersistentModelPatch` of the actual
`RawSurgery` `F` on the time window `(p.a, p.b)`, let `ι : X → model` be any continuous map
(e.g. a cusp torus) landing in the patch neighbourhood, and let `φ_j` be the backward survivor
map of the patch history to the stage `j ∈ [first, last]`.  Then the kernel of
`π₁(X, x) → π₁(stage j)` induced by `φ_j ∘ p.map(t, ι ·)` is independent of `t ∈ (a, b)`.
No surgery-freeness is needed for this statement: the survivor domain is a fixed space and the
patch map is continuous in `t`; surgery-freeness is only what identifies `stage j` with the
actual slice `M_t` (see `patch_kernel_const_surgeryFree`). -/
theorem patch_kernel_const (p : PersistentModelPatch F H T₀ α domain f t₀ x₀)
    (ι : C(X, H.Carrier)) (hι : ∀ y, ι y ∈ p.neighborhood)
    (j : Fin ((F.tower.history p.n).eventCount + 1)) (hj : p.first ≤ j) (hl : j ≤ p.last)
    {s t : ℝ} (hs : s ∈ Ioo p.a p.b) (ht : t ∈ Ioo p.a p.b) (x : X) :
    (FundamentalGroup.map ((survivorCM (F.tower.history p.n).toHistory p.first p.last p.ordered
        j hj hl).comp (patchTorusMap p ι hι s)) x).ker =
    (FundamentalGroup.map ((survivorCM (F.tower.history p.n).toHistory p.first p.last p.ordered
        j hj hl).comp (patchTorusMap p ι hι t)) x).ker :=
  kernel_const_of_family ordConnected_Ioo (patchTorusMap p ι hι)
    (patchTorusMap_continuousOn p ι hι) _ hs ht x

/-- The same without pushing forward by any survivor map: kernel into the survivor domain. -/
theorem patch_kernel_const_domain (p : PersistentModelPatch F H T₀ α domain f t₀ x₀)
    (ι : C(X, H.Carrier)) (hι : ∀ y, ι y ∈ p.neighborhood)
    {s t : ℝ} (hs : s ∈ Ioo p.a p.b) (ht : t ∈ Ioo p.a p.b) (x : X) :
    (FundamentalGroup.map (patchTorusMap p ι hι s) x).ker =
    (FundamentalGroup.map (patchTorusMap p ι hι t) x).ker := by
  have := kernel_const_of_family ordConnected_Ioo (patchTorusMap p ι hι)
    (patchTorusMap_continuousOn p ι hι) (ContinuousMap.id _) hs ht x
  exact this

/-- Surgery-free form: if no event time of the patch history lies in `(s, t]`, then the active
stage is the same, `j = activeStage s = activeStage t`, lies in `[first, last]`, and the kernel of
`π₁(X, x) → π₁(stage j)` of the transported family at `s` and at `t` agree. -/
theorem patch_kernel_const_surgeryFree (p : PersistentModelPatch F H T₀ α domain f t₀ x₀)
    (ι : C(X, H.Carrier)) (hι : ∀ y, ι y ∈ p.neighborhood)
    (s t : Icc (0 : ℝ) (F.tower.history p.n).horizon) (hst : (s : ℝ) ≤ t)
    (hs : (s : ℝ) ∈ Ioo p.a p.b) (ht : (t : ℝ) ∈ Ioo p.a p.b)
    (hno : ∀ i, (F.tower.history p.n).toHistory.time i ∉ Ioc (s : ℝ) t) (x : X) :
    (FundamentalGroup.map ((survivorCM (F.tower.history p.n).toHistory p.first p.last p.ordered
        ((F.tower.history p.n).toHistory.activeStage s) (p.stages s hs).1 (p.stages s hs).2).comp
        (patchTorusMap p ι hι s)) x).ker =
    (FundamentalGroup.map ((survivorCM (F.tower.history p.n).toHistory p.first p.last p.ordered
        ((F.tower.history p.n).toHistory.activeStage t) (p.stages t ht).1 (p.stages t ht).2).comp
        (patchTorusMap p ι hι t)) x).ker := by
  have heq := activeStage_eq_of_no_event (F.tower.history p.n).toHistory s t hst hno
  have aux : ∀ (j j' : Fin ((F.tower.history p.n).eventCount + 1)) (hjj : j = j')
      (hj : p.first ≤ j) (hl : j ≤ p.last) (hj' : p.first ≤ j') (hl' : j' ≤ p.last),
      (FundamentalGroup.map ((survivorCM (F.tower.history p.n).toHistory p.first p.last
        p.ordered j hj hl).comp (patchTorusMap p ι hι s)) x).ker =
      (FundamentalGroup.map ((survivorCM (F.tower.history p.n).toHistory p.first p.last
        p.ordered j' hj' hl').comp (patchTorusMap p ι hι t)) x).ker := by
    intro j j' hjj hj hl hj' hl'
    subst hjj
    exact patch_kernel_const p ι hι j hj hl hs ht x
  exact aux _ _ heq _ _ _ _

/-- Consumer form: if the actual maps `m t : X → M t` into the slices factor as
`E t ∘ φ_j ∘ (patch family)` on a sub-interval `J` of the window with each `E t`
`π₁`-injective (an identification of the stage with the slice, supplied by the caller from the
tower's `SamePresentation` data), then `ker (π₁ X → π₁ M_t)` is constant on `J`. -/
theorem patch_kernel_const_transported (p : PersistentModelPatch F H T₀ α domain f t₀ x₀)
    (ι : C(X, H.Carrier)) (hι : ∀ y, ι y ∈ p.neighborhood)
    (j : Fin ((F.tower.history p.n).eventCount + 1)) (hj : p.first ≤ j) (hl : j ≤ p.last)
    {J : Set ℝ} (hJ : J.OrdConnected) (hJab : J ⊆ Ioo p.a p.b)
    (M : ℝ → Type*) [∀ t, TopologicalSpace (M t)]
    (E : ∀ t, C(((F.tower.history p.n).toHistory.stage j).Carrier, M t))
    (m : ∀ t, C(X, M t))
    (hm : ∀ t ∈ J, m t = (E t).comp ((survivorCM (F.tower.history p.n).toHistory p.first
      p.last p.ordered j hj hl).comp (patchTorusMap p ι hι t))) (x : X)
    (hE : ∀ t ∈ J, Function.Injective (FundamentalGroup.map (E t)
      (survivorCM (F.tower.history p.n).toHistory p.first p.last p.ordered j hj hl
        (patchTorusMap p ι hι t x))))
    {s t : ℝ} (hs : s ∈ J) (ht : t ∈ J) :
    (FundamentalGroup.map (m s) x).ker = (FundamentalGroup.map (m t) x).ker :=
  kernel_const_of_transported hJ (patchTorusMap p ι hι)
    ((patchTorusMap_continuousOn p ι hι).mono (prod_mono hJab subset_rfl))
    (survivorCM (F.tower.history p.n).toHistory p.first p.last p.ordered j hj hl) M E m hm x
    hE hs ht

end Patch

end GC.LongTime.CuspP1
