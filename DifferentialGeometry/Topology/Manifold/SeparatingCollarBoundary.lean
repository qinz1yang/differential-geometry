import DifferentialGeometry.Topology.Manifold.SeparatingCollar
import DifferentialGeometry.Topology.Manifold.RegularLevel.Sublevel

open Set DifferentialGeometry.Topology.Morse
open scoped Manifold ContDiff Topology
set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.Manifold.RegularLevel

variable {m : ℕ} {H : Type*} [TopologicalSpace H]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  (I : ModelWithCorners ℝ (MorseModel (m + 1)) H)
  [I.Boundaryless] [IsManifold I ∞ M]

@[reducible]
private def setChartedSpace {f : M → ℝ} {a : ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hr : ∀ x, f x = a → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0)
    {t : Set M} (ht : {x | f x ≤ a} = t) : ChartedSpace (MorseHalfSpace m) t :=
  ht ▸ sublevelChartedSpace I hf hr

private theorem setIsManifold {f : M → ℝ} {a : ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hr : ∀ x, f x = a → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0)
    {t : Set M} (ht : {x | f x ≤ a} = t) :
    let _ := setChartedSpace I hf hr ht
    IsManifold (morseModelWithCornersHalfSpace m) ∞ t := by
  cases ht
  exact sublevelIsManifold I hf hr

private def setDiffeomorph {f : M → ℝ} {a : ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hr : ∀ x, f x = a → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0)
    {t : Set M} (ht : {x | f x ≤ a} = t) :
    let _ := sublevelChartedSpace I hf hr
    let _ := setChartedSpace I hf hr ht
    {x : M // f x ≤ a} ≃ₘ⟮morseModelWithCornersHalfSpace m, morseModelWithCornersHalfSpace m⟯ t := by
  cases ht
  let _ := sublevelChartedSpace I hf hr
  exact Diffeomorph.refl _ _ ∞

private theorem setDiffeomorph_toHomeomorph {f : M → ℝ} {a : ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hr : ∀ x, f x = a → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0)
    {t : Set M} (ht : {x | f x ≤ a} = t) :
    let _ := sublevelChartedSpace I hf hr
    let _ := setChartedSpace I hf hr ht
    (setDiffeomorph I hf hr ht).toHomeomorph = Homeomorph.setCongr ht := by
  cases ht
  rfl

private theorem setBoundary_iff {f : M → ℝ} {a : ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hr : ∀ x, f x = a → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0)
    {t : Set M} (ht : {x | f x ≤ a} = t) (x : t) :
    let _ := setChartedSpace I hf hr ht
    (morseModelWithCornersHalfSpace m).IsBoundaryPoint x ↔ f x = a := by
  cases ht
  exact sublevelBoundary_iff I hf hr x

private theorem contMDiff_set_inclusion {f : M → ℝ} {a : ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hr : ∀ x, f x = a → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0)
    {t : Set M} (ht : {x | f x ≤ a} = t) :
    let _ := setChartedSpace I hf hr ht
    ContMDiff (morseModelWithCornersHalfSpace m) I ∞ (Subtype.val : t → M) := by
  cases ht
  exact contMDiff_sublevel_inclusion I hf hr

private def frontierBoundaryHomeomorph {X : Type*} [TopologicalSpace X]
    (A : Set X) (B : Set (closure A))
    (hB : ∀ x : closure A, x ∈ B ↔ (x : X) ∈ frontier (closure A)) :
    frontier (closure A) ≃ₜ B where
  toFun y := ⟨⟨y.val, by
    have hh := frontier_subset_closure y.property
    simpa only [closure_closure] using hh⟩, (hB _).mpr y.property⟩
  invFun x := ⟨x.val.val, (hB x.val).mp x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

end DifferentialGeometry.Manifold.RegularLevel

namespace DifferentialGeometry.Topology.SmoothTwoSidedCollar

open DifferentialGeometry.Manifold.RegularLevel

variable {m : ℕ}
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type} [TopologicalSpace H] {G : Type} [TopologicalSpace G]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ (MorseModel (m + 1)) G}
    {S : Type} [TopologicalSpace S] [ChartedSpace H S]
    {M : Type} [TopologicalSpace M] [ChartedSpace G M]
    {e : S → M} (h : SmoothTwoSidedCollar I J e)
    [CompactSpace S] [ConnectedSpace S] [T2Space M]
    [ConnectedSpace M] [LocallyPathConnectedSpace M]
    [J.Boundaryless] [IsManifold J ∞ M]
    (hsep : ¬ IsConnected h.toTwoSidedCollar.complement)

@[reducible]
def negativeClosureChartedSpace :
    ChartedSpace (MorseHalfSpace m) (closure h.toTwoSidedCollar.negativeSide) :=
  setChartedSpace J (h.contMDiff_sideDefiningFunction_of_disconnected hsep)
    (fun _ hx => h.mfderiv_sideDefiningFunction_ne_zero hx)
    (h.sideDefiningFunction_nonpos_set_of_disconnected hsep)

@[reducible]
def positiveClosureChartedSpace :
    ChartedSpace (MorseHalfSpace m) (closure h.toTwoSidedCollar.positiveSide) :=
  setChartedSpace J (h.contMDiff_oppositeSideDefiningFunction_of_disconnected hsep)
    (fun _ hx => h.mfderiv_oppositeSideDefiningFunction_ne_zero hx)
    (h.oppositeSideDefiningFunction_nonpos_set_of_disconnected hsep)


theorem negativeClosureIsManifold :
    let _ := h.negativeClosureChartedSpace hsep
    IsManifold (morseModelWithCornersHalfSpace m) ∞ (closure h.toTwoSidedCollar.negativeSide) :=
  setIsManifold J (h.contMDiff_sideDefiningFunction_of_disconnected hsep)
    (fun _ hx => h.mfderiv_sideDefiningFunction_ne_zero hx)
    (h.sideDefiningFunction_nonpos_set_of_disconnected hsep)


theorem positiveClosureIsManifold :
    let _ := h.positiveClosureChartedSpace hsep
    IsManifold (morseModelWithCornersHalfSpace m) ∞ (closure h.toTwoSidedCollar.positiveSide) :=
  setIsManifold J (h.contMDiff_oppositeSideDefiningFunction_of_disconnected hsep)
    (fun _ hx => h.mfderiv_oppositeSideDefiningFunction_ne_zero hx)
    (h.oppositeSideDefiningFunction_nonpos_set_of_disconnected hsep)

def negativeSublevelClosureDiffeomorph :
    let _ := DifferentialGeometry.Manifold.RegularLevel.sublevelChartedSpace J
      (h.contMDiff_sideDefiningFunction_of_disconnected hsep)
      (fun _ hx => h.mfderiv_sideDefiningFunction_ne_zero hx)
    let _ := h.negativeClosureChartedSpace hsep
    {x : M // h.sideDefiningFunction x ≤ 0} ≃ₘ⟮morseModelWithCornersHalfSpace m,
      morseModelWithCornersHalfSpace m⟯ (closure h.toTwoSidedCollar.negativeSide) :=
  setDiffeomorph J (h.contMDiff_sideDefiningFunction_of_disconnected hsep)
    (fun _ hx => h.mfderiv_sideDefiningFunction_ne_zero hx)
    (h.sideDefiningFunction_nonpos_set_of_disconnected hsep)


theorem negativeSublevelClosureDiffeomorph_toHomeomorph :
    let _ := DifferentialGeometry.Manifold.RegularLevel.sublevelChartedSpace J
      (h.contMDiff_sideDefiningFunction_of_disconnected hsep)
      (fun _ hx => h.mfderiv_sideDefiningFunction_ne_zero hx)
    let _ := h.negativeClosureChartedSpace hsep
    (h.negativeSublevelClosureDiffeomorph hsep).toHomeomorph =
      Homeomorph.setCongr (h.sideDefiningFunction_nonpos_set_of_disconnected hsep) :=
  setDiffeomorph_toHomeomorph J (h.contMDiff_sideDefiningFunction_of_disconnected hsep)
    (fun _ hx => h.mfderiv_sideDefiningFunction_ne_zero hx)
    (h.sideDefiningFunction_nonpos_set_of_disconnected hsep)


def positiveSublevelClosureDiffeomorph :
    let _ := DifferentialGeometry.Manifold.RegularLevel.sublevelChartedSpace J
      (h.contMDiff_oppositeSideDefiningFunction_of_disconnected hsep)
      (fun _ hx => h.mfderiv_oppositeSideDefiningFunction_ne_zero hx)
    let _ := h.positiveClosureChartedSpace hsep
    {x : M // h.oppositeSideDefiningFunction x ≤ 0} ≃ₘ⟮morseModelWithCornersHalfSpace m,
      morseModelWithCornersHalfSpace m⟯ (closure h.toTwoSidedCollar.positiveSide) :=
  setDiffeomorph J (h.contMDiff_oppositeSideDefiningFunction_of_disconnected hsep)
    (fun _ hx => h.mfderiv_oppositeSideDefiningFunction_ne_zero hx)
    (h.oppositeSideDefiningFunction_nonpos_set_of_disconnected hsep)


theorem positiveSublevelClosureDiffeomorph_toHomeomorph :
    let _ := DifferentialGeometry.Manifold.RegularLevel.sublevelChartedSpace J
      (h.contMDiff_oppositeSideDefiningFunction_of_disconnected hsep)
      (fun _ hx => h.mfderiv_oppositeSideDefiningFunction_ne_zero hx)
    let _ := h.positiveClosureChartedSpace hsep
    (h.positiveSublevelClosureDiffeomorph hsep).toHomeomorph =
      Homeomorph.setCongr (h.oppositeSideDefiningFunction_nonpos_set_of_disconnected hsep) :=
  setDiffeomorph_toHomeomorph J (h.contMDiff_oppositeSideDefiningFunction_of_disconnected hsep)
    (fun _ hx => h.mfderiv_oppositeSideDefiningFunction_ne_zero hx)
    (h.oppositeSideDefiningFunction_nonpos_set_of_disconnected hsep)

theorem negativeClosureBoundary_iff (x : closure h.toTwoSidedCollar.negativeSide) :
    let _ := h.negativeClosureChartedSpace hsep
    (morseModelWithCornersHalfSpace m).IsBoundaryPoint x ↔ (x : M) ∈ range e :=
  (setBoundary_iff J (h.contMDiff_sideDefiningFunction_of_disconnected hsep)
    (fun _ hx => h.mfderiv_sideDefiningFunction_ne_zero hx)
    (h.sideDefiningFunction_nonpos_set_of_disconnected hsep) x).trans
      (h.sideDefiningFunction_eq_zero_iff_mem_range x)


theorem positiveClosureBoundary_iff (x : closure h.toTwoSidedCollar.positiveSide) :
    let _ := h.positiveClosureChartedSpace hsep
    (morseModelWithCornersHalfSpace m).IsBoundaryPoint x ↔ (x : M) ∈ range e :=
  (setBoundary_iff J (h.contMDiff_oppositeSideDefiningFunction_of_disconnected hsep)
    (fun _ hx => h.mfderiv_oppositeSideDefiningFunction_ne_zero hx)
    (h.oppositeSideDefiningFunction_nonpos_set_of_disconnected hsep) x).trans
      (Set.ext_iff.mp h.oppositeSideDefiningFunction_zeroSet x)


theorem negativeClosureBoundary :
    let _ := h.negativeClosureChartedSpace hsep
    (morseModelWithCornersHalfSpace m).boundary (closure h.toTwoSidedCollar.negativeSide) =
      (Subtype.val : closure h.toTwoSidedCollar.negativeSide → M) ⁻¹' range e := by
  let _ := h.negativeClosureChartedSpace hsep
  ext x
  exact h.negativeClosureBoundary_iff hsep x


theorem positiveClosureBoundary :
    let _ := h.positiveClosureChartedSpace hsep
    (morseModelWithCornersHalfSpace m).boundary (closure h.toTwoSidedCollar.positiveSide) =
      (Subtype.val : closure h.toTwoSidedCollar.positiveSide → M) ⁻¹' range e := by
  let _ := h.positiveClosureChartedSpace hsep
  ext x
  exact h.positiveClosureBoundary_iff hsep x


theorem contMDiff_negativeClosure_inclusion :
    let _ := h.negativeClosureChartedSpace hsep
    ContMDiff (morseModelWithCornersHalfSpace m) J ∞
      (Subtype.val : closure h.toTwoSidedCollar.negativeSide → M) :=
  contMDiff_set_inclusion J (h.contMDiff_sideDefiningFunction_of_disconnected hsep)
    (fun _ hx => h.mfderiv_sideDefiningFunction_ne_zero hx)
    (h.sideDefiningFunction_nonpos_set_of_disconnected hsep)


theorem contMDiff_positiveClosure_inclusion :
    let _ := h.positiveClosureChartedSpace hsep
    ContMDiff (morseModelWithCornersHalfSpace m) J ∞
      (Subtype.val : closure h.toTwoSidedCollar.positiveSide → M) :=
  contMDiff_set_inclusion J (h.contMDiff_oppositeSideDefiningFunction_of_disconnected hsep)
    (fun _ hx => h.mfderiv_oppositeSideDefiningFunction_ne_zero hx)
    (h.oppositeSideDefiningFunction_nonpos_set_of_disconnected hsep)

def negativeBoundaryHomeomorph :
    let _ := h.negativeClosureChartedSpace hsep
    S ≃ₜ (morseModelWithCornersHalfSpace m).boundary (closure h.toTwoSidedCollar.negativeSide) := by
  let _ := h.negativeClosureChartedSpace hsep
  exact (h.toTwoSidedCollar.negativeFrontierHomeomorph hsep).trans
    (frontierBoundaryHomeomorph h.toTwoSidedCollar.negativeSide
      ((morseModelWithCornersHalfSpace m).boundary (closure h.toTwoSidedCollar.negativeSide))
      (fun x => by
        rw [h.toTwoSidedCollar.frontier_closure_negativeSide hsep]
        exact h.negativeClosureBoundary_iff hsep x))


theorem negativeBoundaryHomeomorph_coe (s : S) :
    let _ := h.negativeClosureChartedSpace hsep
    (h.negativeBoundaryHomeomorph hsep s).val.val = e s := rfl

def positiveBoundaryHomeomorph :
    let _ := h.positiveClosureChartedSpace hsep
    S ≃ₜ (morseModelWithCornersHalfSpace m).boundary (closure h.toTwoSidedCollar.positiveSide) := by
  let _ := h.positiveClosureChartedSpace hsep
  exact (h.toTwoSidedCollar.positiveFrontierHomeomorph hsep).trans
    (frontierBoundaryHomeomorph h.toTwoSidedCollar.positiveSide
      ((morseModelWithCornersHalfSpace m).boundary (closure h.toTwoSidedCollar.positiveSide))
      (fun x => by
        rw [h.toTwoSidedCollar.frontier_closure_positiveSide hsep]
        exact h.positiveClosureBoundary_iff hsep x))


theorem positiveBoundaryHomeomorph_coe (s : S) :
    let _ := h.positiveClosureChartedSpace hsep
    (h.positiveBoundaryHomeomorph hsep s).val.val = e s := rfl

end DifferentialGeometry.Topology.SmoothTwoSidedCollar
