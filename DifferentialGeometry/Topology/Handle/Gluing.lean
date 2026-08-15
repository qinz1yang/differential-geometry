import DifferentialGeometry.Topology.Handle.Attachment
import DifferentialGeometry.Topology.Handle.Manifold

namespace DifferentialGeometry.Topology.Handle

open scoped Manifold

noncomputable section

universe u v w u'

variable {k l : ℕ}

def adjunctionMap {X : Type u} {Y : Type v} (φ : AttachingRegion k l → X)
    (φ' : AttachingRegion k l → Y) (h : X → Y) (hφ : ∀ a, h (φ a) = φ' a) :
    AdjunctionSpace k l φ → AdjunctionSpace k l φ' :=
  Quot.lift (Sum.elim (fun d : StandardHandle k l => cell φ' d) (fun x : X => lower φ' (h x)))
    (by
      intro a b hab
      rcases hab with ⟨x, hx | hx⟩
      · rcases hx with ⟨ha, hb⟩
        subst a
        subst b
        change cell φ' (attachingInclusion k l x) = lower φ' (h (φ x))
        rw [adjunction_coherence φ' x]
        exact congrArg (lower φ') (hφ x).symm
      · rcases hx with ⟨hb, ha⟩
        subst a
        subst b
        change lower φ' (h (φ x)) = cell φ' (attachingInclusion k l x)
        rw [adjunction_coherence φ' x]
        exact congrArg (lower φ') (hφ x))

theorem adjunctionMap_lower {X : Type u} {Y : Type v} (φ : AttachingRegion k l → X)
    (φ' : AttachingRegion k l → Y) (h : X → Y) (hφ : ∀ a, h (φ a) = φ' a) (x : X) :
    adjunctionMap φ φ' h hφ (lower φ x) = lower φ' (h x) := by
  rfl

theorem adjunctionMap_cell {X : Type u} {Y : Type v} (φ : AttachingRegion k l → X)
    (φ' : AttachingRegion k l → Y) (h : X → Y) (hφ : ∀ a, h (φ a) = φ' a)
    (d : StandardHandle k l) :
    adjunctionMap φ φ' h hφ (cell φ d) = cell φ' d := by
  rfl

theorem adjunctionMap_id {X : Type u} (φ : AttachingRegion k l → X) :
    adjunctionMap φ φ id (fun _ => rfl) = id := by
  funext z
  rcases Quot.exists_rep z with ⟨s, rfl⟩
  cases s with
  | inl d =>
    rfl
  | inr x =>
    rfl

theorem adjunctionMap_comp {X : Type u} {Y : Type v} {Z : Type w} (φ : AttachingRegion k l → X)
    (φ' : AttachingRegion k l → Y) (φ'' : AttachingRegion k l → Z) (h : X → Y) (g : Y → Z)
    (hφ : ∀ a, h (φ a) = φ' a) (hφ' : ∀ a, g (φ' a) = φ'' a) :
    adjunctionMap φ' φ'' g hφ' ∘ adjunctionMap φ φ' h hφ =
    adjunctionMap φ φ'' (g ∘ h) (fun a => by
        change g (h (φ a)) = φ'' a
        rw [hφ a]
        exact hφ' a) := by
  funext z
  rcases Quot.exists_rep z with ⟨s, rfl⟩
  cases s with
  | inl d =>
    rfl
  | inr x =>
    rfl

theorem continuous_adjunctionMap {X : Type u} {Y : Type v} [TopologicalSpace X]
    [TopologicalSpace Y] (φ : AttachingRegion k l → X) (φ' : AttachingRegion k l → Y)
    (h : X → Y) (hφ : ∀ a, h (φ a) = φ' a) (hh : Continuous h) :
    Continuous (adjunctionMap φ φ' h hφ) := by
  have hrel : ∀ a b : StandardHandle k l ⊕ X,
      DifferentialGeometry.Topology.adjunctionRel (attachingInclusion k l) φ a b →
      Sum.elim (fun d : StandardHandle k l => cell φ' d) (fun x : X => lower φ' (h x)) a =
        Sum.elim (fun d : StandardHandle k l => cell φ' d) (fun x : X => lower φ' (h x)) b := by
    intro a b hab
    rcases hab with ⟨x, hx | hx⟩
    · rcases hx with ⟨ha, hb⟩
      subst a
      subst b
      change cell φ' (attachingInclusion k l x) = lower φ' (h (φ x))
      rw [adjunction_coherence φ' x]
      exact congrArg (lower φ') (hφ x).symm
    · rcases hx with ⟨hb, ha⟩
      subst a
      subst b
      change lower φ' (h (φ x)) = cell φ' (attachingInclusion k l x)
      rw [adjunction_coherence φ' x]
      exact congrArg (lower φ') (hφ x)
  exact continuous_quot_lift hrel (Continuous.sumElim (continuous_cell φ') ((continuous_lower φ').comp hh))

noncomputable def adjunctionCongr {X : Type u} {Y : Type v} [TopologicalSpace X]
    [TopologicalSpace Y] (φ : AttachingRegion k l → X) (φ' : AttachingRegion k l → Y)
    (h : X ≃ₜ Y) (hφ : ∀ a, h.toFun (φ a) = φ' a) :
    AdjunctionSpace k l φ ≃ₜ AdjunctionSpace k l φ' where
  toFun := adjunctionMap φ φ' h.toFun hφ
  invFun := adjunctionMap φ' φ h.symm.toFun (fun a => by
    rw [← hφ a]
    exact h.left_inv (φ a))
  left_inv := by
    intro z
    have hmain : adjunctionMap φ' φ h.symm.toFun
        (fun a => by
          rw [← hφ a]
          exact h.left_inv (φ a)) ∘
        adjunctionMap φ φ' h.toFun hφ = id := by
      calc
        adjunctionMap φ' φ h.symm.toFun
            (fun a => by
              rw [← hφ a]
              exact h.left_inv (φ a)) ∘
            adjunctionMap φ φ' h.toFun hφ =
            adjunctionMap φ φ (h.symm.toFun ∘ h.toFun)
              (fun a => by
                change h.symm.toFun (h.toFun (φ a)) = φ a
                exact h.left_inv (φ a)) :=
          adjunctionMap_comp φ φ' φ h.toFun h.symm.toFun hφ (fun a => by
            rw [← hφ a]
            exact h.left_inv (φ a))
        _ = adjunctionMap φ φ id (fun a => rfl) := by
          congr 1
          funext x
          exact h.left_inv x
        _ = id := adjunctionMap_id φ
    exact congrFun hmain z
  right_inv := by
    intro z
    have hmain : adjunctionMap φ φ' h.toFun hφ ∘
        adjunctionMap φ' φ h.symm.toFun
          (fun a => by
            rw [← hφ a]
            exact h.left_inv (φ a)) = id := by
      calc
        adjunctionMap φ φ' h.toFun hφ ∘
            adjunctionMap φ' φ h.symm.toFun
              (fun a => by
                rw [← hφ a]
                exact h.left_inv (φ a)) =
            adjunctionMap φ' φ' (h.toFun ∘ h.symm.toFun)
              (fun a => by
                change h.toFun (h.symm.toFun (φ' a)) = φ' a
                exact h.right_inv (φ' a)) :=
          adjunctionMap_comp φ' φ φ' h.symm.toFun h.toFun (fun a => by
            rw [← hφ a]
            exact h.left_inv (φ a)) hφ
        _ = adjunctionMap φ' φ' id (fun a => rfl) := by
          congr 1
          funext x
          exact h.right_inv x
        _ = id := adjunctionMap_id φ'
    exact congrFun hmain z
  continuous_toFun := continuous_adjunctionMap φ φ' h.toFun hφ h.continuous_toFun
  continuous_invFun := continuous_adjunctionMap φ' φ h.symm.toFun (fun a => by
    rw [← hφ a]
    exact h.left_inv (φ a)) h.symm.continuous_toFun

theorem adjunctionCongr_lower {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (φ : AttachingRegion k l → X) (φ' : AttachingRegion k l → Y) (h : X ≃ₜ Y)
    (hφ : ∀ a, h.toFun (φ a) = φ' a) (x : X) :
    adjunctionCongr φ φ' h hφ (lower φ x) = lower φ' (h.toFun x) := by
  exact adjunctionMap_lower φ φ' h.toFun hφ x

theorem adjunctionCongr_cell {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (φ : AttachingRegion k l → X) (φ' : AttachingRegion k l → Y) (h : X ≃ₜ Y)
    (hφ : ∀ a, h.toFun (φ a) = φ' a) (d : StandardHandle k l) :
    adjunctionCongr φ φ' h hφ (cell φ d) = cell φ' d := by
  exact adjunctionMap_cell φ φ' h.toFun hφ d

@[reducible]
noncomputable def adjunctionChartedSpace {X : Type u} {Y : Type v} [TopologicalSpace X]
    [TopologicalSpace Y] (φ : AttachingRegion k l → X) (h : AdjunctionSpace k l φ ≃ₜ Y)
    {H : Type w} [TopologicalSpace H] [ChartedSpace H Y] : ChartedSpace H (AdjunctionSpace k l φ) :=
  chartedSpaceOfHomeomorph h

theorem adjunctionIsManifold {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H) {X : Type u} {Y : Type v} [TopologicalSpace X]
    [TopologicalSpace Y] [ChartedSpace H Y] (φ : AttachingRegion k l → X)
    (h : AdjunctionSpace k l φ ≃ₜ Y) {n : WithTop ℕ∞} [IsManifold I n Y] :
    @IsManifold 𝕜 _ E _ _ H _ I n (AdjunctionSpace k l φ) _
      (adjunctionChartedSpace φ h) :=
  isManifoldOfHomeomorph I h

theorem contMDiff_adjunctionHomeomorph {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H) {X : Type u} {Y : Type v} [TopologicalSpace X]
    [TopologicalSpace Y] [ChartedSpace H Y] (φ : AttachingRegion k l → X)
    (h : AdjunctionSpace k l φ ≃ₜ Y) {n : WithTop ℕ∞} [IsManifold I n Y] :
    @ContMDiff 𝕜 _ E _ _ H _ I (AdjunctionSpace k l φ) _ (adjunctionChartedSpace φ h)
      E _ _ H _ I Y _ _ n h :=
  contMDiff_homeomorph_of_chartedSpaceOfHomeomorph h I n

theorem contMDiff_adjunctionHomeomorph_symm {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H) {X : Type u} {Y : Type v} [TopologicalSpace X]
    [TopologicalSpace Y] [ChartedSpace H Y] (φ : AttachingRegion k l → X)
    (h : AdjunctionSpace k l φ ≃ₜ Y) {n : WithTop ℕ∞} [IsManifold I n Y] :
    @ContMDiff 𝕜 _ E _ _ H _ I Y _ _ E _ _ H _ I (AdjunctionSpace k l φ) _
      (adjunctionChartedSpace φ h) n h.symm :=
  contMDiff_homeomorph_symm_of_chartedSpaceOfHomeomorph h I n

theorem contMDiff_lower_of_contMDiff {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H) {X : Type u} {Y : Type v} [TopologicalSpace X]
    [TopologicalSpace Y] [ChartedSpace H X] [ChartedSpace H Y] (φ : AttachingRegion k l → X)
    (h : AdjunctionSpace k l φ ≃ₜ Y) {n : WithTop ℕ∞} [IsManifold I n Y]
    (hf : @ContMDiff 𝕜 _ E _ _ H _ I X _ _ E _ _ H _ I Y _ _ n
      (fun x : X => h.toFun (lower φ x))) :
    @ContMDiff 𝕜 _ E _ _ H _ I X _ _ E _ _ H _ I (AdjunctionSpace k l φ) _
      (adjunctionChartedSpace φ h) n (lower φ) := by
  letI : ChartedSpace H (AdjunctionSpace k l φ) := adjunctionChartedSpace φ h
  letI : IsManifold I n (AdjunctionSpace k l φ) := adjunctionIsManifold I φ h
  have hsymm : @ContMDiff 𝕜 _ E _ _ H _ I Y _ _ E _ _ H _ I (AdjunctionSpace k l φ) _
      (adjunctionChartedSpace φ h) n h.symm :=
    contMDiff_adjunctionHomeomorph_symm I φ h
  have hcomp : @ContMDiff 𝕜 _ E _ _ H _ I X _ _ E _ _ H _ I (AdjunctionSpace k l φ) _
      (adjunctionChartedSpace φ h) n (fun x : X => h.symm.toFun (h.toFun (lower φ x))) :=
    hsymm.comp hf
  refine hcomp.congr ?_
  intro x
  exact (h.left_inv (lower φ x)).symm

theorem contMDiff_cell_of_contMDiff {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H) {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] [ChartedSpace H Y] (φ : AttachingRegion k l → X)
    (h : AdjunctionSpace k l φ ≃ₜ Y) {n : WithTop ℕ∞}
    [Fact (k = (k - 1) + 1)] [Fact (l = (l - 1) + 1)] [IsManifold I n Y]
    (hf : @ContMDiff ℝ _ (EuclideanSpace ℝ (Fin ((k - 1) + 1)) ×
        EuclideanSpace ℝ (Fin ((l - 1) + 1))) _ _
      (ModelProd (EuclideanHalfSpace ((k - 1) + 1)) (EuclideanHalfSpace ((l - 1) + 1))) _
      ((modelWithCornersEuclideanHalfSpace ((k - 1) + 1)).prod
        (modelWithCornersEuclideanHalfSpace ((l - 1) + 1)))
      (StandardHandle k l) _ (standardHandleChartedSpace k l)
      E _ _ H _ I Y _ _ n
      (fun d : StandardHandle k l => h.toFun (cell φ d))) :
    @ContMDiff ℝ _ (EuclideanSpace ℝ (Fin ((k - 1) + 1)) ×
        EuclideanSpace ℝ (Fin ((l - 1) + 1))) _ _
      (ModelProd (EuclideanHalfSpace ((k - 1) + 1)) (EuclideanHalfSpace ((l - 1) + 1))) _
      ((modelWithCornersEuclideanHalfSpace ((k - 1) + 1)).prod
        (modelWithCornersEuclideanHalfSpace ((l - 1) + 1)))
      (StandardHandle k l) _ (standardHandleChartedSpace k l)
      E _ _ H _ I (AdjunctionSpace k l φ) _ (adjunctionChartedSpace φ h)
      n (cell φ) := by
  letI : ChartedSpace (ModelProd (EuclideanHalfSpace ((k - 1) + 1))
      (EuclideanHalfSpace ((l - 1) + 1))) (StandardHandle k l) :=
    standardHandleChartedSpace k l
  letI : ChartedSpace H (AdjunctionSpace k l φ) := adjunctionChartedSpace φ h
  letI : IsManifold I n (AdjunctionSpace k l φ) := adjunctionIsManifold I φ h
  have hsymm : @ContMDiff ℝ _ E _ _ H _ I Y _ _ E _ _ H _ I (AdjunctionSpace k l φ) _
      (adjunctionChartedSpace φ h) n h.symm :=
    contMDiff_adjunctionHomeomorph_symm I φ h
  have hcomp : @ContMDiff ℝ _ (EuclideanSpace ℝ (Fin ((k - 1) + 1)) ×
        EuclideanSpace ℝ (Fin ((l - 1) + 1))) _ _
      (ModelProd (EuclideanHalfSpace ((k - 1) + 1)) (EuclideanHalfSpace ((l - 1) + 1))) _
      ((modelWithCornersEuclideanHalfSpace ((k - 1) + 1)).prod
        (modelWithCornersEuclideanHalfSpace ((l - 1) + 1)))
      (StandardHandle k l) _ (standardHandleChartedSpace k l)
      E _ _ H _ I (AdjunctionSpace k l φ) _ (adjunctionChartedSpace φ h)
      n (fun d : StandardHandle k l => h.symm.toFun (h.toFun (cell φ d))) :=
    hsymm.comp hf
  refine hcomp.congr ?_
  intro d
  exact (h.left_inv (cell φ d)).symm

end

end DifferentialGeometry.Topology.Handle
