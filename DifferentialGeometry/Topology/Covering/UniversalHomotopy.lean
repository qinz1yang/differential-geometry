import DifferentialGeometry.Topology.Covering.UniversalMap

noncomputable section

open scoped unitInterval

namespace DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [LocallyPathConnectedSpace Y] [SemilocallySimplyConnectedSpace Y]
  {f g : C(X, Y)}

def mapHomotopy (H : f.Homotopy g) (x₀ : X) :
    C(I × @UniversalCover X _ ⟨x₀⟩, @UniversalCover Y _ ⟨f x₀⟩) := by
  letI : Inhabited X := ⟨x₀⟩
  letI : Inhabited Y := ⟨f x₀⟩
  exact (@proj_isCoveringMap Y _ ⟨f x₀⟩ _ _).liftHomotopy
    (H.toContinuousMap.comp ((ContinuousMap.id I).prodMap
      ⟨@proj X _ ⟨x₀⟩, proj_continuous⟩))
    (map f x₀) (fun p => H.apply_zero p.1)

@[simp]
theorem proj_mapHomotopy (H : f.Homotopy g) (x₀ : X)
    (t : I) (p : @UniversalCover X _ ⟨x₀⟩) :
    @proj Y _ ⟨f x₀⟩ (mapHomotopy H x₀ (t, p)) = H (t, @proj X _ ⟨x₀⟩ p) := by
  exact congrFun ((@proj_isCoveringMap Y _ ⟨f x₀⟩ _ _).liftHomotopy_lifts _ _ _) (t, p)

@[simp]
theorem mapHomotopy_zero (H : f.Homotopy g) (x₀ : X)
    (p : @UniversalCover X _ ⟨x₀⟩) : mapHomotopy H x₀ (0, p) = map f x₀ p :=
  (@proj_isCoveringMap Y _ ⟨f x₀⟩ _ _).liftHomotopy_zero _ _ _ p

theorem mapHomotopy_smul (H : f.Homotopy g) (x₀ : X)
    (a : FundamentalGroup X x₀) (t : I) (p : @UniversalCover X _ ⟨x₀⟩) :
    letI : Inhabited X := ⟨x₀⟩
    letI : Inhabited Y := ⟨f x₀⟩
    letI : MulAction (FundamentalGroup X x₀) (@UniversalCover X _ ⟨x₀⟩) :=
      @deckMulAction X _ ⟨x₀⟩
    letI : MulAction (FundamentalGroup Y (f x₀)) (@UniversalCover Y _ ⟨f x₀⟩) :=
      @deckMulAction Y _ ⟨f x₀⟩
    mapHomotopy H x₀ (t, a • p) =
      FundamentalGroup.map f x₀ a • mapHomotopy H x₀ (t, p) := by
  change mapHomotopy H x₀ (t, @deckAct X _ ⟨x₀⟩ a p) =
    @deckAct Y _ ⟨f x₀⟩ (FundamentalGroup.map f x₀ a) (mapHomotopy H x₀ (t, p))
  have h := (@proj_isCoveringMap Y _ ⟨f x₀⟩ _ _).eq_of_comp_eq
    ((mapHomotopy H x₀).continuous.comp
      (Continuous.prodMk_left (@deckAct X _ ⟨x₀⟩ a p)))
    ((@loopShift_cont Y _ ⟨f x₀⟩ _
      (FundamentalGroup.toPath (FundamentalGroup.map f x₀ a)⁻¹)).comp
      ((mapHomotopy H x₀).continuous.comp (Continuous.prodMk_left p)))
    (by
      funext s
      change @proj Y _ ⟨f x₀⟩ (mapHomotopy H x₀ (s, @deckAct X _ ⟨x₀⟩ a p)) =
        @proj Y _ ⟨f x₀⟩
          (@deckAct Y _ ⟨f x₀⟩ (FundamentalGroup.map f x₀ a) (mapHomotopy H x₀ (s, p)))
      rw [proj_mapHomotopy]
      change H (s, (@deckAct X _ ⟨x₀⟩ a p).1) =
        @proj Y _ ⟨f x₀⟩
          (@deckAct Y _ ⟨f x₀⟩ (FundamentalGroup.map f x₀ a)
            (mapHomotopy H x₀ (s, p)))
      rw [show (@deckAct X _ ⟨x₀⟩ a p).1 = p.1 from rfl]
      rw [show @proj Y _ ⟨f x₀⟩
          (@deckAct Y _ ⟨f x₀⟩ (FundamentalGroup.map f x₀ a)
            (mapHomotopy H x₀ (s, p))) =
          @proj Y _ ⟨f x₀⟩ (mapHomotopy H x₀ (s, p)) from rfl]
      exact (proj_mapHomotopy H x₀ s p).symm)
    0 (by
      simp only [Function.comp_apply]
      change mapHomotopy H x₀ (0, @deckAct X _ ⟨x₀⟩ a p) =
        @deckAct Y _ ⟨f x₀⟩ (FundamentalGroup.map f x₀ a)
          (mapHomotopy H x₀ (0, p))
      rw [mapHomotopy_zero, mapHomotopy_zero]
      exact map_smul f x₀ a p)
  exact congrFun h t

def mapHomotopyEndpoint (H : f.Homotopy g) (x₀ : X) :
    C(@UniversalCover X _ ⟨x₀⟩, @UniversalCover Y _ ⟨f x₀⟩) :=
  (mapHomotopy H x₀).comp ⟨fun p => (1, p), by fun_prop⟩

@[simp]
theorem proj_mapHomotopyEndpoint (H : f.Homotopy g) (x₀ : X)
    (p : @UniversalCover X _ ⟨x₀⟩) :
    @proj Y _ ⟨f x₀⟩ (mapHomotopyEndpoint H x₀ p) = g (@proj X _ ⟨x₀⟩ p) := by
  change @proj Y _ ⟨f x₀⟩ (mapHomotopy H x₀ (1, p)) = g (@proj X _ ⟨x₀⟩ p)
  rw [proj_mapHomotopy, H.apply_one]

def mapHomotopyLift (H : f.Homotopy g) (x₀ : X) :
    (map f x₀).Homotopy (mapHomotopyEndpoint H x₀) where
  toContinuousMap := mapHomotopy H x₀
  map_zero_left := mapHomotopy_zero H x₀
  map_one_left _ := rfl

theorem mapHomotopy_basePoint (H : f.Homotopy g) (x₀ : X) (t : I) :
    mapHomotopy H x₀ (t, @basePoint X _ ⟨x₀⟩) =
      (@proj_isCoveringMap Y _ ⟨f x₀⟩ _ _).liftPath (H.evalAt x₀)
        (@basePoint Y _ ⟨f x₀⟩) (H.evalAt x₀).source t := by
  have h : (fun s => mapHomotopy H x₀ (s, @basePoint X _ ⟨x₀⟩)) =
      (@proj_isCoveringMap Y _ ⟨f x₀⟩ _ _).liftPath (H.evalAt x₀)
        (@basePoint Y _ ⟨f x₀⟩) (H.evalAt x₀).source := by
    apply ((@proj_isCoveringMap Y _ ⟨f x₀⟩ _ _).eq_liftPath_iff _).mpr
    refine ⟨(mapHomotopy H x₀).continuous.comp
      (Continuous.prodMk_left (@basePoint X _ ⟨x₀⟩)), ?_, ?_⟩
    · funext s
      exact proj_mapHomotopy H x₀ s (@basePoint X _ ⟨x₀⟩)
    · simp only [mapHomotopy_zero, map_basePoint]
  exact congrFun h t

theorem mapHomotopyEndpoint_smul (H : f.Homotopy g) (x₀ : X)
    (a : FundamentalGroup X x₀) (p : @UniversalCover X _ ⟨x₀⟩) :
    letI : Inhabited X := ⟨x₀⟩
    letI : Inhabited Y := ⟨f x₀⟩
    letI : MulAction (FundamentalGroup X x₀) (@UniversalCover X _ ⟨x₀⟩) :=
      @deckMulAction X _ ⟨x₀⟩
    letI : MulAction (FundamentalGroup Y (f x₀)) (@UniversalCover Y _ ⟨f x₀⟩) :=
      @deckMulAction Y _ ⟨f x₀⟩
    mapHomotopyEndpoint H x₀ (a • p) =
      FundamentalGroup.map f x₀ a • mapHomotopyEndpoint H x₀ p :=
  mapHomotopy_smul H x₀ a 1 p

end DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover
