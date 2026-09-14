import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CGHSubsequenceClosure
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.WindowCompactnessProducer

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Filter
open DifferentialGeometry.CheegerGromovCompactness

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable [NeZero (Module.finrank Real E)]

structure FiniteArcInjectivityEstimates
    (X : FiniteArcFlowSeq.{u, uE, uH} (I := I)) where
  radius : Real
  radius_pos : 0 < radius
  bound : ∀ k : Nat, HasInjRadiusAt (I := I) ((X.term k).atTime (I := I) 0)
    ((X.term k).atTime (I := I) 0).basepoint radius

omit [I.Boundaryless] [NeZero (Module.finrank Real E)] in
theorem finiteArcEstimates_tail (X : FiniteArcFlowSeq.{u, uE, uH} (I := I))
    (hes : FiniteArcEstimates X) (N : Nat) : FiniteArcEstimates (X.tail N) where
  complete := fun k t ht => hes.complete (k + N) t ht
  curvature := fun A hA => by
    obtain ⟨C, hC, hb⟩ := hes.curvature A hA
    exact ⟨C, hC, fun k t ht x => hb (k + N) t ht x⟩
  connected := fun k => hes.connected (k + N)

noncomputable def finiteArcInjectivityEstimates_tail (X : FiniteArcFlowSeq.{u, uE, uH} (I := I))
    (h : FiniteArcInjectivityEstimates X) (N : Nat) :
    FiniteArcInjectivityEstimates (X.tail N) :=
  ⟨h.radius, h.radius_pos, fun k => h.bound (k + N)⟩

noncomputable def windowCompactnessEstimates_injectivity_of_finiteArcInjectivityEstimates
    (X : FiniteArcFlowSeq.{u, uE, uH} (I := I)) (h : FiniteArcInjectivityEstimates X)
    (A : Real) (hA : 0 < A) (hcov : ∀ k : Nat, A ≤ X.horizon k) :
    FlowScaleInjectivityBound (I := I) (X.window A hA hcov) :=
  ⟨h.radius, h.radius_pos, fun k => h.bound k⟩

noncomputable def finiteArcInjectivityEstimates_of_windowCompactnessEstimates_injectivity
    (X : FiniteArcFlowSeq.{u, uE, uH} (I := I)) (A : Real) (hA : 0 < A)
    (hcov : ∀ k : Nat, A ≤ X.horizon k)
    (h : FlowScaleInjectivityBound (I := I) (X.window A hA hcov)) :
    FiniteArcInjectivityEstimates X :=
  ⟨h.ρ, h.pos, fun k => h.bound k⟩

theorem nonempty_finiteArcInjectivityEstimates_iff_windowCompactnessEstimates_injectivity
    (X : FiniteArcFlowSeq.{u, uE, uH} (I := I)) (A : Real) (hA : 0 < A)
    (hcov : ∀ k : Nat, A ≤ X.horizon k) :
    Nonempty (FiniteArcInjectivityEstimates X) ↔
      Nonempty (FlowScaleInjectivityBound (I := I) (X.window A hA hcov)) :=
  ⟨fun h => ⟨windowCompactnessEstimates_injectivity_of_finiteArcInjectivityEstimates X
      h.some A hA hcov⟩,
    fun h => ⟨finiteArcInjectivityEstimates_of_windowCompactnessEstimates_injectivity X
      A hA hcov h.some⟩⟩

noncomputable def finiteArcInjectivityEstimates_of_flowInjOfVol
    (X : FiniteArcFlowSeq.{u, uE, uH} (I := I)) (A : Real) (hA : 0 < A)
    (hcov : ∀ k : Nat, A ≤ X.horizon k)
    (hcomplete : SeqMetricComplete (I := I) ((X.window A hA hcov).atZero (I := I)))
    (hconn : ∀ i : Nat,
      letI : TopologicalSpace (((X.window A hA hcov).atZero (I := I)).obj i).M :=
        (((X.window A hA hcov).atZero (I := I)).obj i).topology
      ConnectedSpace (((X.window A hA hcov).atZero (I := I)).obj i).M)
    (hgeom : SeqBoundedGeometry (I := I) ((X.window A hA hcov).atZero (I := I)))
    (V : FlowNoncollapsingScale (I := I) (X.window A hA hcov))
    (hvol : IsFlowNoncollapsingScaleBound (I := I) V) :
    FiniteArcInjectivityEstimates X :=
  finiteArcInjectivityEstimates_of_windowCompactnessEstimates_injectivity X A hA hcov
    (flowInjOfVol (I := I) (X.window A hA hcov) hcomplete hconn hgeom V hvol)

noncomputable def windowCompactnessEstimates_of_finiteArcEstimates
    (X : FiniteArcFlowSeq.{u, uE, uH} (I := I)) (hes : FiniteArcEstimates X)
    (hinj : FiniteArcInjectivityEstimates X) (A : Real) (hA : 0 < A)
    (hcov : ∀ k : Nat, A ≤ X.horizon k) :
    WindowCompactnessEstimates X A hA hcov where
  complete := windowCompactnessEstimates_complete_of_finiteArcEstimates X hes A hA hcov
  curvature := windowCompactnessEstimates_curvature_of_finiteArcEstimates X hes A hA hcov
  injectivity :=
    windowCompactnessEstimates_injectivity_of_finiteArcInjectivityEstimates X hinj A hA hcov
  connected := windowCompactnessEstimates_connected_of_finiteArcEstimates X hes A hA hcov

structure WindowCompactnessFrontier (X : FiniteArcFlowSeq.{u, uE, uH} (I := I))
    (hT : Tendsto X.horizon atTop atTop) : Prop where
  compact : ∀ (m : Nat) (φ : Nat → Nat), StrictMono φ →
    WindowCompactnessEstimates (X.tail (X.windowShift hT m)) (windowHorizon m)
      (windowHorizon_pos m) (fun k => X.le_horizon_add_windowShift hT m k) →
    ∃ ψ : Nat → Nat, StrictMono ψ ∧ X.WindowConverges hT m (φ ∘ ψ)

theorem windowCompactnessFrontier_of_finiteArcWindowCompactnessInput
    (X : FiniteArcFlowSeq.{u, uE, uH} (I := I))
    (hT : Tendsto X.horizon atTop atTop) (h : FiniteArcWindowCompactnessInput X hT) :
    WindowCompactnessFrontier X hT where
  compact := fun m φ hφ _ => h m φ hφ

noncomputable def windowCompactnessEstimates_window_of_finiteArcEstimates
    (X : FiniteArcFlowSeq.{u, uE, uH} (I := I))
    (hT : Tendsto X.horizon atTop atTop) (hes : FiniteArcEstimates X)
    (hinj : FiniteArcInjectivityEstimates X) (m : Nat) :
    WindowCompactnessEstimates (X.tail (X.windowShift hT m)) (windowHorizon m)
      (windowHorizon_pos m) (fun k => X.le_horizon_add_windowShift hT m k) :=
  windowCompactnessEstimates_of_finiteArcEstimates (X.tail (X.windowShift hT m))
    (finiteArcEstimates_tail X hes (X.windowShift hT m))
    (finiteArcInjectivityEstimates_tail X hinj (X.windowShift hT m))
    (windowHorizon m) (windowHorizon_pos m) (fun k => X.le_horizon_add_windowShift hT m k)

theorem finiteArcWindowCompactnessInput_of_windowCompactnessEstimates
    (X : FiniteArcFlowSeq.{u, uE, uH} (I := I))
    (hT : Tendsto X.horizon atTop atTop) (hfrontier : WindowCompactnessFrontier X hT)
    (hest : ∀ m : Nat, WindowCompactnessEstimates (X.tail (X.windowShift hT m))
      (windowHorizon m) (windowHorizon_pos m)
      (fun k => X.le_horizon_add_windowShift hT m k)) :
    FiniteArcWindowCompactnessInput X hT :=
  fun m φ hφ => hfrontier.compact m φ hφ (hest m)

theorem finiteArcWindowCompactnessInput_of_finiteArcEstimates
    (X : FiniteArcFlowSeq.{u, uE, uH} (I := I))
    (hT : Tendsto X.horizon atTop atTop) (hfrontier : WindowCompactnessFrontier X hT)
    (hes : FiniteArcEstimates X) (hinj : FiniteArcInjectivityEstimates X) :
    FiniteArcWindowCompactnessInput X hT :=
  finiteArcWindowCompactnessInput_of_windowCompactnessEstimates X hT hfrontier
    (fun m => windowCompactnessEstimates_window_of_finiteArcEstimates X hT hes hinj m)

theorem exists_strictMono_forall_shift_windowConverges_of_finiteArcEstimates
    (X : FiniteArcFlowSeq.{u, uE, uH} (I := I))
    (hT : Tendsto X.horizon atTop atTop) (hfrontier : WindowCompactnessFrontier X hT)
    (hes : FiniteArcEstimates X) (hinj : FiniteArcInjectivityEstimates X) :
    ∃ φ : Nat → Nat, StrictMono φ ∧
      ∀ m : Nat, X.WindowConverges hT m (fun k => φ (m + k)) :=
  exists_strictMono_forall_shift_windowConverges X hT
    (finiteArcWindowCompactnessInput_of_finiteArcEstimates X hT hfrontier hes hinj)
    (fun _ _ ψ _ hψ hconv => ⟨(Classical.choice hconv).compSubseq ψ hψ⟩)

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
