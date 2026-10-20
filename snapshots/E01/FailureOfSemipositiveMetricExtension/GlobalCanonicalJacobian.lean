import FailureOfSemipositiveMetricExtension.ComplexThreefoldJacobian
import FailureOfSemipositiveMetricExtension.FixedFiberCanonicalTangentForms

/-! Threefold chart Jacobians and their actual fixed-fibre restrictions.
The family coordinate is preserved, so the full Jacobian equals the vertical
Jacobian with the ordered coordinates (z₁,z₂,t). -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.GlobalCanonical
noncomputable section
open Set Topology
open scoped Manifold ContDiff

def change (i j : Fin 4) (e f : Fin 2) : ChartCoord → ChartCoord :=
  chartCoordinates j f ∘ chartParam i e

def changeDomain (i j : Fin 4) (e f : Fin 2) : Set ChartCoord :=
  ((homeomorphChart i e).symm.trans (homeomorphChart j f)).source

theorem changeDomain_isOpen (i j : Fin 4) (e f : Fin 2) :
    IsOpen (changeDomain i j e f) := ((homeomorphChart i e).symm.trans (homeomorphChart j f)).open_source

theorem change_contDiffOn (i j : Fin 4) (e f : Fin 2) (n : WithTop ℕ∞) :
    ContDiffOn ℂ n (change i j e f) (changeDomain i j e f) :=
  GlobalIncidence.transition_contDiffOn i j e f n

theorem change_differentiableAt (i j : Fin 4) (e f : Fin 2) (q : ChartCoord)
    (hq : q ∈ changeDomain i j e f) : DifferentiableAt ℂ (change i j e f) q :=
  ((change_contDiffOn i j e f 1).contDiffAt ((changeDomain_isOpen i j e f).mem_nhds hq)).differentiableAt (by norm_num)

theorem change_parameter (i j : Fin 4) (e f : Fin 2) (q : ChartCoord)
    (hq : q ∈ changeDomain i j e f) : (change i j e f q).2 = q.2 := by
  change (chartCoordinates j f (chartParam i e q)).2 = _
  have hp : chartParam i e q ∈ chartSource j f := hq.2
  rw [chartCoordinates_eq_explicit j f (chartParam i e q) hp]
  rfl

/-- The actual derivative fixes the family-coordinate covector. -/
theorem change_derivative_parameter (i j : Fin 4) (e f : Fin 2) (q : ChartCoord)
    (hq : q ∈ changeDomain i j e f) (v : ChartCoord) :
    ((fderiv ℂ (change i j e f) q) v).2 = v.2 := by
  have he : (fun w => (change i j e f w).2) =ᶠ[𝓝 q] (fun w : ChartCoord => w.2) := by
    filter_upwards [(changeDomain_isOpen i j e f).mem_nhds hq] with w hw
    exact change_parameter i j e f w hw
  have hd := (change_differentiableAt i j e f q hq).hasFDerivAt.snd
  have hs : HasFDerivAt (fun w : ChartCoord => w.2) (ContinuousLinearMap.snd ℂ (ℂ × ℂ) ℂ) q := hasFDerivAt_snd
  have hh := (hd.congr_of_eventuallyEq he.symm).unique hs
  exact congrArg (fun A => A v) hh

/-- Restricting the genuine threefold change to a fixed parameter is exactly the
already constructed actual surface change. -/
theorem change_vertical (t : ℂ) (i j : Fin 4) (e f : Fin 2) (q : FixedFiber.Coord) :
    (change i j e f (q,t)).1 = FixedFiber.change t i j e f q := rfl

theorem change_vertical_derivative (t : ℂ) (i j : Fin 4) (e f : Fin 2) (q : FixedFiber.Coord)
    (hq : (q,t) ∈ changeDomain i j e f) :
    fderiv ℂ (FixedFiber.change t i j e f) q =
      (ContinuousLinearMap.fst ℂ (ℂ × ℂ) ℂ).comp
        ((fderiv ℂ (change i j e f) (q,t)).comp (ContinuousLinearMap.inl ℂ (ℂ × ℂ) ℂ)) := by
  have hi : HasFDerivAt (fun w : FixedFiber.Coord => (w,t))
      (ContinuousLinearMap.inl ℂ (ℂ × ℂ) ℂ) q :=
    (hasFDerivAt_id q).prodMk (hasFDerivAt_const t q)
  have hc := ((change_differentiableAt i j e f (q,t) hq).hasFDerivAt.comp q hi).fst
  exact hc.fderiv

/-- The exact determinant equality behind restriction/adjunction by dt. -/
theorem change_jacobian_eq_fiber (t : ℂ) (i j : Fin 4) (e f : Fin 2) (q : FixedFiber.Coord)
    (hq : (q,t) ∈ changeDomain i j e f) :
    ComplexThreefoldJacobian.jacobian (change i j e f) (q,t) =
      ComplexSurfaceJacobian.jacobian (FixedFiber.change t i j e f) q := by
  unfold ComplexThreefoldJacobian.jacobian ComplexSurfaceJacobian.jacobian
  rw [ComplexThreefoldJacobian.determinant_parameter_preserving _
    (change_derivative_parameter i j e f (q,t) hq),change_vertical_derivative t i j e f q hq]

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.GlobalCanonical
