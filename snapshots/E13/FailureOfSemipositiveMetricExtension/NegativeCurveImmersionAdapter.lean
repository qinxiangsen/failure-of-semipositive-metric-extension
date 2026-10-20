import FailureOfSemipositiveMetricExtension.NegativeCurveBundleAdapter
import FailureOfSemipositiveMetricExtension.FixedFiberAmbientImmersion
import FailureOfSemipositiveMetricExtension.ProjectiveDirectionProductTangent

/-! The negative-curve interface's projective immersion is the actual central
surface's original compact projective ambient inclusion. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.NegativeCurveAdapter
noncomputable section
open Set Topology IsManifold
open scoped Manifold ContDiff

abbrev surfaceDirections (p : GlobalIncidence.Fiber 0) := p.val.2

theorem surfaceDirections_contMDiff (n : WithTop ℕ∞) :
    ContMDiff 𝓘(ℂ,FixedFiber.Coord) 𝓘(ℂ,ProjectiveDirectionProduct.Coord) n surfaceDirections :=
  ProjectiveDirectionProduct.contMDiff_of_components _ n (fun r => FixedFiber.direction_contMDiff 0 r n)

theorem ambientDerivative_product (p : GlobalIncidence.Fiber 0) :
    mfderiv 𝓘(ℂ,FixedFiber.Coord) projectiveAmbientModel (fun q : GlobalIncidence.Fiber 0 => q.val) p =
      (mfderiv 𝓘(ℂ,FixedFiber.Coord) 𝓘(ℂ,ℂ × ℂ) (FixedFiber.blowdown 0) p).prod
        (mfderiv 𝓘(ℂ,FixedFiber.Coord) 𝓘(ℂ,ProjectiveDirectionProduct.Coord) surfaceDirections p) :=
  (((FixedFiber.blowdown_contMDiff 0 1) p).mdifferentiableAt le_rfl).mfderiv_prod
    (((surfaceDirections_contMDiff 1) p).mdifferentiableAt le_rfl)

theorem directionDerivative_component (p : GlobalIncidence.Fiber 0) (r : Fin 4)
    (v : TangentSpace 𝓘(ℂ,FixedFiber.Coord) p) :
    ProjectiveDirectionProduct.componentDerivative (surfaceDirections p)
      (mfderiv 𝓘(ℂ,FixedFiber.Coord) 𝓘(ℂ,ProjectiveDirectionProduct.Coord) surfaceDirections p v) r =
        mfderiv 𝓘(ℂ,FixedFiber.Coord) 𝓘(ℂ) (FixedFiber.direction 0 r) p v :=
  (mfderiv_comp_apply p
    (((ProjectiveDirectionProduct.eval_contMDiff r 1) (surfaceDirections p)).mdifferentiableAt le_rfl)
    (((surfaceDirections_contMDiff 1) p).mdifferentiableAt le_rfl) v).symm

theorem jointDerivative_injective (p : GlobalIncidence.Fiber 0) : Function.Injective
    (fun v : TangentSpace 𝓘(ℂ,FixedFiber.Coord) p =>
      (mfderiv 𝓘(ℂ,FixedFiber.Coord) 𝓘(ℂ,ℂ × ℂ) (FixedFiber.blowdown 0) p v,
       (fun r => mfderiv 𝓘(ℂ,FixedFiber.Coord) 𝓘(ℂ) (FixedFiber.direction 0 r) p v))) := by
  intro v w hvw
  apply FixedFiber.ambient_inclusion_mfderiv_injective 0 p
  rw [ambientDerivative_product]
  change (mfderiv 𝓘(ℂ,FixedFiber.Coord) 𝓘(ℂ,ℂ × ℂ) (FixedFiber.blowdown 0) p v,
    mfderiv 𝓘(ℂ,FixedFiber.Coord) 𝓘(ℂ,ProjectiveDirectionProduct.Coord) surfaceDirections p v) =
      (mfderiv 𝓘(ℂ,FixedFiber.Coord) 𝓘(ℂ,ℂ × ℂ) (FixedFiber.blowdown 0) p w,
       mfderiv 𝓘(ℂ,FixedFiber.Coord) 𝓘(ℂ,ProjectiveDirectionProduct.Coord) surfaceDirections p w)
  apply Prod.ext
  · have hb := congrArg (fun z : (ℂ × ℂ) × (Fin 4 → ℂ) => z.1) hvw
    exact hb
  · apply ProjectiveDirectionProduct.componentDerivative_injective (surfaceDirections p)
    funext r
    rw [directionDerivative_component,directionDerivative_component]
    exact congrArg (fun z => z.2 r) hvw

def immersion : FailureOfSemipositiveMetricExtension.NegativeCurveRemovalInterface.ProjectiveImmersion
    (M := GlobalIncidence.Fiber 0) where
  planeCount := 1
  lineCount := 4
  plane _ := FixedFiber.blowdown 0
  line r := FixedFiber.direction 0 r
  plane_analytic _ := FixedFiber.blowdown_contMDiff 0 ω
  line_analytic r := FixedFiber.direction_contMDiff 0 r ω
  joint_tangent_injective p := by
    intro v w hvw
    apply jointDerivative_injective p
    apply Prod.ext
    · exact congrArg (fun z : (Fin 1 → ℂ × ℂ) × (Fin 4 → ℂ) => z.1 0) hvw
    · exact congrArg (fun z : (Fin 1 → ℂ × ℂ) × (Fin 4 → ℂ) => z.2) hvw

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.NegativeCurveAdapter
