import FailureOfSemipositiveMetricExtension.CaoFamilyAdapter
import FailureOfSemipositiveMetricExtension.ProjectiveDirectionProductTangent

/-! The generic projective-immersion field is filled by the actual blowdown,
four directions, and family projection. The joint derivative is related to the
already verified ambient derivative through the genuine factor tangent maps. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.CaoAdapter
noncomputable section
open Set Topology IsManifold
open scoped Manifold ContDiff

/-- Exact product decomposition of the actual ambient inclusion derivative. -/
theorem ambientDerivative_product (p : Total) :
    mfderiv 𝓘(ℂ,ChartCoord) ambientModel (fun q : Total => q.val) p =
      (mfderiv 𝓘(ℂ,ChartCoord) 𝓘(ℂ,ℂ × ℂ) blowdown p).prod
        ((mfderiv 𝓘(ℂ,ChartCoord) 𝓘(ℂ,ProjectiveDirectionProduct.Coord) directions p).prod
          (mfderiv 𝓘(ℂ,ChartCoord) 𝓘(ℂ) projection p)) := by
  have hb := ((blowdown_contMDiff 1) p).mdifferentiableAt le_rfl
  have hd := ((directions_contMDiff 1) p).mdifferentiableAt le_rfl
  have ht := ((projection_contMDiff 1) p).mdifferentiableAt le_rfl
  have h := hb.mfderiv_prod (hd.prodMk ht)
  rw [hd.mfderiv_prod ht] at h
  exact h

/-- Evaluation of the product tangent vector requires the actual derivative of
evaluation, not a choice-dependent identification with its raw coordinates. -/
theorem directionDerivative_component (p : Total) (r : Fin 4)
    (v : TangentSpace 𝓘(ℂ,ChartCoord) p) :
    ProjectiveDirectionProduct.componentDerivative (directions p)
      (mfderiv 𝓘(ℂ,ChartCoord) 𝓘(ℂ,ProjectiveDirectionProduct.Coord) directions p v) r =
        mfderiv 𝓘(ℂ,ChartCoord) 𝓘(ℂ) (fun q : Total => directions q r) p v := by
  exact (mfderiv_comp_apply p
    (((ProjectiveDirectionProduct.eval_contMDiff r 1) (directions p)).mdifferentiableAt le_rfl)
    (((directions_contMDiff 1) p).mdifferentiableAt le_rfl) v).symm

/-- The complete tuple-of-components identity, with the necessary product-to-
factor tangent conversion displayed explicitly. -/
theorem ambientDerivative_components (p : Total) (v : TangentSpace 𝓘(ℂ,ChartCoord) p) :
    let w := mfderiv 𝓘(ℂ,ChartCoord) ambientModel (fun q : Total => q.val) p v
    (w.1,ProjectiveDirectionProduct.componentDerivative (directions p) w.2.1,w.2.2) =
      (mfderiv 𝓘(ℂ,ChartCoord) 𝓘(ℂ,ℂ × ℂ) blowdown p v,
       (fun r => mfderiv 𝓘(ℂ,ChartCoord) 𝓘(ℂ) (fun q : Total => directions q r) p v),
       mfderiv 𝓘(ℂ,ChartCoord) 𝓘(ℂ) projection p v) := by
  rw [ambientDerivative_product]
  dsimp only [ContinuousLinearMap.prod_apply]
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · funext r
      exact directionDerivative_component p r v
    · rfl

theorem jointDerivative_injective (p : Total) : Function.Injective
    (fun v : TangentSpace 𝓘(ℂ,ChartCoord) p =>
      (mfderiv 𝓘(ℂ,ChartCoord) 𝓘(ℂ,ℂ × ℂ) blowdown p v,
       (fun r => mfderiv 𝓘(ℂ,ChartCoord) 𝓘(ℂ) (fun q : Total => directions q r) p v),
       mfderiv 𝓘(ℂ,ChartCoord) 𝓘(ℂ) projection p v)) := by
  intro v w hvw
  apply total_inclusion_mfderiv_injective p
  rw [ambientDerivative_product]
  change (mfderiv 𝓘(ℂ,ChartCoord) 𝓘(ℂ,ℂ × ℂ) blowdown p v,
    mfderiv 𝓘(ℂ,ChartCoord) 𝓘(ℂ,ProjectiveDirectionProduct.Coord) directions p v,
    mfderiv 𝓘(ℂ,ChartCoord) 𝓘(ℂ) projection p v) =
    (mfderiv 𝓘(ℂ,ChartCoord) 𝓘(ℂ,ℂ × ℂ) blowdown p w,
    mfderiv 𝓘(ℂ,ChartCoord) 𝓘(ℂ,ProjectiveDirectionProduct.Coord) directions p w,
    mfderiv 𝓘(ℂ,ChartCoord) 𝓘(ℂ) projection p w)
  apply Prod.ext
  · have hb := congrArg (fun z : (ℂ × ℂ) × (Fin 4 → ℂ) × ℂ => z.1) hvw
    exact hb
  · apply Prod.ext
    · apply ProjectiveDirectionProduct.componentDerivative_injective (directions p)
      funext r
      rw [directionDerivative_component,directionDerivative_component]
      exact congrArg (fun z => z.2.1 r) hvw
    · exact congrArg (fun z => z.2.2) hvw

/-- One actual P² map, four actual P¹ maps and the actual family parameter meet
every field of the review-only generic projective immersion criterion. -/
def immersion : CaoExtensionInterface.ProjectiveImmersion (M := Total) where
  planeCount := 1
  lineCount := 4
  plane _ := blowdown
  line r := fun p => directions p r
  affine := projection
  plane_analytic _ := blowdown_contMDiff ω
  line_analytic r := direction_contMDiff r ω
  affine_analytic := projection_contMDiff ω
  joint_tangent_injective p := by
    intro v w hvw
    apply jointDerivative_injective p
    exact Prod.ext (congrArg (fun z => z.1 0) hvw)
      (Prod.ext (congrArg (fun z => z.2.1) hvw) (congrArg (fun z => z.2.2) hvw))

@[simp] theorem immersion_plane (r : Fin 1) : immersion.plane r = blowdown := rfl
@[simp] theorem immersion_line (r : Fin 4) : immersion.line r = fun p => directions p r := rfl
@[simp] theorem immersion_affine : immersion.affine = projection := rfl

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.CaoAdapter
