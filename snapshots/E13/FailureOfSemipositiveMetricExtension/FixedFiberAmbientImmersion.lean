import FailureOfSemipositiveMetricExtension.GlobalAmbientImmersion
import FailureOfSemipositiveMetricExtension.FiberTangentAdjunction

/-! Every actual fixed fibre is a compact analytic surface embedded with
injective tangent map in the original compact product P² × (P¹)^4. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence
noncomputable section
open Set Topology IsManifold
open scoped Manifold ContDiff

abbrev ProjectiveAmbient := PlanePoint × (Fin 4 → Direction)
abbrev projectiveAmbientModel := 𝓘(ℂ,ℂ × ℂ).prod 𝓘(ℂ,ProjectiveDirectionProduct.Coord)

/-- Insert a fixed family parameter in the actual projective ambient product. -/
def ambientInsertParameter (t : ℂ) (p : ProjectiveAmbient) : Ambient := (p.1,p.2,t)

theorem ambientInsertParameter_contMDiff (t : ℂ) (n : WithTop ℕ∞) :
    ContMDiff projectiveAmbientModel ambientModel n (ambientInsertParameter t) :=
  contMDiff_fst.prodMk (contMDiff_snd.prodMk contMDiff_const)

namespace FixedFiber

theorem ambient_inclusion_contMDiff (t : ℂ) (n : WithTop ℕ∞) :
    ContMDiff 𝓘(ℂ,Coord) projectiveAmbientModel n (fun p : Fiber t => p.val) := by
  have hd : ContMDiff 𝓘(ℂ,Coord) 𝓘(ℂ,ProjectiveDirectionProduct.Coord) n
      (fun p : Fiber t => p.val.2) :=
    ProjectiveDirectionProduct.contMDiff_of_components _ n (fun r => direction_contMDiff t r n)
  exact (blowdown_contMDiff t n).prodMk hd

theorem ambient_inclusion_isClosedEmbedding (t : ℂ) :
    IsClosedEmbedding (fun p : Fiber t => p.val) :=
  (fiberLocus_isClosed t).isClosedEmbedding_subtypeVal

/-- Forgetting the fixed parameter still gives an injective actual tangent map:
the total ambient inclusion factors through this projective ambient inclusion. -/
theorem ambient_inclusion_mfderiv_injective (t : ℂ) (p : Fiber t) :
    Function.Injective (mfderiv 𝓘(ℂ,Coord) projectiveAmbientModel
      (fun q : Fiber t => q.val) p) := by
  have hi := ((inclusion_contMDiff t 1) p).mdifferentiableAt le_rfl
  have hg := ((total_inclusion_contMDiff 1) (inclusion t p)).mdifferentiableAt le_rfl
  have hj := ((ambient_inclusion_contMDiff t 1) p).mdifferentiableAt le_rfl
  have ha := ((ambientInsertParameter_contMDiff t 1) p.val).mdifferentiableAt le_rfl
  have hcomp : Function.Injective (mfderiv 𝓘(ℂ,Coord) ambientModel
      ((fun q : Total => q.val) ∘ inclusion t) p) := by
    rw [mfderiv_comp p hg hi]
    exact (total_inclusion_mfderiv_injective (inclusion t p)).comp
      (GlobalCanonical.inclusion_mfderiv_injective t p)
  have he : (fun q : Total => q.val) ∘ inclusion t =
      ambientInsertParameter t ∘ (fun q : Fiber t => q.val) := rfl
  rw [he,mfderiv_comp p ha hj] at hcomp
  change Function.Injective
    ((mfderiv projectiveAmbientModel ambientModel (ambientInsertParameter t) p.val) ∘
      (mfderiv 𝓘(ℂ,Coord) projectiveAmbientModel (fun q : Fiber t => q.val) p)) at hcomp
  exact hcomp.of_comp

/-- Compactness and analytic closed immersion in a compact projective ambient
space hold for all parameters, including the central one. -/
theorem compact_analytic_projective_embedding (t : ℂ) :
    CompactSpace (Fiber t) ∧ CompactSpace ProjectiveAmbient ∧
      IsManifold 𝓘(ℂ,Coord) ω (Fiber t) ∧
      IsManifold projectiveAmbientModel ω ProjectiveAmbient ∧
      IsClosedEmbedding (fun p : Fiber t => p.val) ∧
      ContMDiff 𝓘(ℂ,Coord) projectiveAmbientModel ω (fun p : Fiber t => p.val) ∧
      ∀ p : Fiber t, Function.Injective (mfderiv 𝓘(ℂ,Coord) projectiveAmbientModel
        (fun q : Fiber t => q.val) p) :=
  ⟨inferInstance,inferInstance,inferInstance,inferInstance,
    ambient_inclusion_isClosedEmbedding t,ambient_inclusion_contMDiff t ω,
    ambient_inclusion_mfderiv_injective t⟩

end FixedFiber
end
end FailureOfSemipositiveMetricExtension.GlobalIncidence
