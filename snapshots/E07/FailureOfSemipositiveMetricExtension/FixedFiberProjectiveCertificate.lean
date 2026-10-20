import FailureOfSemipositiveMetricExtension.FixedFiberBlowdownComplement
import FailureOfSemipositiveMetricExtension.GlobalAmbientImmersion

/-! Concrete fixed-fibre hypotheses for the standard Segre/Chow and rationality
comparison. The codomain is the ACTUAL projective product P² × (P¹)^4, not the
noncompact total ambient product with the parameter line. No algebraization,
GAGA or paper-specific conclusion is postulated here. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiber
noncomputable section
open Set Topology IsManifold
open scoped Manifold ContDiff

abbrev ProjectiveAmbient := PlanePoint × (Fin 4 → Direction)
abbrev projectiveAmbientModel := 𝓘(ℂ,ℂ × ℂ).prod 𝓘(ℂ,ProjectiveDirectionProduct.Coord)

def projectiveInclusion (t : ℂ) : Fiber t → ProjectiveAmbient := Subtype.val

theorem projectiveInclusion_isClosedEmbedding (t : ℂ) :
    IsClosedEmbedding (projectiveInclusion t) :=
  (fiberLocus_isClosed t).isClosedEmbedding_subtypeVal

theorem projectiveInclusion_contMDiff (t : ℂ) (n : WithTop ℕ∞) :
    ContMDiff 𝓘(ℂ,Coord) projectiveAmbientModel n (projectiveInclusion t) :=
  (blowdown_contMDiff t n).prodMk
    (ProjectiveDirectionProduct.contMDiff_of_components _ n (fun r => direction_contMDiff t r n))

def projectiveInsertParameter (t : ℂ) (q : ProjectiveAmbient) : Ambient := (q.1,q.2,t)

theorem projectiveInsertParameter_contMDiff (t : ℂ) (n : WithTop ℕ∞) :
    ContMDiff projectiveAmbientModel ambientModel n (projectiveInsertParameter t) :=
  contMDiff_fst.prodMk (contMDiff_snd.prodMk contMDiff_const)

def projectiveAmbientCoordinates (t : ℂ) (r : Fin 4) (e : Fin 2)
    (q : ProjectiveAmbient) : Coord :=
  (ambientCoordinates r e (projectiveInsertParameter t q)).1

@[simp] theorem projectiveAmbientCoordinates_inclusion (t : ℂ) (r : Fin 4) (e : Fin 2)
    (p : Fiber t) (hp : p ∈ source t r e) :
    projectiveAmbientCoordinates t r e (projectiveInclusion t p) = coordinates t r e p := by
  change (ambientCoordinates r e (inclusion t p).val).1 = _
  rw [ambientCoordinates_chartSource r e (inclusion t p) hp]
  rfl

theorem projectiveAmbientCoordinates_contMDiffAt (t : ℂ) (r : Fin 4) (e : Fin 2)
    (n : WithTop ℕ∞) (p : Fiber t) (hp : p ∈ source t r e) :
    ContMDiffAt projectiveAmbientModel 𝓘(ℂ,Coord) n
      (projectiveAmbientCoordinates t r e) (projectiveInclusion t p) := by
  have hb := ((mem_chartSource_iff r e (inclusion t p)).mp hp).1
  have hd := ((mem_chartSource_iff r e (inclusion t p)).mp hp).2.1
  have h := (ambientCoordinates_contMDiffAt r e n (inclusion t p).val hb hd).comp
    (projectiveInclusion t p) (projectiveInsertParameter_contMDiff t n).contMDiffAt
  exact (contDiff_fst.contMDiff.contMDiffAt :
    ContMDiffAt 𝓘(ℂ,ChartCoord) 𝓘(ℂ,Coord) n Prod.fst _).comp _ h

def projectiveRetraction (t : ℂ) (r : Fin 4) (e : Fin 2) : ProjectiveAmbient → Fiber t :=
  param t r e ∘ projectiveAmbientCoordinates t r e

theorem projectiveRetraction_contMDiffAt (t : ℂ) (r : Fin 4) (e : Fin 2)
    (n : WithTop ℕ∞) (p : Fiber t) (hp : p ∈ source t r e) :
    ContMDiffAt projectiveAmbientModel 𝓘(ℂ,Coord) n
      (projectiveRetraction t r e) (projectiveInclusion t p) := by
  have hq : projectiveAmbientCoordinates t r e (projectiveInclusion t p) ∈ domain t r e := by
    rw [projectiveAmbientCoordinates_inclusion t r e p hp]
    exact (chart t r e).map_source hp
  exact ((param_contMDiffOn t r e n).contMDiffAt ((domain_isOpen t r e).mem_nhds hq)).comp
    _ (projectiveAmbientCoordinates_contMDiffAt t r e n p hp)

theorem projectiveRetraction_inclusion_eventuallyEq (t : ℂ) (r : Fin 4) (e : Fin 2)
    (p : Fiber t) (hp : p ∈ source t r e) :
    projectiveRetraction t r e ∘ projectiveInclusion t =ᶠ[𝓝 p] id := by
  filter_upwards [(source_isOpen t r e).mem_nhds hp] with q hq
  change param t r e (projectiveAmbientCoordinates t r e (projectiveInclusion t q)) = q
  rw [projectiveAmbientCoordinates_inclusion t r e q hq]
  exact param_coordinates t r e q hq

/-- A genuine complex-linear tangent left inverse, including exceptional points. -/
theorem projectiveInclusion_mfderiv_leftInverse (t : ℂ) (p : Fiber t) :
    ∃ L : TangentSpace projectiveAmbientModel (projectiveInclusion t p) →L[ℂ]
        TangentSpace 𝓘(ℂ,Coord) p,
      L.comp (mfderiv 𝓘(ℂ,Coord) projectiveAmbientModel (projectiveInclusion t) p) =
        ContinuousLinearMap.id ℂ (TangentSpace 𝓘(ℂ,Coord) p) := by
  obtain ⟨⟨r,e⟩,hp⟩ := charts_cover t p
  refine ⟨mfderiv projectiveAmbientModel 𝓘(ℂ,Coord)
    (projectiveRetraction t r e) (projectiveInclusion t p),?_⟩
  have heq := (projectiveRetraction_inclusion_eventuallyEq t r e p hp).mfderiv_eq
    (I := 𝓘(ℂ,Coord)) (I' := 𝓘(ℂ,Coord))
  apply ContinuousLinearMap.ext
  intro v
  have hc := mfderiv_comp_apply p
    ((projectiveRetraction_contMDiffAt t r e 1 p hp).mdifferentiableAt le_rfl)
    (((projectiveInclusion_contMDiff t 1) p).mdifferentiableAt le_rfl) v
  rw [heq,mfderiv_id] at hc
  exact hc.symm

theorem projectiveInclusion_mfderiv_injective (t : ℂ) (p : Fiber t) :
    Function.Injective (mfderiv 𝓘(ℂ,Coord) projectiveAmbientModel (projectiveInclusion t) p) := by
  obtain ⟨L,hL⟩ := projectiveInclusion_mfderiv_leftInverse t p
  have hl : Function.LeftInverse L
      (mfderiv 𝓘(ℂ,Coord) projectiveAmbientModel (projectiveInclusion t) p) :=
    fun v => congrArg (fun T => T v) hL
  exact hl.injective

/-- Every actual compact fibre embeds as a smooth closed complex submanifold
of the fixed projective product. Standard Segre and Chow may now be invoked
externally, with their concrete embedding hypotheses discharged. -/
theorem actual_fiber_projective_closed_immersion (t : ℂ) :
    IsClosedEmbedding (projectiveInclusion t) ∧
      ContMDiff 𝓘(ℂ,Coord) projectiveAmbientModel ω (projectiveInclusion t) ∧
      ∀ p : Fiber t, Function.Injective
        (mfderiv 𝓘(ℂ,Coord) projectiveAmbientModel (projectiveInclusion t) p) :=
  ⟨projectiveInclusion_isClosedEmbedding t,projectiveInclusion_contMDiff t ω,
    projectiveInclusion_mfderiv_injective t⟩

/-- All concrete geometric inputs to the standard projective rational-surface
interpretation, in one certificate for the SAME original fixed fibre. The
algebraic realization and GAGA conclusion are deliberately not redefined here. -/
theorem actual_fiber_projective_rational_input_certificate (t : ℂ) :
    CompactSpace (Fiber t) ∧ IsManifold 𝓘(ℂ,Coord) ω (Fiber t) ∧
      IsClosedEmbedding (projectiveInclusion t) ∧
      ContMDiff 𝓘(ℂ,Coord) projectiveAmbientModel ω (projectiveInclusion t) ∧
      (∀ p : Fiber t, Function.Injective
        (mfderiv 𝓘(ℂ,Coord) projectiveAmbientModel (projectiveInclusion t) p)) ∧
      IsProperMap (blowdown t) ∧ Function.Surjective (blowdown t) ∧
      Dense (BlowdownComplement.partialHomeomorph t).source ∧
      Dense (BlowdownComplement.partialHomeomorph t).target ∧
      ContMDiffOn 𝓘(ℂ,Coord) 𝓘(ℂ,ℂ × ℂ) ω
        (BlowdownComplement.partialHomeomorph t) (BlowdownComplement.partialHomeomorph t).source ∧
      ContMDiffOn 𝓘(ℂ,ℂ × ℂ) 𝓘(ℂ,Coord) ω
        (BlowdownComplement.partialHomeomorph t).symm
        (BlowdownComplement.partialHomeomorph t).target :=
  ⟨inferInstance,inferInstance,projectiveInclusion_isClosedEmbedding t,
    projectiveInclusion_contMDiff t ω,projectiveInclusion_mfderiv_injective t,
    BlowdownComplement.actual_fiber_proper_dense_open_biholomorphism t⟩

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiber
