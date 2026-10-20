import FailureOfSemipositiveMetricExtension.GlobalCanonicalTangentForms
import FailureOfSemipositiveMetricExtension.ThreefoldAdjunctionAlgebra

/-! Actual tangent maps of fibre inclusion and projection, in the adapted
threefold atlas. No tangent-kernel or adjunction identification is assumed. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.GlobalCanonical
noncomputable section
open Set IsManifold Topology
open scoped Manifold ContDiff

theorem coordinates_mfderiv_inclusion (t : ℂ) (i : Fin 4) (e : Fin 2) (p : Fiber t)
    (hp : p ∈ FixedFiber.source t i e) :
    (mfderiv 𝓘(ℂ,ChartCoord) 𝓘(ℂ,ChartCoord) (chartCoordinates i e) (FixedFiber.inclusion t p)).comp
      (mfderiv 𝓘(ℂ,FixedFiber.Coord) 𝓘(ℂ,ChartCoord) (FixedFiber.inclusion t) p) =
    (ContinuousLinearMap.inl ℂ (ℂ × ℂ) ℂ).comp
      (mfderiv 𝓘(ℂ,FixedFiber.Coord) 𝓘(ℂ,FixedFiber.Coord) (FixedFiber.coordinates t i e) p) := by
  have he : (chartCoordinates i e ∘ FixedFiber.inclusion t) =ᶠ[𝓝 p]
      (FixedFiber.insertParameter t ∘ FixedFiber.coordinates t i e) := by
    filter_upwards [(FixedFiber.source_isOpen t i e).mem_nhds hp] with q hq
    exact FixedFiber.global_coordinates_eq t i e q hq
  have hg := ((chartCoordinates_contMDiffOn i e 1).contMDiffAt
    ((chartSource_isOpen i e).mem_nhds hp)).mdifferentiableAt le_rfl
  have hi := ((FixedFiber.inclusion_contMDiff t 1) p).mdifferentiableAt le_rfl
  have hc := ((FixedFiber.coordinates_contMDiffOn t i e 1).contMDiffAt
    ((FixedFiber.source_isOpen t i e).mem_nhds hp)).mdifferentiableAt le_rfl
  have hin : HasFDerivAt (FixedFiber.insertParameter t) (ContinuousLinearMap.inl ℂ (ℂ × ℂ) ℂ)
      (FixedFiber.coordinates t i e p) :=
    (hasFDerivAt_id _).prodMk (hasFDerivAt_const t _)
  have hh := he.mfderiv_eq (I := 𝓘(ℂ,FixedFiber.Coord)) (I' := 𝓘(ℂ,ChartCoord))
  rw [mfderiv_comp p hg hi,mfderiv_comp p hin.differentiableAt.mdifferentiableAt hc,
    mfderiv_eq_fderiv,hin.fderiv] at hh
  exact hh

theorem projection_mfderiv_coordinates (i : Fin 4) (e : Fin 2) (p : Total)
    (hp : p ∈ chartSource i e) :
    mfderiv 𝓘(ℂ,ChartCoord) 𝓘(ℂ) projection p =
      (ContinuousLinearMap.snd ℂ (ℂ × ℂ) ℂ).comp
        (mfderiv 𝓘(ℂ,ChartCoord) 𝓘(ℂ,ChartCoord) (chartCoordinates i e) p) := by
  have he : projection =ᶠ[𝓝 p] (fun q => (chartCoordinates i e q).2) := by
    filter_upwards [(chartSource_isOpen i e).mem_nhds hp] with q hq
    rw [chartCoordinates_eq_explicit i e q hq]
    rfl
  have hc := ((chartCoordinates_contMDiffOn i e 1).contMDiffAt
    ((chartSource_isOpen i e).mem_nhds hp)).mdifferentiableAt le_rfl
  rw [he.mfderiv_eq]
  have hs : MDifferentiableAt 𝓘(ℂ,ChartCoord) 𝓘(ℂ) (fun q : ChartCoord => q.2)
      (chartCoordinates i e p) := (hasFDerivAt_snd : HasFDerivAt
        (fun q : ChartCoord => q.2) (ContinuousLinearMap.snd ℂ (ℂ × ℂ) ℂ)
          (chartCoordinates i e p)).differentiableAt.mdifferentiableAt
  simpa only [mfderiv_eq_fderiv,fderiv_snd] using mfderiv_comp p hs hc

/-- The actual derivative of fibre inclusion is injective. -/
theorem inclusion_mfderiv_injective (t : ℂ) (p : Fiber t) :
    Function.Injective (mfderiv 𝓘(ℂ,FixedFiber.Coord) 𝓘(ℂ,ChartCoord) (FixedFiber.inclusion t) p) := by
  obtain ⟨⟨i,e⟩,hp⟩ := FixedFiber.charts_cover t p
  intro v w hvw
  have he := congrArg (fun A => A v) (coordinates_mfderiv_inclusion t i e p hp)
  have hf := congrArg (fun A => A w) (coordinates_mfderiv_inclusion t i e p hp)
  dsimp only at he hf
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.inl_apply] at he hf
  rw [hvw] at he
  have hh := he.symm.trans hf
  have hcoord : FixedFiber.chartTangentEquiv t i e p hp v = FixedFiber.chartTangentEquiv t i e p hp w :=
    congrArg Prod.fst hh
  exact (FixedFiber.chartTangentEquiv t i e p hp).injective hcoord

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.GlobalCanonical
